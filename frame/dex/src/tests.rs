// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use crate::{mock::*, *};

use frame_support::{assert_noop, assert_ok, traits::fungibles::InspectEnumerable};

fn events() -> Vec<Event<Test>> {
	let result = System::events()
		.into_iter()
		.map(|r| r.event)
		.filter_map(|e| if let mock::RuntimeEvent::Dex(inner) = e { Some(inner) } else { None })
		.collect();

	System::reset_events();

	result
}

fn pools() -> Vec<PoolIdOf<Test>> {
	let mut s: Vec<_> = Pools::<Test>::iter().map(|x| x.0).collect();
	s.sort();
	s
}

fn assets() -> Vec<u32> {
	// if the storage would be public:
	// let mut s: Vec<_> = pallet_assets::pallet::Asset::<Test>::iter().map(|x| x.0).collect();
	let mut s: Vec<_> = <<Test as Config>::Assets>::asset_ids().collect();
	s.sort();
	s
}

fn pool_assets() -> Vec<u32> {
	// if the storage would be public:
	// let mut s: Vec<_> = pallet_assets::pallet::PoolAsset::<Test>::iter().map(|x| x.0).collect();
	let mut s: Vec<_> = <<Test as Config>::PoolAssets>::asset_ids().collect();
	s.sort();
	s
}

fn create_tokens(owner: u64, tokens: Vec<u32>) {
	for token_id in tokens {
		assert_ok!(Assets::force_create(RuntimeOrigin::root(), token_id, owner, true, 1));
	}
}

fn balance(owner: u64, token_id: u32) -> u64 {
	<<Test as Config>::Assets>::balance(token_id, owner)
}

fn currency_balance(owner: u64) -> u64 {
	<<Test as Config>::Currency>::free_balance(owner)
}

fn pool_balance(owner: u64, token_id: u32) -> u64 {
	<<Test as Config>::PoolAssets>::balance(token_id, owner)
}

#[test]
fn create_pool_should_work() {
	new_test_ext().execute_with(|| {
		let user = 1;
		// let token_1 = 1;
		let token_2 = 2;
		let pool_id = token_2;

		create_tokens(user, vec![token_2]);

		let lp_token: u32 = Dex::get_next_pool_asset_id();
		assert_ok!(Dex::create_pool(RuntimeOrigin::signed(user), token_2));
		assert_eq!(lp_token + 1, Dex::get_next_pool_asset_id());

		assert_eq!(events(), [Event::<Test>::PoolCreated { creator: user, pool_id, lp_token }]);
		assert_eq!(pools(), vec![pool_id]);
		assert_eq!(assets(), vec![token_2]);
		assert_eq!(pool_assets(), vec![lp_token]);
	});
}

#[test]
fn create_same_pool_twice_should_fail() {
	new_test_ext().execute_with(|| {
		let user = 1;
		let token_2 = 2;

		create_tokens(user, vec![token_2]);

		let lp_token: u32 = Dex::get_next_pool_asset_id();
		assert_ok!(Dex::create_pool(RuntimeOrigin::signed(user), token_2));
		let expected_free = lp_token + 1;
		assert_eq!(expected_free, Dex::get_next_pool_asset_id());

		assert_noop!(
			Dex::create_pool(RuntimeOrigin::signed(user), token_2),
			Error::<Test>::PoolExists
		);
		assert_eq!(expected_free, Dex::get_next_pool_asset_id());
	});
}

#[test]
fn different_pools_should_have_different_lp_tokens() {
	new_test_ext().execute_with(|| {
		let user = 1;
		let token_2 = 2;
		let token_3 = 3;
		let pool_id_1_2 = token_2;
		let pool_id_1_3 = token_3;

		create_tokens(user, vec![token_2]);

		let lp_token2_1: u32 = Dex::get_next_pool_asset_id();
		assert_ok!(Dex::create_pool(RuntimeOrigin::signed(user), token_2));
		let lp_token3_1: u32 = Dex::get_next_pool_asset_id();

		assert_eq!(
			events(),
			[Event::<Test>::PoolCreated {
				creator: user,
				pool_id: pool_id_1_2,
				lp_token: lp_token2_1
			}]
		);

		assert_ok!(Dex::create_pool(RuntimeOrigin::signed(user), token_3));
		assert_eq!(
			events(),
			[Event::<Test>::PoolCreated {
				creator: user,
				pool_id: pool_id_1_3,
				lp_token: lp_token3_1
			}]
		);

		assert_ne!(lp_token2_1, lp_token3_1);
	});
}

#[test]
fn add_liquidity_should_work() {
	new_test_ext().execute_with(|| {
		let user = 1;
		let token_2 = 2;
		let pool_id = token_2;

		create_tokens(user, vec![token_2]);
		let lp_token = Dex::get_next_pool_asset_id();
		assert_ok!(Dex::create_pool(RuntimeOrigin::signed(user), token_2));

		assert_ok!(Balances::set_balance(RuntimeOrigin::root(), user, 1000, 0));
		assert_ok!(Assets::mint(RuntimeOrigin::signed(user), token_2, user, 1000));

		assert_ok!(Dex::add_liquidity(
			RuntimeOrigin::signed(user),
			token_2,
			10,
			10,
			10,
			10,
			user,
			2
		));

		assert!(events().contains(&Event::<Test>::LiquidityAdded {
			who: user,
			mint_to: user,
			pool_id,
			amount1_provided: 10,
			amount2_provided: 10,
			lp_token,
			liquidity: 9,
		}));

		let pallet_account = Dex::account_id();
		assert_eq!(currency_balance(pallet_account), 10);
		assert_eq!(balance(pallet_account, token_2), 10);
		assert_eq!(pool_balance(user, lp_token), 9);
	});
}

#[test]
fn remove_liquidity_should_work() {
	new_test_ext().execute_with(|| {
		let user = 1;
		let token_2 = 2;
		let pool_id = token_2;

		create_tokens(user, vec![token_2]);
		let lp_token = Dex::get_next_pool_asset_id();
		assert_ok!(Dex::create_pool(RuntimeOrigin::signed(user), token_2));

		assert_ok!(Balances::set_balance(RuntimeOrigin::root(), user, 1000, 0));
		assert_ok!(Assets::mint(RuntimeOrigin::signed(user), token_2, user, 1000));

		assert_ok!(Dex::add_liquidity(
			RuntimeOrigin::signed(user),
			// token_1,
			token_2,
			10,
			10,
			10,
			10,
			user,
			2
		));

		assert_ok!(Dex::remove_liquidity(RuntimeOrigin::signed(user), token_2, 9, 0, 0, user, 2));

		assert!(events().contains(&Event::<Test>::LiquidityRemoved {
			who: user,
			withdraw_to: user,
			pool_id,
			amount1: 9,
			amount2: 9,
			lp_token,
			liquidity: 9,
		}));

		let pallet_account = Dex::account_id();
		assert_eq!(currency_balance(pallet_account), 1);
		assert_eq!(balance(pallet_account, token_2), 1);
		assert_eq!(pool_balance(pallet_account, lp_token), 1);

		assert_eq!(currency_balance(user), 999);
		assert_eq!(balance(user, token_2), 999);
		assert_eq!(pool_balance(user, lp_token), 0);
	});
}

#[test]
fn quote_price_should_work() {
	new_test_ext().execute_with(|| {
		let user = 1;
		let token_2 = 2;

		create_tokens(user, vec![token_2]);
		assert_ok!(Dex::create_pool(RuntimeOrigin::signed(user), token_2));

		assert_ok!(Balances::set_balance(RuntimeOrigin::root(), user, 1000, 0));
		assert_ok!(Assets::mint(RuntimeOrigin::signed(user), token_2, user, 1000));

		assert_ok!(Dex::add_liquidity(
			RuntimeOrigin::signed(user),
			token_2,
			1000,
			20,
			1,
			1,
			user,
			2
		));

		assert_eq!(Dex::quote_tokens(token_2, 3000), Some(60));
	});
}

#[test]
fn sell_exact_tokens_for_native_should_work() {
	new_test_ext().execute_with(|| {
		let user = 1;
		let token_2 = 2;
		let deadline = 2;

		create_tokens(user, vec![token_2]);
		assert_ok!(Dex::create_pool(RuntimeOrigin::signed(user), token_2));

		assert_ok!(Balances::set_balance(RuntimeOrigin::root(), user, 1000, 0));
		assert_ok!(Assets::mint(RuntimeOrigin::signed(user), token_2, user, 1000));

		let liquidity1 = 1000;
		let liquidity2 = 20;
		assert_ok!(Dex::add_liquidity(
			RuntimeOrigin::signed(user),
			token_2,
			liquidity1,
			liquidity2,
			1,
			1,
			user,
			deadline
		));

		assert_eq!(currency_balance(user), 0);

		let exchange_amount = 10;
		assert_ok!(Dex::sell_exact_tokens_for_native(
			RuntimeOrigin::signed(user),
			token_2,
			exchange_amount,
			1,
			user,
			3
		));

		let expect_receive =
			Dex::get_native_out(&exchange_amount, &liquidity2, &liquidity1).ok().unwrap();
		let pallet_account = Dex::account_id();
		assert_eq!(currency_balance(user), expect_receive);
		assert_eq!(currency_balance(pallet_account), liquidity1 - expect_receive);
		assert_eq!(balance(pallet_account, token_2), liquidity2 + exchange_amount);
	});
}
