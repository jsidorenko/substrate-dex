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

fn pools() -> Vec<u32> {
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

fn create_assets(owner: u64, assets: Vec<u32>) {
	for asset_id in assets {
		assert_ok!(Assets::force_create(RuntimeOrigin::root(), asset_id, owner, true, 1));
	}
}

fn balance(owner: u64, asset_id: u32) -> u64 {
	<<Test as Config>::Assets>::balance(asset_id, owner)
}

fn currency_balance(owner: u64) -> u64 {
	<<Test as Config>::Currency>::free_balance(owner)
}

fn pool_balance(owner: u64, lp_asset_id: u32) -> u64 {
	<<Test as Config>::PoolAssets>::balance(lp_asset_id, owner)
}

#[test]
fn create_pool_should_work() {
	new_test_ext().execute_with(|| {
		let user = 1;
		// let asset_1 = 1;
		let asset_2 = 2;
		let asset_id = asset_2;

		create_assets(user, vec![asset_2]);

		let lp_asset: u32 = Dex::get_next_pool_asset_id();
		assert_ok!(Dex::create_pool(RuntimeOrigin::signed(user), asset_2));
		assert_eq!(lp_asset + 1, Dex::get_next_pool_asset_id());

		assert_eq!(events(), [Event::<Test>::PoolCreated { creator: user, asset_id, lp_asset }]);
		assert_eq!(pools(), vec![asset_id]);
		assert_eq!(assets(), vec![asset_2]);
		assert_eq!(pool_assets(), vec![lp_asset]);
	});
}

#[test]
fn create_same_pool_twice_should_fail() {
	new_test_ext().execute_with(|| {
		let user = 1;
		let asset_2 = 2;

		create_assets(user, vec![asset_2]);

		let lp_asset: u32 = Dex::get_next_pool_asset_id();
		assert_ok!(Dex::create_pool(RuntimeOrigin::signed(user), asset_2));
		let expected_free = lp_asset + 1;
		assert_eq!(expected_free, Dex::get_next_pool_asset_id());

		assert_noop!(
			Dex::create_pool(RuntimeOrigin::signed(user), asset_2),
			Error::<Test>::PoolExists
		);
		assert_eq!(expected_free, Dex::get_next_pool_asset_id());
	});
}

#[test]
fn different_pools_should_have_different_lp_assets() {
	new_test_ext().execute_with(|| {
		let user = 1;
		let asset_2 = 2;
		let asset_3 = 3;
		let pool_id_1_2 = asset_2;
		let pool_id_1_3 = asset_3;

		create_assets(user, vec![asset_2]);

		let lp_asset2_1: u32 = Dex::get_next_pool_asset_id();
		assert_ok!(Dex::create_pool(RuntimeOrigin::signed(user), asset_2));
		let lp_asset3_1: u32 = Dex::get_next_pool_asset_id();

		assert_eq!(
			events(),
			[Event::<Test>::PoolCreated {
				creator: user,
				asset_id: pool_id_1_2,
				lp_asset: lp_asset2_1
			}]
		);

		assert_ok!(Dex::create_pool(RuntimeOrigin::signed(user), asset_3));
		assert_eq!(
			events(),
			[Event::<Test>::PoolCreated {
				creator: user,
				asset_id: pool_id_1_3,
				lp_asset: lp_asset3_1
			}]
		);

		assert_ne!(lp_asset2_1, lp_asset3_1);
	});
}

#[test]
fn add_liquidity_should_work() {
	new_test_ext().execute_with(|| {
		let user = 1;
		let asset_2 = 2;
		let asset_id = asset_2;

		create_assets(user, vec![asset_2]);
		let lp_asset = Dex::get_next_pool_asset_id();
		assert_ok!(Dex::create_pool(RuntimeOrigin::signed(user), asset_2));

		assert_ok!(Balances::set_balance(RuntimeOrigin::root(), user, 1000, 0));
		assert_ok!(Assets::mint(RuntimeOrigin::signed(user), asset_2, user, 1000));

		assert_ok!(Dex::add_liquidity(
			RuntimeOrigin::signed(user),
			asset_2,
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
			asset_id,
			amount_native_provided: 10,
			amount_asset_provided: 10,
			lp_asset,
			liquidity: 9,
		}));

		let pallet_account = Dex::account_id();
		assert_eq!(currency_balance(pallet_account), 10);
		assert_eq!(balance(pallet_account, asset_2), 10);
		assert_eq!(pool_balance(user, lp_asset), 9);
	});
}

#[test]
fn remove_liquidity_should_work() {
	new_test_ext().execute_with(|| {
		let user = 1;
		let asset_2 = 2;
		let asset_id = asset_2;

		create_assets(user, vec![asset_2]);
		let lp_asset = Dex::get_next_pool_asset_id();
		assert_ok!(Dex::create_pool(RuntimeOrigin::signed(user), asset_2));

		assert_ok!(Balances::set_balance(RuntimeOrigin::root(), user, 1000, 0));
		assert_ok!(Assets::mint(RuntimeOrigin::signed(user), asset_2, user, 1000));

		assert_ok!(Dex::add_liquidity(
			RuntimeOrigin::signed(user),
			asset_2,
			10,
			10,
			10,
			10,
			user,
			2
		));

		assert_ok!(Dex::remove_liquidity(RuntimeOrigin::signed(user), asset_2, 9, 0, 0, user, 2));

		assert!(events().contains(&Event::<Test>::LiquidityRemoved {
			who: user,
			withdraw_to: user,
			asset_id,
			amount_native_withdrawn: 9,
			amount_asset_withdrawn: 9,
			lp_asset,
			liquidity: 9,
		}));

		let pallet_account = Dex::account_id();
		assert_eq!(currency_balance(pallet_account), 1);
		assert_eq!(balance(pallet_account, asset_2), 1);
		assert_eq!(pool_balance(pallet_account, lp_asset), 1);

		assert_eq!(currency_balance(user), 999);
		assert_eq!(balance(user, asset_2), 999);
		assert_eq!(pool_balance(user, lp_asset), 0);
	});
}

#[test]
fn quote_price_should_work() {
	new_test_ext().execute_with(|| {
		let user = 1;
		let asset_2 = 2;

		create_assets(user, vec![asset_2]);
		assert_ok!(Dex::create_pool(RuntimeOrigin::signed(user), asset_2));

		assert_ok!(Balances::set_balance(RuntimeOrigin::root(), user, 1000, 0));
		assert_ok!(Assets::mint(RuntimeOrigin::signed(user), asset_2, user, 1000));

		assert_ok!(Dex::add_liquidity(
			RuntimeOrigin::signed(user),
			asset_2,
			1000,
			20,
			1,
			1,
			user,
			2
		));

		assert_eq!(Dex::quote_asset(asset_2, 3000), Some(60));
	});
}

#[test]
fn sell_exact_asset_for_native_should_work() {
	new_test_ext().execute_with(|| {
		let user = 1;
		let asset_2 = 2;
		let deadline = 2;

		create_assets(user, vec![asset_2]);
		assert_ok!(Dex::create_pool(RuntimeOrigin::signed(user), asset_2));

		assert_ok!(Balances::set_balance(RuntimeOrigin::root(), user, 1000, 0));
		assert_ok!(Assets::mint(RuntimeOrigin::signed(user), asset_2, user, 1000));

		let liquidity1 = 1000;
		let liquidity2 = 20;
		assert_ok!(Dex::add_liquidity(
			RuntimeOrigin::signed(user),
			asset_2,
			liquidity1,
			liquidity2,
			1,
			1,
			user,
			deadline
		));

		assert_eq!(currency_balance(user), 0);

		let exchange_amount = 10;
		assert_ok!(Dex::sell_exact_asset_for_native(
			RuntimeOrigin::signed(user),
			asset_2,
			exchange_amount,
			1,
			user,
			3
		));

		let expect_receive =
			Dex::get_native_out(&exchange_amount, &liquidity2, &liquidity1).ok().unwrap();
		let pallet_account = Dex::account_id();
		assert_eq!(expect_receive, 332);
		assert_eq!(currency_balance(user), expect_receive);
		assert_eq!(currency_balance(pallet_account), liquidity1 - expect_receive);
		assert_eq!(balance(pallet_account, asset_2), liquidity2 + exchange_amount);
	});
}

#[test]
fn sell_asset_for_exact_native_should_work() {
	new_test_ext().execute_with(|| {
		let user = 1;
		let asset_id = 2;
		let deadline = 2;
		let pallet_account = Dex::account_id();

		create_assets(user, vec![asset_id]);
		assert_ok!(Dex::create_pool(RuntimeOrigin::signed(user), asset_id));

		assert_ok!(Balances::set_balance(RuntimeOrigin::root(), user, 1000, 0));
		assert_ok!(Assets::mint(RuntimeOrigin::signed(user), asset_id, user, 1000));

		let before_native = currency_balance(pallet_account) + currency_balance(user);
		let before_asset = balance(pallet_account, asset_id) + balance(user, asset_id);

		let liquidity_native = 1000;
		let liquidity_asset = 20;
		assert_ok!(Dex::add_liquidity(
			RuntimeOrigin::signed(user),
			asset_id,
			liquidity_native,
			liquidity_asset,
			1,
			1,
			user,
			deadline
		));

		assert_eq!(currency_balance(user), 0);

		let requested_native = 1;
		assert_ok!(Dex::sell_asset_for_exact_native(
			RuntimeOrigin::signed(user),
			asset_id,
			requested_native, // native_amount_out
			60,               // asset_amount_in_max
			user,
			3
		));

		let expect_give = Dex::get_asset_in(&requested_native, &liquidity_native, &liquidity_asset)
			.ok()
			.unwrap();

		assert_eq!(currency_balance(user), requested_native, "should receive exact amount");
		assert_eq!(currency_balance(pallet_account), liquidity_native - requested_native);
		assert_eq!(balance(pallet_account, asset_id), liquidity_asset + dbg!(expect_give));

		// check invariants:

		// dot and asset totals should be preserved.
		let after_native = currency_balance(pallet_account) + currency_balance(user);
		let after_asset = balance(pallet_account, asset_id) + balance(user, asset_id);
		assert_eq!(before_native, after_native);
		assert_eq!(before_asset, after_asset);
	});
}

#[test]
fn buy_asset_for_exact_native_should_work() {
	new_test_ext().execute_with(|| {
		let user = 1;
		let asset_id = 2;
		let deadline = 2;
		let pallet_account = Dex::account_id();

		create_assets(user, vec![asset_id]);
		assert_ok!(Dex::create_pool(RuntimeOrigin::signed(user), asset_id));

		assert_ok!(Balances::set_balance(RuntimeOrigin::root(), user, 3000, 0));
		assert_ok!(Assets::mint(RuntimeOrigin::signed(user), asset_id, user, 1000));

		let before_native = currency_balance(pallet_account) + currency_balance(user);
		let before_asset = balance(pallet_account, asset_id) + balance(user, asset_id);

		let liquidity_native = 1000;
		let liquidity_asset = 20;
		assert_ok!(Dex::add_liquidity(
			RuntimeOrigin::signed(user),
			asset_id,
			liquidity_native,
			liquidity_asset,
			1,
			1,
			user,
			deadline
		));

		assert_eq!(currency_balance(user), 2000);
		// assert_debit_credit(|| getter, || getter_creditor, 200, || action);

		let given_native = 1;
		assert_ok!(Dex::buy_asset_for_exact_native(
			RuntimeOrigin::signed(user),
			asset_id,
			given_native, // native_amount_in
			10,           // asset_amount_out_max
			user,
			3
		));

		let expect_give = Dex::get_asset_out(&given_native, &liquidity_native, &liquidity_asset)
			.ok()
			.unwrap();

		assert_eq!(currency_balance(user), 2000 - given_native, "should receive exact amount");
		assert_eq!(currency_balance(pallet_account), liquidity_native + given_native);
		assert_eq!(balance(pallet_account, asset_id), liquidity_asset - dbg!(expect_give));

		// check invariants:

		// dot and asset totals should be preserved.
		let after_native = currency_balance(pallet_account) + currency_balance(user);
		let after_asset = balance(pallet_account, asset_id) + balance(user, asset_id);
		assert_eq!(before_native, after_native);
		assert_eq!(before_asset, after_asset);
	});
}

#[test]
fn buy_exact_asset_for_native_should_work() {
	new_test_ext().execute_with(|| {
		let user = 1;
		let asset_id = 2;
		let deadline = 2;
		let pallet_account = Dex::account_id();

		create_assets(user, vec![asset_id]);
		assert_ok!(Dex::create_pool(RuntimeOrigin::signed(user), asset_id));

		assert_ok!(Balances::set_balance(RuntimeOrigin::root(), user, 3000, 0));
		assert_ok!(Assets::mint(RuntimeOrigin::signed(user), asset_id, user, 1000));

		let before_native = currency_balance(pallet_account) + currency_balance(user);
		let before_asset = balance(pallet_account, asset_id) + balance(user, asset_id);

		let liquidity_native = 1000;
		let liquidity_asset = 20;
		assert_ok!(Dex::add_liquidity(
			RuntimeOrigin::signed(user),
			asset_id,
			liquidity_native,
			liquidity_asset,
			1,
			1,
			user,
			deadline
		));

		assert_eq!(currency_balance(user), 2000);
		// assert_debit_credit(|| getter, || getter_creditor, 200, || action);

		let requested_assets = 1;
		assert_ok!(Dex::buy_exact_asset_for_native(
			RuntimeOrigin::signed(user),
			asset_id,
			requested_assets, // asset_amount_out
			100,              // native_amount_in_max
			user,
			3
		));

		let expect_give =
			Dex::get_native_in(&requested_assets, &liquidity_native, &liquidity_asset)
				.ok()
				.unwrap();

		assert_eq!(currency_balance(user), 2000 - expect_give, "should receive exact amount");
		assert_eq!(currency_balance(pallet_account), liquidity_native + expect_give);
		assert_eq!(balance(pallet_account, asset_id), liquidity_asset - dbg!(requested_assets));
		assert_eq!(balance(user, asset_id), 1000 - liquidity_asset + dbg!(requested_assets));

		// check invariants:

		// dot and asset totals should be preserved.
		let after_native = currency_balance(pallet_account) + currency_balance(user);
		let after_asset = balance(pallet_account, asset_id) + balance(user, asset_id);
		assert_eq!(before_native, after_native);
		assert_eq!(before_asset, after_asset);

		// TODO: check pool always grows bigger invariant.
	});
}
