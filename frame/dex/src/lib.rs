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

#![cfg_attr(not(feature = "std"), no_std)]
use frame_support::traits::Incrementable;

mod types;

#[cfg(test)]
mod tests;

#[cfg(test)]
mod mock;

pub use pallet::*;
pub use types::*;

// https://docs.uniswap.org/protocol/V2/concepts/protocol-overview/smart-contracts#minimum-liquidity
// TODO: make it configurable
// TODO: weights and benchmarking.
// TODO: more specific error codes.
pub const MIN_LIQUIDITY: u64 = 1;

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	use frame_support::{
		traits::{
			fungible::{Inspect as InspectFungible, Transfer as TransferFungible},
			fungibles::{metadata::Mutate as MutateMetadata, Create, Inspect, Mutate, Transfer},
		},
		PalletId,
	};
	use sp_runtime::traits::{
		AccountIdConversion, AtLeast32BitUnsigned, CheckedAdd, CheckedDiv, CheckedMul, CheckedSub,
		IntegerSquareRoot, One, Zero,
	};

	#[pallet::pallet]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config: frame_system::Config {
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;

		type Currency: InspectFungible<Self::AccountId, Balance = Self::AssetBalance>
			+ TransferFungible<Self::AccountId>;

		type AssetBalance: AtLeast32BitUnsigned
			+ codec::FullCodec
			+ Copy
			+ MaybeSerializeDeserialize
			+ sp_std::fmt::Debug
			+ From<u64>
			+ IntegerSquareRoot
			+ Zero
			+ TypeInfo
			+ MaxEncodedLen;

		type AssetId: Member
			+ Parameter
			+ Copy
			+ From<u32>
			+ MaybeSerializeDeserialize
			+ MaxEncodedLen
			+ PartialOrd
			+ TypeInfo;

		type PoolAssetId: Member
			+ Parameter
			+ Default
			+ Copy
			+ codec::HasCompact
			+ From<u32>
			+ MaybeSerializeDeserialize
			+ MaxEncodedLen
			+ PartialOrd
			+ TypeInfo
			+ Incrementable;

		type Assets: Inspect<Self::AccountId, AssetId = Self::AssetId, Balance = Self::AssetBalance>
			+ Transfer<Self::AccountId>;

		type PoolAssets: Inspect<Self::AccountId, AssetId = Self::PoolAssetId, Balance = Self::AssetBalance>
			+ Create<Self::AccountId>
			+ Mutate<Self::AccountId>
			+ MutateMetadata<Self::AccountId>
			+ Transfer<Self::AccountId>;

		/// The dex's pallet id, used for deriving its sovereign account ID.
		#[pallet::constant]
		type PalletId: Get<PalletId>;
	}

	pub type BalanceOf<T> = <<T as Config>::Currency as InspectFungible<
		<T as frame_system::Config>::AccountId,
	>>::Balance;

	pub type AssetBalanceOf<T> =
		<<T as Config>::Assets as Inspect<<T as frame_system::Config>::AccountId>>::Balance;

	#[pallet::storage]
	pub type Pools<T: Config> = StorageMap<
		_,
		Blake2_128Concat,
		T::AssetId,
		PoolInfo<T::AccountId, T::AssetId, T::PoolAssetId, BalanceOf<T>, AssetBalanceOf<T>>,
		OptionQuery,
	>;

	/// Stores the `PoolAssetId` that is going to be used for the next lp token.
	/// This gets incremented whenever a new lp pool is created.
	#[pallet::storage]
	pub type NextPoolAssetId<T: Config> = StorageValue<_, T::PoolAssetId, OptionQuery>;

	// Pallet's events.
	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		PoolCreated {
			creator: T::AccountId,
			asset_id: T::AssetId,
			lp_asset: T::PoolAssetId,
		},
		LiquidityAdded {
			who: T::AccountId,
			mint_to: T::AccountId,
			asset_id: T::AssetId,
			amount_native_provided: BalanceOf<T>,
			amount_asset_provided: AssetBalanceOf<T>,
			lp_asset: T::PoolAssetId,
			liquidity: AssetBalanceOf<T>,
		},
		LiquidityRemoved {
			who: T::AccountId,
			withdraw_to: T::AccountId,
			asset_id: T::AssetId,
			amount_native_withdrawn: BalanceOf<T>,
			amount_asset_withdrawn: AssetBalanceOf<T>,
			lp_asset: T::PoolAssetId,
			liquidity: AssetBalanceOf<T>,
		},
		SwapExecuted {
			who: T::AccountId,
			send_to: T::AccountId,
			asset_id: T::AssetId,
			amount_in: AssetBalanceOf<T>,
			amount_out: AssetBalanceOf<T>,
		},
	}

	// Your Pallet's error messages.
	#[pallet::error]
	pub enum Error<T> {
		/// Provided assets are equal.
		EqualAssets,
		/// Pool already exists.
		PoolExists,
		/// Desired amount can't be zero.
		WrongDesiredAmount,
		/// The deadline has already passed.
		DeadlinePassed,
		/// The pool doesn't exist.
		PoolNotFound,
		/// An overflow happened.
		Overflow,
		/// Insufficient amount provided.
		InsufficientAmount,
		/// Optimal calculated amount is less than desired.
		OptimalAmountLessThanDesired,
		/// Insufficient liquidity minted.
		InsufficientLiquidityMinted,
		/// Asked liquidity can't be zero.
		ZeroLiquidity,
		/// Amount can't be zero.
		ZeroAmount,
		/// Calculated amount out is less than min desired.
		InsufficientOutputAmount,
		/// Insufficient liquidity in the pool.
		InsufficientLiquidity,
		/// Excessive input amount.
		ExcessiveInputAmount,
	}

	// Pallet's callable functions.
	#[pallet::call]
	impl<T: Config> Pallet<T> {
		#[pallet::call_index(0)]
		#[pallet::weight(0)]
		pub fn create_pool(origin: OriginFor<T>, asset_id: T::AssetId) -> DispatchResult {
			let sender = ensure_signed(origin)?;

			ensure!(!Pools::<T>::contains_key(&asset_id), Error::<T>::PoolExists);

			let pallet_account = Self::account_id();

			let lp_asset = NextPoolAssetId::<T>::get().unwrap_or(T::PoolAssetId::initial_value());

			let next_lp_asset_id = lp_asset.increment();
			NextPoolAssetId::<T>::set(Some(next_lp_asset_id));

			T::PoolAssets::create(lp_asset, pallet_account.clone(), true, MIN_LIQUIDITY.into())?;
			T::PoolAssets::set(lp_asset, &pallet_account, "LP".into(), "LP".into(), 0)?;

			let pool_info = PoolInfo {
				owner: sender.clone(),
				lp_asset,
				asset_id,
				balance_native: Zero::zero(),
				balance_asset: Zero::zero(),
			};

			Pools::<T>::insert(asset_id, pool_info);

			Self::deposit_event(Event::PoolCreated { creator: sender, asset_id, lp_asset });

			Ok(())
		}

		#[pallet::weight(0)]
		pub fn add_liquidity(
			origin: OriginFor<T>,
			asset_id: T::AssetId,
			native_desired: BalanceOf<T>,
			asset_desired: AssetBalanceOf<T>,
			amount_native_min: BalanceOf<T>,
			amount_asset_min: AssetBalanceOf<T>,
			mint_to: T::AccountId,
			deadline: T::BlockNumber,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;

			ensure!(
				native_desired > Zero::zero() && asset_desired > Zero::zero(),
				Error::<T>::WrongDesiredAmount
			);

			let now = frame_system::Pallet::<T>::block_number();
			ensure!(deadline >= now, Error::<T>::DeadlinePassed);

			Pools::<T>::try_mutate(&asset_id, |maybe_pool| {
				let pool = maybe_pool.as_mut().ok_or(Error::<T>::PoolNotFound)?;

				let amount_native: BalanceOf<T>;
				let amount_asset: AssetBalanceOf<T>;

				let reserve_native = pool.balance_native;
				let reserve_asset = pool.balance_asset;

				if reserve_native.is_zero() && reserve_asset.is_zero() {
					amount_native = native_desired;
					amount_asset = asset_desired;
				} else {
					let amount_asset_optimal =
						Self::quote_asset_inner(&native_desired, &reserve_native, &reserve_asset)?;

					if amount_asset_optimal <= asset_desired {
						ensure!(amount_asset_optimal >= amount_asset_min, Error::<T>::InsufficientAmount);
						amount_native = native_desired;
						amount_asset = amount_asset_optimal;
					} else {
						let amount_native_optimal =
							Self::quote_native_inner(&asset_desired, &reserve_asset, &reserve_native)?;
						ensure!(
							amount_native_optimal <= native_desired,
							Error::<T>::OptimalAmountLessThanDesired
						);
						ensure!(amount_native_optimal >= amount_native_min, Error::<T>::InsufficientAmount);
						amount_native = amount_native_optimal;
						amount_asset = asset_desired;
					}
				}

				let pallet_account = Self::account_id();
				T::Currency::transfer(&sender, &pallet_account, amount_native, false)?;
				T::Assets::transfer(asset_id, &sender, &pallet_account, amount_asset, false)?;

				let total_supply = T::PoolAssets::total_issuance(pool.lp_asset);

				let liquidity: AssetBalanceOf<T>;
				if total_supply.is_zero() {
					liquidity = amount_native
						.checked_mul(&amount_asset)
						.ok_or(Error::<T>::Overflow)?
						.integer_sqrt()
						.checked_sub(&MIN_LIQUIDITY.into())
						.ok_or(Error::<T>::Overflow)?;
					T::PoolAssets::mint_into(pool.lp_asset, &pallet_account, MIN_LIQUIDITY.into())?;
				} else {
					let side_native = amount_native
						.checked_mul(&total_supply)
						.ok_or(Error::<T>::Overflow)?
						.checked_div(&reserve_native)
						.ok_or(Error::<T>::Overflow)?;

					let side_asset = amount_asset
						.checked_mul(&total_supply)
						.ok_or(Error::<T>::Overflow)?
						.checked_div(&reserve_asset)
						.ok_or(Error::<T>::Overflow)?;

					liquidity = side_native.min(side_asset);
				}

				ensure!(liquidity > MIN_LIQUIDITY.into(), Error::<T>::InsufficientLiquidityMinted);

				T::PoolAssets::mint_into(pool.lp_asset, &mint_to, liquidity)?;

				pool.balance_native = reserve_native + amount_native;
				pool.balance_asset = reserve_asset + amount_asset;

				Self::deposit_event(Event::LiquidityAdded {
					who: sender,
					mint_to,
					asset_id,
					amount_native_provided: amount_native,
					amount_asset_provided: amount_asset,
					lp_asset: pool.lp_asset,
					liquidity,
				});

				Ok(())
			})
		}

		#[pallet::weight(0)]
		pub fn remove_liquidity(
			origin: OriginFor<T>,
			asset_id: T::AssetId,
			liquidity: AssetBalanceOf<T>,
			amount_native_min: BalanceOf<T>,
			amount_asset_min: AssetBalanceOf<T>,
			withdraw_to: T::AccountId,
			deadline: T::BlockNumber,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;

			ensure!(liquidity > Zero::zero(), Error::<T>::ZeroLiquidity);

			let now = frame_system::Pallet::<T>::block_number();
			ensure!(deadline >= now, Error::<T>::DeadlinePassed);

			Pools::<T>::try_mutate(&asset_id, |maybe_pool| {
				let pool = maybe_pool.as_mut().ok_or(Error::<T>::PoolNotFound)?;

				let pallet_account = Self::account_id();
				T::PoolAssets::transfer(pool.lp_asset, &sender, &pallet_account, liquidity, false)?;

				let reserve_native = pool.balance_native;
				let reserve_asset = pool.balance_asset;

				let total_supply = T::PoolAssets::total_issuance(pool.lp_asset);

				let amount_native = liquidity
					.checked_mul(&reserve_native)
					.ok_or(Error::<T>::Overflow)?
					.checked_div(&total_supply)
					.ok_or(Error::<T>::Overflow)?;

				let amount_asset = liquidity
					.checked_mul(&reserve_asset)
					.ok_or(Error::<T>::Overflow)?
					.checked_div(&total_supply)
					.ok_or(Error::<T>::Overflow)?;

				ensure!(
					!amount_native.is_zero() && amount_native >= amount_native_min,
					Error::<T>::InsufficientAmount
				);
				ensure!(
					!amount_asset.is_zero() && amount_asset >= amount_asset_min,
					Error::<T>::InsufficientAmount
				);

				T::PoolAssets::burn_from(pool.lp_asset, &pallet_account, liquidity)?;

				T::Currency::transfer(&pallet_account, &withdraw_to, amount_native, false)?;
				T::Assets::transfer(asset_id, &pallet_account, &withdraw_to, amount_asset, false)?;

				pool.balance_native = reserve_native - amount_native;
				pool.balance_asset = reserve_asset - amount_asset;

				Self::deposit_event(Event::LiquidityRemoved {
					who: sender,
					withdraw_to,
					asset_id,
					amount_native_withdrawn: amount_native,
					amount_asset_withdrawn: amount_asset,
					lp_asset: pool.lp_asset,
					liquidity,
				});

				Ok(())
			})
		}

		/// some native --> exact number of assets
		#[pallet::weight(0)]
		pub fn buy_exact_asset_for_native(
			origin: OriginFor<T>,
			asset_id: T::AssetId,
			amount_out: AssetBalanceOf<T>,
			amount_in_min: BalanceOf<T>,
			send_to: T::AccountId,
			deadline: T::BlockNumber,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;

			ensure!(
				amount_out > Zero::zero() && amount_in_min > Zero::zero(),
				Error::<T>::ZeroAmount
			);

			let now = frame_system::Pallet::<T>::block_number();
			ensure!(deadline >= now, Error::<T>::DeadlinePassed);

			Pools::<T>::try_mutate(&asset_id, |maybe_pool| {
				let pool = maybe_pool.as_mut().ok_or(Error::<T>::PoolNotFound)?;

				let amount_in =
					Self::get_native_in(&amount_out, &pool.balance_native, &pool.balance_asset)?;

				ensure!(amount_in >= amount_in_min, Error::<T>::InsufficientOutputAmount);

				let pallet_account = Self::account_id();

				T::Currency::transfer(&sender, &pallet_account, amount_out, false)?;

				ensure!(amount_out < pool.balance_asset, Error::<T>::InsufficientLiquidity);

				T::Assets::transfer(asset_id, &pallet_account, &send_to, amount_in, false)?;

				pool.balance_native += amount_in;
				pool.balance_asset -= amount_out;

				Self::deposit_event(Event::SwapExecuted {
					who: sender,
					send_to,
					asset_id,
					amount_in,
					amount_out,
				});

				Ok(())
			})
		}

		/// Exact number of assets --> some native
		#[pallet::weight(0)]
		pub fn sell_exact_asset_for_native(
			origin: OriginFor<T>,
			asset_id: T::AssetId,
			amount_in: AssetBalanceOf<T>,
			amount_out_min: BalanceOf<T>,
			send_to: T::AccountId,
			deadline: T::BlockNumber,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;

			ensure!(
				amount_in > Zero::zero() && amount_out_min > Zero::zero(),
				Error::<T>::ZeroAmount
			);

			let now = frame_system::Pallet::<T>::block_number();
			ensure!(deadline >= now, Error::<T>::DeadlinePassed);

			Pools::<T>::try_mutate(&asset_id, |maybe_pool| {
				let pool = maybe_pool.as_mut().ok_or(Error::<T>::PoolNotFound)?;

				let amount_out =
					Self::get_native_out(&amount_in, &pool.balance_asset, &pool.balance_native)?;

				ensure!(amount_out >= amount_out_min, Error::<T>::InsufficientOutputAmount);

				let pallet_account = Self::account_id();

				T::Assets::transfer(asset_id, &sender, &pallet_account, amount_in, false)?;

				ensure!(amount_out < pool.balance_native, Error::<T>::InsufficientLiquidity);

				T::Currency::transfer(&pallet_account, &sender, amount_out, false)?;

				pool.balance_asset += amount_in;
				pool.balance_native -= amount_out;

				Self::deposit_event(Event::SwapExecuted {
					who: sender,
					send_to,
					asset_id,
					amount_in,
					amount_out,
				});

				Ok(())
			})
		}

		/// Exact native --> some assets
		#[pallet::weight(0)]
		pub fn buy_asset_for_exact_native(
			origin: OriginFor<T>,
			asset_id: T::AssetId,
			amount_in: AssetBalanceOf<T>,
			amount_out_max: BalanceOf<T>,
			send_to: T::AccountId,
			deadline: T::BlockNumber,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;

			ensure!(
				amount_in > Zero::zero() && amount_out_max > Zero::zero(),
				Error::<T>::ZeroAmount
			);

			let now = frame_system::Pallet::<T>::block_number();
			ensure!(deadline >= now, Error::<T>::DeadlinePassed);

			Pools::<T>::try_mutate(&asset_id, |maybe_pool| {
				let pool = maybe_pool.as_mut().ok_or(Error::<T>::PoolNotFound)?;

				let amount_out =
					Self::get_native_out(&amount_in, &pool.balance_native, &pool.balance_asset)?;
				ensure!(amount_out <= amount_out_max, Error::<T>::ExcessiveInputAmount);

				let pallet_account = Self::account_id();
				T::Currency::transfer(&sender, &pallet_account, amount_in, false)?;

				ensure!(amount_out < pool.balance_asset, Error::<T>::InsufficientLiquidity);

				T::Assets::transfer(asset_id, &pallet_account, &send_to, amount_out, false)?;

				pool.balance_native += amount_in;
				pool.balance_asset -= amount_out;

				Self::deposit_event(Event::SwapExecuted {
					who: sender,
					send_to,
					asset_id,
					amount_in,
					amount_out,
				});

				Ok(())
			})
		}

		/// Some assets --> exact native
		#[pallet::weight(0)]
		pub fn sell_asset_for_exact_native(
			origin: OriginFor<T>,
			asset_id: T::AssetId,
			amount_out: AssetBalanceOf<T>,
			amount_in_max: BalanceOf<T>,
			send_to: T::AccountId,
			deadline: T::BlockNumber,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;

			ensure!(
				amount_out > Zero::zero() && amount_in_max > Zero::zero(),
				Error::<T>::ZeroAmount
			);

			let now = frame_system::Pallet::<T>::block_number();
			ensure!(deadline >= now, Error::<T>::DeadlinePassed);

			Pools::<T>::try_mutate(&asset_id, |maybe_pool| {
				let pool = maybe_pool.as_mut().ok_or(Error::<T>::PoolNotFound)?;

				let amount_in =
					Self::get_asset_in(&amount_out, &pool.balance_native, &pool.balance_asset)?;
				ensure!(amount_in <= amount_in_max, Error::<T>::ExcessiveInputAmount);

				let pallet_account = Self::account_id();

				T::Assets::transfer(asset_id, &pallet_account, &send_to, amount_in, false)?;

				ensure!(amount_out < pool.balance_native, Error::<T>::InsufficientLiquidity);

				T::Currency::transfer(&sender, &pallet_account, amount_out, false)?;

				pool.balance_asset += amount_in;
				pool.balance_native -= amount_out;

				Self::deposit_event(Event::SwapExecuted {
					who: sender,
					send_to,
					asset_id,
					amount_in,
					amount_out,
				});

				Ok(())
			})
		}
	}

	impl<T: Config> Pallet<T> {
		/// The account ID of the dex pallet.
		///
		/// This actually does computation. If you need to keep using it, then make sure you cache
		/// the value and only call this once.
		pub fn account_id() -> T::AccountId {
			T::PalletId::get().into_account_truncating()
		}

		pub fn quote_asset(asset_id: u32, amount: u64) -> Option<AssetBalanceOf<T>> {
			let asset_id: T::AssetId = asset_id.into();
			let amount = amount.into();
		
			if let Some(pool) = Pools::<T>::get(asset_id) {
				Self::quote_asset_inner(&amount, &pool.balance_native, &pool.balance_asset).ok()
			} else {
				None
			}
		}

		pub fn quote_native(asset_id: u32, amount: u64) -> Option<BalanceOf<T>> {
			let asset_id: T::AssetId = asset_id.into();
			let amount = amount.into();
		
			if let Some(pool) = Pools::<T>::get(asset_id) {
				Self::quote_native_inner(&amount, &pool.balance_asset, &pool.balance_native).ok()
			} else {
				None
			}
		}

		// TODO: we should probably use u128 for calculations
		/// Calculates the optimal amount from the reserves.
		pub fn quote_native_inner(
			amount: &AssetBalanceOf<T>,
			reserve_asset: &AssetBalanceOf<T>,
			reserve_native: &BalanceOf<T>,
		) -> Result<BalanceOf<T>, Error<T>> {
			amount
				.checked_mul(&reserve_native)
				.ok_or(Error::<T>::Overflow)?
				.checked_div(&reserve_asset)
				.ok_or(Error::<T>::Overflow)
		}

		// TODO: we should probably use u128 for calculations
		/// Calculates the optimal amount from the reserves.
		pub fn quote_asset_inner(
			amount: &BalanceOf<T>,
			reserve_native: &BalanceOf<T>,
			reserve_asset: &AssetBalanceOf<T>,
		) -> Result<AssetBalanceOf<T>, Error<T>> {
			// amount * reserve_asset / reserve_native
			amount
				.checked_mul(&reserve_asset)
				.ok_or(Error::<T>::Overflow)?
				.checked_div(&reserve_native)
				.ok_or(Error::<T>::Overflow)
		}

		/// Calculates amount out
		///
		/// Given an input amount of an asset and pair reserves, returns the maximum output amount
		/// of the other asset
		pub fn get_native_out(
			amount_in: &AssetBalanceOf<T>,
			reserve_in: &AssetBalanceOf<T>,
			reserve_out: &BalanceOf<T>,
		) -> Result<BalanceOf<T>, Error<T>> {
			if reserve_in.is_zero() || reserve_out.is_zero() {
				return Err(Error::<T>::InsufficientLiquidity.into())
			}

			// TODO: extract 0.3% into config
			// TODO: could use Permill type
			let amount_in_with_fee =
				amount_in.checked_mul(&997u64.into()).ok_or(Error::<T>::Overflow)?;

			let numerator =
				amount_in_with_fee.checked_mul(reserve_out).ok_or(Error::<T>::Overflow)?;

			let denominator = reserve_in
				.checked_mul(&1000u64.into())
				.ok_or(Error::<T>::Overflow)?
				.checked_add(&amount_in_with_fee)
				.ok_or(Error::<T>::Overflow)?;

			numerator.checked_div(&denominator).ok_or(Error::<T>::Overflow)
		}

		/// Calculates amount out
		///
		/// Given an input amount of an asset and pair reserves, returns the maximum output amount
		/// of the other asset
		pub fn get_asset_out(
			amount_in: &BalanceOf<T>,
			reserve_in: &BalanceOf<T>,
			reserve_out: &AssetBalanceOf<T>,
		) -> Result<AssetBalanceOf<T>, Error<T>> {
			if reserve_in.is_zero() || reserve_out.is_zero() {
				return Err(Error::<T>::InsufficientLiquidity.into())
			}

			// TODO: extract 0.3% into config
			// TODO: could use Permill type
			let amount_in_with_fee =
				amount_in.checked_mul(&997u64.into()).ok_or(Error::<T>::Overflow)?;

			let numerator =
				amount_in_with_fee.checked_mul(reserve_out).ok_or(Error::<T>::Overflow)?;

			let denominator = reserve_in
				.checked_mul(&1000u64.into())
				.ok_or(Error::<T>::Overflow)?
				.checked_add(&amount_in_with_fee)
				.ok_or(Error::<T>::Overflow)?;

			numerator.checked_div(&denominator).ok_or(Error::<T>::Overflow)
		}

		/// Calculates amount in
		///
		/// Given an output amount of an asset and pair reserves, returns a required input amount
		/// of the other asset
		pub fn get_native_in(
			amount_out: &AssetBalanceOf<T>,
			reserve_in: &BalanceOf<T>,
			reserve_out: &AssetBalanceOf<T>,
		) -> Result<BalanceOf<T>, Error<T>> {
			if reserve_in.is_zero() || reserve_out.is_zero() {
				return Err(Error::<T>::InsufficientLiquidity.into())
			}

			// TODO: extract 0.3% into config
			let numerator = reserve_in
				.checked_mul(amount_out)
				.ok_or(Error::<T>::Overflow)?
				.checked_mul(&1000u64.into())
				.ok_or(Error::<T>::Overflow)?;

			let denominator = reserve_out
				.checked_sub(amount_out)
				.ok_or(Error::<T>::Overflow)?
				.checked_mul(&997u64.into())
				.ok_or(Error::<T>::Overflow)?;

			numerator
				.checked_div(&denominator)
				.ok_or(Error::<T>::Overflow)?
				.checked_add(&One::one())
				.ok_or(Error::<T>::Overflow)
		}

		/// Calculates amount in
		///
		/// Given an output amount of an asset and pair reserves, returns a required input amount
		/// of the other asset
		pub fn get_asset_in(
			amount_out: &BalanceOf<T>,
			reserve_in: &AssetBalanceOf<T>,
			reserve_out: &BalanceOf<T>,
		) -> Result<AssetBalanceOf<T>, Error<T>> {
			if reserve_in.is_zero() || reserve_out.is_zero() {
				return Err(Error::<T>::InsufficientLiquidity.into())
			}

			// TODO: extract 0.3% into config
			let numerator = reserve_in
				.checked_mul(amount_out)
				.ok_or(Error::<T>::Overflow)?
				.checked_mul(&1000u64.into())
				.ok_or(Error::<T>::Overflow)?;

			let denominator = reserve_out
				.checked_sub(amount_out)
				.ok_or(Error::<T>::Overflow)?
				.checked_mul(&997u64.into())
				.ok_or(Error::<T>::Overflow)?;

			numerator
				.checked_div(&denominator)
				.ok_or(Error::<T>::Overflow)?
				.checked_add(&One::one())
				.ok_or(Error::<T>::Overflow)
		}

		#[cfg(test)]
		pub fn get_next_pool_asset_id() -> T::PoolAssetId {
			NextPoolAssetId::<T>::get().unwrap_or(T::PoolAssetId::initial_value())
		}
	}
}
