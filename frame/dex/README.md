# Decentralized exchange pallet

Substrate DEX pallet based on Uniswap V1/V2 logic.

## Overview

This pallet allows to:
 - create a liquidity pool for the native asset and another asset
 - provide the liquidity and receive back an LP asset
 - exchange the LP asset back to assets
 - swap asset for native and native for asset if there is a pool created
 - query for an exchange price via a new RPC endpoint

## RPC usage

```shell
curl http://localhost:9933 -H "Content-Type:application/json;charset=utf-8" -d   '{
     "jsonrpc":"2.0",
      "id":1,
      "method":"dex_quotePrice",
      "params": [1, 2, 100]
    }'
```
where:
 - `params[0]` - asset1 id
 - `params[1]` - asset2 id
 - `params[2]` - amount to swap

## Pallet extrinsics

```rust

    // Creates a pool. `lp_asset` is stored in a separate asset registry.
    pub fn create_pool(
      origin: OriginFor<T>,
      asset1: AssetIdOf<T>,
      asset2: AssetIdOf<T>,
      lp_asset: AssetIdOf<T>,
    ) -> DispatchResult;

    // Provide liquidity into the pool of `asset1` and `asset2`
    // NOTE: an optimal amount of asset1 and asset2 will be calculated and
    // might be different to provided `amount1_desired`/`amount2_desired`
    // thus it's needed to provide the min amount you're happy to provide.
    // Params `amount1_min`/`amount2_min` represent that.
    pub fn add_liquidity(
      origin: OriginFor<T>,
      asset_id: AssetIdOf<T>,
      amount_native_desired: BalanceOf<T>,
      amount_asset_desired: AssetBalanceOf<T>,
      amount_native_min: BalanceOf<T>,
      amount_asset_min: AssetBalanceOf<T>,
      mint_to: T::AccountId,
      deadline: T::BlockNumber,
    ) -> DispatchResult;

    // Allows to remove the liquidity by providing an lp token.
    // With the usage of `amount1_min`/`amount2_min` it's possible to control
    // the min amount of returned tokens you're happy with.
    pub fn remove_liquidity(
      origin: OriginFor<T>,
      asset_id: AssetIdOf<T>,
      liquidity: AssetBalanceOf<T>,
      amount_native_min: BalanceOf<T>,
      amount_asset_min: AssetBalanceOf<T>,
      withdraw_to: T::AccountId,
      deadline: T::BlockNumber,
    ) -> DispatchResult;

    // Swap the exact amount of `asset1` into `asset2`.
    // `amount_out_min` param allows to specify the min amount of the `asset2`
    // you're happy to receive.
    pub fn buy_exact_native_for_assset(
      origin: OriginFor<T>,
      asset_id: AssetIdOf<T>,
      amount_out: AssetBalanceOf<T>,
      amount_in_min: AssetBalanceOf<T>,
      send_to: T::AccountId,
      deadline: T::BlockNumber,
    ) -> DispatchResult;

    // Swap any amount of `asset1` to get the exact amount of `asset2`.
    // `amount_in_max` param allows to specify the max amount of the `asset1`
    // you're happy to provide.
    pub fn sell_exact_asset_for_native(
      origin: OriginFor<T>,
      asset_id: AssetIdOf<T>,
      amount_in: AssetBalanceOf<T>,
      amount_out_min: AssetBalanceOf<T>,
      send_to: T::AccountId,
      deadline: T::BlockNumber,
    ) -> DispatchResult;


    // Swap the exact amount of `asset1` into `asset2`.
    // `amount_out_min` param allows to specify the min amount of the `asset2`
    // you're happy to receive.
    pub fn buy_asset_for_exact_native(
      origin: OriginFor<T>,
      asset_id: AssetIdOf<T>,
      amount_in: AssetBalanceOf<T>,
      amount_out_max: AssetBalanceOf<T>,
      send_to: T::AccountId,
      deadline: T::BlockNumber,
    ) -> DispatchResult;

    // Swap any amount of `asset1` to get the exact amount of `asset2`.
    // `amount_in_max` param allows to specify the max amount of the `asset1`
    // you're happy to provide.
    pub fn sell_tokens_for_exact_asset(
      origin: OriginFor<T>,
      asset_id: AssetIdOf<T>,
      amount_out: AssetBalanceOf<T>,
      amount_in_max: AssetBalanceOf<T>,
      send_to: T::AccountId,
      deadline: T::BlockNumber,
    ) -> DispatchResult;
```
