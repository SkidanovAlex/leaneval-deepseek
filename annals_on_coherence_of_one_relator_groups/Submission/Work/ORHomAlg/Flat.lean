/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Flatness and weak dimension for noncommutative rings

Mathlib's `Module.Flat` is only available over commutative rings, so here we define flatness of a
right module `M` over an arbitrary ring `R` as exactness of the functor `M ⊠[R] -`, together with
the weak dimension of `M`.  The characterisation in terms of vanishing of `Tor` is proved
separately (see `Work.ORHomAlg.Flat`).
-/
module

public import Submission.Work.ORHomAlg.Tor

@[expose] public section

namespace Work.ORHomAlg

universe u

/-- A right `R`-module `M` is *flat* if `M ⊠[R] -` preserves injective linear maps. -/
def IsFlatRight (R : Type u) [Ring R] (M : Type u) [AddCommGroup M] [Module Rᵐᵒᵖ M] : Prop :=
  ∀ ⦃N N' : Type u⦄ [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
    (g : N →ₗ[R] N'), Function.Injective g →
      Function.Injective (BalancedTensor.lTensor (M := M) g)

/-- A left `R`-module `L` is *flat* if `- ⊠[R] L` preserves injective linear maps. -/
def IsFlatLeft (R : Type u) [Ring R] (L : Type u) [AddCommGroup L] [Module R L] : Prop :=
  ∀ ⦃M M' : Type u⦄ [AddCommGroup M] [Module Rᵐᵒᵖ M] [AddCommGroup M'] [Module Rᵐᵒᵖ M']
    (g : M →ₗ[Rᵐᵒᵖ] M'), Function.Injective g →
      Function.Injective (BalancedTensor.rTensor (N := L) g)

/-- A right `R`-module has weak dimension at most `n` if `Tor_k(M, -)` vanishes for `k > n`. -/
def weakDimLe (R : Type u) [Ring R] (M : Type u) [AddCommGroup M] [Module Rᵐᵒᵖ M] (n : ℕ) : Prop :=
  ∀ (N : Type u) [AddCommGroup N] [Module R N] (k : ℕ), n < k → Subsingleton (Tor (R := R) k M N)

end Work.ORHomAlg
