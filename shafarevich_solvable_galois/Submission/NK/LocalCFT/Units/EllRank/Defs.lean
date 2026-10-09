/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The number of index-`ℓ` subgroups of an abelian group

This file sets up the vocabulary for counting index-`ℓ` subgroups of a
commutative group, in additive notation.

For an additive commutative group `A` and a prime `ℓ`:

* `nsmulTop ℓ A` is the subgroup `ℓA` of `ℓ`-th multiples;
* `ellQuot ℓ A` is the elementary abelian `ℓ`-group `A ⧸ ℓA`, viewed as an
  `𝔽_ℓ`-vector space;
* `ellDual ℓ A` is its dual;
* `nIdx ℓ A` is the number of additive subgroups of `A` of index `ℓ`.

The main theorem proved on top of these definitions is
`nIdx ℓ V ≤ nIdx ℓ A` for a finite index subgroup `V ≤ A`
(`NK.LocalCFT.Units.EllRank.nIdx_le_of_finiteIndex`).
-/
import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical
open Module

namespace NK.LocalCFT.Units.EllRank

noncomputable section

/-- The number of additive subgroups of index `n` of an additive commutative group. -/
noncomputable def nIdx (n : ℕ) (A : Type*) [AddCommGroup A] : ℕ :=
  Nat.card {H : AddSubgroup A // H.index = n}

/-- `ℓA`, the subgroup of `ℓ`-th multiples of an additive commutative group. -/
noncomputable def nsmulTop (ℓ : ℕ) (A : Type*) [AddCommGroup A] : AddSubgroup A :=
  (⊤ : AddSubgroup A).map (nsmulAddMonoidHom ℓ)

/-- The elementary abelian `ℓ`-quotient `A ⧸ ℓA`, an `𝔽_ℓ`-vector space. -/
abbrev ellQuot (ℓ : ℕ) (A : Type*) [AddCommGroup A] : Type _ := A ⧸ nsmulTop ℓ A

instance instModuleEllQuot (ℓ : ℕ) (A : Type*) [AddCommGroup A] :
    Module (ZMod ℓ) (ellQuot ℓ A) :=
  QuotientAddGroup.zmodModule (fun x => by
    refine AddSubgroup.mem_map.mpr ⟨x, trivial, ?_⟩
    simp)

/-- The dual of the elementary abelian quotient `A ⧸ ℓA`. -/
abbrev ellDual (ℓ : ℕ) (A : Type*) [AddCommGroup A] : Type _ :=
  Module.Dual (ZMod ℓ) (ellQuot ℓ A)

/-- The number `(ℓ ^ r - 1) / (ℓ - 1)` where `r` is the `𝔽_ℓ`-dimension of `A ⧸ ℓA`. -/
noncomputable def ellCard (ℓ : ℕ) (A : Type*) [AddCommGroup A] : ℕ :=
  ∑ i ∈ Finset.range (finrank (ZMod ℓ) (ellQuot ℓ A)), ℓ ^ i

end

end NK.LocalCFT.Units.EllRank
