/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Tate sequence `0 → Ĥ⁻¹(G, A) → A_G → A^G → Ĥ⁰(G, A) → 0`

Besides the connecting maps between different coefficient modules, the two low-degree Tate
groups are related to the fixed points `A^G = H⁰(G, A)` and the coinvariants
`A_G = A/I_G·A = H₀(G, A)` by the classical exact sequence

`0 → Ĥ⁻¹(G, A) → A_G --N--> A^G → Ĥ⁰(G, A) → 0`,

in which `Ĥ⁻¹(G, A) = ker(N : A_G → A^G)` is the kernel of the norm on the coinvariants and
`Ĥ⁰(G, A) = A^G/N(A)` is its cokernel.  In particular `Ĥ⁻¹` is naturally identified with a
subgroup of `H₀(G, A)` and `Ĥ⁰` with a quotient of `H⁰(G, A)`.

## Main definitions

* `Work.Tate.coinvariants` : the coinvariants `A_G = A/I_G·A`;
* `Work.Tate.coinvMk` : the quotient map `A → A_G`;
* `Work.Tate.normCoinv` : the norm as a map `A_G → A^G` (well defined because `N` kills
  the augmentation submodule);
* `Work.Tate.Hm1ToCoinv` : the inclusion `Ĥ⁻¹(G, A) → A_G`.

## Main results

* `Work.Tate.range_normCoinv_eq_ker_H0π` : `im(N : A_G → A^G) = ker(A^G → Ĥ⁰(G, A))`;
* `Work.Tate.range_Hm1ToCoinv_eq_ker_normCoinv` : `im(Ĥ⁻¹(G, A) → A_G) = ker(N : A_G → A^G)`;
* `Work.Tate.Hm1ToCoinv_injective` : `Ĥ⁻¹(G, A) → A_G` is injective.
-/
import Mathlib
import Submission.Work.Tate.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u v

namespace Work.Tate

open scoped BigOperators

variable (G : Type u) (A : Type v) [Group G] [AddCommGroup A] [DistribMulAction G A]

/-- The coinvariants `A_G = A/I_G·A` of a `G`-module (the zeroth homology group `H₀(G, A)`). -/
noncomputable abbrev coinvariants : Type v := A ⧸ augmentation G A

/-- The quotient map `A → A_G`. -/
noncomputable def coinvMk : A →+ coinvariants G A :=
  QuotientAddGroup.mk' (augmentation G A)

theorem coinvMk_eq_zero_iff (a : A) : coinvMk G A a = 0 ↔ a ∈ augmentation G A :=
  QuotientAddGroup.eq_zero_iff a

@[simp] theorem coinvMk_apply (a : A) :
    coinvMk G A a = QuotientAddGroup.mk' (augmentation G A) a := rfl

section Fintype

variable [Fintype G]

/-- The norm descends to the coinvariants: `N` kills `I_G·A`, so it induces a map
`A_G → A^G`. -/
noncomputable def normCoinv : coinvariants G A →+ fixedSubgroup G A :=
  QuotientAddGroup.lift (augmentation G A) (normToFixed G A) (by
    intro x hx
    rw [AddMonoidHom.mem_ker]
    exact Subtype.ext (norm_eq_zero_of_mem_augmentation hx))

@[simp] theorem normCoinv_apply (a : A) :
    (normCoinv G A (coinvMk G A a) : A) = norm G A a := rfl

/-- The natural map `Ĥ⁻¹(G, A) → A_G`, `[a] ↦ a + I_G·A`. -/
noncomputable def Hm1ToCoinv : Hm1 G A →+ coinvariants G A :=
  QuotientAddGroup.lift (augInKer G A) ((coinvMk G A).comp (norm G A).ker.subtype) (by
    intro x hx
    rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, coinvMk_eq_zero_iff]
    exact hx)

@[simp] theorem Hm1ToCoinv_apply (a : (norm G A).ker) :
    Hm1ToCoinv G A (Hm1π G A a) = coinvMk G A a := rfl

end Fintype

end Work.Tate
