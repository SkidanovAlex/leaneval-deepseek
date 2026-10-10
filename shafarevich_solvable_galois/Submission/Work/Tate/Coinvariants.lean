import Mathlib.Data.Fintype.Defs
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.GroupWithZero.Action.Defs
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
