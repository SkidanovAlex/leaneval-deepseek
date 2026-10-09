import Submission.Work.SSGRoute.E1aClean.BaseChangeResH1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! # `KoverEquiv`: the type identification `↥(Kover L) ≃ ↥K`

The two coercion paths of the base-changed top field (`↥(Kover L)` vs `↥K`) are *not* defeq —
exactly the phenomenon that made `Kover_coe` refuse `rfl` and that blocked the naive statement of
`res_galOIncl` (`NOTE_levelChangeRoute.md` §2g(3)).  This file supplies the identification
memberwise, as the identity on the underlying elements of `Ω`: the two subtypes have the same
carrier, so both directions are `x ↦ ⟨x.1, x.2⟩` and the round-trips are `rfl`. -/

namespace Work.SSGRoute.E1aClean

open CategoryTheory SSGRoute.PTExt

noncomputable section

variable {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω]
variable {K : IntermediateField k Ω}

/-- **The identification of the two coercion paths of the base-changed top field**, as an
equivalence of types (the identity on the underlying elements of `Ω`). -/
def KoverEquiv (L : IntermediateField k K) : ↥(Kover L) ≃ ↥K where
  toFun x := ⟨x.1, x.2⟩
  invFun y := ⟨y.1, y.2⟩
  left_inv x := rfl
  right_inv y := rfl

@[simp] theorem KoverEquiv_apply (L : IntermediateField k K) (x : ↥(Kover L)) :
    ((KoverEquiv L x : ↥K) : Ω) = (x : Ω) := rfl

@[simp] theorem KoverEquiv_symm_apply (L : IntermediateField k K) (y : ↥K) :
    (((KoverEquiv L).symm y : ↥(Kover L)) : Ω) = (y : Ω) := rfl

/-! ## Test: is the structure compatibility `rfl` under the memberwise map?

The coercion path does not bite for the *membership* predicate (that is `Kover`'s `carrier` by
definition).  The question for the group-level conjugation is whether it also does not bite for the
*operations* (multiplication, and the scalar action on the `Ω`-elements).  If these two `example`s
close by `rfl`, the `AlgEquiv`/`MulEquiv` version of the identification is free too. -/

example (L : IntermediateField k K) (x y : ↥(Kover L)) :
    ((KoverEquiv L (x * y) : ↥K)) = KoverEquiv L x * KoverEquiv L y := rfl

example (L : IntermediateField k K) (c : ↥L) (x : ↥(Kover L)) :
    ((KoverEquiv L (c • x) : ↥K)) = c • KoverEquiv L x := rfl

end

end Work.SSGRoute.E1aClean
