import Submission.Work.SSGRoute.E1aClean.BaseChangeKoverEquiv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! # `KoverAlgEquiv`: the `↥L`-algebra identification `↥K ≃ₐ[↥L] ↥(Kover L)`

Stone two of §2g(3).  The memberwise map `x ↦ ⟨x.1, x.2⟩` of `BaseChangeKoverEquiv` is not only a
type equivalence but a `↥L`-algebra equivalence: by the `rfl` tests recorded there, multiplication
and the `↥L`-scalar action are both `rfl`-compatible, so every obligation here is `rfl`. -/

namespace Work.SSGRoute.E1aClean

open CategoryTheory SSGRoute.PTExt

noncomputable section

variable {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω]
variable {K : IntermediateField k Ω}

/-- **Stone two**: the two coercion paths of the base-changed top field agree as `↥L`-algebras. -/
def KoverAlgEquiv (L : IntermediateField k K) : ↥K ≃ₐ[↥L] ↥(Kover L) where
  toFun x := KoverEquiv L ⟨x.1, x.2⟩
  invFun y := (KoverEquiv L).symm y
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp] theorem KoverAlgEquiv_apply (L : IntermediateField k K) (x : ↥K) :
    ((KoverAlgEquiv L x : ↥(Kover L)) : Ω) = (x : Ω) := rfl

/-- The inverse is the memberwise map in the other direction. -/
@[simp] theorem KoverAlgEquiv_symm_apply (L : IntermediateField k K) (y : ↥(Kover L)) :
    (((KoverAlgEquiv L).symm y : ↥K) : Ω) = (y : Ω) := rfl

end

end Work.SSGRoute.E1aClean
