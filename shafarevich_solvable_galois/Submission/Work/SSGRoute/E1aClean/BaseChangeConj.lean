import Submission.Work.SSGRoute.E1aClean.BaseChangeKoverAlgEquiv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! # The induced conjugation `Gal(↥K/↥L) ≃* Gal(↥(Kover L)/↥L)`

Stone three's first half.  Note (recorded in `NOTE_levelChangeRoute.md` §2g(3)) that `AlgEquiv`'s
`Mul` does **not** compose across the two types, so the conjugation is spelled through
`AlgEquiv.trans` rather than as `e * σ * e.symm`; by the structure-compatibility tests in
`BaseChangeKoverEquiv`/`BaseChangeKoverAlgEquiv` all obligations are `rfl`-level. -/

namespace Work.SSGRoute.E1aClean

open CategoryTheory SSGRoute.PTExt

noncomputable section

variable {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω]
variable {K : IntermediateField k Ω}

/-- **The conjugation of the two automorphism groups by the memberwise identification.** -/
def galKConj (L : IntermediateField k K) :
    (↥K ≃ₐ[↥L] ↥K) ≃* (↥(Kover L) ≃ₐ[↥L] ↥(Kover L)) where
  toFun σ := (KoverAlgEquiv L).symm.trans (σ.trans (KoverAlgEquiv L))
  invFun τ := (KoverAlgEquiv L).trans (τ.trans (KoverAlgEquiv L).symm)
  left_inv σ := AlgEquiv.ext fun _ => rfl
  right_inv τ := AlgEquiv.ext fun _ => rfl
  map_mul' σ τ := AlgEquiv.ext fun _ => rfl

@[simp] theorem galKConj_apply (L : IntermediateField k K) (σ : ↥K ≃ₐ[↥L] ↥K) (x : ↥(Kover L)) :
    (((galKConj L σ) x : ↥(Kover L)) : Ω) = (σ ((KoverAlgEquiv L).symm x) : Ω) := rfl

end

end Work.SSGRoute.E1aClean
