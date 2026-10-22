import Mathlib

namespace Work.CWIND.BFun

open CategoryTheory CategoryTheory.Limits

/-- A morphism out of the coproduct `∐_j ℤ` of copies of `ℤ` (indexed by an arbitrary type `J`)
into a module `N` is determined by the images of the canonical generators `ι j 1`.

Indeed, the inclusions `ι j : ℤ ⟶ ∐_j ℤ` exhibit `∐_j ℤ` as a colimit, so two morphisms agree as
soon as they agree after precomposition with each `ι j`; and a morphism `ℤ ⟶ N` is determined by the
image of `1`. -/
theorem sigmaIotaApplyInjective (J : Type) (N : ModuleCat.{0} ℤ) :
    Function.Injective (fun (χ : (∐ fun _ : J => ModuleCat.of ℤ ℤ) ⟶ N) =>
      fun j : J => χ (CategoryTheory.Limits.Sigma.ι (fun _ : J => ModuleCat.of ℤ ℤ) j 1)) := by
  intro χ₁ χ₂ h
  -- Two morphisms out of the coproduct agree once they agree after precomposition with the
  -- coproduct inclusions.
  apply Cofan.IsColimit.hom_ext (coproductIsCoproduct (fun _ : J => ModuleCat.of ℤ ℤ))
  intro j
  -- It remains to compare the two maps `ℤ ⟶ N`, and these are determined by the image of `1`.
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  simpa using congrFun h j

end Work.CWIND.BFun
