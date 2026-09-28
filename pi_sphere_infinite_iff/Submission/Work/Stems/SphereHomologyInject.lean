import Mathlib
import Submission.Work.Cohomology.sphereHomologyTop

/-!
# The chosen identification `Hₙ(Sⁿ;ℤ) ≅ ℤ` is injective

`Work.Cohomology.sphereHomologyTop n hn` is a chosen isomorphism `Hₙ(Sⁿ;ℤ) ≅ ℤ`.  Any of its
underlying maps is injective (it is an isomorphism of `ℤ`-modules), which is the form in which the
identification is used when one wants to conclude that a homology class vanishes from the vanishing
of its image under the identification (for instance when converting "the degree of a smooth
self-map of `Sⁿ` is `0`" into the vanishing of its Hurewicz class).
-/

namespace Work.Cohomology

open CategoryTheory

/-- The underlying map of the chosen identification `Hₙ(Sⁿ;ℤ) ≅ ℤ` is injective. -/
theorem sphereHomologyTop_hom_injective (n : ℕ) (hn : 1 ≤ n) :
    Function.Injective (ModuleCat.Hom.hom (Classical.choice
      (sphereHomologyTop n hn)).hom) := by
  have h := congrArg ModuleCat.Hom.hom
    (CategoryTheory.Iso.hom_inv_id (Classical.choice (sphereHomologyTop n hn)))
  rw [ModuleCat.hom_comp, ModuleCat.hom_id] at h
  intro x y hxy
  have hx := LinearMap.congr_fun h x
  have hy := LinearMap.congr_fun h y
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at hx hy
  rw [hxy] at hx
  rw [hy] at hx
  exact hx.symm

end Work.Cohomology
