import Mathlib
import Submission.Work.Cohomology.Chains

namespace Work.Cohomology

open CategoryTheory AlgebraicTopology

/-- The transposed singular differentials compose to zero, so that they define a cochain complex:
the `R`-dual of the singular chain complex. -/
theorem dualDifferential_comp (R : Type) [CommRing R] (X : TopCat) (n : ℕ) :
    Work.Cohomology.dualDifferential R X n ≫ Work.Cohomology.dualDifferential R X (n + 1) = 0 := by
  -- The underlying linear maps of the two differentials are `f ↦ f ∘ d_{n+1,n}` and
  -- `g ↦ g ∘ d_{n+2,n+1}`; their composite is `f ↦ f ∘ (d_{n+1,n} ∘ d_{n+2,n+1}) = 0`
  -- because the singular chain complex is a complex.
  have htotal : ((singularChains R X).d (n + 1) n).hom.comp
      ((singularChains R X).d ((n + 1) + 1) (n + 1)).hom = 0 := by
    rw [← ModuleCat.hom_comp, ← ModuleCat.hom_zero]
    exact congrArg ModuleCat.Hom.hom
      (HomologicalComplex.d_comp_d (singularChains R X) ((n + 1) + 1) (n + 1) n)
  have key : ∀ y : (singularChains R X).X ((n + 1) + 1),
      ((singularChains R X).d (n + 1) n).hom
        (((singularChains R X).d ((n + 1) + 1) (n + 1)).hom y) = 0 := by
    intro y
    have h := LinearMap.congr_fun htotal y
    simpa [LinearMap.comp_apply] using h
  apply ModuleCat.hom_ext
  simp only [ModuleCat.hom_comp, ModuleCat.hom_zero, dualDifferential, ModuleCat.hom_ofHom]
  ext f x
  change f (((singularChains R X).d (n + 1) n).hom
      (((singularChains R X).d ((n + 1) + 1) (n + 1)).hom x)) = 0
  rw [key x]
  exact map_zero f

end Work.Cohomology
