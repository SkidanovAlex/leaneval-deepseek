import Mathlib
import Submission.Work.Serre.Basic

/-!
# `H₀(X;ℚ) ≅ ℚ` for a path-connected space

The zeroth singular homology `H₀(X;R)` of a space is the free `R`-module on `π₀(X)`, the set of
path components of `X`; Mathlib records this as
`TopCat.singularHomology₀Iso : H₀(X;R) ≅ ∐ (fun _ : ZerothHomotopy X ↦ R)` together with the
augmentation `TopCat.singularHomology₀ε : H₀(X;R) ⟶ R`, which is the sum of the coefficients on
each component.  If `X` is path-connected (in particular nonempty) there is exactly one path
component, so the augmentation is an isomorphism: this is Mathlib's instance
`TopCat.instIsIsoSingularHomology₀ε` (`[PathConnectedSpace X] : IsIso (X.singularHomology₀ε R)`).

The only point to be careful about is that the workspace's `ratH (TopCat.of X) 0` is *definitionally*
`((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) 0).obj (ModuleCat.of ℚ ℚ)).obj
(TopCat.of X)` (`ratChains` is the singular chain complex functor, and `ratH` its homology), so
the Mathlib augmentation of that object is the augmentation of `ratH (TopCat.of X) 0`.  Likewise
`PathConnectedSpace (TopCat.of X)` has to be provided by hand from `PathConnectedSpace X`
(instance search does not see through `TopCat.of`), hence the `haveI`.

## Main result

* `Work.Serre.ratH_zero_of_pathConnected` — `H₀(X;ℚ) ≅ ℚ` for path-connected `X`.
-/

namespace Work.Serre

open CategoryTheory CategoryTheory.Limits

/-- **The zeroth rational homology of a path-connected space is `ℚ`.** -/
theorem ratH_zero_of_pathConnected (X : Type) [TopologicalSpace X] [PathConnectedSpace X] :
    Nonempty (Work.Serre.ratH (TopCat.of X) 0 ≅ ModuleCat.of ℚ ℚ) := by
  -- `TopCat.of X` does not inherit `PathConnectedSpace X` by instance search (the carrier is only
  -- definitionally `X`), so provide it explicitly: this is what unlocks Mathlib's instance
  -- "the augmentation `H₀(X;R) → R` is an isomorphism for a path-connected `X`".
  haveI hpc : PathConnectedSpace (TopCat.of X) := ‹PathConnectedSpace X›
  have hε : IsIso (TopCat.singularHomology₀ε (C := ModuleCat ℚ) (TopCat.of X)
      (ModuleCat.of ℚ ℚ)) := inferInstance
  -- `ratH (TopCat.of X) 0` is definitionally the source of `singularHomology₀ε`, so the
  -- augmentation itself is the required isomorphism.
  exact ⟨@asIso (ModuleCat ℚ) _ (Work.Serre.ratH (TopCat.of X) 0) (ModuleCat.of ℚ ℚ)
    (TopCat.singularHomology₀ε (C := ModuleCat ℚ) (TopCat.of X) (ModuleCat.of ℚ ℚ)) hε⟩

end Work.Serre
