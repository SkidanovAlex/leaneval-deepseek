import Mathlib
import Submission.Work.Normal.Basic
import Submission.Work.Normal.JuliaBasics
import Submission.Work.Normal.poly_eval_surjective

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Complete invariance of the Fatou and Julia sets of a polynomial map

For a polynomial map `f` of degree `d ≥ 2` the Julia set and the Fatou set are completely
invariant:

`f '' JuliaSet f = JuliaSet f = f ⁻¹' JuliaSet f`,  `f '' FatouSet f = FatouSet f = f ⁻¹' FatouSet f`.

The inclusion `f ⁻¹' JuliaSet f ⊆ JuliaSet f` is `preimage_juliaSet_subset`; the rest follows from
surjectivity of `f` (`poly_eval_surjective`) and the forward invariance `JuliaSet f ⊆ f ⁻¹' JuliaSet f`
(which is the same statement read in the opposite direction).
-/

namespace Work.Normal

open Set Filter Topology Function
open scoped Topology Polynomial

/-- The Julia set of a polynomial map of degree at least two is completely invariant, backward
form: `f ⁻¹' J = J`. -/
theorem preimage_juliaSet_eq {d : ℕ} {f : ℂ → ℂ} (hd : 2 ≤ d)
    (hf : IsPolynomialMapOfDegree d f) : f ⁻¹' (JuliaSet f) = JuliaSet f := by
  refine Subset.antisymm (preimage_juliaSet_subset hd hf) ?_
  intro y hy
  exact mapsTo_juliaSet hd hf hy

/-- The Julia set of a polynomial map of degree at least two is completely invariant, forward
form: `f '' J = J`. -/
theorem image_juliaSet_eq {d : ℕ} {f : ℂ → ℂ} (hd : 2 ≤ d)
    (hf : IsPolynomialMapOfDegree d f) : f '' (JuliaSet f) = JuliaSet f := by
  refine Subset.antisymm ?_ ?_
  · rintro y ⟨x, hx, rfl⟩
    exact mapsTo_juliaSet hd hf hx
  · intro y hy
    obtain ⟨x, rfl⟩ := poly_eval_surjective (by omega : 1 ≤ d) hf y
    exact ⟨x, preimage_juliaSet_subset hd hf hy, rfl⟩

/-- The Fatou set of a polynomial map of degree at least two is backward invariant. -/
theorem preimage_fatouSet_eq {d : ℕ} {f : ℂ → ℂ} (hd : 2 ≤ d)
    (hf : IsPolynomialMapOfDegree d f) : f ⁻¹' (FatouSet f) = FatouSet f := by
  rw [← juliaSet_compl, preimage_compl, preimage_juliaSet_eq hd hf]

/-- The Fatou set of a polynomial map of degree at least two is forward invariant. -/
theorem mapsTo_fatouSet {d : ℕ} {f : ℂ → ℂ} (hd : 2 ≤ d)
    (hf : IsPolynomialMapOfDegree d f) : MapsTo f (FatouSet f) (FatouSet f) := by
  intro z hz
  rw [← preimage_fatouSet_eq hd hf] at hz
  exact hz

/-- The Fatou set of a polynomial map of degree at least two is completely invariant, forward
form: `f '' F = F`. -/
theorem image_fatouSet_eq {d : ℕ} {f : ℂ → ℂ} (hd : 2 ≤ d)
    (hf : IsPolynomialMapOfDegree d f) : f '' (FatouSet f) = FatouSet f := by
  refine Subset.antisymm ?_ ?_
  · rintro y ⟨x, hx, rfl⟩
    exact mapsTo_fatouSet hd hf hx
  · intro y hy
    obtain ⟨x, rfl⟩ := poly_eval_surjective (by omega : 1 ≤ d) hf y
    refine ⟨x, ?_, rfl⟩
    show x ∈ FatouSet f
    rw [← preimage_fatouSet_eq hd hf]
    exact hy

end Work.Normal
