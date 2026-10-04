import Mathlib
import Submission.Work.Diff.STE.B3.SymCalcStep8.localInvKit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3.SymCalcStep8

open Set Filter

/-- **A smooth map with non-vanishing Jacobian determinant on an open set is an open map there.**

`θ` is strictly differentiable at every point of `S` (`ContDiffAt.hasStrictFDerivAt`), and at such a
point a non-vanishing determinant makes the derivative an invertible continuous linear map
(`lidCleOfDetNeZero`), so the inverse function theorem says that `θ` maps neighbourhoods of `z` onto
neighbourhoods of `θ z` (`HasStrictFDerivAt.map_nhds_eq_of_equiv`).  Since `S` is a neighbourhood of
`z`, its image is a neighbourhood of `θ z`; a set that is a neighbourhood of each of its points is
open. -/
theorem isOpen_image_of_det_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (θ : (ι → ℝ) → (ι → ℝ)) (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (S : Set (ι → ℝ)) (hS : IsOpen S)
    (hdet : ∀ z ∈ S, (fderiv ℝ θ z).det ≠ 0) :
    IsOpen (θ '' S) := by
  have hn : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨z, hzS, rfl⟩
  -- `θ` is strictly differentiable at `z`, with invertible derivative
  have hst : HasStrictFDerivAt θ (fderiv ℝ θ z) z :=
    (hθ.contDiffAt (x := z)).hasStrictFDerivAt hn
  have hst' : HasStrictFDerivAt θ (lidCleOfDetNeZero (fderiv ℝ θ z) (hdet z hzS) :
      (ι → ℝ) →L[ℝ] (ι → ℝ)) z := by
    rw [lidCleOfDetNeZero_coe]; exact hst
  -- the inverse function theorem: `θ` maps `nhds z` onto `nhds (θ z)`
  have hmap := hst'.map_nhds_eq_of_equiv
  rw [← hmap, Filter.mem_map]
  exact mem_of_superset (hS.mem_nhds hzS) (Set.subset_preimage_image θ S)

end Work.Diff.STE.B3.SymCalcStep8
