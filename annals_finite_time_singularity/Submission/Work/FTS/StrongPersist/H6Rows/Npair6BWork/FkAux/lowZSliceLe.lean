import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkSliceSup

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

/-- The `η`-weighted radial half of the level-`m` slice sum, `m ≤ 2`, bounded uniformly in `z > 0`
by `9 · HkSq α 4 f`.  Route: `Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkSliceSup_sliceSupGraded`
at `k = 4` applied to the slots `(j,i) = (i,0)` gives `∫_θ sin(2θ)^{-η}(D_z^if z θ)² ≤ 3·HkSq α 4 f`
(`i ≤ 2`, so `i + 0 + 1 ≤ 4`), and
`Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkSliceSup_slice_integrable` gives the
integrability needed to split the integral of the `Finset.range (m+1)`-sum with
`MeasureTheory.integral_finsetSum`; there are `m + 1 ≤ 3` summands, which are nonnegative. -/
theorem lowZSliceLe {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen f)
    (hmem : Work.Spaces.HkMem α 4 f) {m : ℕ} (hm : m ≤ 2) {z : ℝ} (hz : 0 < z) :
    (∫ θ in Work.Spaces.Iθ, ∑ i ∈ Finset.range (m + 1),
        (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.mixed i 0 f z θ) ^ 2)
      ≤ 9 * Work.Spaces.HkSq α 4 f := by
  -- each summand `θ ↦ sin(2θ)^{-η}(D_z^i f z θ)²` (`i ≤ m ≤ 2`) is integrable on `Iθ`
  have hint : ∀ i ∈ Finset.range (m + 1), MeasureTheory.Integrable
      (fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        * (Work.Spaces.mixed i 0 f z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    intro i hi
    have hi2 : i ≤ 2 := by
      have := Finset.mem_range.mp hi
      omega
    exact fkSliceSup_slice_integrable hα hF hmem (j := i) (i := 0) (by omega) hz
  -- and each of them is bounded by `3 · HkSq α 4 f` (the graded slice bound at `k = 4`)
  have hper : ∀ i ∈ Finset.range (m + 1),
      (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        * (Work.Spaces.mixed i 0 f z θ) ^ 2) ≤ 3 * Work.Spaces.HkSq α 4 f := by
    intro i hi
    have hi2 : i ≤ 2 := by
      have := Finset.mem_range.mp hi
      omega
    exact fkSliceSup_sliceSupGraded hα hF hmem i 0 (by omega) z hz
  have hsplit : (∫ θ in Work.Spaces.Iθ, ∑ i ∈ Finset.range (m + 1),
        (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.mixed i 0 f z θ) ^ 2)
      = ∑ i ∈ Finset.range (m + 1),
          ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            * (Work.Spaces.mixed i 0 f z θ) ^ 2 :=
    MeasureTheory.integral_finsetSum (Finset.range (m + 1)) hint
  rw [hsplit]
  have h2 : (∑ i ∈ Finset.range (m + 1),
        ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          * (Work.Spaces.mixed i 0 f z θ) ^ 2)
      ≤ ∑ _i ∈ Finset.range (m + 1), (3 * Work.Spaces.HkSq α 4 f) :=
    Finset.sum_le_sum hper
  have h3 : (∑ _i ∈ Finset.range (m + 1), (3 * Work.Spaces.HkSq α 4 f))
      ≤ 9 * Work.Spaces.HkSq α 4 f := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hcard : ((m + 1 : ℕ) : ℝ) ≤ 3 := by
      exact_mod_cast (by omega : m + 1 ≤ 3)
    nlinarith [Work.Spaces.HkSq_nonneg α 4 f]
  linarith

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
