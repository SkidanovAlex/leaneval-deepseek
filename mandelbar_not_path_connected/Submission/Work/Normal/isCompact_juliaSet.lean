import Mathlib
import Submission.Work.Normal.Basic
import Submission.Work.Normal.Frontier
import Submission.Work.Normal.JuliaBasics

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Normal

open Set Filter Topology Function
open scoped Topology Polynomial

/-- If `R ≥ 2` is an escape radius for `f` (`2 * ‖z‖ ≤ ‖f z‖` whenever `R ≤ ‖z‖`) then the
filled Julia set is contained in the closed disk of radius `R`, and hence so is the Julia set,
which is its boundary. -/
theorem juliaSet_subset_closedBall_of_escapeRadius {d : ℕ} {f : ℂ → ℂ} {R : ℝ} (hd : 2 ≤ d)
    (hf : IsPolynomialMapOfDegree d f) (hR2 : 2 ≤ R)
    (hR : ∀ z : ℂ, R ≤ ‖z‖ → 2 * ‖z‖ ≤ ‖f z‖) :
    JuliaSet f ⊆ Metric.closedBall (0 : ℂ) R := by
  have hKsub : FilledJuliaSet f ⊆ Metric.closedBall (0 : ℂ) R := by
    rw [escapeRadius_filledJulia_eq (f := f) hR2 hR]
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    simpa using hz 0
  calc JuliaSet f = frontier (FilledJuliaSet f) := juliaSet_eq_frontier hd hf
    _ ⊆ closure (FilledJuliaSet f) := frontier_subset_closure
    _ ⊆ closure (Metric.closedBall (0 : ℂ) R) := closure_mono hKsub
    _ = Metric.closedBall (0 : ℂ) R := Metric.isClosed_closedBall.closure_eq

/-- The Julia set of a polynomial map of degree at least two is compact (it is a closed subset of
the compact filled Julia set). -/
theorem isCompact_juliaSet {d : ℕ} {f : ℂ → ℂ} (hd : 2 ≤ d)
    (hf : IsPolynomialMapOfDegree d f) : IsCompact (JuliaSet f) := by
  obtain ⟨R, hR2, hR, -, -, -, -, -⟩ := escapeRadius hd hf
  exact (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset (isClosed_juliaSet f)
    (juliaSet_subset_closedBall_of_escapeRadius hd hf hR2 hR)

end Work.Normal
