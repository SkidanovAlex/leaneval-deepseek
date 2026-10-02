import Mathlib
import Submission.Work.Tubular.DiscManifold.Defs
import Submission.Work.SignatureBordism.BallBoundary

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Smoothness of the preferred chart of the closed ball, read on the model space

The preferred chart `chartAt (Half n) b` of the closed ball `Ball n = D^{n+1}` at a point `b`
(the `ChartedSpace` structure `Work.SignatureBordism.ballChartedSpace`) is either

* the centre chart `interiorChart n`, whose forward formula is
  `v ↦ consCLM (max (v 0 + 1/2) 0) (tail v)` (the translation `v ↦ v + (1/2) e₀` on its source), or
* a half-ball chart `halfChart n i ε`, whose forward formula is the radial "flattening"
  `v ↦ consCLM (1 - ‖v‖) (tail (permIso i v))`.

Both formulas are smooth on the ambient region where they are used: the translation on
`{v | -(1/2) < v 0}` and the flattening on `{v | v ≠ 0 ⊆ ...}` (`contDiffOn_halfToFunE`, which
needs `v ≠ 0` because of the norm).  Reading the forward chart on the model space through the total
map `Work.Tubular.discPt` (which sends a vector outside the ball to `0`), this gives the smoothness
of

`v ↦ ((chartAt (Half n) b (discPt n v)).val)`

on `{v | v ∈ Ball n ∧ discPt n v ∈ (chartAt (Half n) b).source}`.

This is the companion of `Work.Tubular.DiscManifold.contDiffOn_ballChartAt_symm` (the inverse chart
read on the model space), and is one of the analytic inputs of the tubular-neighbourhood
construction of the disc manifold.
-/

open scoped Manifold ContDiff Topology

namespace Work.Tubular.DiscManifold

open Work.SignatureBordism

/-- **Smoothness of the centre chart read on the model space.**  On the region
`{v | -(1/2) < v 0}` the formula `interiorToFunE n` is the translation `v ↦ v + shiftE n`. -/
theorem contDiffOn_interiorToFunE (n : ℕ) :
    ContDiffOn ℝ ⊤ (fun v : EuclideanSpace ℝ (Fin (n + 1)) => interiorToFunE n v)
      {v : EuclideanSpace ℝ (Fin (n + 1)) | -(1 / 2 : ℝ) < v 0} :=
  ((contDiff_id.add contDiff_const).contDiffOn).congr
    (fun _v hv => interiorToFunE_eq_of_pos n hv)

theorem contDiffOn_ballChartAt (n : ℕ) (b : Work.SignatureBordism.Ball n) :
    ContDiffOn ℝ 1
      (fun v : EuclideanSpace ℝ (Fin (n + 1)) =>
        ((chartAt (Work.SignatureBordism.Half n) b (Work.Tubular.discPt n v) : Work.SignatureBordism.Half n).val))
      {v : EuclideanSpace ℝ (Fin (n + 1)) |
        v ∈ Work.SignatureBordism.Ball n ∧ Work.Tubular.discPt n v ∈ (chartAt (Work.SignatureBordism.Half n) b).source} := by
  classical
  set S : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
    {v | v ∈ Ball n ∧ discPt n v ∈ (chartAt (Half n) b).source} with hS
  by_cases hb : b ∈ interiorSource n
  · -- The preferred chart is the centre chart: the formula is the translation `v ↦ v + shiftE n`.
    have hchart : chartAt (Half n) b = interiorChart n := ballChartAt_of_mem n hb
    have hsrc : S ⊆ {v : EuclideanSpace ℝ (Fin (n + 1)) | -(1 / 2 : ℝ) < v 0} := by
      intro v hv
      have hmem : discPt n v ∈ (interiorChart n).source := by rw [← hchart]; exact hv.2
      rw [interiorChart_source] at hmem
      rw [discPt_of_mem n hv.1] at hmem
      exact hmem.1
    have hbase : ContDiffOn ℝ 1 (fun v : EuclideanSpace ℝ (Fin (n + 1)) => interiorToFunE n v) S :=
      (contDiffOn_interiorToFunE n).mono hsrc |>.of_le le_top
    refine hbase.congr (fun v hv => ?_)
    rw [hchart, discPt_of_mem n hv.1]
    rfl
  · -- The preferred chart is a half-ball chart: the formula is smooth off the origin, and the
    -- source of the half-ball chart excludes the origin.
    obtain ⟨i, s, hchart⟩ : ∃ (i : Fin (n + 1)) (s : Bool),
        chartAt (Half n) b = halfChart n i s :=
      ⟨ballCoord n b (ball_ne_zero_of_not_mem n hb),
        decide (0 < (b : EuclideanSpace ℝ (Fin (n + 1)))
          (ballCoord n b (ball_ne_zero_of_not_mem n hb))), by
        have h1 : chartAt (Half n) b = ballChartAt n b := rfl
        rw [h1, ballChartAt_of_not_mem n hb]
        rfl⟩
    have hne : S ⊆ {v : EuclideanSpace ℝ (Fin (n + 1)) | v ≠ 0} := by
      intro v hv
      have hmem : discPt n v ∈ (halfChart n i s).source := by rw [← hchart]; exact hv.2
      rw [halfChart_source, halfSource, Set.mem_ofPred_eq] at hmem
      rw [discPt_of_mem n hv.1] at hmem
      exact ne_zero_of_apply_ne (ne_zero_of_bsign_mul_pos hmem)
    have hbase : ContDiffOn ℝ 1 (fun v : EuclideanSpace ℝ (Fin (n + 1)) => halfToFunE n i s v) S :=
      (contDiffOn_halfToFunE n i s).mono hne |>.of_le le_top
    refine hbase.congr (fun v hv => ?_)
    rw [hchart, discPt_of_mem n hv.1]
    exact halfChart_apply n i s ⟨v, hv.1⟩

end Work.Tubular.DiscManifold
