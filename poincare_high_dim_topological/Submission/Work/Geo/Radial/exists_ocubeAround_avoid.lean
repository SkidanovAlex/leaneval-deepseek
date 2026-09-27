import Mathlib
import Submission.Work.Geo.Radial.Basic

namespace Work.Geo.Radial

open Set Metric
open Work.Geo.Radial

/-- Upgrading point-avoidance to neighbourhood-avoidance: if a continuous map `ĝ` from the
closed unit disc in `ℝ^{j+1}` into a Hausdorff space `M` misses the chart image of a point
`q` of the open unit cube, then it misses the chart image of a whole sup-norm cube around `q`.
(Prove the elementary "Euclidean ball contains a sup-norm cube" step inline.) -/
theorem exists_ocubeAround_avoid {n j : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    (c : PL.CubeChart n M)
    (ĝ : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin (j + 1))) 1, M))
    {q : EuclideanSpace ℝ (Fin n)} (hq : q ∈ PL.openCube (n := n) 1)
    (hav : c.toFun q ∉ Set.range ĝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ u : Metric.closedBall (0 : EuclideanSpace ℝ (Fin (j + 1))) 1,
      ĝ u ∉ c.toFun '' ocubeAround q ε := by
  classical
  -- The disc is compact, so the image of `ĝ` is compact, hence closed in the Hausdorff
  -- space `M` (`↥(closedBall 0 1)` is a compact space).
  have hKclosed : IsClosed (Set.range ĝ) := (isCompact_range ĝ.continuous).isClosed
  -- `c.toFun q` lies in the open complement of the image.
  have hcompl : (Set.range ĝ)ᶜ ∈ nhds (c.toFun q) :=
    hKclosed.isOpen_compl.mem_nhds hav
  -- The chart is continuous at `q`, so the preimage of that complement is a neighbourhood
  -- of `q`; it contains a Euclidean ball of some radius `δ > 0`.
  have hopen : IsOpen (PL.openCube (n := n) 1) := by
    rw [← ocubeAround_zero]; exact isOpen_ocubeAround 0 1
  have hcontAt : ContinuousAt c.toFun q := c.cont.continuousAt (hopen.mem_nhds hq)
  have hpre : c.toFun ⁻¹' (Set.range ĝ)ᶜ ∈ nhds q := hcontAt.preimage_mem_nhds hcompl
  obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhds_iff.mp hpre
  -- A sup-norm cube of radius `δ / (√n + 1)` is contained in the Euclidean ball of
  -- radius `δ` around `q`.
  refine ⟨δ / (Real.sqrt n + 1), ?_, ?_⟩
  · positivity
  · intro u ⟨y, hy, hyeq⟩
    have hyball : y ∈ Metric.ball q δ := by
      rw [Metric.mem_ball, dist_eq_norm]
      have hbound : ‖y - q‖ ≤ Real.sqrt n * (δ / (Real.sqrt n + 1)) :=
        norm_le_sqrt_mul_of_abs_le fun i => le_of_lt (hy i)
      have hlt : Real.sqrt n * (δ / (Real.sqrt n + 1)) < δ := by
        have hden : 0 < Real.sqrt n + 1 := by positivity
        have h1 : Real.sqrt n / (Real.sqrt n + 1) < 1 := div_lt_one hden |>.mpr (lt_add_one _)
        have h2 : Real.sqrt n * (δ / (Real.sqrt n + 1))
            = δ * (Real.sqrt n / (Real.sqrt n + 1)) := by ring
        rw [h2]
        calc δ * (Real.sqrt n / (Real.sqrt n + 1)) < δ * 1 := mul_lt_mul_of_pos_left h1 hδpos
          _ = δ := mul_one δ
      linarith
    exact (hδsub hyball) (hyeq ▸ Set.mem_range_self u)

end Work.Geo.Radial
