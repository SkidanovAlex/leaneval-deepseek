import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassCHon.SliceMassAux

open MeasureTheory Filter Topology

theorem continuousOn_of_integral_bound {m Φ : ℝ → ℝ}
    (hΦ : MeasureTheory.IntegrableOn Φ (Set.Ioi (0 : ℝ))) (hnn : ∀ z, 0 ≤ Φ z)
    (h : ∀ z₁ z₂ : ℝ, 0 < z₁ → z₁ ≤ z₂ →
      |m z₂ - m z₁| ≤ ∫ s in z₁..z₂, Φ s) :
    ContinuousOn m (Set.Ioi (0 : ℝ)) := by
  intro x hx
  have hx0 : 0 < x := hx
  -- The primitive of `Φ` is continuous at `x`.
  have hsub : Set.uIcc (x / 2) (2 * x) ⊆ Set.Ioi 0 := by
    intro y hy
    rw [Set.mem_Ioi]
    rcases Set.mem_uIcc.mp hy with ⟨h1, -⟩ | ⟨h1, h2⟩
    · linarith
    · linarith
  have hint : IntervalIntegrable Φ volume (x / 2) (2 * x) :=
    MeasureTheory.IntegrableOn.intervalIntegrable (hΦ.mono_set hsub)
  have hcw : ContinuousWithinAt (fun b => ∫ s in x..b, Φ s) (Set.Icc (x / 2) (2 * x)) x := by
    refine intervalIntegral.continuousWithinAt_primitive (μ := volume) (f := Φ)
      (a := x) (b₀ := x) (b₁ := x / 2) (b₂ := 2 * x) ?_ ?_
    · exact Real.volume_singleton
    · rw [min_eq_right (by linarith : x / 2 ≤ x), max_eq_right (by linarith : x ≤ 2 * x)]
      exact hint
  have hcAt : ContinuousAt (fun b => ∫ s in x..b, Φ s) x :=
    hcw.continuousAt (Icc_mem_nhds (by linarith) (by linarith))
  have hcwI : ContinuousWithinAt (fun b => ∫ s in x..b, Φ s) (Set.Ioi 0) x :=
    hcAt.continuousWithinAt
  have htend : Tendsto (fun b => ∫ s in x..b, Φ s) (𝓝[Set.Ioi (0:ℝ)] x) (𝓝 0) := by
    simpa using hcwI.tendsto
  have hlimAbs : Tendsto (fun y => |∫ s in x..y, Φ s|) (𝓝[Set.Ioi (0:ℝ)] x) (𝓝 0) := by
    simpa using htend.abs
  -- The pointwise bound.
  have hbound : ∀ y, 0 < y → |m y - m x| ≤ |∫ s in x..y, Φ s| := by
    intro y hy
    rcases le_or_gt x y with hxy | hyx
    · refine le_trans (h x y hx0 hxy) ?_
      exact le_of_eq (abs_of_nonneg (intervalIntegral.integral_nonneg_of_forall hxy hnn)).symm
    · have h1 : |m y - m x| ≤ ∫ s in y..x, Φ s := by
        have := h y x hy hyx.le
        rwa [abs_sub_comm] at this
      refine le_trans h1 ?_
      rw [intervalIntegral.integral_symm x y]
      exact neg_le_abs _
  have hev : ∀ᶠ y in 𝓝[Set.Ioi (0:ℝ)] x, |m y - m x| ≤ |∫ s in x..y, Φ s| := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact hbound y hy
  have hm : Tendsto (fun y => |m y - m x|) (𝓝[Set.Ioi (0:ℝ)] x) (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall (fun y => abs_nonneg _)) hev hlimAbs
  show Tendsto m (𝓝[Set.Ioi (0:ℝ)] x) (𝓝 (m x))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa [Real.norm_eq_abs] using hm

end Work.FTS.ClassCHon.SliceMassAux
