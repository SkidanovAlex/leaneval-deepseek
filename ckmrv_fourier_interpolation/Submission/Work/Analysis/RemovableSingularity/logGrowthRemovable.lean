import Mathlib

namespace Work.Analysis.RemovableSingularity

open Filter Topology Asymptotics
open scoped Topology

/-- Auxiliary real-analytic limit: for real constants `C`, `D`, the function
`t ↦ (C * (1 + |log t|) + D) * t` tends to `0` as `t → 0⁺`.  This is the
quantitative content of the fact that `t * log t → 0` at `0⁺`. -/
lemma tendsto_one_add_abs_log_mul (C D : ℝ) :
    Tendsto (fun t : ℝ => (C * (1 + |Real.log t|) + D) * t) (𝓝[>] 0) (𝓝 0) := by
  have hlog : Tendsto (fun t : ℝ => Real.log t * t) (𝓝[>] 0) (𝓝 0) := by
    have h := tendsto_log_mul_rpow_nhdsGT_zero (r := 1) one_pos
    simpa using h
  have habs : Tendsto (fun t : ℝ => |Real.log t| * t) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => |Real.log t * t|) (𝓝[>] 0) (𝓝 0) := by
      simpa using hlog.abs
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [abs_mul]
    congr 1
    exact abs_of_pos ht
  have hid : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have h2 : Tendsto (fun t : ℝ => t + |Real.log t| * t) (𝓝[>] 0) (𝓝 0) := by
    simpa using hid.add habs
  have h3 : Tendsto (fun t : ℝ => (1 + |Real.log t|) * t) (𝓝[>] 0) (𝓝 0) := by
    simpa [add_mul, one_mul] using h2
  have h4 : Tendsto (fun t : ℝ => C * ((1 + |Real.log t|) * t) + D * t) (𝓝[>] 0) (𝓝 0) := by
    simpa using (h3.const_mul C).add (hid.const_mul D)
  simpa only [add_mul, mul_assoc] using h4

/-- **Removable singularity under logarithmic growth.**  A function holomorphic on the punctured
unit disk whose growth at `0` is at most logarithmic (hence slower than any negative power of
`|z|`) extends holomorphically across `0`.

Equivalently: `|G z| ≤ C (1 + |log |z||)` forces `z ↦ (z - 0) G z` to converge to `0` at `0`,
which is exactly the hypothesis of Riemann's removable singularity theorem. -/
theorem logGrowthRemovable {G : ℂ → ℂ}
    (hG : DifferentiableOn ℂ G (Metric.ball 0 1 \ {0}))
    (hgr : ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℂ, q ≠ 0 → ‖q‖ < 1 → ‖G q‖ ≤ C * (1 + |Real.log ‖q‖|)) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (Metric.ball 0 1) ∧ ∀ q : ℂ, q ≠ 0 → ‖q‖ < 1 → F q = G q := by
  obtain ⟨C, _hC, hCb⟩ := hgr
  -- Eventually in a punctured neighbourhood of `0` we have `z ≠ 0` and `‖z‖ < 1`.
  have hev : ∀ᶠ z : ℂ in 𝓝[≠] (0:ℂ), z ≠ 0 ∧ ‖z‖ < 1 := by
    have hball : Metric.ball (0:ℂ) 1 ∈ 𝓝[≠] (0:ℂ) :=
      nhdsWithin_le_nhds (Metric.isOpen_ball.mem_nhds (by simp))
    filter_upwards [self_mem_nhdsWithin, hball] with z hz hzb
    exact ⟨hz, by simpa [Metric.mem_ball, dist_eq_norm] using hzb⟩
  -- Pointwise logarithmic bound on `‖(G z - G 0) * z‖`.
  have hbound : ∀ᶠ z : ℂ in 𝓝[≠] (0:ℂ),
      ‖(G z - G 0) * z‖ ≤ (C * (1 + |Real.log ‖z‖|) + ‖G 0‖) * ‖z‖ := by
    filter_upwards [hev] with z hz
    obtain ⟨hz0, hzlt⟩ := hz
    calc
      ‖(G z - G 0) * z‖ = ‖G z - G 0‖ * ‖z‖ := norm_mul _ _
      _ ≤ (‖G z‖ + ‖G 0‖) * ‖z‖ :=
          mul_le_mul_of_nonneg_right (norm_sub_le _ _) (norm_nonneg _)
      _ ≤ (C * (1 + |Real.log ‖z‖|) + ‖G 0‖) * ‖z‖ :=
          mul_le_mul_of_nonneg_right (add_le_add (hCb z hz0 hzlt) le_rfl) (norm_nonneg _)
  -- The comparison function tends to `0`.
  have htend : Tendsto (fun z : ℂ => (C * (1 + |Real.log ‖z‖|) + ‖G 0‖) * ‖z‖)
      (𝓝[≠] (0:ℂ)) (𝓝 0) := by
    simpa [Function.comp_def] using
      (tendsto_one_add_abs_log_mul C ‖G 0‖).comp (tendsto_norm_nhdsNE_zero (E := ℂ))
  have hsq : Tendsto (fun z : ℂ => ‖(G z - G 0) * z‖) (𝓝[≠] (0:ℂ)) (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun z => norm_nonneg _) hbound htend
  have hmain : Tendsto (fun z : ℂ => (G z - G 0) * z) (𝓝[≠] (0:ℂ)) (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hsq
  -- Translate into the little-o hypothesis of Riemann's removable singularity theorem.
  have hlittle : (fun z : ℂ => G z - G 0) =o[𝓝[≠] (0:ℂ)] (fun z => (z - 0)⁻¹) := by
    refine (isLittleO_iff_tendsto ?_).mpr ?_
    · intro z hz
      have hz0 : z = 0 := sub_eq_zero.mp (inv_eq_zero.mp hz)
      simp [hz0]
    · show Tendsto (fun z : ℂ => (G z - G 0) / (z - 0)⁻¹) (𝓝[≠] (0:ℂ)) (𝓝 0)
      simpa only [div_inv_eq_mul, sub_zero] using hmain
  refine ⟨Function.update G 0 ((𝓝[≠] (0:ℂ)).limUnder G), ?_, ?_⟩
  · exact Complex.differentiableOn_update_limUnder_of_isLittleO
      (Metric.isOpen_ball.mem_nhds (by simp)) hG hlittle
  · intro q hq _hqlt
    exact Function.update_of_ne hq _ _

end Work.Analysis.RemovableSingularity
