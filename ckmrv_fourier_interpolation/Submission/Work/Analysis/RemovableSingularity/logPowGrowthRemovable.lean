import Mathlib

set_option linter.unusedVariables false

namespace Work.Analysis.RemovableSingularity

open Filter Topology Asymptotics
open scoped Topology

/-- Elementary inequality: for real `N ≥ 0` and `u ≥ 0`, `(1 + u)^N ≤ 2^N (1 + u^N)`. -/
private lemma rpow_one_add_le_two_rpow_mul (N u : ℝ) (hN : 0 ≤ N) (hu : 0 ≤ u) :
    (1 + u) ^ N ≤ 2 ^ N * (1 + u ^ N) := by
  rcases le_or_gt 1 u with h | h
  · have h1 : 1 + u ≤ 2 * u := by linarith
    calc (1 + u) ^ N ≤ (2 * u) ^ N := Real.rpow_le_rpow (by linarith) h1 hN
      _ = 2 ^ N * u ^ N := Real.mul_rpow (by norm_num) hu
      _ ≤ 2 ^ N * (1 + u ^ N) := by
          apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by norm_num) N)
          linarith [Real.rpow_nonneg hu N]
  · have h1 : 1 + u ≤ 2 := by linarith
    have h2 : (1 + u) ^ N ≤ 2 ^ N := Real.rpow_le_rpow (by linarith) h1 hN
    have h4 : (1 : ℝ) ≤ 1 + u ^ N := by linarith [Real.rpow_nonneg hu N]
    have hp : (0:ℝ) < 2 ^ N := Real.rpow_pos_of_pos (by norm_num) N
    nlinarith

/-- `|log t|^N * t → 0` as `t → 0⁺`, for every real exponent `N`.  This is the
logarithmic-domination statement `|log t|^N = o(t^{-1})`. -/
private lemma tendsto_abs_log_rpow_mul (N : ℝ) :
    Tendsto (fun t : ℝ => |Real.log t| ^ N * t) (𝓝[>] 0) (𝓝 0) := by
  have h := (isLittleO_abs_log_rpow_rpow_nhdsGT_zero N (by norm_num : (-1:ℝ) < 0)).tendsto_div_nhds_zero
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hpow : t ^ (-1:ℝ) = t⁻¹ := by rw [Real.rpow_neg ht.le, Real.rpow_one]
  rw [hpow, div_inv_eq_mul]

/-- Auxiliary real-analytic limit: for real constants `C`, `D` and exponent `N ≥ 0`,
`t ↦ (C * (1 + |log t|)^N + D) * t` tends to `0` as `t → 0⁺`.  This is the quantitative
content of the fact that a power of a logarithm is dominated by `t`. -/
private lemma tendsto_one_add_abs_log_pow_mul (C D N : ℝ) (hN : 0 ≤ N) :
    Tendsto (fun t : ℝ => (C * (1 + |Real.log t|) ^ N + D) * t) (𝓝[>] 0) (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => |Real.log t| ^ N * t) (𝓝[>] 0) (𝓝 0) :=
    tendsto_abs_log_rpow_mul N
  have hid : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have h2 : Tendsto (fun t : ℝ => (1 + |Real.log t| ^ N) * t) (𝓝[>] 0) (𝓝 0) := by
    have h := hid.add h1
    simpa [add_mul, one_mul] using h
  have h3 : Tendsto (fun t : ℝ => 2 ^ N * ((1 + |Real.log t| ^ N) * t)) (𝓝[>] 0) (𝓝 0) := by
    simpa using h2.const_mul (2 ^ N)
  have hupper : ∀ᶠ t : ℝ in 𝓝[>] 0,
      (1 + |Real.log t|) ^ N * t ≤ 2 ^ N * ((1 + |Real.log t| ^ N) * t) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hb := rpow_one_add_le_two_rpow_mul N |Real.log t| hN (abs_nonneg _)
    calc (1 + |Real.log t|) ^ N * t ≤ (2 ^ N * (1 + |Real.log t| ^ N)) * t :=
          mul_le_mul_of_nonneg_right hb ht.le
      _ = 2 ^ N * ((1 + |Real.log t| ^ N) * t) := by ring
  have hlower : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 ≤ (1 + |Real.log t|) ^ N * t := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have : (0:ℝ) ≤ 1 + |Real.log t| := by linarith [abs_nonneg (Real.log t)]
    exact mul_nonneg (Real.rpow_nonneg this N) ht.le
  have hmain : Tendsto (fun t : ℝ => (1 + |Real.log t|) ^ N * t) (𝓝[>] 0) (𝓝 0) :=
    squeeze_zero' hlower hupper h3
  have hC' : Tendsto (fun t : ℝ => C * ((1 + |Real.log t|) ^ N * t)) (𝓝[>] 0) (𝓝 0) := by
    simpa using hmain.const_mul C
  have hD : Tendsto (fun t : ℝ => D * t) (𝓝[>] 0) (𝓝 0) := by
    simpa using hid.const_mul D
  have hcd := hC'.add hD
  simpa [add_mul, mul_assoc] using hcd

/-- **Removable singularity under polynomial logarithmic growth.**  A function holomorphic on a
punctured disc `0 < ‖z‖ < ρ`, whose growth at `0` is at most a power of `|log ‖z‖|` (hence slower
than any negative power of `‖z‖`), extends holomorphically across `0`.

This is `Work.Analysis.RemovableSingularity.logGrowthRemovable` with `ρ` and the exponent `N`
generalised; the proof is the same, the only new input being
`(fun t ↦ (1 + |log t|)^N * t) → 0` as `t → 0⁺`. -/
theorem logPowGrowthRemovable {G : ℂ → ℂ} {ρ C N : ℝ} (hρ : 0 < ρ) (hC : 0 ≤ C) (hN : 0 ≤ N)
    (hG : DifferentiableOn ℂ G (Metric.ball 0 ρ \ {0}))
    (hgr : ∀ q : ℂ, q ≠ 0 → ‖q‖ < ρ → ‖G q‖ ≤ C * (1 + |Real.log ‖q‖|) ^ N) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (Metric.ball 0 ρ) ∧
      ∀ q : ℂ, q ≠ 0 → ‖q‖ < ρ → F q = G q := by
  -- Eventually in a punctured neighbourhood of `0` we have `z ≠ 0` and `‖z‖ < ρ`.
  have hev : ∀ᶠ z : ℂ in 𝓝[≠] (0:ℂ), z ≠ 0 ∧ ‖z‖ < ρ := by
    have hball : Metric.ball (0:ℂ) ρ ∈ 𝓝[≠] (0:ℂ) :=
      nhdsWithin_le_nhds (Metric.isOpen_ball.mem_nhds (by simpa [Metric.mem_ball] using hρ))
    filter_upwards [self_mem_nhdsWithin, hball] with z hz hzb
    exact ⟨hz, by simpa [Metric.mem_ball, dist_eq_norm] using hzb⟩
  -- Pointwise logarithmic bound on `‖(G z - G 0) * z‖`.
  have hbound : ∀ᶠ z : ℂ in 𝓝[≠] (0:ℂ),
      ‖(G z - G 0) * z‖ ≤ (C * (1 + |Real.log ‖z‖|) ^ N + ‖G 0‖) * ‖z‖ := by
    filter_upwards [hev] with z hz
    obtain ⟨hz0, hzlt⟩ := hz
    calc
      ‖(G z - G 0) * z‖ = ‖G z - G 0‖ * ‖z‖ := norm_mul _ _
      _ ≤ (‖G z‖ + ‖G 0‖) * ‖z‖ :=
          mul_le_mul_of_nonneg_right (norm_sub_le _ _) (norm_nonneg _)
      _ ≤ (C * (1 + |Real.log ‖z‖|) ^ N + ‖G 0‖) * ‖z‖ :=
          mul_le_mul_of_nonneg_right (add_le_add (hgr z hz0 hzlt) le_rfl) (norm_nonneg _)
  -- The comparison function tends to `0`.
  have htend : Tendsto (fun z : ℂ => (C * (1 + |Real.log ‖z‖|) ^ N + ‖G 0‖) * ‖z‖)
      (𝓝[≠] (0:ℂ)) (𝓝 0) := by
    simpa [Function.comp_def] using
      (tendsto_one_add_abs_log_pow_mul C ‖G 0‖ N hN).comp (tendsto_norm_nhdsNE_zero (E := ℂ))
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
      (Metric.isOpen_ball.mem_nhds (by simpa [Metric.mem_ball] using hρ)) hG hlittle
  · intro q hq _hqlt
    exact Function.update_of_ne hq _ _

end Work.Analysis.RemovableSingularity
