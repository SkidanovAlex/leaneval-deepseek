import Submission.FUP.HSGainStep

open FractalUncertainty MeasureTheory FourierTransform Metric Filter Set Pointwise
open scoped ENNReal BigOperators Topology ContDiff

set_option autoImplicit false
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-!
# Han–Schlag's §5, step 11: the tails of the cut-off vanish

The tails `∫_{‖w‖ ≥ R_T} φ` of the cut-off tend to `0` as the threshold `R_T → ∞` (dominated
convergence), so the parameter `T` can be chosen so that both the lower-bound defect `tailMass`
and the upper-bound constant `eUp` are as small as we please.
-/

namespace Submission.FUP

/-- The tail integrals `∫_{‖w‖ ≥ R_T} φ` vanish when `R_T → ∞`. -/
lemma tendsto_tailSet (Φ : FupCutoff d) {R : ℕ → ℝ} (hR : Tendsto R atTop atTop) :
    Tendsto (fun T : ℕ => ∫ w in {w : ℝᵈ | R T ≤ ‖w‖}, Φ.reFun w) atTop (𝓝 0) := by
  rw [show (fun T : ℕ => ∫ w in {w : ℝᵈ | R T ≤ ‖w‖}, Φ.reFun w)
      = fun T : ℕ => ∫ w : ℝᵈ,
          ({w : ℝᵈ | R T ≤ ‖w‖}.indicator (fun w => Φ.reFun w)) w from
    funext fun T => (integral_indicator (measurableSet_le measurable_const measurable_norm)).symm]
  have hbound : ∀ᵐ w ∂(volume : Measure ℝᵈ), Tendsto
      (fun T : ℕ => ({w : ℝᵈ | R T ≤ ‖w‖}.indicator (fun w => Φ.reFun w)) w)
      atTop (𝓝 0) := by
    refine Filter.Eventually.of_forall fun w => ?_
    have hev : ∀ᶠ T : ℕ in atTop, w ∉ {v : ℝᵈ | R T ≤ ‖v‖} := by
      filter_upwards [hR.eventually_gt_atTop ‖w‖] with T hT
      simp only [Set.mem_setOf_eq, not_le]
      exact hT
    refine (tendsto_const_nhds (x := (0:ℝ))).congr' (hev.mono fun T hT => ?_)
    exact (Set.indicator_of_notMem hT (fun _ => Φ.reFun w)).symm
  have hmain := tendsto_integral_of_dominated_convergence (μ := (volume : Measure ℝᵈ))
    (f := fun _ : ℝᵈ => (0:ℝ)) (fun w => ‖Φ.reFun w‖)
    (fun T => (Φ.continuous_reFun.measurable.indicator
      (measurableSet_le measurable_const measurable_norm)).aestronglyMeasurable)
    Φ.integrable_reFun.norm ?_ hbound
  · simpa only [integral_zero] using hmain
  · intro T
    filter_upwards with w
    by_cases hw : w ∈ {v : ℝᵈ | R T ≤ ‖v‖}
    · rw [Set.indicator_of_mem hw]
    · rw [Set.indicator_of_notMem hw, norm_zero]
      positivity

/-- The thresholds `c L^{T-1}` tend to `+∞`. -/
lemma tendsto_threshold {L : ℕ} (hL : 1 < L) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun T : ℕ => c * (L : ℝ) ^ (T - 1)) atTop atTop := by
  have hL1 : (1:ℝ) < (L:ℝ) := by exact_mod_cast hL
  have hLpos : (0:ℝ) < (L:ℝ) := by linarith
  have hLne : (L : ℝ) ≠ 0 := ne_of_gt hLpos
  have hfrac : (fun T : ℕ => (L:ℝ)^T * (L:ℝ)⁻¹) =ᶠ[atTop] fun T : ℕ => (L:ℝ)^(T-1) := by
    filter_upwards [eventually_ge_atTop 1] with T hT
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : T ≠ 0) with ⟨k, rfl⟩
    rw [Nat.succ_sub_one, pow_succ, mul_assoc, mul_inv_cancel₀ hLne, mul_one]
  refine Tendsto.congr' ?_ (((tendsto_pow_atTop_atTop_of_one_lt hL1).atTop_mul_const
    (inv_pos.mpr hLpos)).const_mul_atTop hc)
  filter_upwards [hfrac] with T hT
  simpa only [] using congrArg (fun x => c * x) hT

lemma tendsto_tail_integral {L : ℕ} (hL : 1 < L) {c : ℝ} (hc : 0 < c) (Φ : FupCutoff d) :
    Tendsto (fun T : ℕ => ∫ w in {w : ℝᵈ | c * (L : ℝ) ^ (T - 1) ≤ ‖w‖}, Φ.reFun w)
      atTop (𝓝 0) :=
  tendsto_tailSet Φ (tendsto_threshold hL hc)

/-- Both tails can be made arbitrarily small. -/
theorem exists_T_tails_le {L : ℕ} (hL : 1 < L) (Φ : FupCutoff d) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 1 ≤ T ∧ tailMass Φ L T ≤ ε ∧ eUp Φ L T ≤ ε := by
  have h1 : Tendsto (fun T : ℕ => tailMass Φ L T) atTop (𝓝 0) := by
    have hR : Tendsto (fun T : ℕ => (L:ℝ)^(T-1)/10) atTop atTop := by
      refine (tendsto_threshold hL (c := (10:ℝ)⁻¹) (by norm_num)).congr' ?_
      filter_upwards with T
      rw [div_eq_mul_inv, mul_comm]
    have h := tendsto_tailSet Φ hR
    simpa only [tailMass] using h
  have h2 : Tendsto (fun T : ℕ => eUp Φ L T) atTop (𝓝 0) := by
    have hR : Tendsto (fun T : ℕ => 2 * (L:ℝ)^(T-1)/5) atTop atTop := by
      refine (tendsto_threshold hL (c := (2/5:ℝ)) (by norm_num)).congr' ?_
      filter_upwards with T
      rw [div_eq_mul_inv]
      ring
    have h := tendsto_tailSet Φ hR
    simpa only [eUp] using h
  have hev1 : ∀ᶠ T : ℕ in atTop, tailMass Φ L T ≤ ε :=
    ((tendsto_order.1 h1).2 _ hε).mono fun T hT => le_of_lt hT
  have hev2 : ∀ᶠ T : ℕ in atTop, eUp Φ L T ≤ ε :=
    ((tendsto_order.1 h2).2 _ hε).mono fun T hT => le_of_lt hT
  obtain ⟨T, hT1, hT2, hT3⟩ := (hev1.and (hev2.and (eventually_ge_atTop 1))).exists
  exact ⟨T, hT3, hT1, hT2⟩

end Submission.FUP
