import Mathlib
import Submission.Work.GM.Affine.region_II_vocab
import Submission.Work.GM.Affine.window_integral_Bsum
import Submission.Work.GM.Affine.tsum_resonance_eq_finsum
import Submission.Work.GM.Affine.finset_sum_window_le_WinMass
import Submission.Work.GM.Affine.resonant_count_good
import Submission.Work.GM.Affine.region_II_resonant_high_defs
import Submission.Work.GM.Affine.supf_le_of_decay
import Submission.Work.GM.Affine.resHigh_ghatRes_sq_le
import Submission.Work.GM.Affine.resMajorant_integral_le
import Submission.Work.GM.Affine.window_mass_le_WinMass

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.GM.Affine

noncomputable section

/-! ## Auxiliary facts used in the high part of region II -/

/-- A constant dominating `‖psi1hat K‖`, from the faster-than-polynomial decay of `ψ̂₁`. -/
lemma exists_psi1hat_bound_high (K : ℝ) (hK : 0 < K) :
    ∃ V : ℝ, 0 < V ∧ ∀ y : ℝ, ‖psi1hat K y‖ ≤ V := by
  obtain ⟨V, hVpos, hV⟩ := psi1hat_decay K hK 0
  exact ⟨V, hVpos, fun y => by have h := hV y; rwa [pow_zero, div_one] at h⟩

/-- `Bsum f M₂` is continuous for continuous compactly supported `f`. -/
lemma resHigh_continuous_Bsum {M₂ : ℝ} {f : ℝ → ℝ} (hf : Continuous f)
    (hcs : HasCompactSupport f) :
    Continuous (fun u : ℝ => Bsum f M₂ u) := by
  unfold Bsum
  refine continuous_finsetSum _ (fun m₂ _ => ?_)
  exact continuous_const.mul ((continuous_fhat hf hcs).comp (continuous_const.mul continuous_id))

/-- `resMajorant` is measurable (it is a finite sum of window indicators times continuous
functions). -/
lemma resHigh_measurable_resMajorant (M₁ M₂ M₃ T : ℝ) {f : ℝ → ℝ} (hf : Continuous f)
    (hcs : HasCompactSupport f) : Measurable (resMajorant M₁ M₂ M₃ T f) := by
  have hunfold : resMajorant M₁ M₂ M₃ T f = fun ξ : ℝ =>
      ∑ p ∈ (R1 M₁).product (Finset.Icc (-(⌈T ^ 6⌉ + 2)) (⌈T ^ 6⌉ + 2)),
        (if |(p.2 : ℝ) - ξ / (p.1 : ℝ)| ≤ 2 / M₃ then
          (1 / (p.1 : ℝ) ^ 2) * ‖Bsum f M₂ (ξ / (p.1 : ℝ))‖ ^ 2 else 0) := by
    funext ξ; rw [resMajorant]
  rw [hunfold]
  refine Finset.measurable_sum _ (fun p hp => ?_)
  refine Measurable.ite ?_ ?_ measurable_const
  · exact measurableSet_le (by fun_prop) measurable_const
  · exact (continuous_const.mul (((resHigh_continuous_Bsum hf hcs).comp
      (continuous_id.div_const _)).norm.pow 2)).measurable

/-- Dropping the window indicators only increases the majorant. -/
lemma resHigh_resMajorant_le (M₁ M₂ M₃ T : ℝ) (f : ℝ → ℝ) (ξ : ℝ) :
    resMajorant M₁ M₂ M₃ T f ξ ≤
      ∑ p ∈ resPairs M₁ T, (1 / (p.1 : ℝ) ^ 2) * ‖Bsum f M₂ (ξ / (p.1 : ℝ))‖ ^ 2 := by
  rw [resMajorant, resPairs]
  refine Finset.sum_le_sum (fun p hp => ?_)
  by_cases h : |(p.2 : ℝ) - ξ / (p.1 : ℝ)| ≤ 2 / M₃
  · simp only [h, if_true]
    exact le_rfl
  · simp only [h, if_false]
    positivity

/-- `resMajorant` is integrable on the (bounded) region: it is dominated by a finite sum of
continuous functions. -/
lemma resHigh_resMajorant_integrable {M₁ M₂ M₃ T : ℝ} {f : ℝ → ℝ} (hf : Continuous f)
    (hcs : HasCompactSupport f) :
    IntegrableOn (resMajorant M₁ M₂ M₃ T f) (resRegion T M₁ M₃) volume := by
  have hbigcont : Continuous (fun ξ : ℝ =>
      ∑ p ∈ resPairs M₁ T, (1 / (p.1 : ℝ) ^ 2) * ‖Bsum f M₂ (ξ / (p.1 : ℝ))‖ ^ 2) := by
    refine continuous_finsetSum _ (fun p _ => ?_)
    exact continuous_const.mul (((resHigh_continuous_Bsum hf hcs).comp
      (continuous_id.div_const _)).norm.pow 2)
  have hsub : resRegion T M₁ M₃ ⊆ Set.Icc (-(T ^ 6)) (T ^ 6) := by
    intro ξ hξ
    rw [resRegion, Set.mem_sdiff, Set.mem_Icc] at hξ
    exact Set.mem_Icc.mpr ⟨hξ.1.1, hξ.1.2⟩
  have hbigint : IntegrableOn (fun ξ : ℝ =>
      ∑ p ∈ resPairs M₁ T, (1 / (p.1 : ℝ) ^ 2) * ‖Bsum f M₂ (ξ / (p.1 : ℝ))‖ ^ 2)
      (resRegion T M₁ M₃) volume :=
    (hbigcont.continuousOn.integrableOn_compact isCompact_Icc).mono_set hsub
  refine Integrable.mono' hbigint
    ((resHigh_measurable_resMajorant M₁ M₂ M₃ T hf hcs).aestronglyMeasurable) ?_
  filter_upwards with ξ
  have hnn : 0 ≤ resMajorant M₁ M₂ M₃ T f ξ := by
    rw [resMajorant]
    refine Finset.sum_nonneg (fun p hp => ?_)
    by_cases h : |(p.2 : ℝ) - ξ / (p.1 : ℝ)| ≤ 2 / M₃
    · simp only [h, if_true]; positivity
    · simp only [h, if_false, le_refl]
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  exact resHigh_resMajorant_le M₁ M₂ M₃ T f ξ

/-- **Region II of GM Lemma 9.2, the high part (`|ξ| > 4M₁/M₃`).**

Strategy: (i) rewrite the `∑'_ℓ` inside `ghatRes` as the finite sum over `Icc (-⌈T⁶⌉-2) (⌈T⁶⌉+2)`
(this is `tsum_resonance_eq_finsum`, using `|ξ| ≤ T⁶` and `|m₁| ≥ 1` for `m₁ ∈ R1 M₁`);
(ii) Cauchy-Schwarz over the resonant pair finset with `resonant_count_good` (`ε = δ/6`), which
bounds its cardinality by `C T^δ (1 + M₁/M₃)` because `4M₁/M₃ < |ξ| ≤ T⁶`;
(iii) exchange the finite sum over pairs with the integral, bound `‖ψ̂₁‖ ≤ V`, extend the ξ-integral
of each pair to its full resonant window `[m₁ℓ - 2|m₁|/M₃, m₁ℓ + 2|m₁|/M₃]`, and apply
`window_integral_Bsum` to get `(|m₁|/M₃) ∫_{[-2,2]} ‖Hfun f M₂ M₃ ℓ τ‖² dτ`;
(iv) sum over `ℓ` and use `finset_sum_window_le_WinMass`, and sum over `m₁` with
`sum_inv_abs_R1_le` (`Σ_{m₁∈R1} 1/|m₁| ≤ 8`).
Result: `∫ ≤ 8 C V² T^δ (M₁+M₃) WinMass`. -/
theorem region_II_resonant_high {K : ℝ} (hK : 0 < K) (δ : ℝ) (hδ : 0 < δ)
    (c : ℕ → ℝ → ℝ) :
    ∃ C' : ℝ, 0 < C' ∧
      ∀ (T Λ : ℝ), 1 ≤ T → 0 < Λ → ∀ (M₁ M₂ M₃ : ℝ),
        1 ≤ M₃ → 0 < M₁ → 0 < M₂ →
        ∀ (f : ℝ → ℝ), Continuous f → HasCompactSupport f →
        (∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
          ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ) →
        (∫ ξ in (Set.Icc (-(T ^ 6)) (T ^ 6)) \ (Set.Icc (-(4 * M₁ / M₃)) (4 * M₁ / M₃)),
            ‖ghatRes K M₁ M₂ M₃ f ξ‖ ^ 2) ≤
          C' * T ^ δ * (M₁ + M₃) * WinMass f M₂ M₃ := by
  obtain ⟨V, hVpos, hV⟩ := exists_psi1hat_bound_high K hK
  obtain ⟨C0, hC0pos, hC0⟩ := resonant_count_good (ε := δ / 6) (by linarith)
  refine ⟨8 * C0 * V ^ 2, by positivity, ?_⟩
  intro T Λ hT hΛ M₁ M₂ M₃ hM₃ hM₁ hM₂ f hf hcs hdec
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hM₃pos : 0 < M₃ := lt_of_lt_of_le zero_lt_one hM₃
  have hTd : 0 < T ^ δ := Real.rpow_pos_of_pos hTpos δ
  have hCcup : 0 < 1 + M₁ / M₃ := by positivity
  -- (i)+(ii): pointwise Cauchy–Schwarz bound on the region
  have hpt : ∀ ξ ∈ resRegion T M₁ M₃,
      ‖ghatRes K M₁ M₂ M₃ f ξ‖ ^ 2
        ≤ (C0 * T ^ δ * (1 + M₁ / M₃)) * V ^ 2 * M₃ ^ 2 * resMajorant M₁ M₂ M₃ T f ξ := by
    intro ξ hξ
    rw [resRegion, Set.mem_sdiff, Set.mem_Icc] at hξ
    obtain ⟨⟨hξ1, hξ2⟩, hξ3⟩ := hξ
    have hξabs : |ξ| ≤ T ^ 6 := abs_le.mpr ⟨hξ1, hξ2⟩
    have hξlo : 4 * M₁ / M₃ < |ξ| := by
      rcases not_and_or.mp hξ3 with h | h
      · have h' : ξ < -(4 * M₁ / M₃) := not_le.mp h
        have h2 : 4 * M₁ / M₃ < -ξ := by linarith
        linarith [neg_le_abs ξ]
      · have h' : 4 * M₁ / M₃ < ξ := not_le.mp h
        linarith [le_abs_self ξ]
    have hcard : (((resPairs M₁ T).filter
        (fun p => |(p.2 : ℝ) - ξ / (p.1 : ℝ)| ≤ 2 / M₃)).card : ℝ)
        ≤ C0 * T ^ δ * (1 + M₁ / M₃) := by
      have h := hC0 M₁ M₃ T ξ hM₁ hM₃ hT hξlo hξabs
        (((resPairs M₁ T).filter (fun p => |(p.2 : ℝ) - ξ / (p.1 : ℝ)| ≤ 2 / M₃)))
        (fun p hp => (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1)
        (fun p hp => (Finset.mem_filter.mp hp).2)
      rw [show 6 * (δ / 6) = δ by ring] at h
      exact h
    exact resHigh_ghatRes_sq_le hM₁ hM₃ hT hV hVpos.le (by positivity) hf hcs hξabs hcard
  -- integrability of the dominating function on the region
  have hint : IntegrableOn
      (fun ξ => (C0 * T ^ δ * (1 + M₁ / M₃)) * V ^ 2 * M₃ ^ 2 * resMajorant M₁ M₂ M₃ T f ξ)
      (resRegion T M₁ M₃) volume :=
    ((resHigh_resMajorant_integrable (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) (T := T)
      hf hcs).const_mul _)
  have hSmeas : MeasurableSet (resRegion T M₁ M₃) :=
    measurableSet_Icc.diff measurableSet_Icc
  -- monotonicity of the integral
  have hmono : ∫ ξ in resRegion T M₁ M₃, ‖ghatRes K M₁ M₂ M₃ f ξ‖ ^ 2
      ≤ ∫ ξ in resRegion T M₁ M₃,
          (C0 * T ^ δ * (1 + M₁ / M₃)) * V ^ 2 * M₃ ^ 2 * resMajorant M₁ M₂ M₃ T f ξ := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun ξ => sq_nonneg _)) hint ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hSmeas] with ξ hξ
    exact hpt ξ hξ
  -- (iii)+(iv): the resonant majorant integral
  have hIntRes : ∫ ξ in resRegion T M₁ M₃, resMajorant M₁ M₂ M₃ T f ξ
      ≤ (8 / M₃) * WinMass f M₂ M₃ :=
    resMajorant_integral_le hM₃ hM₁ hf hcs
      (fun s => window_mass_le_WinMass hT hM₂ hM₃ hf hdec s)
  calc ∫ ξ in resRegion T M₁ M₃, ‖ghatRes K M₁ M₂ M₃ f ξ‖ ^ 2
      ≤ ∫ ξ in resRegion T M₁ M₃,
          (C0 * T ^ δ * (1 + M₁ / M₃)) * V ^ 2 * M₃ ^ 2 * resMajorant M₁ M₂ M₃ T f ξ := hmono
    _ = (C0 * T ^ δ * (1 + M₁ / M₃)) * V ^ 2 * M₃ ^ 2
          * ∫ ξ in resRegion T M₁ M₃, resMajorant M₁ M₂ M₃ T f ξ := by
        rw [MeasureTheory.integral_const_mul]
    _ ≤ (C0 * T ^ δ * (1 + M₁ / M₃)) * V ^ 2 * M₃ ^ 2 * ((8 / M₃) * WinMass f M₂ M₃) := by
        apply mul_le_mul_of_nonneg_left hIntRes
        positivity
    _ = 8 * C0 * V ^ 2 * T ^ δ * (M₁ + M₃) * WinMass f M₂ M₃ := by
        field_simp
        ring

end

end Work.GM.Affine
