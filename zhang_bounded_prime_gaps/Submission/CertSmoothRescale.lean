import Submission.CertSmoothRatio
import Submission.Rescale

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

open scoped BigOperators Topology
open Filter Finset MeasureTheory

/-!
# The rescaled smoothed certificate: a continuous competitor of the sieve

`Submission/CertSmoothRatio.lean` produces a smoothed certificate whose quotient exceeds any
threshold below the certificate's, and `Submission/Rescale.lean`'s
`exists_ratioScale_rescale_gt` (Polymath8a §5.1/§5.3) turns such a quotient into a *rescaled*
function whose **sieve-scale** quotient `ratioScale 50 (24/25·ϑ/2)` exceeds `1`.

This module assembles the two: it produces an explicit continuous, compactly supported
competitor supported in the `λ·(26/25)`-simplex whose sieve-scale quotient exceeds `1` — the
quantitative input of the tensor localisation `exists_tensorData_thin` and of
`hkey_of_thin_tensorData`.
-/

namespace Commons.NumberTheory.MaynardSieve

noncomputable section

theorem exists_certPoly_bound' :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ simplexC 50 ((26 : ℝ) / 25), |certPoly t| ≤ B := by
  obtain ⟨B, hB⟩ := exists_certPoly_bound
  exact ⟨max B 0, le_max_right _ _, fun t ht => le_trans (hB t ht) (le_max_left _ _)⟩

/-- For a marginal point outside the marginal simplex of the certificate, the whole line
`x ↦ extendAt i x t'` lies outside the certificate simplex. -/
theorem certSmooth_extendAt_eq_zero_of_notMem_marg (i : Fin 50) {γ : ℝ} (hγ : 0 < γ)
    {t' : {j : Fin 50 // j ≠ i} → ℝ} (ht' : t' ∉ marginalSet 50 i ((26 : ℝ) / 25)) (x : ℝ) :
    certSmooth γ (extendAt i x t') = 0 := by
  refine certSmooth_support hγ ?_
  simp only [marginalSet, Set.mem_ofPred_eq, not_and_or] at ht'
  rcases ht' with h | h
  · push Not at h
    obtain ⟨j, hj⟩ := h
    intro hmem
    have h1 := hmem.1 j
    rw [extendAt, dif_neg j.2] at h1
    linarith
  · intro hmem
    have h2 := hmem.2
    rw [sum_extendAt] at h2
    have h3 : (0 : ℝ) ≤ x := hmem.1 i |>.trans_eq (by rw [extendAt, dif_pos rfl])
    have h4 : (0 : ℝ) ≤ ∑ j : {l : Fin 50 // l ≠ i}, t' j := by linarith
    linarith

/-- **The squared line integrals of the smoothed certificate are integrable.** -/
theorem integrable_line_integral_sq (i : Fin 50) {γ : ℝ} (hγ : 0 < γ) :
    Integrable (fun t' : {j : Fin 50 // j ≠ i} → ℝ =>
      (∫ x : ℝ, certSmooth γ (extendAt i x t')) ^ 2) volume := by
  obtain ⟨B, hB0, hB⟩ := exists_certPoly_bound'
  set C : ℝ := (B * ((26 : ℝ) / 25)) ^ 2 with hC
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  have hbd : Integrable (fun t' : {j : Fin 50 // j ≠ i} → ℝ =>
      (marginalSet 50 i ((26 : ℝ) / 25)).indicator (fun _ => C) t') volume := by
    rw [integrable_indicator_iff (measurableSet_marginalSet 50 i ((26 : ℝ) / 25))]
    exact integrableOn_const (ne_of_lt (volume_marginalSet_lt_top ((26 : ℝ) / 25) i))
  refine Integrable.mono' hbd ?_ ?_
  · -- measurability of the squared line integral
    have hcont : Continuous (Function.uncurry (fun (t' : {j : Fin 50 // j ≠ i} → ℝ) (x : ℝ) =>
        certSmooth γ (extendAt i x t'))) := by
      refine (continuous_certSmooth hγ).comp ?_
      refine continuous_pi (fun j => ?_)
      by_cases hj : j = i
      · simp only [Function.uncurry_apply_pair, extendAt, dif_pos hj]
        exact continuous_snd
      · simp only [Function.uncurry_apply_pair, extendAt, dif_neg hj]
        exact (continuous_apply (⟨j, hj⟩ : {l : Fin 50 // l ≠ i})).comp continuous_fst
    exact ((StronglyMeasurable.integral_prod_right hcont.stronglyMeasurable).pow 2).aestronglyMeasurable
  · filter_upwards with t'
    rw [Real.norm_eq_abs]
    by_cases ht' : t' ∈ marginalSet 50 i ((26 : ℝ) / 25)
    · rw [Set.indicator_of_mem ht']
      have hle : |∫ x : ℝ, certSmooth γ (extendAt i x t')| ≤ B * ((26 : ℝ) / 25) :=
        abs_integral_certSmooth_le i t' hγ hB hB0
      rw [abs_of_nonneg (sq_nonneg _), hC, ← sq_abs (∫ x : ℝ, certSmooth γ (extendAt i x t'))]
      exact pow_le_pow_left₀ (abs_nonneg _) hle 2
    · rw [Set.indicator_of_notMem ht']
      have hz : (∫ x : ℝ, certSmooth γ (extendAt i x t')) = 0 := by
        rw [show (fun x : ℝ => certSmooth γ (extendAt i x t')) = fun _ => (0 : ℝ) from
          funext (fun x => certSmooth_extendAt_eq_zero_of_notMem_marg i hγ ht' x)]
        simp
      simp [hz]

theorem JFunc_nonneg (k : ℕ) (i : Fin k) (c : ℝ) (F : (Fin k → ℝ) → ℝ) :
    0 ≤ JFunc k i c F := by
  classical
  unfold JFunc
  refine integral_nonneg_of_ae ?_
  filter_upwards with t'
  by_cases h : t' ∈ marginalSet k i c
  · simp only [h, ↓reduceIte, mul_one]
    exact sq_nonneg _
  · simp [h]

/-- **The continuous, compactly supported competitor of the sieve.**  Its support lies in the
`λ·(26/25)`-simplex and its sieve-scale quotient exceeds `1`. -/
theorem exists_smooth_competitor {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : 2 / ϑ < (4001 : ℝ) / 1000) :
    ∃ (F : (Fin 50 → ℝ) → ℝ) (lam : ℝ), 0 < lam ∧ lam ≤ ϑ / 2 ∧
      Continuous F ∧ HasCompactSupport F ∧
      (∀ t : Fin 50 → ℝ, t ∉ simplexSet 50 (lam * ((26 : ℝ) / 25)) → F t = 0) ∧
      (1 : ℝ) < ratioScale 50 (((24 : ℝ) / 25) * (ϑ / 2)) F := by
  have hthr : 2 / ϑ
      < (∑ i : Fin 50, JFunc 50 i ((24 : ℝ) / 25) certFun) / IFuncOrth 50 certFun := by
    rw [div_lt_iff₀ hϑ]
    have h2 : (2 : ℝ) / ϑ * ϑ < ((4001 : ℝ) / 1000) * ϑ := mul_lt_mul_of_pos_right hϑ' hϑ
    rw [div_mul_cancel₀ _ (ne_of_gt hϑ)] at h2
    have h3 : ((4001 : ℝ) / 1000) * ϑ
        < ((∑ i : Fin 50, JFunc 50 i ((24 : ℝ) / 25) certFun) / IFuncOrth 50 certFun) * ϑ :=
      mul_lt_mul_of_pos_right cert_ratio_gt_sharp hϑ
    linarith
  obtain ⟨γ, hγ, hratio⟩ := exists_certSmooth_ratio_gt_of_lt hthr
  have hJ0 : (0 : ℝ) ≤ ∑ i : Fin 50, JFunc 50 i ((24 : ℝ) / 25) (certSmooth γ) :=
    Finset.sum_nonneg (fun i _ => JFunc_nonneg 50 i _ _)
  have hI : 0 < IFuncOrth 50 (certSmooth γ) := by
    by_contra hcon
    push Not at hcon
    rcases lt_or_eq_of_le hcon with hlt | heq
    · have hle : (∑ i : Fin 50, JFunc 50 i ((24 : ℝ) / 25) (certSmooth γ))
          / IFuncOrth 50 (certSmooth γ) ≤ 0 :=
        div_nonpos_of_nonneg_of_nonpos hJ0 (le_of_lt hlt)
      have hpos : 0 < 2 / ϑ := div_pos (by norm_num) hϑ
      linarith
    · rw [heq, div_zero] at hratio
      have hpos : 0 < 2 / ϑ := div_pos (by norm_num) hϑ
      linarith
  have hratio' : 2 * 1 / ϑ < ratioScale 50 (1 - (1 : ℝ) / 25) (certSmooth γ) := by
    rw [show (1 : ℝ) - 1 / 25 = 24 / 25 from by norm_num]
    simpa [one_mul, ratioScale] using hratio
  obtain ⟨lam, hlam0, hlamle, hsieve⟩ :=
    exists_ratioScale_rescale_gt (k := 50) (ε := (1 : ℝ) / 25) (ϑ := ϑ) (m := 1) hϑ one_pos
      (by norm_num : (1 : ℝ) / 25 ≤ 1) (certSmooth γ) hI hratio'
      (fun i => integrable_line_integral_sq i hγ)
  refine ⟨rescale lam (certSmooth γ), lam, hlam0, hlamle, ?_, ?_, ?_, ?_⟩
  · -- continuity
    refine (continuous_certSmooth hγ).comp ?_
    refine continuous_pi (fun j => ?_)
    exact ((continuous_apply j : Continuous fun t : Fin 50 → ℝ => t j)).div_const lam
  · -- compact support
    have hsupp : ∀ s : Fin 50 → ℝ, s ∉ simplexSet 50 ((26 : ℝ) / 25) → certSmooth γ s = 0 :=
      fun s hs => certSmooth_support hγ (by simpa [simplexC_eq_simplexSet] using hs)
    refine HasCompactSupport.of_support_subset_isCompact
      (isCompact_simplexC 50 (lam * ((26 : ℝ) / 25))) (fun t ht => ?_)
    simp only [Function.mem_support] at ht
    rw [simplexC_eq_simplexSet]
    by_contra hcon
    exact ht (rescale_eq_zero_of_notMem lam ((26 : ℝ) / 25) hlam0 hsupp hcon)
  · -- support
    have hsupp : ∀ s : Fin 50 → ℝ, s ∉ simplexSet 50 ((26 : ℝ) / 25) → certSmooth γ s = 0 :=
      fun s hs => certSmooth_support hγ (by simpa [simplexC_eq_simplexSet] using hs)
    intro t ht
    exact rescale_eq_zero_of_notMem lam ((26 : ℝ) / 25) hlam0 hsupp (by simpa using ht)
  · -- the sieve-scale quotient
    have h : (1 : ℝ) - 1 / 25 = 24 / 25 := by norm_num
    rwa [h] at hsieve

end

end Commons.NumberTheory.MaynardSieve

