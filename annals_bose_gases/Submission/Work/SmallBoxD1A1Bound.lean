import Mathlib.Tactic.Have
import Mathlib.Analysis.Fourier.Notation
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.SmallBoxD1A1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# SESSION-284 — M2: the D1 `A₁` mode-content bound

FS `lm:appbogolubov` adds `A₁ = (2π)^{-3}K_s a ∫(b_p†b_p + b†_{-p}b_{-p})dp` and estimates it by
`A₁ ≤ K_s a (n₀+1)|B|^{-1} n₊`.  In the corpus the corresponding obligation is

  `(2π)^{-3} ∫_q (P_{u_q} + P_{v_q}) dq ≤ 2 (N̂+1) chiSup² · cnPlus`,

where `P_g = modeP s g Φ = (s³)^{-1}∫_{Λ^N}(boxOp s 1 g Φ)²`, `g_q = qMode s q`,
and `cnPlus` is the number of excited particles.  This module proves that bound.

Route (SESSION-284):
* `boxOp s (fun _ => 1) (qModeRe s q) Φ x = Σ_i ∫_{Λ} qModeRe s q z·Φ(x_{i↦z})dz`
  (`boxOp` is a sum over slots) and each slot integral reduces to the bare `χ`-cosine overlap
  against the EXCITED part `aQ s i Φ` (`qModeRe_slot_eq_cos`);
* Cauchy–Schwarz over the slots + the `χ`-overlap bound (`cos_overlap_sq_integral_le` with the
  pointwise `χ ≤ chiSup`) gives, for every `x`,
  `(2π)^{-3}∫_q (boxOp …)² ≤ (N̂+1)chiSup² Σ_i ∫_{Λ}(aQ s i Φ)(x_{i↦z})²`;
* integrating in `x` and exchanging the `q`- and `x`-integrals (Fubini, the `q`-integrand
  dominated by the uniform decay `K/(1+‖q‖)³` of `exists_qModeRe_mode_bound`) and using the
  torsion identity (`integral_swap_update`) for the slot integral turns the right-hand side into
  `(N̂+1) chiSup² cnPlus`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal FourierTransform

namespace Submission

open _root_.BoseGases
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## 1 The `χ`-sup bound and the overlap estimates -/

/-- `chiSup = (∫χ²)^{-1/2}` is nonnegative. -/
lemma chiSup_nonneg : 0 ≤ chiSup := by
  rw [chiSup]
  exact inv_nonneg.mpr (Real.sqrt_nonneg _)

/-- the pointwise `χ`-bound at its maximum. -/
lemma chiScale_sq_le_chiSup (ℓ : ℝ) (x : ℝ³) : chiScale ℓ x ^ 2 ≤ chiSup ^ 2 := by
  have h1 : 0 ≤ chiScale ℓ x := chiScale_nonneg ℓ x
  have h2 : chiScale ℓ x ≤ chiSup := by
    have h := abs_chiScale_le ℓ x
    rwa [abs_of_nonneg h1] at h
  exact pow_le_pow_left₀ h1 h2 2

/-- **The `χ`-cosine overlap bound with the `χ`-sup.**  For SMOOTH `H`,
`(2π)^{-3}∫_q (∫_{Λ}χ(z)cos⟨q,z⟩H(z)dz)² ≤ chiSup² ∫_{Λ}H²`. -/
theorem cos_overlap_le_chiSup {s : ℝ} (hs : 0 < s) {H : ℝ³ → ℝ}
    (hH : ContDiff ℝ ∞ H) :
    ((2 * π) ^ 3)⁻¹
        * ∫ q, (∫ z in acube s, chiScale s z * Real.cos (inner ℝ q z) * H z) ^ 2
      ≤ chiSup ^ 2 * ∫ z in acube s, H z ^ 2 := by
  refine le_trans (cos_overlap_sq_integral_le hs hH) ?_
  have hsupp : ∀ z : ℝ³, z ∉ acube s → (chiScale s z * H z) ^ 2 = 0 := by
    intro z hz
    have hχ : chiScale s z = 0 := not_ne_iff.mp fun h => hz (chiScale_mem_acube hs h)
    rw [hχ, zero_mul]
    exact zero_pow (by norm_num)
  rw [(setIntegral_eq_integral_of_forall_compl_eq_zero hsupp).symm]
  rw [← MeasureTheory.integral_const_mul]
  have hcont : Continuous fun z : ℝ³ => chiSup ^ 2 * H z ^ 2 :=
    continuous_const.mul (hH.continuous.pow 2)
  refine integral_mono_of_nonneg (Eventually.of_forall fun z => sq_nonneg _)
    (ContinuousOn.integrableOn_compact (acube_compact hs) hcont.continuousOn) ?_
  refine Eventually.of_forall fun z => ?_
  simp only []
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right (chiScale_sq_le_chiSup s z) (sq_nonneg _)

/-- **The `χ`-sine overlap bound with the `χ`-sup.** -/
theorem sin_overlap_le_chiSup {s : ℝ} (hs : 0 < s) {H : ℝ³ → ℝ}
    (hH : ContDiff ℝ ∞ H) :
    ((2 * π) ^ 3)⁻¹
        * ∫ q, (∫ z in acube s, chiScale s z * Real.sin (inner ℝ q z) * H z) ^ 2
      ≤ chiSup ^ 2 * ∫ z in acube s, H z ^ 2 := by
  refine le_trans (sin_overlap_sq_integral_le hs hH) ?_
  have hsupp : ∀ z : ℝ³, z ∉ acube s → (chiScale s z * H z) ^ 2 = 0 := by
    intro z hz
    have hχ : chiScale s z = 0 := not_ne_iff.mp fun h => hz (chiScale_mem_acube hs h)
    rw [hχ, zero_mul]
    exact zero_pow (by norm_num)
  rw [(setIntegral_eq_integral_of_forall_compl_eq_zero hsupp).symm]
  rw [← MeasureTheory.integral_const_mul]
  have hcont : Continuous fun z : ℝ³ => chiSup ^ 2 * H z ^ 2 :=
    continuous_const.mul (hH.continuous.pow 2)
  refine integral_mono_of_nonneg (Eventually.of_forall fun z => sq_nonneg _)
    (ContinuousOn.integrableOn_compact (acube_compact hs) hcont.continuousOn) ?_
  refine Eventually.of_forall fun z => ?_
  simp only []
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right (chiScale_sq_le_chiSup s z) (sq_nonneg _)

/-! ## 2 The slot-integral reductions -/

/-- the `qModeRe` slot integral is the bare `χ`-cosine overlap (all `x`). -/
lemma boxOp_qModeRe_eq_sum {s : ℝ} (hs : 0 < s) {n : ℕ} {Φ : X (n + 1) → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) (x : X (n + 1)) (q : ℝ³) :
    boxOp s (fun _ => (1 : ℝ)) (qModeRe s q) Φ x
      = ∑ i : Fin (n + 1), ∫ z in acube s,
          chiScale s z * Real.cos (inner ℝ q z) * (aQ s i Φ) (Function.update x i z) := by
  rw [show boxOp s (fun _ => (1 : ℝ)) (qModeRe s q) Φ x
      = ∑ i : Fin (n + 1), ∫ z in acube s, qModeRe s q z * Φ (Function.update x i z) from by
    simp only [boxOp, one_mul]]
  exact Finset.sum_congr rfl (fun i _ => qModeRe_slot_eq_cos hs q hΦ i x)

/-- the `qModeIm` slot integral is MINUS the bare `χ`-sine overlap. -/
lemma qModeIm_slot_eq_neg_sin {s : ℝ} (hs : 0 < s) {n : ℕ} (p : ℝ³)
    {Φ : X (n + 1) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (i : Fin (n + 1)) (x : X (n + 1)) :
    (∫ z in acube s, qModeIm s p z * Φ (Function.update x i z))
      = - ∫ z in acube s, chiScale s z * Real.sin (inner ℝ p z)
          * (aQ s i Φ) (Function.update x i z) := by
  rw [slot_eq_excited hs (continuous_qModeIm p) (integral_qModeIm_eq_zero hs p) hΦ i x]
  set H : ℝ³ → ℝ := fun z => (aQ s i Φ) (Function.update x i z) with hH
  have hHc : Continuous H :=
    (contDiff_aQ hs i hΦ).continuous.comp (continuous_const.update i continuous_id)
  have hHmean : (∫ z in acube s, H z) = 0 := aQ_fibre_mean_zero hs hΦ.continuous i x
  have hpt : ∀ z : ℝ³, qModeIm s p z * H z
      = - (chiScale s z * Real.sin (inner ℝ p z) * H z
            + ((s ^ 3)⁻¹ * (modeChat s p).im) * H z) := by
    intro z
    rw [qModeIm_eq]
    ring
  have hc1 : Continuous fun z : ℝ³ => chiScale s z * Real.sin (inner ℝ p z) * H z :=
    ((chiScale_continuous s).mul
      (Real.continuous_sin.comp (continuous_const.inner continuous_id))).mul hHc
  have hc2 : Continuous fun z : ℝ³ => ((s ^ 3)⁻¹ * (modeChat s p).im) * H z :=
    continuous_const.mul hHc
  calc (∫ z in acube s, qModeIm s p z * H z)
      = ∫ z in acube s, - (chiScale s z * Real.sin (inner ℝ p z) * H z
            + ((s ^ 3)⁻¹ * (modeChat s p).im) * H z) :=
        setIntegral_congr_fun (acube_measurable s) (fun z _ => hpt z)
    _ = - (∫ z in acube s, (chiScale s z * Real.sin (inner ℝ p z) * H z
            + ((s ^ 3)⁻¹ * (modeChat s p).im) * H z)) := by
        rw [MeasureTheory.integral_neg]
    _ = - ((∫ z in acube s, chiScale s z * Real.sin (inner ℝ p z) * H z)
            + ∫ z in acube s, ((s ^ 3)⁻¹ * (modeChat s p).im) * H z) := by
        rw [MeasureTheory.integral_add
          (ContinuousOn.integrableOn_compact (acube_compact hs) hc1.continuousOn)
          (ContinuousOn.integrableOn_compact (acube_compact hs) hc2.continuousOn)]
    _ = - ((∫ z in acube s, chiScale s z * Real.sin (inner ℝ p z) * H z)
            + ((s ^ 3)⁻¹ * (modeChat s p).im) * ∫ z in acube s, H z) := by
        rw [MeasureTheory.integral_const_mul]
    _ = - ∫ z in acube s, chiScale s z * Real.sin (inner ℝ p z) * H z := by
        rw [hHmean, mul_zero, add_zero]

/-- the `qModeIm` analogue of `boxOp_qModeRe_eq_sum`. -/
lemma boxOp_qModeIm_eq_sum {s : ℝ} (hs : 0 < s) {n : ℕ} {Φ : X (n + 1) → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) (x : X (n + 1)) (q : ℝ³) :
    boxOp s (fun _ => (1 : ℝ)) (qModeIm s q) Φ x
      = - ∑ i : Fin (n + 1), ∫ z in acube s,
          chiScale s z * Real.sin (inner ℝ q z) * (aQ s i Φ) (Function.update x i z) := by
  rw [show boxOp s (fun _ => (1 : ℝ)) (qModeIm s q) Φ x
      = ∑ i : Fin (n + 1), ∫ z in acube s, qModeIm s q z * Φ (Function.update x i z) from by
    simp only [boxOp, one_mul]]
  rw [Finset.sum_congr rfl (fun i _ => qModeIm_slot_eq_neg_sin hs q hΦ i x),
    Finset.sum_neg_distrib]

/-! ## 3 The torsion (slot-swap) identity for the excited fibre -/

/-- **The torsion identity.**  `∫_x ∫_z G(x_{i↦z}) = s³ ∫_x G x` over the box. -/
lemma abox_slot_swap_eq {s : ℝ} (hs : 0 < s) {n : ℕ} (i : Fin (n + 1))
    {G : X (n + 1) → ℝ} (hG : Continuous G) :
    (∫ x in abox (n + 1) s, ∫ z in acube s, G (Function.update x i z))
      = s ^ 3 * ∫ x in abox (n + 1) s, G x := by
  have hG' : Continuous fun p : X (n + 1) × ℝ³ => G (Function.update p.1 i p.2) :=
    hG.comp (continuous_fst.update i continuous_snd)
  have hsw := integral_swap_update (s := s) hs (n := n) i
    (G := fun x z => G (Function.update x i z)) hG'
  rw [hsw]
  have hfix : ∀ x : X (n + 1), ∀ z : ℝ³,
      Function.update (Function.update x i z) i (x i) = x := by
    intro x z
    rw [Function.update_idem, Function.update_eq_self]
  have hconst : ∀ x : X (n + 1),
      (∫ z in acube s, G (Function.update (Function.update x i z) i (x i)))
        = s ^ 3 * G x := by
    intro x
    have : (fun z : ℝ³ => G (Function.update (Function.update x i z) i (x i)))
        = fun _ : ℝ³ => G x := by
      funext z; rw [hfix]
    rw [this, MeasureTheory.setIntegral_const, Measure.real_def, acube_volume s hs.le,
      ENNReal.toReal_ofReal (by positivity)]
    rw [smul_eq_mul]
  rw [show (∫ x in abox (n + 1) s,
        ∫ z in acube s, G (Function.update (Function.update x i z) i (x i)))
      = ∫ x in abox (n + 1) s, s ^ 3 * G x from
    integral_congr_ae (Eventually.of_forall hconst)]
  rw [MeasureTheory.integral_const_mul]

/-! ## 4 The per-`x` mode bound -/

/-- the model `(1+‖q‖)^{-6}` is integrable in `ℝ³`. -/
lemma integrable_one_add_norm_six_r3 :
    Integrable (fun q : ℝ³ => (1 + ‖q‖) ^ (-(6 : ℝ))) volume :=
  integrable_one_add_norm (E := ℝ³) (μ := volume) (r := 6)
    (by rw [finrank_euclideanSpace, Fintype.card_fin]; norm_num)

/-- the elementary conversion `(C/r³)² = C²r^{-6}`. -/
lemma div_cube_sq_eq (C r : ℝ) (hr : 0 < r) :
    (C / r ^ 3) ^ 2 = C ^ 2 * r ^ (-(6 : ℝ)) := by
  have h6 : r ^ (-(6 : ℝ)) = ((r ^ 3) ^ 2)⁻¹ := by
    rw [show (-(6 : ℝ)) = -((6 : ℕ) : ℝ) from by norm_num, Real.rpow_neg (le_of_lt hr),
      Real.rpow_natCast]
    congr 1
    ring
  rw [h6, div_pow, div_eq_mul_inv]

/-- **THE PER-`x` MODE BOUND.**  For `x` in the box,
`(2π)^{-3}∫_q (boxOp s 1 (qModeRe s q) Φ x)² ≤ (N̂+1)chiSup² Σ_i ∫_Λ (aQ s i Φ)(x_{i↦z})²dz`. -/
lemma modeP_qModeRe_xbound {s : ℝ} (hs : 0 < s) {n : ℕ} {Φ : X (n + 1) → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) {x : X (n + 1)} (hx : x ∈ abox (n + 1) s) :
    ((2 * π) ^ 3)⁻¹ * ∫ q, (boxOp s (fun _ => (1 : ℝ)) (qModeRe s q) Φ x) ^ 2
      ≤ ((n : ℝ) + 1) * chiSup ^ 2 * ∑ i : Fin (n + 1),
          ∫ z in acube s, ((aQ s i Φ) (Function.update x i z)) ^ 2 := by
  obtain ⟨K, hK0, hKb⟩ := exists_qModeRe_mode_bound hs n Φ (hΦ.of_le (WithTop.coe_le_coe.mpr le_top))
  have hint_i : ∀ i : Fin (n + 1), Integrable (fun q : ℝ³ =>
      (∫ z in acube s, qModeRe s q z * Φ (Function.update x i z)) ^ 2) := by
    intro i
    have hcont : Continuous fun q : ℝ³ =>
        ∫ z in acube s, qModeRe s q z * Φ (Function.update x i z) := by
      refine continuous_parametric_integral_of_continuous
        (f := fun q z => qModeRe s q z * Φ (Function.update x i z)) ?_ (acube_compact hs)
      rw [show Function.uncurry (fun q z => qModeRe s q z * Φ (Function.update x i z))
          = fun r : ℝ³ × ℝ³ => qModeRe s r.1 r.2 * Φ (Function.update x i r.2) from by
        funext r; rfl]
      exact (continuous_qModeRe_pair hs).mul
        (hΦ.continuous.comp (continuous_const.update i continuous_snd))
    refine Integrable.mono'
      (g := fun q : ℝ³ => K ^ 2 * (1 + ‖q‖) ^ (-(6 : ℝ))) ?_ ?_ ?_
    · refine (integrable_one_add_norm_six_r3.const_mul (K ^ 2)).congr ?_
      filter_upwards with q
      ring
    · exact (hcont.pow 2).aestronglyMeasurable
    · filter_upwards with q
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      calc (∫ z in acube s, qModeRe s q z * Φ (Function.update x i z)) ^ 2
          = |∫ z in acube s, qModeRe s q z * Φ (Function.update x i z)| ^ 2 := by rw [sq_abs]
        _ ≤ (K / (1 + ‖q‖) ^ 3) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hKb x hx i q) 2
        _ = K ^ 2 * (1 + ‖q‖) ^ (-(6 : ℝ)) := div_cube_sq_eq K (1 + ‖q‖) (by positivity)
  have hint_sum : Integrable (fun q : ℝ³ => (((n : ℝ) + 1)) * ∑ i : Fin (n + 1),
      (∫ z in acube s, qModeRe s q z * Φ (Function.update x i z)) ^ 2) := by
    refine Integrable.const_mul ?_ _
    exact integrable_finsetSum _ (fun i _ => hint_i i)
  have hCS : ∀ q : ℝ³, (boxOp s (fun _ => (1 : ℝ)) (qModeRe s q) Φ x) ^ 2
      ≤ ((n : ℝ) + 1) * ∑ i : Fin (n + 1),
          (∫ z in acube s, qModeRe s q z * Φ (Function.update x i z)) ^ 2 := by
    intro q
    rw [show boxOp s (fun _ => (1 : ℝ)) (qModeRe s q) Φ x
        = ∑ i : Fin (n + 1), ∫ z in acube s, qModeRe s q z * Φ (Function.update x i z) from by
      simp only [boxOp, one_mul]]
    exact sq_sum_fin_le _
  -- the `χ`-cosine form of each slot integral
  have hcong : ∀ i : Fin (n + 1),
      (fun q : ℝ³ => (∫ z in acube s, qModeRe s q z * Φ (Function.update x i z)) ^ 2)
        = fun q => (∫ z in acube s, chiScale s z * Real.cos (inner ℝ q z)
            * (aQ s i Φ) (Function.update x i z)) ^ 2 := by
    intro i
    funext q
    rw [qModeRe_slot_eq_cos hs q hΦ i x]
  have hper : ∀ i : Fin (n + 1),
      ((2 * π) ^ 3)⁻¹ * ∫ q, (∫ z in acube s, qModeRe s q z * Φ (Function.update x i z)) ^ 2
        ≤ chiSup ^ 2 * ∫ z in acube s, ((aQ s i Φ) (Function.update x i z)) ^ 2 := by
    intro i
    rw [hcong i]
    exact cos_overlap_le_chiSup hs ((contDiff_aQ hs i hΦ).comp (contDiff_update ∞ x i))
  have hmain : ∫ q, (boxOp s (fun _ => (1 : ℝ)) (qModeRe s q) Φ x) ^ 2
      ≤ ((n : ℝ) + 1) * ∑ i : Fin (n + 1),
          ∫ q, (∫ z in acube s, qModeRe s q z * Φ (Function.update x i z)) ^ 2 := by
    refine le_trans (integral_mono_of_nonneg (Eventually.of_forall fun q => sq_nonneg _)
      hint_sum (Eventually.of_forall fun q => hCS q)) ?_
    rw [MeasureTheory.integral_const_mul]
    rw [MeasureTheory.integral_finsetSum Finset.univ (fun i _ => hint_i i)]
  have h1 : ((2 * π) ^ 3)⁻¹ * ∫ q, (boxOp s (fun _ => (1 : ℝ)) (qModeRe s q) Φ x) ^ 2
      ≤ ((2 * π) ^ 3)⁻¹ * (((n : ℝ) + 1) * ∑ i : Fin (n + 1),
          ∫ q, (∫ z in acube s, qModeRe s q z * Φ (Function.update x i z)) ^ 2) :=
    mul_le_mul_of_nonneg_left hmain (by positivity)
  have h2 : ((2 * π) ^ 3)⁻¹ * (((n : ℝ) + 1) * ∑ i : Fin (n + 1),
        ∫ q, (∫ z in acube s, qModeRe s q z * Φ (Function.update x i z)) ^ 2)
      = ((n : ℝ) + 1) * ∑ i : Fin (n + 1),
          ((2 * π) ^ 3)⁻¹ * ∫ q,
            (∫ z in acube s, qModeRe s q z * Φ (Function.update x i z)) ^ 2 := by
    rw [← Finset.mul_sum]
    ring
  have h3 : ((n : ℝ) + 1) * ∑ i : Fin (n + 1),
        ((2 * π) ^ 3)⁻¹ * ∫ q,
          (∫ z in acube s, qModeRe s q z * Φ (Function.update x i z)) ^ 2
      ≤ ((n : ℝ) + 1) * ∑ i : Fin (n + 1),
          chiSup ^ 2 * ∫ z in acube s, ((aQ s i Φ) (Function.update x i z)) ^ 2 :=
    mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hper i)) (by positivity)
  have h4 : ((n : ℝ) + 1) * ∑ i : Fin (n + 1),
        chiSup ^ 2 * ∫ z in acube s, ((aQ s i Φ) (Function.update x i z)) ^ 2
      = ((n : ℝ) + 1) * chiSup ^ 2 * ∑ i : Fin (n + 1),
          ∫ z in acube s, ((aQ s i Φ) (Function.update x i z)) ^ 2 := by
    rw [← Finset.mul_sum]
    ring
  linarith [h1, h2, h3, h4]


/-- joint continuity of `qModeIm`. -/
lemma continuous_qModeIm_pair {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Continuous (fun q : ℝ³ × ℝ³ => qModeIm ℓ q.1 q.2) := by
  rw [show (fun q : ℝ³ × ℝ³ => qModeIm ℓ q.1 q.2)
      = fun q => (qMode ℓ q.1 q.2).im from by funext q; rfl]
  exact Complex.continuous_im.comp (continuous_qMode_pair hℓ)

/-- **The `qModeIm` per-`x` bound** (the twin of `modeP_qModeRe_xbound`). -/
lemma modeP_qModeIm_xbound {s : ℝ} (hs : 0 < s) {n : ℕ} {Φ : X (n + 1) → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) {x : X (n + 1)} (hx : x ∈ abox (n + 1) s) :
    ((2 * π) ^ 3)⁻¹ * ∫ q, (boxOp s (fun _ => (1 : ℝ)) (qModeIm s q) Φ x) ^ 2
      ≤ ((n : ℝ) + 1) * chiSup ^ 2 * ∑ i : Fin (n + 1),
          ∫ z in acube s, ((aQ s i Φ) (Function.update x i z)) ^ 2 := by
  obtain ⟨K, hK0, hKb⟩ := exists_qModeIm_mode_bound hs n Φ
    (hΦ.of_le (WithTop.coe_le_coe.mpr le_top))
  have hint_i : ∀ i : Fin (n + 1), Integrable (fun q : ℝ³ =>
      (∫ z in acube s, qModeIm s q z * Φ (Function.update x i z)) ^ 2) := by
    intro i
    have hcont : Continuous fun q : ℝ³ =>
        ∫ z in acube s, qModeIm s q z * Φ (Function.update x i z) := by
      refine continuous_parametric_integral_of_continuous
        (f := fun q z => qModeIm s q z * Φ (Function.update x i z)) ?_ (acube_compact hs)
      rw [show Function.uncurry (fun q z => qModeIm s q z * Φ (Function.update x i z))
          = fun r : ℝ³ × ℝ³ => qModeIm s r.1 r.2 * Φ (Function.update x i r.2) from by
        funext r; rfl]
      exact (continuous_qModeIm_pair hs).mul
        (hΦ.continuous.comp (continuous_const.update i continuous_snd))
    refine Integrable.mono'
      (g := fun q : ℝ³ => K ^ 2 * (1 + ‖q‖) ^ (-(6 : ℝ))) ?_ ?_ ?_
    · refine (integrable_one_add_norm_six_r3.const_mul (K ^ 2)).congr ?_
      filter_upwards with q
      ring
    · exact (hcont.pow 2).aestronglyMeasurable
    · filter_upwards with q
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      calc (∫ z in acube s, qModeIm s q z * Φ (Function.update x i z)) ^ 2
          = |∫ z in acube s, qModeIm s q z * Φ (Function.update x i z)| ^ 2 := by rw [sq_abs]
        _ ≤ (K / (1 + ‖q‖) ^ 3) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hKb x hx i q) 2
        _ = K ^ 2 * (1 + ‖q‖) ^ (-(6 : ℝ)) := div_cube_sq_eq K (1 + ‖q‖) (by positivity)
  have hint_sum : Integrable (fun q : ℝ³ => ((n : ℝ) + 1) * ∑ i : Fin (n + 1),
      (∫ z in acube s, qModeIm s q z * Φ (Function.update x i z)) ^ 2) := by
    refine Integrable.const_mul ?_ _
    exact integrable_finsetSum _ (fun i _ => hint_i i)
  have hCS : ∀ q : ℝ³, (boxOp s (fun _ => (1 : ℝ)) (qModeIm s q) Φ x) ^ 2
      ≤ ((n : ℝ) + 1) * ∑ i : Fin (n + 1),
          (∫ z in acube s, qModeIm s q z * Φ (Function.update x i z)) ^ 2 := by
    intro q
    rw [show boxOp s (fun _ => (1 : ℝ)) (qModeIm s q) Φ x
        = ∑ i : Fin (n + 1), ∫ z in acube s, qModeIm s q z * Φ (Function.update x i z) from by
      simp only [boxOp, one_mul]]
    exact sq_sum_fin_le _
  have hcong : ∀ i : Fin (n + 1),
      (fun q : ℝ³ => (∫ z in acube s, qModeIm s q z * Φ (Function.update x i z)) ^ 2)
        = fun q => (∫ z in acube s, chiScale s z * Real.sin (inner ℝ q z)
            * (aQ s i Φ) (Function.update x i z)) ^ 2 := by
    intro i
    funext q
    rw [qModeIm_slot_eq_neg_sin hs q hΦ i x, neg_sq]
  have hper : ∀ i : Fin (n + 1),
      ((2 * π) ^ 3)⁻¹ * ∫ q, (∫ z in acube s, qModeIm s q z * Φ (Function.update x i z)) ^ 2
        ≤ chiSup ^ 2 * ∫ z in acube s, ((aQ s i Φ) (Function.update x i z)) ^ 2 := by
    intro i
    rw [hcong i]
    exact sin_overlap_le_chiSup hs ((contDiff_aQ hs i hΦ).comp (contDiff_update ∞ x i))
  have hmain : ∫ q, (boxOp s (fun _ => (1 : ℝ)) (qModeIm s q) Φ x) ^ 2
      ≤ ((n : ℝ) + 1) * ∑ i : Fin (n + 1),
          ∫ q, (∫ z in acube s, qModeIm s q z * Φ (Function.update x i z)) ^ 2 := by
    refine le_trans (integral_mono_of_nonneg (Eventually.of_forall fun q => sq_nonneg _)
      hint_sum (Eventually.of_forall fun q => hCS q)) ?_
    rw [MeasureTheory.integral_const_mul]
    rw [MeasureTheory.integral_finsetSum Finset.univ (fun i _ => hint_i i)]
  have h1 : ((2 * π) ^ 3)⁻¹ * ∫ q, (boxOp s (fun _ => (1 : ℝ)) (qModeIm s q) Φ x) ^ 2
      ≤ ((2 * π) ^ 3)⁻¹ * (((n : ℝ) + 1) * ∑ i : Fin (n + 1),
          ∫ q, (∫ z in acube s, qModeIm s q z * Φ (Function.update x i z)) ^ 2) :=
    mul_le_mul_of_nonneg_left hmain (by positivity)
  have h2 : ((2 * π) ^ 3)⁻¹ * (((n : ℝ) + 1) * ∑ i : Fin (n + 1),
        ∫ q, (∫ z in acube s, qModeIm s q z * Φ (Function.update x i z)) ^ 2)
      = ((n : ℝ) + 1) * ∑ i : Fin (n + 1),
          ((2 * π) ^ 3)⁻¹ * ∫ q,
            (∫ z in acube s, qModeIm s q z * Φ (Function.update x i z)) ^ 2 := by
    rw [← Finset.mul_sum]
    ring
  have h3 : ((n : ℝ) + 1) * ∑ i : Fin (n + 1),
        ((2 * π) ^ 3)⁻¹ * ∫ q,
          (∫ z in acube s, qModeIm s q z * Φ (Function.update x i z)) ^ 2
      ≤ ((n : ℝ) + 1) * ∑ i : Fin (n + 1),
          chiSup ^ 2 * ∫ z in acube s, ((aQ s i Φ) (Function.update x i z)) ^ 2 :=
    mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hper i)) (by positivity)
  have h4 : ((n : ℝ) + 1) * ∑ i : Fin (n + 1),
        chiSup ^ 2 * ∫ z in acube s, ((aQ s i Φ) (Function.update x i z)) ^ 2
      = ((n : ℝ) + 1) * chiSup ^ 2 * ∑ i : Fin (n + 1),
          ∫ z in acube s, ((aQ s i Φ) (Function.update x i z)) ^ 2 := by
    rw [← Finset.mul_sum]
    ring
  linarith [h1, h2, h3, h4]

/-! ## 5 The integrated bound (Fubini + the slot peel) -/

/-- **The `qModeRe` half of the `A₁` bound.** -/
lemma a1_re_bound {s : ℝ} (hs : 0 < s) {n : ℕ} {Φ : X (n + 1) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) :
    ((2 * π) ^ 3)⁻¹ * ∫ q, modeP s (qModeRe s q) Φ
      ≤ ((n : ℝ) + 1) * chiSup ^ 2 * cnPlus s Φ := by
  obtain ⟨K, hK0, hKb⟩ := exists_qModeRe_mode_bound hs n Φ
    (hΦ.of_le (WithTop.coe_le_coe.mpr le_top))
  haveI : IsFiniteMeasure ((volume : Measure (X (n + 1))).restrict (abox (n + 1) s)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact abox_lt_top (n + 1) s hs.le⟩
  have hmem : ∀ᵐ p ∂((volume : Measure ℝ³).prod
      ((volume : Measure (X (n + 1))).restrict (abox (n + 1) s))), p.2 ∈ abox (n + 1) s := by
    rw [Measure.ae_prod_iff_ae_ae (p := fun p : ℝ³ × X (n + 1) => p.2 ∈ abox (n + 1) s)
      ((abox_measurable (n + 1) s).preimage measurable_snd)]
    filter_upwards with q
    exact ae_restrict_mem (abox_measurable (n + 1) s)
  have hjoint : Continuous fun p : ℝ³ × X (n + 1) =>
      boxOp s (fun _ => (1 : ℝ)) (qModeRe s p.1) Φ p.2 := by
    rw [show (fun p : ℝ³ × X (n + 1) => boxOp s (fun _ => (1 : ℝ)) (qModeRe s p.1) Φ p.2)
        = fun p => ∑ i : Fin (n + 1), ∫ z in acube s,
            qModeRe s p.1 z * Φ (Function.update p.2 i z) from by
      funext p; simp only [boxOp, one_mul]]
    refine continuous_finsetSum _ (fun i _ => ?_)
    refine continuous_parametric_integral_of_continuous
      (f := fun (p : ℝ³ × X (n + 1)) (z : ℝ³) =>
        qModeRe s p.1 z * Φ (Function.update p.2 i z)) ?_ (acube_compact hs)
    rw [show Function.uncurry (fun (p : ℝ³ × X (n + 1)) (z : ℝ³) =>
          qModeRe s p.1 z * Φ (Function.update p.2 i z))
        = fun r : (ℝ³ × X (n + 1)) × ℝ³ =>
            qModeRe s r.1.1 r.2 * Φ (Function.update r.1.2 i r.2) from by
      funext r; rfl]
    have h1 : Continuous fun r : (ℝ³ × X (n + 1)) × ℝ³ => (r.1.1, r.2) :=
      continuous_fst.fst.prodMk continuous_snd
    have h2 : Continuous fun r : (ℝ³ × X (n + 1)) × ℝ³ => r.1.2 := continuous_fst.snd
    exact ((continuous_qModeRe_pair hs).comp h1).mul
      (hΦ.continuous.comp (h2.update i continuous_snd))
  have hFint : Integrable (fun p : ℝ³ × X (n + 1) =>
      (boxOp s (fun _ => (1 : ℝ)) (qModeRe s p.1) Φ p.2) ^ 2)
      ((volume : Measure ℝ³).prod ((volume : Measure (X (n + 1))).restrict
        (abox (n + 1) s))) := by
    refine Integrable.mono'
      (g := fun p : ℝ³ × X (n + 1) =>
        (((n : ℝ) + 1) * K) ^ 2 * (1 + ‖p.1‖) ^ (-(6 : ℝ))) ?_ ?_ ?_
    · have hb := integrable_one_add_norm_six_r3.mul_prod
        (integrable_const (1 : ℝ) :
          Integrable (fun _ : X (n + 1) => (1 : ℝ))
            ((volume : Measure (X (n + 1))).restrict (abox (n + 1) s)))
      refine (hb.const_mul ((((n : ℝ) + 1) * K) ^ 2)).congr ?_
      filter_upwards with p
      ring
    · exact (hjoint.pow 2).aestronglyMeasurable
    · filter_upwards [hmem] with p hp
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      have h1 : |boxOp s (fun _ => (1 : ℝ)) (qModeRe s p.1) Φ p.2|
          ≤ ((n : ℝ) + 1) * K / (1 + ‖p.1‖) ^ 3 := by
        rw [show boxOp s (fun _ => (1 : ℝ)) (qModeRe s p.1) Φ p.2
            = ∑ i : Fin (n + 1), ∫ z in acube s,
                qModeRe s p.1 z * Φ (Function.update p.2 i z) from by
          simp only [boxOp, one_mul]]
        calc |∑ i : Fin (n + 1), ∫ z in acube s,
                qModeRe s p.1 z * Φ (Function.update p.2 i z)|
            ≤ ∑ i : Fin (n + 1),
                |∫ z in acube s, qModeRe s p.1 z * Φ (Function.update p.2 i z)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _i : Fin (n + 1), K / (1 + ‖p.1‖) ^ 3 :=
              Finset.sum_le_sum (fun i _ => hKb p.2 hp i p.1)
          _ = ((n : ℝ) + 1) * K / (1 + ‖p.1‖) ^ 3 := by
              rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
              push_cast
              ring
      calc (boxOp s (fun _ => (1 : ℝ)) (qModeRe s p.1) Φ p.2) ^ 2
          = |boxOp s (fun _ => (1 : ℝ)) (qModeRe s p.1) Φ p.2| ^ 2 := by rw [sq_abs]
        _ ≤ (((n : ℝ) + 1) * K / (1 + ‖p.1‖) ^ 3) ^ 2 :=
              pow_le_pow_left₀ (abs_nonneg _) h1 2
        _ = (((n : ℝ) + 1) * K) ^ 2 * (1 + ‖p.1‖) ^ (-(6 : ℝ)) :=
              div_cube_sq_eq (((n : ℝ) + 1) * K) (1 + ‖p.1‖) (by positivity)
  have hswap := integral_integral_swap (μ := (volume : Measure ℝ³))
    (ν := (volume : Measure (X (n + 1))).restrict (abox (n + 1) s))
    (f := fun (q : ℝ³) (x : X (n + 1)) =>
      (boxOp s (fun _ => (1 : ℝ)) (qModeRe s q) Φ x) ^ 2) hFint
  have hint_i : ∀ i : Fin (n + 1), Integrable (fun x : X (n + 1) =>
      ∫ z in acube s, ((aQ s i Φ) (Function.update x i z)) ^ 2)
      ((volume : Measure (X (n + 1))).restrict (abox (n + 1) s)) := by
    intro i
    have hc : Continuous fun x : X (n + 1) =>
        ∫ z in acube s, ((aQ s i Φ) (Function.update x i z)) ^ 2 := by
      refine continuous_parametric_integral_of_continuous
        (f := fun (x : X (n + 1)) (z : ℝ³) =>
          ((aQ s i Φ) (Function.update x i z)) ^ 2) ?_ (acube_compact hs)
      rw [show Function.uncurry (fun (x : X (n + 1)) (z : ℝ³) =>
            ((aQ s i Φ) (Function.update x i z)) ^ 2)
          = fun r : X (n + 1) × ℝ³ => ((aQ s i Φ) (Function.update r.1 i r.2)) ^ 2 from by
        funext r; rfl]
      exact (((contDiff_aQ hs i hΦ).continuous.comp
        (continuous_fst.update i continuous_snd))).pow 2
    exact ContinuousOn.integrableOn_compact (abox_compact (n + 1) hs) hc.continuousOn
  have hxbound : (∫ x in abox (n + 1) s, ∫ q,
        (boxOp s (fun _ => (1 : ℝ)) (qModeRe s q) Φ x) ^ 2)
      ≤ ∫ x in abox (n + 1) s, (2 * π) ^ 3 * (((n : ℝ) + 1) * chiSup ^ 2 *
          ∑ i : Fin (n + 1), ∫ z in acube s,
            ((aQ s i Φ) (Function.update x i z)) ^ 2) := by
    refine integral_mono_of_nonneg
      (Eventually.of_forall fun x => integral_nonneg fun q => sq_nonneg _) ?_ ?_
    · refine Integrable.const_mul ?_ _
      refine Integrable.const_mul ?_ _
      exact integrable_finsetSum _ (fun i _ => hint_i i)
    · filter_upwards [ae_restrict_mem (abox_measurable (n + 1) s)] with x hx
      have hb := modeP_qModeRe_xbound hs hΦ hx
      have h2π : (0 : ℝ) < (2 * π) ^ 3 := by positivity
      calc (∫ q, (boxOp s (fun _ => (1 : ℝ)) (qModeRe s q) Φ x) ^ 2)
          = (2 * π) ^ 3 * (((2 * π) ^ 3)⁻¹
              * ∫ q, (boxOp s (fun _ => (1 : ℝ)) (qModeRe s q) Φ x) ^ 2) := by
            rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt h2π), one_mul]
        _ ≤ (2 * π) ^ 3 * (((n : ℝ) + 1) * chiSup ^ 2 * ∑ i : Fin (n + 1),
              ∫ z in acube s, ((aQ s i Φ) (Function.update x i z)) ^ 2) :=
            mul_le_mul_of_nonneg_left hb (le_of_lt h2π)
  have hslot : ∀ i : Fin (n + 1),
      (∫ x in abox (n + 1) s, ∫ z in acube s,
          ((aQ s i Φ) (Function.update x i z)) ^ 2)
        = s ^ 3 * ∫ x in abox (n + 1) s, ((aQ s i Φ) x) ^ 2 := fun i =>
    abox_slot_swap_eq hs i ((contDiff_aQ hs i hΦ).continuous.pow 2)
  have hsum : (∫ x in abox (n + 1) s, ∑ i : Fin (n + 1),
        ∫ z in acube s, ((aQ s i Φ) (Function.update x i z)) ^ 2)
      = s ^ 3 * cnPlus s Φ := by
    rw [MeasureTheory.integral_finsetSum Finset.univ (fun i _ => hint_i i)]
    rw [Finset.sum_congr rfl (fun i _ => hslot i)]
    rw [← Finset.mul_sum]
    rfl
  have hRHS : (∫ x in abox (n + 1) s, (2 * π) ^ 3 * (((n : ℝ) + 1) * chiSup ^ 2 *
        ∑ i : Fin (n + 1), ∫ z in acube s, ((aQ s i Φ) (Function.update x i z)) ^ 2))
      = (2 * π) ^ 3 * (((n : ℝ) + 1) * chiSup ^ 2) * (s ^ 3 * cnPlus s Φ) := by
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, hsum]
    ring
  have hA : ((2 * π) ^ 3)⁻¹ * ∫ q, modeP s (qModeRe s q) Φ
      = ((2 * π) ^ 3)⁻¹ * ((s ^ 3)⁻¹ * ∫ q, ∫ x in abox (n + 1) s,
          (boxOp s (fun _ => (1 : ℝ)) (qModeRe s q) Φ x) ^ 2) := by
    rw [show (∫ q, modeP s (qModeRe s q) Φ)
        = (s ^ 3)⁻¹ * ∫ q, ∫ x in abox (n + 1) s,
            (boxOp s (fun _ => (1 : ℝ)) (qModeRe s q) Φ x) ^ 2 from by
      rw [show (fun q => modeP s (qModeRe s q) Φ) = fun q => (s ^ 3)⁻¹ *
          ∫ x in abox (n + 1) s,
            (boxOp s (fun _ => (1 : ℝ)) (qModeRe s q) Φ x) ^ 2 from by
        funext q; rfl]
      rw [MeasureTheory.integral_const_mul]]
  have hB : ((2 * π) ^ 3)⁻¹ * ((s ^ 3)⁻¹ * ∫ q, ∫ x in abox (n + 1) s,
          (boxOp s (fun _ => (1 : ℝ)) (qModeRe s q) Φ x) ^ 2)
      = (s ^ 3)⁻¹ * (((2 * π) ^ 3)⁻¹ * ∫ x in abox (n + 1) s, ∫ q,
          (boxOp s (fun _ => (1 : ℝ)) (qModeRe s q) Φ x) ^ 2) := by
    rw [hswap]
    ring
  have hC : (s ^ 3)⁻¹ * (((2 * π) ^ 3)⁻¹ * ∫ x in abox (n + 1) s, ∫ q,
          (boxOp s (fun _ => (1 : ℝ)) (qModeRe s q) Φ x) ^ 2)
      ≤ (s ^ 3)⁻¹ * (((2 * π) ^ 3)⁻¹ * ∫ x in abox (n + 1) s,
          (2 * π) ^ 3 * (((n : ℝ) + 1) * chiSup ^ 2 *
            ∑ i : Fin (n + 1), ∫ z in acube s,
              ((aQ s i Φ) (Function.update x i z)) ^ 2)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hxbound (by positivity)) (by positivity)
  have hD : (s ^ 3)⁻¹ * (((2 * π) ^ 3)⁻¹ * ∫ x in abox (n + 1) s,
          (2 * π) ^ 3 * (((n : ℝ) + 1) * chiSup ^ 2 *
            ∑ i : Fin (n + 1), ∫ z in acube s, ((aQ s i Φ) (Function.update x i z)) ^ 2))
      = (s ^ 3)⁻¹ * (((2 * π) ^ 3)⁻¹ *
          ((2 * π) ^ 3 * (((n : ℝ) + 1) * chiSup ^ 2) * (s ^ 3 * cnPlus s Φ))) := by
    rw [hRHS]
  have hE : (s ^ 3)⁻¹ * (((2 * π) ^ 3)⁻¹ *
        ((2 * π) ^ 3 * (((n : ℝ) + 1) * chiSup ^ 2) * (s ^ 3 * cnPlus s Φ)))
      = ((n : ℝ) + 1) * chiSup ^ 2 * cnPlus s Φ := by
    have hπ : ((2 * π) ^ 3 : ℝ) ≠ 0 := by positivity
    have hs3 : (s ^ 3 : ℝ) ≠ 0 := by positivity
    field_simp
  linarith [hA, hB, hC, hD, hE]

/-- **The `qModeIm` half of the `A₁` bound.** -/
lemma a1_im_bound {s : ℝ} (hs : 0 < s) {n : ℕ} {Φ : X (n + 1) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) :
    ((2 * π) ^ 3)⁻¹ * ∫ q, modeP s (qModeIm s q) Φ
      ≤ ((n : ℝ) + 1) * chiSup ^ 2 * cnPlus s Φ := by
  obtain ⟨K, hK0, hKb⟩ := exists_qModeIm_mode_bound hs n Φ
    (hΦ.of_le (WithTop.coe_le_coe.mpr le_top))
  haveI : IsFiniteMeasure ((volume : Measure (X (n + 1))).restrict (abox (n + 1) s)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact abox_lt_top (n + 1) s hs.le⟩
  have hmem : ∀ᵐ p ∂((volume : Measure ℝ³).prod
      ((volume : Measure (X (n + 1))).restrict (abox (n + 1) s))), p.2 ∈ abox (n + 1) s := by
    rw [Measure.ae_prod_iff_ae_ae (p := fun p : ℝ³ × X (n + 1) => p.2 ∈ abox (n + 1) s)
      ((abox_measurable (n + 1) s).preimage measurable_snd)]
    filter_upwards with q
    exact ae_restrict_mem (abox_measurable (n + 1) s)
  have hjoint : Continuous fun p : ℝ³ × X (n + 1) =>
      boxOp s (fun _ => (1 : ℝ)) (qModeIm s p.1) Φ p.2 := by
    rw [show (fun p : ℝ³ × X (n + 1) => boxOp s (fun _ => (1 : ℝ)) (qModeIm s p.1) Φ p.2)
        = fun p => ∑ i : Fin (n + 1), ∫ z in acube s,
            qModeIm s p.1 z * Φ (Function.update p.2 i z) from by
      funext p; simp only [boxOp, one_mul]]
    refine continuous_finsetSum _ (fun i _ => ?_)
    refine continuous_parametric_integral_of_continuous
      (f := fun (p : ℝ³ × X (n + 1)) (z : ℝ³) =>
        qModeIm s p.1 z * Φ (Function.update p.2 i z)) ?_ (acube_compact hs)
    rw [show Function.uncurry (fun (p : ℝ³ × X (n + 1)) (z : ℝ³) =>
          qModeIm s p.1 z * Φ (Function.update p.2 i z))
        = fun r : (ℝ³ × X (n + 1)) × ℝ³ =>
            qModeIm s r.1.1 r.2 * Φ (Function.update r.1.2 i r.2) from by
      funext r; rfl]
    have h1 : Continuous fun r : (ℝ³ × X (n + 1)) × ℝ³ => (r.1.1, r.2) :=
      continuous_fst.fst.prodMk continuous_snd
    have h2 : Continuous fun r : (ℝ³ × X (n + 1)) × ℝ³ => r.1.2 := continuous_fst.snd
    exact ((continuous_qModeIm_pair hs).comp h1).mul
      (hΦ.continuous.comp (h2.update i continuous_snd))
  have hFint : Integrable (fun p : ℝ³ × X (n + 1) =>
      (boxOp s (fun _ => (1 : ℝ)) (qModeIm s p.1) Φ p.2) ^ 2)
      ((volume : Measure ℝ³).prod ((volume : Measure (X (n + 1))).restrict
        (abox (n + 1) s))) := by
    refine Integrable.mono'
      (g := fun p : ℝ³ × X (n + 1) =>
        (((n : ℝ) + 1) * K) ^ 2 * (1 + ‖p.1‖) ^ (-(6 : ℝ))) ?_ ?_ ?_
    · have hb := integrable_one_add_norm_six_r3.mul_prod
        (integrable_const (1 : ℝ) :
          Integrable (fun _ : X (n + 1) => (1 : ℝ))
            ((volume : Measure (X (n + 1))).restrict (abox (n + 1) s)))
      refine (hb.const_mul ((((n : ℝ) + 1) * K) ^ 2)).congr ?_
      filter_upwards with p
      ring
    · exact (hjoint.pow 2).aestronglyMeasurable
    · filter_upwards [hmem] with p hp
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      have h1 : |boxOp s (fun _ => (1 : ℝ)) (qModeIm s p.1) Φ p.2|
          ≤ ((n : ℝ) + 1) * K / (1 + ‖p.1‖) ^ 3 := by
        rw [show boxOp s (fun _ => (1 : ℝ)) (qModeIm s p.1) Φ p.2
            = ∑ i : Fin (n + 1), ∫ z in acube s,
                qModeIm s p.1 z * Φ (Function.update p.2 i z) from by
          simp only [boxOp, one_mul]]
        calc |∑ i : Fin (n + 1), ∫ z in acube s,
                qModeIm s p.1 z * Φ (Function.update p.2 i z)|
            ≤ ∑ i : Fin (n + 1),
                |∫ z in acube s, qModeIm s p.1 z * Φ (Function.update p.2 i z)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _i : Fin (n + 1), K / (1 + ‖p.1‖) ^ 3 :=
              Finset.sum_le_sum (fun i _ => hKb p.2 hp i p.1)
          _ = ((n : ℝ) + 1) * K / (1 + ‖p.1‖) ^ 3 := by
              rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
              push_cast
              ring
      calc (boxOp s (fun _ => (1 : ℝ)) (qModeIm s p.1) Φ p.2) ^ 2
          = |boxOp s (fun _ => (1 : ℝ)) (qModeIm s p.1) Φ p.2| ^ 2 := by rw [sq_abs]
        _ ≤ (((n : ℝ) + 1) * K / (1 + ‖p.1‖) ^ 3) ^ 2 :=
              pow_le_pow_left₀ (abs_nonneg _) h1 2
        _ = (((n : ℝ) + 1) * K) ^ 2 * (1 + ‖p.1‖) ^ (-(6 : ℝ)) :=
              div_cube_sq_eq (((n : ℝ) + 1) * K) (1 + ‖p.1‖) (by positivity)
  have hswap := integral_integral_swap (μ := (volume : Measure ℝ³))
    (ν := (volume : Measure (X (n + 1))).restrict (abox (n + 1) s))
    (f := fun (q : ℝ³) (x : X (n + 1)) =>
      (boxOp s (fun _ => (1 : ℝ)) (qModeIm s q) Φ x) ^ 2) hFint
  have hint_i : ∀ i : Fin (n + 1), Integrable (fun x : X (n + 1) =>
      ∫ z in acube s, ((aQ s i Φ) (Function.update x i z)) ^ 2)
      ((volume : Measure (X (n + 1))).restrict (abox (n + 1) s)) := by
    intro i
    have hc : Continuous fun x : X (n + 1) =>
        ∫ z in acube s, ((aQ s i Φ) (Function.update x i z)) ^ 2 := by
      refine continuous_parametric_integral_of_continuous
        (f := fun (x : X (n + 1)) (z : ℝ³) =>
          ((aQ s i Φ) (Function.update x i z)) ^ 2) ?_ (acube_compact hs)
      rw [show Function.uncurry (fun (x : X (n + 1)) (z : ℝ³) =>
            ((aQ s i Φ) (Function.update x i z)) ^ 2)
          = fun r : X (n + 1) × ℝ³ => ((aQ s i Φ) (Function.update r.1 i r.2)) ^ 2 from by
        funext r; rfl]
      exact (((contDiff_aQ hs i hΦ).continuous.comp
        (continuous_fst.update i continuous_snd))).pow 2
    exact ContinuousOn.integrableOn_compact (abox_compact (n + 1) hs) hc.continuousOn
  have hxbound : (∫ x in abox (n + 1) s, ∫ q,
        (boxOp s (fun _ => (1 : ℝ)) (qModeIm s q) Φ x) ^ 2)
      ≤ ∫ x in abox (n + 1) s, (2 * π) ^ 3 * (((n : ℝ) + 1) * chiSup ^ 2 *
          ∑ i : Fin (n + 1), ∫ z in acube s,
            ((aQ s i Φ) (Function.update x i z)) ^ 2) := by
    refine integral_mono_of_nonneg
      (Eventually.of_forall fun x => integral_nonneg fun q => sq_nonneg _) ?_ ?_
    · refine Integrable.const_mul ?_ _
      refine Integrable.const_mul ?_ _
      exact integrable_finsetSum _ (fun i _ => hint_i i)
    · filter_upwards [ae_restrict_mem (abox_measurable (n + 1) s)] with x hx
      have hb := modeP_qModeIm_xbound hs hΦ hx
      have h2π : (0 : ℝ) < (2 * π) ^ 3 := by positivity
      calc (∫ q, (boxOp s (fun _ => (1 : ℝ)) (qModeIm s q) Φ x) ^ 2)
          = (2 * π) ^ 3 * (((2 * π) ^ 3)⁻¹
              * ∫ q, (boxOp s (fun _ => (1 : ℝ)) (qModeIm s q) Φ x) ^ 2) := by
            rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt h2π), one_mul]
        _ ≤ (2 * π) ^ 3 * (((n : ℝ) + 1) * chiSup ^ 2 * ∑ i : Fin (n + 1),
              ∫ z in acube s, ((aQ s i Φ) (Function.update x i z)) ^ 2) :=
            mul_le_mul_of_nonneg_left hb (le_of_lt h2π)
  have hslot : ∀ i : Fin (n + 1),
      (∫ x in abox (n + 1) s, ∫ z in acube s,
          ((aQ s i Φ) (Function.update x i z)) ^ 2)
        = s ^ 3 * ∫ x in abox (n + 1) s, ((aQ s i Φ) x) ^ 2 := fun i =>
    abox_slot_swap_eq hs i ((contDiff_aQ hs i hΦ).continuous.pow 2)
  have hsum : (∫ x in abox (n + 1) s, ∑ i : Fin (n + 1),
        ∫ z in acube s, ((aQ s i Φ) (Function.update x i z)) ^ 2)
      = s ^ 3 * cnPlus s Φ := by
    rw [MeasureTheory.integral_finsetSum Finset.univ (fun i _ => hint_i i)]
    rw [Finset.sum_congr rfl (fun i _ => hslot i)]
    rw [← Finset.mul_sum]
    rfl
  have hRHS : (∫ x in abox (n + 1) s, (2 * π) ^ 3 * (((n : ℝ) + 1) * chiSup ^ 2 *
        ∑ i : Fin (n + 1), ∫ z in acube s, ((aQ s i Φ) (Function.update x i z)) ^ 2))
      = (2 * π) ^ 3 * (((n : ℝ) + 1) * chiSup ^ 2) * (s ^ 3 * cnPlus s Φ) := by
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, hsum]
    ring
  have hA : ((2 * π) ^ 3)⁻¹ * ∫ q, modeP s (qModeIm s q) Φ
      = ((2 * π) ^ 3)⁻¹ * ((s ^ 3)⁻¹ * ∫ q, ∫ x in abox (n + 1) s,
          (boxOp s (fun _ => (1 : ℝ)) (qModeIm s q) Φ x) ^ 2) := by
    rw [show (∫ q, modeP s (qModeIm s q) Φ)
        = (s ^ 3)⁻¹ * ∫ q, ∫ x in abox (n + 1) s,
            (boxOp s (fun _ => (1 : ℝ)) (qModeIm s q) Φ x) ^ 2 from by
      rw [show (fun q => modeP s (qModeIm s q) Φ) = fun q => (s ^ 3)⁻¹ *
          ∫ x in abox (n + 1) s,
            (boxOp s (fun _ => (1 : ℝ)) (qModeIm s q) Φ x) ^ 2 from by
        funext q; rfl]
      rw [MeasureTheory.integral_const_mul]]
  have hB : ((2 * π) ^ 3)⁻¹ * ((s ^ 3)⁻¹ * ∫ q, ∫ x in abox (n + 1) s,
          (boxOp s (fun _ => (1 : ℝ)) (qModeIm s q) Φ x) ^ 2)
      = (s ^ 3)⁻¹ * (((2 * π) ^ 3)⁻¹ * ∫ x in abox (n + 1) s, ∫ q,
          (boxOp s (fun _ => (1 : ℝ)) (qModeIm s q) Φ x) ^ 2) := by
    rw [hswap]
    ring
  have hC : (s ^ 3)⁻¹ * (((2 * π) ^ 3)⁻¹ * ∫ x in abox (n + 1) s, ∫ q,
          (boxOp s (fun _ => (1 : ℝ)) (qModeIm s q) Φ x) ^ 2)
      ≤ (s ^ 3)⁻¹ * (((2 * π) ^ 3)⁻¹ * ∫ x in abox (n + 1) s,
          (2 * π) ^ 3 * (((n : ℝ) + 1) * chiSup ^ 2 *
            ∑ i : Fin (n + 1), ∫ z in acube s,
              ((aQ s i Φ) (Function.update x i z)) ^ 2)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hxbound (by positivity)) (by positivity)
  have hD : (s ^ 3)⁻¹ * (((2 * π) ^ 3)⁻¹ * ∫ x in abox (n + 1) s,
          (2 * π) ^ 3 * (((n : ℝ) + 1) * chiSup ^ 2 *
            ∑ i : Fin (n + 1), ∫ z in acube s, ((aQ s i Φ) (Function.update x i z)) ^ 2))
      = (s ^ 3)⁻¹ * (((2 * π) ^ 3)⁻¹ *
          ((2 * π) ^ 3 * (((n : ℝ) + 1) * chiSup ^ 2) * (s ^ 3 * cnPlus s Φ))) := by
    rw [hRHS]
  have hE : (s ^ 3)⁻¹ * (((2 * π) ^ 3)⁻¹ *
        ((2 * π) ^ 3 * (((n : ℝ) + 1) * chiSup ^ 2) * (s ^ 3 * cnPlus s Φ)))
      = ((n : ℝ) + 1) * chiSup ^ 2 * cnPlus s Φ := by
    have hπ : ((2 * π) ^ 3 : ℝ) ≠ 0 := by positivity
    have hs3 : (s ^ 3 : ℝ) ≠ 0 := by positivity
    field_simp
  linarith [hA, hB, hC, hD, hE]

/-- `K/(1+‖q‖)^6 = K·(1+‖q‖)^{-6}` (the `div`-form used by the integrability bounds). -/
lemma rpow_neg_six_eq (r : ℝ) (hr : 0 < r) : r ^ (-(6 : ℝ)) = (r ^ 6)⁻¹ := by
  rw [show (-(6 : ℝ)) = -((6 : ℕ) : ℝ) from by norm_num, Real.rpow_neg (le_of_lt hr),
    Real.rpow_natCast]

/-- **THE `A₁` MODE-CONTENT BOUND** (the two halves summed). -/
theorem a1_mode_content_bound {s : ℝ} (hs : 0 < s) {n : ℕ} (Φ : X (n + 1) → ℝ)
    (hΦ : ContDiff ℝ ∞ Φ) :
    ((2 * π) ^ 3)⁻¹ * ∫ q, (modeP s (qModeRe s q) Φ + modeP s (qModeIm s q) Φ)
      ≤ 2 * ((n : ℝ) + 1) * chiSup ^ 2 * cnPlus s Φ := by
  obtain ⟨K, hK0, hK⟩ := exists_modeP_decay hs n Φ
    (hΦ.of_le (WithTop.coe_le_coe.mpr le_top))
  have hintR : Integrable (fun q : ℝ³ => modeP s (qModeRe s q) Φ) volume := by
    refine Integrable.mono' (g := fun q : ℝ³ => K * (1 + ‖q‖) ^ (-(6 : ℝ))) ?_ ?_ ?_
    · exact integrable_one_add_norm_six_r3.const_mul K
    · exact (continuous_modeP_qModeRe hs n Φ hΦ.continuous).aestronglyMeasurable
    · filter_upwards with q
      rw [Real.norm_of_nonneg (modeP_nonneg hs _ Φ)]
      calc modeP s (qModeRe s q) Φ ≤ modeP s (qModeRe s q) Φ + modeP s (qModeIm s q) Φ :=
            le_add_of_nonneg_right (modeP_nonneg hs _ Φ)
        _ ≤ K / (1 + ‖q‖) ^ 6 := hK q
        _ = K * (1 + ‖q‖) ^ (-(6 : ℝ)) := by
            rw [div_eq_mul_inv, rpow_neg_six_eq (1 + ‖q‖) (by positivity)]
  have hintI : Integrable (fun q : ℝ³ => modeP s (qModeIm s q) Φ) volume := by
    refine Integrable.mono' (g := fun q : ℝ³ => K * (1 + ‖q‖) ^ (-(6 : ℝ))) ?_ ?_ ?_
    · exact integrable_one_add_norm_six_r3.const_mul K
    · exact (continuous_modeP_qModeIm hs n Φ hΦ.continuous).aestronglyMeasurable
    · filter_upwards with q
      rw [Real.norm_of_nonneg (modeP_nonneg hs _ Φ)]
      calc modeP s (qModeIm s q) Φ ≤ modeP s (qModeRe s q) Φ + modeP s (qModeIm s q) Φ :=
            le_add_of_nonneg_left (modeP_nonneg hs _ Φ)
        _ ≤ K / (1 + ‖q‖) ^ 6 := hK q
        _ = K * (1 + ‖q‖) ^ (-(6 : ℝ)) := by
            rw [div_eq_mul_inv, rpow_neg_six_eq (1 + ‖q‖) (by positivity)]
  rw [MeasureTheory.integral_add hintR hintI, mul_add]
  have h1 := a1_re_bound hs hΦ
  have h2 := a1_im_bound hs hΦ
  linarith [h1, h2]

/-- **FS's `eq:A1estimate` in the D1 shape**: the `A₁`-mass is bounded by the excited count. -/
theorem a1_mass_bound {s : ℝ} (hs : 0 < s) {n : ℕ} {Φ : X (n + 1) → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) {Ks a : ℝ} (hKs : 0 ≤ Ks) (ha : 0 ≤ a) :
    2 * Ks * a * (s ^ 3)⁻¹ * (((2 * π) ^ 3)⁻¹ *
        ∫ q, (modeP s (qModeRe s q) Φ + modeP s (qModeIm s q) Φ))
      ≤ (4 * Ks * chiSup ^ 2) * a * (((n : ℝ) + 1) / s ^ 3) * cnPlus s Φ := by
  have h := a1_mode_content_bound hs Φ hΦ
  have h1 : (0 : ℝ) ≤ 2 * Ks * a * (s ^ 3)⁻¹ := by positivity
  have h2 := mul_le_mul_of_nonneg_left h h1
  have h3 : 2 * Ks * a * (s ^ 3)⁻¹ * (2 * (((n : ℝ) + 1) * chiSup ^ 2 * cnPlus s Φ))
      = (4 * Ks * chiSup ^ 2) * a * (((n : ℝ) + 1) / s ^ 3) * cnPlus s Φ := by
    rw [div_eq_mul_inv]
    ring
  linarith [h2, h3]

end BoseGases
end Submission
