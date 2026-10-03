import Mathlib
import Submission.Work.KMTAreas.A7.Tle_varphitildeNt_bounded
import Submission.Work.KMTAreas.A7.varphiNt_IW_facts
import Submission.Work.KMTAreas.A7.varphiN_mass_bounds
import Submission.Work.KMTAreas.A7.tsum_one_div_one_add_sq_mul_le
import Submission.Work.Analysis.CzShift.Main
import Submission.Work.Analysis.CzShift.exists_isCZSeed_of_fourierInv
import Submission.Work.BourgainPlan.Maximal.main_narrow_taoSetS
import Submission.Work.BourgainPlan.Maximal.mikhlinConvolutionLp
import Submission.Port.Aesm

set_option maxHeartbeats 8000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Finset
open scoped ENNReal NNReal BigOperators FourierTransform
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-! ## §1. The Young step: an `ℓ¹` bound on the kernel gives an `ℓᵖ` bound -/

private theorem eLpNorm_iwConv_le_of_kernelL1_aux {A : Finset Circ} {Φ : Circ → ℂ}
    {p : ENNReal} (hp : 1 < p) (hptop : p < ⊤) {R : ℝ} (hR : 0 ≤ R)
    (hsumm : Summable (fun j : ℤ => ‖iwKernel (iwSymbolSet A Φ) j‖))
    (hmass : (∑' j : ℤ, ‖iwKernel (iwSymbolSet A Φ) j‖) ≤ R) (f : ℤ → ℂ) :
    eLpNorm (iwConv A Φ f) p (Measure.count : Measure ℤ)
      ≤ ENNReal.ofReal R * eLpNorm f p (Measure.count : Measure ℤ) := by
  have hq1 : (1 : ℝ) < p.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top (ne_of_lt hptop)).mpr hp
  have hpeq : p = ENNReal.ofReal p.toReal := (ENNReal.ofReal_toReal (ne_of_lt hptop)).symm
  rw [hpeq]
  set kern : ℤ → ℂ := fun j => iwKernel (iwSymbolSet A Φ) j with hkern
  set Ab : ℝ := ∑' j : ℤ, ‖kern j‖ with hAb
  have hAb_le : Ab ≤ R := by rw [hAb]; exact hmass
  set K : ℤ → ℝ≥0∞ := fun j => ‖kern j‖ₑ with hK
  set Ψ : ℤ → ℝ≥0∞ := fun j => ‖f j‖ₑ with hΨ
  have hKae : AEMeasurable K (Measure.count : Measure ℤ) :=
    (measurable_of_countable K).aemeasurable
  have hΨae : AEMeasurable Ψ (Measure.count : Measure ℤ) :=
    (measurable_of_countable Ψ).aemeasurable
  have hpoint : ∀ n : ℤ, ‖iwConv A Φ f n‖ₑ
      ≤ ∫⁻ y, K (n - y) * Ψ y ∂(Measure.count : Measure ℤ) := by
    intro n
    have h1 : ‖iwConv A Φ f n‖ₑ ≤ ∑' j : ℤ, K j * Ψ (n - j) := by
      rw [iwConv_apply]
      refine (enorm_tsum_le_tsum_enorm).trans (le_of_eq (tsum_congr (fun j => ?_)))
      simp only [hK, hΨ, smul_eq_mul]
      exact enorm_mul _ _
    have h2 : (∑' j : ℤ, K j * Ψ (n - j)) = ∑' y : ℤ, K (n - y) * Ψ y := by
      simpa using (Equiv.tsum_eq (Equiv.subLeft n) (fun j : ℤ => K j * Ψ (n - j))).symm
    rw [lintegral_count, ← h2]
    exact h1
  have hstep2 : eLpNorm (iwConv A Φ f) (ENNReal.ofReal p.toReal)
        (Measure.count : Measure ℤ)
      ≤ eLpNorm (fun n : ℤ => ∫⁻ y, K (n - y) * Ψ y ∂(Measure.count : Measure ℤ))
          (ENNReal.ofReal p.toReal) (Measure.count : Measure ℤ) :=
    eLpNorm_mono_enorm (hf := by pw_aesm) hpoint
  have hconv : eLpNorm (fun n : ℤ => ∫⁻ y, K (n - y) * Ψ y ∂(Measure.count : Measure ℤ))
        (ENNReal.ofReal p.toReal) (Measure.count : Measure ℤ)
      ≤ eLpNorm K (ENNReal.ofReal (1 : ℝ)) (Measure.count : Measure ℤ)
        * eLpNorm Ψ (ENNReal.ofReal p.toReal) (Measure.count : Measure ℤ) :=
    Commons.Analysis.Convolution.eLpNorm_convolution_le_ennreal
      (K := K) (Φ := Ψ) (p := p.toReal) (q := p.toReal) (r := 1)
      (le_of_lt hq1) le_rfl (by ring) hKae hΨae
  have hKnorm : eLpNorm K (ENNReal.ofReal (1 : ℝ)) (Measure.count : Measure ℤ)
      = ENNReal.ofReal Ab := by
    rw [ENNReal.ofReal_one, eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm), lintegral_count, hAb]
    rw [ENNReal.ofReal_tsum_of_nonneg (f := fun j : ℤ => ‖kern j‖)
      (fun j => norm_nonneg _) hsumm]
    exact tsum_congr (fun j => by simp [hK])
  have hΨnorm : eLpNorm Ψ (ENNReal.ofReal p.toReal) (Measure.count : Measure ℤ)
      = eLpNorm f (ENNReal.ofReal p.toReal) (Measure.count : Measure ℤ) := by
    rw [hΨ]
    exact eLpNorm_enorm (hf := by pw_aesm) f
  calc eLpNorm (iwConv A Φ f) (ENNReal.ofReal p.toReal) (Measure.count : Measure ℤ)
      ≤ eLpNorm (fun n : ℤ => ∫⁻ y, K (n - y) * Ψ y ∂(Measure.count : Measure ℤ))
          (ENNReal.ofReal p.toReal) (Measure.count : Measure ℤ) := hstep2
    _ ≤ eLpNorm K (ENNReal.ofReal (1 : ℝ)) (Measure.count : Measure ℤ)
          * eLpNorm Ψ (ENNReal.ofReal p.toReal) (Measure.count : Measure ℤ) := hconv
    _ = ENNReal.ofReal Ab * eLpNorm f (ENNReal.ofReal p.toReal)
          (Measure.count : Measure ℤ) := by
          rw [hKnorm, hΨnorm]
    _ ≤ ENNReal.ofReal R * eLpNorm f (ENNReal.ofReal p.toReal)
          (Measure.count : Measure ℤ) := by
          gcongr

/-! ## §2. Elementary inequalities for the pointwise majorant -/

/-- `min u w ≤ 2uw/(u+w)` for positive `u, w` (twice the harmonic mean dominates the minimum). -/
private lemma min_le_two_mul_div_add {u w : ℝ} (hu : 0 < u) (hw : 0 < w) :
    min u w ≤ 2 * u * w / (u + w) := by
  have hden : 0 < u + w := by linarith
  rcases le_total u w with hle | hle
  · rw [min_eq_left hle, le_div_iff₀ hden]
    nlinarith [hle, hu]
  · rw [min_eq_right hle, le_div_iff₀ hden]
    nlinarith [hle, hw]

/-- `min u (v/t²) ≤ 2u/(1 + (u/v)t²)`: the minimum of the `L¹`-bound `u` and the decay bound
`v/t²` is at most twice their harmonic mean.  No hypothesis on `t` is needed (the convention
`v/0 = 0` is harmless because the right-hand side is then positive). -/
private lemma min_le_harmonic {u v t : ℝ} (hu : 0 < u) (hv : 0 < v) :
    min u (v / t ^ 2) ≤ 2 * u * v / (u * t ^ 2 + v) := by
  rcases eq_or_ne t 0 with h0 | h0
  · subst h0
    have hL : min u (v / (0 : ℝ) ^ 2) = 0 := by
      rw [zero_pow (by norm_num : (2 : ℕ) ≠ 0), div_zero, min_eq_right (le_of_lt hu)]
    have hR : (0 : ℝ) < 2 * u * v / (u * (0 : ℝ) ^ 2 + v) := by
      rw [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, zero_add]
      positivity
    rw [hL]
    exact le_of_lt hR
  · have ht2 : 0 < t ^ 2 := by positivity
    have hw : 0 < v / t ^ 2 := div_pos hv ht2
    have hden : u + v / t ^ 2 = (u * t ^ 2 + v) / t ^ 2 := by
      rw [add_div, mul_div_cancel_right₀ _ (ne_of_gt ht2)]
    have hcancel : v / t ^ 2 * t ^ 2 = v := div_mul_cancel₀ v (ne_of_gt ht2)
    have hid : 2 * u * (v / t ^ 2) / (u + v / t ^ 2) = 2 * u * v / (u * t ^ 2 + v) := by
      rw [hden, div_div_eq_mul_div, mul_assoc, hcancel]
    rw [← hid]
    exact min_le_two_mul_div_add hu hw

/-! ## §3. The `ℓ¹` mass of the kernel of the modulated narrow bump -/

private theorem kernel_mass_of_modulated_bump (A : Finset Circ) (φ : ℝ → ℂ) (c a A₀ B₀ : ℝ)
    (hφcd : ContDiff ℝ 2 φ) (hφcs : HasCompactSupport φ) (ha1 : 1 ≤ a)
    (hA₀ : 0 ≤ A₀) (hB₀ : 0 ≤ B₀)
    (h1 : (∫ y : ℝ, ‖φ y‖) ≤ A₀ / a)
    (h2 : (∫ y : ℝ, ‖iteratedDeriv 2 φ y‖) ≤ B₀ * a) :
    (∑' j : ℤ, ‖iwKernel (iwSymbolSet A (periodize (fun y : ℝ => φ y * ee (c * y)))) j‖)
      ≤ 4 * ((A.card : ℝ) * A₀ + 1)
        + 2 * Real.pi * Real.sqrt (((A.card : ℝ) * A₀ + 1)
            * ((A.card : ℝ) * B₀ / (4 * Real.pi ^ 2) + 1)) := by
  classical
  set cc : ℝ := (A.card : ℝ) with hcc
  have hcc0 : 0 ≤ cc := by rw [hcc]; exact Nat.cast_nonneg _
  set P : ℝ := cc * A₀ + 1 with hP
  set Q : ℝ := cc * B₀ / (4 * Real.pi ^ 2) with hQ
  have hP0 : 0 < P := by rw [hP]; nlinarith
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have ha_ne : a ≠ 0 := ne_of_gt ha0
  set aα : Circ → ℝ := fun α => (AddCircle.equivIco (1 : ℝ) 0 α).val with haα
  set F : ℝ → ℂ := fun y => φ y * ee (c * y) with hF
  have hFcd : ContDiff ℝ 2 F := by
    rw [hF]; exact hφcd.mul (contDiff_ee_const_mul 2 c)
  have hFcs : HasCompactSupport F := by
    rw [hF]; exact HasCompactSupport.mul_right hφcs
  set H : ℝ → ℂ := fun y => ∑ α ∈ A, ee (-(c * aα α)) * φ (y - aα α) with hH
  have hHcd : ContDiff ℝ 2 H := by
    rw [hH]
    exact ContDiff.sum (fun α _ => contDiff_const.mul (hφcd.comp (contDiff_id.sub contDiff_const)))
  have hφ_int : Integrable φ := hφcd.continuous.integrable_of_hasCompactSupport hφcs
  have hiter_int : ∀ n : ℕ, n ≤ 2 → Integrable (fun y : ℝ => ‖iteratedDeriv n φ y‖) := by
    intro n hn
    have hcont : Continuous (iteratedDeriv n φ) :=
      hφcd.continuous_iteratedDeriv n (by exact_mod_cast hn)
    have hcs : HasCompactSupport (iteratedDeriv n φ) := by
      interval_cases n
      · rw [iteratedDeriv_zero]; exact hφcs
      · rw [iteratedDeriv_one]; exact hφcs.deriv
      · rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
        exact hφcs.deriv.deriv
    exact (hcont.integrable_of_hasCompactSupport hcs).norm
  have hH_int : Integrable H := by
    rw [hH]
    exact integrable_finsetSum _ (fun α _ => (hφ_int.comp_sub_right (aα α)).const_mul _)
  have hG : ∀ y : ℝ, (∑ α ∈ A, F (y - aα α)) = H y * ee (c * y) := by
    intro y
    rw [hH, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    show φ (y - aα α) * ee (c * (y - aα α))
      = (ee (-(c * aα α)) * φ (y - aα α)) * ee (c * y)
    have harg : c * (y - aα α) = -(c * aα α) + c * y := by ring
    rw [harg, ← ee_add_]
    ring
  have hderiv : ∀ (n : ℕ), (n : ℕ∞) ≤ (2 : ℕ∞) → ∀ y : ℝ,
      iteratedDeriv n H y = ∑ α ∈ A, ee (-(c * aα α)) * iteratedDeriv n φ (y - aα α) := by
    intro n hn y
    have hn2 : n ≤ 2 := by exact_mod_cast hn
    have hφn : ContDiff ℝ n φ := hφcd.of_le (by exact_mod_cast hn2)
    have hfuns : (∑ α ∈ A, fun y : ℝ => ee (-(c * aα α)) * φ (y - aα α))
        = fun y : ℝ => ∑ α ∈ A, ee (-(c * aα α)) * φ (y - aα α) := by
      funext z
      rw [Finset.sum_apply]
    rw [hH, ← hfuns, iteratedDeriv_sum]
    · refine Finset.sum_congr rfl (fun α _ => ?_)
      rw [iteratedDeriv_const_mul]
      · rw [congrFun (iteratedDeriv_comp_sub_const n φ (aα α)) y]
      · exact (hφn.comp (contDiff_id.sub contDiff_const)).contDiffAt
    · intro α _
      exact (contDiff_const.mul (hφn.comp (contDiff_id.sub contDiff_const))).contDiffAt
  have hpt2 : ∀ y : ℝ, ‖iteratedDeriv 2 H y‖ ≤ ∑ α ∈ A, ‖iteratedDeriv 2 φ (y - aα α)‖ := by
    intro y
    rw [hderiv 2 le_rfl y]
    calc ‖∑ α ∈ A, ee (-(c * aα α)) * iteratedDeriv 2 φ (y - aα α)‖
        ≤ ∑ α ∈ A, ‖ee (-(c * aα α)) * iteratedDeriv 2 φ (y - aα α)‖ := norm_sum_le _ _
      _ ≤ ∑ α ∈ A, ‖iteratedDeriv 2 φ (y - aα α)‖ := by
          refine Finset.sum_le_sum (fun α _ => ?_)
          rw [norm_mul, norm_ee_, one_mul]
  have hdom2 : Integrable (fun y : ℝ => ∑ α ∈ A, ‖iteratedDeriv 2 φ (y - aα α)‖) :=
    integrable_finsetSum _ (fun α _ => (hiter_int 2 le_rfl).comp_sub_right (aα α))
  have hH2_int : Integrable (fun y : ℝ => iteratedDeriv 2 H y) := by
    have hcont : Continuous (iteratedDeriv 2 H) := hHcd.continuous_iteratedDeriv 2 le_rfl
    exact Integrable.mono' hdom2 hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall hpt2)
  have hpt0 : ∀ y : ℝ, ‖H y‖ ≤ ∑ α ∈ A, ‖φ (y - aα α)‖ := by
    intro y
    rw [hH]
    calc ‖∑ α ∈ A, ee (-(c * aα α)) * φ (y - aα α)‖
        ≤ ∑ α ∈ A, ‖ee (-(c * aα α)) * φ (y - aα α)‖ := norm_sum_le _ _
      _ ≤ ∑ α ∈ A, ‖φ (y - aα α)‖ := by
          refine Finset.sum_le_sum (fun α _ => ?_)
          rw [norm_mul, norm_ee_, one_mul]
  have hdom0 : Integrable (fun y : ℝ => ∑ α ∈ A, ‖φ (y - aα α)‖) :=
    integrable_finsetSum _ (fun α _ => (hφ_int.comp_sub_right (aα α)).norm)
  have hIntH : (∫ y : ℝ, ‖H y‖) ≤ cc * (∫ y : ℝ, ‖φ y‖) := by
    calc (∫ y : ℝ, ‖H y‖) ≤ ∫ y : ℝ, ∑ α ∈ A, ‖φ (y - aα α)‖ :=
          integral_mono hH_int.norm hdom0 hpt0
      _ = ∑ α ∈ A, ∫ y : ℝ, ‖φ (y - aα α)‖ :=
          integral_finsetSum _ (fun α _ => (hφ_int.comp_sub_right (aα α)).norm)
      _ = ∑ α ∈ A, ∫ y : ℝ, ‖φ y‖ := by
          refine Finset.sum_congr rfl (fun α _ => ?_)
          exact integral_sub_right_eq_self (fun y : ℝ => ‖φ y‖) (aα α)
      _ = cc * ∫ y : ℝ, ‖φ y‖ := by
          rw [Finset.sum_const, nsmul_eq_mul, hcc]
  have hIntH2 : (∫ y : ℝ, ‖iteratedDeriv 2 H y‖) ≤ cc * (∫ y : ℝ, ‖iteratedDeriv 2 φ y‖) := by
    calc (∫ y : ℝ, ‖iteratedDeriv 2 H y‖)
        ≤ ∫ y : ℝ, ∑ α ∈ A, ‖iteratedDeriv 2 φ (y - aα α)‖ :=
          integral_mono hH2_int.norm hdom2 hpt2
      _ = ∑ α ∈ A, ∫ y : ℝ, ‖iteratedDeriv 2 φ (y - aα α)‖ :=
          integral_finsetSum _ (fun α _ => (hiter_int 2 le_rfl).comp_sub_right (aα α))
      _ = ∑ α ∈ A, ∫ y : ℝ, ‖iteratedDeriv 2 φ y‖ := by
          refine Finset.sum_congr rfl (fun α _ => ?_)
          exact integral_sub_right_eq_self (fun y : ℝ => ‖iteratedDeriv 2 φ y‖) (aα α)
      _ = cc * ∫ y : ℝ, ‖iteratedDeriv 2 φ y‖ := by
          rw [Finset.sum_const, nsmul_eq_mul, hcc]
  have hH_int_all : ∀ n : ℕ, (n : ℕ∞) ≤ (2 : ℕ∞) → Integrable (iteratedDeriv n H) := by
    intro n hn
    have hn2 : n ≤ 2 := by exact_mod_cast hn
    have hcont : Continuous (iteratedDeriv n H) :=
      hHcd.continuous_iteratedDeriv n (by exact_mod_cast hn)
    have hdom : Integrable (fun y : ℝ => ∑ α ∈ A, ‖iteratedDeriv n φ (y - aα α)‖) :=
      integrable_finsetSum _ (fun α _ => (hiter_int n hn2).comp_sub_right (aα α))
    refine Integrable.mono' hdom hcont.aestronglyMeasurable (Filter.Eventually.of_forall ?_)
    intro y
    rw [hderiv n hn y]
    calc ‖∑ α ∈ A, ee (-(c * aα α)) * iteratedDeriv n φ (y - aα α)‖
        ≤ ∑ α ∈ A, ‖ee (-(c * aα α)) * iteratedDeriv n φ (y - aα α)‖ := norm_sum_le _ _
      _ ≤ ∑ α ∈ A, ‖iteratedDeriv n φ (y - aα α)‖ := by
          refine Finset.sum_le_sum (fun α _ => ?_)
          rw [norm_mul, norm_ee_, one_mul]
  have hker : ∀ j : ℤ, iwKernel (iwSymbolSet A (periodize F)) j = 𝓕 H ((j : ℝ) - c) := by
    intro j
    rw [Work.KMTPlan.A6.iwKernel_periodize_fourier A hFcd.continuous hFcs j]
    rw [funext hG]
    exact fourier_mul_ee H c (j : ℝ)
  have hb1 : ∀ x : ℝ, ‖𝓕 H x‖ ≤ (∫ y : ℝ, ‖H y‖) :=
    fun x => VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
  have hb2 : ∀ x : ℝ, x ≠ 0 →
      ‖𝓕 H x‖ ≤ (∫ y : ℝ, ‖iteratedDeriv 2 H y‖) / (2 * Real.pi * |x|) ^ 2 := by
    intro x hx
    have hF2 := Real.fourier_iteratedDeriv (f := H) (N := 2) (n := 2) hHcd hH_int_all
      (by norm_num)
    have hpt := congrFun hF2 x
    have hnorm : ‖𝓕 (iteratedDeriv 2 H) x‖ = (2 * Real.pi * |x|) ^ 2 * ‖𝓕 H x‖ := by
      rw [hpt, norm_smul, norm_pow]
      congr 1
      have hc1 : ‖(2 : ℂ)‖ = 2 := by norm_num
      have hc2 : ‖(Real.pi : ℂ)‖ = |Real.pi| := RCLike.norm_ofReal Real.pi
      have hc3 : ‖((x : ℝ) : ℂ)‖ = |x| := RCLike.norm_ofReal x
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one, hc1, hc2, hc3,
        abs_of_nonneg Real.pi_pos.le]
    have hbdd : ‖𝓕 (iteratedDeriv 2 H) x‖ ≤ (∫ y : ℝ, ‖iteratedDeriv 2 H y‖) :=
      VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
    have hden : 0 < (2 * Real.pi * |x|) ^ 2 := by
      have hxpos : 0 < |x| := abs_pos.mpr hx
      positivity
    rw [le_div_iff₀ hden, mul_comm, ← hnorm]
    exact hbdd
  set A' : ℝ := (∫ y : ℝ, ‖H y‖) + 1 / a with hA'
  set B' : ℝ := (∫ y : ℝ, ‖iteratedDeriv 2 H y‖) / (4 * Real.pi ^ 2) + 1 / a with hB'
  have hA'pos : 0 < A' := by rw [hA']; positivity
  have hB'pos : 0 < B' := by rw [hB']; positivity
  set s : ℝ := Real.sqrt (A' / B') with hs
  have hspos : 0 < s := Real.sqrt_pos.mpr (div_pos hA'pos hB'pos)
  have hs2 : s ^ 2 = A' / B' := Real.sq_sqrt (le_of_lt (div_pos hA'pos hB'pos))
  have hid : ∀ x : ℝ, 2 * A' * B' / (A' * x ^ 2 + B')
      = 2 * A' * (1 / (1 + (s * x) ^ 2)) := by
    intro x
    have hB'ne : B' ≠ 0 := ne_of_gt hB'pos
    have hden : (1 : ℝ) + (s * x) ^ 2 = (A' * x ^ 2 + B') / B' := by
      rw [mul_pow, hs2]
      field_simp
      try ring
    rw [hden, one_div_div, mul_div_assoc]
  have hpt_bound : ∀ j : ℤ,
      ‖iwKernel (iwSymbolSet A (periodize F)) j‖ ≤ 2 * A' / (1 + (s * ((j : ℝ) - c)) ^ 2) := by
    intro j
    rw [hker j]
    rcases eq_or_ne ((j : ℝ) - c) 0 with h0 | h0
    · rw [h0]
      have hb := hb1 0
      have hInt_nn : (0 : ℝ) ≤ ∫ y : ℝ, ‖H y‖ := integral_nonneg (fun y => norm_nonneg _)
      have hd : 2 * A' / (1 + (s * (0:ℝ)) ^ 2) = 2 * A' := by
        rw [mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero, div_one]
      rw [hd, hA']
      linarith [hb, hInt_nn, one_div_pos.mpr ha0]
    · have hA'ub : ‖𝓕 H ((j : ℝ) - c)‖ ≤ A' := by
        have hb := hb1 ((j : ℝ) - c)
        rw [hA']
        linarith [hb, one_div_pos.mpr ha0]
      have hB'ub : ‖𝓕 H ((j : ℝ) - c)‖ ≤ B' / ((j : ℝ) - c) ^ 2 := by
        have hb := hb2 ((j : ℝ) - c) h0
        have hden : (2 * Real.pi * |(j : ℝ) - c|) ^ 2
            = 4 * Real.pi ^ 2 * ((j : ℝ) - c) ^ 2 := by
          rw [mul_pow, sq_abs]
          ring
        rw [hden] at hb
        rw [hB']
        calc ‖𝓕 H ((j : ℝ) - c)‖
            ≤ (∫ y : ℝ, ‖iteratedDeriv 2 H y‖)
                / (4 * Real.pi ^ 2 * ((j : ℝ) - c) ^ 2) := hb
          _ = ((∫ y : ℝ, ‖iteratedDeriv 2 H y‖) / (4 * Real.pi ^ 2))
                / ((j : ℝ) - c) ^ 2 := by rw [div_div]
          _ ≤ ((∫ y : ℝ, ‖iteratedDeriv 2 H y‖) / (4 * Real.pi ^ 2) + 1 / a)
                / ((j : ℝ) - c) ^ 2 := by
              refine div_le_div_of_nonneg_right ?_ (by positivity)
              exact le_add_of_nonneg_right (by positivity)
      have hmin := min_le_harmonic hA'pos hB'pos (u := A') (v := B') (t := (j : ℝ) - c)
      refine le_trans (le_min hA'ub hB'ub) ?_
      exact le_trans hmin (le_of_eq (by rw [hid ((j : ℝ) - c), mul_one_div]))
  have hmaj_summ : Summable (fun j : ℤ => 2 * A' / (1 + (s * ((j : ℝ) - c)) ^ 2)) := by
    have hbase := (tsum_one_div_one_add_sq_mul_le s hspos c).1
    simpa only [mul_one_div] using hbase.mul_left (2 * A')
  have hsumm_kern : Summable (fun j : ℤ => ‖iwKernel (iwSymbolSet A (periodize F)) j‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) hpt_bound hmaj_summ
  have hsum_le : (∑' j : ℤ, ‖iwKernel (iwSymbolSet A (periodize F)) j‖)
      ≤ ∑' j : ℤ, 2 * A' / (1 + (s * ((j : ℝ) - c)) ^ 2) :=
    Summable.tsum_le_tsum hpt_bound hsumm_kern hmaj_summ
  have hmaj_val : (∑' j : ℤ, 2 * A' / (1 + (s * ((j : ℝ) - c)) ^ 2))
      ≤ 2 * A' * (2 + Real.pi / s) := by
    have h := (tsum_one_div_one_add_sq_mul_le s hspos c).2
    calc (∑' j : ℤ, 2 * A' / (1 + (s * ((j : ℝ) - c)) ^ 2))
        = 2 * A' * ∑' j : ℤ, 1 / (1 + (s * ((j : ℝ) - c)) ^ 2) := by
          rw [← tsum_mul_left]
          exact tsum_congr (fun j => by rw [mul_one_div])
      _ ≤ 2 * A' * (2 + Real.pi / s) := mul_le_mul_of_nonneg_left h (by positivity)
  have hAs : A' / s = Real.sqrt (A' * B') := by
    have hsq : (A' / s) ^ 2 = A' * B' := by
      rw [div_pow, hs2]
      first | (field_simp; ring) | field_simp | ring_nf
    rw [← hsq, Real.sqrt_sq (by positivity)]
  have hfinal_le : (∑' j : ℤ, ‖iwKernel (iwSymbolSet A (periodize F)) j‖)
      ≤ 4 * A' + 2 * Real.pi * Real.sqrt (A' * B') := by
    calc (∑' j : ℤ, ‖iwKernel (iwSymbolSet A (periodize F)) j‖)
        ≤ 2 * A' * (2 + Real.pi / s) := le_trans hsum_le hmaj_val
      _ = 4 * A' + 2 * Real.pi * (A' / s) := by ring_nf
      _ = 4 * A' + 2 * Real.pi * Real.sqrt (A' * B') := by rw [hAs]
  have hA'le : A' ≤ P / a := by
    rw [hA', hP, add_div]
    have hInt : (∫ y : ℝ, ‖H y‖) ≤ cc * (A₀ / a) :=
      le_trans hIntH (mul_le_mul_of_nonneg_left h1 hcc0)
    rw [mul_div] at hInt
    linarith [hInt]
  have hB'le : B' ≤ Q * a + 1 / a := by
    rw [hB', hQ]
    have hInt : (∫ y : ℝ, ‖iteratedDeriv 2 H y‖) ≤ cc * (B₀ * a) :=
      le_trans hIntH2 (mul_le_mul_of_nonneg_left h2 hcc0)
    have hrew : cc * B₀ / (4 * Real.pi ^ 2) * a = cc * (B₀ * a) / (4 * Real.pi ^ 2) := by
      ring_nf
    rw [hrew]
    have hstep : (∫ y : ℝ, ‖iteratedDeriv 2 H y‖) / (4 * Real.pi ^ 2)
        ≤ cc * (B₀ * a) / (4 * Real.pi ^ 2) :=
      div_le_div_of_nonneg_right hInt (by positivity)
    linarith
  have hprod : A' * B' ≤ P * (Q + 1) := by
    have h1' : A' * B' ≤ (P / a) * (Q * a + 1 / a) :=
      mul_le_mul hA'le hB'le (le_of_lt hB'pos) (by rw [hP]; positivity)
    have heq : (P / a) * (Q * a + 1 / a) = P * Q + P / a ^ 2 := by
      first | (field_simp; ring) | field_simp | ring_nf
    have hle : P / a ^ 2 ≤ P := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < a ^ 2)]
      have ha2 : 1 ≤ a ^ 2 := by nlinarith
      nlinarith [hP0.le, ha2]
    have hdist : P * (Q + 1) = P * Q + P := by ring
    rw [hdist]
    linarith [h1', le_of_eq heq, hle]
  have hA'P : A' ≤ P := by
    refine le_trans hA'le ?_
    rw [div_le_iff₀ ha0]
    nlinarith [hP0.le, ha1]
  have hmain : (∑' j : ℤ, ‖iwKernel (iwSymbolSet A (periodize F)) j‖)
      ≤ 4 * P + 2 * Real.pi * Real.sqrt (P * (Q + 1)) := by
    refine le_trans hfinal_le ?_
    have hsq : Real.sqrt (A' * B') ≤ Real.sqrt (P * (Q + 1)) := Real.sqrt_le_sqrt hprod
    have h4 : 4 * A' ≤ 4 * P := by linarith
    have h2' : 2 * Real.pi * Real.sqrt (A' * B')
        ≤ 2 * Real.pi * Real.sqrt (P * (Q + 1)) :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    exact add_le_add h4 h2'
  have hconv : 4 * P + 2 * Real.pi * Real.sqrt (P * (Q + 1))
      = 4 * ((A.card : ℝ) * A₀ + 1)
        + 2 * Real.pi * Real.sqrt (((A.card : ℝ) * A₀ + 1)
            * ((A.card : ℝ) * B₀ / (4 * Real.pi ^ 2) + 1)) := by
    rw [hP, hQ, hcc]
  rw [hconv] at hmain
  exact hmain

/-! ## §4. The target -/

/-- **The single-scale `ℓᵖ` bound for the modulated KMT bump in the narrow-bump regime.**  For
every `ρ > 0`, `l ∈ ℕ` and `1 < p < ∞` there is a constant `C` such that the Ionescu–Wainger
projection `Tle ρ l (varphiNt N k₁ t)` is bounded on `ℓᵖ(ℤ)` by `C`, *uniformly* in `N : ℕ`,
`k₁ : ℕ`, `t ∈ [1/2,1]` **subject to the narrow-bump restriction `2 ^ k₁ ≤ N`** (equivalently
`k₁ ≤ Log N`, the regime in which `varphiN N k₁ = η(a·) - η(2a·)` has `a = 2^{Log N - k₁} ≥ 1`,
so the bump has radius `≤ 1`).

The restriction is necessary: without it the statement is FALSE.  Take `l = 0` (so
`iwArithFreqs ρ 0 = {0}`), `N = 1`, `t = 1`, `f = δ₀`; then
`(Tle ρ 0 (varphiNt 1 k₁ 1) δ₀) 1 = 2^{k₁-1} ∫η → ∞` as `k₁ → ∞`, because in the wide-bump regime
`∫ varphiN N k₁ = 2^{k₁-Log N-1}∫η` diverges (the review of this statement found exactly this
counterexample).  In the restricted regime, `varphiN N k₁` is a mean-zero bump of radius `≤ 1` and
the ℓ¹-mass of the convolution kernel is `O(|(ℚ/ℤ)_{≤l}|)`, uniformly in `N, k₁, t`.

This is the constant-cost estimate used for the finitely many *coarse* (non-narrow) scales of the
case split in `Work.KMTAreas.A7.lacunaryBumpVarEstimate`: there `L = max (max l₁ l₂) (max k₁ k₂)`
is bounded, `core` gives `k₁ ≤ Log N`, only `O(ρ,C₀,Λ)`-many scales occur, and each may be bounded
crudely.  Routes: (i) the `ℓ¹`-kernel bound (`Work.KMTAreas.A7.Tle_varphiNt_bounded`) plus Young's
inequality (`Submission.Commons.Analysis.Convolution.eLpNorm_convolution_le_complex`); (ii) the
Magyar–Stein–Wainger single-torsion sampling principle
(`Submission/Work/KMTAreas/MSW_single_torsion.lean`) plus the finite union over
`iwArithFreqs ρ l` (`Work.KMTAreas.IWLqBound_of_singleton_bounds`), whose loss is the *constant*
`card (iwArithFreqs ρ l)`. -/
theorem Tle_varphiNt_single_scale (ρ : ℝ) (hρ : 0 < ρ) (l : ℕ) (p : ENNReal) (hp : 1 < p)
    (hptop : p < ⊤) :
    ∃ C : NNReal, 0 < C ∧ ∀ (N k₁ : ℕ) (hNk : 2 ^ k₁ ≤ N) (t : ℝ)
      (ht : t ∈ Set.Icc (1 / 2 : ℝ) 1) (f : ℤ → ℂ),
      MeasureTheory.eLpNorm (Work.KMTAreas.A7.Tle ρ l (Work.KMTAreas.A7.varphiNt N k₁ t) f)
          p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C : ℝ) * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  classical
  set cc : ℝ := ((iwArithFreqs ρ l).card : ℝ) with hcc
  set Iη : ℝ := ∫ y : ℝ, ‖Work.KMTContract.kmtEta y‖ with hIη
  set Iη2 : ℝ := ∫ y : ℝ, ‖iteratedDeriv 2 Work.KMTContract.kmtEta y‖ with hIη2
  have hIη_nn : (0 : ℝ) ≤ Iη := by
    rw [hIη]; exact integral_nonneg (fun y => norm_nonneg _)
  have hIη2_nn : (0 : ℝ) ≤ Iη2 := by
    rw [hIη2]; exact integral_nonneg (fun y => norm_nonneg _)
  set A₀ : ℝ := 3 / 2 * Iη with hA₀
  set B₀ : ℝ := 3 * Iη2 with hB₀
  have hA₀nn : (0 : ℝ) ≤ A₀ := by
    rw [hA₀]; exact mul_nonneg (by norm_num) hIη_nn
  have hB₀nn : (0 : ℝ) ≤ B₀ := by
    rw [hB₀]; exact mul_nonneg (by norm_num) hIη2_nn
  set P : ℝ := cc * A₀ + 1 with hP
  set Q : ℝ := cc * B₀ / (4 * Real.pi ^ 2) with hQ
  set M : ℝ := 4 * P + 2 * Real.pi * Real.sqrt (P * (Q + 1)) with hM
  have hP0 : (0 : ℝ) < P := by
    rw [hP]
    have hcard : (0 : ℝ) ≤ ((iwArithFreqs ρ l).card : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hMpos : (0 : ℝ) < M := by
    rw [hM]
    have h1 : (0 : ℝ) < 4 * P := by linarith
    have h2 : (0 : ℝ) ≤ 2 * Real.pi * Real.sqrt (P * (Q + 1)) :=
      mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) (Real.sqrt_nonneg _)
    linarith
  have hM0 : (0 : ℝ) ≤ M := le_of_lt hMpos
  refine ⟨Real.toNNReal M, Real.toNNReal_pos.mpr hMpos, ?_⟩
  intro N k₁ hNk t ht f
  set a : ℝ := (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k₁ : ℝ)) with ha
  have hb := varphiN_mass_bounds N k₁ hNk
  have ha1 : 1 ≤ a := by rw [ha]; exact hb.2.2
  have hb1' : (∫ y : ℝ, ‖varphiN N k₁ y‖) ≤ A₀ / a := by
    rw [ha, hA₀, hIη]
    exact hb.1
  have hb2' : (∫ y : ℝ, ‖iteratedDeriv 2 (varphiN N k₁) y‖) ≤ B₀ * a := by
    have h := hb.2.1
    rw [ha, hB₀, hIη2]
    ring_nf at h ⊢
    linarith [h]
  have hmass : (∑' j : ℤ, ‖iwKernel
        (iwSymbolSet (iwArithFreqs ρ l) (periodize (varphiNt N k₁ t))) j‖) ≤ M := by
    have hker := kernel_mass_of_modulated_bump (A := iwArithFreqs ρ l) (φ := varphiN N k₁)
      (c := (N : ℝ) * t) (a := a) (A₀ := A₀) (B₀ := B₀)
      (contDiff_varphiN N k₁) (hasCompactSupport_varphiN N k₁) ha1 hA₀nn hB₀nn hb1' hb2'
    have hfun : (fun y : ℝ => varphiN N k₁ y * ee (((N : ℝ) * t) * y)) = varphiNt N k₁ t := rfl
    rw [hfun] at hker
    refine le_trans hker ?_
    rw [hM, hP, hQ, hcc]
  have hsumm : Summable (fun j : ℤ => ‖iwKernel
      (iwSymbolSet (iwArithFreqs ρ l) (periodize (varphiNt N k₁ t))) j‖) := by
    obtain ⟨-, ⟨Ck, hCkpos, hCk⟩, -⟩ := varphiNt_IW_facts ρ l N k₁ t
    have hbnd : ∀ j : ℤ, ‖iwKernel
        (iwSymbolSet (iwArithFreqs ρ l) (periodize (varphiNt N k₁ t))) j‖
        ≤ Ck * ‖kmtKernWeight j‖ := by
      intro j
      rw [norm_kmtKernWeight j]
      exact (hCk j).trans_eq (div_eq_mul_one_div Ck _)
    exact Summable.of_nonneg_of_le (fun j => norm_nonneg _) hbnd
      (summable_kmtKernWeight.mul_left Ck)
  have hyoung := eLpNorm_iwConv_le_of_kernelL1_aux (A := iwArithFreqs ρ l)
    (Φ := periodize (varphiNt N k₁ t)) hp hptop hM0 hsumm hmass f
  calc eLpNorm (Tle ρ l (varphiNt N k₁ t) f) p Measure.count
      = eLpNorm (iwConv (iwArithFreqs ρ l) (periodize (varphiNt N k₁ t)) f) p Measure.count :=
        rfl
    _ ≤ ENNReal.ofReal M * eLpNorm f p Measure.count := hyoung
    _ ≤ ENNReal.ofReal ((Real.toNNReal M : NNReal) : ℝ) * eLpNorm f p Measure.count := by
        rw [Real.coe_toNNReal M hM0]

end

end Work.KMTAreas.A7
