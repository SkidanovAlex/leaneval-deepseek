import Mathlib
import Submission.Work.FIArea4.Vflip.Vfd.VfdDefs
import Submission.Work.FIArea4.Vflip.Vfd.SepDefs
import Submission.Work.FIArea4.Vflip.sepG_mellin
import Submission.Work.FIArea4.Vflip.sepG_decay
import Submission.Work.FIArea4.Vflip.separation_ineq
import Submission.Work.FIArea4.Vflip.Vfd.fourier_l1_sqrt
import Submission.Work.FIArea4.Vflip.Vfd.dilation_fourier_l1
import Submission.Work.FIArea4.Vflip.Vfd.dyadic_partition_sum
import Submission.Work.FIArea4.Vflip.Vfd.chat_fourier_inversion
import Submission.Work.FIArea4.Vflip.Vfd.contDiff_fcut
import Submission.Work.FIArea4.Vflip.Vfd.fcut_piece_l1

/-!
# The near-cut separation inequality, uniform in `a, b`

This file proves `separation_ineq_nearCut`: the Fourier–Mellin separation inequality for the
weight `bump (|x|*y) * nearCut a b x`, with a constant **uniform** in `a, b` (the dependence on
`a, b` being only the factor `(log (2 + b/a) + 1)^2`).

The proof follows Friedlander–Iwaniec (12.13)–(12.14): the weight is expanded as a product of the
Mellin inversion of `bump` (`sepG_mellin`, `sepG_decay`) and the additive Fourier expansion of the
chirped cutoff `chat a b α x = nearCut a b x * |x|^{iα}`.  The `L¹`-norm of the latter,
`chat_fourier_l1`, is uniform in `a, b` (this is the content of the paper's `(log 2H)²`).
-/

namespace Work.FIArea4.Vflip.Vfd

open MeasureTheory
open scoped FourierTransform

noncomputable section

/-- The rescaled chirped cutoff is a dilation of `chat`: `chat a b α x = a^{iα} fcut (a/b) α (x/a)`. -/
lemma chat_eq_scaled (a b α : ℝ) (ha : 0 < a) (hb : 0 < b) :
    chat a b α = fun x : ℝ => ((a : ℂ) ^ (Complex.I * (α : ℂ))) * fcut (a / b) α (x / a) := by
  funext x
  rw [chat, fcut, nearCut_eq a b x ha.ne' hb.ne', Complex.ofReal_mul]
  have h1 : (a / b) * (x / a) = x / b := by field_simp
  rw [h1]
  have h2 : |x / a| = |x| / a := by rw [abs_div, abs_of_pos ha]
  rw [h2]
  have h3 : ((|x| : ℝ) : ℂ) ^ (Complex.I * (α : ℂ)) =
      ((a : ℝ) : ℂ) ^ (Complex.I * (α : ℂ)) *
        (((|x| / a : ℝ)) : ℂ) ^ (Complex.I * (α : ℂ)) := by
    conv_lhs => rw [show (|x| : ℝ) = a * (|x| / a) by field_simp]
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg ha.le (by positivity)]
  rw [h3]; ring

/-- The Fourier transform is compatible with multiplication by a constant: `𝓕 (c · f) = c · 𝓕 f`. -/
lemma fourier_const_mul (c : ℂ) (f : ℝ → ℂ) :
    𝓕 (fun x : ℝ => c * f x) = fun ξ : ℝ => c * 𝓕 f ξ := by
  funext ξ
  rw [Real.fourier_eq', Real.fourier_eq']
  simp only [Real.inner_apply]
  rw [← MeasureTheory.integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [smul_eq_mul]
  ring

/-- The Fourier transform of a finite sum is the finite sum of the Fourier transforms. -/
lemma fourier_finsetSum {ι : Type*} (f : ι → ℝ → ℂ) (s : Finset ι)
    (hf : ∀ i ∈ s, Integrable (f i)) :
    𝓕 (∑ i ∈ s, f i) = ∑ i ∈ s, 𝓕 (f i) := by
  funext ξ
  have hInt : ∀ i ∈ s, Integrable (fun v : ℝ =>
      Complex.exp (↑(-2 * Real.pi * (v * ξ)) * Complex.I) * f i v) := by
    intro i hi
    have h1 : Integrable (fun v : ℝ =>
        f i v * Complex.exp (↑(-2 * Real.pi * (v * ξ)) * Complex.I)) :=
      Integrable.mul_of_norm_le (hf i hi) 1
        (fun v => le_of_eq (Complex.norm_exp_ofReal_mul_I (-2 * Real.pi * (v * ξ)))) (by fun_prop)
    have h2 : (fun v : ℝ => Complex.exp (↑(-2 * Real.pi * (v * ξ)) * Complex.I) * f i v)
        = fun v : ℝ => f i v * Complex.exp (↑(-2 * Real.pi * (v * ξ)) * Complex.I) := by
      funext v; ring
    rw [h2]; exact h1
  rw [Real.fourier_eq']
  simp only [Finset.sum_apply, Real.fourier_eq', Real.inner_apply, smul_eq_mul]
  simp only [Finset.mul_sum]
  rw [← MeasureTheory.integral_finsetSum s hInt]

/-- The `L¹`-norm of `𝓕 (chat a b α)` equals that of `𝓕 (fcut (a/b) α)`. -/
lemma chat_l1_eq (a b α : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ ξ : ℝ, ‖𝓕 (chat a b α) ξ‖) = ∫ ξ : ℝ, ‖𝓕 (fcut (a / b) α) ξ‖ := by
  rw [chat_eq_scaled a b α ha hb, fourier_const_mul]
  have h3 : (∫ ξ : ℝ, ‖((a : ℂ) ^ (Complex.I * (α : ℂ))) *
        𝓕 (fun x : ℝ => fcut (a / b) α (x / a)) ξ‖)
      = ∫ ξ : ℝ, ‖𝓕 (fun x : ℝ => fcut (a / b) α (x / a)) ξ‖ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [norm_mul, norm_cpow_imag a ha α, one_mul]
  rw [h3]
  have h4 : (fun x : ℝ => fcut (a / b) α (x / a))
      = fun x : ℝ => fcut (a / b) α (a⁻¹ * x) := by
    funext x
    have hx : x / a = a⁻¹ * x := by rw [div_eq_inv_mul, mul_comm]
    rw [hx]
  rw [h4, dilation_fourier_l1 (fcut (a / b) α) a⁻¹ (inv_ne_zero ha.ne')]

/-- The Mellin factor `bump` is supported in `[1/2, 5/2]`. -/
lemma bump_supp : ∀ y : ℝ, (y ≤ 1 / 2 ∨ 5 / 2 ≤ y) → Work.FIArea4.Vflip.bump y = 0 :=
  fun y hy => hy.elim bump_eq_zero_of_le bump_eq_zero_of_ge

lemma nearCut_zero (a b : ℝ) (ha : 0 < a) : Work.FIArea4.Vflip.nearCut a b 0 = 0 := by
  unfold Work.FIArea4.Vflip.nearCut
  have h1 : 4 * (0:ℝ) ^ 2 - a ^ 2 = -a ^ 2 := by ring
  rw [h1, neg_div, div_self (ne_of_gt (pow_pos ha 2)),
    Real.smoothTransition.zero_of_nonpos (show (-1 : ℝ) ≤ 0 by norm_num)]
  ring

lemma norm_cpow_imag_nonneg (r : ℝ) (hr : 0 ≤ r) (s : ℝ) :
    ‖((r : ℝ) : ℂ) ^ (Complex.I * (s : ℂ))‖ ≤ 1 := by
  rcases eq_or_lt_of_le hr with h | h
  · subst h
    rw [Complex.ofReal_zero]
    by_cases hz : Complex.I * (s : ℂ) = 0
    · rw [hz, Complex.cpow_zero]; norm_num
    · rw [Complex.zero_cpow hz]; norm_num
  · rw [norm_cpow_imag r h s]
/-! ## Dyadic pieces of the rescaled chirped cutoff -/

/-- The even dyadic partition bump `χ(t) = η(t) + η(-t) = η(|t|)`. -/
def dyadChi (t : ℝ) : ℝ := dyadEta t + dyadEta (-t)

lemma dyadChi_eq (t : ℝ) : dyadChi t = dyadEta |t| := by
  unfold dyadChi
  rcases le_total 0 t with h | h
  · rw [abs_of_nonneg h, dyadEta_eq_zero_of_le (by linarith : -t ≤ 1 / 2), add_zero]
  · rw [abs_of_nonpos h, dyadEta_eq_zero_of_le (by linarith : t ≤ 1 / 2), zero_add]

lemma contDiff_dyadChi : ContDiff ℝ (⊤ : ℕ∞) dyadChi := by
  unfold dyadChi
  exact contDiff_dyadEta.add (contDiff_dyadEta.comp (by fun_prop))

/-- The piece cutoffs `u ↦ χ(u / 2^j)` have compact support. -/
lemma hasCompactSupport_dyadChi_div (j : ℤ) :
    HasCompactSupport (fun u : ℝ => (dyadChi (u / (2 : ℝ) ^ j) : ℂ)) := by
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ j := zpow_pos (by norm_num) j
  refine HasCompactSupport.of_support_subset_isCompact
    (K := Set.Icc (-(2 * (2 : ℝ) ^ j)) (2 * (2 : ℝ) ^ j)) isCompact_Icc ?_
  rw [Function.support_subset_iff]
  intro u hu
  rw [Set.mem_Icc, ← abs_le]
  have hne : dyadChi (u / (2 : ℝ) ^ j) ≠ 0 := by
    intro h; exact hu (by rw [h]; simp)
  rw [dyadChi_eq, abs_div, abs_of_pos h2pos] at hne
  have h2 := (dyadEta_support hne).2
  rwa [div_le_iff₀ h2pos] at h2

/-- The `j`-th dyadic piece of the rescaled chirped cutoff `fcut ε α`. -/
def fcutPiece (ε α : ℝ) (j : ℤ) : ℝ → ℂ :=
  fun u => (dyadChi (u / (2 : ℝ) ^ j) : ℂ) * fcut ε α u

lemma fcutPiece_eq (ε α : ℝ) (j : ℤ) :
    fcutPiece ε α j = fun u : ℝ => (dyadEta (|u| / (2 : ℝ) ^ j) : ℂ) * fcut ε α u := by
  funext u
  simp only [fcutPiece, dyadChi_eq, abs_div,
    abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) j)]

/-- If `fcut ε α u ≠ 0` then `u` lies in the geometric range of the two cutoffs. -/
lemma fcut_ne_zero {ε α u : ℝ} (hε : 0 < ε) (hu : fcut ε α u ≠ 0) :
    1 / 2 < |u| ∧ |u| < 2 / ε := by
  have hphi : cutPhi u ≠ 0 := by intro h; exact hu (by simp [fcut, h])
  have hpsi : cutPsi (ε * u) ≠ 0 := by intro h; exact hu (by simp [fcut, h])
  refine ⟨?_, ?_⟩
  · by_contra hc
    exact hphi (cutPhi_eq_zero_of_abs_le (not_lt.mp hc))
  · by_contra hc
    have hc' : 2 / ε ≤ |u| := le_of_not_gt hc
    have h2 : (2 : ℝ) ≤ |ε * u| := by
      rw [abs_mul, abs_of_pos hε]
      calc (2 : ℝ) = ε * (2 / ε) := by
            rw [← mul_div_assoc]; exact (mul_div_cancel_left₀ 2 (ne_of_gt hε)).symm
        _ ≤ ε * |u| := mul_le_mul_of_nonneg_left hc' hε.le
    have h4 : (4 : ℝ) ≤ (ε * u) ^ 2 := by
      have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h2 2
      rw [sq_abs] at h
      norm_num1 at h
      exact h
    exact hpsi (cutPsi_eq_zero_of_sq_ge h4)

lemma contDiff_fcutPiece (ε α : ℝ) (hε : 0 < ε) (j : ℤ) :
    ContDiff ℝ (⊤ : ℕ∞) (fcutPiece ε α j) := by
  obtain ⟨hf, -⟩ := contDiff_fcut ε α hε
  have hchi : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => (dyadChi (u / (2 : ℝ) ^ j) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      (contDiff_dyadChi.comp (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => u / (2 : ℝ) ^ j)))
  have h := hchi.mul hf
  show ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => (dyadChi (u / (2 : ℝ) ^ j) : ℂ) * fcut ε α u)
  exact h

lemma hasCompactSupport_fcutPiece (ε α : ℝ) (j : ℤ) : HasCompactSupport (fcutPiece ε α j) := by
  have h1 := hasCompactSupport_dyadChi_div j
  unfold fcutPiece
  exact h1.mul_right

/-- The number of dyadic pieces: the interval of integers `[-1, ⌈log₂ (2/ε)⌉]` has at most
`6 (log (2 + 1/ε) + 1)` elements. -/
lemma card_dyadic_Icc_le (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ((Finset.Icc (-1) ((Nat.ceil (Real.logb 2 (2 / ε)) : ℕ) : ℤ)).card : ℝ)
      ≤ 6 * (Real.log (2 + 1 / ε) + 1) := by
  set n : ℕ := Nat.ceil (Real.logb 2 (2 / ε)) with hn
  have hL0 : (0 : ℝ) ≤ Real.log (2 + 1 / ε) := by
    apply Real.log_nonneg
    have : (0 : ℝ) < 1 / ε := by positivity
    linarith
  have hcard : ((Finset.Icc (-1) (n : ℤ)).card : ℝ) ≤ (n : ℝ) + 2 := by
    rw [Int.card_Icc]
    have hz : Int.toNat ((n : ℤ) + 1 - (-1)) ≤ n + 2 := by
      rw [Int.toNat_le]; push_cast; linarith
    have hz2 : ((Int.toNat ((n : ℤ) + 1 - (-1)) : ℕ) : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by
      exact_mod_cast hz
    have hz3 : ((n + 2 : ℕ) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
    linarith
  have hn_le : (n : ℝ) ≤ Real.logb 2 (2 / ε) + 1 := by
    have hb : (0 : ℝ) ≤ Real.logb 2 (2 / ε) := by
      refine Real.logb_nonneg (by norm_num) ?_
      rw [one_le_div hε]; linarith
    have := Nat.ceil_lt_add_one hb
    rw [← hn] at this
    linarith
  have hlogb : Real.logb 2 (2 / ε) ≤ 3 * Real.log (2 + 1 / ε) := by
    have hlog2 : (0 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hsplit : Real.log (2 / ε) = Real.log 2 + Real.log (1 / ε) := by
      rw [one_div, div_eq_mul_inv, Real.log_mul (by norm_num) (ne_of_gt (by positivity : (0:ℝ) < ε⁻¹))]
    have hle1 : Real.log (1 / ε) ≤ Real.log (2 + 1 / ε) :=
      Real.log_le_log (by positivity) (by linarith)
    have hεinv : (0 : ℝ) ≤ 1 / ε := by positivity
    have hle2 : Real.log 2 ≤ Real.log (2 + 1 / ε) :=
      Real.log_le_log (by norm_num) (by linarith)
    have h2L : Real.log (2 / ε) ≤ 2 * Real.log (2 + 1 / ε) := by rw [hsplit]; linarith
    unfold Real.logb
    rw [div_le_iff₀ hlog2]
    calc Real.log (2 / ε) ≤ 2 * Real.log (2 + 1 / ε) := h2L
      _ ≤ 3 * Real.log (2 + 1 / ε) * Real.log 2 := by
          have key : (0 : ℝ) ≤ 3 * Real.log 2 - 2 := by linarith [Real.log_two_gt_d9]
          nlinarith [mul_nonneg hL0 key]
  calc ((Finset.Icc (-1) (n : ℤ)).card : ℝ) ≤ (n : ℝ) + 2 := hcard
    _ ≤ Real.logb 2 (2 / ε) + 3 := by linarith
    _ ≤ 3 * Real.log (2 + 1 / ε) + 3 := by linarith
    _ ≤ 6 * (Real.log (2 + 1 / ε) + 1) := by nlinarith [hL0]

/-- **The `L¹`-bound for the rescaled chirped cutoff**, obtained by summing the dyadic pieces:
the pieces number `≲ log(2 + 1/ε)` and each contributes `O((1+|α|)²)`. -/
theorem fcut_fourier_l1 :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε α : ℝ), 0 < ε → ε ≤ 1 →
      ∫ ξ : ℝ, ‖𝓕 (fcut ε α) ξ‖ ≤ C * (1 + |α|) ^ 2 * (Real.log (2 + 1 / ε) + 1) := by
  obtain ⟨Cp, hCppos, hCp⟩ := fcut_piece_l1
  refine ⟨max 1 (Cp * 6), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro ε α hε hε1
  set n : ℕ := Nat.ceil (Real.logb 2 (2 / ε)) with hn
  set J : Finset ℤ := Finset.Icc (-1) (n : ℤ) with hJ
  have hpart : ∀ u : ℝ, fcut ε α u = ∑ j ∈ J, fcutPiece ε α j u := by
    intro u
    by_cases hu : fcut ε α u = 0
    · simp [fcutPiece, hu]
    · obtain ⟨hu1, hu2⟩ := fcut_ne_zero hε hu
      have hne0 : u ≠ 0 := by rintro rfl; rw [abs_zero] at hu1; norm_num at hu1
      have hm : (2 : ℝ) ^ (-1 : ℤ) ≤ |u| := by rw [zpow_neg_one]; norm_num1; linarith
      have hn' : |u| ≤ (2 : ℝ) ^ ((n : ℤ)) := by
        have h1 : 2 / ε ≤ (2 : ℝ) ^ ((n : ℝ)) := by
          refine le_trans (Real.rpow_logb (b := 2) (x := 2 / ε) (by norm_num) (by norm_num)
            (by positivity)).ge ?_
          exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) (Nat.le_ceil _)
        rw [Real.rpow_natCast] at h1
        rw [zpow_natCast]
        linarith
      have hsum0 : (∑ j ∈ J, dyadEta (|u| / (2 : ℝ) ^ j)) = 1 :=
        dyadic_partition_sum |u| (abs_pos.mpr hne0) (-1) (n : ℤ) hm hn'
      have hcongr : ∀ j : ℤ, dyadChi (u / (2 : ℝ) ^ j) = dyadEta (|u| / (2 : ℝ) ^ j) := by
        intro j
        rw [dyadChi_eq, abs_div, abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) j)]
      have hcast : (∑ j ∈ J, (dyadChi (u / (2 : ℝ) ^ j) : ℂ))
          = ((∑ j ∈ J, dyadEta (|u| / (2 : ℝ) ^ j) : ℝ) : ℂ) := by
        rw [Complex.ofReal_sum]
        exact Finset.sum_congr rfl (fun j _ => by rw [hcongr j])
      have hsumC : (∑ j ∈ J, (dyadChi (u / (2 : ℝ) ^ j) : ℂ)) = 1 := by
        rw [hcast, hsum0, Complex.ofReal_one]
      simp only [fcutPiece]
      rw [← Finset.sum_mul, hsumC, one_mul]
  have hFsum : (fcut ε α : ℝ → ℂ) = ∑ j ∈ J, fcutPiece ε α j := by
    funext u; rw [Finset.sum_apply]; exact hpart u
  have hIntP : ∀ j ∈ J, Integrable (fcutPiece ε α j) := by
    intro j _
    have hcd := contDiff_fcutPiece ε α hε j
    have hcs := hasCompactSupport_fcutPiece ε α j
    let S : SchwartzMap ℝ ℂ := hcs.toSchwartzMap hcd
    have h : Integrable (⇑S) := S.integrable (μ := volume)
    exact h
  have hFourier : 𝓕 (fcut ε α) = ∑ j ∈ J, 𝓕 (fcutPiece ε α j) := by
    rw [hFsum]
    exact fourier_finsetSum (fcutPiece ε α) J hIntP
  have hInt : ∀ j ∈ J, Integrable (fun ξ : ℝ => ‖𝓕 (fcutPiece ε α j) ξ‖) := by
    intro j hj
    have hcd := contDiff_fcutPiece ε α hε j
    have hcs := hasCompactSupport_fcutPiece ε α j
    let S : SchwartzMap ℝ ℂ := hcs.toSchwartzMap hcd
    have h2 : Integrable (𝓕 (fcutPiece ε α j)) := by
      have h := (𝓕 S : SchwartzMap ℝ ℂ).integrable (μ := volume)
      rw [SchwartzMap.fourier_coe] at h
      exact h
    exact h2.norm
  have hcardJ : (J.card : ℝ) ≤ 6 * (Real.log (2 + 1 / ε) + 1) := by
    rw [hJ, hn]; exact card_dyadic_Icc_le ε hε hε1
  calc ∫ ξ : ℝ, ‖𝓕 (fcut ε α) ξ‖
      = ∫ ξ : ℝ, ‖∑ j ∈ J, 𝓕 (fcutPiece ε α j) ξ‖ := by
        rw [hFourier]; simp only [Finset.sum_apply]
    _ ≤ ∫ ξ : ℝ, ∑ j ∈ J, ‖𝓕 (fcutPiece ε α j) ξ‖ := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ξ => norm_nonneg _)
          (MeasureTheory.integrable_finsetSum J (fun j hj => hInt j hj))
          (Filter.Eventually.of_forall fun ξ => ?_)
        exact norm_sum_le _ _
    _ = ∑ j ∈ J, ∫ ξ : ℝ, ‖𝓕 (fcutPiece ε α j) ξ‖ :=
        MeasureTheory.integral_finsetSum J (fun j hj => hInt j hj)
    _ ≤ ∑ j ∈ J, Cp * (1 + |α|) ^ 2 := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        have := hCp ε α hε hε1 j
        rwa [← fcutPiece_eq ε α j] at this
    _ = J.card • (Cp * (1 + |α|) ^ 2) := Finset.sum_const _
    _ ≤ 6 * (Real.log (2 + 1 / ε) + 1) * (Cp * (1 + |α|) ^ 2) := by
        rw [nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right hcardJ (by positivity)
    _ ≤ max 1 (Cp * 6) * (1 + |α|) ^ 2 * (Real.log (2 + 1 / ε) + 1) := by
        have hlog : (0 : ℝ) ≤ Real.log (2 + 1 / ε) + 1 := by linarith
        have h2 : (0 : ℝ) ≤ (1 + |α|) ^ 2 := by positivity
        calc 6 * (Real.log (2 + 1 / ε) + 1) * (Cp * (1 + |α|) ^ 2)
            = (Cp * 6) * (1 + |α|) ^ 2 * (Real.log (2 + 1 / ε) + 1) := by ring
          _ ≤ max 1 (Cp * 6) * (1 + |α|) ^ 2 * (Real.log (2 + 1 / ε) + 1) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) h2) hlog

/-- **The `L¹`-bound for the chirped cutoff `chat a b α`**, uniform in `a, b`. -/
theorem chat_fourier_l1 :
    ∃ C : ℝ, 0 < C ∧ ∀ (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (α : ℝ),
      ∫ ξ : ℝ, ‖𝓕 (chat a b α) ξ‖ ≤ C * (1 + |α|) ^ 2 * (Real.log (2 + b / a) + 1) := by
  obtain ⟨Cf, hCfpos, hCf⟩ := fcut_fourier_l1
  refine ⟨Cf, hCfpos, ?_⟩
  intro a b ha hab α
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hε : 0 < a / b := div_pos ha hb
  have hε1 : a / b ≤ 1 := (div_le_one hb).mpr hab
  have hbd : (2 : ℝ) + 1 / (a / b) = 2 + b / a := by
    field_simp [ha.ne', hb.ne']
  calc ∫ ξ : ℝ, ‖𝓕 (chat a b α) ξ‖
      = ∫ ξ : ℝ, ‖𝓕 (fcut (a / b) α) ξ‖ := chat_l1_eq a b α ha hb
    _ ≤ Cf * (1 + |α|) ^ 2 * (Real.log (2 + 1 / (a / b)) + 1) := hCf (a / b) α hε hε1
    _ = Cf * (1 + |α|) ^ 2 * (Real.log (2 + b / a) + 1) := by rw [hbd]

lemma integrable_fourier_chat (a b α : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    Integrable (𝓕 (chat a b α)) := by
  obtain ⟨hcd, hcs, -⟩ := chat_fourier_inversion a b α ha hab
  let S : SchwartzMap ℝ ℂ := hcs.toSchwartzMap hcd
  have h : Integrable (⇑(𝓕 S : SchwartzMap ℝ ℂ)) := (𝓕 S : SchwartzMap ℝ ℂ).integrable (μ := volume)
  rw [SchwartzMap.fourier_coe] at h
  exact h

/-- **The near-cut separation inequality, uniform in `a, b`.** -/
theorem separation_ineq_nearCut :
    ∃ C : ℝ, 0 < C ∧ ∀ (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
      (ι : Type) [Fintype ι] (x y : ι → ℝ) (c : ι → ℂ) (M : ℝ),
      (∀ i, 0 < y i) →
      (∀ u t : ℝ, ‖∑ i, c i * Complex.exp (2 * Real.pi * Complex.I * (u * x i)) *
            (y i : ℂ) ^ (Complex.I * t)‖ ≤ M) →
      ‖∑ i, c i * ((Work.FIArea4.Vflip.bump (|x i| * y i)
            * Work.FIArea4.Vflip.nearCut a b (x i) : ℝ) : ℂ)‖
        ≤ C * (Real.log (2 + b / a) + 1) ^ 2 * M := by
  classical
  obtain ⟨KG, hKGpos, hKGdec⟩ := sepG_decay contDiff_bump bump_supp
  have hGmellin := sepG_mellin contDiff_bump bump_supp
  have hIntG : Integrable (sepG Work.FIArea4.Vflip.bump) :=
    integrable_sepG _ contDiff_bump bump_supp
  obtain ⟨KC, hKCpos, hKCl1⟩ := chat_fourier_l1
  -- ## the majorant
  set Maj : ℝ → ℝ := fun t => (KC * (1 + |2 * Real.pi * t|) ^ 2) * ‖sepG Work.FIArea4.Vflip.bump t‖
    with hMajdef
  have hMajint : Integrable Maj := by
    have hbase : Integrable (fun t : ℝ => (1 + |t|) ^ (-(2 : ℝ))) := by
      have h := integrable_one_add_norm (μ := volume) (E := ℝ) (r := 2)
        (by rw [Module.finrank_self]; norm_num)
      simpa [Real.norm_eq_abs] using h
    have hbdd : ∀ t : ℝ, Maj t ≤ (KG * KC * (1 + 2 * Real.pi) ^ 2) * (1 + |t|) ^ (-(2 : ℝ)) := by
      intro t
      have hpow : (1 + |2 * Real.pi * t|) ^ 2 ≤ (1 + 2 * Real.pi) ^ 2 * (1 + |t|) ^ 2 := by
        have h3 : |2 * Real.pi * t| = 2 * Real.pi * |t| := by
          rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos,
            abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        have h2 : 1 + |2 * Real.pi * t| ≤ (1 + 2 * Real.pi) * (1 + |t|) := by
          rw [h3]; nlinarith [abs_nonneg t, Real.pi_pos]
        calc (1 + |2 * Real.pi * t|) ^ 2 ≤ ((1 + 2 * Real.pi) * (1 + |t|)) ^ 2 :=
              pow_le_pow_left₀ (by positivity) h2 2
          _ = (1 + 2 * Real.pi) ^ 2 * (1 + |t|) ^ 2 := by ring
      have hrpow : (1 + |t|) ^ 2 * (1 + |t|) ^ (-(4 : ℝ)) = (1 + |t|) ^ (-(2 : ℝ)) := by
        rw [← Real.rpow_natCast (1 + |t|) 2,
          ← Real.rpow_add (by positivity : (0 : ℝ) < 1 + |t|)]
        norm_num
      rw [hMajdef]
      calc (KC * (1 + |2 * Real.pi * t|) ^ 2) * ‖sepG Work.FIArea4.Vflip.bump t‖
          ≤ (KC * ((1 + 2 * Real.pi) ^ 2 * (1 + |t|) ^ 2)) *
              (KG * (1 + |t|) ^ (-(4 : ℝ))) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hpow hKCpos.le) (hKGdec t) (norm_nonneg _)
              (by positivity)
        _ = (KG * KC * (1 + 2 * Real.pi) ^ 2) * (1 + |t|) ^ (-(2 : ℝ)) := by
            rw [show (KC * ((1 + 2 * Real.pi) ^ 2 * (1 + |t|) ^ 2)) *
                  (KG * (1 + |t|) ^ (-(4 : ℝ)))
                = (KC * (1 + 2 * Real.pi) ^ 2 * KG) *
                  ((1 + |t|) ^ 2 * (1 + |t|) ^ (-(4 : ℝ))) by ring]
            rw [hrpow]; ring
    refine Integrable.mono' (hbase.const_mul (KG * KC * (1 + 2 * Real.pi) ^ 2)) ?_ ?_
    · rw [hMajdef]
      exact ((by fun_prop : Continuous fun t : ℝ =>
        KC * (1 + |2 * Real.pi * t|) ^ 2)).aestronglyMeasurable.mul
          hIntG.aestronglyMeasurable.norm
    · filter_upwards with t
      rw [Real.norm_of_nonneg (by rw [hMajdef]; positivity)]
      exact hbdd t
  have hMajnn : ∀ t : ℝ, 0 ≤ Maj t := by intro t; rw [hMajdef]; positivity
  refine ⟨(∫ t : ℝ, Maj t) + 1, by positivity, ?_⟩
  intro a b ha hab ι _ x y c M hy hM
  have hMnn : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 0)
  have hIntW : ∀ t : ℝ, Integrable (𝓕 (chat a b (2 * Real.pi * t))) :=
    fun t => integrable_fourier_chat a b (2 * Real.pi * t) ha hab
  -- ## the two explicit local functions
  set Tc : ι → ℝ → ℂ := fun i t => (Work.FIArea4.Vflip.nearCut a b (x i) : ℂ) *
      (((|x i| : ℝ) : ℂ) ^ (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ))) *
      ((y i : ℂ) ^ (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ))) with hTc
  set Sf : ℝ → ℝ → ℂ := fun u t => ∑ i, c i *
      Complex.exp (2 * Real.pi * Complex.I * (u * x i)) *
      (y i : ℂ) ^ (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ)) with hSf
  have hSfbd : ∀ u t : ℝ, ‖Sf u t‖ ≤ M := by
    intro u t
    rw [hSf]
    exact hM u (2 * Real.pi * t)
  -- ## 0. continuity of the local factor `Tc i`
  have hcontTc : ∀ i, Continuous (Tc i) := by
    intro i
    by_cases hi : x i = 0
    · have hnc : Work.FIArea4.Vflip.nearCut a b (x i) = 0 := by rw [hi]; exact nearCut_zero a b ha
      have hfun : Tc i = fun _ : ℝ => 0 := by
        funext t; rw [hTc]; simp only [hnc, Complex.ofReal_zero, zero_mul]
      rw [hfun]; exact continuous_const
    · rw [hTc]
      have hxi : 0 < |x i| := abs_pos.mpr hi
      have h1 : Continuous (fun t : ℝ =>
          ((|x i| : ℝ) : ℂ) ^ (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ))) :=
        continuous_cpow_ofReal |x i| hxi
      have h2 : Continuous (fun t : ℝ =>
          (y i : ℂ) ^ (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ))) :=
        continuous_cpow_ofReal (y i) (hy i)
      exact (continuous_const.mul h1).mul h2
  -- ## 1. the per-index Mellin identity
  have hper : ∀ i, ((Work.FIArea4.Vflip.bump (|x i| * y i)
        * Work.FIArea4.Vflip.nearCut a b (x i) : ℝ) : ℂ) =
      ∫ t : ℝ, sepG Work.FIArea4.Vflip.bump t * Tc i t := by
    intro i
    by_cases hi : x i = 0
    · have hnc : Work.FIArea4.Vflip.nearCut a b (x i) = 0 := by rw [hi]; exact nearCut_zero a b ha
      have hTc0 : Tc i = fun _ : ℝ => 0 := by
        funext t; rw [hTc]; simp only [hnc, Complex.ofReal_zero, zero_mul]
      simp [hnc, hTc0]
    · have hpos : 0 < |x i| * y i := mul_pos (abs_pos.mpr hi) (hy i)
      rw [Complex.ofReal_mul, hGmellin (|x i| * y i) hpos]
      rw [← MeasureTheory.integral_mul_const
        (((Work.FIArea4.Vflip.nearCut a b (x i) : ℝ)) : ℂ)
        (fun t : ℝ => sepG Work.FIArea4.Vflip.bump t *
          Complex.exp (2 * Real.pi * Complex.I * (t * Real.log (|x i| * y i))))]
      apply integral_congr_ae
      filter_upwards with t
      rw [hTc]
      have h1 : Complex.exp (2 * Real.pi * Complex.I * (t * Real.log (|x i| * y i))) =
          ((|x i| * y i : ℝ) : ℂ) ^ (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ)) := by
        rw [cpow_ofReal_eq_exp (|x i| * y i) hpos (2 * Real.pi * t)]
        congr 1; push_cast; ring
      rw [h1, Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg (abs_nonneg (x i)) (hy i).le]
      ring
  -- ## 2. integrability of the summands of the outer integral
  have hIntTc : ∀ i, AEStronglyMeasurable (Tc i) := fun i => (hcontTc i).aestronglyMeasurable
  have hIntSummand : ∀ i, Integrable (fun t : ℝ =>
      c i * (sepG Work.FIArea4.Vflip.bump t * Tc i t)) := by
    intro i
    have hb : Integrable (fun t : ℝ => sepG Work.FIArea4.Vflip.bump t * Tc i t) :=
      Integrable.mul_of_norm_le hIntG 1 (fun t => by
        rw [hTc, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        calc |Work.FIArea4.Vflip.nearCut a b (x i)| *
              ‖((|x i| : ℝ) : ℂ) ^ (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ))‖ *
                ‖(y i : ℂ) ^ (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ))‖
            ≤ 1 * 1 * 1 := by
              refine mul_le_mul (mul_le_mul ?_
                (norm_cpow_imag_nonneg |x i| (abs_nonneg _) _) (norm_nonneg _) (by norm_num))
                (norm_cpow_imag_nonneg (y i) (hy i).le _) (norm_nonneg _) (by norm_num)
              rw [abs_of_nonneg (Work.FIArea4.Vflip.nearCut_nonneg a b (x i))]
              exact Work.FIArea4.Vflip.nearCut_le_one a b (x i)
          _ = 1 := by norm_num) (hIntTc i)
    exact hb.const_mul (c i)
  -- ## 3. the outer identity
  have houter : (∑ i, c i * ((Work.FIArea4.Vflip.bump (|x i| * y i)
        * Work.FIArea4.Vflip.nearCut a b (x i) : ℝ) : ℂ)) =
      ∫ t : ℝ, sepG Work.FIArea4.Vflip.bump t * (∑ i, c i * Tc i t) := by
    have h1 : (∑ i, c i * ((Work.FIArea4.Vflip.bump (|x i| * y i)
          * Work.FIArea4.Vflip.nearCut a b (x i) : ℝ) : ℂ)) =
        ∑ i, c i * ∫ t : ℝ, sepG Work.FIArea4.Vflip.bump t * Tc i t :=
      Finset.sum_congr rfl (fun i _ => by rw [hper i])
    rw [h1]
    have h2 : (∑ i, c i * ∫ t : ℝ, sepG Work.FIArea4.Vflip.bump t * Tc i t) =
        ∑ i, ∫ t : ℝ, c i * (sepG Work.FIArea4.Vflip.bump t * Tc i t) :=
      Finset.sum_congr rfl (fun i _ => by rw [MeasureTheory.integral_const_mul])
    rw [h2, ← MeasureTheory.integral_finsetSum Finset.univ
      (fun i _ => hIntSummand i)]
    apply integral_congr_ae
    filter_upwards with t
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  -- ## 4. the inner (chirp) expansion at fixed `t`
  have hinner : ∀ t : ℝ, (∑ i, c i * Tc i t) =
      ∫ u : ℝ, 𝓕 (chat a b (2 * Real.pi * t)) u * Sf u t := by
    intro t
    have hterm : ∀ i : ι, ∫ u : ℝ, 𝓕 (chat a b (2 * Real.pi * t)) u *
          (c i * Complex.exp (2 * Real.pi * Complex.I * (u * x i)) *
            (y i : ℂ) ^ (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ))) = c i * Tc i t := by
      intro i
      have hA := (chat_fourier_inversion a b (2 * Real.pi * t) ha hab).2.2 (x i)
      have hre : (fun u : ℝ => 𝓕 (chat a b (2 * Real.pi * t)) u *
            (c i * Complex.exp (2 * Real.pi * Complex.I * (u * x i)) *
              (y i : ℂ) ^ (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ)))) =
          fun u : ℝ => (c i * (y i : ℂ) ^ (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ))) *
              (𝓕 (chat a b (2 * Real.pi * t)) u *
                Complex.exp (2 * Real.pi * Complex.I * (u * x i))) := by
        funext u; ring
      rw [hre, MeasureTheory.integral_const_mul, hA, hTc]
      simp only [chat]
      ring
    rw [hSf]
    have h1 : (fun u : ℝ => 𝓕 (chat a b (2 * Real.pi * t)) u *
          ((fun u t => ∑ i, c i * Complex.exp (2 * Real.pi * Complex.I * (u * x i)) *
              (y i : ℂ) ^ (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ))) u t)) =
        fun u : ℝ => ∑ i, 𝓕 (chat a b (2 * Real.pi * t)) u *
            (c i * Complex.exp (2 * Real.pi * Complex.I * (u * x i)) *
              (y i : ℂ) ^ (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ))) := by
      funext u
      simp only
      rw [Finset.mul_sum]
    rw [h1, MeasureTheory.integral_finsetSum]
    · exact Finset.sum_congr rfl (fun i _ => (hterm i).symm)
    · intro i _
      refine Integrable.mul_of_norm_le (hIntW t) ‖c i‖ (fun u => ?_) ?_
      · have hnormexp :
            ‖Complex.exp (2 * Real.pi * Complex.I * ((u : ℂ) * (x i : ℂ)))‖ = 1 := by
          rw [show 2 * ↑Real.pi * Complex.I * ((u : ℂ) * (x i : ℂ))
              = ((2 * Real.pi * (u * x i) : ℝ) : ℂ) * Complex.I by push_cast; ring]
          exact Complex.norm_exp_ofReal_mul_I _
        rw [norm_mul, norm_mul, hnormexp, norm_cpow_imag _ (hy i) _]
        simp
      · exact ((by fun_prop : Continuous fun u : ℝ =>
            c i * Complex.exp (2 * Real.pi * Complex.I * (u * x i)) *
              (y i : ℂ) ^ (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ)))).aestronglyMeasurable
  -- ## 5. the bound
  have hEq : (∑ i, c i * ((Work.FIArea4.Vflip.bump (|x i| * y i)
        * Work.FIArea4.Vflip.nearCut a b (x i) : ℝ) : ℂ)) =
      ∫ t : ℝ, sepG Work.FIArea4.Vflip.bump t *
        (∫ u : ℝ, 𝓕 (chat a b (2 * Real.pi * t)) u * Sf u t) := by
    rw [houter]
    apply integral_congr_ae
    filter_upwards with t
    rw [hinner t]
  have hL1 : (1 : ℝ) ≤ Real.log (2 + b / a) + 1 := by
    have hb : 0 < b := lt_of_lt_of_le ha hab
    have : (0 : ℝ) ≤ Real.log (2 + b / a) :=
      Real.log_nonneg (by have hd : 0 ≤ b / a := (div_pos hb ha).le; linarith)
    linarith
  have hbound : ‖∫ t : ℝ, sepG Work.FIArea4.Vflip.bump t *
        (∫ u : ℝ, 𝓕 (chat a b (2 * Real.pi * t)) u * Sf u t)‖
      ≤ M * (Real.log (2 + b / a) + 1) * ∫ t : ℝ, Maj t := by
    calc ‖∫ t : ℝ, sepG Work.FIArea4.Vflip.bump t *
          (∫ u : ℝ, 𝓕 (chat a b (2 * Real.pi * t)) u * Sf u t)‖
        ≤ ∫ t : ℝ, ‖sepG Work.FIArea4.Vflip.bump t *
            (∫ u : ℝ, 𝓕 (chat a b (2 * Real.pi * t)) u * Sf u t)‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ t : ℝ, M * (Real.log (2 + b / a) + 1) * Maj t := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => norm_nonneg _)
            (hMajint.const_mul (M * (Real.log (2 + b / a) + 1)))
            (Filter.Eventually.of_forall fun t => ?_)
          dsimp only
          rw [norm_mul]
          have hZ : ‖∫ u : ℝ, 𝓕 (chat a b (2 * Real.pi * t)) u * Sf u t‖ ≤
              M * ∫ u : ℝ, ‖𝓕 (chat a b (2 * Real.pi * t)) u‖ := by
            calc ‖∫ u : ℝ, 𝓕 (chat a b (2 * Real.pi * t)) u * Sf u t‖
                ≤ ∫ u : ℝ, ‖𝓕 (chat a b (2 * Real.pi * t)) u * Sf u t‖ :=
                  norm_integral_le_integral_norm _
              _ ≤ ∫ u : ℝ, ‖𝓕 (chat a b (2 * Real.pi * t)) u‖ * M := by
                  refine integral_mono_of_nonneg
                    (Filter.Eventually.of_forall fun u => norm_nonneg _)
                    ((hIntW t).norm.mul_const M) (Filter.Eventually.of_forall fun u => ?_)
                  dsimp only
                  rw [norm_mul]
                  exact mul_le_mul_of_nonneg_left (hSfbd u t) (norm_nonneg _)
              _ = M * ∫ u : ℝ, ‖𝓕 (chat a b (2 * Real.pi * t)) u‖ := by
                  rw [MeasureTheory.integral_mul_const, mul_comm]
          have hKC := hKCl1 a b ha hab (2 * Real.pi * t)
          rw [hMajdef]
          calc ‖sepG Work.FIArea4.Vflip.bump t‖ *
                ‖∫ u : ℝ, 𝓕 (chat a b (2 * Real.pi * t)) u * Sf u t‖
              ≤ ‖sepG Work.FIArea4.Vflip.bump t‖ *
                (M * ∫ u : ℝ, ‖𝓕 (chat a b (2 * Real.pi * t)) u‖) :=
                mul_le_mul_of_nonneg_left hZ (norm_nonneg _)
            _ ≤ ‖sepG Work.FIArea4.Vflip.bump t‖ *
                (M * (KC * (1 + |2 * Real.pi * t|) ^ 2 * (Real.log (2 + b / a) + 1))) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left hKC hMnn) (norm_nonneg _)
            _ = M * (Real.log (2 + b / a) + 1) *
                  ((KC * (1 + |2 * Real.pi * t|) ^ 2) * ‖sepG Work.FIArea4.Vflip.bump t‖) := by
                ring
      _ = M * (Real.log (2 + b / a) + 1) * ∫ t : ℝ, Maj t := by
          rw [MeasureTheory.integral_const_mul]
  -- ## 6. conclusion
  rw [hEq]
  have hlog : (1 : ℝ) ≤ (Real.log (2 + b / a) + 1) ^ 2 := one_le_pow₀ hL1
  have hDnn : (0 : ℝ) ≤ ∫ t : ℝ, Maj t := integral_nonneg hMajnn
  have hstep1 : M * (Real.log (2 + b / a) + 1) * ∫ t : ℝ, Maj t
      ≤ M * (Real.log (2 + b / a) + 1) ^ 2 * ∫ t : ℝ, Maj t :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by nlinarith [hL1]) hMnn) hDnn
  have hstep2 : M * (Real.log (2 + b / a) + 1) ^ 2 * ∫ t : ℝ, Maj t
      ≤ ((∫ t : ℝ, Maj t) + 1) * (Real.log (2 + b / a) + 1) ^ 2 * M := by
    nlinarith [hDnn, hMnn, sq_nonneg (Real.log (2 + b / a) + 1),
      mul_nonneg hMnn (sq_nonneg (Real.log (2 + b / a) + 1))]
  calc ‖∫ t : ℝ, sepG Work.FIArea4.Vflip.bump t *
        (∫ u : ℝ, 𝓕 (chat a b (2 * Real.pi * t)) u * Sf u t)‖
      ≤ M * (Real.log (2 + b / a) + 1) * ∫ t : ℝ, Maj t := hbound
    _ ≤ M * (Real.log (2 + b / a) + 1) ^ 2 * ∫ t : ℝ, Maj t := hstep1
    _ ≤ ((∫ t : ℝ, Maj t) + 1) * (Real.log (2 + b / a) + 1) ^ 2 * M := hstep2

end

end Work.FIArea4.Vflip.Vfd
