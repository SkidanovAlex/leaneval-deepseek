import Mathlib
import Submission.Commons.Analysis.Complex.logDeriv_sub_divisor_le
import Submission.Commons.Analysis.Complex.logDeriv_zeroFree_ball_bound_analytic
import Submission.Commons.Analysis.Complex.circleLogDerivContour_bound
import Submission.Commons.NumberTheory.Zeta.zeta_zeroFreeRegion_logDeriv_bound
import Submission.Commons.NumberTheory.Zeta.zeta_zeroFree_near_axis
import Submission.Commons.NumberTheory.Zeta.zeta_lower_bound_right_of_one
import Submission.Commons.NumberTheory.Zeta.zeta_lower_re_two
import Submission.Commons.NumberTheory.Zeta.zeta_logDeriv_re_axis_bound
import Submission.Commons.NumberTheory.Zeta.zeta_strip_polyGrowth
import Submission.Commons.NumberTheory.Zeta.zeta1_exists_good_radius
import Submission.Commons.NumberTheory.Zeta.zeta_strip_polyGrowth_neg
import Submission.Commons.NumberTheory.Zeta.zeta_norm_le_const_of_three_le_re
import Submission.Commons.NumberTheory.LSeries.norm_riemannZeta_lower_of_three_four_one
import Submission.Port.LogDerivCompat

open Complex Metric Filter Set
open scoped Real Topology BigOperators

namespace Commons.NumberTheory.Zeta

noncomputable section

set_option maxHeartbeats 4000000

/-! ## Auxiliary: the Euler-product bound for `ζ'/ζ` on `Re s > 1` -/

private lemma summable_vonMangoldt_mul_rpow_neg (σ : ℝ) (hσ : 1 < σ) :
    Summable (fun n : ℕ => ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ)) := by
  have h := (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (σ : ℂ))
    (by simpa using hσ)).norm
  refine h.congr (fun n => ?_)
  rw [LSeries.norm_term_eq]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [if_neg hn, Complex.ofReal_re,
      Complex.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      Real.rpow_neg (Nat.cast_nonneg n) σ, div_eq_mul_inv]

private lemma norm_LSeries_term_vonMangoldt (s : ℂ) (n : ℕ) :
    ‖LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) s n‖ =
      ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-s.re) := by
  rw [LSeries.norm_term_eq]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [if_neg hn, Complex.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      Real.rpow_neg (Nat.cast_nonneg n) s.re, div_eq_mul_inv]

private lemma vonMangoldt_tsum_eq_zeta_re (σ : ℝ) (hσ : 1 < σ) :
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ)) =
      (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re := by
  have hsumm : LSeriesSummable
      (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hσ)
  have hζid := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
    (s := (σ : ℂ)) (by simpa using hσ)
  rw [← hζid, LSeries, Complex.re_tsum hsumm]
  refine tsum_congr (fun n => ?_)
  rw [LSeries.term_def]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [if_neg hn, ← Complex.ofReal_natCast,
      ← Complex.ofReal_cpow (Nat.cast_nonneg n) σ, ← Complex.ofReal_div,
      Complex.ofReal_re, Real.rpow_neg (Nat.cast_nonneg n) σ, div_eq_mul_inv]

/-- **Euler-product bound for the logarithmic derivative of `ζ`.**  For `1 < Re s ≤ 3`,
`‖ζ'(s)/ζ(s)‖ ≤ 1/(Re s - 1) + C`. -/
private lemma logDeriv_zeta_norm_le_one_lt_re :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 1 < s.re → s.re ≤ 3 →
      ‖deriv riemannZeta s / riemannZeta s‖ ≤ 1 / (s.re - 1) + C := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := zeta_logDeriv_re_axis_bound
  refine ⟨C₀ + 1, by linarith, ?_⟩
  intro s hs hs3
  have hsumm := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have hid := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  have h1 : deriv riemannZeta s / riemannZeta s
      = -(LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) s) := by
    rw [hid]; ring
  have hnorm : ‖deriv riemannZeta s / riemannZeta s‖
      ≤ ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-s.re) := by
    rw [h1]
    calc ‖-(LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) s)‖
        = ‖LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) s‖ := norm_neg _
      _ ≤ ∑' n : ℕ, ‖LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) s n‖ :=
          norm_tsum_le_tsum_norm hsumm.norm
      _ = ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-s.re) :=
          tsum_congr (fun n => norm_LSeries_term_vonMangoldt s n)
  have hI : (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-s.re))
      ≤ 1 / (s.re - 1) + (C₀ + 1) := by
    by_cases hs2 : s.re ≤ 2
    · rw [vonMangoldt_tsum_eq_zeta_re s.re hs]
      have h := hC₀ s.re hs hs2
      linarith
    · have hs2' : 2 ≤ s.re := le_of_not_ge hs2
      have hmono : (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-s.re))
          ≤ (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(2:ℝ))) := by
        refine Summable.tsum_le_tsum (fun n => ?_)
          (summable_vonMangoldt_mul_rpow_neg s.re hs) (summable_vonMangoldt_mul_rpow_neg 2 (by norm_num))
        rcases eq_or_ne n 0 with rfl | hn
        · simp
        · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
          refine mul_le_mul_of_nonneg_left ?_ (ArithmeticFunction.vonMangoldt_nonneg)
          exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
      have h2 : (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(2:ℝ)))
          ≤ 1 + C₀ := by
        rw [vonMangoldt_tsum_eq_zeta_re 2 (by norm_num)]
        have h := hC₀ 2 (by norm_num) (by norm_num)
        norm_num at h
        exact h
      have hge : (0:ℝ) ≤ 1 / (s.re - 1) := by positivity
      linarith
  linarith



/-! ## Growth bounds -/

private lemma zeta_growth_strip :
    ∃ Kg : ℝ, 0 < Kg ∧ ∀ w : ℂ, -2 ≤ w.re → w.re ≤ 6 → 1 ≤ |w.im| →
      ‖riemannZeta w‖ ≤ Kg * (|w.im| + 3) ^ 12 := by
  obtain ⟨C3, hC3pos, hC3⟩ := zeta_norm_le_const_of_three_le_re
  obtain ⟨C4, hC4pos, hC4⟩ := zeta_strip_polyGrowth
  obtain ⟨C12, hC12pos, hC12⟩ := zeta_strip_polyGrowth_neg
  refine ⟨max C3 (max C4 C12), lt_max_of_lt_left hC3pos, ?_⟩
  intro w hr2 hr6 him
  have hwre : ((w.re : ℂ) + Complex.I * (w.im : ℂ)) = w := by
    rw [mul_comm Complex.I (w.im : ℂ)]; exact Complex.re_add_im w
  have hC3le : C3 ≤ max C3 (max C4 C12) := le_max_left _ _
  have hC4le : C4 ≤ max C3 (max C4 C12) := le_trans (le_max_left _ _) (le_max_right _ _)
  have hC12le : C12 ≤ max C3 (max C4 C12) := le_trans (le_max_right _ _) (le_max_right _ _)
  by_cases h3 : w.re ≤ 3
  · by_cases h1 : w.re ≤ -1
    · calc ‖riemannZeta w‖ = ‖riemannZeta ((w.re : ℂ) + Complex.I * (w.im : ℂ))‖ := by
            rw [hwre]
        _ ≤ C12 * (|w.im| + 3) ^ 12 := hC12 w.re w.im hr2 h1 him
        _ ≤ max C3 (max C4 C12) * (|w.im| + 3) ^ 12 :=
            mul_le_mul_of_nonneg_right hC12le (by positivity)
    · have h1' : -1 ≤ w.re := le_of_lt (not_le.mp h1)
      calc ‖riemannZeta w‖ = ‖riemannZeta ((w.re : ℂ) + Complex.I * (w.im : ℂ))‖ := by
            rw [hwre]
        _ ≤ C4 * (|w.im| + 3) ^ 4 := hC4 w.re w.im h1' h3 him
        _ ≤ max C3 (max C4 C12) * (|w.im| + 3) ^ 12 := by
            have hb : (1 : ℝ) ≤ |w.im| + 3 := by linarith [abs_nonneg w.im]
            have hpow : (|w.im| + 3) ^ 4 ≤ (|w.im| + 3) ^ 12 :=
              pow_le_pow_right₀ hb (by norm_num)
            calc C4 * (|w.im| + 3) ^ 4 ≤ max C3 (max C4 C12) * (|w.im| + 3) ^ 4 :=
                  mul_le_mul_of_nonneg_right hC4le (by positivity)
              _ ≤ max C3 (max C4 C12) * (|w.im| + 3) ^ 12 :=
                  mul_le_mul_of_nonneg_left hpow (by positivity)
  · have h3' : 3 ≤ w.re := le_of_lt (not_le.mp h3)
    calc ‖riemannZeta w‖ ≤ C3 := hC3 w h3' 
      _ ≤ max C3 (max C4 C12) * (|w.im| + 3) ^ 12 := by
          have hb : (1 : ℝ) ≤ |w.im| + 3 := by linarith [abs_nonneg w.im]
          have h1 : (1 : ℝ) ≤ (|w.im| + 3) ^ 12 := one_le_pow₀ hb
          have h2 : (0:ℝ) < max C3 (max C4 C12) := lt_max_of_lt_left hC3pos
          nlinarith [hC3le, h1, h2]


private lemma zeta1_growth_circle {Kg cd : ℝ} (hKg : 0 < Kg) (hcdpos : 0 < cd)
    (hg : ∀ w : ℂ, -2 ≤ w.re → w.re ≤ 6 → 1 ≤ |w.im| →
      ‖riemannZeta w‖ ≤ Kg * (|w.im| + 3) ^ 12)
    (hcd : ∀ T : ℝ, cd ≤ ‖riemannZeta ((2 : ℂ) + (T : ℂ) * Complex.I)‖) :
    (∀ t R : ℝ, 5 ≤ |t| → 7 / 2 ≤ R → R ≤ 4 → ∀ w : ℂ,
        ‖w - ((2 : ℂ) + (t : ℂ) * Complex.I)‖ = R →
        ‖riemannZeta₁ w‖ ≤ Kg * (|t| + 7) ^ 13) ∧
    (∀ t : ℝ, 5 ≤ |t| →
        cd ≤ ‖riemannZeta₁ ((2 : ℂ) + (t : ℂ) * Complex.I)‖) := by
  constructor
  · intro t R ht hRlo hRhi w hw
    set cA : ℂ := (2 : ℂ) + (t : ℂ) * Complex.I with hcAdef
    have hcAim : cA.im = t := by simp [cA]
    have hcA1 : cA ≠ 1 := by
      intro h
      have him : cA.im = 0 := by rw [h]; simp
      rw [hcAim] at him
      rw [him] at ht
      norm_num at ht
    have hcAnorm : ‖cA‖ ≤ |t| + 2 := by
      calc ‖cA‖ = ‖(2 : ℂ) + (t : ℂ) * Complex.I‖ := rfl
        _ ≤ ‖(2 : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ := norm_add_le _ _
        _ = 2 + |t| := by
            rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
            norm_num
        _ = |t| + 2 := by ring
    have hw1 : w ≠ 1 := by
      intro h
      have hR : ‖(1 : ℂ) - cA‖ = R := by rw [← h]; exact hw
      have hsq : ‖(1 : ℂ) - cA‖ ^ 2 = 1 + t ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        simp [cA]
        ring
      have ht2 : (25 : ℝ) ≤ t ^ 2 := by
        have := sq_abs t
        nlinarith [this, abs_nonneg t, ht]
      have h4 : (4 : ℝ) < ‖(1 : ℂ) - cA‖ := by
        nlinarith [hsq, ht2, norm_nonneg ((1 : ℂ) - cA)]
      linarith [hR, hRhi, h4]
    have hre_im : -2 ≤ w.re ∧ w.re ≤ 6 ∧ 1 ≤ |w.im| ∧ |w.im| ≤ |t| + 4 := by
      have h1 : |w.re - 2| ≤ R := by
        have h := Complex.abs_re_le_norm (w - cA)
        rw [show (w - cA).re = w.re - 2 by simp [cA]] at h
        rw [hw] at h
        exact h
      have h2 : |w.im - t| ≤ R := by
        have h := Complex.abs_im_le_norm (w - cA)
        rw [show (w - cA).im = w.im - t by simp [cA]] at h
        rw [hw] at h
        exact h
      have h2c : |w.im - t| ≤ 4 := le_trans h2 hRhi
      have h1c : |w.re - 2| ≤ 4 := le_trans h1 hRhi
      have h1b : -4 ≤ w.re - 2 ∧ w.re - 2 ≤ 4 := abs_le.mp h1c
      have h2b : -4 ≤ w.im - t ∧ w.im - t ≤ 4 := abs_le.mp h2c
      have h3 : |t| - |w.im| ≤ |w.im - t| := by
        simpa [abs_sub_comm] using abs_sub_abs_le_abs_sub t w.im
      refine ⟨by linarith [h1b.1], by linarith [h1b.2], ?_, ?_⟩
      · linarith [h3, h2c, ht]
      · rw [abs_le]
        exact ⟨by linarith [h2b.1, neg_abs_le t], by linarith [h2b.2, le_abs_self t]⟩
    have hwnorm : ‖w‖ ≤ |t| + 6 := by
      have h1 : ‖w‖ ≤ ‖w - cA‖ + ‖cA‖ := by
        calc ‖w‖ = ‖(w - cA) + cA‖ := by ring_nf
          _ ≤ ‖w - cA‖ + ‖cA‖ := norm_add_le _ _
      linarith [h1, hcAnorm, hRhi]
    have hζw : ‖riemannZeta w‖ ≤ Kg * (|t| + 7) ^ 12 := by
      have h := hg w hre_im.1 hre_im.2.1 hre_im.2.2.1
      have hle : |w.im| + 3 ≤ |t| + 7 := by linarith [hre_im.2.2.2]
      have hb : 0 ≤ |w.im| + 3 := by linarith [abs_nonneg w.im]
      have hpow : (|w.im| + 3) ^ 12 ≤ (|t| + 7) ^ 12 := pow_le_pow_left₀ hb hle 12
      calc ‖riemannZeta w‖ ≤ Kg * (|w.im| + 3) ^ 12 := h
        _ ≤ Kg * (|t| + 7) ^ 12 := mul_le_mul_of_nonneg_left hpow (le_of_lt hKg)
    have hprod : ‖riemannZeta₁ w‖ = ‖w - 1‖ * ‖riemannZeta w‖ := by
      have hraw : riemannZeta₁ w = (w - 1) * riemannZeta w := by
        rw [riemannZeta_eq_inv_sub_mul hw1]
        field_simp
      rw [hraw, norm_mul]
    rw [hprod]
    have hw1le : ‖w - 1‖ ≤ |t| + 7 := by
      have h1 : ‖w - 1‖ ≤ ‖w‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      rw [norm_one] at h1
      linarith [h1, hwnorm]
    calc ‖w - 1‖ * ‖riemannZeta w‖ ≤ (|t| + 7) * (Kg * (|t| + 7) ^ 12) :=
          mul_le_mul hw1le hζw (norm_nonneg _) (by linarith [abs_nonneg t])
      _ = Kg * (|t| + 7) ^ 13 := by ring
  · intro t ht
    set cA : ℂ := (2 : ℂ) + (t : ℂ) * Complex.I with hcAdef
    have hcAim : cA.im = t := by simp [cA]
    have hcA1 : cA ≠ 1 := by
      intro h
      have him : cA.im = 0 := by rw [h]; simp
      rw [hcAim] at him
      rw [him] at ht
      norm_num at ht
    have h1 : (1 : ℝ) ≤ ‖cA - 1‖ := by
      have him : |t| ≤ ‖cA - 1‖ := by
        have := Complex.abs_im_le_norm (cA - 1)
        rwa [show (cA - 1).im = t by simp [cA]] at this
      linarith [ht]
    have h2 : cd ≤ ‖riemannZeta cA‖ := by
      have h := hcd t
      rw [hcAdef]; exact h
    have hmul : ‖riemannZeta₁ cA‖ = ‖cA - 1‖ * ‖riemannZeta cA‖ := by
      have hraw : riemannZeta₁ cA = (cA - 1) * riemannZeta cA := by
        rw [riemannZeta_eq_inv_sub_mul hcA1]
        field_simp
      rw [hraw, norm_mul]
    rw [hmul]
    nlinarith [h1, h2, norm_nonneg (cA - 1), norm_nonneg (riemannZeta cA)]

private lemma logDeriv_zeta1_eq (s : ℂ) (hs1 : s ≠ 1) (hζ : riemannZeta s ≠ 0) :
    logDeriv riemannZeta₁ s = deriv riemannZeta s / riemannZeta s + (s - 1)⁻¹ := by
  have hev : riemannZeta₁ =ᶠ[𝓝 s] (fun z => (z - 1) * riemannZeta z) := by
    filter_upwards [compl_singleton_mem_nhds hs1] with z hz
    have hz1 : z ≠ 1 := by simpa using hz
    have h := riemannZeta_eq_inv_sub_mul hz1
    rw [h]
    field_simp
  have hval : logDeriv riemannZeta₁ s = logDeriv (fun z : ℂ => (z - 1) * riemannZeta z) s :=
    (logDeriv_congr_nhds hev).self_of_nhds
  rw [hval]
  have hmul := Submission.Port.logDeriv_mul_fun (x := s) (f := fun z : ℂ => z - 1) (g := riemannZeta)
      (sub_ne_zero.mpr hs1) hζ (by fun_prop) (differentiableAt_riemannZeta hs1)
  rw [hmul]
  have hid : logDeriv (fun z : ℂ => z - 1) s = (s - 1)⁻¹ := by
    rw [logDeriv_apply]; simp
  rw [hid, logDeriv_apply]
  ring

private lemma zeta_logDeriv_le_narrow
    {c₀ C₀ : ℝ} (hc₀ : 0 < c₀) (hC₀ : 0 < C₀)
    (hzf : ∀ u : ℂ, riemannZeta u = 0 → 1 ≤ |u.im| →
      c₀ / Real.log (|u.im| + 3) ≤ 1 - u.re)
    (heuler : ∀ s : ℂ, 1 < s.re → s.re ≤ 3 →
      ‖deriv riemannZeta s / riemannZeta s‖ ≤ 1 / (s.re - 1) + C₀)
    {c : ℝ} (hc : 0 < c) (hcle : c < c₀ / 2) (hc1 : c ≤ 1 / 24) :
    ∃ K₁ : ℝ, 0 < K₁ ∧ ∀ t σ : ℝ, 5 ≤ |t| →
      1 - c / Real.log (|t| + 2) ≤ σ → σ ≤ 1 + 1 / Real.log (|t| + 2) →
      ‖deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) /
          riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ K₁ * Real.log (|t| + 2) := by
  obtain ⟨Kg, hKgpos, hg⟩ := zeta_growth_strip
  obtain ⟨cd, hcdpos, hcd0⟩ := zeta_lower_re_two
  have hcd : ∀ T : ℝ, cd ≤ ‖riemannZeta ((2 : ℂ) + (T : ℂ) * Complex.I)‖ :=
    fun T => by simpa [mul_comm] using hcd0 T
  obtain ⟨hgc, hcdc⟩ := zeta1_growth_circle hKgpos hcdpos hg hcd
  set KgA : ℝ := Kg / cd + 1 with hKgAdef
  have hKgA1 : 1 ≤ KgA := by rw [hKgAdef]; have := div_pos hKgpos hcdpos; linarith
  set δ₀ : ℝ := 1 + c₀ / 2 with hδ₀def
  have hδ₀pos : 0 < δ₀ := by rw [hδ₀def]; linarith
  set δ₁ : ℝ := c₀ / 2 - c with hδ₁def
  have hδ₁pos : 0 < δ₁ := by rw [hδ₁def]; linarith
  set KB : ℝ := 2000 * (|Real.log KgA| + 100) with hKBdef
  have hKBpos : 0 < KB := by rw [hKBdef]; positivity
  set Θ : ℝ := 1 + (1 + c) * (1 + (1 + c) / δ₁) / δ₀ with hΘdef
  have hΘpos : 0 < Θ := by rw [hΘdef]; positivity
  refine ⟨(KB + Θ * (KB + 2) + 1) + (Θ * C₀) + 1, by positivity, ?_⟩
  intro t σ ht hσlo hσhi
  set L : ℝ := Real.log (|t| + 2) with hLdef
  have hLpos : 0 < L := Real.log_pos (by linarith [abs_nonneg t])
  have hL1 : 1 ≤ L := by
    rw [hLdef]
    have h1 : (1 : ℝ) < Real.log 3 := by linarith [Real.log_three_gt_d9]
    have h2 : Real.log 3 ≤ Real.log (|t| + 2) :=
      Real.log_le_log (by norm_num) (by linarith [abs_nonneg t, ht])
    linarith
  have hlogt7 : Real.log (|t| + 7) ≤ 2 * L := by
    rw [hLdef]
    have hle : |t| + 7 ≤ (|t| + 2) ^ 2 := by nlinarith [ht, abs_nonneg t, sq_nonneg |t|]
    calc Real.log (|t| + 7) ≤ Real.log ((|t| + 2) ^ 2) :=
          Real.log_le_log (by positivity) hle
      _ = 2 * Real.log (|t| + 2) := by rw [Real.log_pow]; push_cast; ring
  obtain ⟨R, hRlo, hRhi, hcircR0, hcircR20⟩ := zeta1_exists_good_radius t ht
  set cA : ℂ := (2 : ℂ) + (t : ℂ) * Complex.I with hcAdef
  have hcircR : ∀ w : ℂ, ‖w - cA‖ = R → riemannZeta₁ w ≠ 0 := by
    intro w hw
    refine hcircR0 w ?_
    rw [← hw]
    congr 1
    rw [hcAdef, mul_comm]
  have hcircR2 : ∀ w : ℂ, ‖w - cA‖ = R / 2 → riemannZeta₁ w ≠ 0 := by
    intro w hw
    refine hcircR20 w ?_
    rw [← hw]
    congr 1
    rw [hcAdef, mul_comm]
  set A : ℝ := KgA * (|t| + 7) ^ 13 with hAdef
  have hA1 : 1 ≤ A := by
    rw [hAdef]
    have h1 : (1 : ℝ) ≤ (|t| + 7) ^ 13 := one_le_pow₀ (by linarith [abs_nonneg t])
    nlinarith [hKgA1, h1]
  have hcdcA : cd ≤ ‖riemannZeta₁ cA‖ := by
    have h := hcdc t ht
    rw [hcAdef]; exact h
  have hcA0 : riemannZeta₁ cA ≠ 0 := by
    rw [← norm_pos_iff]
    exact lt_of_lt_of_le hcdpos hcdcA
  have hgrowth : ∀ w : ℂ, ‖w - cA‖ = R → ‖riemannZeta₁ w‖ ≤ A * ‖riemannZeta₁ cA‖ := by
    intro w hw
    have h1 : ‖riemannZeta₁ w‖ ≤ Kg * (|t| + 7) ^ 13 := hgc t R ht hRlo hRhi w hw
    have h2 : Kg * (|t| + 7) ^ 13 ≤ A * ‖riemannZeta₁ cA‖ := by
      have hP : (0 : ℝ) ≤ (|t| + 7) ^ 13 := by positivity
      rw [hAdef, hKgAdef]
      have h3 : (Kg / cd + 1) * cd = Kg + cd := by field_simp
      have h5 : (Kg / cd + 1) * (|t| + 7) ^ 13 * cd = (Kg + cd) * (|t| + 7) ^ 13 := by
        have hcdne : cd ≠ 0 := ne_of_gt hcdpos
        field_simp
      have h4 : (Kg / cd + 1) * (|t| + 7) ^ 13 * cd
          ≤ (Kg / cd + 1) * (|t| + 7) ^ 13 * ‖riemannZeta₁ cA‖ :=
        mul_le_mul_of_nonneg_left hcdcA (mul_nonneg (by positivity) hP)
      have h6 : Kg * (|t| + 7) ^ 13 ≤ (Kg + cd) * (|t| + 7) ^ 13 := by
        have := mul_nonneg (le_of_lt hcdpos) hP
        nlinarith
      linarith [h4, h5.ge, h6]
    linarith [h1, h2]
  set α : ℝ := 3 / 10 with hαdef
  have hα0 : 0 ≤ α := by rw [hαdef]; norm_num
  have hα : α < 1 / 2 := by rw [hαdef]; norm_num
  have hαR : 1 + c / L ≤ α * R := by
    have hαRge : (21 / 20 : ℝ) ≤ α * R := by rw [hαdef]; nlinarith [hRlo]
    have hcL : c / L ≤ 1 / 20 := by
      rw [div_le_iff₀ hLpos]
      have hL7 : Real.log 7 ≤ L := by
        rw [hLdef]
        exact Real.log_le_log (by norm_num) (by linarith [abs_nonneg t, ht])
      have h37 : Real.log 3 ≤ Real.log 7 := Real.log_le_log (by norm_num) (by norm_num)
      have hbig : (5 / 6 : ℝ) ≤ L := by linarith [hL7, h37, Real.log_three_gt_d9]
      nlinarith [hc1]
    linarith [hαRge, hcL]
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hsdef
  set s₁ : ℂ := ((1 + 1 / L : ℝ) : ℂ) + (t : ℂ) * Complex.I with hs₁def
  have hsre : s.re = σ := by simp [s]
  have hsim : s.im = t := by simp [s]
  have hs₁re : s₁.re = 1 + 1 / L := by simp [s₁]
  have hs₁im : s₁.im = t := by simp [s₁]
  have hσ1 : 1 < 1 + 1 / L := by rw [lt_add_iff_pos_right]; positivity
  have hσ13 : (1 + 1 / L : ℝ) ≤ 3 := by
    have h1 : 1 / L ≤ 1 := by rw [div_le_one hLpos]; linarith
    linarith
  have hlog3 : Real.log (|t| + 3) ≤ 2 * L := by
    rw [hLdef]
    have hle : |t| + 3 ≤ (|t| + 2) ^ 2 := by
      have h := sq_nonneg (|t| - 1 / 2); nlinarith [abs_nonneg t]
    have h1 := Real.log_le_log (by positivity) hle
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith
  have hcLe : c / L ≤ c₀ / (2 * L) := by
    rw [div_le_div_iff₀ hLpos (by positivity)]
    nlinarith [hcle]
  have hcLe' : c₀ / (2 * L) ≤ c₀ / Real.log (|t| + 3) := by
    rw [div_le_div_iff₀ (by positivity) (Real.log_pos (by linarith [abs_nonneg t]))]
    nlinarith [hc₀, hlog3]
  have hs_nz : s ≠ 1 := by
    intro h
    have him : s.im = 0 := by rw [h]; simp
    rw [hsim] at him
    rw [him] at ht
    norm_num at ht
  have hs₁_nz : s₁ ≠ 1 := by
    intro h
    have him : s₁.im = 0 := by rw [h]; simp
    rw [hs₁im] at him
    rw [him] at ht
    norm_num at ht
  have hzc0 : riemannZeta s ≠ 0 := by
    intro h
    have h := hzf s h (by rw [hsim]; linarith [ht])
    rw [hsim] at h
    have hcLt : c / L < c₀ / (2 * L) := by
      rw [div_lt_div_iff₀ hLpos (by positivity)]; nlinarith [hcle]
    have h1 : 1 - σ ≤ c / L := by linarith [hσlo]
    have : c₀ / Real.log (|t| + 3) < c₀ / Real.log (|t| + 3) := by linarith [h, h1, hcLt, hcLe']
    exact lt_irrefl _ this
  have hzc1 : riemannZeta s₁ ≠ 0 := by
    intro h
    have h := hzf s₁ h (by rw [hs₁im]; linarith [ht])
    rw [hs₁im, hs₁re] at h
    have hpos : 0 < c₀ / Real.log (|t| + 3) :=
      div_pos hc₀ (Real.log_pos (by linarith [abs_nonneg t]))
    have : 1 - (1 + 1 / L) < 0 := by
      have h1L : 0 < 1 / L := by positivity
      linarith
    linarith [h, hpos, this]
  have hζ1s : riemannZeta₁ s ≠ 0 := by
    intro h
    exact hzc0 (by rw [riemannZeta_eq_inv_sub_mul hs_nz, h, mul_zero])
  have hζ1s1 : riemannZeta₁ s₁ ≠ 0 := by
    intro h
    exact hzc1 (by rw [riemannZeta_eq_inv_sub_mul hs₁_nz, h, mul_zero])
  have hs_ball : ‖s - cA‖ ≤ α * R := by
    have h : s - cA = ((σ - 2 : ℝ) : ℂ) := by
      rw [hsdef, hcAdef]; push_cast; ring
    have h1L : 1 / L ≤ 1 := by rw [div_le_one hLpos]; linarith [hL1]
    have hσ2 : σ - 2 ≤ 0 := by linarith [hσhi, h1L]
    rw [h, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos hσ2]
    have h2 : 2 - σ ≤ 1 + c / L := by linarith [hσlo]
    have h3 : -(σ - 2) = 2 - σ := by ring
    rw [h3]
    exact le_trans h2 hαR
  have hs₁_ball : ‖s₁ - cA‖ ≤ α * R := by
    have h : s₁ - cA = ((1 / L - 1 : ℝ) : ℂ) := by
      rw [hs₁def, hcAdef]; push_cast; ring
    have h1L : 1 / L ≤ 1 := by rw [div_le_one hLpos]; linarith [hL1]
    rw [h, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith [h1L])]
    linarith [hαR]
  set d : ℂ → ℤ := fun u => MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall cA (R / 2)) u
    with hddef
  have hdsupp : (Function.support d).Finite := by
    rw [hddef]
    exact MeromorphicOn.divisor_support_finite_of_subset
      (show MeromorphicOn riemannZeta₁ (Metric.closedBall cA (R / 2)) from
        (show AnalyticOnNhd ℂ riemannZeta₁ (Metric.closedBall cA (R / 2)) from
          fun z _ => differentiable_riemannZeta₁.analyticAt z).meromorphicOn)
      (isCompact_closedBall cA (R / 2)) (by intro z hz; exact hz)
  let S : Finset ℂ := hdsupp.toFinset
  have hSmem : ∀ u : ℂ, u ∈ S ↔ d u ≠ 0 := by
    intro u; simp only [S, Set.Finite.mem_toFinset, Function.mem_support]
  have hdnn : ∀ u : ℂ, (0 : ℝ) ≤ (d u : ℝ) := by
    intro u
    rw [hddef]
    exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg
      ((fun z _ => differentiable_riemannZeta₁.analyticAt z) :
        AnalyticOnNhd ℂ riemannZeta₁ (Metric.closedBall cA (R / 2))) u
  have hfin_s : (∑ᶠ u : ℂ, ((d u : ℤ) : ℂ) * (1 / (s - u)))
      = ∑ u ∈ S, ((d u : ℤ) : ℂ) * (1 / (s - u)) := by
    refine finsum_eq_sum_of_support_subset _ ?_
    intro u hu
    rw [Function.mem_support] at hu
    exact (hSmem u).mpr (by intro hd0; exact hu (by simp [hd0]))
  have hfin_s1 : (∑ᶠ u : ℂ, ((d u : ℤ) : ℂ) * (1 / (s₁ - u)))
      = ∑ u ∈ S, ((d u : ℤ) : ℂ) * (1 / (s₁ - u)) := by
    refine finsum_eq_sum_of_support_subset _ ?_
    intro u hu
    rw [Function.mem_support] at hu
    exact (hSmem u).mpr (by intro hd0; exact hu (by simp [hd0]))
  have hBs := Commons.Analysis.Complex.logDeriv_sub_divisor_le (f := riemannZeta₁) (c := cA) (R := R) (A := A) (α := α)
    (by linarith [hRlo]) hA1 hα0 hα
    (fun z _ => differentiable_riemannZeta₁.analyticAt z) hcA0 hcircR hcircR2 hgrowth hs_ball hζ1s
  have hBs1 := Commons.Analysis.Complex.logDeriv_sub_divisor_le (f := riemannZeta₁) (c := cA) (R := R) (A := A) (α := α)
    (by linarith [hRlo]) hA1 hα0 hα
    (fun z _ => differentiable_riemannZeta₁.analyticAt z) hcA0 hcircR hcircR2 hgrowth hs₁_ball hζ1s1
  set B : ℝ := 4 * Real.log A / (R * (1 - 2 * α) ^ 2) with hBdef
  have hugly1 : ‖logDeriv riemannZeta₁ s - ∑ u ∈ S, ((d u : ℤ) : ℂ) * (1 / (s - u))‖ ≤ B := by
    rw [hfin_s] at hBs
    exact hBs
  have hugly2 : ‖logDeriv riemannZeta₁ s₁ - ∑ u ∈ S, ((d u : ℤ) : ℂ) * (1 / (s₁ - u))‖ ≤ B := by
    rw [hfin_s1] at hBs1
    exact hBs1
  -- B ≤ KB * L
  have hB_le : B ≤ KB * L := by
    rw [hBdef]
    have hden : 0 < R * (1 - 2 * α) ^ 2 := by rw [hαdef]; positivity
    have hden14 : (14 / 25 : ℝ) ≤ R * (1 - 2 * α) ^ 2 := by rw [hαdef]; nlinarith [hRlo]
    have hlogA : Real.log A ≤ |Real.log KgA| + 26 * L := by
      rw [hAdef]
      have h1 : Real.log (KgA * (|t| + 7) ^ 13) = Real.log KgA + 13 * Real.log (|t| + 7) := by
        rw [Real.log_mul (by linarith [hKgA1]) (by positivity), Real.log_pow]
        push_cast; ring
      rw [h1]
      linarith [hlogt7, le_abs_self (Real.log KgA)]
    have hlogAnn : 0 ≤ Real.log A := Real.log_nonneg hA1
    have hstep : 4 * Real.log A / (R * (1 - 2 * α) ^ 2) ≤ 8 * |Real.log KgA| + 186 * L := by
      have hmid : 4 * Real.log A / (R * (1 - 2 * α) ^ 2)
          ≤ (50 / 7) * (|Real.log KgA| + 26 * L) := by
        rw [div_le_iff₀ hden]
        nlinarith [hlogA, hlogAnn, hden14, abs_nonneg (Real.log KgA), hL1]
      have h2 : (50 / 7 : ℝ) * (|Real.log KgA| + 26 * L) ≤ 8 * |Real.log KgA| + 186 * L := by
        have := abs_nonneg (Real.log KgA); nlinarith
      linarith [hmid, h2]
    rw [hKBdef]
    nlinarith [hstep, abs_nonneg (Real.log KgA), hL1]
  have hld1 : logDeriv riemannZeta₁ s₁ = deriv riemannZeta s₁ / riemannZeta s₁ + (s₁ - 1)⁻¹ :=
    logDeriv_zeta1_eq s₁ hs₁_nz hzc1
  have hlogd1 : ‖logDeriv riemannZeta₁ s₁‖ ≤ (L + C₀) + L := by
    rw [hld1]
    have h3 : ‖deriv riemannZeta s₁ / riemannZeta s₁‖ ≤ 1 / (s₁.re - 1) + C₀ :=
      heuler s₁ (by rw [hs₁re]; exact hσ1) (by rw [hs₁re]; exact hσ13)
    have h4 : ‖(s₁ - 1)⁻¹‖ ≤ L := by
      rw [norm_inv, inv_eq_one_div]
      have hne : s₁ - 1 ≠ 0 := sub_ne_zero.mpr hs₁_nz
      have hpos : 0 < ‖s₁ - 1‖ := norm_pos_iff.mpr hne
      rw [div_le_iff₀ hpos]
      have hge : 1 / L ≤ ‖s₁ - 1‖ := by
        have h := Complex.abs_re_le_norm (s₁ - 1)
        rw [show (s₁ - 1).re = 1 / L by simp [s₁]] at h
        rwa [abs_of_nonneg (by positivity)] at h
      have hLL : (1 / L) * L = 1 := by field_simp
      nlinarith [hge, hLpos, hpos, hLL]
    calc ‖deriv riemannZeta s₁ / riemannZeta s₁ + (s₁ - 1)⁻¹‖
        ≤ ‖deriv riemannZeta s₁ / riemannZeta s₁‖ + ‖(s₁ - 1)⁻¹‖ := norm_add_le _ _
      _ ≤ (1 / (s₁.re - 1) + C₀) + L := add_le_add h3 h4
      _ = (L + C₀) + L := by
          rw [hs₁re]
          have h5 : 1 / (1 + 1 / L - 1) = L := by
            rw [show (1 : ℝ) + 1 / L - 1 = 1 / L by ring, one_div_div]
            simp
          rw [h5]
  set M₁ : ℝ := B + (L + C₀) + L with hM₁def
  have hT1 : ‖∑ u ∈ S, ((d u : ℤ) : ℂ) * (1 / (s₁ - u))‖ ≤ M₁ := by
    have heq : logDeriv riemannZeta₁ s₁ -
        (logDeriv riemannZeta₁ s₁ - ∑ u ∈ S, ((d u : ℤ) : ℂ) * (1 / (s₁ - u)))
        = ∑ u ∈ S, ((d u : ℤ) : ℂ) * (1 / (s₁ - u)) := by ring
    rw [← heq, hM₁def]
    calc ‖logDeriv riemannZeta₁ s₁ -
          (logDeriv riemannZeta₁ s₁ - ∑ u ∈ S, ((d u : ℤ) : ℂ) * (1 / (s₁ - u)))‖
        ≤ ‖logDeriv riemannZeta₁ s₁‖ +
          ‖logDeriv riemannZeta₁ s₁ - ∑ u ∈ S, ((d u : ℤ) : ℂ) * (1 / (s₁ - u))‖ :=
          norm_sub_le _ _
      _ ≤ ((L + C₀) + L) + B := add_le_add hlogd1 hugly2
      _ = B + (L + C₀) + L := by ring
  have hzre : ∀ u ∈ S, δ₀ / L ≤ s₁.re - u.re := by
    intro u hu
    have hdun : d u ≠ 0 := (hSmem u).mp hu
    have hdun' : (MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall cA (R / 2))) u ≠ 0 := hdun
    have hzu : riemannZeta₁ u = 0 :=
      Commons.Analysis.Complex.zero_of_divisor_ne_zero (a := cA) (ρ := R / 2)
        (fun z _ => differentiable_riemannZeta₁.analyticAt z) hdun'
    have huim : |u.im - t| ≤ R / 2 := by
      have hu_ball : u ∈ Metric.closedBall cA (R / 2) :=
        Commons.Analysis.Complex.divisor_mem_of_ne_zero hdun'
      have h := Complex.abs_im_le_norm (u - cA)
      rw [show (u - cA).im = u.im - t by simp [cA]] at h
      have h2 : ‖u - cA‖ ≤ R / 2 := by
        rw [Metric.mem_closedBall, dist_eq_norm] at hu_ball; exact hu_ball
      linarith
    have hlogu : Real.log (|u.im| + 3) ≤ 2 * L := by
      have h1 : |u.im| ≤ |t| + 2 := by
        rw [abs_le] at huim
        rw [abs_le]; exact ⟨by linarith [huim.1, neg_abs_le t], by linarith [huim.2, le_abs_self t]⟩
      have h2 : |u.im| + 3 ≤ (|t| + 2) ^ 2 := by nlinarith [h1, ht, abs_nonneg t, sq_nonneg |t|]
      have h3 : Real.log (|u.im| + 3) ≤ Real.log ((|t| + 2) ^ 2) :=
        Real.log_le_log (by positivity) h2
      rw [Real.log_pow] at h3
      push_cast at h3
      rw [hLdef]
      linarith [h3]
    have hu_ne1 : u ≠ 1 := by
      intro h; rw [h, riemannZeta₁_one] at hzu; exact one_ne_zero hzu
    have hzζ : riemannZeta u = 0 := by
      rw [riemannZeta_eq_inv_sub_mul hu_ne1, hzu, mul_zero]
    have huim_ge : 1 ≤ |u.im| := by
      have h3 : |t| - |u.im| ≤ |u.im - t| := by
        simpa [abs_sub_comm] using abs_sub_abs_le_abs_sub t u.im
      linarith [huim, h3, ht, hRlo]
    have hzfre := hzf u hzζ huim_ge
    have hlogpos : 0 < Real.log (|u.im| + 3) := Real.log_pos (by linarith [abs_nonneg u.im])
    have hcmp : c₀ / (2 * L) ≤ c₀ / Real.log (|u.im| + 3) := by
      rw [div_le_div_iff₀ (by positivity) hlogpos]
      nlinarith [hc₀, hlogu]
    have hδ : δ₀ / L = 1 / L + c₀ / (2 * L) := by rw [hδ₀def]; ring
    rw [hs₁re, hδ]
    linarith [hzfre, hcmp]
  have hzu0 : ∀ u ∈ S, riemannZeta u = 0 := by
    intro u hu
    have hdun : d u ≠ 0 := (hSmem u).mp hu
    have hdun' : (MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall cA (R / 2))) u ≠ 0 := hdun
    have hzu : riemannZeta₁ u = 0 :=
      Commons.Analysis.Complex.zero_of_divisor_ne_zero (a := cA) (ρ := R / 2)
        (fun z _ => differentiable_riemannZeta₁.analyticAt z) hdun'
    have hu_ne1 : u ≠ 1 := by
      intro h; rw [h, riemannZeta₁_one] at hzu; exact one_ne_zero hzu
    rw [riemannZeta_eq_inv_sub_mul hu_ne1, hzu, mul_zero]
  have hs_ne : ∀ u ∈ S, s ≠ u := by
    intro u hu h
    exact hzc0 (by rw [h]; exact hzu0 u hu)
  have hs₁_ne : ∀ u ∈ S, s₁ ≠ u := by
    intro u hu h
    exact hzc1 (by rw [h]; exact hzu0 u hu)
  have hU : ∑ u ∈ S, ((d u : ℤ) : ℝ) / ‖s₁ - u‖ ^ 2 ≤ (L / δ₀) * M₁ := by
    have hterm : ∀ u ∈ S, ((d u : ℤ) : ℝ) / ‖s₁ - u‖ ^ 2
        ≤ (L / δ₀) * (((d u : ℤ) : ℝ) * (1 / (s₁ - u)).re) := by
      intro u hu
      have hdu0 : (0 : ℝ) ≤ ((d u : ℤ) : ℝ) := hdnn u
      have hre : (1 / (s₁ - u)).re = (s₁.re - u.re) / ‖s₁ - u‖ ^ 2 := by
        rw [one_div, Complex.inv_re, Complex.sub_re, Complex.normSq_eq_norm_sq]
      rw [hre]
      have hpos : 0 < ‖s₁ - u‖ ^ 2 := by
        have : s₁ - u ≠ 0 := sub_ne_zero.mpr (hs₁_ne u hu)
        positivity
      have hker : 1 ≤ (L / δ₀) * (s₁.re - u.re) := by
        have h2 : (L / δ₀) * (δ₀ / L) = 1 := by field_simp
        rw [← h2]
        exact mul_le_mul_of_nonneg_left (hzre u hu) (by positivity)
      have hmain : 1 / ‖s₁ - u‖ ^ 2 ≤ (L / δ₀) * ((s₁.re - u.re) / ‖s₁ - u‖ ^ 2) := by
        rw [div_le_iff₀ hpos]
        have hq : ((s₁.re - u.re) / ‖s₁ - u‖ ^ 2) * ‖s₁ - u‖ ^ 2 = (s₁.re - u.re) := by
          rw [div_mul_cancel₀ _ (ne_of_gt hpos)]
        rw [mul_assoc, hq]
        exact hker
      calc ((d u : ℤ) : ℝ) / ‖s₁ - u‖ ^ 2
          = ((d u : ℤ) : ℝ) * (1 / ‖s₁ - u‖ ^ 2) := by ring
        _ ≤ ((d u : ℤ) : ℝ) * ((L / δ₀) * ((s₁.re - u.re) / ‖s₁ - u‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left hmain hdu0
        _ = (L / δ₀) * (((d u : ℤ) : ℝ) * ((s₁.re - u.re) / ‖s₁ - u‖ ^ 2)) := by ring
    calc ∑ u ∈ S, ((d u : ℤ) : ℝ) / ‖s₁ - u‖ ^ 2
        ≤ ∑ u ∈ S, (L / δ₀) * (((d u : ℤ) : ℝ) * (1 / (s₁ - u)).re) := Finset.sum_le_sum hterm
      _ = (L / δ₀) * ∑ u ∈ S, (((d u : ℤ) : ℝ) * (1 / (s₁ - u)).re) := by rw [Finset.mul_sum]
      _ ≤ (L / δ₀) * M₁ := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hre : ∑ u ∈ S, (((d u : ℤ) : ℝ) * (1 / (s₁ - u)).re)
              = (∑ u ∈ S, ((d u : ℤ) : ℂ) * (1 / (s₁ - u))).re := by
            rw [Complex.re_sum]
            apply Finset.sum_congr rfl
            intro u _
            rw [Complex.mul_re]
            simp [Complex.ofReal_re, Complex.ofReal_im]
          rw [hre]
          exact le_trans (Complex.re_le_norm _) hT1
  have hs1s : ‖s₁ - s‖ ≤ (1 + c) / L := by
    have h : s₁ - s = ((1 + 1 / L - σ : ℝ) : ℂ) := by
      rw [hs₁def, hsdef]; push_cast; ring
    rw [h, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith [hσhi] : 0 ≤ 1 + 1 / L - σ)]
    rw [show (1 + c) / L = 1 / L + c / L by ring]
    linarith [hσlo]
  have hsu : ∀ u ∈ S, δ₁ / L ≤ ‖s - u‖ := by
    intro u hu
    have h1 : u.re ≤ 1 - c₀ / (2 * L) := by
      have h2 := hzre u hu
      rw [hs₁re] at h2
      have h3 : (1 : ℝ) + 1 / L - δ₀ / L = 1 - c₀ / (2 * L) := by
        rw [hδ₀def]; field_simp; ring
      linarith [h2, h3]
    have h4 : δ₁ / L ≤ σ - u.re := by
      have h5 : δ₁ / L = (1 - c / L) - (1 - c₀ / (2 * L)) := by rw [hδ₁def]; field_simp; ring
      rw [h5]; linarith [hσlo, h1]
    have h6 : σ - u.re ≤ ‖s - u‖ := by
      have h7 : |s.re - u.re| ≤ ‖s - u‖ := by
        have := Complex.abs_re_le_norm (s - u)
        rwa [show (s - u).re = s.re - u.re by simp] at this
      rw [hsre] at h7
      rwa [abs_of_nonneg (by linarith [h4, hδ₁pos, hLpos] : 0 ≤ σ - u.re)] at h7
    linarith [h4, h6]
  have hb1 : ∀ u ∈ S, ‖s₁ - u‖ ≤ (1 + (1 + c) / δ₁) * ‖s - u‖ := by
    intro u hu
    have h1 : ‖s₁ - u‖ ≤ ‖s₁ - s‖ + ‖s - u‖ := by
      calc ‖s₁ - u‖ = ‖(s₁ - s) + (s - u)‖ := by ring_nf
        _ ≤ ‖s₁ - s‖ + ‖s - u‖ := norm_add_le _ _
    have h2 : (1 + c) / L ≤ ((1 + c) / δ₁) * ‖s - u‖ := by
      have h3 : δ₁ / L ≤ ‖s - u‖ := hsu u hu
      have h4 : (1 + c) / L = ((1 + c) / δ₁) * (δ₁ / L) := by field_simp
      rw [h4]
      exact mul_le_mul_of_nonneg_left h3 (by positivity)
    linarith [h1, h2, hs1s]
  have hBnn : 0 ≤ B := by
    rw [hBdef]
    exact div_nonneg (by have := Real.log_nonneg hA1; positivity) (by positivity)
  have hM1nn : 0 ≤ M₁ := by rw [hM₁def]; linarith [hBnn, hLpos, hC₀]
  have hdiff : ‖∑ u ∈ S, ((d u : ℤ) : ℂ) * (1 / (s - u))
      - ∑ u ∈ S, ((d u : ℤ) : ℂ) * (1 / (s₁ - u))‖ ≤ (Θ - 1) * M₁ := by
    have h1 : ‖∑ u ∈ S, ((d u : ℤ) : ℂ) * (1 / (s - u))
        - ∑ u ∈ S, ((d u : ℤ) : ℂ) * (1 / (s₁ - u))‖
        = ‖∑ u ∈ S, ((d u : ℤ) : ℂ) * ((1 / (s - u)) - (1 / (s₁ - u)))‖ := by
      congr 1
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun u _ => by ring)
    rw [h1]
    have h2 : ∀ u ∈ S, ‖((d u : ℤ) : ℂ) * ((1 / (s - u)) - (1 / (s₁ - u)))‖
        ≤ ((d u : ℤ) : ℝ) * (‖s₁ - s‖ * (1 + (1 + c) / δ₁) / ‖s₁ - u‖ ^ 2) := by
      intro u hu
      have hdu0 : (0 : ℝ) ≤ ((d u : ℤ) : ℝ) := hdnn u
      have hnf : ‖((d u : ℤ) : ℂ)‖ = ((d u : ℤ) : ℝ) := by
        rw [Complex.norm_intCast, abs_of_nonneg]
        exact_mod_cast hdnn u
      have hfrac : 1 / (s - u) - 1 / (s₁ - u) = (s₁ - s) / ((s - u) * (s₁ - u)) := by
        have h1 : s - u ≠ 0 := sub_ne_zero.mpr (hs_ne u hu)
        have h2 : s₁ - u ≠ 0 := sub_ne_zero.mpr (hs₁_ne u hu)
        field_simp; ring
      have hb := hb1 u hu
      have hkey : 1 / (‖s - u‖ * ‖s₁ - u‖) ≤ (1 + (1 + c) / δ₁) / ‖s₁ - u‖ ^ 2 := by
        have hp1 : 0 < ‖s - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hs_ne u hu))
        have hp2 : 0 < ‖s₁ - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hs₁_ne u hu))
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hb, hp1, hp2]
      have hstep : ‖s₁ - s‖ / (‖s - u‖ * ‖s₁ - u‖)
          ≤ ‖s₁ - s‖ * (1 + (1 + c) / δ₁) / ‖s₁ - u‖ ^ 2 := by
        have hpos2 : 0 < ‖s₁ - u‖ ^ 2 := by
          have : s₁ - u ≠ 0 := sub_ne_zero.mpr (hs₁_ne u hu)
          positivity
        calc ‖s₁ - s‖ / (‖s - u‖ * ‖s₁ - u‖)
            = ‖s₁ - s‖ * (1 / (‖s - u‖ * ‖s₁ - u‖)) := by ring
          _ ≤ ‖s₁ - s‖ * ((1 + (1 + c) / δ₁) / ‖s₁ - u‖ ^ 2) :=
              mul_le_mul_of_nonneg_left hkey (norm_nonneg _)
          _ = ‖s₁ - s‖ * (1 + (1 + c) / δ₁) / ‖s₁ - u‖ ^ 2 := by ring
      calc ‖((d u : ℤ) : ℂ) * ((1 / (s - u)) - (1 / (s₁ - u)))‖
          = ((d u : ℤ) : ℝ) * (‖s₁ - s‖ / (‖s - u‖ * ‖s₁ - u‖)) := by
            rw [hfrac, norm_mul, hnf, norm_div, norm_mul]
        _ ≤ ((d u : ℤ) : ℝ) * (‖s₁ - s‖ * (1 + (1 + c) / δ₁) / ‖s₁ - u‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hstep hdu0
    calc ‖∑ u ∈ S, ((d u : ℤ) : ℂ) * ((1 / (s - u)) - (1 / (s₁ - u)))‖
        ≤ ∑ u ∈ S, ‖((d u : ℤ) : ℂ) * ((1 / (s - u)) - (1 / (s₁ - u)))‖ := norm_sum_le _ _
      _ ≤ ∑ u ∈ S, ((d u : ℤ) : ℝ) * (‖s₁ - s‖ * (1 + (1 + c) / δ₁) / ‖s₁ - u‖ ^ 2) :=
          Finset.sum_le_sum h2
      _ = ‖s₁ - s‖ * (1 + (1 + c) / δ₁) * (∑ u ∈ S, ((d u : ℤ) : ℝ) / ‖s₁ - u‖ ^ 2) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro u _; ring
      _ ≤ ‖s₁ - s‖ * (1 + (1 + c) / δ₁) * ((L / δ₀) * M₁) :=
          mul_le_mul_of_nonneg_left hU (by positivity)
      _ ≤ ((1 + c) / L) * (1 + (1 + c) / δ₁) * ((L / δ₀) * M₁) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_right hs1s (by positivity)
      _ = (Θ - 1) * M₁ := by
          have hΘ1 : Θ - 1 = (1 + c) * (1 + (1 + c) / δ₁) / δ₀ := by rw [hΘdef]; ring
          rw [hΘ1]
          have h1 : (1 + c) / L * (1 + (1 + c) / δ₁) * ((L / δ₀) * M₁)
              = (1 + c) * (1 + (1 + c) / δ₁) / δ₀ * M₁ := by
            field_simp
          rw [h1]
          try ring
  have hT : ‖∑ u ∈ S, ((d u : ℤ) : ℂ) * (1 / (s - u))‖ ≤ Θ * M₁ := by
    have h1 : ‖∑ u ∈ S, ((d u : ℤ) : ℂ) * (1 / (s - u))‖
        ≤ ‖∑ u ∈ S, ((d u : ℤ) : ℂ) * (1 / (s₁ - u))‖ + (Θ - 1) * M₁ := by
      have heq : ∑ u ∈ S, ((d u : ℤ) : ℂ) * (1 / (s - u))
          = (∑ u ∈ S, ((d u : ℤ) : ℂ) * (1 / (s - u))
              - ∑ u ∈ S, ((d u : ℤ) : ℂ) * (1 / (s₁ - u)))
            + ∑ u ∈ S, ((d u : ℤ) : ℂ) * (1 / (s₁ - u)) := by ring
      rw [heq]
      exact le_trans (norm_add_le _ _) (by linarith [hdiff])
    have h2 : (0 : ℝ) ≤ Θ - 1 := by
      have h3 : (1 + c) * (1 + (1 + c) / δ₁) / δ₀ ≥ 0 := by positivity
      rw [hΘdef]; linarith
    have := hT1
    linarith [h1]
  have hlogd : ‖logDeriv riemannZeta₁ s‖ ≤ B + Θ * M₁ := by
    have h1 : ‖logDeriv riemannZeta₁ s‖ ≤ B + ‖∑ u ∈ S, ((d u : ℤ) : ℂ) * (1 / (s - u))‖ := by
      have heq : logDeriv riemannZeta₁ s
          = (logDeriv riemannZeta₁ s - ∑ u ∈ S, ((d u : ℤ) : ℂ) * (1 / (s - u)))
            + ∑ u ∈ S, ((d u : ℤ) : ℂ) * (1 / (s - u)) := by ring
      rw [heq]
      calc ‖(logDeriv riemannZeta₁ s - ∑ u ∈ S, ((d u : ℤ) : ℂ) * (1 / (s - u)))
            + ∑ u ∈ S, ((d u : ℤ) : ℂ) * (1 / (s - u))‖
          ≤ ‖logDeriv riemannZeta₁ s - ∑ u ∈ S, ((d u : ℤ) : ℂ) * (1 / (s - u))‖
            + ‖∑ u ∈ S, ((d u : ℤ) : ℂ) * (1 / (s - u))‖ := norm_add_le _ _
        _ ≤ B + ‖∑ u ∈ S, ((d u : ℤ) : ℂ) * (1 / (s - u))‖ :=
            add_le_add hugly1 (le_refl _)
    linarith [h1, hT]
  have hM1' : M₁ ≤ (KB + 2) * L + C₀ := by
    rw [hM₁def]
    linarith [hB_le]
  have hfinal : ‖deriv riemannZeta s / riemannZeta s‖ ≤ (KB + Θ * (KB + 2) + 1) * L + Θ * C₀ := by
    have hlds : logDeriv riemannZeta₁ s = deriv riemannZeta s / riemannZeta s + (s - 1)⁻¹ :=
      logDeriv_zeta1_eq s hs_nz hzc0
    have h5 : ‖(s - 1)⁻¹‖ ≤ L := by
      rw [norm_inv, inv_eq_one_div]
      have hne : s - 1 ≠ 0 := sub_ne_zero.mpr hs_nz
      have hpos : 0 < ‖s - 1‖ := norm_pos_iff.mpr hne
      rw [div_le_iff₀ hpos]
      have hge : 1 / L ≤ ‖s - 1‖ := by
        have h := Complex.abs_im_le_norm (s - 1)
        have him : (s - 1).im = t := by rw [Complex.sub_im, Complex.one_im, sub_zero]; exact hsim
        rw [him] at h
        have h1 : (1 : ℝ) / L ≤ |t| := by
          rw [div_le_iff₀ hLpos]; nlinarith [ht, hL1]
        exact le_trans h1 h
      have hLL : (1 / L) * L = 1 := by field_simp
      nlinarith [hge, hLpos, hpos, hLL]
    have h6 : ‖deriv riemannZeta s / riemannZeta s‖ ≤ ‖logDeriv riemannZeta₁ s‖ + ‖(s - 1)⁻¹‖ := by
      have heq : deriv riemannZeta s / riemannZeta s = logDeriv riemannZeta₁ s - (s - 1)⁻¹ := by
        rw [hlds]; ring
      rw [heq]
      exact norm_sub_le _ _
    calc ‖deriv riemannZeta s / riemannZeta s‖
        ≤ ‖logDeriv riemannZeta₁ s‖ + ‖(s - 1)⁻¹‖ := h6
      _ ≤ (B + Θ * M₁) + L := add_le_add hlogd h5
      _ ≤ (KB * L + Θ * M₁) + L := by linarith [hB_le]
      _ ≤ (KB * L + Θ * ((KB + 2) * L + C₀)) + L := by
          have := mul_le_mul_of_nonneg_left hM1' (le_of_lt hΘpos)
          linarith
      _ = (KB + Θ * (KB + 2) + 1) * L + Θ * C₀ := by ring
  calc ‖deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) /
        riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ = ‖deriv riemannZeta s / riemannZeta s‖ := by
        rw [hsdef]
    _ ≤ (KB + Θ * (KB + 2) + 1) * L + Θ * C₀ := hfinal
    _ ≤ ((KB + Θ * (KB + 2) + 1) + (Θ * C₀) + 1) * L := by
        have h1 : Θ * C₀ ≤ Θ * C₀ * L := by
          have h0 : (0 : ℝ) ≤ Θ * C₀ := by positivity
          calc Θ * C₀ = Θ * C₀ * 1 := by ring
            _ ≤ Θ * C₀ * L := mul_le_mul_of_nonneg_left hL1 h0
        have h2 : ((KB + Θ * (KB + 2) + 1) + (Θ * C₀) + 1) * L
            = (KB + Θ * (KB + 2) + 1) * L + Θ * C₀ * L + L := by ring
        rw [h2]; linarith [h1, hLpos]
    _ = ((KB + Θ * (KB + 2) + 1) + (Θ * C₀) + 1) * Real.log (|t| + 2) := by rw [hLdef]


/-! ## Mean value bound along a segment -/

private theorem norm_sub_le_of_segment {F f : ℂ → ℂ} {c x y : ℂ} {R K : ℝ}
    (hx : x ∈ Metric.ball c R) (hy : y ∈ Metric.ball c R)
    (hF : ∀ w ∈ Metric.ball c R, HasDerivAt F (deriv f w / f w) w)
    (hK : ∀ w ∈ segment ℝ x y, ‖deriv f w / f w‖ ≤ K) :
    ‖F y - F x‖ ≤ K * ‖y - x‖ := by
  have hsub : segment ℝ x y ⊆ Metric.ball c R :=
    (convex_ball c R).segment_subset hx hy
  exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := F) (s := segment ℝ x y) (C := K)
    (f' := fun w => ContinuousLinearMap.toSpanSingleton ℂ (deriv f w / f w))
    (x := x) (y := y)
    (fun w hw => ((hF w (hsub hw)).hasFDerivAt).hasFDerivWithinAt)
    (fun w hw => by
      rw [ContinuousLinearMap.norm_toSpanSingleton]
      exact hK w hw)
    (convex_segment x y) (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)

theorem inv_zeta_le_log_zeroFree :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ σ t : ℝ,
      1 - c / Real.log (|t| + 2) ≤ σ → σ ≤ 2 →
        1 / ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          C * (Real.log (|t| + 2) + 1) := by
  obtain ⟨c_zf, C_zf, hc_zf, hC_zf, hzf, _hderiv⟩ := zeta_zeroFreeRegion_logDeriv_bound
  obtain ⟨ε₀, hε₀, hnear⟩ := zeta_zeroFree_near_axis
  obtain ⟨C0, hC0, heuler⟩ := logDeriv_zeta_norm_le_one_lt_re
  obtain ⟨c_lb, hc_lb, hlb⟩ := zeta_lower_bound_right_of_one
  set c : ℝ := min (min (c_zf / 4) (ε₀ * Real.log 2)) (1 / 48) with hcdef
  have hcpos : 0 < c := by rw [hcdef]; positivity
  have hcczf : c ≤ c_zf / 4 := by
    rw [hcdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hcε : c ≤ ε₀ * Real.log 2 := by
    rw [hcdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hc48 : c ≤ 1 / 48 := by rw [hcdef]; exact min_le_right _ _
  have hcle : c < c_zf / 2 := by linarith [hcczf]
  have hc1 : c ≤ 1 / 24 := by linarith [hc48]
  obtain ⟨K₁, hK₁pos, hKnarrow⟩ :=
    zeta_logDeriv_le_narrow (c₀ := c_zf) (C₀ := C0) hc_zf hC0
    (fun u hu him => by
      by_contra hlt
      have h3 : (1 : ℝ) - c_zf / Real.log (|u.im| + 3) ≤ u.re := by linarith [not_le.mp hlt]
      have h4 := hzf u.im him u.re h3
      have harg : ((u.re : ℂ) + Complex.I * (u.im : ℂ)) = u := by
        rw [mul_comm]; exact Complex.re_add_im u
      rw [harg] at h4
      exact h4 hu)
    (fun s hs hs3 => heuler s hs hs3) hcpos hcle hc1
  have hcLog2 : c / Real.log 2 ≤ ε₀ := by
    rw [div_le_iff₀ (Real.log_pos (by norm_num))]
    exact hcε
  have hcL7 : c / Real.log 2 ≤ c_zf / Real.log 8 := by
    rw [div_le_div_iff₀ (Real.log_pos (by norm_num)) (Real.log_pos (by norm_num))]
    have h6 : c ≤ c_zf / 4 := hcczf
    have h7 : Real.log 8 ≤ 4 * Real.log 2 := by
      have h8 : Real.log 8 = 3 * Real.log 2 := by
        rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow]; norm_num
      rw [h8]; nlinarith [Real.log_pos (by norm_num : (1:ℝ) < 2)]
    have h6' : 4 * c ≤ c_zf := by linarith [h6]
    nlinarith [h6', h7, hcpos, Real.log_pos (by norm_num : (1:ℝ) < 2),
      Real.log_pos (by norm_num : (1:ℝ) < 8)]
  set Cbig : ℝ := 4 / c_lb * Real.exp (K₁ * (1 / 4 + c)) + 30 with hCbigdef
  have hCbigpos : 0 < Cbig := by rw [hCbigdef]; positivity
  -- large heights
  have hbig : ∀ σ t : ℝ, 5 ≤ |t| → 1 - c / Real.log (|t| + 2) ≤ σ → σ ≤ 2 →
      1 / ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ Cbig * Real.log (|t| + 2) := by
    intro σ t ht hσlo hσhi
    set L : ℝ := Real.log (|t| + 2) with hLdef
    have htabs : (5 : ℝ) ≤ |t| := ht
    have ht1 : (1 : ℝ) ≤ |t| := by linarith
    have hLpos : 0 < L := Real.log_pos (by linarith [abs_nonneg t])
    have hL1 : 1 ≤ L := by
      rw [hLdef]
      have h1 : (1 : ℝ) < Real.log 3 := by linarith [Real.log_three_gt_d9]
      have h2 : Real.log 3 ≤ Real.log (|t| + 2) :=
        Real.log_le_log (by norm_num) (by linarith [abs_nonneg t, ht])
      linarith
    have hLpos2 : 0 < 4 * L := by positivity
    set σ₂ : ℝ := 1 + 1 / (4 * L) with hσ₂def
    have hσ₂hi : σ₂ ≤ 1 + 1 / L := by
      rw [hσ₂def]
      have h1 : 1 / (4 * L) ≤ 1 / L := by
        rw [div_le_div_iff₀ hLpos2 hLpos]; linarith
      linarith
    have hσ₂lo : 1 - c / L ≤ σ₂ := by
      rw [hσ₂def]
      have h1 : 0 < c / L := div_pos hcpos hLpos
      have h2 : 0 < 1 / (4 * L) := by positivity
      linarith
    have hσ₂gt1 : 1 < σ₂ := by
      rw [hσ₂def]
      have h1 : 0 < 1 / (4 * L) := by positivity
      linarith
    have hσlo' : 1 - c / L ≤ σ := by rwa [hLdef] at hσlo
    rcases le_total σ₂ σ with hge | hlt
    · -- σ ≥ σ₂: use the three-four-one lower bound
      have hσ1 : 1 < σ := lt_of_lt_of_le hσ₂gt1 hge
      have h341 := Commons.NumberTheory.LSeries.norm_riemannZeta_lower_of_three_four_one
        (σ := σ) (t := t) hσ1 hσhi ht1
      rw [← hLdef] at h341
      have hσm : 1 / (4 * L) ≤ σ - 1 := by linarith [hge, hσ₂def]
      have hbase : 1 / (6400 * L ^ 4) ≤ (σ - 1) ^ 3 / (100 * L) := by
        have h2 : (1 / (4 * L)) ^ 3 ≤ (σ - 1) ^ 3 := pow_le_pow_left₀ (by positivity) hσm 3
        have h3 : (1 / (4 * L)) ^ 3 / (100 * L) = 1 / (6400 * L ^ 4) := by field_simp; ring
        rw [← h3]
        exact div_le_div_of_nonneg_right h2 (by positivity)
      have hb : ((σ - 1) ^ 3 / (100 * L)) ^ (-(1 / 4) : ℝ) ≤ 10 * L := by
        have h4 : ((1 : ℝ) / (6400 * L ^ 4)) ^ (-(1 / 4) : ℝ) = (6400 * L ^ 4) ^ (1 / 4 : ℝ) := by
          have hX : (0:ℝ) < 6400 * L ^ 4 := by positivity
          rw [one_div, Real.inv_rpow (le_of_lt hX), Real.rpow_neg (le_of_lt hX), inv_inv]
        have h5 : (6400 * L ^ 4) ^ (1 / 4 : ℝ) = (6400 : ℝ) ^ (1 / 4 : ℝ) * L := by
          rw [Real.mul_rpow (by norm_num) (by positivity),
            show ((L ^ 4 : ℝ)) = L ^ (4 : ℕ) by ring,
            ← Real.rpow_natCast L 4, ← Real.rpow_mul (le_of_lt hLpos)]
          norm_num
        have h6 : ((6400 : ℝ)) ^ (1 / 4 : ℝ) ≤ 10 := by
          have h := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 6400) (by norm_num : (6400:ℝ) ≤ 10^4)
            (by norm_num : (0:ℝ) ≤ 1/4)
          rw [show ((10:ℝ)^4) = 10 ^ (4:ℕ) by ring, ← Real.rpow_natCast (10:ℝ) 4,
            ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 10)] at h
          norm_num at h
          exact h
        have h7 : ((σ - 1) ^ 3 / (100 * L)) ^ (-(1 / 4) : ℝ) ≤ ((1 : ℝ) / (6400 * L ^ 4)) ^ (-(1 / 4) : ℝ) := by
          apply Real.rpow_le_rpow_of_nonpos (by positivity) hbase
          norm_num
        rw [h4, h5] at h7
        nlinarith [h6, h7, hLpos]
      have hfin : 1 / ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 10 * L := by
        have hpos : 0 < ((σ - 1) ^ 3 / (100 * L)) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
        have hζpos : 0 < ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
          apply norm_pos_iff.mpr
          intro hcon
          rw [hcon] at h341
          simp only [norm_zero] at h341
          have := Real.rpow_pos_of_pos (by positivity : (0:ℝ) < (σ-1)^3/(100*L)) (1/4:ℝ)
          linarith
        have h8 : ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖⁻¹
            ≤ (((σ - 1) ^ 3 / (100 * L)) ^ (1 / 4 : ℝ))⁻¹ :=
          (inv_le_inv₀ hζpos hpos).mpr h341
        rw [inv_eq_one_div] at h8
        refine le_trans h8 ?_
        rw [← Real.rpow_neg (le_of_lt (by positivity : (0:ℝ) < (σ-1)^3/(100*L)))]
        exact hb
      have h30 : (30 : ℝ) ≤ Cbig := by
        rw [hCbigdef]
        have h1 : (0:ℝ) ≤ 4 / c_lb * Real.exp (K₁ * (1 / 4 + c)) := by positivity
        linarith
      calc 1 / ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 10 * L := hfin
        _ ≤ Cbig * L := by nlinarith [h30, hLpos]
    · -- σ < σ₂: integrate along the segment
      have hσ₂σ : σ ≤ σ₂ := hlt
      set m : ℂ := ((((1 - c / L) + σ₂) / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I with hmdef
      set ρ : ℝ := (1 / 8 + 2 * c / 3) / L with hρdef
      have hρpos : 0 < ρ := by rw [hρdef]; positivity
      have hρ1 : ρ ≤ 1 := by
        rw [hρdef, div_le_one hLpos]
        nlinarith [hc1, hL1]
      have hmre : m.re = ((1 - c / L) + σ₂) / 2 := by simp [m]
      have hmim : m.im = t := by simp [m]
      have h1not : (1 : ℂ) ∉ Metric.ball m ρ := by
        intro hc
        rw [Metric.mem_ball, dist_eq_norm] at hc
        have h2 : |t| ≤ ‖(1 : ℂ) - m‖ := by
          have h := Complex.abs_im_le_norm ((1 : ℂ) - m)
          rw [show ((1 : ℂ) - m).im = -t by simp [m]] at h
          rwa [abs_neg] at h
        have h3 : ‖(1 : ℂ) - m‖ = ‖m - 1‖ := by rw [norm_sub_rev]
        rw [h3] at hc h2
        linarith [hc, h2, htabs, hρ1]
      have hball : ∀ w ∈ Metric.ball m ρ, riemannZeta w ≠ 0 := by
        intro w hw hcontra
        have hwn : ‖w - m‖ < ρ := by simpa [Metric.mem_ball, dist_eq_norm] using hw
        have hre : 1 - 7 * c / (6 * L) ≤ w.re := by
          have h1 : |w.re - m.re| ≤ ‖w - m‖ := by
            have := Complex.abs_re_le_norm (w - m)
            rwa [show (w - m).re = w.re - m.re by simp] at this
          rw [hmre] at h1
          have h2 : ((1 - c / L) + σ₂) / 2 = 1 + (1 / 4 - c) / (2 * L) := by
            rw [hσ₂def]; field_simp; ring
          rw [h2] at h1
          have h3 : 1 + (1 / 4 - c) / (2 * L) - ρ = 1 - 7 * c / (6 * L) := by
            rw [hρdef]; field_simp; ring
          have h4 : 1 + (1 / 4 - c) / (2 * L) - ‖w - m‖ ≤ w.re := by
            rw [abs_le] at h1; linarith [h1.1]
          linarith [h3, h4, hwn]
        have himge : 1 ≤ |w.im| := by
          have h1 : |w.im - m.im| ≤ ‖w - m‖ := by
            have := Complex.abs_im_le_norm (w - m)
            rwa [show (w - m).im = w.im - m.im by simp] at this
          rw [hmim] at h1
          have h2 : |t| - |w.im| ≤ |w.im - t| := by
            simpa [abs_sub_comm] using abs_sub_abs_le_abs_sub t w.im
          have h4 : |w.im - t| ≤ ρ := le_trans h1 (le_of_lt hwn)
          linarith [h2, h4, htabs, abs_nonneg w.im]
        have hlogw : Real.log (|w.im| + 3) ≤ 2 * L := by
          have h0 : |w.im - t| ≤ ρ := by
            have h2 : |w.im - m.im| ≤ ‖w - m‖ := by
              have := Complex.abs_im_le_norm (w - m)
              rwa [show (w - m).im = w.im - m.im by simp] at this
            rw [hmim] at h2
            exact le_trans h2 (le_of_lt hwn)
          have h1 : |w.im| ≤ |t| + 1 := by
            rw [abs_le] at h0
            rw [abs_le]
            exact ⟨by linarith [h0.1, neg_abs_le t, hρ1], by linarith [h0.2, le_abs_self t, hρ1]⟩
          have h2 : |w.im| + 3 ≤ (|t| + 2) ^ 2 := by
            nlinarith [h1, htabs, abs_nonneg t, sq_nonneg |t|]
          have h3 : Real.log (|w.im| + 3) ≤ Real.log ((|t| + 2) ^ 2) :=
            Real.log_le_log (by positivity) h2
          rw [Real.log_pow] at h3; push_cast at h3
          rw [hLdef]; linarith
        have h1 : c_zf / (2 * L) ≤ c_zf / Real.log (|w.im| + 3) := by
          rw [div_le_div_iff₀ (by positivity) (Real.log_pos (by linarith [himge]))]
          nlinarith [hc_zf, hlogw]
        have h2 : 7 * c / (6 * L) ≤ c_zf / (2 * L) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [hcczf]
        have h3 : 1 - c_zf / Real.log (|w.im| + 3) ≤ w.re := by linarith [hre, h1, h2]
        have h4 := hzf w.im himge w.re h3
        have harg : ((w.re : ℂ) + Complex.I * (w.im : ℂ)) = w := by
          rw [mul_comm]; exact Complex.re_add_im w
        rw [harg] at h4
        exact h4 hcontra
      have hzeta_an : AnalyticOnNhd ℂ riemannZeta (Metric.ball m ρ) := by
        rw [Complex.analyticOnNhd_iff_differentiableOn Metric.isOpen_ball]
        intro z hz
        exact (differentiableAt_riemannZeta (by intro h1; exact h1not (h1 ▸ hz))).differentiableWithinAt
      obtain ⟨F, _hFd, hFh, _hFc, hFre⟩ :=
        Commons.Analysis.Complex.logPrimitiveOnBall_analytic (g := riemannZeta) (c := m) (R := ρ)
          hzeta_an hρpos hball
      have hmemb : ∀ x : ℝ, x ∈ Set.Icc σ σ₂ → ((x : ℂ) + (t : ℂ) * Complex.I) ∈ Metric.ball m ρ := by
        intro x hx
        rw [Set.mem_Icc] at hx
        rw [Metric.mem_ball, dist_eq_norm]
        have h1 : ‖((x : ℂ) + (t : ℂ) * Complex.I) - m‖ = |x - m.re| := by
          have h : ((x : ℂ) + (t : ℂ) * Complex.I) - m = ((x - m.re : ℝ) : ℂ) := by
            apply Complex.ext <;> simp [m]
          rw [h, Complex.norm_real, Real.norm_eq_abs]
        rw [h1]
        have h2 : m.re = 1 + (1 / 4 - c) / (2 * L) := by
          rw [hmre, hσ₂def]; field_simp; ring
        rw [h2]
        have h4 : (1 - c / L) - (1 + (1 / 4 - c) / (2 * L)) = -(1 / 8 + c / 2) / L := by
          field_simp; ring
        have h6 : σ₂ - (1 + (1 / 4 - c) / (2 * L)) = (1 / 8 + c / 2) / L := by
          rw [hσ₂def]; field_simp; ring
        have h3 : |x - (1 + (1 / 4 - c) / (2 * L))| ≤ (1 / 8 + c / 2) / L := by
          refine abs_le.mpr ⟨?_, ?_⟩
          · have hx1 : 1 - c / L ≤ x := le_trans hσlo' hx.1
            linarith [h4, hx1]
          · have hx2 : x ≤ σ₂ := hx.2
            linarith [h6, hx2]
        have h5 : (1 / 8 + c / 2) / L < ρ := by
          rw [hρdef, div_lt_div_iff₀ hLpos hLpos]
          nlinarith [hcpos]
        linarith [h3, h5]
      have hsegK : ∀ w ∈ segment ℝ ((σ : ℂ) + (t : ℂ) * Complex.I) ((σ₂ : ℂ) + (t : ℂ) * Complex.I),
          ‖deriv riemannZeta w / riemannZeta w‖ ≤ K₁ * L := by
        intro w hw
        rw [segment_eq_image'] at hw
        obtain ⟨θ, hθ, rfl⟩ := hw
        change ‖deriv riemannZeta (((σ : ℂ) + (t : ℂ) * Complex.I)
            + θ • (((σ₂ : ℂ) + (t : ℂ) * Complex.I) - ((σ : ℂ) + (t : ℂ) * Complex.I))) /
            riemannZeta (((σ : ℂ) + (t : ℂ) * Complex.I)
            + θ • (((σ₂ : ℂ) + (t : ℂ) * Complex.I) - ((σ : ℂ) + (t : ℂ) * Complex.I)))‖ ≤ K₁ * L
        have hwr : (((σ : ℂ) + (t : ℂ) * Complex.I)
            + θ • (((σ₂ : ℂ) + (t : ℂ) * Complex.I) - ((σ : ℂ) + (t : ℂ) * Complex.I))).re
            = σ + θ * (σ₂ - σ) := by
          simp only [Complex.real_smul, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
            Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.sub_re]
          ring
        have hwi : (((σ : ℂ) + (t : ℂ) * Complex.I)
            + θ • (((σ₂ : ℂ) + (t : ℂ) * Complex.I) - ((σ : ℂ) + (t : ℂ) * Complex.I))).im
            = t := by
          simp only [Complex.real_smul, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
            Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.sub_im]
          ring
        have hθ0 : 0 ≤ θ := hθ.1
        have hθ1 : θ ≤ 1 := hθ.2
        have h1 : 1 - c / L ≤ σ + θ * (σ₂ - σ) := by
          nlinarith [hσlo', hσ₂σ, hθ0, hθ1]
        have h2 : σ + θ * (σ₂ - σ) ≤ 1 + 1 / L := by
          nlinarith [hσ₂hi, hσ₂σ, hσlo', hθ0, hθ1]
        have h3 := hKnarrow t (σ + θ * (σ₂ - σ)) ht h1 h2
        have hweq : ((σ : ℂ) + (t : ℂ) * Complex.I)
            + θ • (((σ₂ : ℂ) + (t : ℂ) * Complex.I) - ((σ : ℂ) + (t : ℂ) * Complex.I))
            = (((σ + θ * (σ₂ - σ) : ℝ)) : ℂ) + (t : ℂ) * Complex.I := by
          apply Complex.ext
          · rw [hwr]; simp
          · rw [hwi]; simp
        rw [hweq]
        exact h3
      have hsub : ‖(((σ₂ : ℂ) + (t : ℂ) * Complex.I) - ((σ : ℂ) + (t : ℂ) * Complex.I))‖
          = σ₂ - σ := by
        have h : (((σ₂ : ℂ) + (t : ℂ) * Complex.I) - ((σ : ℂ) + (t : ℂ) * Complex.I))
            = (((σ₂ - σ : ℝ)) : ℂ) := by
          apply Complex.ext <;> simp
        rw [h, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by linarith [hσ₂σ])]
      have hmemb1 : ((σ : ℂ) + (t : ℂ) * Complex.I) ∈ Metric.ball m ρ :=
        hmemb σ (Set.left_mem_Icc.mpr hσ₂σ)
      have hmemb2 : ((σ₂ : ℂ) + (t : ℂ) * Complex.I) ∈ Metric.ball m ρ :=
        hmemb σ₂ (Set.right_mem_Icc.mpr hσ₂σ)
      have hmean := norm_sub_le_of_segment hmemb1 hmemb2 hFh hsegK
      have hlb2 : c_lb / (4 * L) ≤ ‖riemannZeta ((σ₂ : ℂ) + (t : ℂ) * Complex.I)‖ := by
        have h := hlb (1 / (4 * L)) t (by positivity) (by
          rw [div_le_iff₀ hLpos2]; linarith [hL1])
        have he : 1 + 1 / (4 * L) = σ₂ := by rw [hσ₂def]
        have harg : (((1 + 1 / (4 * L) : ℝ) : ℂ) + Complex.I * (t : ℂ))
            = ((σ₂ : ℂ) + (t : ℂ) * Complex.I) := by
          rw [he]; ring
        rw [harg] at h
        calc c_lb / (4 * L) = c_lb * (1 / (4 * L)) := by ring
          _ ≤ ‖riemannZeta ((σ₂ : ℂ) + (t : ℂ) * Complex.I)‖ := h
      have hlogbound : Real.log (c_lb / (4 * L)) - K₁ * L * (σ₂ - σ)
          ≤ Real.log ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
        have h1 : (F (((σ : ℂ) + (t : ℂ) * Complex.I))).re
            = Real.log ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := hFre _ hmemb1
        have h2 : (F (((σ₂ : ℂ) + (t : ℂ) * Complex.I))).re
            = Real.log ‖riemannZeta ((σ₂ : ℂ) + (t : ℂ) * Complex.I)‖ := hFre _ hmemb2
        have h3 : Real.log (c_lb / (4 * L)) ≤ (F (((σ₂ : ℂ) + (t : ℂ) * Complex.I))).re := by
          rw [h2]
          exact Real.log_le_log (by positivity) hlb2
        have h4 : ‖F (((σ₂ : ℂ) + (t : ℂ) * Complex.I)) - F (((σ : ℂ) + (t : ℂ) * Complex.I))‖
            ≤ K₁ * L * (σ₂ - σ) := by
          rw [← hsub]
          exact hmean
        have h5 : (F (((σ : ℂ) + (t : ℂ) * Complex.I))).re
            ≥ (F (((σ₂ : ℂ) + (t : ℂ) * Complex.I))).re
              - ‖F (((σ₂ : ℂ) + (t : ℂ) * Complex.I)) - F (((σ : ℂ) + (t : ℂ) * Complex.I))‖ := by
          have h6 : (F (((σ₂ : ℂ) + (t : ℂ) * Complex.I))
              - F (((σ : ℂ) + (t : ℂ) * Complex.I))).re
              ≤ ‖F (((σ₂ : ℂ) + (t : ℂ) * Complex.I)) - F (((σ : ℂ) + (t : ℂ) * Complex.I))‖ :=
            Complex.re_le_norm _
          rw [Complex.sub_re] at h6
          linarith
        linarith [h1, h3, h4, h5]
      have hexp2 : c_lb / (4 * L) * Real.exp (-(K₁ * L * (σ₂ - σ)))
          ≤ ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
        have hp1 : 0 < c_lb / (4 * L) := by positivity
        have hp2 : 0 < ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ :=
          norm_pos_iff.mpr (hball _ hmemb1)
        calc c_lb / (4 * L) * Real.exp (-(K₁ * L * (σ₂ - σ)))
            = Real.exp (Real.log (c_lb / (4 * L)) + (-(K₁ * L * (σ₂ - σ)))) := by
              rw [Real.exp_add, Real.exp_log hp1]
          _ = Real.exp (Real.log (c_lb / (4 * L)) - K₁ * L * (σ₂ - σ)) := by ring_nf
          _ ≤ Real.exp (Real.log ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖) :=
              Real.exp_le_exp.mpr hlogbound
          _ = ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := Real.exp_log hp2
      have hexp3 : K₁ * L * (σ₂ - σ) ≤ K₁ * (1 / 4 + c) := by
        have h5 : σ₂ - σ ≤ (1 / 4 + c) / L := by
          have h6 : σ₂ = 1 + 1 / (4 * L) := hσ₂def
          have h7 : 1 - c / L ≤ σ := hσlo'
          have h8 : (1 + 1 / (4 * L)) - (1 - c / L) = (1 / 4 + c) / L := by field_simp; ring
          linarith [h6, h7, h8]
        have h9 : (σ₂ - σ) * L ≤ (1 / 4 + c) := by
          have h11 : (σ₂ - σ) * L ≤ ((1 / 4 + c) / L) * L := mul_le_mul_of_nonneg_right h5 (le_of_lt hLpos)
          rw [div_mul_cancel₀ _ (ne_of_gt hLpos)] at h11
          exact h11
        nlinarith [h9, hK₁pos, hLpos]
      calc 1 / ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ 1 / (c_lb / (4 * L) * Real.exp (-(K₁ * L * (σ₂ - σ)))) :=
            one_div_le_one_div_of_le (by positivity) hexp2
        _ = (4 * L / c_lb) * Real.exp (K₁ * L * (σ₂ - σ)) := by
            have h1 : (Real.exp (-(K₁ * L * (σ₂ - σ))))⁻¹ = Real.exp (K₁ * L * (σ₂ - σ)) := by
              rw [← Real.exp_neg]; congr 1; ring
            rw [one_div, mul_inv, h1, inv_div]
        _ ≤ (4 * L / c_lb) * Real.exp (K₁ * (1 / 4 + c)) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp3) (by positivity)
        _ = (4 / c_lb * Real.exp (K₁ * (1 / 4 + c))) * L := by ring
        _ ≤ Cbig * L := by
            have h1 : 4 / c_lb * Real.exp (K₁ * (1 / 4 + c)) ≤ Cbig := by
              rw [hCbigdef]; linarith
            nlinarith [h1, hLpos]
  -- small heights
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℂ, ‖z - 1‖ < δ → (1 / 2 : ℝ) ≤ ‖riemannZeta₁ z‖ := by
    have hcont : ContinuousAt (fun z : ℂ => ‖riemannZeta₁ z‖) 1 :=
      differentiable_riemannZeta₁.continuous.continuousAt.norm
    have h1 : ∀ᶠ z in 𝓝 (1 : ℂ), (1 / 2 : ℝ) < ‖riemannZeta₁ z‖ :=
      hcont.eventually (isOpen_Ioi.mem_nhds (by norm_num [riemannZeta₁_one]))
    obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.mp h1
    refine ⟨δ, hδpos, fun z hz => ?_⟩
    have hz' : dist z 1 < δ := by rw [dist_eq_norm]; exact hz
    exact le_of_lt (hδ hz')
  set δ : ℝ := min δ₀ (1 / 2) with hδdef
  have hδpos : 0 < δ := lt_min hδ₀pos (by norm_num)
  have hδle : δ ≤ 1 / 2 := min_le_right _ _
  have hδ10 : δ ≤ δ₀ := min_le_left _ _
  have hδ₁ : ∀ z : ℂ, ‖z - 1‖ < δ → (1 / 2 : ℝ) ≤ ‖riemannZeta₁ z‖ :=
    fun z hz => hδ₀ z (lt_of_lt_of_le hz hδ10)
  have hCsm : ∃ Csm : ℝ, 0 < Csm ∧ ∀ s : ℂ, 1 - c / Real.log 2 ≤ s.re → s.re ≤ 2 →
      |s.im| ≤ 5 → δ ≤ ‖s - 1‖ → 1 / ‖riemannZeta s‖ ≤ Csm := by
    set K : Set ℂ := Metric.closedBall (0 : ℂ) 10 ∩ {s : ℂ | 1 - c / Real.log 2 ≤ s.re}
      ∩ {s : ℂ | s.re ≤ 2} ∩ {s : ℂ | |s.im| ≤ 5} ∩ {s : ℂ | δ ≤ ‖s - 1‖} with hKdef
    have hKc : IsCompact K := by
      rw [hKdef]
      have h0 : IsCompact (Metric.closedBall (0 : ℂ) 10
          ∩ {s : ℂ | 1 - c / Real.log 2 ≤ s.re}) :=
        (isCompact_closedBall (0:ℂ) 10).inter_right
          (isClosed_le continuous_const continuous_re)
      have h1 : IsCompact (Metric.closedBall (0 : ℂ) 10
          ∩ {s : ℂ | 1 - c / Real.log 2 ≤ s.re} ∩ {s : ℂ | s.re ≤ 2}) :=
        h0.inter_right (isClosed_le continuous_re continuous_const)
      have h2 : IsCompact (Metric.closedBall (0 : ℂ) 10
          ∩ {s : ℂ | 1 - c / Real.log 2 ≤ s.re} ∩ {s : ℂ | s.re ≤ 2}
          ∩ {s : ℂ | |s.im| ≤ 5}) :=
        h1.inter_right (isClosed_le (by fun_prop : Continuous (fun s : ℂ => |s.im|))
          continuous_const)
      exact h2.inter_right
        (isClosed_le continuous_const (continuous_norm.comp (continuous_id.sub continuous_const)))
    have h2mem : (2 : ℂ) ∈ K := by
      rw [hKdef]
      refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
      · rw [Metric.mem_closedBall, dist_zero_right]; norm_num
      · show 1 - c / Real.log 2 ≤ (2 : ℂ).re
        rw [show (2 : ℂ).re = 2 by norm_num]
        have h2 : 0 < c / Real.log 2 := div_pos hcpos (Real.log_pos (by norm_num))
        linarith
      · show (2 : ℂ).re ≤ 2
        rw [show (2 : ℂ).re = 2 by norm_num]
      · simp
      · simp only [Set.mem_setOf_eq]
        have h1 : (2:ℂ) - 1 = 1 := by ring
        rw [h1, norm_one]; linarith [hδle]
    have hKne : K.Nonempty := ⟨2, h2mem⟩
    have hzne : ∀ s ∈ K, riemannZeta s ≠ 0 := by
      intro s hs
      rw [hKdef] at hs
      obtain ⟨⟨⟨⟨_, hsre⟩, hs2⟩, hsim⟩, _⟩ := hs
      have hsre' : 1 - c / Real.log 2 ≤ s.re := hsre
      have hs2' : s.re ≤ 2 := hs2
      have hsim' : |s.im| ≤ 5 := hsim
      have hcanon : ((s.re : ℂ) + I * (s.im : ℂ)) = s := by
        rw [mul_comm]; exact Complex.re_add_im s
      rw [← hcanon]
      rcases le_total 4 |s.im| with h4 | h4
      · have h1 : 1 ≤ |s.im| := by linarith
        have h4' : c / Real.log 2 ≤ c_zf / Real.log (|s.im| + 3) := by
          rw [div_le_div_iff₀ (Real.log_pos (by norm_num))
            (Real.log_pos (by linarith [abs_nonneg s.im]))]
          have h7 : Real.log (|s.im| + 3) ≤ Real.log 8 :=
            Real.log_le_log (by linarith [abs_nonneg s.im]) (by linarith [(abs_le.mp hsim').2])
          have h8 : Real.log 8 = 3 * Real.log 2 := by
            rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow]; norm_num
          have h9 : c * Real.log (|s.im| + 3) ≤ c * Real.log 8 :=
            mul_le_mul_of_nonneg_left h7 (le_of_lt hcpos)
          have h10 : c * Real.log 8 ≤ c_zf * Real.log 2 := by
            rw [h8]
            have h11 : 3 * c ≤ c_zf := by linarith [hcczf]
            nlinarith [Real.log_pos (by norm_num : (1:ℝ) < 2), hcpos]
          linarith
        exact hzf s.im h1 s.re (by linarith [hsre', h4'])
      · exact hnear s.im s.re h4 (by linarith [hcLog2, hsre']) hs2'
    have hcont : ContinuousOn (fun s : ℂ => ‖(riemannZeta s)⁻¹‖) K := by
      have h1 : ContinuousOn riemannZeta K := by
        intro s hs
        have hsne : s ≠ 1 := by
          rw [hKdef] at hs
          obtain ⟨⟨⟨⟨_, _⟩, _⟩, _⟩, hs4⟩ := hs
          intro h; rw [h] at hs4; simp at hs4; linarith [hδpos]
        exact ((differentiableAt_riemannZeta hsne).continuousAt).continuousWithinAt
      exact (h1.inv₀ (fun s hs => hzne s hs)).norm
    obtain ⟨x, hxK, hmax⟩ := hKc.exists_isMaxOn hKne hcont
    refine ⟨‖(riemannZeta x)⁻¹‖, ?_, ?_⟩
    · rw [norm_inv]; exact inv_pos.mpr (norm_pos_iff.mpr (hzne x hxK))
    · intro s h1 h2 h3 h4
      rw [one_div, ← norm_inv]
      apply hmax
      rw [hKdef]
      refine ⟨⟨⟨⟨?_, h1⟩, h2⟩, h3⟩, h4⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      have hsq : ‖s‖ ^ 2 = s.re ^ 2 + s.im ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]; ring
      have hcl : c / Real.log 2 ≤ 3 := by
        rw [div_le_iff₀ (Real.log_pos (by norm_num))]
        nlinarith [hc48, Real.log_two_gt_d9]
      have h5 : |s.re| ≤ 2 := by
        rw [abs_le]
        exact ⟨by linarith [h1, hcl], h2⟩
      nlinarith [hsq, norm_nonneg s, abs_le.mp h5, abs_le.mp h3, sq_nonneg s.re, sq_nonneg s.im]
  obtain ⟨Csm, hCsmpos, hCsmb⟩ := hCsm
  set Cfin : ℝ := max Cbig (Csm + 5) + 6 with hCfindef
  have hCfinpos : 0 < Cfin + 1 := by
    have h1 : Cbig ≤ Cfin + 1 := by
      rw [hCfindef]
      have := le_max_left Cbig (Csm + 5)
      linarith
    linarith [hCbigpos]
  refine ⟨c, Cfin + 1, hcpos, hCfinpos, ?_⟩
  intro σ t hσlo hσhi
  have hLpos : 0 < Real.log (|t| + 2) := Real.log_pos (by linarith [abs_nonneg t])
  have hL1 : 1 ≤ Real.log (|t| + 2) + 1 := by linarith [hLpos]
  rcases le_total 5 |t| with ht | ht
  · have h := hbig σ t ht hσlo hσhi
    refine le_trans h ?_
    have h1 : Cbig ≤ Cfin + 1 := by
      rw [hCfindef]
      have := le_max_left Cbig (Csm + 5)
      linarith
    nlinarith [h1, hLpos, hCbigpos]
  · have h3 : 1 - c / Real.log 2 ≤ σ := by
      have h5 : c / Real.log (|t| + 2) ≤ c / Real.log 2 := by
        rw [div_le_div_iff₀ hLpos (Real.log_pos (by norm_num))]
        have h6 : Real.log 2 ≤ Real.log (|t| + 2) := Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
        nlinarith [hcpos, h6]
      linarith [hσlo, h5]
    have him : |t| ≤ 5 := ht
    have hlog4pi : (2 : ℝ) ≤ Real.log (4 * Real.pi) := by
      have hp : (8 : ℝ) ≤ 4 * Real.pi := by nlinarith [Real.pi_gt_three]
      have h2 : Real.log 8 ≤ Real.log (4 * Real.pi) := Real.log_le_log (by norm_num) hp
      have h3 : (2 : ℝ) ≤ Real.log 8 := by
        have h4 : Real.log 8 = 3 * Real.log 2 := by
          rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow]; norm_num
        rw [h4]; nlinarith [Real.log_two_gt_d9]
      linarith [h2, h3]
    have hcase : 1 / ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ Csm + 5 := by
      by_cases h6 : δ ≤ ‖(((σ : ℂ) + (t : ℂ) * Complex.I)) - 1‖
      · have h7 := hCsmb ((σ : ℂ) + (t : ℂ) * Complex.I) (by simpa using h3) (by simpa using hσhi)
          (by simpa using him) h6
        linarith
      · have h6 : ‖(((σ : ℂ) + (t : ℂ) * Complex.I)) - 1‖ < δ := not_le.mp h6
        have h6le : ‖(((σ : ℂ) + (t : ℂ) * Complex.I)) - 1‖ ≤ 1 / 2 :=
          le_of_lt (lt_of_lt_of_le h6 hδle)
        by_cases h1 : ((σ : ℂ) + (t : ℂ) * Complex.I) = 1
        · have hζ1 : (2 : ℝ) / 3 ≤ ‖riemannZeta (1 : ℂ)‖ := by
            rw [riemannZeta_one, norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
            have hlog : Complex.log (4 * (Real.pi : ℂ)) = ((Real.log (4 * Real.pi) : ℝ) : ℂ) := by
              rw [show (4 * (Real.pi : ℂ)) = ((4 * Real.pi : ℝ) : ℂ) by push_cast; ring]
              exact (Complex.ofReal_log (by positivity)).symm
            have hnum : ((Real.eulerMascheroniConstant : ℂ) - Complex.log (4 * (Real.pi : ℂ)))
                = (((Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) : ℝ) : ℂ) := by
              rw [hlog]; push_cast; ring
            rw [hnum, Complex.norm_real, Real.norm_eq_abs,
              abs_of_neg (by linarith [hlog4pi, Real.eulerMascheroniConstant_lt_two_thirds])]
            linarith [hlog4pi, Real.eulerMascheroniConstant_lt_two_thirds]
          have h2 : 1 / ‖riemannZeta (1 : ℂ)‖ ≤ 3 / 2 := by
            rw [div_le_iff₀ (by linarith [hζ1])]
            linarith
          rw [h1]
          linarith [h2, hCsmpos]
        · have h2 : riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)
              = ((((σ : ℂ) + (t : ℂ) * Complex.I)) - 1)⁻¹
                * riemannZeta₁ (((σ : ℂ) + (t : ℂ) * Complex.I)) :=
            riemannZeta_eq_inv_sub_mul h1
          have hnn : (1 / 2 : ℝ) ≤ ‖riemannZeta₁ (((σ : ℂ) + (t : ℂ) * Complex.I))‖ :=
            hδ₁ _ h6
          have hspos : 0 < ‖(((σ : ℂ) + (t : ℂ) * Complex.I)) - 1‖ :=
            norm_pos_iff.mpr (sub_ne_zero.mpr h1)
          have hlow : 1 ≤ ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
            rw [h2, norm_mul, norm_inv]
            have hinv : (2 : ℝ) ≤ ‖(((σ : ℂ) + (t : ℂ) * Complex.I)) - 1‖⁻¹ := by
              have h8 : (1 / 2 : ℝ)⁻¹ ≤ ‖(((σ : ℂ) + (t : ℂ) * Complex.I)) - 1‖⁻¹ :=
                (inv_le_inv₀ (by norm_num) hspos).mpr h6le
              simpa using h8
            have hmul : (2 : ℝ) * (1 / 2)
                ≤ ‖(((σ : ℂ) + (t : ℂ) * Complex.I)) - 1‖⁻¹
                  * ‖riemannZeta₁ (((σ : ℂ) + (t : ℂ) * Complex.I))‖ :=
              mul_le_mul hinv hnn (by norm_num) (by positivity)
            linarith
          have hfin : 1 / ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 1 := by
            have h9 := one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num) hlow
            simpa using h9
          linarith [hfin, hCsmpos]
    refine le_trans hcase ?_
    have h9 : Csm + 5 ≤ (Cfin + 1) * (Real.log (|t| + 2) + 1) := by
      have h10 : Csm + 5 ≤ Cfin + 1 := by
        rw [hCfindef]
        have := le_max_right Cbig (Csm + 5)
        linarith
      nlinarith [h10, hL1, hCfinpos]
    exact h9
end
end Commons.NumberTheory.Zeta
