import Mathlib
import Submission.Work.FIArea7.UniMollify6
import Submission.Work.FIArea7.UniChain6
import Submission.Work.FIArea7.Section16Detection
import Submission.Work.FIArea7.coprime_gnorm_of_dvd_absDelta
import Submission.Work.FIArea7.norm_omegaDetect_le_one
import Submission.Work.FIArea7.norm_reflSign_le_one
import Submission.Work.FIArea7.absDelta_ne_zero_of_isCoprime
import Submission.Work.FIArea7.quadruple_le

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

set_option maxHeartbeats 4000000

/-! ## 0. Auxiliary vocabulary -/

/-- The common summand of `WUniOmega6Pull6` and `WUniOmega6Pull6Moll`, *without* the logarithmic
factor. -/
def Pull6Base (β : GaussianInt → ℂ) (b e : ℕ) (z1 z2 : GaussianInt) : ℂ :=
  if Work.FIPlan.GaussCoprime z1 z2 ∧ 4 * b * e ∣ Work.FIPlan.absDelta z1 z2 then
    (reflSign z1 z2 : ℂ)
      * omegaDetect (4 * b * e) e z1 z2
      * Complex.I ^ (((z2.re - 1) / 2 : ℤ) - ((z1.re - 1) / 2 : ℤ))
      * (betaPrime β z1 * star (betaPrime β z2))
  else 0

/-! ## 1. Elementary helpers -/

lemma Pull6Base_eq_zero_of_left (β : GaussianInt → ℂ) (b e : ℕ) {z1 z2 : GaussianInt}
    (h : β z1 = 0) : Pull6Base β b e z1 z2 = 0 := by
  by_cases hc : Work.FIPlan.GaussCoprime z1 z2 ∧ 4 * b * e ∣ Work.FIPlan.absDelta z1 z2
  · rw [Pull6Base, if_pos hc]; simp [betaPrime, h]
  · rw [Pull6Base, if_neg hc]

lemma Pull6Base_eq_zero_of_right (β : GaussianInt → ℂ) (b e : ℕ) {z1 z2 : GaussianInt}
    (h : β z2 = 0) : Pull6Base β b e z1 z2 = 0 := by
  by_cases hc : Work.FIPlan.GaussCoprime z1 z2 ∧ 4 * b * e ∣ Work.FIPlan.absDelta z1 z2
  · rw [Pull6Base, if_pos hc]; simp [betaPrime, h]
  · rw [Pull6Base, if_neg hc]

lemma absDelta_comm' (z1 z2 : GaussianInt) :
    Work.FIPlan.absDelta z2 z1 = Work.FIPlan.absDelta z1 z2 := by
  have h : Work.FIPlan.Delta z2 z1 = -Work.FIPlan.Delta z1 z2 := by
    unfold Work.FIPlan.Delta
    rw [show star z2 * z1 = star (star z1 * z2) from by rw [star_mul, star_star], Zsqrtd.im_star]
  unfold Work.FIPlan.absDelta
  rw [h, Int.natAbs_neg]

lemma theta_le_one (Pa : Work.FITop.Params) : Pa.θ ≤ 1 := by
  have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
  have hlog : (1 : ℝ) < Real.log (Pa.x : ℝ) := by
    have h3 : (1 : ℝ) < Real.log 3 := by linarith [Real.log_three_gt_d9]
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hx3
    linarith
  rw [Pa.hθ]
  exact Real.rpow_le_one_of_one_le_of_nonpos (le_of_lt hlog) (by linarith [Pa.hA, Pa.hA'])

lemma one_le_log_add_two {N : ℝ} (hN : 1 ≤ N) : 1 ≤ Real.log (N + 2) := by
  have h3 : (1 : ℝ) < Real.log 3 := by linarith [Real.log_three_gt_d9]
  have h : Real.log 3 ≤ Real.log (N + 2) := Real.log_le_log (by norm_num) (by linarith)
  linarith

private lemma prodLE6 {a b c d e f A B C D E F : ℝ}
    (hA : a ≤ A) (hB : b ≤ B) (hC : c ≤ C) (hD : d ≤ D) (hE : e ≤ E) (hF : f ≤ F)
    (ha : 0 ≤ A) (hb : 0 ≤ B) (hc : 0 ≤ C) (hd : 0 ≤ D) (he : 0 ≤ E) (hf : 0 ≤ F)
    (h0 : 0 ≤ b) (h1 : 0 ≤ c) (h2 : 0 ≤ d) (h3 : 0 ≤ e) (h4 : 0 ≤ f) :
    a * b * c * d * e * f ≤ A * B * C * D * E * F := by
  have h1' : a * b ≤ A * B := mul_le_mul hA hB h0 ha
  have h2' : a * b * c ≤ A * B * C := mul_le_mul h1' hC h1 (mul_nonneg ha hb)
  have h3' : a * b * c * d ≤ A * B * C * D :=
    mul_le_mul h2' hD h2 (mul_nonneg (mul_nonneg ha hb) hc)
  have h4' : a * b * c * d * e ≤ A * B * C * D * E :=
    mul_le_mul h3' hE h3 (mul_nonneg (mul_nonneg (mul_nonneg ha hb) hc) hd)
  exact mul_le_mul h4' hF h4 (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ha hb) hc) hd) he)

lemma sum_norm_sq_le (G : Finset GaussianInt) (β : GaussianInt → ℂ) :
    (∑ z ∈ G, ‖β z‖) ^ 2
      ≤ (((G.filter (fun z => β z ≠ 0)).card : ℕ) : ℝ) * (∑ z ∈ G, ‖β z‖ ^ 2) := by
  have h1 : (∑ z ∈ G, ‖β z‖) = ∑ z ∈ G.filter (fun z => β z ≠ 0), ‖β z‖ := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun z hz => ?_)
    by_cases h : β z ≠ 0
    · simp [h]
    · have h0 : β z = 0 := not_not.mp h
      simp [h0]
  rw [h1]
  have h2 := sq_sum_le_card_mul_sum_sq (s := G.filter (fun z => β z ≠ 0)) (f := fun z => ‖β z‖)
  have h3 : (∑ z ∈ G.filter (fun z => β z ≠ 0), ‖β z‖ ^ 2) ≤ ∑ z ∈ G, ‖β z‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun z _ _ => by positivity)
  calc (∑ z ∈ G.filter (fun z => β z ≠ 0), ‖β z‖) ^ 2
      ≤ (((G.filter (fun z => β z ≠ 0)).card : ℕ) : ℝ)
          * (∑ z ∈ G.filter (fun z => β z ≠ 0), ‖β z‖ ^ 2) := h2
    _ ≤ (((G.filter (fun z => β z ≠ 0)).card : ℕ) : ℝ) * (∑ z ∈ G, ‖β z‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)

/-! ## 3. The per-pair bound -/

lemma norm_term_le {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt} {β : GaussianInt → ℂ}
    (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) {K : ℕ} (hK : 1 ≤ K)
    {b e : ℕ} (hb : 1 ≤ b) (he : 1 ≤ e) (z1 z2 : GaussianInt) :
    ‖Pull6Base β b e z1 z2 *
        (((Work.FITop4.logFac6 z1 z2 : ℝ) : ℂ) - logFac6Series z1 z2 K)‖
      ≤ (if 4 * b * e ∣ Work.FIPlan.absDelta z1 z2 then (1 : ℝ) else 0)
          * (4 * ((1 + Pa.θ) * Pa.N) / ((K : ℝ) * ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)))
          * ‖β z1‖ * ‖β z2‖ := by
  have hMnn : (0 : ℝ) ≤ (1 + Pa.θ) * Pa.N := by
    have h1 : (0 : ℝ) < 1 + Pa.θ := by linarith [Pa.hθ0]
    have h2 : (0 : ℝ) < Pa.N := by linarith [Pa.hN1]
    exact le_of_lt (mul_pos h1 h2)
  have hRHSnn : (0 : ℝ) ≤ (if 4 * b * e ∣ Work.FIPlan.absDelta z1 z2 then (1 : ℝ) else 0)
          * (4 * ((1 + Pa.θ) * Pa.N) / ((K : ℝ) * ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)))
          * ‖β z1‖ * ‖β z2‖ := by
    have hq : (0 : ℝ) ≤ 4 * ((1 + Pa.θ) * Pa.N)
        / ((K : ℝ) * ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)) :=
      div_nonneg (by linarith) (by positivity)
    have hg : (0 : ℝ) ≤ (if 4 * b * e ∣ Work.FIPlan.absDelta z1 z2 then (1 : ℝ) else 0) := by
      by_cases h : 4 * b * e ∣ Work.FIPlan.absDelta z1 z2 <;> simp [h]
    exact mul_nonneg (mul_nonneg (mul_nonneg hg hq) (norm_nonneg _)) (norm_nonneg _)
  rcases eq_or_ne (β z1) 0 with h1 | h1
  · rw [Pull6Base_eq_zero_of_left β b e h1, zero_mul, norm_zero]; exact hRHSnn
  rcases eq_or_ne (β z2) 0 with h2 | h2
  · rw [Pull6Base_eq_zero_of_right β b e h2, zero_mul, norm_zero]; exact hRHSnn
  by_cases hc : Work.FIPlan.GaussCoprime z1 z2 ∧ 4 * b * e ∣ Work.FIPlan.absDelta z1 z2
  · rw [Pull6Base, if_pos hc]
    obtain ⟨hcop, hdiv⟩ := hc
    rw [if_pos hdiv]
    have hgn1 : ((Work.FIPlan.gnorm z1 : ℕ) : ℝ) ≤ (1 + Pa.θ) * Pa.N := (hβ.support h1).2.2.1
    have hgn2 : ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) ≤ (1 + Pa.θ) * Pa.N := (hβ.support h2).2.2.1
    have hDne : Work.FIPlan.Delta z1 z2 ≠ 0 := by
      refine absDelta_ne_zero_of_isCoprime hcop ?_ ?_
      · have h : 0 < |((z1.re : ℤ) : ℝ)| :=
          lt_of_le_of_lt (mul_nonneg (le_of_lt Pa.hϑ0) (Real.sqrt_nonneg Pa.N))
            (hβ.isAxisFree h1).1
        exact_mod_cast (abs_ne_zero.mp (ne_of_gt h))
      · have h : 0 < |((z1.im : ℤ) : ℝ)| :=
          lt_of_le_of_lt (mul_nonneg (le_of_lt Pa.hϑ0) (Real.sqrt_nonneg Pa.N))
            (hβ.isAxisFree h1).2
        exact_mod_cast (abs_ne_zero.mp (ne_of_gt h))
    have hQpos : (0 : ℕ) < 4 * b * e := by positivity
    have hcop1 : Nat.Coprime (Work.FIPlan.gnorm z1) (4 * b * e) :=
      coprime_gnorm_of_dvd_absDelta hQpos (hβ.support h2).1 (hβ.support h1).1
        (hβ.squarefree_gnorm h2) (hβ.squarefree_gnorm h1) hcop.symm
        (by rw [absDelta_comm']; exact hdiv)
    have hcop2 : Nat.Coprime (Work.FIPlan.gnorm z2) (4 * b * e) :=
      coprime_gnorm_of_dvd_absDelta hQpos (hβ.support h1).1 (hβ.support h2).1
        (hβ.squarefree_gnorm h1) (hβ.squarefree_gnorm h2) hcop hdiv
    haveI : NeZero (4 * b * e) := ⟨Nat.pos_iff_ne_zero.mp hQpos⟩
    have homega : ‖omegaDetect (4 * b * e) e z1 z2‖ ≤ 1 :=
      norm_omegaDetect_le_one (4 * b * e) e z1 z2 hcop1 hcop2
    have herr := abs_logFac6_sub_series_le z1 z2 K hK hMnn hgn1 hgn2 hDne
    have hrefl : ‖(reflSign z1 z2 : ℂ)‖ ≤ 1 := norm_reflSign_le_one z1 z2
    have hIpow : ‖Complex.I ^ (((z2.re - 1) / 2 : ℤ) - ((z1.re - 1) / 2 : ℤ))‖ ≤ 1 := by
      rw [norm_zpow, Complex.norm_I, one_zpow]
    have hb1 : ‖betaPrime β z1‖ ≤ ‖β z1‖ := norm_betaPrime_le β z1
    have hb2 : ‖betaPrime β z2‖ ≤ ‖β z2‖ := norm_betaPrime_le β z2
    have hnorm_eq : ‖((reflSign z1 z2 : ℂ) * omegaDetect (4 * b * e) e z1 z2
          * Complex.I ^ (((z2.re - 1) / 2 : ℤ) - ((z1.re - 1) / 2 : ℤ))
          * (betaPrime β z1 * star (betaPrime β z2)))
          * (((Work.FITop4.logFac6 z1 z2 : ℝ) : ℂ) - logFac6Series z1 z2 K)‖
        = ‖(reflSign z1 z2 : ℂ)‖ * ‖omegaDetect (4 * b * e) e z1 z2‖
          * ‖Complex.I ^ (((z2.re - 1) / 2 : ℤ) - ((z1.re - 1) / 2 : ℤ))‖
          * ‖betaPrime β z1‖ * ‖betaPrime β z2‖
          * ‖(((Work.FITop4.logFac6 z1 z2 : ℝ) : ℂ) - logFac6Series z1 z2 K)‖ := by
      simp only [norm_mul, norm_star]
      ring
    rw [hnorm_eq]
    have key := prodLE6 hrefl homega hIpow hb1 hb2 herr
      (by norm_num) (by norm_num) (by norm_num) (norm_nonneg _) (norm_nonneg _)
      (div_nonneg (by linarith) (by positivity))
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    calc ‖(reflSign z1 z2 : ℂ)‖ * ‖omegaDetect (4 * b * e) e z1 z2‖
          * ‖Complex.I ^ (((z2.re - 1) / 2 : ℤ) - ((z1.re - 1) / 2 : ℤ))‖
          * ‖betaPrime β z1‖ * ‖betaPrime β z2‖
          * ‖(((Work.FITop4.logFac6 z1 z2 : ℝ) : ℂ) - logFac6Series z1 z2 K)‖
        ≤ (1:ℝ) * (1:ℝ) * (1:ℝ) * ‖β z1‖ * ‖β z2‖
            * (4 * ((1 + Pa.θ) * Pa.N) / ((K : ℝ) * ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ))) := key
      _ = (1:ℝ) * (4 * ((1 + Pa.θ) * Pa.N)
            / ((K : ℝ) * ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)))
            * ‖β z1‖ * ‖β z2‖ := by ring
  · rw [Pull6Base, if_neg hc, zero_mul, norm_zero]; exact hRHSnn

/-! ## 4. The difference of the two pulled-out sums -/

theorem Pull6_sub_Moll_eq (Pa : Work.FITop.Params) (X : ℕ) (β : GaussianInt → ℂ) (K : ℕ) :
    WUniOmega6Pull6 Pa X β - WUniOmega6Pull6Moll Pa X β K
      = 2 * ∑ b ∈ Finset.Icc 1 (uniB Pa), ∑ e ∈ Finset.Icc 1 X,
            (((ArithmeticFunction.moebius b : ℝ) / (b : ℝ) : ℝ) : ℂ)
              * ∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
                  ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
                    Pull6Base β b e z1 z2
                      * ((Work.FITop4.logFac6 z1 z2 : ℂ) - logFac6Series z1 z2 K) := by
  have hb1 : ∀ (b e : ℕ) (z1 z2 : GaussianInt),
      (if Work.FIPlan.GaussCoprime z1 z2 ∧ 4 * b * e ∣ Work.FIPlan.absDelta z1 z2 then
          (reflSign z1 z2 : ℂ) * omegaDetect (4 * b * e) e z1 z2
            * Complex.I ^ (((z2.re - 1) / 2 : ℤ) - ((z1.re - 1) / 2 : ℤ))
            * (betaPrime β z1 * star (betaPrime β z2))
            * (Work.FITop4.logFac6 z1 z2 : ℂ) else 0)
        = Pull6Base β b e z1 z2 * (Work.FITop4.logFac6 z1 z2 : ℂ) := by
    intro b e z1 z2
    unfold Pull6Base
    by_cases hc : Work.FIPlan.GaussCoprime z1 z2 ∧ 4 * b * e ∣ Work.FIPlan.absDelta z1 z2
    · simp only [if_pos hc]
    · simp only [if_neg hc, zero_mul]
  have hb2 : ∀ (b e : ℕ) (z1 z2 : GaussianInt),
      (if Work.FIPlan.GaussCoprime z1 z2 ∧ 4 * b * e ∣ Work.FIPlan.absDelta z1 z2 then
          (reflSign z1 z2 : ℂ) * omegaDetect (4 * b * e) e z1 z2
            * Complex.I ^ (((z2.re - 1) / 2 : ℤ) - ((z1.re - 1) / 2 : ℤ))
            * (betaPrime β z1 * star (betaPrime β z2))
            * logFac6Series z1 z2 K else 0)
        = Pull6Base β b e z1 z2 * logFac6Series z1 z2 K := by
    intro b e z1 z2
    unfold Pull6Base
    by_cases hc : Work.FIPlan.GaussCoprime z1 z2 ∧ 4 * b * e ∣ Work.FIPlan.absDelta z1 z2
    · simp only [if_pos hc]
    · simp only [if_neg hc, zero_mul]
  have hin1 : (∑ b ∈ Finset.Icc 1 (uniB Pa), ∑ e ∈ Finset.Icc 1 X,
            (((ArithmeticFunction.moebius b : ℝ) / (b : ℝ) : ℝ) : ℂ)
              * ∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
                  ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
                    (if Work.FIPlan.GaussCoprime z1 z2 ∧ 4 * b * e ∣ Work.FIPlan.absDelta z1 z2 then
                      (reflSign z1 z2 : ℂ) * omegaDetect (4 * b * e) e z1 z2
                        * Complex.I ^ (((z2.re - 1) / 2 : ℤ) - ((z1.re - 1) / 2 : ℤ))
                        * (betaPrime β z1 * star (betaPrime β z2))
                        * (Work.FITop4.logFac6 z1 z2 : ℂ) else 0))
      = ∑ b ∈ Finset.Icc 1 (uniB Pa), ∑ e ∈ Finset.Icc 1 X,
            (((ArithmeticFunction.moebius b : ℝ) / (b : ℝ) : ℝ) : ℂ)
              * ∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
                  ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
                    Pull6Base β b e z1 z2 * (Work.FITop4.logFac6 z1 z2 : ℂ) := by
    refine Finset.sum_congr rfl (fun b _ => ?_)
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [show (∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
                ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
                (if Work.FIPlan.GaussCoprime z1 z2 ∧ 4 * b * e ∣ Work.FIPlan.absDelta z1 z2 then
                  (reflSign z1 z2 : ℂ) * omegaDetect (4 * b * e) e z1 z2
                    * Complex.I ^ (((z2.re - 1) / 2 : ℤ) - ((z1.re - 1) / 2 : ℤ))
                    * (betaPrime β z1 * star (betaPrime β z2))
                    * (Work.FITop4.logFac6 z1 z2 : ℂ) else 0))
          = ∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
              ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
                Pull6Base β b e z1 z2 * (Work.FITop4.logFac6 z1 z2 : ℂ)
        from Finset.sum_congr rfl (fun z1 _ => Finset.sum_congr rfl (fun z2 _ => hb1 b e z1 z2))]
  have hin2 : (∑ b ∈ Finset.Icc 1 (uniB Pa), ∑ e ∈ Finset.Icc 1 X,
            (((ArithmeticFunction.moebius b : ℝ) / (b : ℝ) : ℝ) : ℂ)
              * ∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
                  ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
                    (if Work.FIPlan.GaussCoprime z1 z2 ∧ 4 * b * e ∣ Work.FIPlan.absDelta z1 z2 then
                      (reflSign z1 z2 : ℂ) * omegaDetect (4 * b * e) e z1 z2
                        * Complex.I ^ (((z2.re - 1) / 2 : ℤ) - ((z1.re - 1) / 2 : ℤ))
                        * (betaPrime β z1 * star (betaPrime β z2))
                        * logFac6Series z1 z2 K else 0))
      = ∑ b ∈ Finset.Icc 1 (uniB Pa), ∑ e ∈ Finset.Icc 1 X,
            (((ArithmeticFunction.moebius b : ℝ) / (b : ℝ) : ℝ) : ℂ)
              * ∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
                  ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
                    Pull6Base β b e z1 z2 * logFac6Series z1 z2 K := by
    refine Finset.sum_congr rfl (fun b _ => ?_)
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [show (∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
                ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
                (if Work.FIPlan.GaussCoprime z1 z2 ∧ 4 * b * e ∣ Work.FIPlan.absDelta z1 z2 then
                  (reflSign z1 z2 : ℂ) * omegaDetect (4 * b * e) e z1 z2
                    * Complex.I ^ (((z2.re - 1) / 2 : ℤ) - ((z1.re - 1) / 2 : ℤ))
                    * (betaPrime β z1 * star (betaPrime β z2))
                    * logFac6Series z1 z2 K else 0))
          = ∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
              ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
                Pull6Base β b e z1 z2 * logFac6Series z1 z2 K
        from Finset.sum_congr rfl (fun z1 _ => Finset.sum_congr rfl (fun z2 _ => hb2 b e z1 z2))]
  have hP1 : WUniOmega6Pull6 Pa X β
      = 2 * ∑ b ∈ Finset.Icc 1 (uniB Pa), ∑ e ∈ Finset.Icc 1 X,
            (((ArithmeticFunction.moebius b : ℝ) / (b : ℝ) : ℝ) : ℂ)
              * ∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
                  ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
                    Pull6Base β b e z1 z2 * (Work.FITop4.logFac6 z1 z2 : ℂ) := by
    unfold WUniOmega6Pull6
    exact congrArg (fun x => 2 * x) hin1
  have hP2 : WUniOmega6Pull6Moll Pa X β K
      = 2 * ∑ b ∈ Finset.Icc 1 (uniB Pa), ∑ e ∈ Finset.Icc 1 X,
            (((ArithmeticFunction.moebius b : ℝ) / (b : ℝ) : ℝ) : ℂ)
              * ∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
                  ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
                    Pull6Base β b e z1 z2 * logFac6Series z1 z2 K := by
    unfold WUniOmega6Pull6Moll
    exact congrArg (fun x => 2 * x) hin2
  have hinner : ∀ b e : ℕ,
      (∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
          ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
            Pull6Base β b e z1 z2 * (Work.FITop4.logFac6 z1 z2 : ℂ))
        - (∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
            ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
              Pull6Base β b e z1 z2 * logFac6Series z1 z2 K)
      = ∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
          ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
            Pull6Base β b e z1 z2
              * ((Work.FITop4.logFac6 z1 z2 : ℂ) - logFac6Series z1 z2 K) := by
    intro b e
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun z1 _ => ?_)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun z2 _ => ?_)
    rw [← mul_sub]
  have hlin' : (∑ b ∈ Finset.Icc 1 (uniB Pa), ∑ e ∈ Finset.Icc 1 X,
            (((ArithmeticFunction.moebius b : ℝ) / (b : ℝ) : ℝ) : ℂ)
              * ∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
                  ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
                    Pull6Base β b e z1 z2 * (Work.FITop4.logFac6 z1 z2 : ℂ))
      - (∑ b ∈ Finset.Icc 1 (uniB Pa), ∑ e ∈ Finset.Icc 1 X,
            (((ArithmeticFunction.moebius b : ℝ) / (b : ℝ) : ℝ) : ℂ)
              * ∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
                  ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
                    Pull6Base β b e z1 z2 * logFac6Series z1 z2 K)
      = ∑ b ∈ Finset.Icc 1 (uniB Pa), ∑ e ∈ Finset.Icc 1 X,
            (((ArithmeticFunction.moebius b : ℝ) / (b : ℝ) : ℝ) : ℂ)
              * ∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
                  ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
                    Pull6Base β b e z1 z2
                      * ((Work.FITop4.logFac6 z1 z2 : ℂ) - logFac6Series z1 z2 K) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [← mul_sub, hinner b e]
  rw [hP1, hP2]
  rw [← mul_sub]
  exact congrArg (fun x => 2 * x) hlin'

/-! ## 5. The main bound -/

end

end Work.FIArea7
