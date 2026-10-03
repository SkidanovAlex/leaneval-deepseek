import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Pert.Setup
import Submission.Work.Pert.Basic
import Submission.Work.Pert.dev_base_v3
import Submission.Work.Pert.Ksub2.walk_explicit
import Submission.Work.Pert.Phi_dev_gate_lin_v5
import Submission.Work.Pert.deriv_sub_id_le_on_cone
import Submission.Work.Pert.strip_high
import Submission.Work.Pert.V5.Basics
import Submission.Work.Pert.V5.horiz_dev_le_of_margin
import Submission.Work.Pert.V5.horiz_dev_le_gen
import Submission.Work.Pert.V5.horiz_dev_le_clear
import Submission.Work.Pert.liftF_sub_translation_le
import Submission.Work.PertCrux.norm_tauC_sub_tau0_le
import Submission.Work.Pert.liftF_defect_le_tauC
import Submission.Work.Pert.Pin.back_two_clear
import Submission.Work.Pert.Pin.rr_mul_Xi_ge
import Submission.Work.Pert.Pin.arith_strip_v4

namespace Work.Pert.Pin

open Set Metric

set_option maxHeartbeats 4000000

/-- Chaining `‖a - b‖ ≤ A`, `‖b - c‖ ≤ B` into `‖a - c‖ ≤ A + B`. -/
private lemma chain_add {a b c : ℂ} {A B : ℝ} (h1 : ‖a - b‖ ≤ A) (h2 : ‖b - c‖ ≤ B) :
    ‖a - c‖ ≤ A + B := by
  have h := norm_add_le (a - b) (b - c)
  have he : (a - b) + (b - c) = a - c := by ring
  rw [he] at h
  linarith

/-- The `b₁`-margin at a point of the horizontal line at height `t`. -/
private lemma mgA_line (Ξ : ℝ) (α : ℂ) (t ξ : ℝ) :
    Work.Pert.V5.mgA Ξ α ((ξ : ℂ) + (t : ℂ) * Complex.I) =
      ξ - Ξ + (1 / α).re + |t + (1 / α).im| := by
  simp only [Work.Pert.V5.mgA, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_I_re, Complex.mul_I_im, mul_zero, add_zero, zero_add, neg_zero]

/-- The `b₂`-margin at a point of the horizontal line at height `t`. -/
private lemma mgB_line (Ξ : ℝ) (t ξ : ℝ) :
    Work.Pert.V5.mgB Ξ ((ξ : ℂ) + (t : ℂ) * Complex.I) = |t| - Ξ - ξ := by
  simp only [Work.Pert.V5.mgB, Complex.add_im, Complex.ofReal_im, Complex.mul_I_im,
    Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, mul_zero, add_zero, zero_add, neg_zero]

/-- **Logarithm bound for the clearing tool.**  If the leg length `ℓ` is at most
`16 (M + 2 + Ξ)`, then `1 + log (2 + ℓ)` is dominated by `9` times the target's logarithmic
factor `1 + log (2 + M) + log (2 + y)`. -/
private lemma clear_log_le {M Ξ ℓ y : ℝ} (hM : 2 ^ 10 ≤ M) (hΞ : 0 < Ξ) (hΞM : Ξ ≤ M)
    (hℓ : ℓ ≤ 16 * (M + 2 + Ξ)) (hℓnn : 0 ≤ ℓ) (hy : 0 ≤ y) :
    1 + Real.log (2 + ℓ) ≤ 9 * (1 + Real.log (2 + M) + Real.log (2 + y)) := by
  have hpos : (0 : ℝ) < M + 2 + Ξ := by linarith
  have h1 : (2 : ℝ) + ℓ ≤ 2 ^ 6 * (M + 2 + Ξ) := by
    have h2 : (2 : ℝ) ≤ 2 ^ 5 * (M + 2 + Ξ) := by nlinarith [hM, hΞ]
    nlinarith [hℓ, h2]
  have h3 : (0 : ℝ) < 2 + ℓ := by linarith
  have h4 : Real.log (2 + ℓ) ≤ Real.log ((2 : ℝ) ^ 6 * (M + 2 + Ξ)) :=
    Real.log_le_log h3 h1
  have h5 : Real.log ((2 : ℝ) ^ 6 * (M + 2 + Ξ))
      = Real.log ((2 : ℝ) ^ 6) + Real.log (M + 2 + Ξ) :=
    Real.log_mul (by norm_num) (ne_of_gt hpos)
  have h6 : Real.log ((2 : ℝ) ^ 6) ≤ 6 := by
    have h : Real.log ((2 : ℝ) ^ 6) = 6 * Real.log 2 := by
      rw [Real.log_pow]
      norm_num
    have h7 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
    linarith
  have h7 : M + 2 + Ξ ≤ 2 * (M + 2) := by linarith
  have h8 : Real.log (M + 2 + Ξ) ≤ Real.log (2 * (M + 2)) :=
    Real.log_le_log (by linarith) h7
  have h9 : Real.log (2 * (M + 2)) = Real.log 2 + Real.log (M + 2) :=
    Real.log_mul (by norm_num) (by linarith)
  have h10 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
  have h11 : Real.log (M + 2) = Real.log (2 + M) := by rw [add_comm]
  have h12 : (0 : ℝ) ≤ Real.log (2 + y) := Real.log_nonneg (by linarith)
  have h13 : (0 : ℝ) ≤ Real.log (2 + M) := Real.log_nonneg (by linarith)
  rw [h5] at h4
  linarith

/-- **The defect term of the clearing tool is affordable.** -/
private lemma clear_defect_le {Ξ rr ℓ Mf : ℝ} (hΞ : 0 < Ξ) (hrr : 0 < rr)
    (hℓnn : 0 ≤ ℓ) (hMf : 0 ≤ Mf)
    (hlog : 1 + Real.log (2 + ℓ) ≤ 9 * Mf) :
    2 ^ 24 * (1 + 1 / rr) * (1 + Real.log (2 + ℓ))
      ≤ 2 ^ 43 * (1 + Ξ + 1 / Ξ + 1 / rr) * Mf := by
  have hS1 : (1 : ℝ) ≤ 1 + Ξ + 1 / Ξ + 1 / rr := by
    have h1 : (0 : ℝ) ≤ 1 / Ξ := by positivity
    have h2 : (0 : ℝ) ≤ 1 / rr := by positivity
    linarith
  have h2 : 1 + 1 / rr ≤ 2 * (1 + Ξ + 1 / Ξ + 1 / rr) := by
    have h1 : (0 : ℝ) ≤ 1 / Ξ := by positivity
    have h2 : (0 : ℝ) ≤ 1 / rr := by positivity
    linarith
  have hlogpos : (0 : ℝ) ≤ 1 + Real.log (2 + ℓ) := by
    have h : (0 : ℝ) ≤ Real.log (2 + ℓ) := Real.log_nonneg (by linarith)
    linarith
  have h3 : (9 : ℝ) * 2 ^ 25 ≤ 2 ^ 43 := by norm_num
  have h4 : 2 ^ 24 * (1 + 1 / rr) * (1 + Real.log (2 + ℓ))
      ≤ 2 ^ 24 * (2 * (1 + Ξ + 1 / Ξ + 1 / rr)) * (9 * Mf) := by
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left h2 (by norm_num)
    · exact hlog
    · exact hlogpos
    · positivity
  have h5 : 2 ^ 24 * (2 * (1 + Ξ + 1 / Ξ + 1 / rr)) * (9 * Mf)
      = 9 * 2 ^ 25 * (1 + Ξ + 1 / Ξ + 1 / rr) * Mf := by ring
  have h6 : (9 : ℝ) * 2 ^ 25 * (1 + Ξ + 1 / Ξ + 1 / rr) * Mf
      ≤ 2 ^ 43 * (1 + Ξ + 1 / Ξ + 1 / rr) * Mf := by
    apply mul_le_mul_of_nonneg_right _ hMf
    apply mul_le_mul_of_nonneg_right h3
    exact le_trans zero_le_one hS1
  linarith [h4, h5.le, h5.ge, h6]

/-- **The defect term of the general tool is affordable**, provided `Ξ < 2^11` and (the key
consistency fact) `rr Ξ ≥ 1/64`. -/
private lemma gen_defect_le {Ξ rr L Mf : ℝ} (hΞ : 0 < Ξ) (hrr : 0 < rr)
    (hXi : Ξ < 2 ^ 11) (hkey : 1 / 64 ≤ rr * Ξ) (hL : 0 ≤ L) (hMf : 0 ≤ Mf) (hLMf : L ≤ Mf) :
    2 ^ 24 * (1 + 1 / rr) * (1 + Ξ) * (1 + 1 / Ξ) * L
      ≤ 2 ^ 43 * (1 + Ξ + 1 / Ξ + 1 / rr) * Mf := by
  have hS1 : (1 : ℝ) ≤ 1 + Ξ + 1 / Ξ + 1 / rr := by
    have h1 : (0 : ℝ) ≤ 1 / Ξ := by positivity
    have h2 : (0 : ℝ) ≤ 1 / rr := by positivity
    linarith
  have hSnn : (0 : ℝ) ≤ 1 + Ξ + 1 / Ξ + 1 / rr := le_trans zero_le_one hS1
  have hSΞ : Ξ ≤ 1 + Ξ + 1 / Ξ + 1 / rr := by
    have h2 : (0 : ℝ) ≤ 1 / Ξ + 1 / rr := by positivity
    linarith
  have hrr64 : 1 / rr ≤ 64 * Ξ := by
    rw [div_le_iff₀ hrr]
    nlinarith [hkey]
  -- ## the `Ξ + 2` part
  have hB1 : (1 + 1 / rr) * (Ξ + 2) ≤ 2 ^ 18 * (1 + Ξ + 1 / Ξ + 1 / rr) := by
    have h1 : (1 + 1 / rr) * (Ξ + 2) ≤ (1 + 64 * Ξ) * (Ξ + 2) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have h2 : (1 + 64 * Ξ) * (Ξ + 2) ≤ 2 ^ 18 * (1 + Ξ + 1 / Ξ + 1 / rr) := by
      have h3 : (1 + 64 * Ξ) * (Ξ + 2) = 64 * Ξ ^ 2 + 129 * Ξ + 2 := by ring
      rw [h3]
      have a : 64 * Ξ ^ 2 ≤ 64 * Ξ * (1 + Ξ + 1 / Ξ + 1 / rr) := by
        nlinarith [hSΞ, hΞ]
      have b : 129 * Ξ ≤ 129 * (1 + Ξ + 1 / Ξ + 1 / rr) := by linarith [hSΞ]
      have c : (2 : ℝ) ≤ 2 * (1 + Ξ + 1 / Ξ + 1 / rr) := by linarith [hS1]
      have d : 64 * Ξ + 131 ≤ 2 ^ 18 := by nlinarith [hXi]
      have h4 : 64 * Ξ ^ 2 + 129 * Ξ + 2
          ≤ 64 * Ξ * (1 + Ξ + 1 / Ξ + 1 / rr)
            + 129 * (1 + Ξ + 1 / Ξ + 1 / rr) + 2 * (1 + Ξ + 1 / Ξ + 1 / rr) := by
        linarith [a, b, c]
      have h5 : 64 * Ξ * (1 + Ξ + 1 / Ξ + 1 / rr)
            + 129 * (1 + Ξ + 1 / Ξ + 1 / rr) + 2 * (1 + Ξ + 1 / Ξ + 1 / rr)
          = (64 * Ξ + 131) * (1 + Ξ + 1 / Ξ + 1 / rr) := by ring
      have h6 : (64 * Ξ + 131) * (1 + Ξ + 1 / Ξ + 1 / rr)
          ≤ 2 ^ 18 * (1 + Ξ + 1 / Ξ + 1 / rr) :=
        mul_le_mul_of_nonneg_right d hSnn
      linarith [h4, h5.le, h5.ge, h6]
    linarith [h1, h2]
  -- ## the `1 / Ξ` part
  have hB2 : (1 + 1 / rr) / Ξ ≤ 65 * (1 + Ξ + 1 / Ξ + 1 / rr) := by
    have hr : (1 + 1 / rr) ≤ 1 + 64 * Ξ := by linarith
    have h7 : Ξ + 1 ≤ Ξ * (1 + Ξ + 1 / Ξ + 1 / rr) := by
      have e : Ξ * (1 + Ξ + 1 / Ξ + 1 / rr) = Ξ + Ξ * Ξ + Ξ * (1 / Ξ) + Ξ * (1 / rr) := by ring
      have h8 : Ξ * (1 / Ξ) = 1 := by field_simp
      have h9 : (0 : ℝ) ≤ Ξ * Ξ + Ξ * (1 / rr) := by positivity
      linarith [e, h8, h9]
    have h6 : 1 + 64 * Ξ ≤ 65 * (Ξ * (1 + Ξ + 1 / Ξ + 1 / rr)) := by nlinarith [h7]
    rw [div_le_iff₀ hΞ]
    nlinarith [hr, h6]
  -- ## assembly
  have hB : (1 + 1 / rr) * (Ξ + 2 + 1 / Ξ) ≤ 2 ^ 19 * (1 + Ξ + 1 / Ξ + 1 / rr) := by
    have he : (1 + 1 / rr) * (Ξ + 2 + 1 / Ξ) = (1 + 1 / rr) * (Ξ + 2) + (1 + 1 / rr) / Ξ := by
      ring
    rw [he]
    have h19 : (2 : ℝ) ^ 18 + 65 ≤ 2 ^ 19 := by norm_num
    nlinarith [hB1, hB2, hSnn, h19]
  have hkey2 : (1 + Ξ) * (1 + 1 / Ξ) = Ξ + 2 + 1 / Ξ := by
    field_simp
    ring
  have h24 : (2 : ℝ) ^ 24 * 2 ^ 19 = 2 ^ 43 := by norm_num
  have hm : 2 ^ 24 * (1 + 1 / rr) * (1 + Ξ) * (1 + 1 / Ξ) * L
      ≤ 2 ^ 24 * (2 ^ 19 * (1 + Ξ + 1 / Ξ + 1 / rr)) * L := by
    have he : 2 ^ 24 * (1 + 1 / rr) * (1 + Ξ) * (1 + 1 / Ξ) * L
        = 2 ^ 24 * ((1 + 1 / rr) * (Ξ + 2 + 1 / Ξ)) * L := by
      linear_combination (2 ^ 24 * (1 + 1 / rr) * L) * hkey2
    rw [he]
    apply mul_le_mul_of_nonneg_right _ hL
    exact mul_le_mul_of_nonneg_left hB (by norm_num)
  calc 2 ^ 24 * (1 + 1 / rr) * (1 + Ξ) * (1 + 1 / Ξ) * L
      ≤ 2 ^ 24 * (2 ^ 19 * (1 + Ξ + 1 / Ξ + 1 / rr)) * L := hm
    _ = 2 ^ 43 * (1 + Ξ + 1 / Ξ + 1 / rr) * L := by rw [← h24]; ring
    _ ≤ 2 ^ 43 * (1 + Ξ + 1 / Ξ + 1 / rr) * Mf := by
        apply mul_le_mul_of_nonneg_left hLMf
        have : (0 : ℝ) ≤ 2 ^ 43 * (1 + Ξ + 1 / Ξ + 1 / rr) := by positivity
        exact this

theorem Phi_dev_gate_strip_v2 {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hF : MandelDim.FatouStatement)
    {Ξ rr M Kp Rde C₁ C₂ : ℝ} {α σ : ℂ} {u Φm : ℂ → ℂ} {z₀ : ℂ}
    (hΞ : 0 < Ξ) (hrr : 0 < rr) (hM : 2 ^ 10 ≤ M) (hKp : 0 ≤ Kp)
    (hRde : 0 < Rde) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂)
    (hpincl : Ξ + 2 * Kp * (1 + Real.log (2 + M)) + Real.sqrt 2 * Rde ≤ M)
    (hInF1 : MandelDim.InF1 α) (hα : ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ)))
    (hQAdm : MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))))
    (hσ : σ ≠ 0) (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hu : DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr))
    (hu2 : ∀ z ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2)
    (hτQ : ∀ z ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α z ∈ Metric.ball (0 : ℂ) rr)
    (hNT : MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm Ξ α))
    (hΦm : MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φm (Work.Pert.Qm Ξ α))
    (hDE : ∀ (Φ v : ℂ → ℂ) (z : ℂ) (R : ℝ), Rde ≤ R →
      DifferentiableOn ℂ Φ (Metric.ball z R) → Set.InjOn Φ (Metric.ball z R) →
      DifferentiableOn ℂ v (Metric.ball z R) → (∀ w ∈ Metric.ball z R, ‖v w - 1‖ < 1 / 4) →
      (∀ w ∈ Metric.ball z R, w + v w ∈ Metric.ball z R → Φ (w + v w) = Φ w + 1) →
      ‖deriv Φ z - 1 / v z‖ ≤ C₁ * (1 / R ^ 2 + ‖deriv v z‖) ∧
      ‖deriv Φ z - 1 / v z‖ ≤ C₂ / R)
    (hz₀ : z₀ ∈ Work.Pert.Qm Ξ α)
    (hpin : Φm z₀ = (((-M : ℝ)) : ℂ))
    (hpinbd : ‖z₀ + (((M : ℝ)) : ℂ)‖ ≤ Kp * (1 + Real.log (2 + M))) :
    ∃ C : ℝ, 0 < C ∧ C ≤ (Kp + 1 + C₂) * 2 ^ 44 * (1 + Ξ + 1 / Ξ + 1 / rr) ∧
      ∀ z : ℂ, z ∈ Work.Pert.Qm Ξ α → -(Ξ + 1) ≤ z.re → z.re ≤ 2 →
        Ξ + 2 + Real.sqrt 2 * Rde ≤ |z.im| →
        ‖Φm z - z‖ ≤ C * (1 + Real.log (2 + M) + Real.log (2 + |z.im|)) + |z.im| / 20 := by
  refine ⟨(Kp + 1 + C₂) * 2 ^ 44 * (1 + Ξ + 1 / Ξ + 1 / rr), ?_, le_rfl, ?_⟩
  · have h1 : (0 : ℝ) < Kp + 1 + C₂ := by linarith
    have h2 : (0 : ℝ) < 2 ^ 44 := by norm_num
    have h3 : (0 : ℝ) < 1 + Ξ + 1 / Ξ + 1 / rr := by
      have h4 : 0 < 1 / Ξ := by positivity
      have h5 : 0 < 1 / rr := by positivity
      linarith
    exact mul_pos (mul_pos h1 h2) h3
  · intro z hz hzlo hzhi htim
    -- ## 0. elementary consequences of `hpincl`
    have hLpos : (0 : ℝ) < 1 + Real.log (2 + M) := by
      have h : (0 : ℝ) ≤ Real.log (2 + M) := Real.log_nonneg (by linarith)
      linarith
    have hKLnn : (0 : ℝ) ≤ Kp * (1 + Real.log (2 + M)) := mul_nonneg hKp hLpos.le
    have hs2nn : (0 : ℝ) ≤ Real.sqrt 2 * Rde := mul_nonneg (Real.sqrt_nonneg 2) hRde.le
    have hΞM : Ξ ≤ M := by linarith [hpincl, hΞ.le, hKLnn, hs2nn]
    have hs2M : Real.sqrt 2 * Rde ≤ M := by linarith [hpincl, hΞ.le, hKLnn, hs2nn]
    have hKpLh : Kp * (1 + Real.log (2 + M)) ≤ M / 2 := by linarith [hpincl, hΞ.le, hs2nn]
    have hsq2pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hA : 18 * M + 2 * Ξ + 2 ^ 10 ≤ (1 / α).re :=
      Work.Pert.band_Qm_key_bound hΞ hM hInF1 hα
    -- ## 1. the pin's coordinates and margins
    have hpinre : |z₀.re + M| ≤ Kp * (1 + Real.log (2 + M)) := by
      have h := Complex.abs_re_le_norm (z₀ + (((M : ℝ)) : ℂ))
      simp only [Complex.add_re, Complex.ofReal_re] at h
      exact le_trans h hpinbd
    have hpinim : |z₀.im| ≤ Kp * (1 + Real.log (2 + M)) := by
      have h := Complex.abs_im_le_norm (z₀ + (((M : ℝ)) : ℂ))
      simp only [Complex.add_im, Complex.ofReal_im, add_zero] at h
      exact le_trans h hpinbd
    have hpinre_lb : -M - Kp * (1 + Real.log (2 + M)) ≤ z₀.re := by
      have h := (abs_le.mp hpinre).1; linarith
    have hpinre_ub : z₀.re ≤ -M + Kp * (1 + Real.log (2 + M)) := by
      have h := (abs_le.mp hpinre).2; linarith
    have hmargA_pin : 16 * M ≤ Work.Pert.V5.mgA Ξ α z₀ := by
      have h1 : (0 : ℝ) ≤ |z₀.im + (1 / α).im| := abs_nonneg _
      simp only [Work.Pert.V5.mgA]
      linarith [hpinre_lb, hA, h1, hKpLh, hΞ.le, hM]
    have hmargB_pin : Real.sqrt 2 * Rde ≤ Work.Pert.V5.mgB Ξ z₀ := by
      have h1 : (0 : ℝ) ≤ |z₀.im| := abs_nonneg _
      simp only [Work.Pert.V5.mgB]
      linarith [hpinre_ub, h1, hpincl, hΞ.le]
    have hpinbig : max (Real.sqrt 2 * Rde) 1 + 17 / 8 < Work.Pert.V5.mgA Ξ α z₀ := by
      have h : max (Real.sqrt 2 * Rde) 1 ≤ M + 1 :=
        max_le (by linarith [hs2M]) (by linarith [hM])
      linarith [hmargA_pin, hM]
    -- ## 2. the margins of `z`
    have hmargA_z : 16 * M ≤ Work.Pert.V5.mgA Ξ α z := by
      have h1 : (0 : ℝ) ≤ |z.im + (1 / α).im| := abs_nonneg _
      simp only [Work.Pert.V5.mgA]
      linarith [hzlo, hA, h1, hM]
    have hmargB_z : Real.sqrt 2 * Rde ≤ Work.Pert.V5.mgB Ξ z := by
      simp only [Work.Pert.V5.mgB]
      linarith [htim, hzhi]
    have hzbig : max (Real.sqrt 2 * Rde) 1 + 17 / 8 < Work.Pert.V5.mgA Ξ α z := by
      have h : max (Real.sqrt 2 * Rde) 1 ≤ M + 1 :=
        max_le (by linarith [hs2M]) (by linarith [hM])
      linarith [hmargA_z, hM]
    -- ## 3. the two two-step backward iterates
    obtain ⟨z₂, hz₂Q, hz₂F, hz₂ball, hz₂clr, hz₂im, hz₂re, hz₂dev⟩ :=
      back_two_clear_fixed hΞ hM hInF1 hα hQAdm hRde hNT hΦm hz hzbig hmargB_z
    obtain ⟨ζ₂, hζ₂Q, hζ₂F, hζ₂ball, hζ₂clr, hζ₂im, hζ₂re, hζ₂dev⟩ :=
      back_two_clear_fixed hΞ hM hInF1 hα hQAdm hRde hNT hΦm hz₀ hpinbig hmargB_pin
    have hz₂re_lb : z.re - 2 - 2 / 32 ≤ z₂.re := by
      have h := (abs_le.mp hz₂re).1
      simp only [Complex.add_re] at h
      norm_num at h
      linarith
    have hz₂re_ub : z₂.re ≤ z.re - 2 + 2 / 32 := by
      have h := (abs_le.mp hz₂re).2
      simp only [Complex.add_re] at h
      norm_num at h
      linarith
    have hζ₂re_lb : z₀.re - 2 - 2 / 32 ≤ ζ₂.re := by
      have h := (abs_le.mp hζ₂re).1
      simp only [Complex.add_re] at h
      norm_num at h
      linarith
    have hζ₂re_ub : ζ₂.re ≤ z₀.re - 2 + 2 / 32 := by
      have h := (abs_le.mp hζ₂re).2
      simp only [Complex.add_re] at h
      norm_num at h
      linarith
    -- ## 4. the comparison abscissa
    set xv : ℝ := min ζ₂.re (-(Ξ + 2 ^ 10)) with hxvdef
    have hxv_le : xv ≤ -(Ξ + 2 ^ 10) := min_le_right _ _
    have hxv_leζ : xv ≤ ζ₂.re := min_le_left _ _
    have hxv_ge : -(Ξ + 2 ^ 10 + 2 * M) ≤ xv := by
      have h2 : -(Ξ + 2 ^ 10 + 2 * M) ≤ ζ₂.re := by
        have h3 : -(M + M / 2 + 2 + 2 / 32) ≤ ζ₂.re := by
          have h4 := hpinre_lb
          linarith [hKpLh]
        linarith [hΞM, hM, h3]
      exact le_min h2 (by linarith [hΞ, hM])
    have hxv_le_z₂ : xv ≤ z₂.re := by
      have h3 : -(Ξ + 2 ^ 10) ≤ z₂.re := by
        have h4 := hz₂re_lb
        linarith [hzlo]
      linarith [hxv_le]
    -- ## 5. the radius scale `κ`
    set κ : ℝ := max (Real.sqrt 2 * Rde) 1 with hκdef
    have hκpos : 0 < κ := lt_max_iff.mpr (Or.inl (mul_pos hsq2pos hRde))
    have hκlo : Real.sqrt 2 * Rde ≤ κ := by rw [hκdef]; exact le_max_left _ _
    have hκge1 : 1 ≤ κ := by rw [hκdef]; exact le_max_right _ _
    have hκRde : Rde ≤ κ / Real.sqrt 2 := by
      rcases le_total 1 (Real.sqrt 2 * Rde) with h | h
      · have hκeq : κ = Real.sqrt 2 * Rde := by rw [hκdef]; exact max_eq_left h
        rw [hκeq, le_div_iff₀ hsq2pos]
        linarith
      · have hκeq : κ = 1 := by rw [hκdef]; exact max_eq_right h
        rw [hκeq, le_div_iff₀ hsq2pos]
        nlinarith [h, hsq2pos, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    have hκC : C₂ * Real.sqrt 2 / κ ≤ 2 * C₂ := by
      rcases le_total 1 (Real.sqrt 2 * Rde) with h | h
      · have hκeq : κ = Real.sqrt 2 * Rde := by rw [hκdef]; exact max_eq_left h
        rw [hκeq]
        have hprod : (0 : ℝ) < Real.sqrt 2 * Rde := mul_pos hsq2pos hRde
        rw [div_le_iff₀ hprod]
        have hsq1 : (1 : ℝ) ≤ Real.sqrt 2 := by
          nlinarith [hsq2pos, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
        calc C₂ * Real.sqrt 2 = C₂ * Real.sqrt 2 * 1 := by ring
          _ ≤ C₂ * Real.sqrt 2 * (2 * Rde) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              have hsq2le : Real.sqrt 2 ≤ 2 := by
                nlinarith [hsq2pos, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
              nlinarith [h, hsq2le, hsq1, hRde.le]
          _ = 2 * C₂ * (Real.sqrt 2 * Rde) := by ring
      · have hκeq : κ = 1 := by rw [hκdef]; exact max_eq_right h
        rw [hκeq, div_one]
        nlinarith [hsq2pos, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), hC₂.le]
    have hκ16 : κ ≤ 16 * M := by
      have h : κ ≤ M + 1 := by
        rw [hκdef]
        exact max_le (by linarith [hs2M]) (by linarith [hM])
      linarith [hM]
    have hκ_mgBz₂ : κ ≤ Work.Pert.V5.mgB Ξ z₂ := by
      have h : κ ≤ Work.Pert.V5.mgB Ξ z₂ := le_trans hz₂clr (min_le_right _ _)
      rw [hκdef] at h; exact h
    have hκ_mgBζ₂ : κ ≤ Work.Pert.V5.mgB Ξ ζ₂ := by
      have h : κ ≤ Work.Pert.V5.mgB Ξ ζ₂ := le_trans hζ₂clr (min_le_right _ _)
      rw [hκdef] at h; exact h
    -- ## 6. the horizontal legs
    have hmarginA : ∀ ξ ∈ Set.Icc xv z₂.re,
        κ ≤ min (Work.Pert.V5.mgA Ξ α ((ξ : ℂ) + (z₂.im : ℂ) * Complex.I))
                (Work.Pert.V5.mgB Ξ ((ξ : ℂ) + (z₂.im : ℂ) * Complex.I)) := by
      intro ξ hξ
      have h1 : κ ≤ Work.Pert.V5.mgA Ξ α ((ξ : ℂ) + (z₂.im : ℂ) * Complex.I) := by
        rw [mgA_line]
        have h2 : xv ≤ ξ := hξ.1
        have h3 : (0 : ℝ) ≤ |z₂.im + (1 / α).im| := abs_nonneg _
        linarith [h2, hxv_le, hA, h3, hκ16]
      have h2 : κ ≤ Work.Pert.V5.mgB Ξ ((ξ : ℂ) + (z₂.im : ℂ) * Complex.I) := by
        rw [mgB_line]
        have h3 : ξ ≤ z₂.re := hξ.2
        have h4 : Work.Pert.V5.mgB Ξ z₂ = |z₂.im| - Ξ - z₂.re := by
          simp only [Work.Pert.V5.mgB]
        linarith [h3, hκ_mgBz₂, h4.le, h4.ge]
      exact le_min h1 h2
    have hmarginC : ∀ ξ ∈ Set.Icc xv ζ₂.re,
        κ ≤ min (Work.Pert.V5.mgA Ξ α ((ξ : ℂ) + (ζ₂.im : ℂ) * Complex.I))
                (Work.Pert.V5.mgB Ξ ((ξ : ℂ) + (ζ₂.im : ℂ) * Complex.I)) := by
      intro ξ hξ
      have h1 : κ ≤ Work.Pert.V5.mgA Ξ α ((ξ : ℂ) + (ζ₂.im : ℂ) * Complex.I) := by
        rw [mgA_line]
        have h2 : xv ≤ ξ := hξ.1
        have h3 : (0 : ℝ) ≤ |ζ₂.im + (1 / α).im| := abs_nonneg _
        linarith [h2, hxv_le, hA, h3, hκ16]
      have h2 : κ ≤ Work.Pert.V5.mgB Ξ ((ξ : ℂ) + (ζ₂.im : ℂ) * Complex.I) := by
        rw [mgB_line]
        have h3 : ξ ≤ ζ₂.re := hξ.2
        have h4 : Work.Pert.V5.mgB Ξ ζ₂ = |ζ₂.im| - Ξ - ζ₂.re := by
          simp only [Work.Pert.V5.mgB]
        linarith [h3, hκ_mgBζ₂, h4.le, h4.ge]
      exact le_min h1 h2
    have hDE2 : ∀ (Φ v : ℂ → ℂ) (z : ℂ) (R : ℝ), Rde ≤ R →
        DifferentiableOn ℂ Φ (Metric.ball z R) → Set.InjOn Φ (Metric.ball z R) →
        DifferentiableOn ℂ v (Metric.ball z R) → (∀ w ∈ Metric.ball z R, ‖v w - 1‖ < 1 / 4) →
        (∀ w ∈ Metric.ball z R, w + v w ∈ Metric.ball z R → Φ (w + v w) = Φ w + 1) →
        ‖deriv Φ z - 1 / v z‖ ≤ C₂ / R :=
      fun Φ v z R hR h1 h2 h3 h4 h5 => (hDE Φ v z R hR h1 h2 h3 h4 h5).2
    have hlegC := Work.Pert.V5.horiz_dev_le_of_margin hF hΞ hrr hM hInF1 hα hRde hC₂ hσ hnorm
      hu hu2 hτQ hDE2 hNT hΦm (a := xv) (b := ζ₂.re) (s := ζ₂.im) (κ := κ)
      hxv_leζ hκpos hκRde hmarginC
    have hlegB := Work.Pert.V5.dev_vert_band hF hΞ hrr hM hInF1 hα hQAdm hσ hnorm hu hu2 hτQ
      hNT hΦm xv z₂.im ζ₂.im hxv_ge hxv_le
    -- ## 6b. the left leg `[xv, z₂.re]` at height `z₂.im`
    have hsegA : ∀ ξ ∈ Set.Icc xv z₂.re,
        ((ξ : ℂ) + (z₂.im : ℂ) * Complex.I) ∈ Work.Pert.Qm Ξ α := by
      intro ξ hξ
      have hm := hmarginA ξ hξ
      rw [Work.Pert.V5.mem_Qm_iff_mg]
      exact ⟨lt_of_lt_of_le hκpos (le_trans hm (min_le_left _ _)),
             lt_of_lt_of_le hκpos (le_trans hm (min_le_right _ _))⟩
    have hloA : ∀ ξ ∈ Set.Icc xv z₂.re,
        Real.sqrt 2 * Rde ≤ min (Work.Pert.V5.mgA Ξ α ((ξ : ℂ) + (z₂.im : ℂ) * Complex.I))
                                (Work.Pert.V5.mgB Ξ ((ξ : ℂ) + (z₂.im : ℂ) * Complex.I)) :=
      fun ξ hξ => le_trans hκlo (hmarginA ξ hξ)
    have hposA : ∀ ξ ∈ Set.Icc xv z₂.re,
        1 ≤ min (Work.Pert.V5.mgA Ξ α ((ξ : ℂ) + (z₂.im : ℂ) * Complex.I))
                (Work.Pert.V5.mgB Ξ ((ξ : ℂ) + (z₂.im : ℂ) * Complex.I)) :=
      fun ξ hξ => le_trans hκge1 (hmarginA ξ hξ)
    have hz₂re_sixteen : z₂.re ≤ 1 / 16 := by linarith [hz₂re_ub, hzhi]
    have hℓA_le : z₂.re - xv ≤ M + Kp * (1 + Real.log (2 + M)) + 2 ^ 10 + 3 := by
      rw [hxvdef]
      rcases le_total ζ₂.re (-(Ξ + 2 ^ 10)) with h | h
      · rw [min_eq_left h]
        have h1 : -M - Kp * (1 + Real.log (2 + M)) - 2 - 2 / 32 ≤ ζ₂.re := by
          linarith [hζ₂re_lb, hpinre_lb]
        linarith [hz₂re_sixteen, h1]
      · rw [min_eq_right h]
        linarith [hz₂re_sixteen, hΞM, hKLnn]
    have hℓA_nn : 0 ≤ z₂.re - xv := by linarith [hxv_le_z₂]
    have hlegA : ‖(Φm ((z₂.re : ℂ) + (z₂.im : ℂ) * Complex.I)
          - ((z₂.re : ℂ) + (z₂.im : ℂ) * Complex.I))
        - (Φm ((xv : ℂ) + (z₂.im : ℂ) * Complex.I)
          - ((xv : ℂ) + (z₂.im : ℂ) * Complex.I))‖
        ≤ C₂ * 2 ^ 6 * (1 + Ξ) * (1 + Real.log (2 + M))
          + 2 ^ 43 * (1 + Ξ + 1 / Ξ + 1 / rr)
              * (1 + Real.log (2 + M) + Real.log (2 + |z.im|)) := by
      have hkey := rr_mul_Xi_ge (Ξ := Ξ) (rr := rr) (M := M) hΞ hrr hM hInF1 hα hσ hnorm hu2 hτQ
      have hLnn : (0 : ℝ) ≤ 1 + Real.log (2 + M) := le_of_lt hLpos
      have hMfnn : (0 : ℝ) ≤ 1 + Real.log (2 + M) + Real.log (2 + |z.im|) := by
        have h1 : (0 : ℝ) ≤ Real.log (2 + |z.im|) :=
          Real.log_nonneg (by linarith [abs_nonneg z.im])
        linarith
      rcases le_or_gt (2 ^ 11 : ℝ) Ξ with hbig | hsmall
      · -- ### Case A: `Ξ ≥ 2^11`, clear the lattice
        have hQsub : ∀ w ∈ Work.Pert.Qm Ξ α, w ∈ Work.Pert.Qm (2 ^ 11) α := by
          intro w hw
          rw [Work.Pert.V5.mem_Qm_iff_mg] at hw
          rw [Work.Pert.V5.mem_Qm_iff_mg]
          refine ⟨?_, ?_⟩
          · have h : Work.Pert.V5.mgA Ξ α w ≤ Work.Pert.V5.mgA (2 ^ 11) α w := by
              simp only [Work.Pert.V5.mgA]; linarith
            linarith [hw.1]
          · have h : Work.Pert.V5.mgB Ξ w ≤ Work.Pert.V5.mgB (2 ^ 11) w := by
              simp only [Work.Pert.V5.mgB]; linarith
            linarith [hw.2]
        have hαne : α ≠ 0 := by
          intro h0
          have hre : 0 < α.re := by
            have hh := hInF1; simp only [MandelDim.InF1] at hh
            linarith [abs_nonneg α.im]
          rw [h0] at hre; simp at hre
        have hclear : ∀ ξ ∈ Set.Icc xv z₂.re, ∀ k : ℤ,
            ‖α‖ * 2 ^ 10 ≤ ‖α * ((ξ : ℂ) + (z₂.im : ℂ) * Complex.I) - (k : ℂ)‖ := by
          intro ξ hξ k
          have hw2 : ((ξ : ℂ) + (z₂.im : ℂ) * Complex.I) ∈ Work.Pert.Qm (2 ^ 11) α :=
            hQsub _ (hsegA ξ hξ)
          have hlat := (Work.Pert.scale_lattice (show (0 : ℝ) < 2 ^ 11 by norm_num) hInF1).2
            hw2 k
          rw [show ((2 : ℝ) ^ 11) / 2 = 2 ^ 10 by norm_num] at hlat
          calc ‖α‖ * 2 ^ 10
              ≤ ‖α‖ * ‖((ξ : ℂ) + (z₂.im : ℂ) * Complex.I) - (k : ℂ) / α‖ :=
                mul_le_mul_of_nonneg_left hlat (norm_nonneg α)
            _ = ‖α * (((ξ : ℂ) + (z₂.im : ℂ) * Complex.I) - (k : ℂ) / α)‖ := by rw [norm_mul]
            _ = ‖α * ((ξ : ℂ) + (z₂.im : ℂ) * Complex.I) - (k : ℂ)‖ := by
                rw [mul_sub, mul_div_cancel₀ _ hαne]
        have hlen : z₂.re - xv ≤ 16 * (M + 2 + Ξ) := by
          have h : z₂.re - xv ≤ M + M / 2 + 2 ^ 10 + 3 := by linarith [hℓA_le, hKpLh]
          nlinarith [h, hM, hΞ, hΞM]
        have hcl := Work.Pert.V5.horiz_dev_le_clear (Ξ := Ξ) (rr := rr) (M := M) (Rde := Rde)
          (C₂ := C₂) (α := α) (σ := σ) (u := u) (Φm := Φm) (s := z₂.im) (a := xv) (b := z₂.re)
          hΞ hrr hM hInF1 hα hRde hC₂ hσ hnorm hu hu2 hτQ hDE2 hNT hΦm
          (hsegA xv ⟨le_rfl, hxv_le_z₂⟩) (hsegA z₂.re ⟨hxv_le_z₂, le_rfl⟩) hxv_le_z₂
          hlen hclear hloA hposA
        have hlogA : 1 + Real.log (2 + z₂.re - xv)
            ≤ 9 * (1 + Real.log (2 + M) + Real.log (2 + |z.im|)) := by
          have h0 := clear_log_le (M := M) (Ξ := Ξ) (ℓ := z₂.re - xv) (y := |z.im|)
            hM hΞ hΞM hlen hℓA_nn (abs_nonneg z.im)
          rw [show (2 : ℝ) + (z₂.re - xv) = 2 + z₂.re - xv from by ring] at h0
          exact h0
        have hlogB : 1 + Real.log (2 + (z₂.re - xv))
            ≤ 9 * (1 + Real.log (2 + M) + Real.log (2 + |z.im|)) := by
          rw [show (2 : ℝ) + (z₂.re - xv) = 2 + z₂.re - xv from by ring]
          exact hlogA
        have hdef := clear_defect_le (Ξ := Ξ) (rr := rr) (ℓ := z₂.re - xv)
          (Mf := 1 + Real.log (2 + M) + Real.log (2 + |z.im|)) hΞ hrr hℓA_nn hMfnn hlogB
        rw [show (2 : ℝ) + z₂.re - xv = 2 + (z₂.re - xv) from by ring] at hcl
        linarith [hcl, hdef]
      · -- ### Case B: `Ξ < 2^11`, the general (low-margin) tool
        have hlen : |z₂.re - xv| ≤ 2 * M + 2 ^ 12 := by
          rw [abs_of_nonneg hℓA_nn]
          have h : z₂.re - xv ≤ M + M / 2 + 2 ^ 10 + 3 := by linarith [hℓA_le, hKpLh]
          nlinarith [h, hM, hΞ]
        have hloG : ∀ x ∈ Set.Icc (min xv z₂.re) (max xv z₂.re),
            Real.sqrt 2 * Rde ≤ min (Work.Pert.V5.mgA Ξ α (x + z₂.im * Complex.I))
                                    (Work.Pert.V5.mgB Ξ (x + z₂.im * Complex.I)) := by
          intro x hx
          rw [min_eq_left hxv_le_z₂, max_eq_right hxv_le_z₂] at hx
          exact hloA x hx
        have hposG : ∀ x ∈ Set.Icc (min xv z₂.re) (max xv z₂.re),
            1 ≤ min (Work.Pert.V5.mgA Ξ α (x + z₂.im * Complex.I))
                    (Work.Pert.V5.mgB Ξ (x + z₂.im * Complex.I)) := by
          intro x hx
          rw [min_eq_left hxv_le_z₂, max_eq_right hxv_le_z₂] at hx
          exact hposA x hx
        have hgen := Work.Pert.V5.horiz_dev_le_gen (Ξ := Ξ) (rr := rr) (M := M) (Rde := Rde)
          (C₂ := C₂) (α := α) (σ := σ) (u := u) (Φm := Φm) (s := z₂.im) (a := xv) (b := z₂.re)
          hΞ hrr hM hInF1 hα hRde hC₂ hσ hnorm hu hu2 hτQ hDE2 hNT hΦm
          (hsegA xv ⟨le_rfl, hxv_le_z₂⟩) (hsegA z₂.re ⟨hxv_le_z₂, le_rfl⟩)
          hlen hloG hposG
        have hLle : 1 + Real.log (2 + M) ≤ 1 + Real.log (2 + M) + Real.log (2 + |z.im|) := by
          have h1 : (0 : ℝ) ≤ Real.log (2 + |z.im|) :=
            Real.log_nonneg (by linarith [abs_nonneg z.im])
          linarith
        have hdef := gen_defect_le (Ξ := Ξ) (rr := rr) (L := 1 + Real.log (2 + M))
          (Mf := 1 + Real.log (2 + M) + Real.log (2 + |z.im|))
          hΞ hrr hsmall hkey hLnn hMfnn hLle
        linarith [hgen, hdef]
    -- ## 7. assemble
    have hA' : ‖(Φm z₂ - z₂) - (Φm ((xv : ℂ) + (z₂.im : ℂ) * Complex.I)
        - ((xv : ℂ) + (z₂.im : ℂ) * Complex.I))‖
        ≤ C₂ * 2 ^ 6 * (1 + Ξ) * (1 + Real.log (2 + M))
          + 2 ^ 43 * (1 + Ξ + 1 / Ξ + 1 / rr)
              * (1 + Real.log (2 + M) + Real.log (2 + |z.im|)) := by
      have h := hlegA
      rw [show ((z₂.re : ℂ) + (z₂.im : ℂ) * Complex.I) = z₂ from Complex.re_add_im z₂] at h
      exact h
    have hC' : ‖(Φm ((xv : ℂ) + (ζ₂.im : ℂ) * Complex.I)
        - ((xv : ℂ) + (ζ₂.im : ℂ) * Complex.I)) - (Φm ζ₂ - ζ₂)‖
        ≤ (C₂ * Real.sqrt 2 / κ + 1 / 31) * (ζ₂.re - xv) := by
      rw [norm_sub_rev]
      have h := hlegC
      rw [show ((ζ₂.re : ℂ) + (ζ₂.im : ℂ) * Complex.I) = ζ₂ from Complex.re_add_im ζ₂] at h
      exact h
    have hζ₂dev' : ‖(Φm ζ₂ - ζ₂) - (Φm z₀ - z₀)‖ ≤ 2 / 32 := by
      rw [norm_sub_rev]; exact hζ₂dev
    have hchain : ‖(Φm z - z) - (Φm z₀ - z₀)‖
        ≤ 2 / 32 + ((C₂ * 2 ^ 6 * (1 + Ξ) * (1 + Real.log (2 + M))
              + 2 ^ 43 * (1 + Ξ + 1 / Ξ + 1 / rr)
                  * (1 + Real.log (2 + M) + Real.log (2 + |z.im|)))
            + ((1 / 150 + 1 / 31) * |ζ₂.im - z₂.im|
              + ((C₂ * Real.sqrt 2 / κ + 1 / 31) * (ζ₂.re - xv) + 2 / 32))) :=
      chain_add hz₂dev (chain_add hA' (chain_add hlegB (chain_add hC' hζ₂dev')))
    have hDz₀ : ‖Φm z₀ - z₀‖ ≤ Kp * (1 + Real.log (2 + M)) :=
      Work.Pert.V5.pin_dev_le hpin hpinbd
    have hmain : ‖Φm z - z‖ ≤ Kp * (1 + Real.log (2 + M)) + 1 / 8
        + (C₂ * 2 ^ 6 * (1 + Ξ) * (1 + Real.log (2 + M))
            + 2 ^ 43 * (1 + Ξ + 1 / Ξ + 1 / rr)
                * (1 + Real.log (2 + M) + Real.log (2 + |z.im|)))
        + (1 / 150 + 1 / 31) * |ζ₂.im - z₂.im|
        + (C₂ * Real.sqrt 2 / κ + 1 / 31) * (ζ₂.re - xv) + 1 / 8 := by
      have hsplit := norm_add_le ((Φm z - z) - (Φm z₀ - z₀)) (Φm z₀ - z₀)
      have he : ((Φm z - z) - (Φm z₀ - z₀)) + (Φm z₀ - z₀) = Φm z - z := by ring
      rw [he] at hsplit
      have h2 := add_le_add hchain hDz₀
      have h3 : (2 / 32 + ((C₂ * 2 ^ 6 * (1 + Ξ) * (1 + Real.log (2 + M))
              + 2 ^ 43 * (1 + Ξ + 1 / Ξ + 1 / rr)
                  * (1 + Real.log (2 + M) + Real.log (2 + |z.im|)))
            + ((1 / 150 + 1 / 31) * |ζ₂.im - z₂.im|
              + ((C₂ * Real.sqrt 2 / κ + 1 / 31) * (ζ₂.re - xv) + 2 / 32))))
          + Kp * (1 + Real.log (2 + M))
          ≤ Kp * (1 + Real.log (2 + M)) + 1 / 8
            + (C₂ * 2 ^ 6 * (1 + Ξ) * (1 + Real.log (2 + M))
                + 2 ^ 43 * (1 + Ξ + 1 / Ξ + 1 / rr)
                    * (1 + Real.log (2 + M) + Real.log (2 + |z.im|)))
            + (1 / 150 + 1 / 31) * |ζ₂.im - z₂.im|
            + (C₂ * Real.sqrt 2 / κ + 1 / 31) * (ζ₂.re - xv) + 1 / 8 := by linarith
      linarith [hsplit, h2, h3]
    -- ## 8. the remaining slot bounds and the final arithmetic
    have hℓC : ζ₂.re - xv ≤ 2 ^ 10 := by
      have h1 : ζ₂.re ≤ -M + Kp * (1 + Real.log (2 + M)) - 2 + 2 / 32 := by
        linarith [hζ₂re_ub, hpinre_ub]
      rcases le_total ζ₂.re (-(Ξ + 2 ^ 10)) with h | h
      · rw [hxvdef, min_eq_left h]; linarith [hΞM, hM]
      · rw [hxvdef, min_eq_right h]
        have h2 : -M - (Kp * (1 + Real.log (2 + M)) + 2 + 2 / 32) ≤ ζ₂.re := by
          linarith [hζ₂re_lb]
        linarith [hpincl, hΞ.le, hs2nn]
    have hℓCnn : 0 ≤ ζ₂.re - xv := by linarith [hxv_leζ]
    have hlegC'' : (C₂ * Real.sqrt 2 / κ + 1 / 31) * (ζ₂.re - xv) ≤ (2 * C₂ + 1 / 31) * 2 ^ 10 := by
      apply mul_le_mul
      · linarith [hκC]
      · exact hℓC
      · exact hℓCnn
      · positivity
    have hHy : |ζ₂.im - z₂.im| ≤ |z.im| + Kp * (1 + Real.log (2 + M)) + 1 / 4 := by
      have h1 : |ζ₂.im| ≤ Kp * (1 + Real.log (2 + M)) + 2 / 32 := by
        have h1a := abs_sub_abs_le_abs_sub ζ₂.im z₀.im
        linarith [h1a, hpinim, hζ₂im]
      have h2 : |z₂.im| ≤ |z.im| + 2 / 32 := by
        have h2a := abs_sub_abs_le_abs_sub z₂.im z.im
        linarith [h2a, hz₂im]
      have h3 : |ζ₂.im - z₂.im| ≤ |ζ₂.im| + |z₂.im| := by
        have := abs_add_le ζ₂.im (-z₂.im)
        simpa only [sub_eq_add_neg, abs_neg] using this
      linarith [h1, h2, h3]
    have harith := arith_strip_v4 (Ξ := Ξ) (rr := rr) (M := M) (Kp := Kp) (C₂ := C₂)
      (y := |z.im|) hΞ hrr hM hKp hC₂.le (abs_nonneg z.im)
    linarith [hmain, harith, hlegC'', hHy]

end Work.Pert.Pin
