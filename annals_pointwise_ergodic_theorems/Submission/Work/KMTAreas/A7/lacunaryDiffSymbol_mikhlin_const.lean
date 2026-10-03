/-
# The Mikhlin criterion for the finite difference symbol, with a general shift constant

This is `Work.KMTAreas.A7.lacunaryDiffSymbol_mikhlin` (PROVED, in
`Submission/Work/KMTAreas/A7/lacunaryDiffSymbol_mikhlin.lean`) with the hypothesis
`∀ i ∈ D, |c i| ≤ 2 * σ i` relaxed to `∀ i ∈ D, |c i| ≤ K * σ i`, `K ≥ 0` a parameter:
the constant `A` of the conclusion then depends on `K`.

The proof is the proof of the original with `2` replaced by `K`: the only places the hypothesis is
used are `|c i| |ξ| ≤ K σ i |ξ|` (hence `‖e^{2πi c_i ξ} - 1‖ ≤ 2π K σ i |ξ|`) and
`2π|c i| ≤ 2π K σ i`.  The constant of the original,
`B = 4πM0 + (4πM1 + 4πM0) + (4πM2 + 8πM1 + 16π²M0)`, becomes
`B = 2πKM0 + (2πKM1 + 2πKM0) + (2πKM2 + 4πKM1 + 4π²K²M0)`, and `A = 1 + (2/(1-lam⁻¹)) B`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.lacunarySum_norm_bound
import Submission.Work.KMTAreas.A7.diffSymbol_contDiff_deriv

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTAreas.A7

open Finset

noncomputable section

/-! ## Elementary norm facts -/

private lemma pow_two_le_self_of_le_one {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : t ^ 2 ≤ t := by
  nlinarith

private lemma pow_three_le_self_of_le_one {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : t ^ 3 ≤ t := by
  have h2 : t ^ 2 ≤ 1 := by nlinarith
  calc t ^ 3 = t ^ 2 * t := by ring
    _ ≤ 1 * t := mul_le_mul_of_nonneg_right h2 h0
    _ = t := one_mul t

private lemma norm_two_pi_I_mul (a b : ℝ) :
    ‖(2 * Real.pi * Complex.I * ((a : ℂ) * (b : ℂ)) : ℂ)‖ = 2 * Real.pi * (|a| * |b|) := by
  have h : (2 * Real.pi * Complex.I * ((a : ℂ) * (b : ℂ)) : ℂ)
      = Complex.I * (((2 * Real.pi * (a * b) : ℝ)) : ℂ) := by push_cast; ring
  rw [h, Complex.norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_mul, abs_mul, abs_mul, abs_of_pos Real.pi_pos,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]

private lemma norm_two_pi_I_mul_real (a : ℝ) :
    ‖(2 * Real.pi * Complex.I * (a : ℂ) : ℂ)‖ = 2 * Real.pi * |a| := by
  have h : (2 * Real.pi * Complex.I * (a : ℂ) : ℂ)
      = 2 * Real.pi * Complex.I * ((a : ℂ) * (1 : ℂ)) := by ring
  have hh := norm_two_pi_I_mul a 1
  simpa using hh

private lemma norm_exp_two_pi_I_mul (a b : ℝ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * (b : ℂ)))‖ = 1 := by
  have h : (2 * Real.pi * Complex.I * ((a : ℂ) * (b : ℂ)) : ℂ)
      = Complex.I * (((2 * Real.pi * (a * b) : ℝ)) : ℂ) := by push_cast; ring
  rw [h, Complex.norm_exp_I_mul_ofReal]

private lemma norm_exp_two_pi_I_mul_sub_one_le (a b : ℝ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * (b : ℂ))) - 1‖
      ≤ 2 * Real.pi * (|a| * |b|) := by
  have h : (2 * Real.pi * Complex.I * ((a : ℂ) * (b : ℂ)) : ℂ)
      = Complex.I * (((2 * Real.pi * (a * b) : ℝ)) : ℂ) := by push_cast; ring
  rw [h, Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show (2 * Real.pi * (a * b)) / 2 = Real.pi * (a * b) by ring]
  rw [Real.norm_eq_abs, abs_mul, show |(2 : ℝ)| = 2 by norm_num]
  have h3 : |Real.sin (Real.pi * (a * b))| ≤ Real.pi * (|a| * |b|) := by
    calc |Real.sin (Real.pi * (a * b))| ≤ |Real.pi * (a * b)| := Real.abs_sin_le_abs
      _ = Real.pi * (|a| * |b|) := by rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos]
  linarith

/-! ## The per-term Mikhlin bounds -/

/-- **The value bound of a single term** of the difference symbol, with the shift hypothesis
`|c| ≤ K σ` in place of the original `|c| ≤ 2 σ`. -/
private lemma diffTerm_value_bound {η : ℝ → ℂ} {M0 K σ c : ℝ} (hM0 : 0 ≤ M0)
    (hη0 : ∀ y : ℝ, ‖η y‖ ≤ M0) (hc : |c| ≤ K * σ) {ε : ℂ} (hε : ‖ε‖ ≤ 1) (ξ : ℝ) :
    ‖ε * (η (σ * ξ) * (Complex.exp (2 * Real.pi * Complex.I * (c * ξ)) - 1))‖
      ≤ (2 * Real.pi * K * M0) * (σ * |ξ|) := by
  have hE := norm_exp_two_pi_I_mul_sub_one_le c ξ
  have hcx : |c| * |ξ| ≤ K * σ * |ξ| := mul_le_mul_of_nonneg_right hc (abs_nonneg ξ)
  have h1 : ‖η (σ * ξ)‖ * ‖Complex.exp (2 * Real.pi * Complex.I * (c * ξ)) - 1‖
      ≤ M0 * (2 * Real.pi * (|c| * |ξ|)) := mul_le_mul (hη0 _) hE (norm_nonneg _) hM0
  have h2 : 2 * Real.pi * (|c| * |ξ|) ≤ 2 * Real.pi * (K * σ * |ξ|) :=
    mul_le_mul_of_nonneg_left hcx (by positivity)
  have h3 : M0 * (2 * Real.pi * (|c| * |ξ|)) ≤ M0 * (2 * Real.pi * (K * σ * |ξ|)) :=
    mul_le_mul_of_nonneg_left h2 hM0
  calc ‖ε * (η (σ * ξ) * (Complex.exp (2 * Real.pi * Complex.I * (c * ξ)) - 1))‖
      ≤ ‖ε‖ * (‖η (σ * ξ)‖ * ‖Complex.exp (2 * Real.pi * Complex.I * (c * ξ)) - 1‖) := by
        rw [norm_mul, norm_mul]
    _ ≤ 1 * (M0 * (2 * Real.pi * (|c| * |ξ|))) :=
        mul_le_mul hε h1 (mul_nonneg (norm_nonneg _) (norm_nonneg _)) zero_le_one
    _ ≤ 1 * (M0 * (2 * Real.pi * (K * σ * |ξ|))) := mul_le_mul_of_nonneg_left h3 zero_le_one
    _ = (2 * Real.pi * K * M0) * (σ * |ξ|) := by ring

/-- **The first-derivative bound of a single term** of the difference symbol. -/
private lemma diffTerm_deriv_bound {η : ℝ → ℂ} {M0 M1 K σ c : ℝ} (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1)
    (hK : 0 ≤ K) (hη0 : ∀ y : ℝ, ‖η y‖ ≤ M0) (hη1 : ∀ y : ℝ, ‖deriv η y‖ ≤ M1)
    (hσ : 0 < σ) (hc : |c| ≤ K * σ) {ε : ℂ} (hε : ‖ε‖ ≤ 1) {ξ : ℝ} (hξ : σ * |ξ| ≤ 1) :
    |ξ| * ‖ε * (σ * deriv η (σ * ξ) * (Complex.exp (2 * Real.pi * Complex.I * (c * ξ)) - 1)
        + η (σ * ξ) * ((2 * Real.pi * Complex.I * c) *
            Complex.exp (2 * Real.pi * Complex.I * (c * ξ))))‖
      ≤ (2 * Real.pi * K * M1 + 2 * Real.pi * K * M0) * (σ * |ξ|) := by
  have hσc : ‖(σ : ℂ)‖ = σ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hσ.le]
  have hE1 : ‖Complex.exp (2 * Real.pi * Complex.I * (c * ξ)) - 1‖
      ≤ 2 * Real.pi * (|c| * |ξ|) := norm_exp_two_pi_I_mul_sub_one_le c ξ
  have hE2 : ‖Complex.exp (2 * Real.pi * Complex.I * (c * ξ))‖ = 1 :=
    norm_exp_two_pi_I_mul c ξ
  have hcx : |c| * |ξ| ≤ K * σ * |ξ| := mul_le_mul_of_nonneg_right hc (abs_nonneg ξ)
  -- piece A: the differentiated amplitude
  have hp1 : ‖(σ : ℂ) * deriv η (σ * ξ) * (Complex.exp (2 * Real.pi * Complex.I * (c * ξ)) - 1)‖
      ≤ 2 * Real.pi * K * M1 * σ ^ 2 * |ξ| := by
    have hA : ‖deriv η (σ * ξ)‖ ≤ M1 := hη1 _
    have hmul : ‖(σ : ℂ) * deriv η (σ * ξ)‖ ≤ σ * M1 := by
      calc ‖(σ : ℂ) * deriv η (σ * ξ)‖ ≤ ‖(σ : ℂ)‖ * ‖deriv η (σ * ξ)‖ := norm_mul_le _ _
        _ = σ * ‖deriv η (σ * ξ)‖ := by rw [hσc]
        _ ≤ σ * M1 := mul_le_mul_of_nonneg_left hA hσ.le
    calc ‖(σ : ℂ) * deriv η (σ * ξ) * (Complex.exp (2 * Real.pi * Complex.I * (c * ξ)) - 1)‖
        ≤ ‖(σ : ℂ) * deriv η (σ * ξ)‖
            * ‖Complex.exp (2 * Real.pi * Complex.I * (c * ξ)) - 1‖ := norm_mul_le _ _
      _ ≤ (σ * M1) * (2 * Real.pi * (|c| * |ξ|)) :=
          mul_le_mul hmul hE1 (norm_nonneg _) (by positivity)
      _ ≤ (σ * M1) * (2 * Real.pi * (K * σ * |ξ|)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left hcx (by positivity)
      _ = 2 * Real.pi * K * M1 * σ ^ 2 * |ξ| := by ring
  -- piece B: the differentiated character
  have hp2 : ‖η (σ * ξ) * ((2 * Real.pi * Complex.I * (c : ℂ)) *
      Complex.exp (2 * Real.pi * Complex.I * (c * ξ)))‖ ≤ 2 * Real.pi * K * M0 * σ := by
    have hB2 : ‖(2 * Real.pi * Complex.I * (c : ℂ)) *
        Complex.exp (2 * Real.pi * Complex.I * (c * ξ))‖ = 2 * Real.pi * |c| := by
      rw [norm_mul, norm_two_pi_I_mul_real, hE2, mul_one]
    calc ‖η (σ * ξ) * ((2 * Real.pi * Complex.I * (c : ℂ)) *
            Complex.exp (2 * Real.pi * Complex.I * (c * ξ)))‖
        ≤ ‖η (σ * ξ)‖ * ‖(2 * Real.pi * Complex.I * (c : ℂ)) *
            Complex.exp (2 * Real.pi * Complex.I * (c * ξ))‖ := norm_mul_le _ _
      _ = ‖η (σ * ξ)‖ * (2 * Real.pi * |c|) := by rw [hB2]
      _ ≤ M0 * (2 * Real.pi * |c|) := mul_le_mul_of_nonneg_right (hη0 _) (by positivity)
      _ ≤ M0 * (2 * Real.pi * (K * σ)) := by
          apply mul_le_mul_of_nonneg_left _ hM0
          exact mul_le_mul_of_nonneg_left hc (by positivity)
      _ = 2 * Real.pi * K * M0 * σ := by ring
  have hmid : ‖ε * ((σ : ℂ) * deriv η (σ * ξ)
        * (Complex.exp (2 * Real.pi * Complex.I * (c * ξ)) - 1)
        + η (σ * ξ) * ((2 * Real.pi * Complex.I * (c : ℂ))
            * Complex.exp (2 * Real.pi * Complex.I * (c * ξ))))‖
      ≤ 2 * Real.pi * K * M1 * σ ^ 2 * |ξ| + 2 * Real.pi * K * M0 * σ := by
    have hAB : ‖(σ : ℂ) * deriv η (σ * ξ) * (Complex.exp (2 * Real.pi * Complex.I * (c * ξ)) - 1)
          + η (σ * ξ) * ((2 * Real.pi * Complex.I * (c : ℂ))
              * Complex.exp (2 * Real.pi * Complex.I * (c * ξ)))‖
        ≤ ‖(σ : ℂ) * deriv η (σ * ξ)
              * (Complex.exp (2 * Real.pi * Complex.I * (c * ξ)) - 1)‖
          + ‖η (σ * ξ) * ((2 * Real.pi * Complex.I * (c : ℂ))
              * Complex.exp (2 * Real.pi * Complex.I * (c * ξ)))‖ := norm_add_le _ _
    calc ‖ε * ((σ : ℂ) * deriv η (σ * ξ)
            * (Complex.exp (2 * Real.pi * Complex.I * (c * ξ)) - 1)
            + η (σ * ξ) * ((2 * Real.pi * Complex.I * (c : ℂ))
                * Complex.exp (2 * Real.pi * Complex.I * (c * ξ))))‖
        ≤ ‖ε‖ * ‖(σ : ℂ) * deriv η (σ * ξ)
              * (Complex.exp (2 * Real.pi * Complex.I * (c * ξ)) - 1)
            + η (σ * ξ) * ((2 * Real.pi * Complex.I * (c : ℂ))
                * Complex.exp (2 * Real.pi * Complex.I * (c * ξ)))‖ := norm_mul_le _ _
      _ ≤ 1 * (‖(σ : ℂ) * deriv η (σ * ξ)
              * (Complex.exp (2 * Real.pi * Complex.I * (c * ξ)) - 1)‖
          + ‖η (σ * ξ) * ((2 * Real.pi * Complex.I * (c : ℂ))
              * Complex.exp (2 * Real.pi * Complex.I * (c * ξ)))‖) :=
          mul_le_mul hε hAB (norm_nonneg _) zero_le_one
      _ = ‖(σ : ℂ) * deriv η (σ * ξ)
              * (Complex.exp (2 * Real.pi * Complex.I * (c * ξ)) - 1)‖
          + ‖η (σ * ξ) * ((2 * Real.pi * Complex.I * (c : ℂ))
              * Complex.exp (2 * Real.pi * Complex.I * (c * ξ)))‖ := one_mul _
      _ ≤ 2 * Real.pi * K * M1 * σ ^ 2 * |ξ| + 2 * Real.pi * K * M0 * σ := by
          linarith [hp1, hp2]
  calc |ξ| * ‖ε * (σ * deriv η (σ * ξ) * (Complex.exp (2 * Real.pi * Complex.I * (c * ξ)) - 1)
        + η (σ * ξ) * ((2 * Real.pi * Complex.I * c) *
            Complex.exp (2 * Real.pi * Complex.I * (c * ξ))))‖
      = |ξ| * ‖ε * ((σ : ℂ) * deriv η (σ * ξ)
            * (Complex.exp (2 * Real.pi * Complex.I * (c * ξ)) - 1)
          + η (σ * ξ) * ((2 * Real.pi * Complex.I * (c : ℂ))
              * Complex.exp (2 * Real.pi * Complex.I * (c * ξ))))‖ := by ring_nf
    _ ≤ |ξ| * (2 * Real.pi * K * M1 * σ ^ 2 * |ξ| + 2 * Real.pi * K * M0 * σ) :=
        mul_le_mul_of_nonneg_left hmid (abs_nonneg ξ)
    _ = 2 * Real.pi * K * M1 * (σ * |ξ|) ^ 2 + 2 * Real.pi * K * M0 * (σ * |ξ|) := by ring
    _ ≤ (2 * Real.pi * K * M1 + 2 * Real.pi * K * M0) * (σ * |ξ|) := by
        have h0 : 0 ≤ σ * |ξ| := mul_nonneg hσ.le (abs_nonneg ξ)
        have h2 : (σ * |ξ|) ^ 2 ≤ σ * |ξ| := pow_two_le_self_of_le_one h0 hξ
        have h4 : 2 * Real.pi * K * M1 * (σ * |ξ|) ^ 2
            ≤ 2 * Real.pi * K * M1 * (σ * |ξ|) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
        linarith

/-- **The second-derivative bound of a single term** of the difference symbol. -/
private lemma diffTerm_deriv2_bound {η : ℝ → ℂ} {M0 M1 M2 K σ c : ℝ} (hM0 : 0 ≤ M0)
    (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2) (hK : 0 ≤ K)
    (hη0 : ∀ y : ℝ, ‖η y‖ ≤ M0) (hη1 : ∀ y : ℝ, ‖deriv η y‖ ≤ M1)
    (hη2 : ∀ y : ℝ, ‖iteratedDeriv 2 η y‖ ≤ M2)
    (hσ : 0 < σ) (hc : |c| ≤ K * σ) {ε : ℂ} (hε : ‖ε‖ ≤ 1) {ξ : ℝ} (hξ : σ * |ξ| ≤ 1) :
    |ξ| ^ 2 * ‖ε * (σ * (σ * iteratedDeriv 2 η (σ * ξ))
        * (Complex.exp (2 * Real.pi * Complex.I * (c * ξ)) - 1)
        + (σ * deriv η (σ * ξ)) * ((2 * Real.pi * Complex.I * c)
            * Complex.exp (2 * Real.pi * Complex.I * (c * ξ)))
        + (σ * deriv η (σ * ξ)) * ((2 * Real.pi * Complex.I * c)
            * Complex.exp (2 * Real.pi * Complex.I * (c * ξ)))
        + η (σ * ξ) * ((2 * Real.pi * Complex.I * c)
            * ((2 * Real.pi * Complex.I * c)
              * Complex.exp (2 * Real.pi * Complex.I * (c * ξ)))))‖
      ≤ (2 * Real.pi * K * M2 + 4 * Real.pi * K * M1 + 4 * Real.pi ^ 2 * K ^ 2 * M0)
          * (σ * |ξ|) := by
  have hσc : ‖(σ : ℂ)‖ = σ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hσ.le]
  have hE1 : ‖Complex.exp (2 * Real.pi * Complex.I * (c * ξ)) - 1‖
      ≤ 2 * Real.pi * (|c| * |ξ|) := norm_exp_two_pi_I_mul_sub_one_le c ξ
  have hE2 : ‖Complex.exp (2 * Real.pi * Complex.I * (c * ξ))‖ = 1 :=
    norm_exp_two_pi_I_mul c ξ
  have hcx : |c| * |ξ| ≤ K * σ * |ξ| := mul_le_mul_of_nonneg_right hc (abs_nonneg ξ)
  have hcx2 : 2 * Real.pi * |c| ≤ 2 * Real.pi * (K * σ) :=
    mul_le_mul_of_nonneg_left hc (by positivity)
  -- piece A2: the twice-differentiated amplitude
  have hpA : ‖(σ : ℂ) * ((σ : ℂ) * iteratedDeriv 2 η (σ * ξ))
      * (Complex.exp (2 * Real.pi * Complex.I * (c * ξ)) - 1)‖
      ≤ 2 * Real.pi * K * M2 * σ ^ 3 * |ξ| := by
    have hA : ‖iteratedDeriv 2 η (σ * ξ)‖ ≤ M2 := hη2 _
    have hmul : ‖(σ : ℂ) * ((σ : ℂ) * iteratedDeriv 2 η (σ * ξ))‖ ≤ σ * (σ * M2) := by
      calc ‖(σ : ℂ) * ((σ : ℂ) * iteratedDeriv 2 η (σ * ξ))‖
          ≤ ‖(σ : ℂ)‖ * ‖(σ : ℂ) * iteratedDeriv 2 η (σ * ξ)‖ := norm_mul_le _ _
        _ ≤ ‖(σ : ℂ)‖ * (‖(σ : ℂ)‖ * ‖iteratedDeriv 2 η (σ * ξ)‖) :=
            mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _)
        _ = σ * (σ * ‖iteratedDeriv 2 η (σ * ξ)‖) := by rw [hσc]
        _ ≤ σ * (σ * M2) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hA hσ.le) hσ.le
    calc ‖(σ : ℂ) * ((σ : ℂ) * iteratedDeriv 2 η (σ * ξ))
            * (Complex.exp (2 * Real.pi * Complex.I * (c * ξ)) - 1)‖
        ≤ ‖(σ : ℂ) * ((σ : ℂ) * iteratedDeriv 2 η (σ * ξ))‖
            * ‖Complex.exp (2 * Real.pi * Complex.I * (c * ξ)) - 1‖ := norm_mul_le _ _
      _ ≤ (σ * (σ * M2)) * (2 * Real.pi * (|c| * |ξ|)) :=
          mul_le_mul hmul hE1 (norm_nonneg _) (by positivity)
      _ ≤ (σ * (σ * M2)) * (2 * Real.pi * (K * σ * |ξ|)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left hcx (by positivity)
      _ = 2 * Real.pi * K * M2 * σ ^ 3 * |ξ| := by ring
  -- piece B2: the first derivative of the character, with one differentiated amplitude
  have hpB : ‖((σ : ℂ) * deriv η (σ * ξ)) * ((2 * Real.pi * Complex.I * (c : ℂ))
      * Complex.exp (2 * Real.pi * Complex.I * (c * ξ)))‖ ≤ 2 * Real.pi * K * M1 * σ ^ 2 := by
    have hmm : ‖(σ : ℂ) * deriv η (σ * ξ)‖ ≤ σ * M1 := by
      calc ‖(σ : ℂ) * deriv η (σ * ξ)‖ ≤ ‖(σ : ℂ)‖ * ‖deriv η (σ * ξ)‖ := norm_mul_le _ _
        _ = σ * ‖deriv η (σ * ξ)‖ := by rw [hσc]
        _ ≤ σ * M1 := mul_le_mul_of_nonneg_left (hη1 _) hσ.le
    have hB2 : ‖(2 * Real.pi * Complex.I * (c : ℂ))
        * Complex.exp (2 * Real.pi * Complex.I * (c * ξ))‖ = 2 * Real.pi * |c| := by
      rw [norm_mul, norm_two_pi_I_mul_real, hE2, mul_one]
    calc ‖((σ : ℂ) * deriv η (σ * ξ)) * ((2 * Real.pi * Complex.I * (c : ℂ))
            * Complex.exp (2 * Real.pi * Complex.I * (c * ξ)))‖
        ≤ ‖(σ : ℂ) * deriv η (σ * ξ)‖ * ‖(2 * Real.pi * Complex.I * (c : ℂ))
            * Complex.exp (2 * Real.pi * Complex.I * (c * ξ))‖ := norm_mul_le _ _
      _ ≤ (σ * M1) * (2 * Real.pi * |c|) :=
          mul_le_mul hmm (le_of_eq hB2) (norm_nonneg _) (by positivity)
      _ ≤ (σ * M1) * (2 * Real.pi * (K * σ)) :=
          mul_le_mul_of_nonneg_left hcx2 (by positivity)
      _ = 2 * Real.pi * K * M1 * σ ^ 2 := by ring
  -- piece C2: the twice-differentiated character
  have hpC : ‖η (σ * ξ) * ((2 * Real.pi * Complex.I * (c : ℂ))
      * ((2 * Real.pi * Complex.I * (c : ℂ))
        * Complex.exp (2 * Real.pi * Complex.I * (c * ξ))))‖ ≤ 4 * Real.pi ^ 2 * K ^ 2 * M0 * σ ^ 2 := by
    have hB2 : ‖(2 * Real.pi * Complex.I * (c : ℂ))
        * ((2 * Real.pi * Complex.I * (c : ℂ))
          * Complex.exp (2 * Real.pi * Complex.I * (c * ξ)))‖
        = (2 * Real.pi * |c|) * (2 * Real.pi * |c|) := by
      have h4 : ‖(2 * Real.pi * Complex.I * (c : ℂ))
          * Complex.exp (2 * Real.pi * Complex.I * (c * ξ))‖ = 2 * Real.pi * |c| := by
        rw [norm_mul, norm_two_pi_I_mul_real, hE2, mul_one]
      rw [norm_mul, norm_two_pi_I_mul_real, h4]
    calc ‖η (σ * ξ) * ((2 * Real.pi * Complex.I * (c : ℂ))
            * ((2 * Real.pi * Complex.I * (c : ℂ))
              * Complex.exp (2 * Real.pi * Complex.I * (c * ξ))))‖
        ≤ ‖η (σ * ξ)‖ * ‖(2 * Real.pi * Complex.I * (c : ℂ))
            * ((2 * Real.pi * Complex.I * (c : ℂ))
              * Complex.exp (2 * Real.pi * Complex.I * (c * ξ)))‖ := norm_mul_le _ _
      _ = ‖η (σ * ξ)‖ * ((2 * Real.pi * |c|) * (2 * Real.pi * |c|)) := by rw [hB2]
      _ ≤ M0 * ((2 * Real.pi * |c|) * (2 * Real.pi * |c|)) :=
          mul_le_mul_of_nonneg_right (hη0 _) (by positivity)
      _ ≤ M0 * ((2 * Real.pi * (K * σ)) * (2 * Real.pi * (K * σ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hcx2 hcx2 (by positivity) (by positivity)) hM0
      _ = 4 * Real.pi ^ 2 * K ^ 2 * M0 * σ ^ 2 := by ring
  have hmid : ‖ε * ((σ : ℂ) * ((σ : ℂ) * iteratedDeriv 2 η (σ * ξ))
        * (Complex.exp (2 * Real.pi * Complex.I * (c * ξ)) - 1)
        + ((σ : ℂ) * deriv η (σ * ξ)) * ((2 * Real.pi * Complex.I * (c : ℂ))
            * Complex.exp (2 * Real.pi * Complex.I * (c * ξ)))
        + ((σ : ℂ) * deriv η (σ * ξ)) * ((2 * Real.pi * Complex.I * (c : ℂ))
            * Complex.exp (2 * Real.pi * Complex.I * (c * ξ)))
        + η (σ * ξ) * ((2 * Real.pi * Complex.I * (c : ℂ))
            * ((2 * Real.pi * Complex.I * (c : ℂ))
              * Complex.exp (2 * Real.pi * Complex.I * (c * ξ)))))‖
      ≤ 2 * Real.pi * K * M2 * σ ^ 3 * |ξ|
        + (4 * Real.pi * K * M1 * σ ^ 2 + 4 * Real.pi ^ 2 * K ^ 2 * M0 * σ ^ 2) := by
    have h1 := norm_add_le (((σ : ℂ) * ((σ : ℂ) * iteratedDeriv 2 η (σ * ξ))
          * (Complex.exp (2 * Real.pi * Complex.I * (c * ξ)) - 1))
        + (((σ : ℂ) * deriv η (σ * ξ)) * ((2 * Real.pi * Complex.I * (c : ℂ))
            * Complex.exp (2 * Real.pi * Complex.I * (c * ξ))))
        + (((σ : ℂ) * deriv η (σ * ξ)) * ((2 * Real.pi * Complex.I * (c : ℂ))
            * Complex.exp (2 * Real.pi * Complex.I * (c * ξ)))))
      (η (σ * ξ) * ((2 * Real.pi * Complex.I * (c : ℂ))
            * ((2 * Real.pi * Complex.I * (c : ℂ))
              * Complex.exp (2 * Real.pi * Complex.I * (c * ξ)))))
    have h2 := norm_add_le (((σ : ℂ) * ((σ : ℂ) * iteratedDeriv 2 η (σ * ξ))
          * (Complex.exp (2 * Real.pi * Complex.I * (c * ξ)) - 1))
        + (((σ : ℂ) * deriv η (σ * ξ)) * ((2 * Real.pi * Complex.I * (c : ℂ))
            * Complex.exp (2 * Real.pi * Complex.I * (c * ξ)))))
      (((σ : ℂ) * deriv η (σ * ξ)) * ((2 * Real.pi * Complex.I * (c : ℂ))
            * Complex.exp (2 * Real.pi * Complex.I * (c * ξ))))
    have h3 := norm_add_le (((σ : ℂ) * ((σ : ℂ) * iteratedDeriv 2 η (σ * ξ))
          * (Complex.exp (2 * Real.pi * Complex.I * (c * ξ)) - 1)))
      (((σ : ℂ) * deriv η (σ * ξ)) * ((2 * Real.pi * Complex.I * (c : ℂ))
            * Complex.exp (2 * Real.pi * Complex.I * (c * ξ))))
    have hABC : ‖((σ : ℂ) * ((σ : ℂ) * iteratedDeriv 2 η (σ * ξ))
          * (Complex.exp (2 * Real.pi * Complex.I * (c * ξ)) - 1)
        + ((σ : ℂ) * deriv η (σ * ξ)) * ((2 * Real.pi * Complex.I * (c : ℂ))
            * Complex.exp (2 * Real.pi * Complex.I * (c * ξ)))
        + ((σ : ℂ) * deriv η (σ * ξ)) * ((2 * Real.pi * Complex.I * (c : ℂ))
            * Complex.exp (2 * Real.pi * Complex.I * (c * ξ)))
        + η (σ * ξ) * ((2 * Real.pi * Complex.I * (c : ℂ))
            * ((2 * Real.pi * Complex.I * (c : ℂ))
              * Complex.exp (2 * Real.pi * Complex.I * (c * ξ)))))‖
        ≤ ‖(σ : ℂ) * ((σ : ℂ) * iteratedDeriv 2 η (σ * ξ))
              * (Complex.exp (2 * Real.pi * Complex.I * (c * ξ)) - 1)‖
          + ‖((σ : ℂ) * deriv η (σ * ξ)) * ((2 * Real.pi * Complex.I * (c : ℂ))
              * Complex.exp (2 * Real.pi * Complex.I * (c * ξ)))‖
          + ‖((σ : ℂ) * deriv η (σ * ξ)) * ((2 * Real.pi * Complex.I * (c : ℂ))
              * Complex.exp (2 * Real.pi * Complex.I * (c * ξ)))‖
          + ‖η (σ * ξ) * ((2 * Real.pi * Complex.I * (c : ℂ))
              * ((2 * Real.pi * Complex.I * (c : ℂ))
                * Complex.exp (2 * Real.pi * Complex.I * (c * ξ))))‖ := by linarith
    calc ‖ε * ((σ : ℂ) * ((σ : ℂ) * iteratedDeriv 2 η (σ * ξ))
            * (Complex.exp (2 * Real.pi * Complex.I * (c * ξ)) - 1)
          + ((σ : ℂ) * deriv η (σ * ξ)) * ((2 * Real.pi * Complex.I * (c : ℂ))
              * Complex.exp (2 * Real.pi * Complex.I * (c * ξ)))
          + ((σ : ℂ) * deriv η (σ * ξ)) * ((2 * Real.pi * Complex.I * (c : ℂ))
              * Complex.exp (2 * Real.pi * Complex.I * (c * ξ)))
          + η (σ * ξ) * ((2 * Real.pi * Complex.I * (c : ℂ))
              * ((2 * Real.pi * Complex.I * (c : ℂ))
                * Complex.exp (2 * Real.pi * Complex.I * (c * ξ)))))‖
        ≤ ‖ε‖ * ‖((σ : ℂ) * ((σ : ℂ) * iteratedDeriv 2 η (σ * ξ))
              * (Complex.exp (2 * Real.pi * Complex.I * (c * ξ)) - 1)
            + ((σ : ℂ) * deriv η (σ * ξ)) * ((2 * Real.pi * Complex.I * (c : ℂ))
                * Complex.exp (2 * Real.pi * Complex.I * (c * ξ)))
            + ((σ : ℂ) * deriv η (σ * ξ)) * ((2 * Real.pi * Complex.I * (c : ℂ))
                * Complex.exp (2 * Real.pi * Complex.I * (c * ξ)))
            + η (σ * ξ) * ((2 * Real.pi * Complex.I * (c : ℂ))
                * ((2 * Real.pi * Complex.I * (c : ℂ))
                  * Complex.exp (2 * Real.pi * Complex.I * (c * ξ)))))‖ := norm_mul_le _ _
      _ ≤ 1 * (‖(σ : ℂ) * ((σ : ℂ) * iteratedDeriv 2 η (σ * ξ))
              * (Complex.exp (2 * Real.pi * Complex.I * (c * ξ)) - 1)‖
            + ‖((σ : ℂ) * deriv η (σ * ξ)) * ((2 * Real.pi * Complex.I * (c : ℂ))
                * Complex.exp (2 * Real.pi * Complex.I * (c * ξ)))‖
            + ‖((σ : ℂ) * deriv η (σ * ξ)) * ((2 * Real.pi * Complex.I * (c : ℂ))
                * Complex.exp (2 * Real.pi * Complex.I * (c * ξ)))‖
            + ‖η (σ * ξ) * ((2 * Real.pi * Complex.I * (c : ℂ))
                * ((2 * Real.pi * Complex.I * (c : ℂ))
                  * Complex.exp (2 * Real.pi * Complex.I * (c * ξ))))‖) :=
          mul_le_mul hε hABC (norm_nonneg _) zero_le_one
      _ = ‖(σ : ℂ) * ((σ : ℂ) * iteratedDeriv 2 η (σ * ξ))
              * (Complex.exp (2 * Real.pi * Complex.I * (c * ξ)) - 1)‖
            + ‖((σ : ℂ) * deriv η (σ * ξ)) * ((2 * Real.pi * Complex.I * (c : ℂ))
                * Complex.exp (2 * Real.pi * Complex.I * (c * ξ)))‖
            + ‖((σ : ℂ) * deriv η (σ * ξ)) * ((2 * Real.pi * Complex.I * (c : ℂ))
                * Complex.exp (2 * Real.pi * Complex.I * (c * ξ)))‖
            + ‖η (σ * ξ) * ((2 * Real.pi * Complex.I * (c : ℂ))
                * ((2 * Real.pi * Complex.I * (c : ℂ))
                  * Complex.exp (2 * Real.pi * Complex.I * (c * ξ))))‖ := one_mul _
      _ ≤ 2 * Real.pi * K * M2 * σ ^ 3 * |ξ|
            + (4 * Real.pi * K * M1 * σ ^ 2 + 4 * Real.pi ^ 2 * K ^ 2 * M0 * σ ^ 2) := by
          linarith [hpA, hpB, hpC]
  calc |ξ| ^ 2 * ‖ε * (σ * (σ * iteratedDeriv 2 η (σ * ξ))
        * (Complex.exp (2 * Real.pi * Complex.I * (c * ξ)) - 1)
        + (σ * deriv η (σ * ξ)) * ((2 * Real.pi * Complex.I * c)
            * Complex.exp (2 * Real.pi * Complex.I * (c * ξ)))
        + (σ * deriv η (σ * ξ)) * ((2 * Real.pi * Complex.I * c)
            * Complex.exp (2 * Real.pi * Complex.I * (c * ξ)))
        + η (σ * ξ) * ((2 * Real.pi * Complex.I * c)
            * ((2 * Real.pi * Complex.I * c)
              * Complex.exp (2 * Real.pi * Complex.I * (c * ξ)))))‖
      = |ξ| ^ 2 * ‖ε * ((σ : ℂ) * ((σ : ℂ) * iteratedDeriv 2 η (σ * ξ))
            * (Complex.exp (2 * Real.pi * Complex.I * (c * ξ)) - 1)
          + ((σ : ℂ) * deriv η (σ * ξ)) * ((2 * Real.pi * Complex.I * (c : ℂ))
              * Complex.exp (2 * Real.pi * Complex.I * (c * ξ)))
          + ((σ : ℂ) * deriv η (σ * ξ)) * ((2 * Real.pi * Complex.I * (c : ℂ))
              * Complex.exp (2 * Real.pi * Complex.I * (c * ξ)))
          + η (σ * ξ) * ((2 * Real.pi * Complex.I * (c : ℂ))
              * ((2 * Real.pi * Complex.I * (c : ℂ))
                * Complex.exp (2 * Real.pi * Complex.I * (c * ξ)))))‖ := by ring_nf
    _ ≤ |ξ| ^ 2 * (2 * Real.pi * K * M2 * σ ^ 3 * |ξ|
          + (4 * Real.pi * K * M1 * σ ^ 2 + 4 * Real.pi ^ 2 * K ^ 2 * M0 * σ ^ 2)) :=
        mul_le_mul_of_nonneg_left hmid (sq_nonneg |ξ|)
    _ = 2 * Real.pi * K * M2 * (σ * |ξ|) ^ 3
          + (4 * Real.pi * K * M1 * (σ * |ξ|) ^ 2 + 4 * Real.pi ^ 2 * K ^ 2 * M0 * (σ * |ξ|) ^ 2) := by
        ring
    _ ≤ (2 * Real.pi * K * M2 + 4 * Real.pi * K * M1 + 4 * Real.pi ^ 2 * K ^ 2 * M0) * (σ * |ξ|) := by
        have h0 : 0 ≤ σ * |ξ| := mul_nonneg hσ.le (abs_nonneg ξ)
        have h2 : (σ * |ξ|) ^ 2 ≤ σ * |ξ| := pow_two_le_self_of_le_one h0 hξ
        have h3 : (σ * |ξ|) ^ 3 ≤ σ * |ξ| := pow_three_le_self_of_le_one h0 hξ
        have e1 : 2 * Real.pi * K * M2 * (σ * |ξ|) ^ 3
            ≤ 2 * Real.pi * K * M2 * (σ * |ξ|) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
        have e2 : 4 * Real.pi * K * M1 * (σ * |ξ|) ^ 2
            ≤ 4 * Real.pi * K * M1 * (σ * |ξ|) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
        have e3 : 4 * Real.pi ^ 2 * K ^ 2 * M0 * (σ * |ξ|) ^ 2
            ≤ 4 * Real.pi ^ 2 * K ^ 2 * M0 * (σ * |ξ|) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
        linarith


/-! ## The criterion -/

/-- **The Mikhlin/Hörmander criterion for the finite difference symbol, with a general shift
constant `K`.**  This is `Work.KMTAreas.A7.lacunaryDiffSymbol_mikhlin` with the hypothesis
`|c i| ≤ 2 σ i` relaxed to `|c i| ≤ K σ i`. -/
theorem lacunaryDiffSymbol_mikhlin_const (η : ℝ → ℂ) (M0 M1 M2 : ℝ) (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1)
    (hM2 : 0 ≤ M2) (hηcd : ContDiff ℝ 2 η)
    (hη0 : ∀ y : ℝ, |y| ≤ 1 → ‖η y‖ ≤ M0)
    (hη1 : ∀ y : ℝ, |y| ≤ 1 → ‖deriv η y‖ ≤ M1)
    (hη2 : ∀ y : ℝ, |y| ≤ 1 → ‖iteratedDeriv 2 η y‖ ≤ M2)
    (hηs0 : ∀ y : ℝ, 1 ≤ |y| → η y = 0)
    (hηs1 : ∀ y : ℝ, 1 ≤ |y| → deriv η y = 0)
    (hηs2 : ∀ y : ℝ, 1 ≤ |y| → iteratedDeriv 2 η y = 0)
    (hηd : ∀ y : ℝ, HasDerivAt η (deriv η y) y)
    (hηd2 : ∀ y : ℝ, HasDerivAt (deriv η) (iteratedDeriv 2 η y) y)
    (K : ℝ) (hK : 0 ≤ K) (lam : ℝ) (hlam : 1 < lam) :
    ∃ A : ℝ, 0 < A ∧ ∀ {ι : Type*} (D : Finset ι) (σ c : ι → ℝ) (ε : ι → ℂ),
      Work.Analysis.CzShift.LacunaryFam lam D σ → (∀ i ∈ D, |c i| ≤ K * σ i) →
      (∀ i ∈ D, ‖ε i‖ ≤ 1) →
      ContDiff ℝ 2 (fun ξ : ℝ => ∑ i ∈ D, ε i * (η (σ i * ξ) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1))) ∧
      (∀ ξ : ℝ, ‖∑ i ∈ D, ε i * (η (σ i * ξ) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1))‖ ≤ A) ∧
      (∀ ξ : ℝ, |ξ| * ‖deriv (fun ξ : ℝ => ∑ i ∈ D, ε i * (η (σ i * ξ) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1))) ξ‖ ≤ A) ∧
      (∀ ξ : ℝ, |ξ| ^ 2 * ‖iteratedDeriv 2 (fun ξ : ℝ => ∑ i ∈ D, ε i * (η (σ i * ξ) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1))) ξ‖ ≤ A) := by
  have hη0all : ∀ y : ℝ, ‖η y‖ ≤ M0 := by
    intro y
    by_cases h : |y| ≤ 1
    · exact hη0 y h
    · have h1 : 1 ≤ |y| := le_of_lt (not_le.mp h)
      rw [hηs0 y h1, norm_zero]
      exact hM0
  have hη1all : ∀ y : ℝ, ‖deriv η y‖ ≤ M1 := by
    intro y
    by_cases h : |y| ≤ 1
    · exact hη1 y h
    · have h1 : 1 ≤ |y| := le_of_lt (not_le.mp h)
      rw [hηs1 y h1, norm_zero]
      exact hM1
  have hη2all : ∀ y : ℝ, ‖iteratedDeriv 2 η y‖ ≤ M2 := by
    intro y
    by_cases h : |y| ≤ 1
    · exact hη2 y h
    · have h1 : 1 ≤ |y| := le_of_lt (not_le.mp h)
      rw [hηs2 y h1, norm_zero]
      exact hM2
  have hden : 0 < 1 - lam⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ hlam)
  set Kr : ℝ := 2 / (1 - lam⁻¹) with hKrdef
  have hKrpos : 0 < Kr := by rw [hKrdef]; exact div_pos two_pos hden
  have hKC : ∀ C : ℝ, 2 * C / (1 - lam⁻¹) = Kr * C := by
    intro C
    rw [hKrdef, div_eq_mul_inv, div_eq_mul_inv]
    ring
  set C0 : ℝ := 2 * Real.pi * K * M0 with hC0def
  set C1 : ℝ := 2 * Real.pi * K * M1 + 2 * Real.pi * K * M0 with hC1def
  set C2 : ℝ := 2 * Real.pi * K * M2 + 4 * Real.pi * K * M1 + 4 * Real.pi ^ 2 * K ^ 2 * M0
    with hC2def
  have hC0nn : 0 ≤ C0 := by rw [hC0def]; positivity
  have hC1nn : 0 ≤ C1 := by rw [hC1def]; positivity
  have hC2nn : 0 ≤ C2 := by rw [hC2def]; positivity
  set B : ℝ := C0 + C1 + C2 with hBdef
  have hBnn : 0 ≤ B := by rw [hBdef]; linarith
  have hAB0 : C0 ≤ B := by rw [hBdef]; linarith
  have hAB1 : C1 ≤ B := by rw [hBdef]; linarith
  have hAB2 : C2 ≤ B := by rw [hBdef]; linarith
  have hApos : 0 < 1 + Kr * B := by
    have : 0 ≤ Kr * B := mul_nonneg hKrpos.le hBnn
    linarith
  refine ⟨1 + Kr * B, hApos, ?_⟩
  intro ι D σ c ε hlac hc hε
  obtain ⟨hFcd, hFd1, hFd2⟩ := diffSymbol_contDiff_deriv η hηcd hηd hηd2 D σ c ε
  refine ⟨hFcd, ?_, ?_, ?_⟩
  · -- ## the pointwise bound
    intro ξ
    by_cases hξ : ξ = 0
    · rw [hξ]
      have h0 : (∑ i ∈ D, ε i * (η (σ i * (0 : ℝ))
          * (Complex.exp (2 * Real.pi * Complex.I * (c i * (0 : ℝ))) - 1))) = 0 := by
        simp [Complex.exp_zero]
      rw [h0, norm_zero]
      exact le_of_lt hApos
    · have hf : ∀ i ∈ D, σ i * |ξ| ≤ 1 →
          ‖ε i * (η (σ i * ξ) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1))‖
            ≤ C0 * (σ i * |ξ|) := by
        intro i hi _
        rw [hC0def]
        exact diffTerm_value_bound hM0 hη0all (hc i hi) (hε i hi) ξ
      have hzero : ∀ i ∈ D, 1 < σ i * |ξ| →
          ε i * (η (σ i * ξ) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1)) = 0 := by
        intro i hi ht
        have hσi : 0 < σ i := hlac.1 i hi
        have hlt : 1 ≤ |σ i * ξ| := by rw [abs_mul, abs_of_pos hσi]; exact ht.le
        rw [hηs0 (σ i * ξ) hlt]
        ring
      calc ‖∑ i ∈ D, ε i * (η (σ i * ξ)
            * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1))‖
          ≤ ∑ i ∈ D, ‖ε i * (η (σ i * ξ)
              * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1))‖ := norm_sum_le _ _
        _ ≤ 2 * C0 / (1 - lam⁻¹) := lacunarySum_norm_bound hlam hlac hξ hC0nn hf hzero
        _ = Kr * C0 := hKC C0
        _ ≤ 1 + Kr * B := by
            have hmul : Kr * C0 ≤ Kr * B := mul_le_mul_of_nonneg_left hAB0 hKrpos.le
            linarith
  · -- ## the first derivative bound
    intro ξ
    have hderiv : deriv (fun ξ : ℝ => ∑ i ∈ D, ε i * (η (σ i * ξ)
          * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1))) ξ
        = ∑ i ∈ D, ε i * (σ i * deriv η (σ i * ξ)
            * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1)
            + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i)
              * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))) := (hFd1 ξ).deriv
    rw [hderiv]
    by_cases hξ : ξ = 0
    · rw [hξ, abs_zero, zero_mul]
      exact le_of_lt hApos
    · have hf1 : ∀ i ∈ D, σ i * |ξ| ≤ 1 →
          ‖(|ξ| : ℝ) • (ε i * (σ i * deriv η (σ i * ξ)
            * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1)
            + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i)
              * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))))‖
            ≤ C1 * (σ i * |ξ|) := by
        intro i hi ht
        have hσi : 0 < σ i := hlac.1 i hi
        have hsmul : ‖(|ξ| : ℝ) • (ε i * (σ i * deriv η (σ i * ξ)
            * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1)
            + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i)
              * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))))‖
            = |ξ| * ‖ε i * (σ i * deriv η (σ i * ξ)
            * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1)
            + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i)
              * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))))‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_abs]
        rw [hsmul, hC1def]
        exact diffTerm_deriv_bound hM0 hM1 hK hη0all hη1all hσi (hc i hi) (hε i hi) ht
      have hzero1 : ∀ i ∈ D, 1 < σ i * |ξ| →
          (|ξ| : ℝ) • (ε i * (σ i * deriv η (σ i * ξ)
            * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1)
            + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i)
              * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))))) = 0 := by
        intro i hi ht
        have hσi : 0 < σ i := hlac.1 i hi
        have hlt : 1 ≤ |σ i * ξ| := by rw [abs_mul, abs_of_pos hσi]; exact ht.le
        rw [hηs0 (σ i * ξ) hlt, hηs1 (σ i * ξ) hlt]
        simp
      have hpush1 : (|ξ| : ℝ) • (∑ i ∈ D, ε i * (σ i * deriv η (σ i * ξ)
            * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1)
            + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i)
              * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))))
          = ∑ i ∈ D, (|ξ| : ℝ) • (ε i * (σ i * deriv η (σ i * ξ)
            * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1)
            + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i)
              * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))))) := Finset.smul_sum
      calc |ξ| * ‖∑ i ∈ D, ε i * (σ i * deriv η (σ i * ξ)
            * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1)
            + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i)
              * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))))‖
          = ‖(|ξ| : ℝ) • (∑ i ∈ D, ε i * (σ i * deriv η (σ i * ξ)
            * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1)
            + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i)
              * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))))‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_abs]
        _ = ‖∑ i ∈ D, (|ξ| : ℝ) • (ε i * (σ i * deriv η (σ i * ξ)
            * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1)
            + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i)
              * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))))‖ := by rw [hpush1]
        _ ≤ ∑ i ∈ D, ‖(|ξ| : ℝ) • (ε i * (σ i * deriv η (σ i * ξ)
            * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1)
            + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i)
              * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))))‖ := norm_sum_le _ _
        _ ≤ 2 * C1 / (1 - lam⁻¹) := lacunarySum_norm_bound hlam hlac hξ hC1nn hf1 hzero1
        _ = Kr * C1 := hKC C1
        _ ≤ 1 + Kr * B := by
            have hmul : Kr * C1 ≤ Kr * B := mul_le_mul_of_nonneg_left hAB1 hKrpos.le
            linarith
  · -- ## the second derivative bound
    intro ξ
    have hderiv2 : iteratedDeriv 2 (fun ξ : ℝ => ∑ i ∈ D, ε i * (η (σ i * ξ)
          * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1))) ξ
        = ∑ i ∈ D, ε i * (σ i * (σ i * iteratedDeriv 2 η (σ i * ξ))
            * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1)
            + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i)
              * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))
            + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i)
              * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))
            + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i)
              * ((2 * Real.pi * Complex.I * c i)
                * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))))) := by
      have hfun : deriv (fun ξ : ℝ => ∑ i ∈ D, ε i * (η (σ i * ξ)
            * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1)))
          = (fun ξ : ℝ => ∑ i ∈ D, ε i * (σ i * deriv η (σ i * ξ)
              * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1)
              + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i)
                * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))))) :=
        funext (fun ξ => (hFd1 ξ).deriv)
      calc iteratedDeriv 2 (fun ξ : ℝ => ∑ i ∈ D, ε i * (η (σ i * ξ)
              * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1))) ξ
          = deriv (iteratedDeriv 1 (fun ξ : ℝ => ∑ i ∈ D, ε i * (η (σ i * ξ)
              * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1)))) ξ := by
              rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ]
        _ = deriv (deriv (fun ξ : ℝ => ∑ i ∈ D, ε i * (η (σ i * ξ)
              * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1)))) ξ := by
              rw [iteratedDeriv_one]
        _ = deriv (fun ξ : ℝ => ∑ i ∈ D, ε i * (σ i * deriv η (σ i * ξ)
              * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1)
              + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i)
                * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))))) ξ := by rw [hfun]
        _ = ∑ i ∈ D, ε i * (σ i * (σ i * iteratedDeriv 2 η (σ i * ξ))
            * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1)
            + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i)
              * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))
            + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i)
              * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))
            + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i)
              * ((2 * Real.pi * Complex.I * c i)
                * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))))) := (hFd2 ξ).deriv
    rw [hderiv2]
    by_cases hξ : ξ = 0
    · rw [hξ, abs_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]
      exact le_of_lt hApos
    · have hf2 : ∀ i ∈ D, σ i * |ξ| ≤ 1 →
          ‖(|ξ| ^ 2 : ℝ) • (ε i * (σ i * (σ i * iteratedDeriv 2 η (σ i * ξ))
            * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1)
            + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i)
              * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))
            + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i)
              * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))
            + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i)
              * ((2 * Real.pi * Complex.I * c i)
                * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))))))‖
            ≤ C2 * (σ i * |ξ|) := by
        intro i hi ht
        have hσi : 0 < σ i := hlac.1 i hi
        have hsmul : ‖(|ξ| ^ 2 : ℝ) • (ε i * (σ i * (σ i * iteratedDeriv 2 η (σ i * ξ))
            * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1)
            + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i)
              * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))
            + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i)
              * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))
            + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i)
              * ((2 * Real.pi * Complex.I * c i)
                * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))))))‖
            = |ξ| ^ 2 * ‖ε i * (σ i * (σ i * iteratedDeriv 2 η (σ i * ξ))
            * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1)
            + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i)
              * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))
            + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i)
              * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))
            + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i)
              * ((2 * Real.pi * Complex.I * c i)
                * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))))‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg |ξ|)]
        rw [hsmul, hC2def]
        exact diffTerm_deriv2_bound hM0 hM1 hM2 hK hη0all hη1all hη2all hσi (hc i hi)
          (hε i hi) ht
      have hzero2 : ∀ i ∈ D, 1 < σ i * |ξ| →
          (|ξ| ^ 2 : ℝ) • (ε i * (σ i * (σ i * iteratedDeriv 2 η (σ i * ξ))
            * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1)
            + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i)
              * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))
            + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i)
              * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))
            + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i)
              * ((2 * Real.pi * Complex.I * c i)
                * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))))) = 0 := by
        intro i hi ht
        have hσi : 0 < σ i := hlac.1 i hi
        have hlt : 1 ≤ |σ i * ξ| := by rw [abs_mul, abs_of_pos hσi]; exact ht.le
        rw [hηs0 (σ i * ξ) hlt, hηs1 (σ i * ξ) hlt, hηs2 (σ i * ξ) hlt]
        simp
      have hpush2 : (|ξ| ^ 2 : ℝ) • (∑ i ∈ D, ε i * (σ i * (σ i * iteratedDeriv 2 η (σ i * ξ))
            * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1)
            + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i)
              * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))
            + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i)
              * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))
            + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i)
              * ((2 * Real.pi * Complex.I * c i)
                * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))))))
          = ∑ i ∈ D, (|ξ| ^ 2 : ℝ) • (ε i * (σ i * (σ i * iteratedDeriv 2 η (σ i * ξ))
            * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1)
            + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i)
              * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))
            + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i)
              * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))
            + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i)
              * ((2 * Real.pi * Complex.I * c i)
                * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))))) := Finset.smul_sum
      calc |ξ| ^ 2 * ‖∑ i ∈ D, ε i * (σ i * (σ i * iteratedDeriv 2 η (σ i * ξ))
            * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1)
            + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i)
              * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))
            + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i)
              * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))
            + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i)
              * ((2 * Real.pi * Complex.I * c i)
                * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))))‖
          = ‖(|ξ| ^ 2 : ℝ) • (∑ i ∈ D, ε i * (σ i * (σ i * iteratedDeriv 2 η (σ i * ξ))
            * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1)
            + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i)
              * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))
            + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i)
              * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))
            + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i)
              * ((2 * Real.pi * Complex.I * c i)
                * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))))))‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg |ξ|)]
        _ = ‖∑ i ∈ D, (|ξ| ^ 2 : ℝ) • (ε i * (σ i * (σ i * iteratedDeriv 2 η (σ i * ξ))
            * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1)
            + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i)
              * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))
            + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i)
              * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))
            + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i)
              * ((2 * Real.pi * Complex.I * c i)
                * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))))))‖ := by rw [hpush2]
        _ ≤ ∑ i ∈ D, ‖(|ξ| ^ 2 : ℝ) • (ε i * (σ i * (σ i * iteratedDeriv 2 η (σ i * ξ))
            * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1)
            + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i)
              * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))
            + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i)
              * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))
            + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i)
              * ((2 * Real.pi * Complex.I * c i)
                * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))))))‖ := norm_sum_le _ _
        _ ≤ 2 * C2 / (1 - lam⁻¹) := lacunarySum_norm_bound hlam hlac hξ hC2nn hf2 hzero2
        _ = Kr * C2 := hKC C2
        _ ≤ 1 + Kr * B := by
            have hmul : Kr * C2 ≤ Kr * B := mul_le_mul_of_nonneg_left hAB2 hKrpos.le
            linarith

end

end Work.KMTAreas.A7
