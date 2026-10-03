import Mathlib
import Submission.Work.KMTAreas.A7.lacunarySum_norm_bound
import Submission.Work.KMTAreas.A7.diffSymbol_contDiff_deriv

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTAreas.A7

open Finset

private lemma pow_two_le_self_of_le_one {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : t ^ 2 ≤ t := by nlinarith

private lemma pow_three_le_self_of_le_one {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : t ^ 3 ≤ t := by
  have h2 : t ^ 2 ≤ 1 := by nlinarith
  calc t ^ 3 = t ^ 2 * t := by ring
    _ ≤ 1 * t := mul_le_mul_of_nonneg_right h2 h0
    _ = t := one_mul t

private lemma norm_two_pi_I_mul (a b : ℝ) :
    ‖(2 * Real.pi * Complex.I * ((a : ℂ) * (b : ℂ)) : ℂ)‖ = 2 * Real.pi * (|a| * |b|) := by
  have h : (2 * Real.pi * Complex.I * ((a : ℂ) * (b : ℂ)) : ℂ)
      = Complex.I * (((2 * Real.pi * (a*b) : ℝ)) : ℂ) := by push_cast; ring
  rw [h, Complex.norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_mul, abs_mul, abs_mul, abs_of_pos Real.pi_pos,
    abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]

private lemma norm_two_pi_I_mul_real (a : ℝ) :
    ‖(2 * Real.pi * Complex.I * (a : ℂ) : ℂ)‖ = 2 * Real.pi * |a| := by
  have h : (2 * Real.pi * Complex.I * (a : ℂ) : ℂ)
      = 2 * Real.pi * Complex.I * ((a : ℂ) * (1 : ℂ)) := by ring
  have hh := norm_two_pi_I_mul a 1
  simpa using hh

private lemma norm_exp_two_pi_I_mul (a b : ℝ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * (b : ℂ)))‖ = 1 := by
  have h : (2 * Real.pi * Complex.I * ((a : ℂ) * (b : ℂ)) : ℂ)
      = Complex.I * (((2 * Real.pi * (a*b) : ℝ)) : ℂ) := by push_cast; ring
  rw [h, Complex.norm_exp_I_mul_ofReal]

private lemma norm_exp_two_pi_I_mul_sub_one_le (a b : ℝ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * (b : ℂ))) - 1‖
      ≤ 2 * Real.pi * (|a| * |b|) := by
  have h : (2 * Real.pi * Complex.I * ((a : ℂ) * (b : ℂ)) : ℂ)
      = Complex.I * (((2 * Real.pi * (a*b) : ℝ)) : ℂ) := by push_cast; ring
  rw [h, Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show (2 * Real.pi * (a * b)) / 2 = Real.pi * (a * b) by ring]
  rw [Real.norm_eq_abs, abs_mul, show |(2:ℝ)| = 2 by norm_num]
  have h3 : |Real.sin (Real.pi * (a * b))| ≤ Real.pi * (|a| * |b|) := by
    calc |Real.sin (Real.pi * (a * b))| ≤ |Real.pi * (a * b)| := Real.abs_sin_le_abs
      _ = Real.pi * (|a| * |b|) := by rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos]
  linarith

theorem lacunaryDiffSymbol_mikhlin (η : ℝ → ℂ) (M0 M1 M2 : ℝ) (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1)
    (hM2 : 0 ≤ M2) (hηcd : ContDiff ℝ 2 η)
    (hη0 : ∀ y : ℝ, |y| ≤ 1 → ‖η y‖ ≤ M0)
    (hη1 : ∀ y : ℝ, |y| ≤ 1 → ‖deriv η y‖ ≤ M1)
    (hη2 : ∀ y : ℝ, |y| ≤ 1 → ‖iteratedDeriv 2 η y‖ ≤ M2)
    (hηs0 : ∀ y : ℝ, 1 ≤ |y| → η y = 0)
    (hηs1 : ∀ y : ℝ, 1 ≤ |y| → deriv η y = 0)
    (hηs2 : ∀ y : ℝ, 1 ≤ |y| → iteratedDeriv 2 η y = 0)
    (hηd : ∀ y : ℝ, HasDerivAt η (deriv η y) y)
    (hηd2 : ∀ y : ℝ, HasDerivAt (deriv η) (iteratedDeriv 2 η y) y)
    (lam : ℝ) (hlam : 1 < lam) :
    ∃ A : ℝ, 0 < A ∧ ∀ {ι : Type*} (D : Finset ι) (σ c : ι → ℝ) (ε : ι → ℂ),
      Work.Analysis.CzShift.LacunaryFam lam D σ → (∀ i ∈ D, |c i| ≤ 2 * σ i) →
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
  have hKpos : 0 < 1 - lam⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ hlam)
  let K : ℝ := 2 / (1 - lam⁻¹)
  let B : ℝ := 4 * Real.pi * M0 + (4 * Real.pi * M1 + 4 * Real.pi * M0)
    + (4 * Real.pi * M2 + 8 * Real.pi * M1 + 16 * Real.pi ^ 2 * M0)
  have hKpos' : 0 < K := by
    show 0 < 2 / (1 - lam⁻¹)
    exact div_pos two_pos hKpos
  have hBnn : 0 ≤ B := by
    show 0 ≤ 4 * Real.pi * M0 + (4 * Real.pi * M1 + 4 * Real.pi * M0)
      + (4 * Real.pi * M2 + 8 * Real.pi * M1 + 16 * Real.pi ^ 2 * M0)
    positivity
  have hKC : ∀ C : ℝ, 2 * C / (1 - lam⁻¹) = K * C := by
    intro C
    show 2 * C / (1 - lam⁻¹) = (2 / (1 - lam⁻¹)) * C
    rw [div_eq_mul_inv, div_eq_mul_inv]; ring
  have hA0 : 4 * Real.pi * M0 ≤ B := by
    show 4 * Real.pi * M0 ≤ 4 * Real.pi * M0 + (4 * Real.pi * M1 + 4 * Real.pi * M0)
      + (4 * Real.pi * M2 + 8 * Real.pi * M1 + 16 * Real.pi ^ 2 * M0)
    have h1 : 0 ≤ 4 * Real.pi * M1 + 4 * Real.pi * M0 := by positivity
    have h2 : 0 ≤ 4 * Real.pi * M2 + 8 * Real.pi * M1 + 16 * Real.pi ^ 2 * M0 := by positivity
    linarith
  have hA1 : 4 * Real.pi * M1 + 4 * Real.pi * M0 ≤ B := by
    show 4 * Real.pi * M1 + 4 * Real.pi * M0 ≤ 4 * Real.pi * M0 + (4 * Real.pi * M1 + 4 * Real.pi * M0)
      + (4 * Real.pi * M2 + 8 * Real.pi * M1 + 16 * Real.pi ^ 2 * M0)
    have h1 : 0 ≤ 4 * Real.pi * M0 := by positivity
    have h2 : 0 ≤ 4 * Real.pi * M2 + 8 * Real.pi * M1 + 16 * Real.pi ^ 2 * M0 := by positivity
    linarith
  have hA2 : 4 * Real.pi * M2 + 8 * Real.pi * M1 + 16 * Real.pi ^ 2 * M0 ≤ B := by
    show 4 * Real.pi * M2 + 8 * Real.pi * M1 + 16 * Real.pi ^ 2 * M0
      ≤ 4 * Real.pi * M0 + (4 * Real.pi * M1 + 4 * Real.pi * M0)
      + (4 * Real.pi * M2 + 8 * Real.pi * M1 + 16 * Real.pi ^ 2 * M0)
    have h1 : 0 ≤ 4 * Real.pi * M0 := by positivity
    have h2 : 0 ≤ 4 * Real.pi * M1 + 4 * Real.pi * M0 := by positivity
    linarith
  refine ⟨1 + K * B, ?_, ?_⟩
  · have : 0 ≤ K * B := mul_nonneg hKpos'.le hBnn
    linarith
  intro ι D σ c ε hlac hc hε
  obtain ⟨hFcd, hFd1, hFd2⟩ := diffSymbol_contDiff_deriv η hηcd hηd hηd2 D σ c ε
  refine ⟨hFcd, ?_, ?_, ?_⟩
  · -- ## pointwise bound
    intro ξ
    by_cases hξ : ξ = 0
    · rw [hξ]
      have h0 : (∑ i ∈ D, ε i * (η (σ i * (0:ℝ)) * (Complex.exp (2 * Real.pi * Complex.I * (c i * (0:ℝ))) - 1))) = 0 := by
        simp [Complex.exp_zero]
      rw [h0, norm_zero]
      positivity
    · have hC0 : (0:ℝ) ≤ 4 * Real.pi * M0 := by positivity
      have hf : ∀ i ∈ D, σ i * |ξ| ≤ 1 →
          ‖ε i * (η (σ i * ξ) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1))‖ ≤ (4 * Real.pi * M0) * (σ i * |ξ|) := by
        intro i hi ht
        have hE := norm_exp_two_pi_I_mul_sub_one_le (c i) ξ
        have hcx : |c i| * |ξ| ≤ 2 * σ i * |ξ| :=
          mul_le_mul_of_nonneg_right (hc i hi) (abs_nonneg ξ)
        have h1 : ‖η (σ i * ξ)‖ * ‖Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1‖ ≤ M0 * (2 * Real.pi * (|c i| * |ξ|)) :=
          mul_le_mul (hη0all _) hE (norm_nonneg _) hM0
        have h2 : 2 * Real.pi * (|c i| * |ξ|) ≤ 2 * Real.pi * (2 * σ i * |ξ|) :=
          mul_le_mul_of_nonneg_left hcx (by positivity)
        have h3 : M0 * (2 * Real.pi * (|c i| * |ξ|)) ≤ M0 * (2 * Real.pi * (2 * σ i * |ξ|)) :=
          mul_le_mul_of_nonneg_left h2 hM0
        calc ‖ε i * (η (σ i * ξ) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1))‖
            ≤ ‖ε i‖ * (‖η (σ i * ξ)‖ * ‖Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1‖) := by rw [norm_mul, norm_mul]
          _ ≤ 1 * (M0 * (2 * Real.pi * (|c i| * |ξ|))) :=
              mul_le_mul (hε i hi) h1 (mul_nonneg (norm_nonneg _) (norm_nonneg _)) zero_le_one
          _ ≤ 1 * (M0 * (2 * Real.pi * (2 * σ i * |ξ|))) :=
              mul_le_mul_of_nonneg_left h3 zero_le_one
          _ = (4 * Real.pi * M0) * (σ i * |ξ|) := by ring
      have hzero : ∀ i ∈ D, 1 < σ i * |ξ| → ε i * (η (σ i * ξ) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1)) = 0 := by
        intro i hi ht
        have hσi : 0 < σ i := hlac.1 i hi
        have hlt : 1 ≤ |σ i * ξ| := by rw [abs_mul, abs_of_pos hσi]; exact ht.le
        rw [hηs0 (σ i * ξ) hlt]
        ring
      have hsum := lacunarySum_norm_bound hlam hlac hξ hC0 hf hzero
      calc ‖∑ i ∈ D, ε i * (η (σ i * ξ) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1))‖
          ≤ ∑ i ∈ D, ‖ε i * (η (σ i * ξ) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1))‖ := norm_sum_le _ _
        _ ≤ 2 * (4 * Real.pi * M0) / (1 - lam⁻¹) := hsum
        _ = K * (4 * Real.pi * M0) := hKC _
        _ ≤ 1 + K * B := by
            have hmul : K * (4 * Real.pi * M0) ≤ K * B :=
              mul_le_mul_of_nonneg_left hA0 hKpos'.le
            linarith
  · -- ## first derivative bound
    intro ξ
    have hderiv : deriv (fun ξ : ℝ => ∑ i ∈ D, ε i * (η (σ i * ξ) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1))) ξ = ∑ i ∈ D, ε i * (σ i * deriv η (σ i * ξ) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1) + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))) := (hFd1 ξ).deriv
    rw [hderiv]
    by_cases hξ : ξ = 0
    · rw [hξ, abs_zero, zero_mul]
      positivity
    · have hC1 : (0:ℝ) ≤ 4 * Real.pi * M1 + 4 * Real.pi * M0 := by positivity
      have hf1 : ∀ i ∈ D, σ i * |ξ| ≤ 1 →
          ‖(|ξ| : ℝ) • (ε i * (σ i * deriv η (σ i * ξ) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1) + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))))‖
            ≤ (4 * Real.pi * M1 + 4 * Real.pi * M0) * (σ i * |ξ|) := by
        intro i hi ht
        have hσi : 0 < σ i := hlac.1 i hi
        have hσc : ‖(σ i : ℂ)‖ = σ i := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hσi.le]
        have hE1 : ‖Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1‖ ≤ 2 * Real.pi * (|c i| * |ξ|) :=
          norm_exp_two_pi_I_mul_sub_one_le (c i) ξ
        have hE2 : ‖Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))‖ = 1 := norm_exp_two_pi_I_mul (c i) ξ
        have hcx : |c i| * |ξ| ≤ 2 * σ i * |ξ| :=
          mul_le_mul_of_nonneg_right (hc i hi) (abs_nonneg ξ)
        have hp1 : ‖σ i * deriv η (σ i * ξ) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1)‖ ≤ 4 * Real.pi * M1 * σ i ^ 2 * |ξ| := by
          have hA : ‖deriv η (σ i * ξ)‖ ≤ M1 := hη1all _
          have hmul : ‖σ i * deriv η (σ i * ξ)‖ ≤ σ i * M1 := by
            calc ‖(σ i : ℂ) * deriv η (σ i * ξ)‖
                ≤ ‖(σ i : ℂ)‖ * ‖deriv η (σ i * ξ)‖ := norm_mul_le _ _
              _ = σ i * ‖deriv η (σ i * ξ)‖ := by rw [hσc]
              _ ≤ σ i * M1 := mul_le_mul_of_nonneg_left hA hσi.le
          have hkey : ‖deriv η (σ i * ξ)‖ * ‖Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1‖ ≤ M1 * (2 * Real.pi * (|c i| * |ξ|)) :=
            mul_le_mul hA hE1 (norm_nonneg _) hM1
          calc ‖σ i * deriv η (σ i * ξ) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1)‖ ≤ ‖(σ i : ℂ) * deriv η (σ i * ξ)‖ * ‖Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1‖ := norm_mul_le _ _
            _ ≤ (σ i * M1) * (2 * Real.pi * (|c i| * |ξ|)) :=
                mul_le_mul hmul hE1 (norm_nonneg _) (by positivity)
            _ ≤ (σ i * M1) * (2 * Real.pi * (2 * σ i * |ξ|)) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                exact mul_le_mul_of_nonneg_left hcx (by positivity)
            _ = 4 * Real.pi * M1 * σ i ^ 2 * |ξ| := by ring
        have hp2 : ‖η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))‖ ≤ 4 * Real.pi * M0 * σ i := by
          have hB2 : ‖(2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))‖ = 2 * Real.pi * |c i| := by
            rw [norm_mul, norm_two_pi_I_mul_real, hE2, mul_one]
          calc ‖η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))‖ ≤ ‖η (σ i * ξ)‖ * ‖(2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))‖ :=
                norm_mul_le _ _
            _ = ‖η (σ i * ξ)‖ * (2 * Real.pi * |c i|) := by rw [hB2]
            _ ≤ M0 * (2 * Real.pi * |c i|) :=
                mul_le_mul_of_nonneg_right (hη0all _) (by positivity)
            _ ≤ M0 * (2 * Real.pi * (2 * σ i)) := by
                apply mul_le_mul_of_nonneg_left _ hM0
                exact mul_le_mul_of_nonneg_left (hc i hi) (by positivity)
            _ = 4 * Real.pi * M0 * σ i := by ring
        have hmid : ‖ε i * (σ i * deriv η (σ i * ξ) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1) + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))))‖
            ≤ 4 * Real.pi * M1 * σ i ^ 2 * |ξ| + 4 * Real.pi * M0 * σ i := by
          have hAB : ‖σ i * deriv η (σ i * ξ) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1) + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))‖ ≤ ‖σ i * deriv η (σ i * ξ) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1)‖ + ‖η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))‖ := norm_add_le _ _
          calc ‖ε i * (σ i * deriv η (σ i * ξ) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1) + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))))‖ ≤ ‖ε i‖ * ‖σ i * deriv η (σ i * ξ) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1) + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))‖ := norm_mul_le _ _
            _ ≤ 1 * (‖σ i * deriv η (σ i * ξ) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1)‖ + ‖η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))‖) :=
                mul_le_mul (hε i hi) hAB (norm_nonneg _) zero_le_one
            _ = ‖σ i * deriv η (σ i * ξ) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1)‖ + ‖η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))‖ := one_mul _
            _ ≤ 4 * Real.pi * M1 * σ i ^ 2 * |ξ| + 4 * Real.pi * M0 * σ i := by linarith
        calc ‖(|ξ| : ℝ) • (ε i * (σ i * deriv η (σ i * ξ) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1) + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))))‖ = |ξ| * ‖ε i * (σ i * deriv η (σ i * ξ) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1) + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))))‖ := by
              rw [norm_smul, Real.norm_eq_abs, abs_abs]
          _ ≤ |ξ| * (4 * Real.pi * M1 * σ i ^ 2 * |ξ| + 4 * Real.pi * M0 * σ i) :=
              mul_le_mul_of_nonneg_left hmid (abs_nonneg ξ)
          _ = 4 * Real.pi * M1 * (σ i * |ξ|) ^ 2 + 4 * Real.pi * M0 * (σ i * |ξ|) := by ring
          _ ≤ (4 * Real.pi * M1 + 4 * Real.pi * M0) * (σ i * |ξ|) := by
              have h0 : 0 ≤ σ i * |ξ| := mul_nonneg hσi.le (abs_nonneg ξ)
              have h2 : (σ i * |ξ|) ^ 2 ≤ σ i * |ξ| := pow_two_le_self_of_le_one h0 ht
              have h4 : 4 * Real.pi * M1 * (σ i * |ξ|) ^ 2
                  ≤ 4 * Real.pi * M1 * (σ i * |ξ|) :=
                mul_le_mul_of_nonneg_left h2 (by positivity)
              linarith
      have hzero1 : ∀ i ∈ D, 1 < σ i * |ξ| → (|ξ| : ℝ) • (ε i * (σ i * deriv η (σ i * ξ) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1) + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))))) = 0 := by
        intro i hi ht
        have hσi : 0 < σ i := hlac.1 i hi
        have hlt : 1 ≤ |σ i * ξ| := by rw [abs_mul, abs_of_pos hσi]; exact ht.le
        rw [hηs0 (σ i * ξ) hlt, hηs1 (σ i * ξ) hlt]
        simp
      have hsum1 := lacunarySum_norm_bound hlam hlac hξ hC1 hf1 hzero1
      have hpush : (|ξ| : ℝ) • (∑ i ∈ D, ε i * (σ i * deriv η (σ i * ξ) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1) + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))))) = ∑ i ∈ D, (|ξ| : ℝ) • (ε i * (σ i * deriv η (σ i * ξ) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1) + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))))) := Finset.smul_sum
      calc |ξ| * ‖∑ i ∈ D, ε i * (σ i * deriv η (σ i * ξ) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1) + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))))‖ = ‖(|ξ| : ℝ) • (∑ i ∈ D, ε i * (σ i * deriv η (σ i * ξ) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1) + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))))‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_abs]
        _ = ‖∑ i ∈ D, (|ξ| : ℝ) • (ε i * (σ i * deriv η (σ i * ξ) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1) + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))))‖ := by rw [hpush]
        _ ≤ ∑ i ∈ D, ‖(|ξ| : ℝ) • (ε i * (σ i * deriv η (σ i * ξ) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1) + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))))‖ := norm_sum_le _ _
        _ ≤ 2 * (4 * Real.pi * M1 + 4 * Real.pi * M0) / (1 - lam⁻¹) := hsum1
        _ = K * (4 * Real.pi * M1 + 4 * Real.pi * M0) := hKC _
        _ ≤ 1 + K * B := by
            have hmul : K * (4 * Real.pi * M1 + 4 * Real.pi * M0) ≤ K * B :=
              mul_le_mul_of_nonneg_left hA1 hKpos'.le
            linarith
  · -- ## second derivative bound
    intro ξ
    have hderiv2 : iteratedDeriv 2 (fun ξ : ℝ => ∑ i ∈ D, ε i * (η (σ i * ξ) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1))) ξ = ∑ i ∈ D, ε i * (σ i * (σ i * iteratedDeriv 2 η (σ i * ξ)) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1) + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))) + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))) + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))))) := by
      have hfun : deriv (fun ξ : ℝ => ∑ i ∈ D, ε i * (η (σ i * ξ) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1))) = (fun ξ : ℝ => ∑ i ∈ D, ε i * (σ i * deriv η (σ i * ξ) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1) + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))))) := funext (fun ξ => (hFd1 ξ).deriv)
      calc iteratedDeriv 2 (fun ξ : ℝ => ∑ i ∈ D, ε i * (η (σ i * ξ) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1))) ξ
          = deriv (iteratedDeriv 1 (fun ξ : ℝ => ∑ i ∈ D, ε i * (η (σ i * ξ) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1)))) ξ := by
              rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ]
        _ = deriv (deriv (fun ξ : ℝ => ∑ i ∈ D, ε i * (η (σ i * ξ) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1)))) ξ := by rw [iteratedDeriv_one]
        _ = deriv (fun ξ : ℝ => ∑ i ∈ D, ε i * (σ i * deriv η (σ i * ξ) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1) + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))))) ξ := by rw [hfun]
        _ = ∑ i ∈ D, ε i * (σ i * (σ i * iteratedDeriv 2 η (σ i * ξ)) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1) + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))) + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))) + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))))) := (hFd2 ξ).deriv
    rw [hderiv2]
    by_cases hξ : ξ = 0
    · rw [hξ, abs_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0), zero_mul]
      positivity
    · have hC2 : (0:ℝ) ≤ 4 * Real.pi * M2 + 8 * Real.pi * M1 + 16 * Real.pi ^ 2 * M0 := by
        positivity
      have hf2 : ∀ i ∈ D, σ i * |ξ| ≤ 1 →
          ‖(|ξ| ^ 2 : ℝ) • (ε i * (σ i * (σ i * iteratedDeriv 2 η (σ i * ξ)) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1) + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))) + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))) + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))))))‖
            ≤ (4 * Real.pi * M2 + 8 * Real.pi * M1 + 16 * Real.pi ^ 2 * M0) * (σ i * |ξ|) := by
        intro i hi ht
        have hσi : 0 < σ i := hlac.1 i hi
        have hσc : ‖(σ i : ℂ)‖ = σ i := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hσi.le]
        have hE1 : ‖Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1‖ ≤ 2 * Real.pi * (|c i| * |ξ|) :=
          norm_exp_two_pi_I_mul_sub_one_le (c i) ξ
        have hE2 : ‖Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))‖ = 1 := norm_exp_two_pi_I_mul (c i) ξ
        have hcx : |c i| * |ξ| ≤ 2 * σ i * |ξ| :=
          mul_le_mul_of_nonneg_right (hc i hi) (abs_nonneg ξ)
        have hcx2 : 2 * Real.pi * |c i| ≤ 2 * Real.pi * (2 * σ i) :=
          mul_le_mul_of_nonneg_left (hc i hi) (by positivity)
        -- piece A2
        have hpA : ‖σ i * (σ i * iteratedDeriv 2 η (σ i * ξ)) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1)‖ ≤ 4 * Real.pi * M2 * σ i ^ 3 * |ξ| := by
          have hA : ‖iteratedDeriv 2 η (σ i * ξ)‖ ≤ M2 := hη2all _
          have hmul : ‖σ i * (σ i * iteratedDeriv 2 η (σ i * ξ))‖ ≤ σ i * (σ i * M2) := by
            calc ‖(σ i : ℂ) * ((σ i : ℂ) * iteratedDeriv 2 η (σ i * ξ))‖
                ≤ ‖(σ i : ℂ)‖ * ‖(σ i : ℂ) * iteratedDeriv 2 η (σ i * ξ)‖ := norm_mul_le _ _
              _ ≤ ‖(σ i : ℂ)‖ * (‖(σ i : ℂ)‖ * ‖iteratedDeriv 2 η (σ i * ξ)‖) :=
                  mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _)
              _ = σ i * (σ i * ‖iteratedDeriv 2 η (σ i * ξ)‖) := by rw [hσc]
              _ ≤ σ i * (σ i * M2) :=
                  mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hA hσi.le) hσi.le
          calc ‖σ i * (σ i * iteratedDeriv 2 η (σ i * ξ)) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1)‖ ≤ ‖σ i * (σ i * iteratedDeriv 2 η (σ i * ξ))‖ * ‖Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1‖ :=
                norm_mul_le _ _
            _ ≤ (σ i * (σ i * M2)) * (2 * Real.pi * (|c i| * |ξ|)) :=
                mul_le_mul hmul hE1 (norm_nonneg _) (by positivity)
            _ ≤ (σ i * (σ i * M2)) * (2 * Real.pi * (2 * σ i * |ξ|)) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                exact mul_le_mul_of_nonneg_left hcx (by positivity)
            _ = 4 * Real.pi * M2 * σ i ^ 3 * |ξ| := by ring
        -- piece B2
        have hpB : ‖(σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))‖ ≤ 4 * Real.pi * M1 * σ i ^ 2 := by
          have hmm : ‖σ i * deriv η (σ i * ξ)‖ ≤ σ i * M1 := by
            calc ‖(σ i : ℂ) * deriv η (σ i * ξ)‖
                ≤ ‖(σ i : ℂ)‖ * ‖deriv η (σ i * ξ)‖ := norm_mul_le _ _
              _ = σ i * ‖deriv η (σ i * ξ)‖ := by rw [hσc]
              _ ≤ σ i * M1 := mul_le_mul_of_nonneg_left (hη1all _) hσi.le
          have hB2 : ‖(2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))‖ = 2 * Real.pi * |c i| := by
            rw [norm_mul, norm_two_pi_I_mul_real, hE2, mul_one]
          calc ‖(σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))‖ ≤ ‖σ i * deriv η (σ i * ξ)‖ * ‖(2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))‖ :=
                norm_mul_le _ _
            _ ≤ (σ i * M1) * (2 * Real.pi * |c i|) :=
                mul_le_mul hmm (le_of_eq hB2) (norm_nonneg _) (by positivity)
            _ ≤ (σ i * M1) * (2 * Real.pi * (2 * σ i)) :=
                mul_le_mul_of_nonneg_left hcx2 (by positivity)
            _ = 4 * Real.pi * M1 * σ i ^ 2 := by ring
        -- piece C2
        have hpC : ‖η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))))‖ ≤ 16 * Real.pi ^ 2 * M0 * σ i ^ 2 := by
          have hB2 : ‖(2 * Real.pi * Complex.I * c i) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))‖
              = (2 * Real.pi * |c i|) * (2 * Real.pi * |c i|) := by
            have h4 : ‖(2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))‖ = 2 * Real.pi * |c i| := by
              rw [norm_mul, norm_two_pi_I_mul_real, hE2, mul_one]
            rw [norm_mul, norm_two_pi_I_mul_real, h4]
          calc ‖η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))))‖
              ≤ ‖η (σ i * ξ)‖ * ‖(2 * Real.pi * Complex.I * c i) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))‖ :=
                norm_mul_le _ _
            _ = ‖η (σ i * ξ)‖ * ((2 * Real.pi * |c i|) * (2 * Real.pi * |c i|)) := by rw [hB2]
            _ ≤ M0 * ((2 * Real.pi * |c i|) * (2 * Real.pi * |c i|)) :=
                mul_le_mul_of_nonneg_right (hη0all _) (by positivity)
            _ ≤ M0 * ((2 * Real.pi * (2 * σ i)) * (2 * Real.pi * (2 * σ i))) :=
                mul_le_mul_of_nonneg_left (mul_le_mul hcx2 hcx2 (by positivity) (by positivity)) hM0
            _ = 16 * Real.pi ^ 2 * M0 * σ i ^ 2 := by ring
        have hmid : ‖ε i * (σ i * (σ i * iteratedDeriv 2 η (σ i * ξ)) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1) + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))) + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))) + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))))‖
            ≤ 4 * Real.pi * M2 * σ i ^ 3 * |ξ|
              + (8 * Real.pi * M1 * σ i ^ 2 + 16 * Real.pi ^ 2 * M0 * σ i ^ 2) := by
          have h1 := norm_add_le ((σ i * (σ i * iteratedDeriv 2 η (σ i * ξ)) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1)) + ((σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))) + ((σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))))) (η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))))
          have h2 := norm_add_le ((σ i * (σ i * iteratedDeriv 2 η (σ i * ξ)) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1)) + ((σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))))) ((σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))))
          have h3 := norm_add_le (σ i * (σ i * iteratedDeriv 2 η (σ i * ξ)) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1)) ((σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))))
          have hABC : ‖σ i * (σ i * iteratedDeriv 2 η (σ i * ξ)) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1) + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))) + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))) + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))))‖ ≤ ‖σ i * (σ i * iteratedDeriv 2 η (σ i * ξ)) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1)‖ + ‖(σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))‖ + ‖(σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))‖ + ‖η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))))‖ := by linarith
          calc ‖ε i * (σ i * (σ i * iteratedDeriv 2 η (σ i * ξ)) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1) + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))) + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))) + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))))‖ ≤ ‖ε i‖ * ‖σ i * (σ i * iteratedDeriv 2 η (σ i * ξ)) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1) + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))) + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))) + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))))‖ := norm_mul_le _ _
            _ ≤ 1 * (‖σ i * (σ i * iteratedDeriv 2 η (σ i * ξ)) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1)‖ + ‖(σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))‖ + ‖(σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))‖ + ‖η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))))‖) :=
                mul_le_mul (hε i hi) hABC (norm_nonneg _) zero_le_one
            _ = ‖σ i * (σ i * iteratedDeriv 2 η (σ i * ξ)) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1)‖ + ‖(σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))‖ + ‖(σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))‖ + ‖η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))))‖ := one_mul _
            _ ≤ 4 * Real.pi * M2 * σ i ^ 3 * |ξ|
                  + (8 * Real.pi * M1 * σ i ^ 2 + 16 * Real.pi ^ 2 * M0 * σ i ^ 2) := by
                linarith
        calc ‖(|ξ| ^ 2 : ℝ) • (ε i * (σ i * (σ i * iteratedDeriv 2 η (σ i * ξ)) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1) + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))) + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))) + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))))))‖ = |ξ| ^ 2 * ‖ε i * (σ i * (σ i * iteratedDeriv 2 η (σ i * ξ)) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1) + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))) + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))) + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))))‖ := by
              rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg |ξ|)]
          _ ≤ |ξ| ^ 2 * (4 * Real.pi * M2 * σ i ^ 3 * |ξ|
                + (8 * Real.pi * M1 * σ i ^ 2 + 16 * Real.pi ^ 2 * M0 * σ i ^ 2)) :=
              mul_le_mul_of_nonneg_left hmid (sq_nonneg |ξ|)
          _ = 4 * Real.pi * M2 * (σ i * |ξ|) ^ 3
                + (8 * Real.pi * M1 * (σ i * |ξ|) ^ 2 + 16 * Real.pi ^ 2 * M0 * (σ i * |ξ|) ^ 2) := by
              ring
          _ ≤ (4 * Real.pi * M2 + 8 * Real.pi * M1 + 16 * Real.pi ^ 2 * M0) * (σ i * |ξ|) := by
              have h0 : 0 ≤ σ i * |ξ| := mul_nonneg hσi.le (abs_nonneg ξ)
              have h2 : (σ i * |ξ|) ^ 2 ≤ σ i * |ξ| := pow_two_le_self_of_le_one h0 ht
              have h3 : (σ i * |ξ|) ^ 3 ≤ σ i * |ξ| := pow_three_le_self_of_le_one h0 ht
              have e1 : 4 * Real.pi * M2 * (σ i * |ξ|) ^ 3 ≤ 4 * Real.pi * M2 * (σ i * |ξ|) :=
                mul_le_mul_of_nonneg_left h3 (by positivity)
              have e2 : 8 * Real.pi * M1 * (σ i * |ξ|) ^ 2 ≤ 8 * Real.pi * M1 * (σ i * |ξ|) :=
                mul_le_mul_of_nonneg_left h2 (by positivity)
              have e3 : 16 * Real.pi ^ 2 * M0 * (σ i * |ξ|) ^ 2
                  ≤ 16 * Real.pi ^ 2 * M0 * (σ i * |ξ|) :=
                mul_le_mul_of_nonneg_left h2 (by positivity)
              linarith
      have hzero2 : ∀ i ∈ D, 1 < σ i * |ξ| → (|ξ| ^ 2 : ℝ) • (ε i * (σ i * (σ i * iteratedDeriv 2 η (σ i * ξ)) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1) + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))) + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))) + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))))) = 0 := by
        intro i hi ht
        have hσi : 0 < σ i := hlac.1 i hi
        have hlt : 1 ≤ |σ i * ξ| := by rw [abs_mul, abs_of_pos hσi]; exact ht.le
        rw [hηs0 (σ i * ξ) hlt, hηs1 (σ i * ξ) hlt, hηs2 (σ i * ξ) hlt]
        simp
      have hsum2 := lacunarySum_norm_bound hlam hlac hξ hC2 hf2 hzero2
      have hpush2 : (|ξ| ^ 2 : ℝ) • (∑ i ∈ D, ε i * (σ i * (σ i * iteratedDeriv 2 η (σ i * ξ)) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1) + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))) + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))) + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))))) = ∑ i ∈ D, (|ξ| ^ 2 : ℝ) • (ε i * (σ i * (σ i * iteratedDeriv 2 η (σ i * ξ)) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1) + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))) + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))) + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))))) :=
        Finset.smul_sum
      calc |ξ| ^ 2 * ‖∑ i ∈ D, ε i * (σ i * (σ i * iteratedDeriv 2 η (σ i * ξ)) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1) + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))) + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))) + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))))‖ = ‖(|ξ| ^ 2 : ℝ) • (∑ i ∈ D, ε i * (σ i * (σ i * iteratedDeriv 2 η (σ i * ξ)) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1) + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))) + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))) + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))))))‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg |ξ|)]
        _ = ‖∑ i ∈ D, (|ξ| ^ 2 : ℝ) • (ε i * (σ i * (σ i * iteratedDeriv 2 η (σ i * ξ)) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1) + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))) + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))) + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))))))‖ := by rw [hpush2]
        _ ≤ ∑ i ∈ D, ‖(|ξ| ^ 2 : ℝ) • (ε i * (σ i * (σ i * iteratedDeriv 2 η (σ i * ξ)) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1) + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))) + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))) + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))))))‖ := norm_sum_le _ _
        _ ≤ 2 * (4 * Real.pi * M2 + 8 * Real.pi * M1 + 16 * Real.pi ^ 2 * M0) / (1 - lam⁻¹) :=
            hsum2
        _ = K * (4 * Real.pi * M2 + 8 * Real.pi * M1 + 16 * Real.pi ^ 2 * M0) := hKC _
        _ ≤ 1 + K * B := by
            have hmul : K * (4 * Real.pi * M2 + 8 * Real.pi * M1 + 16 * Real.pi ^ 2 * M0) ≤ K * B :=
              mul_le_mul_of_nonneg_left hA2 hKpos'.le
            linarith

end Work.KMTAreas.A7
