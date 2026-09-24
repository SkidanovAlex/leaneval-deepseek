import Mathlib
import Submission.Commons.Analysis.ExponentialSums.log_phase_block_bound
import Submission.Commons.Data.Int.sum_Icc_int_eq_sum_Icc_nat

open Finset
open scoped BigOperators
set_option autoImplicit false

open Complex
open scoped Real
open Commons.Analysis.ExponentialSums

namespace Commons.NumberTheory.DirichletPolynomial

/-- `n^{iθ} = exp(i·θ·log n)` for a natural `n ≥ 1` (complex power `Complex.cpow`). -/
lemma logsum_cpow_I_mul_eq_cexp_log (n : ℕ) (θ : ℝ) (hn : 1 ≤ n) :
    (n : ℂ) ^ (Complex.I * (θ : ℂ)) = cexp ((((θ * Real.log (n:ℝ)) : ℝ) : ℂ) * I) := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have hnne : (n:ℂ) ≠ 0 := by
    rw [← Complex.ofReal_natCast n]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt hnpos)
  rw [Complex.cpow_def_of_ne_zero hnne]
  have hlog : Complex.log (n:ℂ) = ((Real.log (n:ℝ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast n]
    exact (Complex.ofReal_log (le_of_lt hnpos)).symm
  rw [hlog]
  congr 1
  push_cast
  ring

/-- `conj (exp (-i a)) = exp (i a)`. -/
lemma logsum_conj_cexp_neg_ofReal_mul_I (a : ℝ) :
    starRingEnd ℂ (cexp ((((-a : ℝ)) : ℂ) * I)) = cexp (((a : ℝ) : ℂ) * I) := by
  rw [← Complex.exp_conj]
  congr 1
  simp [map_mul, Complex.conj_I]

/-- `n^{iθ}` is the conjugate of `exp(-i θ log n)`. -/
lemma logsum_cpow_I_mul_eq_conj_cexp (n : ℕ) (θ : ℝ) (hn : 1 ≤ n) :
    (n : ℂ) ^ (Complex.I * (θ : ℂ))
      = starRingEnd ℂ (cexp ((((-(θ * Real.log (n:ℝ))) : ℝ) : ℂ) * I)) := by
  rw [logsum_cpow_I_mul_eq_cexp_log n θ hn]
  exact (logsum_conj_cexp_neg_ofReal_mul_I (θ * Real.log (n:ℝ))).symm

/-- Partial-sum van der Corput (second-derivative) bound for a log-phase over a dyadic block:
for `θ ≥ 1` and `2 ≤ A ≤ B ≤ 2A`,
`‖∑_{A ≤ n ≤ B} n^{iθ}‖ ≤ K·(√θ + A/√θ)`.
Proved from `Commons.Analysis.ExponentialSums.second_derivative_test` applied to
`f(x) = -θ·log x/(2π)` (so `2π·f(n) = -θ·log n` and `e(2πi f(n)) = conj(n^{iθ})`),
with `a = A-1`, `L = B-A+1`, `r = θ/(2π B²)`, `B₀ = 16`. -/
theorem logsum_partial_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ (θ : ℝ), 1 ≤ θ → ∀ (A B : ℕ), 2 ≤ A → A ≤ B → B ≤ 2 * A →
      ‖∑ n ∈ Finset.Icc A B, (n : ℂ) ^ (Complex.I * (θ : ℂ))‖
        ≤ K * (Real.sqrt θ + (A : ℝ) / Real.sqrt θ) := by
  classical
  obtain ⟨C, hCpos, hSdt⟩ := second_derivative_test (B := 16) (by norm_num : (1:ℝ) ≤ 16)
  refine ⟨C * (2 * Real.sqrt (2 * Real.pi)), by positivity, ?_⟩
  intro θ hθ A B hA hAB hB2A
  have hθ0 : 0 < θ := lt_of_lt_of_le zero_lt_one hθ
  have hApos : (0:ℝ) < (A:ℝ) := by exact_mod_cast (by omega : 0 < A)
  have hA2' : (2:ℝ) ≤ (A:ℝ) := by exact_mod_cast hA
  have hBpos : (0:ℝ) < (B:ℝ) := by exact_mod_cast (by omega : 0 < B)
  set r : ℝ := θ / (2 * Real.pi * (B:ℝ)^2) with hrdef
  have hr : 0 < r := by rw [hrdef]; positivity
  set a : ℤ := (A:ℤ) - 1 with hadef
  set N : ℕ := B - A + 1 with hNdef
  have hN1 : 1 ≤ N := by omega
  have hNle : (N:ℝ) ≤ (B:ℝ) := by
    have h : N ≤ B := by omega
    exact_mod_cast h
  have hcastL : (a:ℝ) = (A:ℝ) - 1 := by rw [hadef]; simp
  have hcastN : ((N:ℕ):ℝ) = (B:ℝ) - (A:ℝ) + 1 := by
    rw [hNdef, Nat.cast_add, Nat.cast_sub hAB, Nat.cast_one]
  have hcastR : (a:ℝ) + (N:ℝ) = (B:ℝ) := by rw [hcastL, hcastN]; ring
  -- smoothness of the phase on the interval
  have hfC : ContDiffOn ℝ 2 (negLogPhase θ) (Set.Icc (a:ℝ) ((a:ℝ) + (N:ℝ))) := by
    refine contDiffOn_negLogPhase ?_
    intro x hx
    have hxA : (A:ℝ) - 1 ≤ x := by
      have h1 := (Set.mem_Icc.mp hx).1
      rwa [hcastL] at h1
    have hx1 : (1:ℝ) ≤ x := by linarith
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one hx1)
  -- two-sided second-derivative control on the interval
  have hpp : ∀ x : ℝ, x ∈ Set.Ioo (a:ℝ) ((a:ℝ) + (N:ℝ)) →
      r ≤ deriv (deriv (negLogPhase θ)) x ∧ deriv (deriv (negLogPhase θ)) x ≤ 16 * r := by
    intro x hx
    have hx1 : (A:ℝ) - 1 < x := by
      have h1 := (Set.mem_Ioo.mp hx).1
      rwa [hcastL] at h1
    have hx2 : x < (B:ℝ) := by
      have h2 := (Set.mem_Ioo.mp hx).2
      rwa [hcastR] at h2
    have hxpos : 0 < x := by linarith
    have hxne : x ≠ 0 := ne_of_gt hxpos
    rw [deriv_deriv_negLogPhase (t := θ) (x := x) hxne]
    have hrval : r = (θ / (2 * Real.pi)) * ((B:ℝ)^2)⁻¹ := by
      rw [hrdef]; field_simp
    have hB2pos : 0 < (B:ℝ)^2 := by positivity
    have hx2pos : 0 < x^2 := by positivity
    constructor
    · rw [hrval]
      have hsq : x^2 ≤ (B:ℝ)^2 := by nlinarith
      have hinv : ((B:ℝ)^2)⁻¹ ≤ (x^2)⁻¹ := (inv_le_inv₀ hB2pos hx2pos).mpr hsq
      exact mul_le_mul_of_nonneg_left hinv (by positivity)
    · rw [hrval]
      have hx4 : (B:ℝ)/4 ≤ x := by
        have h1 : (B:ℝ) ≤ 2 * (A:ℝ) := by exact_mod_cast hB2A
        linarith
      have hBle4x : (B:ℝ) ≤ 4 * x := by linarith
      have hBsq : (B:ℝ)^2 ≤ 16 * x^2 := by
        have h := mul_le_mul hBle4x hBle4x hBpos.le (by positivity)
        nlinarith [h]
      have hinv : (x^2)⁻¹ ≤ 16 * ((B:ℝ)^2)⁻¹ := by
        have h3 : ((B:ℝ)^2) * (x^2)⁻¹ ≤ 16 := by
          calc ((B:ℝ)^2) * (x^2)⁻¹ ≤ (16 * x^2) * (x^2)⁻¹ :=
                mul_le_mul_of_nonneg_right hBsq (by positivity)
            _ = 16 := by rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hx2pos), mul_one]
        rw [show 16 * ((B:ℝ)^2)⁻¹ = 16 / (B:ℝ)^2 by rw [div_eq_mul_inv], le_div_iff₀ hB2pos,
          mul_comm]
        exact h3
      calc (θ / (2 * Real.pi)) * (x^2)⁻¹
          ≤ (θ / (2 * Real.pi)) * (16 * ((B:ℝ)^2)⁻¹) :=
            mul_le_mul_of_nonneg_left hinv (by positivity)
        _ = 16 * ((θ / (2 * Real.pi)) * ((B:ℝ)^2)⁻¹) := by ring
  have hs := hSdt (a := a) (N := N) hN1 (negLogPhase θ) (r := r) hr hfC hpp
  have hIcc_eq : Finset.Icc (a + 1) (a + (N:ℤ)) = Finset.Icc (A:ℤ) (B:ℤ) := by
    have ha1 : a + 1 = (A:ℤ) := by rw [hadef]; ring
    have haN : a + (N:ℤ) = (B:ℤ) := by
      rw [hadef, hNdef, Nat.cast_add, Nat.cast_sub hAB, Nat.cast_one]
      ring
    rw [ha1, haN]
  -- reduction of the target sum to the second-derivative-test sum
  have hkey : (∑ n ∈ Finset.Icc A B, (n:ℂ) ^ (Complex.I * (θ:ℂ)))
      = starRingEnd ℂ (∑ n ∈ Finset.Icc A B,
          cexp ((((-(θ * Real.log (n:ℝ))) : ℝ) : ℂ) * I)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro n hn
    have hnA : A ≤ n := (Finset.mem_Icc.mp hn).1
    exact logsum_cpow_I_mul_eq_conj_cexp n θ (by omega)
  have hnorm_conj : ‖∑ n ∈ Finset.Icc A B, (n:ℂ)^(Complex.I * (θ:ℂ))‖
      = ‖∑ n ∈ Finset.Icc A B, cexp ((((-(θ * Real.log (n:ℝ))) : ℝ) : ℂ) * I)‖ := by
    rw [hkey, Complex.norm_conj]
  have hreindex : (∑ n ∈ Finset.Icc A B, cexp ((((-(θ * Real.log (n:ℝ))) : ℝ) : ℂ) * I))
      = ∑ z ∈ Finset.Icc (A:ℤ) (B:ℤ), cexp ((((-(θ * Real.log (z:ℝ))) : ℝ) : ℂ) * I) := by
    have h := Commons.Data.Int.sum_Icc_int_eq_sum_Icc_nat (L := (A:ℤ)) (R := (B:ℤ))
      (by positivity) (by positivity)
      (fun z : ℤ => cexp ((((-(θ * Real.log (z:ℝ))) : ℝ) : ℂ) * I))
    rw [h]
    simp only [Int.toNat_natCast]
    apply Finset.sum_congr rfl
    intro n hn
    norm_num
  have hphase : ∀ z : ℤ, cexp ((((-(θ * Real.log (z:ℝ))) : ℝ) : ℂ) * I)
      = cexp ((((2 * Real.pi * negLogPhase θ (z:ℝ)) : ℝ) : ℂ) * I) := by
    intro z
    rw [negLogPhase_two_pi_mul (t := θ) (x := (z:ℝ))]
  have hnorm_le : ‖∑ n ∈ Finset.Icc A B, (n:ℂ)^(Complex.I * (θ:ℂ))‖
      ≤ C * ((N:ℝ) * Real.sqrt r + 1 / Real.sqrt r) := by
    calc ‖∑ n ∈ Finset.Icc A B, (n:ℂ)^(Complex.I * (θ:ℂ))‖
        = ‖∑ n ∈ Finset.Icc A B, cexp ((((-(θ * Real.log (n:ℝ))) : ℝ) : ℂ) * I)‖ := hnorm_conj
      _ = ‖∑ z ∈ Finset.Icc (A:ℤ) (B:ℤ), cexp ((((-(θ * Real.log (z:ℝ))) : ℝ) : ℂ) * I)‖ := by
            rw [hreindex]
      _ = ‖∑ z ∈ Finset.Icc (A:ℤ) (B:ℤ),
              cexp ((((2 * Real.pi * negLogPhase θ (z:ℝ)) : ℝ) : ℂ) * I)‖ := by
            congr 1
            exact Finset.sum_congr rfl (fun z _ => hphase z)
      _ = ‖∑ z ∈ Finset.Icc (a + 1) (a + (N:ℤ)),
              cexp ((((2 * Real.pi * negLogPhase θ (z:ℝ)) : ℝ) : ℂ) * I)‖ := by
            rw [hIcc_eq]
      _ ≤ C * ((N:ℝ) * Real.sqrt r + 1 / Real.sqrt r) := hs
  -- elementary arithmetic collapse of the second-derivative-test bound
  have hsqrtden : Real.sqrt (2 * Real.pi * (B:ℝ)^2) = Real.sqrt (2 * Real.pi) * (B:ℝ) := by
    rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2 * Real.pi) ((B:ℝ)^2),
      Real.sqrt_sq_eq_abs, abs_of_nonneg hBpos.le]
  have hsqrt_r : Real.sqrt r = Real.sqrt θ / (Real.sqrt (2 * Real.pi) * (B:ℝ)) := by
    rw [hrdef, Real.sqrt_div (le_of_lt hθ0) (2 * Real.pi * (B:ℝ)^2), hsqrtden]
  have hAterm : (N:ℝ) * Real.sqrt r ≤ Real.sqrt θ / Real.sqrt (2 * Real.pi) := by
    rw [hsqrt_r]
    have heq : (N:ℝ) * (Real.sqrt θ / (Real.sqrt (2*Real.pi) * (B:ℝ))) =
        ((N:ℝ) / (B:ℝ)) * (Real.sqrt θ / Real.sqrt (2*Real.pi)) := by field_simp
    rw [heq]
    have hNB : (N:ℝ) / (B:ℝ) ≤ 1 := by
      rw [div_le_one hBpos]; exact hNle
    have hRpos : 0 ≤ Real.sqrt θ / Real.sqrt (2*Real.pi) := by positivity
    calc ((N:ℝ) / (B:ℝ)) * (Real.sqrt θ / Real.sqrt (2*Real.pi))
        ≤ 1 * (Real.sqrt θ / Real.sqrt (2*Real.pi)) := mul_le_mul_of_nonneg_right hNB hRpos
      _ = Real.sqrt θ / Real.sqrt (2*Real.pi) := one_mul _
  have hBterm : 1 / Real.sqrt r ≤ Real.sqrt (2*Real.pi) * (2 * (A:ℝ)) / Real.sqrt θ := by
    rw [hsqrt_r]
    have heq : 1 / (Real.sqrt θ / (Real.sqrt (2*Real.pi) * (B:ℝ))) =
        Real.sqrt (2*Real.pi) * (B:ℝ) / Real.sqrt θ := by field_simp
    rw [heq]
    have hB2A' : (B:ℝ) ≤ 2 * (A:ℝ) := by exact_mod_cast hB2A
    have hnum : Real.sqrt (2*Real.pi) * (B:ℝ) ≤ Real.sqrt (2*Real.pi) * (2*(A:ℝ)) :=
      mul_le_mul_of_nonneg_left hB2A' (by positivity)
    exact div_le_div_of_nonneg_right hnum (by positivity)
  have hkey1 : Real.sqrt θ / Real.sqrt (2*Real.pi) ≤ 2 * Real.sqrt (2*Real.pi) * Real.sqrt θ := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < Real.sqrt (2*Real.pi))]
    nlinarith [Real.pi_gt_three, Real.sqrt_nonneg θ,
      Real.sq_sqrt (by positivity : (0:ℝ) ≤ 2*Real.pi)]
  have hsum : (N:ℝ) * Real.sqrt r + 1 / Real.sqrt r
      ≤ 2 * Real.sqrt (2*Real.pi) * (Real.sqrt θ + (A:ℝ) / Real.sqrt θ) := by
    have hexp : 2 * Real.sqrt (2*Real.pi) * (Real.sqrt θ + (A:ℝ) / Real.sqrt θ)
        = 2 * Real.sqrt (2*Real.pi) * Real.sqrt θ
          + 2 * Real.sqrt (2*Real.pi) * ((A:ℝ) / Real.sqrt θ) := by ring
    rw [hexp]
    have h3 : 1 / Real.sqrt r ≤ 2 * Real.sqrt (2*Real.pi) * ((A:ℝ) / Real.sqrt θ) := by
      calc 1 / Real.sqrt r ≤ Real.sqrt (2*Real.pi) * (2 * (A:ℝ)) / Real.sqrt θ := hBterm
        _ = 2 * Real.sqrt (2*Real.pi) * ((A:ℝ) / Real.sqrt θ) := by ring
    linarith [hAterm, h3, hkey1]
  calc ‖∑ n ∈ Finset.Icc A B, (n : ℂ) ^ (Complex.I * (θ : ℂ))‖
      ≤ C * ((N:ℝ) * Real.sqrt r + 1 / Real.sqrt r) := hnorm_le
    _ ≤ C * (2 * Real.sqrt (2 * Real.pi) * (Real.sqrt θ + (A:ℝ) / Real.sqrt θ)) :=
          mul_le_mul_of_nonneg_left hsum (le_of_lt hCpos)
    _ = (C * (2 * Real.sqrt (2 * Real.pi))) * (Real.sqrt θ + (A:ℝ) / Real.sqrt θ) := by ring

end Commons.NumberTheory.DirichletPolynomial
