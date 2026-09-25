import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace Commons.Analysis.Fourier

open MeasureTheory
open scoped Real ComplexConjugate Topology BigOperators

noncomputable section

/-- The exponential monomial `θ ↦ e^{2πi n θ}`, the `n`-th Fourier character on the circle
of circumference `1`. -/
private def E (n : ℤ) (θ : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (θ : ℂ))

private lemma E_cont (n : ℤ) : Continuous (E n) := by
  unfold E; fun_prop

private lemma E_mul (n m : ℤ) (θ : ℝ) : E n θ * E m θ = E (n + m) θ := by
  unfold E
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The conjugate of a character is the character of the negated frequency. -/
private lemma E_conj (n : ℤ) (θ : ℝ) : conj (E n θ) = E (-n) θ := by
  unfold E
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, map_intCast, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- Orthogonality of characters: `∫₀¹ e^{2πi k θ} dθ = 1` if `k = 0` and `0` otherwise. -/
private lemma E_integral (k : ℤ) : (∫ θ in (0:ℝ)..1, E k θ) = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · subst hk
    rw [if_pos rfl]
    simp only [E]
    simp
  · rw [if_neg hk]
    have hc : (2 * Real.pi * Complex.I * (k : ℂ)) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_
      · norm_num
      · exact_mod_cast Real.pi_ne_zero
      · exact Complex.I_ne_zero
      · exact_mod_cast hk
    rw [show (fun θ : ℝ => E k θ)
        = (fun θ : ℝ => Complex.exp ((2 * Real.pi * Complex.I * (k:ℂ)) * (θ:ℂ))) from rfl]
    rw [integral_exp_mul_complex hc]
    have h1 : Complex.exp ((2 * Real.pi * Complex.I * (k:ℂ)) * (1:ℝ)) = 1 := by
      have : (2 * Real.pi * Complex.I * (k:ℂ)) * (1:ℝ) = (k:ℂ) * (2 * Real.pi * Complex.I) := by
        push_cast; ring
      rw [this, Complex.exp_int_mul, Complex.exp_two_pi_mul_I, one_zpow]
    have h0 : Complex.exp ((2 * Real.pi * Complex.I * (k:ℂ)) * (0:ℝ)) = 1 := by simp
    rw [h1, h0, sub_self, zero_div]

private lemma norm_sq_re (z : ℂ) : ‖z‖ ^ 2 = (z * conj z).re := by
  rw [Complex.sq_norm, ← Complex.ofReal_re (Complex.normSq z),
    Complex.normSq_eq_conj_mul_self, mul_comm]

private lemma ofReal_norm_sq (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * conj z := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self, mul_comm]

/-- Plancherel's identity for trigonometric polynomials (the `ℓ²`-Fourier identity on the
circle of circumference `1`): the sum of squared moduli of the coefficients equals the
`L²`-norm of the corresponding exponential polynomial. -/
theorem plancherel_trig_polynomial (s : Finset ℤ) (g : ℤ → ℂ) :
    (∑ n ∈ s, ‖g n‖ ^ 2)
      = ∫ θ in (0 : ℝ)..1,
          ‖∑ n ∈ s, g n * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (θ : ℂ))‖ ^ 2 := by
  change (∑ n ∈ s, ‖g n‖ ^ 2)
      = ∫ θ in (0 : ℝ)..1, ‖∑ n ∈ s, g n * E n θ‖ ^ 2
  have hcont : Continuous (fun θ : ℝ => ∑ n ∈ s, g n * E n θ) :=
    continuous_finsetSum s (fun n _ => (E_cont n).const_mul (g n))
  set F : ℝ → ℂ := fun θ => (∑ n ∈ s, g n * E n θ) * conj (∑ n ∈ s, g n * E n θ) with hF
  have hcontF : Continuous F := by
    rw [hF]
    exact hcont.mul (Complex.continuous_conj.comp hcont)
  -- The complex integral of `|f|²` expanded into a double sum and integrated termwise:
  -- characters are orthonormal, so only the diagonal survives.
  have hcomplex : ∫ θ in (0:ℝ)..1, F θ = ∑ n ∈ s, g n * conj (g n) := by
    rw [hF]
    have hpt : ∀ θ : ℝ,
        (∑ n ∈ s, g n * E n θ) * conj (∑ n ∈ s, g n * E n θ)
          = ∑ n ∈ s, ∑ m ∈ s, g n * conj (g m) * E (n - m) θ := by
      intro θ
      have hconj : conj (∑ n ∈ s, g n * E n θ) = ∑ m ∈ s, conj (g m) * E (-m) θ := by
        rw [map_sum]
        refine Finset.sum_congr rfl (fun m _ => ?_)
        rw [map_mul, E_conj]
      rw [hconj, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl (fun n _ => Finset.sum_congr rfl (fun m _ => ?_))
      rw [sub_eq_add_neg, ← E_mul]
      ring
    rw [show (fun θ : ℝ => (∑ n ∈ s, g n * E n θ) * conj (∑ n ∈ s, g n * E n θ))
          = (fun θ : ℝ => ∑ n ∈ s, ∑ m ∈ s, g n * conj (g m) * E (n - m) θ) from
        funext hpt]
    have hinner : ∀ n : ℤ, (∫ θ in (0:ℝ)..1, ∑ m ∈ s, g n * conj (g m) * E (n - m) θ)
        = ∑ m ∈ s, (if n = m then g n * conj (g m) else 0) := by
      intro n
      rw [intervalIntegral.integral_finsetSum]
      · refine Finset.sum_congr rfl (fun m _ => ?_)
        rw [intervalIntegral.integral_const_mul (g n * conj (g m)), E_integral]
        by_cases h : n = m
        · have h0 : n - m = 0 := sub_eq_zero.mpr h
          rw [if_pos h0, if_pos h]; ring
        · have h0 : ¬ (n - m = 0) := fun hh => h (sub_eq_zero.mp hh)
          rw [if_neg h0, if_neg h]; ring
      · intro m _
        exact ((E_cont (n - m)).const_mul (g n * conj (g m))).intervalIntegrable _ _
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl (fun n hn => ?_)
      rw [hinner n, Finset.sum_ite_eq]
      simp [hn]
    · intro n _
      exact (continuous_finsetSum _ (fun m _ =>
        (E_cont (n - m)).const_mul (g n * conj (g m)))).intervalIntegrable _ _
  have hIntFOn : IntegrableOn F (Set.Ioc (0:ℝ) 1) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)).mp
      (hcontF.intervalIntegrable 0 1)
  have key : ∫ θ in (0:ℝ)..1, ‖∑ n ∈ s, g n * E n θ‖ ^ 2 = ∑ n ∈ s, ‖g n‖ ^ 2 := by
    have hpoint : ∀ θ : ℝ, ‖∑ n ∈ s, g n * E n θ‖ ^ 2 = (F θ).re := by
      intro θ; rw [hF]; exact norm_sq_re _
    calc ∫ θ in (0:ℝ)..1, ‖∑ n ∈ s, g n * E n θ‖ ^ 2
        = ∫ θ in (0:ℝ)..1, (F θ).re :=
          intervalIntegral.integral_congr (fun θ _ => hpoint θ)
      _ = ∫ θ in Set.Ioc (0:ℝ) 1, (F θ).re :=
          intervalIntegral.integral_of_le (by norm_num)
      _ = (∫ θ in Set.Ioc (0:ℝ) 1, F θ).re := integral_re hIntFOn
      _ = (∫ θ in (0:ℝ)..1, F θ).re := by
          rw [intervalIntegral.integral_of_le (by norm_num)]
      _ = (∑ n ∈ s, g n * conj (g n)).re := by rw [hcomplex]
      _ = ∑ n ∈ s, ‖g n‖ ^ 2 := by
          rw [show (∑ n ∈ s, g n * conj (g n)) = ∑ n ∈ s, ((‖g n‖^2 : ℝ):ℂ) from
            Finset.sum_congr rfl (fun n _ => (ofReal_norm_sq (g n)).symm)]
          simp only [Complex.re_sum, Complex.ofReal_re]
  exact key.symm

end

end Commons.Analysis.Fourier