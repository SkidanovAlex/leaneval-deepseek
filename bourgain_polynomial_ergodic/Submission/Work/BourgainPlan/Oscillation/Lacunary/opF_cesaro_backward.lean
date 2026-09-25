import Mathlib
import Submission.Work.BourgainPlan.Oscillation.lacunary_defs
import Submission.Work.BourgainPlan.Oscillation.lacunary_truncated_maximal_l2

/-!
# The backward Cesàro Fourier coefficient identity

For the Cesàro average at scale `N` and a finitely supported `f` (supported in the finite set `s`),
the `x`-th Fourier coefficient of the product of the Cesàro multiplier with the trigonometric
polynomial `∑_{j ∈ s} f j e(jθ)` is the backward average of `f`:

`∫_0^1 (N⁻¹ ∑_{n<N} e(nθ)) · (∑_{j∈s} f j e(jθ)) · e(-xθ) dθ = N⁻¹ ∑_{n<N} f (x - n)`

where `e(t) = exp (2 π i t)`.  The proof is orthogonality of the characters on `[0,1]`.
-/

namespace Work.BourgainPlan.Oscillation.Lacunary

open Finset
open scoped BigOperators

noncomputable section

/-! ## Orthogonality of the characters on `[0,1]` -/

private lemma integral_cexp_int (k : ℤ) :
    (∫ θ in (0:ℝ)..1, Complex.exp (2 * Real.pi * Complex.I * ((k : ℝ) * θ)))
      = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · subst hk
    norm_num
  · have hkc : ((k:ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_intCast]; exact_mod_cast hk
    have hp : ((Real.pi : ℂ)) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hc : 2 * (Real.pi : ℂ) * Complex.I * ((k:ℝ) : ℂ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hp) Complex.I_ne_zero) hkc
    have hexp : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((k:ℝ) : ℂ)) = 1 := by
      rw [show 2 * (Real.pi : ℂ) * Complex.I * ((k:ℝ) : ℂ)
            = ((k:ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) from by
          rw [Complex.ofReal_intCast]; ring]
      exact Complex.exp_int_mul_two_pi_mul_I k
    have hcongr : (∫ θ in (0:ℝ)..1, Complex.exp (2 * Real.pi * Complex.I * ((k:ℝ) * θ)))
        = ∫ θ in (0:ℝ)..1, Complex.exp ((2 * (Real.pi : ℂ) * Complex.I * ((k:ℝ) : ℂ)) * θ) := by
      apply intervalIntegral.integral_congr
      intro θ _
      apply congrArg Complex.exp
      push_cast
      ring
    rw [hcongr, integral_exp_mul_complex hc]
    simp only [Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero, Complex.exp_zero,
      hexp, sub_self, zero_div]
    simp [hk]

/-! ## Pointwise identities -/

private lemma exp_add_three (a b c : ℂ) :
    Complex.exp a * Complex.exp b * Complex.exp c = Complex.exp (a + b + c) := by
  rw [← Complex.exp_add, ← Complex.exp_add]

private lemma cexp_product_back (f : ℤ → ℂ) (n : ℕ) (j x : ℤ) (θ : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) * (θ : ℂ)))
      * (f j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (θ : ℂ))))
      * Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℂ) * (θ : ℂ))))
    = f j * Complex.exp (2 * Real.pi * Complex.I * ((((n : ℤ) + j - x : ℤ) : ℝ) * θ)) := by
  rw [show Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) * (θ : ℂ)))
        * (f j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (θ : ℂ))))
        * Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℂ) * (θ : ℂ))))
      = f j * (Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) * (θ : ℂ)))
        * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (θ : ℂ)))
        * Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℂ) * (θ : ℂ))))) from by ring]
  rw [exp_add_three]
  have harg : 2 * Real.pi * Complex.I * ((n : ℂ) * (θ : ℂ))
        + 2 * Real.pi * Complex.I * ((j : ℂ) * (θ : ℂ))
        + (-(2 * Real.pi * Complex.I * ((x : ℂ) * (θ : ℂ))))
      = 2 * Real.pi * Complex.I * ((((n : ℤ) + j - x : ℤ) : ℝ) * θ) := by
    push_cast
    ring
  rw [harg]

private lemma integrand_eq_double_sum (N : ℕ) (f : ℤ → ℂ) (s : Finset ℤ) (x : ℤ) (θ : ℝ) :
    ((N : ℂ)⁻¹ * ∑ n ∈ Finset.range N,
        Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) * (θ : ℂ))))
      * (∑ j ∈ s, f j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (θ : ℂ))))
      * Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℂ) * (θ : ℂ))))
    = (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, ∑ j ∈ s,
        f j * Complex.exp (2 * Real.pi * Complex.I * ((((n : ℤ) + j - x : ℤ) : ℝ) * θ)) := by
  rw [show ((N : ℂ)⁻¹ * ∑ n ∈ Finset.range N,
        Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) * (θ : ℂ))))
      * (∑ j ∈ s, f j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (θ : ℂ))))
      * Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℂ) * (θ : ℂ))))
    = (N : ℂ)⁻¹ * ((∑ n ∈ Finset.range N,
          Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) * (θ : ℂ))))
      * (∑ j ∈ s, f j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (θ : ℂ))))
      * Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℂ) * (θ : ℂ))))) from by ring]
  congr 1
  rw [Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl (fun j _ => cexp_product_back f n j x θ)

/-! ## The one-fibre integral and its collapse -/

private lemma integral_inner (f : ℤ → ℂ) (s : Finset ℤ) (x : ℤ) (n : ℕ) :
    (∫ θ in (0:ℝ)..1, ∑ j ∈ s,
        f j * Complex.exp (2 * Real.pi * Complex.I * ((((n : ℤ) + j - x : ℤ) : ℝ) * θ)))
      = ∑ j ∈ s, f j * (if ((n : ℤ) + j - x) = 0 then 1 else 0) := by
  rw [intervalIntegral.integral_finsetSum (fun j _ =>
    (by fun_prop : Continuous fun θ : ℝ =>
      f j * Complex.exp (2 * Real.pi * Complex.I * ((((n : ℤ) + j - x : ℤ) : ℝ) * θ))).intervalIntegrable
      0 1)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [intervalIntegral.integral_const_mul, integral_cexp_int]

private lemma inner_collapse (f : ℤ → ℂ) (s : Finset ℤ) (hs : ∀ n, n ∉ s → f n = 0)
    (x : ℤ) (n : ℕ) :
    (∑ j ∈ s, f j * (if ((n : ℤ) + j - x) = 0 then (1:ℂ) else 0)) = f (x - (n : ℤ)) := by
  have hterm : ∀ j ∈ s, f j * (if ((n : ℤ) + j - x) = 0 then (1:ℂ) else 0)
      = (if j = x - (n : ℤ) then f j else 0) := by
    intro j _
    have hiff : ((n : ℤ) + j - x = 0) ↔ j = x - (n : ℤ) := by
      constructor <;> intro hh <;> omega
    by_cases h : j = x - (n : ℤ)
    · rw [if_pos (hiff.mpr h), if_pos h, mul_one]
    · rw [if_neg (fun hh => h (hiff.mp hh)), if_neg h, mul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
  by_cases h : x - (n : ℤ) ∈ s
  · rw [if_pos h]
  · rw [if_neg h, hs _ h]

/-! ## The target -/

theorem opF_cesaro_backward (N : ℕ) (hN : 1 ≤ N) (f : ℤ → ℂ) (s : Finset ℤ)
    (hs : ∀ n, n ∉ s → f n = 0) (x : ℤ) :
    (∫ θ in (0:ℝ)..1,
        (((N : ℂ))⁻¹ * ∑ n ∈ Finset.range N,
            Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) * (θ : ℂ))))
          * (∑ j ∈ s, f j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (θ : ℂ))))
          * Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℂ) * (θ : ℂ)))))
      = ((N : ℝ)⁻¹ : ℂ) * ∑ n ∈ Finset.range N, f (x - (n : ℤ)) := by
  have hmain : (∫ θ in (0:ℝ)..1,
        (((N : ℂ))⁻¹ * ∑ n ∈ Finset.range N,
            Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) * (θ : ℂ))))
          * (∑ j ∈ s, f j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (θ : ℂ))))
          * Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℂ) * (θ : ℂ)))))
      = (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, f (x - (n : ℤ)) := by
    rw [show (∫ θ in (0:ℝ)..1,
          (((N : ℂ))⁻¹ * ∑ n ∈ Finset.range N,
              Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) * (θ : ℂ))))
            * (∑ j ∈ s, f j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (θ : ℂ))))
            * Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℂ) * (θ : ℂ)))))
        = ∫ θ in (0:ℝ)..1, (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, ∑ j ∈ s,
            f j * Complex.exp (2 * Real.pi * Complex.I * ((((n : ℤ) + j - x : ℤ) : ℝ) * θ)) from by
      apply intervalIntegral.integral_congr
      intro θ _
      exact integrand_eq_double_sum N f s x θ]
    rw [intervalIntegral.integral_const_mul]
    congr 1
    trans ∑ n ∈ Finset.range N, (∫ θ in (0:ℝ)..1, ∑ j ∈ s,
        f j * Complex.exp (2 * Real.pi * Complex.I * ((((n : ℤ) + j - x : ℤ) : ℝ) * θ)))
    · exact intervalIntegral.integral_finsetSum (fun n _ =>
        (by fun_prop : Continuous fun θ : ℝ => ∑ j ∈ s,
          f j * Complex.exp (2 * Real.pi * Complex.I * ((((n : ℤ) + j - x : ℤ) : ℝ) * θ))).intervalIntegrable
          0 1)
    · exact (Finset.sum_congr rfl (fun n _ => integral_inner f s x n)).trans
        (Finset.sum_congr rfl (fun n _ => inner_collapse f s hs x n))
  rw [hmain, Complex.ofReal_natCast]

end

end Work.BourgainPlan.Oscillation.Lacunary
