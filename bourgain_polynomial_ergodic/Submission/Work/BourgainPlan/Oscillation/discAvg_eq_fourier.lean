import Mathlib
import Submission.Work.BourgainPlan.Oscillation.defs
import Submission.Work.BourgainPlan.Oscillation.discAvg_multiplier_identity

/-!
# The discrete polynomial average as a Fourier integral

The density-kernel average `discAvg P N g n = (1/N) Σ_{i<N} g (n + P(i))` is the `n`-th
Fourier coefficient of the product of the (truncated) polynomial exponential sum with the
finitely supported sequence `g`:

`discAvg P N g n = ∫_0^1 (N⁻¹ Σ_{i<N} e(-P(i) θ)) · (Σ_m g m e(m θ)) · e(-n θ) dθ`,

where `e(x) = exp (2 π i x)`.  This is the "frequency representation" of the polynomial
average that Bourgain's argument reads the multiplier off from.

The proof is the orthogonality of the characters on `[0,1]`, `∫_0^1 e(k θ) dθ = δ_{k,0}`
for `k ∈ ℤ`, applied after expanding the finite products into a doubly indexed finite sum;
the hypothesis `NonnegOnNat P` is used only through `(P.eval i).toNat` and the finiteness
support hypothesis `ht` only to collapse `Σ_{m ∈ t, m = n + P(i)} g m` to `g (n + P(i))`.
-/

open Finset
open scoped BigOperators

namespace Work.BourgainPlan.Oscillation

/-- `exp a * exp b * exp c = exp (a + b + c)`: the additive exponential law for three factors
(kept separate from `Complex.exp_add` so that the associativity pattern is definitional). -/
private lemma exp_mul_exp_mul_exp (a b c : ℂ) :
    Complex.exp a * Complex.exp b * Complex.exp c = Complex.exp (a + b + c) := by
  rw [← Complex.exp_add, ← Complex.exp_add]

/-- **Orthogonality of the characters** `θ ↦ exp (2 π i k θ)` on `[0,1]`. -/
lemma integral_cexp_two_pi_I_mul_int (k : ℤ) :
    ∫ θ in (0:ℝ)..1, Complex.exp (2 * Real.pi * Complex.I * ((k:ℝ) * θ))
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

/-- **The pointwise integrand identity.**  The product of the three exponentials attached to
`i`, `m` and `n` is the single character of frequency `m - P(i) - n`. -/
private lemma cexp_product (P : Polynomial ℤ) (g : ℕ → ℝ) (i m n : ℕ) (θ : ℝ) :
    Complex.exp (-(2 * Real.pi * Complex.I * ((((P.eval (i:ℤ) : ℤ)) : ℝ) * θ)))
      * ((g m : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((m : ℝ) * θ)))
      * Complex.exp (-(2 * Real.pi * Complex.I * ((n : ℝ) * θ)))
    = (g m : ℂ) * Complex.exp
        (2 * Real.pi * Complex.I * ((((m:ℤ) - P.eval (i:ℤ) - (n:ℤ) : ℤ) : ℝ) * θ)) := by
  rw [show Complex.exp (-(2 * Real.pi * Complex.I * ((((P.eval (i:ℤ) : ℤ)) : ℝ) * θ)))
        * ((g m : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((m : ℝ) * θ)))
        * Complex.exp (-(2 * Real.pi * Complex.I * ((n : ℝ) * θ)))
      = (g m : ℂ) * (Complex.exp (-(2 * Real.pi * Complex.I * ((((P.eval (i:ℤ) : ℤ)) : ℝ) * θ)))
        * Complex.exp (2 * Real.pi * Complex.I * ((m : ℝ) * θ))
        * Complex.exp (-(2 * Real.pi * Complex.I * ((n : ℝ) * θ)))) from by ring]
  rw [exp_mul_exp_mul_exp]
  congr 1
  push_cast
  ring_nf

/-- **The pointwise expansion of the integrand** into a doubly indexed finite sum. -/
private lemma integrand_eq_double_sum (P : Polynomial ℤ) (N : ℕ) (g : ℕ → ℝ)
    (t : Finset ℕ) (n : ℕ) (θ : ℝ) :
    ((N : ℂ)⁻¹ * ∑ i ∈ Finset.range N,
        Complex.exp (-(2 * Real.pi * Complex.I * ((((P.eval (i:ℤ) : ℤ)) : ℝ) * θ))))
      * (∑ m ∈ t, (g m : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((m : ℝ) * θ)))
      * Complex.exp (-(2 * Real.pi * Complex.I * ((n : ℝ) * θ)))
    = (N : ℂ)⁻¹ * ∑ i ∈ Finset.range N, ∑ m ∈ t,
        (g m : ℂ) * Complex.exp
          (2 * Real.pi * Complex.I * ((((m:ℤ) - P.eval (i:ℤ) - (n:ℤ) : ℤ) : ℝ) * θ)) := by
  rw [show ((N : ℂ)⁻¹ * ∑ i ∈ Finset.range N,
        Complex.exp (-(2 * Real.pi * Complex.I * ((((P.eval (i:ℤ) : ℤ)) : ℝ) * θ))))
      * (∑ m ∈ t, (g m : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((m : ℝ) * θ)))
      * Complex.exp (-(2 * Real.pi * Complex.I * ((n : ℝ) * θ)))
    = (N : ℂ)⁻¹ * ((∑ i ∈ Finset.range N,
          Complex.exp (-(2 * Real.pi * Complex.I * ((((P.eval (i:ℤ) : ℤ)) : ℝ) * θ))))
      * (∑ m ∈ t, (g m : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((m : ℝ) * θ)))
      * Complex.exp (-(2 * Real.pi * Complex.I * ((n : ℝ) * θ)))) from by ring]
  congr 1
  rw [Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl (fun m _ => cexp_product P g i m n θ)

/-- The frequency `m - P(i) - n` vanishes exactly when `m = n + P(i)` (as natural numbers),
using nonnegativity of `P` on `ℕ`. -/
private lemma int_sub_eq_zero_iff (P : Polynomial ℤ)
    (hP : Submission.BourgainPlan.NonnegOnNat P) (i m n : ℕ) :
    ((m:ℤ) - P.eval (i:ℤ) - (n:ℤ) = 0) ↔ m = n + (P.eval (i:ℤ)).toNat := by
  have hPi : (0:ℤ) ≤ P.eval (i:ℤ) := hP i
  constructor
  · intro h; omega
  · intro h; omega

/-- **One fibre of the frequency sum**: for fixed `i` the integral over `θ` of the `m`-sum
collapses, by orthogonality, to the single value `g (n + P(i))`. -/
private lemma integral_inner (P : Polynomial ℤ) (hP : Submission.BourgainPlan.NonnegOnNat P)
    (g : ℕ → ℝ) (t : Finset ℕ) (ht : ∀ n, n ∉ t → g n = 0) (n i : ℕ) :
    (∫ θ in (0:ℝ)..1, ∑ m ∈ t,
        (g m : ℂ) * Complex.exp
          (2 * Real.pi * Complex.I * ((((m:ℤ) - P.eval (i:ℤ) - (n:ℤ) : ℤ) : ℝ) * θ)))
      = (g (n + (P.eval (i:ℤ)).toNat) : ℂ) := by
  rw [intervalIntegral.integral_finsetSum (fun m _ =>
    (by fun_prop : Continuous fun θ : ℝ =>
      (g m : ℂ) * Complex.exp
        (2 * Real.pi * Complex.I * ((((m:ℤ) - P.eval (i:ℤ) - (n:ℤ) : ℤ) : ℝ) * θ))).intervalIntegrable
      0 1)]
  simp only [intervalIntegral.integral_const_mul, integral_cexp_two_pi_I_mul_int, mul_ite,
    mul_one, mul_zero]
  have hterm : ∀ m ∈ t,
      (if ((m:ℤ) - P.eval (i:ℤ) - (n:ℤ)) = 0 then (g m : ℂ) else 0)
        = if m = n + (P.eval (i:ℤ)).toNat then (g m : ℂ) else 0 := by
    intro m _
    have hiffm := int_sub_eq_zero_iff P hP i m n
    by_cases h : m = n + (P.eval (i:ℤ)).toNat
    · rw [if_pos (hiffm.mpr h), if_pos h]
    · rw [if_neg (fun hh => h (hiffm.mp hh)), if_neg h]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
  by_cases ha : n + (P.eval (i:ℤ)).toNat ∈ t
  · simp [ha]
  · simp [ha, ht _ ha]

/-- **The average, cast to `ℂ`, as the fibre sum of the sampled sequence.** -/
lemma discAvg_cast_eq (P : Polynomial ℤ) (N : ℕ) (g : ℕ → ℝ) (n : ℕ) :
    ((Submission.BourgainPlan.discAvg P N g n : ℝ) : ℂ)
      = (N : ℂ)⁻¹ * ∑ i ∈ Finset.range N, (g (n + (P.eval (i:ℤ)).toNat) : ℂ) := by
  rw [show Submission.BourgainPlan.discAvg P N g n
      = ∑ j ∈ Finset.range (Submission.polySupport P N),
          Submission.polyKernel P N j * g (n + j) from rfl]
  rw [show ((∑ j ∈ Finset.range (Submission.polySupport P N),
        Submission.polyKernel P N j * g (n + j) : ℝ) : ℂ)
      = ∑ j ∈ Finset.range (Submission.polySupport P N),
          (Submission.polyKernel P N j : ℂ) * (g (n + j) : ℂ) from by push_cast; rfl]
  rw [discAvg_multiplier_identity P N (fun j : ℕ => (g (n + j) : ℂ))]

/-- **The Fourier representation of the discrete polynomial average.** -/
theorem discAvg_eq_fourier (P : Polynomial ℤ) (hP : Submission.BourgainPlan.NonnegOnNat P)
    (N : ℕ) (g : ℕ → ℝ) (t : Finset ℕ) (ht : ∀ n, n ∉ t → g n = 0) (n : ℕ) :
    (Submission.BourgainPlan.discAvg P N g n : ℂ)
      = ∫ θ in (0 : ℝ)..1,
          ((N : ℂ)⁻¹ * ∑ i ∈ Finset.range N,
              Complex.exp (-(2 * Real.pi * Complex.I * ((((P.eval (i : ℤ) : ℤ) : ℝ)) * θ))))
            * (∑ m ∈ t, (g m : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((m : ℝ) * θ)))
            * Complex.exp (-(2 * Real.pi * Complex.I * ((n : ℝ) * θ))) := by
  have hI : (∫ θ in (0:ℝ)..1,
        ((N : ℂ)⁻¹ * ∑ i ∈ Finset.range N,
            Complex.exp (-(2 * Real.pi * Complex.I * ((((P.eval (i : ℤ) : ℤ) : ℝ)) * θ))))
          * (∑ m ∈ t, (g m : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((m : ℝ) * θ)))
          * Complex.exp (-(2 * Real.pi * Complex.I * ((n : ℝ) * θ))))
      = (N : ℂ)⁻¹ * ∑ i ∈ Finset.range N, (g (n + (P.eval (i:ℤ)).toNat) : ℂ) := by
    rw [show (∫ θ in (0:ℝ)..1,
          ((N : ℂ)⁻¹ * ∑ i ∈ Finset.range N,
              Complex.exp (-(2 * Real.pi * Complex.I * ((((P.eval (i : ℤ) : ℤ) : ℝ)) * θ))))
            * (∑ m ∈ t, (g m : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((m : ℝ) * θ)))
            * Complex.exp (-(2 * Real.pi * Complex.I * ((n : ℝ) * θ))))
        = ∫ θ in (0:ℝ)..1, (N : ℂ)⁻¹ * ∑ i ∈ Finset.range N, ∑ m ∈ t,
            (g m : ℂ) * Complex.exp
              (2 * Real.pi * Complex.I * ((((m:ℤ) - P.eval (i:ℤ) - (n:ℤ) : ℤ) : ℝ) * θ)) from by
      apply intervalIntegral.integral_congr
      intro θ _
      exact integrand_eq_double_sum P N g t n θ]
    rw [intervalIntegral.integral_const_mul]
    congr 1
    trans (∑ i ∈ Finset.range N, (∫ θ in (0:ℝ)..1, ∑ m ∈ t,
        (g m : ℂ) * Complex.exp
          (2 * Real.pi * Complex.I * ((((m:ℤ) - P.eval (i:ℤ) - (n:ℤ) : ℤ) : ℝ) * θ))))
    · exact intervalIntegral.integral_finsetSum (fun i _ =>
        (by fun_prop : Continuous fun θ : ℝ => ∑ m ∈ t,
          (g m : ℂ) * Complex.exp
            (2 * Real.pi * Complex.I * ((((m:ℤ) - P.eval (i:ℤ) - (n:ℤ) : ℤ) : ℝ) * θ))).intervalIntegrable
          0 1)
    · exact Finset.sum_congr rfl (fun i _ => integral_inner P hP g t ht n i)
  rw [discAvg_cast_eq P N g n, hI]

end Work.BourgainPlan.Oscillation
