import Mathlib
import Submission.Work.BMF.parseval_kernels
import Submission.Work.BMF.stepKern_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Perron integral of a Dirichlet polynomial equals a sum of step kernels

For a sequence `a : ℕ → ℂ`, a scale `X`, a target height `y > 0` and a truncation
parameter `T > 0`, we evaluate the truncated Perron integral of the Dirichlet polynomial
`A(1 + it) = dirPoly a X t`:

  `(1/2π) ∫_{-T}^{T} A(1+it) · y^{1+it}/(1+it) dt
      = ∑_{n ∈ [X,4X]} a n · stepKern 1 T (y/n)`.

The proof is linearity of the (finite) Dirichlet polynomial over the integral: interchanging
the finite sum and the integral, every summand is a single Perron step kernel `stepKern 1 T`,
evaluated at `z = y/n`.  The two ingredients are

* `stepKern_one_eq_integral`: `stepKern 1 T z = (1/2π) ∫_{-T}^{T} z^{1+it}/(1+it) dt` for
  `z > 0`, which is just `Complex.cpow_def_of_ne_zero` (`z^w = exp(log z · w)`);
* `cpow_neg_mul_cpow_ofReal`: `n^{-(1+it)} · y^{1+it} = (y/n)^{1+it}` for `y > 0`,
  which is `Complex.div_cpow_ofReal_nonneg` together with `Complex.cpow_neg`.
-/

namespace Work.BMF

open scoped BigOperators
open Finset Real Complex

/-- Every element of `natIcc a b` is at least `1` as soon as `1 ≤ a`. -/
private lemma one_le_of_mem_natIcc {a b : ℝ} (ha : 1 ≤ a) {n : ℕ} (hn : n ∈ natIcc a b) :
    1 ≤ n := by
  simp only [natIcc, Finset.mem_Icc] at hn
  have h1 : (1 : ℝ) ≤ (⌈a⌉₊ : ℕ) := le_trans ha (Nat.le_ceil a)
  have h2 : 1 ≤ ⌈a⌉₊ := by exact_mod_cast h1
  exact le_trans h2 hn.1

/-- The Perron denominator `1 + it` never vanishes. -/
private lemma one_add_I_mul_ne_zero (t : ℝ) : (1 + Complex.I * (t : ℂ)) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this

/-- The truncated Perron step kernel `stepKern 1 T z`, written in terms of the
complex power `z^{1+it}` (valid for positive real `z`). -/
private lemma stepKern_one_eq_integral {z : ℝ} (hz : 0 < z) (T : ℝ) :
    Commons.Analysis.Complex.stepKern 1 T z
      = (1 / (2 * Real.pi)) * (∫ t in (-T)..T,
          ((z : ℂ) ^ (1 + Complex.I * (t : ℂ))) / (1 + Complex.I * (t : ℂ))) := by
  unfold Commons.Analysis.Complex.stepKern
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  simp only []
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hz.ne')]
  rw [Complex.ofReal_one]
  ring_nf

/-- The multiplicativity identity behind the summation:
`n^{-(1+it)} · y^{1+it} = (y/n)^{1+it}` for positive real `y` and `n ≥ 1`. -/
private lemma cpow_neg_mul_cpow_ofReal {y : ℝ} (hy : 0 < y) {n : ℕ} (_hn : 1 ≤ n) (t : ℝ) :
    (n : ℂ) ^ (-(1 + Complex.I * (t : ℂ))) * (y : ℂ) ^ (1 + Complex.I * (t : ℂ))
      = ((y / (n : ℝ) : ℝ) : ℂ) ^ (1 + Complex.I * (t : ℂ)) := by
  rw [← Complex.ofReal_natCast n]
  rw [Complex.ofReal_div]
  rw [Complex.cpow_neg]
  rw [← div_eq_inv_mul]
  rw [← Complex.div_cpow_ofReal_nonneg hy.le (Nat.cast_nonneg n) (1 + Complex.I * (t : ℂ))]

/-- The integrand `t ↦ c^{1+it}/(1+it)` is continuous for `c ≠ 0`. -/
private lemma continuous_cpow_div (c : ℂ) (hc : c ≠ 0) :
    Continuous (fun t : ℝ => c ^ (1 + Complex.I * (t : ℂ)) / (1 + Complex.I * (t : ℂ))) := by
  apply Continuous.div
  · exact Continuous.const_cpow (by continuity) (Or.inl hc)
  · continuity
  · intro t; exact one_add_I_mul_ne_zero t

theorem dirPoly_perron_integral (a : ℕ → ℂ) {X y T : ℝ} (hX : 1 ≤ X) (hy : 0 < y) (hT : 0 < T) :
    (1 / (2 * Real.pi)) * (∫ t in (-T)..T,
        Work.BMF.dirPoly a X t * ((y : ℂ) ^ (1 + Complex.I * (t : ℂ))) / (1 + Complex.I * (t : ℂ)))
      = ∑ n ∈ Work.BMF.natIcc X (4 * X),
          a n * Commons.Analysis.Complex.stepKern 1 T (y / (n : ℝ)) := by
  -- Interchange the (finite) Dirichlet polynomial with the integral.
  have key : (∫ t in (-T)..T,
        dirPoly a X t * (y : ℂ) ^ (1 + Complex.I * (t : ℂ)) / (1 + Complex.I * (t : ℂ)))
      = ∑ n ∈ natIcc X (4 * X), a n * ∫ t in (-T)..T,
          ((y / (n : ℝ) : ℝ) : ℂ) ^ (1 + Complex.I * (t : ℂ)) / (1 + Complex.I * (t : ℂ)) := by
    have hcongr : (fun t : ℝ =>
          dirPoly a X t * (y : ℂ) ^ (1 + Complex.I * (t : ℂ)) / (1 + Complex.I * (t : ℂ)))
        = fun t : ℝ => ∑ n ∈ natIcc X (4 * X), a n *
            (((y / (n : ℝ) : ℝ) : ℂ) ^ (1 + Complex.I * (t : ℂ)) / (1 + Complex.I * (t : ℂ))) := by
      funext t
      rw [dirPoly]
      rw [Finset.sum_mul, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro n hn
      rw [mul_assoc, cpow_neg_mul_cpow_ofReal hy (one_le_of_mem_natIcc hX hn) t, mul_div_assoc]
    rw [hcongr]
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro n hn
      rw [intervalIntegral.integral_const_mul]
    · intro n hn
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast one_le_of_mem_natIcc hX hn
      have hc : ((y / (n : ℝ) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
      exact Continuous.intervalIntegrable ((continuous_cpow_div _ hc).const_mul (a n)) (-T) T
  rw [key, Finset.mul_sum]
  -- Each remaining integral is exactly one step kernel.
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast one_le_of_mem_natIcc hX hn
  rw [stepKern_one_eq_integral (show 0 < y / (n : ℝ) by positivity) T]
  ring

end Work.BMF
