import Mathlib
import Submission.Work.A3.sum_range_exp_neg_int_mul_div
import Submission.Work.A3.completeSum_linear_eq
import Submission.Work.A3.gcd_natAbs_prime_pow_eq_of_dvd_mul

/-!
# The complete exponential sum of a linear polynomial modulo a prime power

For an integer polynomial `g` of degree exactly `1`, an integer `a` and a prime power
`q = p ^ ν` with `p ∤ a`, the complete sum

  `completeSum g a q = ∑_{r<q} e(-2πi a g(r)/q)`

satisfies the Gauss-sum-type bound

  `‖completeSum g a q‖ ≤ √(gcd (lead g) q) · √q`.

The proof is elementary and in fact *sharp*: a degree-one `g` has `g(r) = c₁ r + c₀`, so

  `completeSum g a q = e(-2πi a c₀/q) · ∑_{r<q} e(-2πi a c₁ r/q)`,

and the geometric sum `∑_{r<q} e(-2πi m r/q)` equals `q` when `q ∣ m` and `0` otherwise.
In the nonvanishing case `q ∣ a c₁`, primality of `p` together with `p ∤ a` forces `q ∣ c₁`,
so that `gcd (lead g) q = q` and both sides are equal to `q`; in the vanishing case the left
side is `0`.

The pieces used here live in the sibling modules
`Submission.Work.A3.sum_range_exp_neg_int_mul_div` (the geometric/complete linear sum),
`Submission.Work.A3.completeSum_linear_eq` (the degree-one splitting) and
`Submission.Work.A3.gcd_natAbs_prime_pow_eq_of_dvd_mul` (the gcd of the leading coefficient).
-/

set_option autoImplicit false

namespace Work.A3

open Polynomial Finset
open scoped BigOperators

noncomputable section

lemma linear_completeSum_bound (g : Polynomial ℤ) {p ν : ℕ} (hp : p.Prime) (hν : 1 ≤ ν)
    (hdeg : g.natDegree = 1) (a : ℤ) (ha : ¬ ((p : ℤ) ∣ a)) :
    ‖Work.A3.completeSum g a (p ^ ν)‖
      ≤ ((Nat.gcd (g.leadingCoeff.natAbs) (p ^ ν) : ℕ) : ℝ) ^ (1/2 : ℝ) *
          (((p ^ ν : ℕ) : ℝ)) ^ (1/2 : ℝ) := by
  set q : ℕ := p ^ ν with hqdef
  have hq1 : 1 ≤ q := by
    rw [hqdef]
    exact Nat.one_le_pow ν p hp.pos
  have hqpos : 0 < q := by omega
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hqpos
  -- the constant phase factor has modulus one
  have hEnorm :
      ‖Complex.exp (-(2 * Real.pi * Complex.I *
        (((a * g.coeff 0 : ℤ) : ℝ) / (q : ℝ))))‖ = 1 := by
    rw [Complex.norm_exp]
    have hre : (-(2 * Real.pi * Complex.I *
        ((((a * g.coeff 0 : ℤ) : ℝ) / (q : ℝ)) : ℂ))).re = 0 := by
      simp [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
    rw [hre, Real.exp_zero]
  -- split the degree-one complete sum and evaluate the linear complete sum
  rw [completeSum_linear_eq g hdeg a, norm_mul, hEnorm, one_mul,
      sum_range_exp_neg_int_mul_div q hq1 (a * g.coeff 1)]
  have hlead : g.leadingCoeff = g.coeff 1 := by
    rw [Polynomial.leadingCoeff, hdeg]
  by_cases hdvd : (q : ℤ) ∣ a * g.coeff 1
  · -- the linear sum is `q`: the gcd of the leading coefficient with `q` is `q` as well
    rw [if_pos hdvd, Complex.norm_natCast]
    have hdiv : ((p : ℤ) ^ ν) ∣ a * g.coeff 1 := by
      have h := hdvd
      rw [hqdef] at h
      push_cast at h
      exact h
    have hgcd : Nat.gcd (g.coeff 1).natAbs q = q := by
      have h2 := gcd_natAbs_prime_pow_eq_of_dvd_mul hp ha hdiv
      rw [← hqdef] at h2
      exact h2
    rw [hlead, hgcd]
    rw [show ((q:ℕ):ℝ) ^ (1/2 : ℝ) * ((q:ℕ):ℝ) ^ (1/2 : ℝ) = (q:ℝ) by
      rw [← Real.sqrt_eq_rpow, Real.mul_self_sqrt hqR.le]]
  · -- the linear sum vanishes
    rw [if_neg hdvd, norm_zero]
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by positivity) _)

end

end Work.A3
