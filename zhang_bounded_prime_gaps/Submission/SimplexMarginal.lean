import Mathlib
import Submission.Commons.MeasureTheory.Integral.simplex_integral_scaled
import Submission.Commons.MeasureTheory.Integral.simplex_integral_shifted
import Submission.Commons.MeasureTheory.Integral.marginal_simplex_integral
import Submission.Commons.MeasureTheory.Integral.beta_integral_scaled
import Submission.SimplexMono
import Submission.M4Cert

/-!
# The `J`-functional's Gram matrix on labelled monomials

For `F = (1+ε-P₁)^A ∏_l t_l^{q_l}` the `i = 0` marginal of `F`, i.e.
`∫_0^{(1+ε)-Σ_{l≠0}t_l} F dt₀`, is a polynomial in the remaining coordinates; its
square (resp. the product of two such marginals) integrated over the shrunken
simplex `(1-ε)·R^k` is the `J`-matrix of Polymath8a Theorem 3.13.

This module formalises

  * `margMono_eq`: the inner integral is `κ · L^{A+q₀+1} · ∏_{l≠0} t_l^{q_l}` with
    `L = 1+ε-Σ_{l≠0}t_l` and `κ = A!·q₀!/(A+q₀+1)!` (the one-dimensional beta integral);
  * `JGram_entry`: consequently the integral of the *product* of the two marginals is
    `κ·κ'·(marginal_simplex_integral)`, i.e. the explicit `Psi` sum of the Polymath8a
    §7.2 computation.
-/

open MeasureTheory Finset
open scoped BigOperators

namespace Commons.NumberTheory.MaynardSieve

noncomputable section

/-- κ factor of the one-dimensional beta integral: `∫_0^L (L-s)^A s^p ds = κ L^{A+p+1}`. -/
def kappa (A p : ℕ) : ℝ :=
  (((A.factorial * p.factorial : ℕ)) : ℝ) / (((A + p + 1).factorial : ℕ) : ℝ)

/-- The marginal of the labelled monomial `(1+ε-Σt)^A ∏_l t_l^{q_l}` over the 0-th
coordinate, as a function of the remaining `k` coordinates. -/
def margMono {k : ℕ} (eps : ℝ) (A : ℕ) (q : Fin (k+1) → ℕ) (t : Fin k → ℝ) : ℝ :=
  (∫ s in (0:ℝ)..(1 + eps - ∑ i, t i), (1 + eps - ∑ i, t i - s)^A * s^(q 0)) *
    ∏ i : Fin k, (t i)^(q (Fin.succ i))

/-- The inner marginal integral: `∫_0^L (L-s)^A s^p ds = κ(A,p)·L^{A+p+1}`. -/
theorem margMono_eq {k : ℕ} (eps : ℝ) (A : ℕ) (q : Fin (k+1) → ℕ) (t : Fin k → ℝ)
    (hL : 0 ≤ 1 + eps - ∑ i, t i) :
    margMono eps A q t =
      kappa A (q 0) * (1 + eps - ∑ i, t i)^(A + q 0 + 1) *
        ∏ i : Fin k, (t i)^(q (Fin.succ i)) := by
  unfold margMono kappa
  rw [Commons.MeasureTheory.Integral.beta_integral_scaled hL A (q 0)]
  ring

/-- **The `J`-matrix entry.**  The integral over the shrunken simplex of the product of the
`0`-marginals of `(1+ε-P₁)^A ∏t^{q}` and `(1+ε-P₁)^{A'} ∏t^{q'}` is computed by the labelled
marginal identity. -/
theorem JGram_entry {k : ℕ} (eps : ℝ) (heps0 : 0 < eps) (heps1 : eps < 1)
    (A A' : ℕ) (q q' : Fin (k+1) → ℕ) :
    ∫ t : Fin k → ℝ in {u | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ 1 - eps},
        margMono eps A q t * margMono eps A' q' t
      = kappa A (q 0) * kappa A' (q' 0) *
          ∑ j ∈ Finset.range (A + A' + q 0 + q' 0 + 3),
            ((Nat.choose (A + A' + q 0 + q' 0 + 2) j : ℕ) : ℝ) * (2 * eps) ^ j *
              ((1 - eps) ^ (k + (A + A' + q 0 + q' 0 + 2 - j)
                    + ∑ i : Fin k, (q (Fin.succ i) + q' (Fin.succ i))) *
                ((((Nat.factorial (A + A' + q 0 + q' 0 + 2 - j)) *
                      ∏ i : Fin k, Nat.factorial (q (Fin.succ i) + q' (Fin.succ i)) : ℕ) : ℝ) /
                  ((Nat.factorial ((A + A' + q 0 + q' 0 + 2 - j)
                      + ∑ i : Fin k, (q (Fin.succ i) + q' (Fin.succ i)) + k) : ℕ) : ℝ))) := by
  have hpoint : ∀ t : Fin k → ℝ, 0 ≤ 1 + eps - ∑ i, t i →
      margMono eps A q t * margMono eps A' q' t
        = kappa A (q 0) * kappa A' (q' 0) *
            ((1 + eps - ∑ i, t i) ^ (A + A' + q 0 + q' 0 + 2) *
              ∏ i : Fin k, (t i) ^ (q (Fin.succ i) + q' (Fin.succ i))) := by
    intro t hL
    have hX : (1 + eps - ∑ i, t i) ^ (A + A' + q 0 + q' 0 + 2)
        = (1 + eps - ∑ i, t i) ^ (A + q 0 + 1) * (1 + eps - ∑ i, t i) ^ (A' + q' 0 + 1) := by
      rw [← pow_add]; congr 1; omega
    have hP : (∏ i : Fin k, (t i)^(q (Fin.succ i) + q' (Fin.succ i)))
        = (∏ i : Fin k, (t i)^(q (Fin.succ i))) * ∏ i : Fin k, (t i)^(q' (Fin.succ i)) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun i _ => by rw [← pow_add])
    rw [margMono_eq eps A q t hL, margMono_eq eps A' q' t hL, hX, hP]
    ring
  have hLon : ∀ t ∈ {u : Fin k → ℝ | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ 1 - eps},
      0 ≤ 1 + eps - ∑ i, t i := by
    intro t ht
    have : ∑ i : Fin k, t i ≤ 1 - eps := ht.2
    linarith
  have hmeas : MeasurableSet {u : Fin k → ℝ | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ 1 - eps} :=
    (isClosed_simplexC k (1 - eps)).measurableSet
  rw [MeasureTheory.setIntegral_congr_fun hmeas (fun t ht => hpoint t (hLon t ht))]
  rw [MeasureTheory.integral_const_mul]
  rw [Commons.MeasureTheory.Integral.marginal_simplex_integral eps heps0 heps1 A A' q q']

end

end Commons.NumberTheory.MaynardSieve
