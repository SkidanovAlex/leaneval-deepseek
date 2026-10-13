import Mathlib
import Submission.Work.DSM4p.Chart

/-!
# DSM4p — the chart generators in "unit" form

Auxiliary API for `Submission/Work/DSM4p/chartMono_estimate.lean` (the monomial estimate of
Bhatt, arXiv:1608.08882, Theorem 3.1(2)).

In the chart model `A = B[1/g]` of `Submission/Work/DSM4p/Chart.lean`, the generator
`x_k(n) = ϖ_k^n / g_k` is a `B`-multiple of the *inverse* of the unit `g_k`.  Keeping that
inverse on the outside is what makes the two-case computation of the estimate work: all
`g`-arithmetic becomes arithmetic in the (commutative) group of units of `A`.

## Contents

* `chartGen_eq_mul_inv` — `x_k(n) = ϖ_k^n · g_k⁻¹`;
* `chartGen_pow_eq` — `x_k(n)^I = ϖ_k^{nI} · (g_k^I)⁻¹`;
* `chartUnit_pow_eq`, `chartUnit_pow_pow'`, `chartUnit_pow_pow` — the root relations
  `g_{k+1}^p = g_k`, `g_{k+r}^{p^r} = g_k`, `g_L^{p^{L-k}} = g_k` in the unit group;
* `rootSystem_pow_pow` — the same for an arbitrary compatible system of `p`-power roots
  (`r L ^ p^{L-k} = r k`), used for `ϖ`.
-/

set_option linter.unusedSectionVars false

namespace Work.DSM4p

universe a

open DSMap DSMap.Mix DSMap.Mix2

variable {p : ℕ} [Fact p.Prime] {B : Type a} [CommRing B]

section ChartUnit

variable {gr : ℕ → B}

/-- The chart generator as a `B`-multiple of the inverse of the unit `g_k`. -/
theorem chartGen_eq_mul_inv (hgr : IsRootSystem p gr) (ϖ : ℕ → B) (n k : ℕ) :
    chartGen hgr ϖ n k =
      algebraMap B (ChartAmbient gr) (ϖ k ^ n) * ↑((chartUnit hgr k)⁻¹) := by
  rw [chartGen, mul_comm]

/-- `x_k(n)^I` again as a `B`-multiple of an inverse unit. -/
theorem chartGen_pow_eq (hgr : IsRootSystem p gr) (ϖ : ℕ → B) (n k I : ℕ) :
    (chartGen hgr ϖ n k) ^ I =
      algebraMap B (ChartAmbient gr) (ϖ k ^ (n * I)) * ↑((chartUnit hgr k ^ I)⁻¹) := by
  rw [chartGen_eq_mul_inv, mul_pow, ← map_pow, ← pow_mul, ← Units.val_pow_eq_pow_val, inv_pow]

/-- The root relation `g_{k+1}^p = g_k` in the unit group of the ambient ring. -/
theorem chartUnit_pow_eq (hgr : IsRootSystem p gr) (k : ℕ) :
    (chartUnit hgr (k + 1)) ^ p = chartUnit hgr k := by
  ext
  rw [Units.val_pow_eq_pow_val, chartUnit_val, chartUnit_val, ← map_pow, hgr k]

/-- Iterated form of the root relation: `g_{k+r}^{p^r} = g_k`. -/
theorem chartUnit_pow_pow' (hgr : IsRootSystem p gr) (k : ℕ) :
    ∀ r : ℕ, (chartUnit hgr (k + r)) ^ (p ^ r) = chartUnit hgr k := by
  intro r
  induction r with
  | zero => simp
  | succ r ih => rw [Nat.add_succ, pow_succ, pow_mul', chartUnit_pow_eq hgr, ih]

/-- `g_L^{p^{L-k}} = g_k` for `k ≤ L`. -/
theorem chartUnit_pow_pow (hgr : IsRootSystem p gr) {k L : ℕ} (h : k ≤ L) :
    (chartUnit hgr L) ^ (p ^ (L - k)) = chartUnit hgr k := by
  rw [← Nat.add_sub_cancel' h, Nat.add_sub_cancel_left, chartUnit_pow_pow' hgr k (L - k)]

end ChartUnit

/-- For any compatible system `r` of `p`-power roots: `r L ^ p^{L-k} = r k` for `k ≤ L`. -/
theorem rootSystem_pow_pow {r : ℕ → B} (h : IsRootSystem p r) {k L : ℕ} (hk : k ≤ L) :
    r L ^ p ^ (L - k) = r k := by
  rw [← Nat.add_sub_cancel' hk, Nat.add_sub_cancel_left, h.pow_pow k (L - k)]

end Work.DSM4p
