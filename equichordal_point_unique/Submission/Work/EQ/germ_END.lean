import Mathlib
import Submission.Work.EQ.Defs
import Submission.Work.EQ.germ_poly_identity

namespace Work.EQ

/-- Scalar algebra behind `germ_END`: if `L - 1 = -a (L+1)` and `L ≠ 0` then for every `p`
```
(p - p/L)² (L p - p)² = a² p² (L p - p/L)² .
```
Indeed both sides reduce to `p⁴ (L-1)⁴ / L² = a⁴ p⁴ (L+1)⁴ / L²` once `(L-1)² = a² (L+1)²`.
This is exactly the `u = 0` instance of the requested identity, valid for arbitrary `p`. -/
private lemma germ_END_algebra (a p L : ℂ) (hL : L ≠ 0) (hrel : L - 1 = -(a * (L + 1))) :
    (p - p / L) ^ 2 * (L * p - p) ^ 2 = a ^ 2 * p ^ 2 * (L * p - p / L) ^ 2 := by
  have hsq : (L - 1) ^ 2 = a ^ 2 * (L + 1) ^ 2 := by rw [hrel]; ring
  have key : (p - p / L) ^ 2 * (L * p - p) ^ 2 - a ^ 2 * p ^ 2 * (L * p - p / L) ^ 2
      = p ^ 4 / L ^ 2 * (L - 1) ^ 2 * ((L - 1) ^ 2 - a ^ 2 * (L + 1) ^ 2) := by
    field_simp
    ring
  have h0 : (p - p / L) ^ 2 * (L * p - p) ^ 2 - a ^ 2 * p ^ 2 * (L * p - p / L) ^ 2 = 0 := by
    rw [key, hsq]; ring
  exact sub_eq_zero.mp h0

theorem germ_END {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : Work.EQ.IsStableGerm a h r) {N D : Polynomial ℂ} (hD0 : Polynomial.eval 0 D ≠ 0)
    (hDN : ∀ᶠ u in nhds (0 : ℂ), h u * Polynomial.eval u D = Polynomial.eval u N)
    {c : ℂ} (hc : c ≠ 0) (hN : N = Polynomial.C c * Polynomial.X) :
    ∀ u : ℂ,
      (Polynomial.eval (u / (Work.EQ.eqLam a : ℂ)) D - Polynomial.eval u D / (Work.EQ.eqLam a : ℂ)) ^ 2 *
        ((Work.EQ.eqLam a : ℂ) * Polynomial.eval u D - Polynomial.eval ((Work.EQ.eqLam a : ℂ) * u) D) ^ 2
      = ((a : ℂ)) ^ 2 * (c ^ 2 * u ^ 2 + Polynomial.eval u D ^ 2) *
        ((Work.EQ.eqLam a : ℂ) * Polynomial.eval (u / (Work.EQ.eqLam a : ℂ)) D -
          Polynomial.eval ((Work.EQ.eqLam a : ℂ) * u) D / (Work.EQ.eqLam a : ℂ)) ^ 2 := by
  have hL : (Work.EQ.eqLam a : ℂ) ≠ 0 := by
    rw [Work.EQ.eqLam]
    have : (((1 - a) / (1 + a) : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]
      exact div_ne_zero (by linarith) (by linarith)
    simpa using this
  have hrelR : Work.EQ.eqLam a - 1 = -(a * (Work.EQ.eqLam a + 1)) := by
    rw [Work.EQ.eqLam]; field_simp; ring
  have hrel : (Work.EQ.eqLam a : ℂ) - 1 = -((a : ℂ) * ((Work.EQ.eqLam a : ℂ) + 1)) := by
    have hm := congrArg (fun x : ℝ => (x : ℂ)) hrelR
    push_cast at hm
    exact hm
  intro u
  rcases eq_or_ne u 0 with hu0 | hu
  · -- `u = 0`: both `eval` arguments collapse to `0`, and the identity is the scalar relation
    -- `(λ-1)² = a²(λ+1)²`.
    subst hu0
    simp only [zero_div, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add]
    exact germ_END_algebra (a : ℂ) (Polynomial.eval 0 D) (Work.EQ.eqLam a : ℂ) hL hrel
  · -- `u ≠ 0`: `germ_poly_identity` for the numerator `N = cX` is this identity multiplied by
    -- `(c u)⁴`, which is non-zero and may be cancelled.
    have hcu : c * u ≠ 0 := mul_ne_zero hc hu
    have h4 : (c * u) ^ 4 ≠ 0 := pow_ne_zero 4 hcu
    have hPIu := Work.EQ.germ_poly_identity ha0 ha1 hh hD0 hDN u
    rw [hN] at hPIu
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] at hPIu
    have hgoal : (c * u) ^ 4 *
        ((Polynomial.eval (u / (Work.EQ.eqLam a : ℂ)) D - Polynomial.eval u D / (Work.EQ.eqLam a : ℂ)) ^ 2 *
          ((Work.EQ.eqLam a : ℂ) * Polynomial.eval u D - Polynomial.eval ((Work.EQ.eqLam a : ℂ) * u) D) ^ 2)
      = (c * u) ^ 4 * (((a : ℂ)) ^ 2 * (c ^ 2 * u ^ 2 + Polynomial.eval u D ^ 2) *
        ((Work.EQ.eqLam a : ℂ) * Polynomial.eval (u / (Work.EQ.eqLam a : ℂ)) D -
          Polynomial.eval ((Work.EQ.eqLam a : ℂ) * u) D / (Work.EQ.eqLam a : ℂ)) ^ 2) := by
      linear_combination hPIu
    exact mul_left_cancel₀ h4 hgoal

end Work.EQ
