/-
# Rational enclosures of `Real.exp (-x)`

The numerical layer of AREA 7 needs rigorous *rational* enclosures of `Real.exp (-x)` for explicit
rational `x > 0`.  Two generic lemmas are proved here from the Taylor bound
`Complex.exp_bound'`:

* `exp_rem_bound` — for `|x| / (n+1) ≤ 1/2`, the `n`-th Taylor partial sum of `exp` differs from
  `exp x` by at most `2 |x|^n / n!`;
* `exp_neg_le_rat`, `exp_neg_ge_rat` — from a rational verification of a single inequality between
  explicit rationals, one obtains `Real.exp (-x) ≤ q`, respectively `q ≤ Real.exp (-x)`.

The instances (one per point of the numerical tables) are generated in `A7/Numerics.lean`.
-/
import Mathlib

open Finset

namespace Work.LinnikAreas.A7

/-- Taylor remainder bound for `Real.exp` at an arbitrary (not necessarily small) point, in the
form needed here: for `|x|/(n+1) ≤ 1/2`, `|exp x - Σ_{m<n} x^m/m!| ≤ 2 |x|^n/n!`. -/
lemma exp_rem_bound (x : ℝ) (n : ℕ) (h : |x| / ((n:ℝ)+1) ≤ 1/2) :
    |Real.exp x - ∑ m ∈ Finset.range n, x^m/(m.factorial : ℝ)| ≤ |x|^n/(n.factorial : ℝ) * 2 := by
  have hxc : ‖(x:ℂ)‖ / (n.succ : ℝ) ≤ 1/2 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    simpa [Nat.cast_succ] using h
  have hb := Complex.exp_bound' (x := (x:ℂ)) (n := n) hxc
  rw [Complex.norm_real, Real.norm_eq_abs] at hb
  have hcast : ((Real.exp x - ∑ m ∈ Finset.range n, x^m/(m.factorial:ℝ) : ℝ) : ℂ)
      = Complex.exp (x:ℂ) - ∑ m ∈ Finset.range n, ((x:ℂ))^m/((m.factorial : ℕ) : ℂ) := by
    push_cast
    rfl
  rw [← hcast] at hb
  rw [Complex.norm_real, Real.norm_eq_abs] at hb
  exact hb

/-- **Upper enclosure of `e^{-x}`.**  If `x ≥ 0` and the explicit rational inequality
`1/q ≤ Σ_{m<n} x^m/m! - 2x^n/n!` holds, then `Real.exp (-x) ≤ q`. -/
lemma exp_neg_le_rat {x : ℝ} (hx : 0 ≤ x) {q : ℝ} (hq : 0 < q) {n : ℕ}
    (h : x / ((n:ℝ)+1) ≤ 1/2)
    (hS : 1/q ≤ (∑ m ∈ Finset.range n, x^m/(m.factorial : ℝ)) - x^n/(n.factorial : ℝ) * 2) :
    Real.exp (-x) ≤ q := by
  have hb := exp_rem_bound x n (by rwa [abs_of_nonneg hx])
  rw [abs_of_nonneg hx] at hb
  have hexp : (∑ m ∈ Finset.range n, x^m/(m.factorial : ℝ)) - x^n/(n.factorial : ℝ) * 2
      ≤ Real.exp x := by
    have := abs_sub_le_iff.1 hb
    linarith [this.1]
  have h1 : q⁻¹ ≤ Real.exp x := by rw [one_div] at hS; exact le_trans hS hexp
  rw [Real.exp_neg]
  exact inv_le_of_inv_le₀ hq h1

/-- **Lower enclosure of `e^{-x}`.**  If `x ≥ 0` and the explicit rational inequality
`Σ_{m<n} x^m/m! + 2x^n/n! ≤ 1/q` holds, then `q ≤ Real.exp (-x)`. -/
lemma exp_neg_ge_rat {x : ℝ} (hx : 0 ≤ x) {q : ℝ} (hq : 0 < q) {n : ℕ}
    (h : x / ((n:ℝ)+1) ≤ 1/2)
    (hS : (∑ m ∈ Finset.range n, x^m/(m.factorial : ℝ)) + x^n/(n.factorial : ℝ) * 2 ≤ 1/q) :
    q ≤ Real.exp (-x) := by
  have hb := exp_rem_bound x n (by rwa [abs_of_nonneg hx])
  rw [abs_of_nonneg hx] at hb
  have hexp : Real.exp x ≤ (∑ m ∈ Finset.range n, x^m/(m.factorial : ℝ)) + x^n/(n.factorial : ℝ) * 2 := by
    have := abs_sub_le_iff.1 hb
    linarith [this.2]
  have h1 : Real.exp x ≤ q⁻¹ := by rw [one_div] at hS; exact le_trans hexp hS
  rw [Real.exp_neg]
  exact (le_inv_comm₀ (Real.exp_pos x) hq).mp h1

end Work.LinnikAreas.A7
