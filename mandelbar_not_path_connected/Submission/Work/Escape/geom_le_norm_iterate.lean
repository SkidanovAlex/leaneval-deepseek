import Mathlib
import Submission.Work.Escape.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Geometric lower bound for escaping orbits

If `f` has monic degree-`d` growth with constant `A` (`MonicGrowth f d A`, `d ≥ 2`) and
`z` lies in the escaping region `{w | max 2 A < ‖w‖}`, then the orbit of `z` grows at least as
fast as the geometric model `2 * (‖z‖/2) ^ (d ^ n)`:

`2 * (‖z‖ / 2) ^ d ^ n ≤ ‖(f^[n]) z‖`.

The mechanism is that once `r = ‖(f^[m]) z‖` satisfies `r ≥ 2` and `r ≥ A`, the growth inequality
`‖f w‖ ≥ ‖w‖^d - A` gives `r_{m+1} ≥ r^d - A ≥ r^d / 2`, because `r^d ≥ r^2 ≥ 2 A`.  Iterating this
and comparing with `2 * (r/2)^d ≥ 2 (r/2)^d / ... ` produces the stated geometric lower bound;
concretely the quantity `2 * (r_0/2)^{d^m}` transforms as `s_{m+1} = 2 (s_m/2)^d ≥ s_m^d / 2^{d-1}`,
and `2^{d-1} ≥ 2` is exactly what is needed for the induction to close.
-/

namespace Work.Escape

/-- `4 ≤ 2^d` for `d ≥ 2`. -/
private lemma four_le_two_pow {d : ℕ} (hd : 2 ≤ d) : (4 : ℝ) ≤ 2 ^ d := by
  have h : (2 : ℝ) ^ 2 ≤ 2 ^ d := pow_le_pow_right₀ (by norm_num) hd
  norm_num at h
  exact h

/-- `2 y^d ≤ (2y)^d / 2` for `y ≥ 0`, `d ≥ 2`: the constant `2` is beaten by the factor
`2^{d-1} = 2^d/2 ≥ 2`. -/
private lemma two_mul_pow_le_div_two {d : ℕ} (hd : 2 ≤ d) {y : ℝ} (hy : 0 ≤ y) :
    2 * y ^ d ≤ (2 * y) ^ d / 2 := by
  have h4 := four_le_two_pow (d := d) hd
  have hyd : 0 ≤ y ^ d := pow_nonneg hy d
  have h : 4 * y ^ d ≤ 2 ^ d * y ^ d := by
    simpa using mul_le_mul_of_nonneg_right h4 hyd
  rw [mul_pow]
  linarith

/-- Growth comparison lemma: a sequence dominating `x ↦ x^d - A` on the region `{x ≥ 2, x ≥ A}`
starting above `2` and above `A` dominates the geometric model `2 * (r 0 / 2)^{d^n}`. -/
private lemma geom_bound_aux {d : ℕ} {A : ℝ} (hd : 2 ≤ d) {r : ℕ → ℝ}
    (h0 : 2 ≤ r 0) (hA0 : A ≤ r 0)
    (hstep : ∀ n, 2 ≤ r n → A ≤ r n → r n ^ d - A ≤ r (n + 1)) (n : ℕ) :
    2 * (r 0 / 2) ^ (d ^ n) ≤ r n := by
  have key : ∀ n, 2 ≤ r n ∧ A ≤ r n ∧ 2 * (r 0 / 2) ^ (d ^ n) ≤ r n := by
    intro n
    induction n with
    | zero =>
      refine ⟨h0, hA0, ?_⟩
      rw [pow_zero d, pow_one]
      linarith
    | succ n ih =>
      obtain ⟨hr2, hA, hg⟩ := ih
      have h1 : (1 : ℝ) ≤ r n := by linarith
      have h2d : r n ^ 2 ≤ r n ^ d := pow_le_pow_right₀ h1 hd
      have hsq : 2 * A ≤ r n ^ 2 := by nlinarith
      have hhalf : r n ^ d / 2 ≤ r (n + 1) := by
        have := hstep n hr2 hA
        linarith
      have hmono : r n ≤ r n ^ d / 2 := by
        have h3 : r n ≤ r n ^ 2 / 2 := by nlinarith
        linarith
      refine ⟨by linarith, by linarith, ?_⟩
      have ht : 0 ≤ (r 0 / 2) ^ (d ^ n) := pow_nonneg (by linarith) _
      have hle : (r 0 / 2) ^ (d ^ n) ≤ r n / 2 := by linarith
      calc 2 * (r 0 / 2) ^ (d ^ (n + 1))
          = 2 * ((r 0 / 2) ^ (d ^ n)) ^ d := by rw [pow_succ, pow_mul]
        _ ≤ 2 * (r n / 2) ^ d := by
              have := pow_le_pow_left₀ ht hle d
              linarith
        _ ≤ (2 * (r n / 2)) ^ d / 2 := two_mul_pow_le_div_two hd (by linarith)
        _ = r n ^ d / 2 := by
              have : 2 * (r n / 2) = r n := by ring
              rw [this]
        _ ≤ r (n + 1) := hhalf
  exact (key n).2.2

/-- For a `MonicGrowth` map of degree `d ≥ 2`, the orbit of a point of the escaping region grows
at least as fast as the geometric model `2 * (‖z‖/2) ^ d ^ n`. -/
theorem geom_le_norm_iterate (f : ℂ → ℂ) (d : ℕ) (A : ℝ) (h : MonicGrowth f d A) (hd : 2 ≤ d)
    {z : ℂ} (hz : z ∈ escapeRegion A) (n : ℕ) :
    2 * (‖z‖ / 2) ^ d ^ n ≤ ‖(f^[n]) z‖ := by
  have hz2 : 2 ≤ ‖z‖ := (two_lt_norm_of_mem_escapeRegion hz).le
  have hzA : A ≤ ‖z‖ := (lt_norm_of_mem_escapeRegion hz).le
  have hstep : ∀ m : ℕ, 2 ≤ ‖(f^[m]) z‖ → A ≤ ‖(f^[m]) z‖ →
      ‖(f^[m]) z‖ ^ d - A ≤ ‖(f^[m + 1]) z‖ := by
    intro m _ _
    rw [Function.iterate_succ_apply']
    exact h.le_norm ((f^[m]) z)
  have hmain := geom_bound_aux (r := fun m => ‖(f^[m]) z‖) hd
    (by simpa using hz2) (by simpa using hzA) hstep n
  simpa using hmain

end Work.Escape
