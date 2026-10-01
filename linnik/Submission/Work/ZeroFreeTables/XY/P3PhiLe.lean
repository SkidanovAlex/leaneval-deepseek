/-
# ZeroFreeTables/XY/P3PhiLe — the `P₃` comparison `Re P₃(α/(β+it)) ≤ (α/β)³ Re P₃(α/(α+it))`

For `0 < β ≤ α` and any real `c`, Heath-Brown's polynomial (4.12)
`P₃(X) = X + X² + (2/3)X³` satisfies

  `Re P₃(α/(β+ic)) ≤ (α/β)³ · Re P₃(α/(α+ic))`.

This is the elementary comparison ("larger value ⇒ smaller weight, after the `α/β` scaling")
used when the near-zero term of HB (9.8) is compared with the reference value at the point
`1 + i·Im s`.

The proof is entirely real-variable.  With `u = β/α` (`0 < u ≤ 1`) and `v = c/α`,
`(α/(β+ic)) = (u+iv)⁻¹` and `(α/(α+ic)) = (1+iv)⁻¹`, and the two real parts are

  `Re P₃((u+iv)⁻¹) = (3(u−1)v⁴ + 6u(u²−1)v² + 3u⁵ + 3u⁴ + 2u³) / (3(u²+v²)³)`,
  `Re P₃((1+iv)⁻¹) = 8 / (3(1+v²)³)`.

Writing `N = 3(u−1)v⁴ + 6u(u²−1)v² + u³(3u²+3u+2)`, monotonicity in `v` gives
`Re P₃((u+iv)⁻¹) ≤ u³(3u²+3u+2)/(3(u²+v²)³)`, and the comparison
`u³(3u²+3u+2)/(3(u²+v²)³) ≤ (1/u)³·8/(3(1+v²)³)` reduces to
`u⁶(3u²+3u+2)(1+v²)³ ≤ 8(u²+v²)³`, which follows from
`u²(1+v²) ≤ u²+v²` (i.e. `v²(1−u²) ≥ 0`) together with `3u²+3u+2 ≤ 8` for `u ≤ 1`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P3.DefsL

namespace Work.ZeroFreeTables.XY

open Complex
open scoped Classical BigOperators

/-- The real part of `P₃` at the inverse of `u+iv` (`u > 0`), in closed form. -/
lemma P3_inv_re (u v : ℝ) (hu : 0 < u) :
    (Work.ZeroFreeTables.P3 (((u : ℂ) + (v : ℂ) * Complex.I)⁻¹)).re
      = (3*(u-1)*v^4 + 6*u*(u^2-1)*v^2 + 3*u^5+3*u^4+2*u^3) / (3*(u^2+v^2)^3) := by
  set z : ℂ := (u : ℂ) + (v : ℂ) * Complex.I with hz
  have hzre : z.re = u := by rw [hz]; simp
  have hzim : z.im = v := by rw [hz]; simp
  have hnorm : z.normSq = u^2+v^2 := by
    rw [Complex.normSq_apply, hzre, hzim]; ring
  have hre : z⁻¹.re = u/(u^2+v^2) := by rw [Complex.inv_re, hnorm, hzre]
  have him : z⁻¹.im = -v/(u^2+v^2) := by rw [Complex.inv_im, hnorm, hzim]
  have h2 : ((z⁻¹)^2).re = z⁻¹.re^2 - z⁻¹.im^2 := by rw [pow_two, Complex.mul_re]; ring
  have h2im : ((z⁻¹)^2).im = 2*z⁻¹.re*z⁻¹.im := by rw [pow_two, Complex.mul_im]; ring
  have h3 : ((z⁻¹)^3).re = z⁻¹.re^3 - 3*z⁻¹.re*z⁻¹.im^2 := by
    rw [show (z⁻¹)^3 = (z⁻¹)^2 * z⁻¹ by ring, Complex.mul_re, h2, h2im]; ring
  have hval : (Work.ZeroFreeTables.P3 (z⁻¹)).re
      = z⁻¹.re + (z⁻¹.re^2 - z⁻¹.im^2)
          + (2/3)*(z⁻¹.re^3 - 3*z⁻¹.re*z⁻¹.im^2) := by
    rw [Work.ZeroFreeTables.P3]; simp only [Complex.add_re, Complex.mul_re]
    rw [h2, h3]; norm_num
  change (Work.ZeroFreeTables.P3 (z⁻¹)).re = _
  rw [hval, hre, him]
  have hD : (0:ℝ) < u^2+v^2 := by positivity
  field_simp
  ring

/-- The value at the reference point: `Re P₃((1+iv)⁻¹) = 8/(3(1+v²)³)` (HB: with
`P₃(X)=X+X²+(2/3)X³` one has `Re P₃(1/(1+iy)) = (8/3)/(1+y²)³`). -/
lemma P3_inv_re_one (v : ℝ) :
    (Work.ZeroFreeTables.P3 (((1 : ℂ) + (v : ℂ) * Complex.I)⁻¹)).re
      = 8/(3*(1+v^2)^3) := by
  rw [show (1:ℂ) = ((1:ℝ):ℂ) from Complex.ofReal_one.symm]
  rw [P3_inv_re 1 v one_pos]
  norm_num

/-- The elementary real inequality behind the comparison: for `0 < u ≤ 1` and any real `v`,
the `P₃`-weight at `u` is dominated by the (`(1/u)³`-scaled) reference weight at `u = 1`. -/
lemma key_bound (u v : ℝ) (hu : 0 < u) (hu1 : u ≤ 1) :
    (3*(u-1)*v^4 + 6*u*(u^2-1)*v^2 + 3*u^5+3*u^4+2*u^3)/(3*(u^2+v^2)^3)
      ≤ (1/u)^3 * (8/(3*(1+v^2)^3)) := by
  have hw1 : 0 ≤ v^2 := sq_nonneg v
  have hu2 : u^2 ≤ 1 := pow_le_one₀ hu.le hu1
  have ht : 3*u^2+3*u+2 ≤ 8 := by nlinarith [hu2, hu1]
  have hN : 3*(u-1)*v^4 + 6*u*(u^2-1)*v^2 + 3*u^5+3*u^4+2*u^3
      ≤ u^3*(3*u^2+3*u+2) := by
    have h1 : 3*(u-1)*v^4 ≤ 0 := by
      apply mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    have h2 : 6*u*(u^2-1)*v^2 ≤ 0 := by
      apply mul_nonpos_of_nonpos_of_nonneg _ hw1
      nlinarith [hu, hu2]
    have h3 : 3*u^5+3*u^4+2*u^3 = u^3*(3*u^2+3*u+2) := by ring
    linarith [h1, h2, h3]
  refine le_trans (div_le_div_of_nonneg_right hN (by positivity)) ?_
  have hA : u^2*(1+v^2) ≤ u^2+v^2 := by
    have : 0 ≤ v^2*(1-u^2) := mul_nonneg hw1 (by linarith)
    nlinarith [this]
  have hcrux : u^6*(3*u^2+3*u+2)*(1+v^2)^3 ≤ 8*(u^2+v^2)^3 := by
    have hcube : (u^2*(1+v^2))^3 ≤ (u^2+v^2)^3 := pow_le_pow_left₀ (by positivity) hA 3
    have hp : (u^2*(1+v^2))^3 = u^6*(1+v^2)^3 := by ring
    rw [hp] at hcube
    have hpos : 0 ≤ u^6*(1+v^2)^3 := by positivity
    have h2 := mul_le_mul_of_nonneg_left ht hpos
    nlinarith [hcube, h2]
  have hR : (1/u)^3*(8/(3*(1+v^2)^3)) = 8/(3*u^3*(1+v^2)^3) := by
    rw [one_div_pow]; field_simp
  rw [hR]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hcrux]

theorem P3PhiLe (α β c : ℝ) (hα : 0 < α) (hβ : 0 < β) (h : β ≤ α) :
    (Work.ZeroFreeTables.P3 ((α : ℂ) / ((β : ℂ) + (c : ℂ) * Complex.I))).re
      ≤ (α / β) ^ 3 * (Work.ZeroFreeTables.P3 ((α : ℂ) / ((α : ℂ) + (c : ℂ) * Complex.I))).re := by
  set u : ℝ := β / α with hu
  set v : ℝ := c / α with hv
  have hu_pos : 0 < u := by rw [hu]; positivity
  have hu_le : u ≤ 1 := by rw [hu]; rw [div_le_one hα]; exact h
  have harg1 : (α : ℂ) / ((β : ℂ) + (c : ℂ) * Complex.I)
      = ((u : ℂ) + (v : ℂ) * Complex.I)⁻¹ := by
    have h1 : ((u : ℂ) + (v : ℂ) * Complex.I)
        = (((β : ℂ) + (c : ℂ) * Complex.I) / (α : ℂ)) := by
      rw [hu, hv]; push_cast; ring
    rw [h1, inv_div]
  have harg2 : (α : ℂ) / ((α : ℂ) + (c : ℂ) * Complex.I)
      = ((1 : ℂ) + (v : ℂ) * Complex.I)⁻¹ := by
    have h1 : ((1 : ℂ) + (v : ℂ) * Complex.I)
        = (((α : ℂ) + (c : ℂ) * Complex.I) / (α : ℂ)) := by
      have hαc : (α : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hα
      rw [hv]; push_cast
      rw [eq_div_iff hαc]; field_simp
    rw [h1, inv_div]
  rw [harg1, harg2]
  rw [P3_inv_re u v hu_pos, P3_inv_re_one v]
  have hscale : (α / β)^3 = (1/u)^3 := by rw [hu, one_div, inv_div]
  rw [hscale]
  exact key_bound u v hu_pos hu_le

end Work.ZeroFreeTables.XY
