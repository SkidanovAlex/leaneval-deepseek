import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Field.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A complex number whose square is a positive real is real

If `z * z = (r : ℂ)` with `r > 0` then `star z = z`.

This is the isolated spot of the `⟸` branch of the reverse Artin–Schreier dictionary
(`Submission/Work/SSGRoute/HRec/NOTES_exists_conjInv_kummerChar.md`): with
`z = Ψ x` and `z * z = ((φ a : ℝ) : ℂ)`, `φ a > 0`, it turns `Ψ (c x) = star (Ψ x)` into
`Ψ (c x) = Ψ x`, whence `c x = x` by injectivity and `x * c x = x * x = a`, i.e. `a ∈ normSet c`.

The route: `z = u + vi` gives `u * u - v * v = r` (`Complex.mul_re`) and `2 * (u * v) = 0`
(`Complex.mul_im`); the first forces `u ≠ 0` (`-v * v ≤ 0 < r`), so `v = 0`, so `z = ↑u` and
`star` fixes it.
-/

noncomputable section

namespace Work.SSGRoute.HRec

theorem star_eq_self_of_mul_self_eq_ofReal {z : ℂ} {r : ℝ} (hr : 0 < r)
    (h : z * z = (r : ℂ)) : starRingEnd ℂ z = z := by
  have him : z.re * z.im + z.im * z.re = 0 := by
    have h' := congrArg Complex.im h
    simpa [Complex.mul_im] using h'
  have hre : z.re * z.re - z.im * z.im = r := by
    have h' := congrArg Complex.re h
    simpa [Complex.mul_re] using h'
  have hzre : z.re ≠ 0 := by
    intro h0
    rw [h0, zero_mul, zero_sub] at hre
    nlinarith [mul_self_nonneg z.im]
  have hzim : z.im = 0 := by
    have h2 : 2 * (z.re * z.im) = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h3 | h3
    · norm_num at h3
    · rcases mul_eq_zero.mp h3 with h4 | h4
      · exact absurd h4 hzre
      · exact h4
  have hz : z = (z.re : ℂ) := by
    apply Complex.ext <;> simp [hzim]
  rw [hz]
  simpa using Complex.conj_ofReal z.re

end Work.SSGRoute.HRec
