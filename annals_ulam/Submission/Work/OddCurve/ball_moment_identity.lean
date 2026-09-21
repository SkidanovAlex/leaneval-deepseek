import Mathlib
import Submission.Work.OddCurve.Defs

/-!
# `Work.OddCurve.ball_moment_identity`

The moment identities of the **unit ball** with respect to the family of lines
`L_s t = s * t` (i.e. `h ≡ 0`) in the odd-dimensional case, in the exact shape in which
they are consumed by the chord-curve machinery.

Writing `c = √(1 + s²)` and substituting `t = u / c`, the radicand becomes

`1 - t² - (s t)² = 1 - (c t)² = 1 - u²`,

so the first moment is `c⁻¹` times the reference constant `refConst n`, and the second
integrand is odd, whence its integral over the symmetric interval vanishes.

The two elementary ingredients are isolated as `integral_scale_one_div` (the affine change of
variables `t = u / c` on a symmetric interval) and `integral_odd_symm_eq_zero` (an odd function
has vanishing integral over a symmetric interval, valid unconditionally since both sides are
Bochner integrals).
-/

namespace Work.OddCurve

noncomputable section

open MeasureTheory Set
open scoped Interval

/-- Affine change of variables on a symmetric interval: for `c ≠ 0`,
`∫_{-1/c}^{1/c} G (c t) dt = c⁻¹ ∫_{-1}^{1} G`. -/
lemma integral_scale_one_div (G : ℝ → ℝ) {c : ℝ} (hc : c ≠ 0) :
    (∫ t in (-(1 / c))..(1 / c), G (c * t)) = c⁻¹ * ∫ u in (-1 : ℝ)..1, G u := by
  have h1 : c * (-(1 / c)) = -1 := by field_simp
  have h2 : c * (1 / c) = 1 := by field_simp
  rw [intervalIntegral.integral_comp_mul_left G hc, h1, h2, smul_eq_mul]

/-- An odd function has vanishing integral over a symmetric interval. -/
lemma integral_odd_symm_eq_zero (F : ℝ → ℝ) (a : ℝ) (hF : ∀ t, F (-t) = -F t) :
    (∫ t in (-a)..a, F t) = 0 := by
  have h1 : (∫ t in (-a)..a, F (-t)) = ∫ t in (-a)..a, F t := by
    rw [intervalIntegral.integral_comp_neg F, neg_neg]
  have h2 : (∫ t in (-a)..a, F (-t)) = -∫ t in (-a)..a, F t := by
    rw [show (∫ t in (-a)..a, F (-t)) = ∫ t in (-a)..a, -F t from
      intervalIntegral.integral_congr (f := fun t => F (-t)) (g := fun t => -F t)
        (fun t _ => hF t)]
    rw [intervalIntegral.integral_neg]
  rw [h1] at h2
  linarith

/-- **The ball moment identity.**  For the unit ball and the lines `L_s t = s * t`, the volume
moment of the slab cut by `L_s` equals the reference constant divided by `√(1 + s²)`, and the
centroid moment vanishes (the slab is symmetric about the origin). -/
theorem ball_moment_identity (n : ℕ) (s : ℝ) :
    (∫ t in (-(1 / Real.sqrt (1 + s ^ 2)))..(1 / Real.sqrt (1 + s ^ 2)),
        (1 - t ^ 2 - (s * t) ^ 2) ^ n * Real.sqrt (1 - t ^ 2 - (s * t) ^ 2)) =
      Work.OddCurve.refConst n / Real.sqrt (1 + s ^ 2) ∧
    (∫ t in (-(1 / Real.sqrt (1 + s ^ 2)))..(1 / Real.sqrt (1 + s ^ 2)),
        (1 - t ^ 2 - (s * t) ^ 2) ^ (n - 1) * Real.sqrt (1 - t ^ 2 - (s * t) ^ 2) * t) = 0 := by
  set c : ℝ := Real.sqrt (1 + s ^ 2) with hc
  have hcpos : 0 < c := by rw [hc]; exact Real.sqrt_pos.mpr (by positivity)
  have hcne : c ≠ 0 := ne_of_gt hcpos
  have hcsq : c ^ 2 = 1 + s ^ 2 := by rw [hc]; exact Real.sq_sqrt (by positivity)
  -- the radicand is `1 - (c t) ^ 2`
  have hkey : ∀ t : ℝ, 1 - t ^ 2 - (s * t) ^ 2 = 1 - (c * t) ^ 2 := by
    intro t; rw [mul_pow, mul_pow, hcsq]; ring
  constructor
  · -- the volume moment: substitute `t = u / c`
    have hrewrite : (∫ t in (-(1 / c))..(1 / c),
          (1 - t ^ 2 - (s * t) ^ 2) ^ n * Real.sqrt (1 - t ^ 2 - (s * t) ^ 2))
        = ∫ t in (-(1 / c))..(1 / c),
            (fun u => (1 - u ^ 2) ^ n * Real.sqrt (1 - u ^ 2)) (c * t) := by
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only
      rw [hkey t]
    rw [hrewrite,
      integral_scale_one_div (fun u => (1 - u ^ 2) ^ n * Real.sqrt (1 - u ^ 2)) hcne]
    rw [refConst_def, div_eq_inv_mul]
  · -- the centroid moment: the integrand is odd
    refine integral_odd_symm_eq_zero
      (fun t => (1 - t ^ 2 - (s * t) ^ 2) ^ (n - 1) * Real.sqrt (1 - t ^ 2 - (s * t) ^ 2) * t)
      (1 / c) ?_
    intro t
    have h2 : 1 - (-t) ^ 2 - (s * (-t)) ^ 2 = 1 - t ^ 2 - (s * t) ^ 2 := by ring
    rw [h2]
    ring

end

end Work.OddCurve
