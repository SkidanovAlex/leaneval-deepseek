import Mathlib
import Submission.Work.EQ.SymDefs

/-!
# Compactness of a polar curve with continuous `2π`-periodic radial function

`Work.EQ.polarPt_compact`: if `ρ : ℝ → ℝ` is continuous and `2π`-periodic, then the polar curve
`θ ↦ polarPt c (ρ θ) θ` (the graph of `ρ` in polar coordinates about the real point `c`) has
compact range.

No boundedness or positivity of `ρ` is assumed: continuity plus periodicity already force the
range to be the image of the compact interval `[0, 2π]`. Indeed the *point* `polarPt c r θ`
depends on the angle only through the factor `Complex.exp (θ * I)`, which has period `2π`, so
the curve map `θ ↦ polarPt c (ρ θ) θ` is itself `2π`-periodic (Mathlib's
`Function.Periodic.image_Icc` identifies the range of a periodic continuous function with the
image of one period interval), and the continuous image of `[0, 2π]` is compact.

This is the compactness input of the equichordal development: it turns the range of a
normalised equichordal curve into a compact subset of the plane.
-/

namespace Work.EQ

open Complex

/-- Shifting the polar angle by `2π` does not move the point `polarPt c r θ`: the angle enters
only through the factor `Complex.exp (θ * I)`, which has period `2π`. -/
private theorem polarPt_angle_periodic (c r : ℝ) :
    Function.Periodic (fun θ : ℝ => polarPt c r θ) (2 * Real.pi) := by
  intro θ
  simp only [polarPt]
  have h : ((θ + 2 * Real.pi : ℝ) : ℂ) * Complex.I
      = (θ : ℂ) * Complex.I + (2 * ↑Real.pi * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- **The polar graph of a continuous periodic radial function is compact.**  For a continuous
`2π`-periodic `ρ`, the curve `θ ↦ polarPt c (ρ θ) θ` has compact range. -/
theorem polarPt_compact {a : ℝ} {ρ : ℝ → ℝ} (hcont : Continuous ρ)
    (hper : ∀ θ, ρ (θ + 2 * Real.pi) = ρ θ) :
    IsCompact (Set.range (fun θ => polarPt (-(a/2)) (ρ θ) θ)) := by
  set F : ℝ → ℂ := fun θ => polarPt (-(a / 2)) (ρ θ) θ with hF
  -- the curve map is continuous
  have hFcont : Continuous F := by
    rw [hF]
    unfold polarPt
    fun_prop
  -- and `2π`-periodic, because `ρ` is and because the angle enters through `exp (θ * I)`
  have hFper : Function.Periodic F (2 * Real.pi) := by
    intro θ
    rw [hF]
    show polarPt (-(a / 2)) (ρ (θ + 2 * Real.pi)) (θ + 2 * Real.pi) =
      polarPt (-(a / 2)) (ρ θ) θ
    rw [hper θ]
    exact polarPt_angle_periodic (-(a / 2)) (ρ θ) θ
  -- hence the range is the image of the compact interval `[0, 2π]`
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hEq : Set.range F = F '' Set.Icc 0 (2 * Real.pi) := by
    simpa using (hFper.image_Icc h2pi 0).symm
  rw [hEq]
  exact isCompact_Icc.image hFcont

end Work.EQ
