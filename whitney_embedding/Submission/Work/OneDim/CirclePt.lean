import Mathlib

/-!
# Two stereographic coordinates on the unit circle

This file collects the two explicit stereographic parametrisations of the unit circle
`Circle`, used to smooth the seam in the dimension-one classification of manifolds.

* `spherePt t` is the point with coordinates `((1 - t^2)/(1 + t^2), 2t/(1 + t^2))`; it maps `0` to
  `Q = 1` and tends to `Qm = -1` as `t → ±∞`.
* `spherePt' t` is the point with coordinates `((t^2 - 1)/(1 + t^2), 2t/(1 + t^2))`; it maps `0` to
  `Qm = -1` and tends to `Q` as `t → ±∞`.
* `sphereCoord` and `sphereCoord'` are the corresponding inverse coordinates.
-/

namespace Work.OneDim

open scoped Manifold ContDiff Topology
open Set

noncomputable section

/-- The point `1` of the unit circle. -/
def Q : Circle := ⟨1, by
  rw [show (1 : ℂ) ∈ Submonoid.unitSphere ℂ ↔ ‖(1 : ℂ)‖ = 1 from by simp [Submonoid.unitSphere]]
  simp⟩

/-- The point `-1` of the unit circle. -/
def Qm : Circle := ⟨-1, by
  rw [show (-1 : ℂ) ∈ Submonoid.unitSphere ℂ ↔ ‖(-1 : ℂ)‖ = 1 from by simp [Submonoid.unitSphere]]
  simp⟩

/-- The point of `Circle` with stereographic coordinate `t` with respect to the pole `-1`:
`0 ↦ 1`, and `t = ±∞ ↦ -1`. -/
def spherePt (t : ℝ) : Circle :=
  ⟨((1 - t ^ 2 : ℝ) : ℂ) / ((1 + t ^ 2 : ℝ) : ℂ)
      + ((2 * t : ℝ) : ℂ) / ((1 + t ^ 2 : ℝ) : ℂ) * Complex.I, by
    rw [show (((1 - t ^ 2 : ℝ) : ℂ) / ((1 + t ^ 2 : ℝ) : ℂ)
        + ((2 * t : ℝ) : ℂ) / ((1 + t ^ 2 : ℝ) : ℂ) * Complex.I) ∈ Submonoid.unitSphere ℂ ↔
      ‖(((1 - t ^ 2 : ℝ) : ℂ) / ((1 + t ^ 2 : ℝ) : ℂ)
        + ((2 * t : ℝ) : ℂ) / ((1 + t ^ 2 : ℝ) : ℂ) * Complex.I)‖ = 1 from by
        simp [Submonoid.unitSphere]]
    rw [← Complex.ofReal_div, ← Complex.ofReal_div, Complex.norm_add_mul_I, Real.sqrt_eq_one]
    field_simp
    ring⟩

/-- The point of `Circle` with stereographic coordinate `t` with respect to the pole `1`:
`0 ↦ -1`, and `t = ±∞ ↦ 1`. -/
def spherePt' (t : ℝ) : Circle :=
  ⟨((t ^ 2 - 1 : ℝ) : ℂ) / ((1 + t ^ 2 : ℝ) : ℂ)
      + ((2 * t : ℝ) : ℂ) / ((1 + t ^ 2 : ℝ) : ℂ) * Complex.I, by
    rw [show (((t ^ 2 - 1 : ℝ) : ℂ) / ((1 + t ^ 2 : ℝ) : ℂ)
        + ((2 * t : ℝ) : ℂ) / ((1 + t ^ 2 : ℝ) : ℂ) * Complex.I) ∈ Submonoid.unitSphere ℂ ↔
      ‖(((t ^ 2 - 1 : ℝ) : ℂ) / ((1 + t ^ 2 : ℝ) : ℂ)
        + ((2 * t : ℝ) : ℂ) / ((1 + t ^ 2 : ℝ) : ℂ) * Complex.I)‖ = 1 from by
        simp [Submonoid.unitSphere]]
    rw [← Complex.ofReal_div, ← Complex.ofReal_div, Complex.norm_add_mul_I, Real.sqrt_eq_one]
    field_simp
    ring⟩

/-- The stereographic coordinate of a point of the plane, with respect to the pole `-1`. -/
def sphereCoord (z : ℂ) : ℝ := z.im / (1 + z.re)

/-- The stereographic coordinate of a point of the plane, with respect to the pole `1`. -/
def sphereCoord' (z : ℂ) : ℝ := z.im / (1 - z.re)

@[simp] theorem spherePt_apply (t : ℝ) :
    ((spherePt t : Circle) : ℂ)
      = ((1 - t ^ 2 : ℝ) : ℂ) / ((1 + t ^ 2 : ℝ) : ℂ)
          + ((2 * t : ℝ) : ℂ) / ((1 + t ^ 2 : ℝ) : ℂ) * Complex.I := rfl

@[simp] theorem spherePt'_apply (t : ℝ) :
    ((spherePt' t : Circle) : ℂ)
      = ((t ^ 2 - 1 : ℝ) : ℂ) / ((1 + t ^ 2 : ℝ) : ℂ)
          + ((2 * t : ℝ) : ℂ) / ((1 + t ^ 2 : ℝ) : ℂ) * Complex.I := rfl

@[simp] theorem Q_coe : ((Q : Circle) : ℂ) = 1 := rfl

@[simp] theorem Qm_coe : ((Qm : Circle) : ℂ) = -1 := rfl

theorem spherePt_zero : spherePt 0 = Q := by
  ext
  simp [spherePt, Q]

theorem spherePt'_zero : spherePt' 0 = Qm := by
  ext
  simp [spherePt', Qm]

end

end Work.OneDim
