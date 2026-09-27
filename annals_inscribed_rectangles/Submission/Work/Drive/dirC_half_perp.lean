import Mathlib
import Submission.Work.Drive.DirCTools

/-!
# Perpendicularity is a doubled-direction difference of `1/2`

`dirC p` is the class of `arg p / π` in `ℝ/ℤ`, the *doubled* direction of the vector `p ∈ ℝ × ℝ`
(so that directions of lines, i.e. `dirC p` up to sign, are represented by classes modulo `1`).

The main statement `Work.Drive.dirC_half_perp` says that for nonzero `v, w` the doubled directions
differ by `1/2` exactly when `v` and `w` are perpendicular.  Because `1/2 = -1/2` in `ℝ/ℤ` the
condition is orientation free.

The proof is reduced to the elementary polar form of the scalar product: with `z`, `ζ` the complex
numbers attached to `v`, `w`,

`eucDot v w = ‖z‖ * ‖ζ‖ * cos (arg z - arg ζ)`

(which follows from `Complex.cos_arg` / `Complex.sin_arg` and the addition formula for `cos`), while
`dirC v - dirC w = 1/2` in `ℝ/ℤ` says exactly `arg z - arg ζ ≡ π/2 (mod π)`, i.e. that this cosine
vanishes.
-/

namespace Work.Drive

open Submission.Collision (dirC)
open Submission.Geometry (eucDot)

/-- The complex number attached to a point of `ℝ × ℝ` is nonzero iff the point is. -/
lemma ofC_ne_zero {p : ℝ × ℝ} (hp : p ≠ 0) : (⟨p.1, p.2⟩ : ℂ) ≠ 0 := by
  intro h
  apply hp
  exact Prod.ext (by simpa using congrArg Complex.re h) (by simpa using congrArg Complex.im h)

/-- The polar form of the Euclidean scalar product: `eucDot v w` is `‖z‖ ‖ζ‖ cos (arg z - arg ζ)`
where `z`, `ζ` are the complex numbers attached to `v`, `w`. -/
lemma cos_arg_sub_eq (v w : ℝ × ℝ) (hv : v ≠ 0) (hw : w ≠ 0) :
    Real.cos (Complex.arg ⟨v.1, v.2⟩ - Complex.arg ⟨w.1, w.2⟩)
      = eucDot v w / (‖(⟨v.1, v.2⟩ : ℂ)‖ * ‖(⟨w.1, w.2⟩ : ℂ)‖) := by
  rw [Real.cos_sub]
  rw [Complex.cos_arg (ofC_ne_zero hv), Complex.sin_arg, Complex.cos_arg (ofC_ne_zero hw),
    Complex.sin_arg]
  simp only [eucDot]
  field_simp

/-- Two classes of `ℝ/ℤ` given by real numbers coincide exactly when the two numbers differ by an
integer. -/
lemma coe_eq_coe_iff_int (x y : ℝ) :
    ((x : ℝ) : UnitAddCircle) = ((y : ℝ) : UnitAddCircle) ↔ ∃ k : ℤ, (k : ℝ) = x - y := by
  rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
  simp only [zsmul_one]

/-- `θ / π - 1/2` is an integer exactly when `θ ≡ π/2` modulo `π`. -/
lemma exists_int_iff_half (θ : ℝ) :
    (∃ k : ℤ, (k : ℝ) = θ / Real.pi - 1 / 2) ↔
      ∃ k : ℤ, θ = (2 * (k : ℝ) + 1) * Real.pi / 2 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    field_simp at hk ⊢
    linarith
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    field_simp at hk ⊢
    linarith

/-- The doubled-direction difference of `1/2` is exactly the vanishing of the cosine of the
difference of the arguments. -/
lemma dirC_half_iff_cos (v w : ℝ × ℝ) :
    dirC v = dirC w + ((1 / 2 : ℝ) : UnitAddCircle) ↔
      Real.cos (Complex.arg ⟨v.1, v.2⟩ - Complex.arg ⟨w.1, w.2⟩) = 0 := by
  have hsub : dirC v - dirC w
      = (((Complex.arg ⟨v.1, v.2⟩ - Complex.arg ⟨w.1, w.2⟩) / Real.pi : ℝ) :
          UnitAddCircle) := by
    rw [dirC, dirC, ← AddCircle.coe_sub]
    congr 1
    ring
  calc
    dirC v = dirC w + ((1 / 2 : ℝ) : UnitAddCircle)
        ↔ dirC v - dirC w = ((1 / 2 : ℝ) : UnitAddCircle) :=
          sub_eq_iff_eq_add'.symm
    _ ↔ (((Complex.arg ⟨v.1, v.2⟩ - Complex.arg ⟨w.1, w.2⟩) / Real.pi : ℝ) :
            UnitAddCircle) = ((1 / 2 : ℝ) : UnitAddCircle) := by rw [hsub]
    _ ↔ ∃ k : ℤ,
          (k : ℝ) = (Complex.arg ⟨v.1, v.2⟩ - Complex.arg ⟨w.1, w.2⟩) / Real.pi - 1 / 2 :=
          coe_eq_coe_iff_int _ _
    _ ↔ ∃ k : ℤ,
          Complex.arg ⟨v.1, v.2⟩ - Complex.arg ⟨w.1, w.2⟩ =
            (2 * (k : ℝ) + 1) * Real.pi / 2 :=
          exists_int_iff_half _
    _ ↔ Real.cos (Complex.arg ⟨v.1, v.2⟩ - Complex.arg ⟨w.1, w.2⟩) = 0 :=
          Real.cos_eq_zero_iff.symm

open Manifold in
open scoped Manifold ContDiff in
/-- **Perpendicularity is a doubled-direction difference of `1/2`.**

For nonzero vectors `v, w` in the plane, the doubled directions `dirC` (the class of `arg / π` in `ℝ/ℤ`)
differ by `1/2` exactly when `v` and `w` are perpendicular.  Since `1/2 = -1/2` in `ℝ/ℤ` the condition
is orientation-free, and it is the bridge between the collision condition at `u = 1/2`
(`1/2 ∈ GoodC γ`, i.e. the inscribed square) and the geometry used by the classical proof of the
inscribed square: two chords of `γ` with the same midpoint and the same length whose doubled directions
differ by `1/2` are exactly the two diagonals of an inscribed square, and conversely.

Suggested route: `dirC` is `arg / π` in `ℝ/ℤ`, so the condition is
`arg v - arg w ≡ π/2 (mod π)`, which is equivalent to `Real.cos (arg v - arg w) = 0`; and
`eucDot v w = ‖v‖ ‖w‖ cos (arg v - arg w)` is the polar form of the scalar product, where
`‖v‖, ‖w‖ > 0`.  Useful facts: `Complex.arg_eq_pi_div_two_iff`,
`Complex.arg_eq_neg_pi_div_two_iff`, `Complex.re_mul_conj` or `Complex.cos_arg_mul_norm`,
`Real.cos_eq_zero_iff`, `AddCircle.coe_add`, `AddCircle.coe_eq_zero_iff`.  A shorter route is available
in the repo: `Work.Drive.dirC_rot90` (`dirC (rot90 v) = dirC v + 1/2` for `rot90 (x,y) = (-y,x)`,
`v ≠ 0`, in `Submission/Work/Drive/inscribed_square.lean`) together with `Work.Drive.dirC_smul_ne`
(`dirC` depends only on the line through `v`): the condition says exactly that `w` is a nonzero multiple
of `rot90 v`. -/
theorem dirC_half_perp {v w : ℝ × ℝ} (hv : v ≠ 0) (hw : w ≠ 0) :
    Submission.Collision.dirC v = Submission.Collision.dirC w + ((1 / 2 : ℝ) : UnitAddCircle) ↔
      Submission.Geometry.eucDot v w = 0 := by
  rw [dirC_half_iff_cos v w, cos_arg_sub_eq v w hv hw]
  have hne : ‖(⟨v.1, v.2⟩ : ℂ)‖ * ‖(⟨w.1, w.2⟩ : ℂ)‖ ≠ 0 := by
    simp [norm_ne_zero_iff.mpr (ofC_ne_zero hv), norm_ne_zero_iff.mpr (ofC_ne_zero hw)]
  rw [div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · exact h
    · exact absurd h hne
  · intro h
    exact Or.inl h

end Work.Drive
