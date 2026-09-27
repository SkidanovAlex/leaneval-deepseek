import Mathlib
import Submission.Work.Mostow.poAux
import Submission.Work.Mostow.StabHoroForm

/-!
# Cauchy–Schwarz for the Minkowski form on the `θ(a)`-orthogonal complement

The null vector `θ(a) = (a, 1)` (`a ∈ Sph n`) is isotropic: `mform (theta a) (theta a) = 0`.
Hence the Minkowski form is *degenerate* on the hyperplane `{x | mform x (theta a) = 0}` and no
positive-definiteness argument applies to it directly.  The structure of that hyperplane is
however transparent: subtracting the `θ(a)`-component of such a vector `x`, i.e. passing to the
shift `x ↦ hspat x - htime x • a`, has Euclidean norm squared exactly `mform x x`, and the
Minkowski pairing of two such vectors is the Euclidean inner product of their images.  The
Cauchy–Schwarz inequality for the Minkowski form on the lightlike hyperplane is therefore the
ordinary Euclidean Cauchy–Schwarz inequality for those images.

This is the algebraic fact underlying the "positive semidefinite on the horosphere tangent
space" statements of the parabolic/horospherical theory.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

/-- **The Minkowski form on `θ(a)ᵗ` is Euclidean.**  If `mform x (theta a) = mform y (theta a) = 0`,
then `mform x y` is the Euclidean inner product of the shifted spatial parts
`hspat x - htime x • a` and `hspat y - htime y • a` (obtained by removing the `θ(a)`-components
of `x` and `y`). -/
lemma mform_eq_inner_shift {n : ℕ} {a : Submission.Mostow.E n} (ha : a ∈ Submission.Mostow.Sph n)
    {x y : Fin n ⊕ Fin 1 → ℝ} (hx : mform x (theta a) = 0) (hy : mform y (theta a) = 0) :
    mform x y = inner ℝ (hspat x - htime x • a) (hspat y - htime y • a) := by
  have hθ := mform_theta_theta_sph a ha
  have hyθ : mform (theta a) y = 0 := by rw [mform_comm]; exact hy
  -- subtracting the `θ(a)`-components does not change the pairing
  have hz : mform (x - htime x • theta a) (y - htime y • theta a) = mform x y := by
    rw [mform_sub_left, mform_sub_right, mform_sub_right, mform_smul_left, mform_smul_right,
      mform_smul_right, mform_smul_left, hx, hyθ, hθ]
    ring
  have hz0 : htime (x - htime x • theta a) = 0 := by simp
  have hz1 : htime (y - htime y • theta a) = 0 := by simp
  rw [← hz, mform_eq, hz0, hz1]
  simp

lemma mformSqLeTheta {n : ℕ} {a : Submission.Mostow.E n} (ha : a ∈ Submission.Mostow.Sph n)
    {x y : Fin n ⊕ Fin 1 → ℝ} (hx : Work.Mostow.mform x (Work.Mostow.theta a) = 0)
    (hy : Work.Mostow.mform y (Work.Mostow.theta a) = 0) :
    (Work.Mostow.mform x y) ^ 2 ≤ Work.Mostow.mform x x * Work.Mostow.mform y y := by
  have hxx := mform_eq_inner_shift ha hx hx
  have hyy := mform_eq_inner_shift ha hy hy
  have hxy := mform_eq_inner_shift ha hx hy
  have hcs := real_inner_mul_inner_self_le
    (hspat x - htime x • a) (hspat y - htime y • a)
  rw [pow_two, hxy, hxx, hyy]
  exact hcs

end Work.Mostow
