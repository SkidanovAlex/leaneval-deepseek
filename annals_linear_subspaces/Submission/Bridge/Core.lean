import Mathlib
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Bridge core: sine of angles and orthogonal residuals

The challenge (`ChallengeDeps`) defines distances between subspaces of `ℝᵈ` via lines and the
sine of unoriented angles between representatives.  The geometry developed for the model
(`planeResidual`, residuals `‖u − π_x u‖`) measures distances via orthogonal projection.

This file proves the bridge facts in the ambient language of a general finite-dimensional real
inner product space `E` (so everything here is Mathlib-only and reusable):

* `sin` of an unoriented angle is invariant under rescaling the vectors by nonzero reals, so it
  is well defined on `Projectivization` elements;
* for unit vectors `u`, `w`: `sin (angle u w) = ‖u - ⟪u,w⟫ • w‖`;
* if `w ∈ x` is a unit vector then `‖u - π_x u‖ ≤ sin (angle u w)`, and the minimum over unit
  vectors of `x` is attained.

All lemmas are in namespace `Submission.Bridge.Core`.
-/

noncomputable section

open scoped LinearAlgebra.Projectivization
open Module Real InnerProductGeometry
open Real

set_option autoImplicit false

namespace Submission.Bridge.Core

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- `sin (angle (-x) y) = sin (angle x y)`. -/
lemma sin_angle_neg_left (x y : E) : sin (angle (-x) y) = sin (angle x y) := by
  rw [angle_neg_left, sin_pi_sub]

/-- `sin (angle x (-y)) = sin (angle x y)`. -/
lemma sin_angle_neg_right (x y : E) : sin (angle x (-y)) = sin (angle x y) := by
  rw [angle_neg_right, sin_pi_sub]

/-- `sin (angle (-x) (-y)) = sin (angle x y)`. -/
lemma sin_angle_neg_neg (x y : E) : sin (angle (-x) (-y)) = sin (angle x y) := by
  rw [angle_neg_left, sin_pi_sub, sin_angle_neg_right]

/-- The sine of an unoriented angle is invariant under rescaling both vectors by *nonzero*
scalars (in particular it only depends on the lines spanned by the two vectors). -/
lemma sin_angle_smul_smul (c d : ℝ) (hc : c ≠ 0) (hd : d ≠ 0) (x y : E) :
    sin (angle (c • x) (d • y)) = sin (angle x y) := by
  rcases lt_or_gt_of_ne hc with hc | hc
  · have h1 := angle_smul_left_of_neg (x := x) (y := d • y) (r := c) hc
    rw [h1]
    rcases lt_or_gt_of_ne hd with hd | hd
    · have h2 := angle_smul_right_of_neg (x := -x) (y := y) (r := d) hd
      rw [h2]
      rw [sin_angle_neg_neg]
    · have h2 := angle_smul_right_of_pos (x := -x) (y := y) (r := d) hd
      rw [h2]
      rw [sin_angle_neg_left]
  · have h1 := angle_smul_left_of_pos (x := x) (y := d • y) (r := c) hc
    rw [h1]
    rcases lt_or_gt_of_ne hd with hd | hd
    · have h2 := angle_smul_right_of_neg (x := x) (y := y) (r := d) hd
      rw [h2]
      rw [sin_angle_neg_right]
    · have h2 := angle_smul_right_of_pos (x := x) (y := y) (r := d) hd
      rw [h2]

/-- The projection onto the orthogonal complement is the residual:
`u - π_s u = π_{sᗮ} u`. -/
lemma residual_eq_starProjection_orthogonal (s : Submodule ℝ E) (u : E) :
    u - s.starProjection u = sᗮ.starProjection u := by
  exact (Submodule.starProjection_orthogonal_val (K := s) u).symm

/-- Pythagoras for the orthogonal residual: `‖u - π_s u‖² = ‖u‖² - ‖π_s u‖²`. -/
lemma norm_sub_starProjection_sq (s : Submodule ℝ E) (u : E) :
    ‖u - s.starProjection u‖ ^ 2 = ‖u‖ ^ 2 - ‖s.starProjection u‖ ^ 2 := by
  have h := Submodule.norm_sq_eq_add_norm_sq_starProjection u s
  have hc2 : ‖sᗮ.starProjection u‖ ^ 2 = ‖u - s.starProjection u‖ ^ 2 := by
    rw [residual_eq_starProjection_orthogonal]
  nlinarith

/-- For `w ∈ s`, the inner product with `u` only sees the projection of `u` onto `s`. -/
lemma inner_eq_inner_starProjection (s : Submodule ℝ E) (u w : E) (hw : w ∈ s) :
    inner ℝ u w = inner ℝ (s.starProjection u) w := by
  have hperp : u - s.starProjection u ∈ sᗮ := s.sub_starProjection_mem_orthogonal u
  have h0 : inner ℝ (u - s.starProjection u) w = 0 := by
    exact inner_eq_zero_symm.mp (Submodule.inner_right_of_mem_orthogonal (K := s) (u := w)
      (v := u - s.starProjection u) hw hperp)
  calc
    inner ℝ u w = inner ℝ ((s.starProjection u) + (u - s.starProjection u)) w := by
        congr 1; abel
    _ = inner ℝ (s.starProjection u) w + inner ℝ (u - s.starProjection u) w := by
        rw [inner_add_left]
    _ = inner ℝ (s.starProjection u) w := by rw [h0, add_zero]

/-- Cauchy–Schwarz form used below: for a unit vector `w ∈ s`, `⟪u, w⟫² ≤ ‖π_s u‖²`. -/
lemma inner_sq_le_starProjection_sq (s : Submodule ℝ E) (u w : E) (hw : w ∈ s) (hw1 : ‖w‖ = 1) :
    (inner ℝ u w) ^ 2 ≤ ‖s.starProjection u‖ ^ 2 := by
  have hmain : inner ℝ u w = inner ℝ (s.starProjection u) w := inner_eq_inner_starProjection s u w hw
  rw [hmain]
  have h := real_inner_mul_inner_self_le (s.starProjection u) w
  calc
    (inner ℝ (s.starProjection u) w) ^ 2
        ≤ (inner ℝ (s.starProjection u) (s.starProjection u)) * (inner ℝ w w) := by simpa [sq] using h
    _ = ‖s.starProjection u‖ ^ 2 * ‖w‖ ^ 2 := by rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    _ = ‖s.starProjection u‖ ^ 2 := by rw [hw1]; ring

/-- Square norm of the distance from a vector `u` to the line spanned by `w`. -/
lemma norm_sub_inner_smul_sq (u w : E) :
    ‖u - inner ℝ u w • w‖ ^ 2 = ‖u‖ ^ 2 - 2 * (inner ℝ u w) ^ 2 + (inner ℝ u w) ^ 2 * ‖w‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq (u - inner ℝ u w • w)]
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    RCLike.conj_to_real]
  rw [real_inner_comm w u]
  rw [real_inner_self_eq_norm_sq u, real_inner_self_eq_norm_sq w]
  ring

/-- For unit `u`, `w`: `‖u - ⟪u,w⟫ • w‖² = 1 - ⟪u,w⟫²`. -/
lemma norm_sub_inner_smul_sq_unit (u w : E) (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) :
    ‖u - inner ℝ u w • w‖ ^ 2 = 1 - (inner ℝ u w) ^ 2 := by
  rw [norm_sub_inner_smul_sq]
  rw [hu, hw]
  ring

/-- **Core identity**: for unit vectors `u`, `w`, the sine of the angle between them is the
distance from `u` to the line spanned by `w`. -/
lemma sin_angle_eq_dist_unit (u w : E) (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) :
    sin (angle u w) = ‖u - inner ℝ u w • w‖ := by
  have hs : 0 ≤ sin (angle u w) := sin_angle_nonneg u w
  have hn : 0 ≤ ‖u - inner ℝ u w • w‖ := norm_nonneg _
  apply (sq_eq_sq₀ hs hn).1
  have hcos : Real.cos (angle u w) = inner ℝ u w := by
    have h := cos_angle_mul_norm_mul_norm u w
    simpa [hu, hw] using h
  have hmain : sin (angle u w) ^ 2 = 1 - (inner ℝ u w) ^ 2 := by
    rw [← hcos]
    have hsq := sin_sq_add_cos_sq (angle u w)
    nlinarith
  rw [hmain]
  exact (norm_sub_inner_smul_sq_unit u w hu hw).symm

/-- Projection to a subspace containing a line is at least as good as projection to that line:
for unit `u` and unit `w ∈ s`, `‖u - π_s u‖ ≤ sin (angle u w)`. -/
lemma residual_le_sin_angle {s : Submodule ℝ E} (u w : E) (hu : ‖u‖ = 1) (hw : ‖w‖ = 1)
    (hws : w ∈ s) :
    ‖u - s.starProjection u‖ ≤ sin (angle u w) := by
  have hs : 0 ≤ ‖u - s.starProjection u‖ := norm_nonneg _
  have hn : 0 ≤ sin (angle u w) := sin_angle_nonneg u w
  rw [← sq_le_sq₀ hs hn]
  have h1 : ‖u - s.starProjection u‖ ^ 2 = 1 - ‖s.starProjection u‖ ^ 2 := by
    rw [norm_sub_starProjection_sq, hu]
    ring
  have h2 : sin (angle u w) ^ 2 = 1 - (inner ℝ u w) ^ 2 := by
    have hcos : Real.cos (angle u w) = inner ℝ u w := by
      have hc := cos_angle_mul_norm_mul_norm u w
      simpa [hu, hw] using hc
    rw [← hcos]
    have hsq := sin_sq_add_cos_sq (angle u w)
    nlinarith
  rw [h1, h2]
  have h := inner_sq_le_starProjection_sq s u w hws hw
  nlinarith

/-- A nonzero subspace contains a unit vector. -/
lemma exists_unit_of_ne_bot (s : Submodule ℝ E) (hs : s ≠ ⊥) :
    ∃ w : E, w ∈ s ∧ ‖w‖ = 1 := by
  rcases s.exists_mem_ne_zero_of_ne_bot hs with ⟨w, hws, hw0⟩
  refine ⟨(‖w‖)⁻¹ • w, s.smul_mem (‖w‖)⁻¹ hws, ?_⟩
  rw [norm_smul]
  rw [Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg w))]
  rw [inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw0)]

/-- Sine invariant under rescaling the *left* vector by a nonzero scalar. -/
lemma sin_angle_smul_left (c : ℝ) (hc : c ≠ 0) (x y : E) :
    sin (angle (c • x) y) = sin (angle x y) := by
  simpa using sin_angle_smul_smul c 1 hc one_ne_zero x y

/-- Sine invariant under rescaling the *right* vector by a nonzero scalar. -/
lemma sin_angle_smul_right (d : ℝ) (hd : d ≠ 0) (x y : E) :
    sin (angle x (d • y)) = sin (angle x y) := by
  simpa using sin_angle_smul_smul 1 d one_ne_zero hd x y

/-- The representative of a line lies in the line. -/
lemma rep_mem_self (Z : ℙ ℝ E) : Z.rep ∈ Z.submodule := by
  rw [Projectivization.submodule_eq]
  exact Submodule.subset_span (by simp : Z.rep ∈ ({Z.rep} : Set E))

/-- The representative of `mk v hv` is a nonzero scalar multiple of `v`. -/
lemma mk_rep_smul (v : E) (hv : v ≠ 0) :
    ∃ a : ℝ, a ≠ 0 ∧ (Projectivization.mk ℝ v hv).rep = a • v := by
  rcases Projectivization.exists_smul_eq_mk_rep ℝ v hv with ⟨a, ha⟩
  exact ⟨a, (Units.ne_zero a), ha.symm⟩

/-- A unit vector is nonzero. -/
lemma ne_zero_of_norm_eq_one {v : E} (h : ‖v‖ = 1) : v ≠ 0 := by
  intro hv
  rw [hv] at h
  norm_num at h

end Submission.Bridge.Core
