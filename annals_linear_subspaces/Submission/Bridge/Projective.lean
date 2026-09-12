import Mathlib
import Submission.Bridge.Core

/-!
# Bridge, projective layer: distances from a line to a subspace

The challenge (`ChallengeDeps`) defines distances between subspaces of `ℝᵈ` via lines in the
projectivization `ℙ ℝ ℝᵈ` and the sine of the unoriented angle between representatives.  Here
we prove, in a general finite-dimensional real inner product space `E` (Mathlib-only), the
*line-to-subspace* identity behind that definition:

For a unit vector `u` and a subspace `s ≠ ⊥`,

`lineToSubspace (Projectivization.mk ℝ u hu) s = ‖u - π_s u‖`

where `lineToSubspace X s = ⨅ Z : {Z : ℙ ℝ E // Z.submodule ≤ s}, sin (angle X.rep Z.rep)`.

The infimum over the lines of `s` of the sine of the angle with `X` is the sine of the angle
between the line and the subspace, i.e. the norm of the orthogonal residual.  This is the
`distLineSubspace` of the challenge (equal to the `distLines`-infimum over lines of the
subspace).

All statements are in namespace `Submission.Bridge.Projective`.
-/

noncomputable section

open scoped LinearAlgebra.Projectivization
open Module Real InnerProductGeometry
open Real

set_option autoImplicit false

namespace Submission.Bridge.Projective

open Submission.Bridge.Core

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Distance from a line `X` to a subspace `s`: the minimum over lines `Z ≤ s` of the sine of
the angle between the two lines (mirror of `LinearSubspaces.distLineSubspace`). -/
def lineToSubspace (X : ℙ ℝ E) (s : Submodule ℝ E) : ℝ :=
  ⨅ Z : {Z : ℙ ℝ E // Z.submodule ≤ s}, sin (angle X.rep Z.1.rep)

/-- The lower-bound side of the line identity: every line `Z ≤ s` gives a value at least
`‖u - π_s u‖`. -/
lemma residual_le_sin_angle_line {s : Submodule ℝ E} (u : E) (hu : ‖u‖ = 1)
    (Z : {Z : ℙ ℝ E // Z.submodule ≤ s}) :
    ‖u - s.starProjection u‖ ≤ sin (angle u Z.1.rep) := by
  let z : E := (‖Z.1.rep‖)⁻¹ • Z.1.rep
  have hz0 : Z.1.rep ≠ 0 := Z.1.rep_nonzero
  have hz0' : (‖Z.1.rep‖) ≠ 0 := norm_ne_zero_iff.mpr hz0
  have hzs : z ∈ s := by
    unfold z
    exact s.smul_mem (‖Z.1.rep‖)⁻¹ (Z.2 (rep_mem_self Z.1))
  have hz1 : ‖z‖ = 1 := by
    unfold z
    rw [norm_smul]
    rw [Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg Z.1.rep))]
    rw [inv_mul_cancel₀ hz0']
  have hm : Z.1.rep = ‖Z.1.rep‖ • z := by
    unfold z
    rw [smul_smul]
    rw [mul_inv_cancel₀ hz0']
    simp
  calc
    ‖u - s.starProjection u‖ ≤ sin (angle u z) := residual_le_sin_angle (s := s) u z hu hz1 hzs
    _ = sin (angle u (‖Z.1.rep‖ • z)) := (sin_angle_smul_right (‖Z.1.rep‖) hz0' u z).symm
    _ = sin (angle u Z.1.rep) := by rw [← hm]

/-- The distance from a line `X` to `s` only depends on the sine of the angle between `X.rep`
and the unit representative of `Z`, so it is unchanged if we replace `X` by any other
representative of the same line (here: any line spanned by the same vector). -/
lemma lineToSubspace_eq_of_eq_rep {X X' : ℙ ℝ E} {s : Submodule ℝ E}
    (h : ∃ a : ℝ, a ≠ 0 ∧ X'.rep = a • X.rep) :
    lineToSubspace X s = lineToSubspace X' s := by
  rcases h with ⟨a, ha0, hX'⟩
  unfold lineToSubspace
  apply congrArg (fun f : {Z : ℙ ℝ E // Z.submodule ≤ s} → ℝ =>
    ⨅ Z : {Z : ℙ ℝ E // Z.submodule ≤ s}, f Z)
  funext Z
  rw [hX']
  exact (sin_angle_smul_left a ha0 X.rep Z.1.rep).symm

/-- The upper-bound side of the line identity: some line of `s` (that of the projected
residual, or any line if `u ⊥ s`) achieves exactly `‖u - π_s u‖`. -/
lemma exists_line_sin_angle_eq_residual (s : Submodule ℝ E) (u : E) (hu : ‖u‖ = 1)
    (hs : s ≠ ⊥) :
    ∃ Z0 : {Z : ℙ ℝ E // Z.submodule ≤ s},
      sin (angle u Z0.1.rep) = ‖u - s.starProjection u‖ := by
  classical
  by_cases hπ : s.starProjection u = 0
  · obtain ⟨w0, hw0s, hw01⟩ := exists_unit_of_ne_bot s hs
    let Z0 : {Z : ℙ ℝ E // Z.submodule ≤ s} :=
      ⟨Projectivization.mk ℝ w0 (ne_zero_of_norm_eq_one hw01), by
        rw [Projectivization.submodule_mk]
        exact (Submodule.span_singleton_le_iff_mem w0 s).mpr hw0s⟩
    refine ⟨Z0, ?_⟩
    rcases mk_rep_smul w0 (ne_zero_of_norm_eq_one hw01) with ⟨a, ha0, hrep⟩
    have hsin : sin (angle u Z0.1.rep) = sin (angle u w0) := by
      rw [hrep]
      exact sin_angle_smul_right a ha0 u w0
    rw [hsin]
    have hu0 : inner ℝ u w0 = 0 := by
      have hzz := Submodule.starProjection_inner_eq_zero (K := s) u w0 hw0s
      simpa [hπ] using hzz
    have hsinval : sin (angle u w0) = 1 := by
      apply (sq_eq_sq₀ (sin_angle_nonneg u w0) (by norm_num)).1
      rw [sin_angle_eq_dist_unit u w0 hu hw01]
      rw [norm_sub_inner_smul_sq_unit u w0 hu hw01]
      rw [hu0]
      norm_num
    have hres : ‖u - s.starProjection u‖ = 1 := by
      simpa [hπ, hu]
    rw [hsinval, hres]
  · let w0 : E := (‖s.starProjection u‖)⁻¹ • s.starProjection u
    have hw0s : w0 ∈ s := by
      unfold w0
      exact s.smul_mem (‖s.starProjection u‖)⁻¹ (s.starProjection_apply_mem u)
    have hw01 : ‖w0‖ = 1 := by
      unfold w0
      rw [norm_smul]
      rw [Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg (s.starProjection u)))]
      rw [inv_mul_cancel₀ (norm_ne_zero_iff.mpr hπ)]
    let Z0 : {Z : ℙ ℝ E // Z.submodule ≤ s} :=
      ⟨Projectivization.mk ℝ w0 (ne_zero_of_norm_eq_one hw01), by
        rw [Projectivization.submodule_mk]
        exact (Submodule.span_singleton_le_iff_mem w0 s).mpr hw0s⟩
    refine ⟨Z0, ?_⟩
    rcases mk_rep_smul w0 (ne_zero_of_norm_eq_one hw01) with ⟨a, ha0, hrep⟩
    have hsin : sin (angle u Z0.1.rep) = sin (angle u w0) := by
      rw [hrep]
      exact sin_angle_smul_right a ha0 u w0
    rw [hsin]
    have hmain : inner ℝ u w0 = ‖s.starProjection u‖ := by
      unfold w0
      have hc : inner ℝ u (s.starProjection u) = ‖s.starProjection u‖ ^ 2 := by
        have hzz := Submodule.starProjection_inner_eq_zero (K := s) u (s.starProjection u)
          (s.starProjection_apply_mem u)
        have h0 : inner ℝ (s.starProjection u) (u - s.starProjection u) = 0 :=
          inner_eq_zero_symm.mp hzz
        have h2 : inner ℝ u (s.starProjection u) = inner ℝ (s.starProjection u) (s.starProjection u) := by
          rw [real_inner_comm]
          calc
            inner ℝ (s.starProjection u) u
                = inner ℝ (s.starProjection u) ((s.starProjection u) + (u - s.starProjection u)) := by congr 1; abel
            _ = inner ℝ (s.starProjection u) (s.starProjection u) + inner ℝ (s.starProjection u) (u - s.starProjection u) := by
                rw [inner_add_right]
            _ = inner ℝ (s.starProjection u) (s.starProjection u) := by rw [h0, add_zero]
        rw [h2, real_inner_self_eq_norm_sq]
      calc
        inner ℝ u ((‖s.starProjection u‖)⁻¹ • s.starProjection u)
            = (‖s.starProjection u‖)⁻¹ * inner ℝ u (s.starProjection u) := by rw [inner_smul_right]
        _ = (‖s.starProjection u‖)⁻¹ * (‖s.starProjection u‖ ^ 2) := by rw [hc]
        _ = ‖s.starProjection u‖ := by
            rw [sq]
            rw [← mul_assoc]
            rw [inv_mul_cancel₀ (norm_ne_zero_iff.mpr hπ)]
            rw [one_mul]
    have hww : inner ℝ u w0 • w0 = s.starProjection u := by
      unfold w0
      rw [hmain]
      rw [smul_smul]
      rw [mul_inv_cancel₀ (norm_ne_zero_iff.mpr hπ)]
      simp
    calc
      sin (angle u w0) = ‖u - inner ℝ u w0 • w0‖ := sin_angle_eq_dist_unit u w0 hu hw01
      _ = ‖u - s.starProjection u‖ := by rw [hww]

/-- The distance from the line spanned by a unit vector `u` to the subspace `s` is the norm of
the orthogonal residual: `lineToSubspace (mk u) s = ‖u - π_s u‖`. -/
lemma lineToSubspace_mk_unit (u : E) (hu1 : ‖u‖ = 1) (hu : u ≠ 0) (s : Submodule ℝ E)
    (hs : s ≠ ⊥) :
    lineToSubspace (Projectivization.mk ℝ u hu) s = ‖u - s.starProjection u‖ := by
  classical
  unfold lineToSubspace
  -- the function over lines Z evaluated at the representative of `mk u` equals the same
  -- function at the unit vector `u` itself (representatives differ by a nonzero scalar):
  have hfun : (fun Z : {Z : ℙ ℝ E // Z.submodule ≤ s} => sin (angle u Z.1.rep)) =
      (fun Z : {Z : ℙ ℝ E // Z.submodule ≤ s} =>
        sin (angle (Projectivization.mk ℝ u hu).rep Z.1.rep)) := by
    funext Z
    rcases mk_rep_smul u hu with ⟨a, ha0, hrep⟩
    rw [hrep]
    exact (sin_angle_smul_left a ha0 u Z.1.rep).symm
  apply le_antisymm
  · -- ≤: exhibit a line Z0 with the exact value
    rcases exists_line_sin_angle_eq_residual s u hu1 hs with ⟨Z0, hZ0⟩
    have hbdd2 : BddBelow (Set.range (fun Z : {Z : ℙ ℝ E // Z.submodule ≤ s} =>
        sin (angle u Z.1.rep))) := by
      refine ⟨0, ?_⟩
      rintro y ⟨Z, rfl⟩
      exact sin_angle_nonneg _ _
    have hle0 := ciInf_le (f := (fun Z : {Z : ℙ ℝ E // Z.submodule ≤ s} =>
        sin (angle u Z.1.rep))) hbdd2 Z0
    have hle1 : (⨅ Z : {Z : ℙ ℝ E // Z.submodule ≤ s}, sin (angle u Z.1.rep)) ≤
        ‖u - s.starProjection u‖ := by
      rwa [hZ0] at hle0
    rw [hfun] at hle1
    exact hle1
  · -- ≥: every line gives a value ≥ ‖u - π_s u‖
    have hge : ∀ Z : {Z : ℙ ℝ E // Z.submodule ≤ s},
        ‖u - s.starProjection u‖ ≤ sin (angle u Z.1.rep) := residual_le_sin_angle_line u hu1
    haveI : Nonempty {Z : ℙ ℝ E // Z.submodule ≤ s} := by
      rcases exists_unit_of_ne_bot s hs with ⟨w0, hw0s, hw01⟩
      exact ⟨⟨Projectivization.mk ℝ w0 (ne_zero_of_norm_eq_one hw01), by
        rw [Projectivization.submodule_mk]
        exact (Submodule.span_singleton_le_iff_mem w0 s).mpr hw0s⟩⟩
    have hle2 : ‖u - s.starProjection u‖ ≤
        (⨅ Z : {Z : ℙ ℝ E // Z.submodule ≤ s}, sin (angle u Z.1.rep)) := le_ciInf hge
    rw [hfun] at hle2
    exact hle2

/-- The distance from the line spanned by a unit vector `u` to the subspace `s` is the norm of
the orthogonal residual, expressed through the line of `u`. -/
lemma lineToSubspace_mk_unit' (u : E) (hu1 : ‖u‖ = 1) (s : Submodule ℝ E) (hs : s ≠ ⊥) :
    lineToSubspace (Projectivization.mk ℝ u (ne_zero_of_norm_eq_one hu1)) s =
      ‖u - s.starProjection u‖ :=
  lineToSubspace_mk_unit u hu1 (ne_zero_of_norm_eq_one hu1) s hs

end Submission.Bridge.Projective
