import Mathlib
import Submission.Work.Step2.Geometry
import Submission.Work.Step2.halfAbove_isEmbeddedSphere

/-!
# The lower half of Pardon's double bubble is an embedded sphere

This is the companion of `Work.Step2.halfAbove_isEmbeddedSphere`.  Instead of repeating the
"straightening" argument of that file, we obtain the lower half from the upper one by the reflection
of `ℝ³` in the coordinate plane `{y (σ 2) = c (σ 2)}`.

Writing `y' = coordReflect c σ y` for the reflected point,

* `y' (σ i) = y (σ i)` for `i ≠ 2` and `y' (σ 2) = 2 * c (σ 2) - y (σ 2)`
  (`coordReflect_apply_of_ne`, `coordReflect_apply_self`);
* hence every coordinate distance `|y' (σ i) - c (σ i)|` equals `|y (σ i) - c (σ i)|`
  (`abs_sub_coordReflect`), so the box norm and the whole box `PBox s c σ` are preserved
  (`boxNorm_coordReflect`, `mem_PBox_coordReflect`);
* the reflection is an involution (`coordReflect_involutive`), hence injective and continuous;
* it exchanges the half-space `{y (σ 2) ≤ c (σ 2) + u}` with `{y (σ 2) ≥ c (σ 2) - u}` and the
  cutting plane `{y (σ 2) = c (σ 2) + u}` with `{y (σ 2) = c (σ 2) - u}`, so that

  `coordReflect c σ z ∈ halfAbove s c σ (-u) ↔ z ∈ halfBelow s c σ u`
  (`coordReflect_mem_halfAbove_neg`) and
  `coordReflect c σ '' halfAbove s c σ (-u) = halfBelow s c σ u`
  (`coordReflect_image_halfAbove`).

Carrying the embedding of `halfAbove s c σ (-u)` (which `halfAbove_isEmbeddedSphere` provides
under `|-u| < boxSide 2 * s`, i.e. under `|u| < boxSide 2 * s`) through the reflection therefore
exhibits `halfBelow s c σ u` as an embedded sphere.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Step2

noncomputable section

/-! ## The reflection in the coordinate plane `{y (σ 2) = c (σ 2)}` -/

/-- The reflection of `ℝ³` in the coordinate plane `{y (σ 2) = c (σ 2)}`: it changes the `σ 2`
coordinate `y (σ 2)` into `2 * c (σ 2) - y (σ 2)` and fixes the other two coordinates. -/
def coordReflect (c : R3) (σ : Equiv.Perm (Fin 3)) (y : R3) : R3 :=
  y + (2 * (c (σ 2) - y (σ 2))) • (PiLp.single 2 (σ 2) (1 : ℝ) : R3)

/-- Two points of `ℝ³` agree as soon as they agree in the three coordinates `σ i`. -/
private theorem eq_of_coord_eq {a b : R3} {σ : Equiv.Perm (Fin 3)}
    (h : ∀ i : Fin 3, a (σ i) = b (σ i)) : a = b := by
  ext j
  obtain ⟨i, rfl⟩ := σ.surjective j
  exact h i

theorem coordReflect_apply_self (c : R3) (σ : Equiv.Perm (Fin 3)) (y : R3) :
    coordReflect c σ y (σ 2) = 2 * c (σ 2) - y (σ 2) := by
  simp only [coordReflect, PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, smul_eq_mul,
    ↓reduceIte, mul_one]
  ring

theorem coordReflect_apply_of_ne (c : R3) (σ : Equiv.Perm (Fin 3)) (y : R3) {i : Fin 3}
    (hi : i ≠ 2) : coordReflect c σ y (σ i) = y (σ i) := by
  simp only [coordReflect, PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, smul_eq_mul,
    Equiv.apply_eq_iff_eq, hi, ↓reduceIte, mul_zero, add_zero]

/-- The reflection is an involution. -/
theorem coordReflect_involutive (c : R3) (σ : Equiv.Perm (Fin 3)) (y : R3) :
    coordReflect c σ (coordReflect c σ y) = y := by
  apply eq_of_coord_eq (σ := σ)
  intro i
  by_cases hi : i = 2
  · subst hi
    rw [coordReflect_apply_self, coordReflect_apply_self]
    ring
  · rw [coordReflect_apply_of_ne c σ _ hi, coordReflect_apply_of_ne c σ y hi]

/-- The reflection is injective. -/
theorem coordReflect_injective (c : R3) (σ : Equiv.Perm (Fin 3)) :
    Function.Injective (coordReflect c σ) :=
  Function.LeftInverse.injective (g := coordReflect c σ) (fun y => coordReflect_involutive c σ y)

/-- The reflection is continuous. -/
theorem continuous_coordReflect (c : R3) (σ : Equiv.Perm (Fin 3)) :
    Continuous (coordReflect c σ) := by
  have hcoord : Continuous fun y : R3 => y (σ 2) :=
    PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (σ 2)
  rw [show coordReflect c σ = fun y : R3 =>
      y + (2 * (c (σ 2) - y (σ 2))) • (PiLp.single 2 (σ 2) (1 : ℝ) : R3) from rfl]
  exact continuous_id.add
    ((continuous_const.sub hcoord).const_mul 2 |>.smul continuous_const)

/-! ## The reflection preserves the box -/

/-- The coordinate distances to the centre `c` are preserved by the reflection. -/
theorem abs_sub_coordReflect (c : R3) (σ : Equiv.Perm (Fin 3)) (y : R3) (i : Fin 3) :
    |coordReflect c σ y (σ i) - c (σ i)| = |y (σ i) - c (σ i)| := by
  by_cases hi : i = 2
  · subst hi
    rw [coordReflect_apply_self,
      show 2 * c (σ 2) - y (σ 2) - c (σ 2) = -(y (σ 2) - c (σ 2)) by ring, abs_neg]
  · rw [coordReflect_apply_of_ne c σ y hi]

/-- The reflection preserves the box norm. -/
theorem boxNorm_coordReflect (c : R3) (σ : Equiv.Perm (Fin 3)) (y : R3) :
    Submission.boxNorm c σ (coordReflect c σ y) = Submission.boxNorm c σ y := by
  simp only [Submission.boxNorm, abs_sub_coordReflect]

/-- The reflection preserves Pardon's box. -/
theorem mem_PBox_coordReflect (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (y : R3) :
    coordReflect c σ y ∈ Submission.PBox s c σ ↔ y ∈ Submission.PBox s c σ := by
  rw [Submission.mem_PBox_iff, Submission.mem_PBox_iff, boxNorm_coordReflect]

/-! ## The reflection exchanges the two halves of the double bubble -/

/-- **The reflection turns membership in the lower half of the double bubble into membership in the
upper half with the opposite shift.**  Indeed it preserves the box norm (the sphere part) and the
box, and it reverses the `σ 2`-inequality `z (σ 2) ≤ c (σ 2) + u` into
`c (σ 2) - u ≤ (coordReflect c σ z) (σ 2)` while moving the cutting plane
`{y (σ 2) = c (σ 2) + u}` to `{y (σ 2) = c (σ 2) - u}`. -/
theorem coordReflect_mem_halfAbove_neg {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    {z : R3} :
    coordReflect c σ z ∈ halfAbove s c σ (-u) ↔ z ∈ halfBelow s c σ u := by
  rw [mem_halfAbove, mem_halfBelow, boxNorm_coordReflect, mem_PBox_coordReflect,
    coordReflect_apply_self]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨h1, by linarith⟩
    · exact Or.inr ⟨h1, by linarith⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨h1, by linarith⟩
    · exact Or.inr ⟨h1, by linarith⟩

/-- **The reflection carries the upper half of the double bubble (with shift `-u`) onto the lower
half (with shift `u`).** -/
theorem coordReflect_image_halfAbove (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    coordReflect c σ '' halfAbove s c σ (-u) = halfBelow s c σ u := by
  apply Set.Subset.antisymm
  · rintro z ⟨y, hy, rfl⟩
    exact (coordReflect_mem_halfAbove_neg (z := coordReflect c σ y)).mp
      (by rwa [coordReflect_involutive])
  · intro z hz
    exact ⟨coordReflect c σ z, (coordReflect_mem_halfAbove_neg (z := z)).mpr hz,
      coordReflect_involutive c σ z⟩

/-! ## The lower half of the double bubble is an embedded sphere -/

theorem halfBelow_isEmbeddedSphere {s : ℝ} (hs : 0 < s) (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3)) {u : ℝ}
    (hu : |u| < Submission.boxSide 2 * s) :
    Work.InnermostDisk.IsEmbeddedSphere (Work.Step2.halfBelow s c σ u) := by
  have hneg : |-u| < Submission.boxSide 2 * s := by rwa [abs_neg]
  obtain ⟨e, hinj, hrange⟩ := halfAbove_isEmbeddedSphere hs c σ hneg
  refine ⟨⟨fun w => coordReflect c σ (e w),
    (continuous_coordReflect c σ).comp e.continuous⟩, ?_, ?_⟩
  · intro w w' h
    exact hinj (coordReflect_injective c σ h)
  · show Set.range (fun w => coordReflect c σ (e w)) = halfBelow s c σ u
    rw [show Set.range (fun w => coordReflect c σ (e w))
        = coordReflect c σ '' Set.range e from
      Set.range_comp (g := coordReflect c σ) (f := e)]
    rw [hrange, coordReflect_image_halfAbove]

end

end Work.Step2
