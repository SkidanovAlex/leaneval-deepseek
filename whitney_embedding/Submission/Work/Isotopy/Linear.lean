import Mathlib
import Submission.Work.Isotopy.Basic

/-!
# Explicit ambient isotopies of a normed space

The two basic "we may assume without loss of generality" moves for embeddings into `ℝ^N`:

* `Work.Isotopy.AmbientIsotopy.translation v` is the ambient isotopy `x ↦ x + t • v`
  (translation by a vector, interpolated linearly in time);
* `Work.Isotopy.AmbientIsotopy.dilation ε hε` is the ambient isotopy interpolating between the
  identity at time `0` and the dilation `x ↦ ε • x` by a *positive* factor at time `1`
  (a convex combination of `1` and `ε` is used as the scale factor, so that every time slice is an
  invertible map).

Consequently the image of an embedding can be moved into any prescribed ball and into any
prescribed position, which is the first step of the gluing argument for the non-compact case.
-/

open Topology Set Function

namespace Work.Isotopy

namespace AmbientIsotopy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Translation by `t • v` at time `t`. -/
noncomputable def translation (v : E) : AmbientIsotopy E where
  toHomeomorph :=
    { toFun := fun p => (p.1 + p.2 • v, p.2)
      invFun := fun p => (p.1 - p.2 • v, p.2)
      left_inv := by
        rintro ⟨x, t⟩
        simp
      right_inv := by
        rintro ⟨y, t⟩
        simp
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  map_snd := fun p => rfl
  map_zero_fst := fun x => by simp

@[simp]
theorem translation_apply (v : E) (t : ℝ) (x : E) :
    (translation v).apply t x = x + t • v := rfl

theorem translation_apply_one (v : E) (x : E) : (translation v).apply 1 x = x + v := by
  rw [translation_apply, one_smul]

@[simp]
theorem translation_apply_zero (v : E) (x : E) : (translation v).apply 0 x = x := by
  rw [translation_apply, zero_smul, add_zero]

/-- The scale factor of the dilation isotopy: a convex combination of `1` (at `t ≤ 0`) and `ε`
(for `t ≥ 1`). -/
noncomputable def dilationScale (ε : ℝ) (t : ℝ) : ℝ :=
  1 + Real.smoothTransition t * (ε - 1)

theorem continuous_dilationScale (ε : ℝ) : Continuous (dilationScale ε) := by
  unfold dilationScale
  exact continuous_const.add (Real.smoothTransition.continuous.mul continuous_const)

theorem dilationScale_pos {ε : ℝ} (hε : 0 < ε) (t : ℝ) : 0 < dilationScale ε t := by
  have hs0 : 0 ≤ Real.smoothTransition t := Real.smoothTransition.nonneg t
  have hs1 : Real.smoothTransition t ≤ 1 := Real.smoothTransition.le_one t
  have hcomp : dilationScale ε t =
      (1 - Real.smoothTransition t) * 1 + Real.smoothTransition t * ε := by
    simp only [dilationScale]; ring
  have hmin : min 1 ε ≤ dilationScale ε t := by
    rw [hcomp]
    have hA : 0 ≤ 1 - Real.smoothTransition t := by linarith
    nlinarith [min_le_left (1 : ℝ) ε, min_le_right (1 : ℝ) ε, mul_nonneg hA (zero_le_one),
      mul_nonneg hs0 (le_of_lt hε), hs0, hs1]
  exact lt_of_lt_of_le (lt_min one_pos hε) hmin

@[simp]
theorem dilationScale_zero (ε : ℝ) : dilationScale ε 0 = 1 := by
  simp [dilationScale, Real.smoothTransition.zero]

@[simp]
theorem dilationScale_one (ε : ℝ) : dilationScale ε 1 = ε := by
  simp [dilationScale, Real.smoothTransition.one]

/-- The dilation isotopy by a positive factor `ε`: identity at time `0`, `x ↦ ε • x` at time `1`. -/
noncomputable def dilation (ε : ℝ) (hε : 0 < ε) : AmbientIsotopy E where
  toHomeomorph :=
    { toFun := fun p => (dilationScale ε p.2 • p.1, p.2)
      invFun := fun p => ((dilationScale ε p.2)⁻¹ • p.1, p.2)
      left_inv := by
        rintro ⟨x, t⟩
        have h : dilationScale ε t ≠ 0 := ne_of_gt (dilationScale_pos hε t)
        refine Prod.ext ?_ rfl
        show (dilationScale ε t)⁻¹ • (dilationScale ε t • x) = x
        rw [smul_smul, inv_mul_cancel₀ h, one_smul]
      right_inv := by
        rintro ⟨y, t⟩
        have h : dilationScale ε t ≠ 0 := ne_of_gt (dilationScale_pos hε t)
        refine Prod.ext ?_ rfl
        show dilationScale ε t • ((dilationScale ε t)⁻¹ • y) = y
        rw [smul_smul, mul_inv_cancel₀ h, one_smul]
      continuous_toFun := by
        refine Continuous.prodMk ?_ continuous_snd
        exact ((continuous_dilationScale ε).comp continuous_snd).smul continuous_fst
      continuous_invFun := by
        refine Continuous.prodMk ?_ continuous_snd
        have h1 : Continuous fun p : E × ℝ => (dilationScale ε p.2)⁻¹ :=
          ((continuous_dilationScale ε).comp continuous_snd).inv₀
            (fun p => ne_of_gt (dilationScale_pos hε p.2))
        exact h1.smul continuous_fst }
  map_snd := fun p => rfl
  map_zero_fst := fun x => by simp

theorem dilation_apply (ε : ℝ) (_hε : 0 < ε) (t : ℝ) (x : E) :
    (dilation ε _hε).apply t x = dilationScale ε t • x := rfl

@[simp]
theorem dilation_apply_zero (ε : ℝ) (hε : 0 < ε) (x : E) :
    (dilation ε hε).apply 0 x = x := by
  rw [dilation_apply, dilationScale_zero, one_smul]

theorem dilation_apply_one (ε : ℝ) (hε : 0 < ε) (x : E) :
    (dilation ε hε).apply 1 x = ε • x := by
  rw [dilation_apply, dilationScale_one]

end AmbientIsotopy

end Work.Isotopy
