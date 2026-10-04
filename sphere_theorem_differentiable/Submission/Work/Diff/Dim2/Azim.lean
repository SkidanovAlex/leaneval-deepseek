import Submission.Work.Diff.Dim2.Lib
import Submission.Work.Diff.Dim2.Ambient

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Conversions between `ℂ` and `ℝ² = EuclideanSpace ℝ (Fin 2)`, and the rotation

Auxiliary definitions for the azimuth (`Plan3.lean` §7): the canonical identifications
`ofC : ℂ → ℝ²`, `toC : ℝ² → ℂ`, the argument `argE`, and the rotation `rotE t z` (multiplication by
`exp (i t)`), together with the elementary lemmas about them that the azimuth statements use.
-/

set_option autoImplicit false

namespace Work.Diff.Dim2

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set Filter

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The canonical identification `ℂ ≃ ℝ²`. -/
def ofC (z : ℂ) : EuclideanSpace ℝ (Fin 2) :=
  (EuclideanSpace.equiv (Fin 2) (𝕜 := ℝ)).symm ![z.re, z.im]

/-- The canonical identification `ℝ² ≃ ℂ`. -/
def toC (v : EuclideanSpace ℝ (Fin 2)) : ℂ := ⟨v 0, v 1⟩

/-- The argument of a point of `ℝ²` (junk at `0`). -/
def argE (v : EuclideanSpace ℝ (Fin 2)) : ℝ := Complex.arg (toC v)

/-- Rotation by the angle `t` in `ℝ²` (multiplication by `exp (i t)`). -/
def rotE (t : ℝ) (z : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  ofC (Complex.exp (t * Complex.I) * toC z)

lemma re_ofC (z : ℂ) : ofC z 0 = z.re := by simp [ofC, EuclideanSpace.equiv]
lemma im_ofC (z : ℂ) : ofC z 1 = z.im := by simp [ofC, EuclideanSpace.equiv]

@[simp] lemma toC_ofC (z : ℂ) : toC (ofC z) = z := by
  apply Complex.ext
  · simpa [toC] using re_ofC z
  · simpa [toC] using im_ofC z

@[simp] lemma ofC_toC (v : EuclideanSpace ℝ (Fin 2)) : ofC (toC v) = v := by
  ext i
  fin_cases i <;> simp [toC, ofC, EuclideanSpace.equiv]

@[simp] lemma ofC_zero : ofC 0 = 0 := by
  ext i; fin_cases i <;> simp [ofC, EuclideanSpace.equiv]

lemma toC_circPt (t : ℝ) : toC (circPt t) = (Real.cos t : ℂ) + (Real.sin t : ℂ) * Complex.I := by
  apply Complex.ext
  · simp [toC, circPt, EuclideanSpace.equiv, Complex.cos_ofReal_re]
  · simp [toC, circPt, EuclideanSpace.equiv, Complex.sin_ofReal_re]

lemma ofC_exp_I (t : ℝ) :
    ofC (Complex.exp ((t : ℂ) * Complex.I)) = circPt t := by
  have h : toC (circPt t) = Complex.exp ((t : ℂ) * Complex.I) := by
    rw [toC_circPt, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [← h, ofC_toC]

lemma norm_toC (v : EuclideanSpace ℝ (Fin 2)) : ‖toC v‖ = ‖v‖ := by
  have h1 : ‖toC v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    have hv : toC v = ⟨v 0, v 1⟩ := rfl
    rw [hv, Complex.normSq_mk, ← real_inner_self_eq_norm_sq v, inner_fin_two]
  nlinarith [norm_nonneg (toC v), norm_nonneg v]

lemma norm_ofC (z : ℂ) : ‖ofC z‖ = ‖z‖ := by
  rw [← norm_toC (ofC z), toC_ofC]

lemma norm_rotE (t : ℝ) (z : EuclideanSpace ℝ (Fin 2)) : ‖rotE t z‖ = ‖z‖ := by
  show ‖ofC (Complex.exp ((t : ℂ) * Complex.I) * toC z)‖ = ‖z‖
  rw [norm_ofC, norm_mul, norm_toC, Complex.norm_exp]
  have h : ((t : ℂ) * Complex.I).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [h, Real.exp_zero, one_mul]

lemma rotE_zero (z : EuclideanSpace ℝ (Fin 2)) : rotE 0 z = z := by
  rw [rotE, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul, ofC_toC]

lemma rotE_add (s t : ℝ) (z : EuclideanSpace ℝ (Fin 2)) :
    rotE s (rotE t z) = rotE (s + t) z := by
  rw [rotE, rotE, rotE, toC_ofC, ← mul_assoc, ← Complex.exp_add]
  have h : (s : ℂ) * Complex.I + (t : ℂ) * Complex.I = ((s + t : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h]

/-- Reflection of the second coordinate (an isometry of `ℝ²` when `|s| = 1`). -/
def reflE (s : ℝ) (z : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  ofC ⟨(toC z).re, s * (toC z).im⟩

lemma reflE_one (z : EuclideanSpace ℝ (Fin 2)) : reflE 1 z = z := by
  rw [reflE, one_mul, ofC_toC]

lemma reflE_apply_zero (s : ℝ) (z : EuclideanSpace ℝ (Fin 2)) : reflE s z 0 = z 0 := by
  rw [reflE, re_ofC]
  rfl

lemma reflE_apply_one (s : ℝ) (z : EuclideanSpace ℝ (Fin 2)) : reflE s z 1 = s * z 1 := by
  rw [reflE, im_ofC]
  rfl

lemma norm_reflE {s : ℝ} (hs : s * s = 1) (z : EuclideanSpace ℝ (Fin 2)) :
    ‖reflE s z‖ = ‖z‖ := by
  have h1 : ‖reflE s z‖ ^ 2 = ‖z‖ ^ 2 := by
    rw [reflE, norm_ofC, ← norm_toC z, ← Complex.normSq_eq_norm_sq,
      ← Complex.normSq_eq_norm_sq]
    rw [Complex.normSq_mk, Complex.normSq_mk]
    nlinarith [sq_nonneg (toC z).im]
  nlinarith [norm_nonneg (reflE s z), norm_nonneg z]

end

end Work.Diff.Dim2
