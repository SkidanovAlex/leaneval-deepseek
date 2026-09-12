import Submission.Model
import Mathlib

/-!
# Algebraic facts about the model geodesic field

Task: prove the final theorem `accel_smul`.

`accel` is quadratic in the velocity argument: `accel gx T (λ • v) = λ ^ 2 • accel gx T v`.
(Geodesic equations are homogeneous in the velocity, which makes time-rescaling of geodesics
possible: if `(c, vel)` solves with initial velocity `v`, then `t ↦ c (λ t)` with velocity
`λ • vel (λ t)` solves with initial velocity `λ • v`.)

Recall from `Submission/Model.lean` (definitions with exactly these names and types):

    abbrev Bilin E := E →L[ℝ] (E →L[ℝ] ℝ)
    evalAtV (v : E) : Bilin E →L[ℝ] ℝ      -- B ↦ (B v) v
    rhsCovector (T : E →L[ℝ] Bilin E) (v : E) : E →L[ℝ] ℝ
          --  w ↦ ½ ((T w) v) v − ((T v) v) w   (exactly: (1/2) • (evalAtV v).comp T − (T v) v)
    accel (gx : Bilin E) (T : E →L[ℝ] Bilin E) (v : E) : E
          --  (ContinuousLinearMap.inverse gx) (rhsCovector T v)

## Proof sketch

1. `rhsCovector T (λ • v) = (λ ^ 2) • rhsCovector T v` (equality of covectors), because
   `(T w) (λv) (λv) = λ^2 (T w) v v` (bilinearity of the bilinear form `T w` in both arguments)
   and `(T (λv)) (λv) w = λ (T v) (λ v) w = λ^2 (T v) v w`.  Do this by `funext w` and unfold
   `rhsCovector`; `simp` with bilinearity lemmas like `map_smul`, `map_smulₛₗ`,
   `ContinuousLinearMap.smul_apply`, and ring for the scalars.
2. `accel gx T (λ•v) = (ContinuousLinearMap.inverse gx) ((λ^2) • rhsCovector T v)`
   = `(λ^2) • accel gx T v` (linearity of `inverse gx`).

You may add helper lemmas.  Do NOT change the statement of `accel_smul`.
-/

open ContinuousLinearMap
open scoped ContDiff
open Set

namespace Submission.Model

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable section

/-- Bilinearity of a bilinear form in both arguments: `(B (s • v)) (s • v) = s ^ 2 * (B v) v`. -/
lemma bilin_smul_smul (B : Bilin E) (v : E) (s : ℝ) :
    (B (s • v)) (s • v) = s ^ 2 * ((B v) v) := by
  simp [map_smul, smul_apply, pow_two]
  ring

/-- The value `((T (s • v)) (s • v)) w` scales quadratically in `s`, by linearity of `T`
and bilinearity of the bilinear form `T v`. -/
lemma derivBilin_smul_smul (T : E →L[ℝ] Bilin E) (v w : E) (s : ℝ) :
    ((T (s • v)) (s • v)) w = s ^ 2 * (((T v) v) w) := by
  simp [map_smul, smul_apply, pow_two]
  ring

/-- Pointwise formula for `rhsCovector`: `(rhsCovector T u) w = ½ ((T w) u) u − ((T u) u) w`. -/
lemma rhsCovector_apply (T : E →L[ℝ] Bilin E) (u w : E) :
    (rhsCovector T u) w = (1 / 2 : ℝ) * (((T w) u) u) - (((T u) u) w) := by
  simp [rhsCovector, evalAtV]

/-- `rhsCovector` is quadratic in the velocity argument. -/
lemma rhsCovector_smul (T : E →L[ℝ] Bilin E) (v : E) (s : ℝ) :
    rhsCovector T (s • v) = (s ^ 2) • rhsCovector T v := by
  ext w
  calc
    (rhsCovector T (s • v)) w
        = (1 / 2 : ℝ) * (((T w) (s • v)) (s • v)) - (((T (s • v)) (s • v)) w) := by
            rw [rhsCovector_apply]
    _ = (s ^ 2) * ((1 / 2 : ℝ) * (((T w) v) v) - (((T v) v) w)) := by
            rw [bilin_smul_smul (T w) v s, derivBilin_smul_smul T v w s]
            ring
    _ = ((s ^ 2) • rhsCovector T v) w := by
            rw [smul_apply, rhsCovector_apply, smul_eq_mul]

/-- `accel` is quadratic in the velocity. -/
theorem accel_smul (gx : Bilin E) (T : E →L[ℝ] Bilin E) (v : E) (s : ℝ) :
    accel gx T (s • v) = (s ^ 2) • accel gx T v := by
  unfold accel
  rw [rhsCovector_smul]
  rw [map_smul]

end

end Submission.Model
