import Mathlib
import Submission.Work.HP.BCSDefs

/-!
# `toEZ`: integer vectors as Euclidean vectors (ℤ-valued input)

Moved out of `BCSDefs` (2026-09-28) because `Work.HP.MMDefs` defines a different
`Work.HP.toEZ` (ℝ-valued input); keeping both in `BCSDefs` made every module that imports
`BCSDefs` and `MMDefs` fail with "environment already contains Work.HP.toEZ". Import this
file only where the ℤ-valued `toEZ` is needed (`BCS.span_toE`, `BCS.lift_bound`,
`MDEstimates.exists_lift_norm`, `Q44Child.latZeroGeom`); do not co-import it with `MMDefs`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Finset
open scoped BigOperators

namespace Work.HP

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Integer vectors as Euclidean vectors -/

/-- The integer vector `v` as an element of Euclidean space. -/
def toEZ (v : ι → ℤ) : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun i => (v i : ℝ))

@[simp] lemma toEZ_apply (v : ι → ℤ) (i : ι) : (toEZ v).ofLp i = (v i : ℝ) := rfl

lemma toEZ_injective : Function.Injective (toEZ : (ι → ℤ) → EuclideanSpace ℝ ι) := by
  intro v w h
  ext i
  have := congrArg (fun z : EuclideanSpace ℝ ι => z.ofLp i) h
  simpa using this

/-- `toEZ` as a `ℤ`-linear map. -/
def toEHom : (ι → ℤ) →ₗ[ℤ] EuclideanSpace ℝ ι where
  toFun := toEZ
  map_add' v w := by ext i; simp [toEZ]
  map_smul' n v := by ext i; simp [toEZ]

@[simp] lemma toEHom_apply (v : ι → ℤ) : toEHom v = toEZ v := rfl

/-- The Euclidean norm of `toEZ v` is `eNorm v`. -/
lemma norm_toEZ (v : ι → ℤ) : ‖toEZ v‖ = eNorm v := by
  rw [eNorm, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [toEZ_apply, Real.norm_eq_abs, sq_abs]

end Work.HP
