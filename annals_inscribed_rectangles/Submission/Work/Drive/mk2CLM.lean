import Mathlib
import Submission.Work.Drive.cone_chain

/-!
# The coordinate projections of `ℝ³` as continuous linear maps

`Work.Drive.mk2 (u 0) (u 1)` is the `(u 0, u 1)`-coordinate of `u : ℝ³`, and `u 2` is the third
coordinate.  This file packages the two as continuous linear maps

* `Work.Drive.mk2CLM : ℝ³ →L ℝ²`,   `mk2CLM u = mk2 (u 0) (u 1)`;
* `Work.Drive.coordCLM2 : ℝ³ →L ℝ`,  `coordCLM2 u = u 2`.

They are the `π` and `τ` of the block form `Work.Drive.tripleTransverseE_of_blocks`: the derivative of
a radial sweep has the shape `(b ∘ π + a • τ, c ∘ π)`, with `π` the plane's parameter and `τ` the
radial (sweep) parameter.
-/

namespace Work.Drive

open scoped Manifold ContDiff

noncomputable section

/-- The map `u ↦ mk2 (u 0) (u 1)` as a **linear** map. -/
def mk2Lin : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toFun u := mk2 (u 0) (u 1)
  map_add' a b := by ext i; fin_cases i <;> simp [mk2]
  map_smul' c a := by ext i; fin_cases i <;> simp [mk2]

/-- **The `(u 0, u 1)`-coordinate projection `ℝ³ → ℝ²`**, as a continuous linear map. -/
def mk2CLM : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  mk2Lin.toContinuousLinearMap

/-- **The third-coordinate functional `ℝ³ → ℝ`**, as a continuous linear map. -/
def coordCLM2 : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ :=
  ({
    toFun := fun u => u 2
    map_add' := fun a b => by simp
    map_smul' := fun c a => by simp } :
    EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ).toContinuousLinearMap

@[simp] lemma mk2CLM_apply (u : EuclideanSpace ℝ (Fin 3)) :
    mk2CLM u = mk2 (u 0) (u 1) := rfl

@[simp] lemma coordCLM2_apply (u : EuclideanSpace ℝ (Fin 3)) :
    coordCLM2 u = u 2 := rfl

/-- The two coordinate maps separate points: a vector all of whose coordinates are hit by the two
projections is determined. -/
lemma coord_eq_of (u v : EuclideanSpace ℝ (Fin 3))
    (h1 : mk2CLM u = mk2CLM v) (h2 : coordCLM2 u = coordCLM2 v) : u = v := by
  ext i
  fin_cases i
  · have := congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w 0) h1
    simpa using this
  · have := congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w 1) h1
    simpa using this
  · simpa using h2

end

end Work.Drive
