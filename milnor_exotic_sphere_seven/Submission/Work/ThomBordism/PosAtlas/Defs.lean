import Mathlib
import Submission.Work.PTGeometric.HOFXfer
import Submission.Work.Orient.Boundary

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PosAtlas: the vocabulary for converting an orientation family into an oriented atlas

The target `Work.ThomBordism.positiveAtlas_of_orientationFamily` asks for a charted-space structure
on a compact `9`-dimensional manifold with boundary whose transition functions have positive
determinant at the interior points, given an orientation family `γ`.

The construction is the classical one: take the given charts and *flip* a chart by a reflection of
the model (an orientation-reversing diffeomorphism) whenever the chart is inconsistent with `γ`.
This file fixes the vocabulary:

* `E9` — the model space `ℝ⁹`;
* `reflLin`, `reflHomeo` — the reflection of `ℝ⁹` negating the coordinate `1`: it preserves the
  first coordinate (hence the half-space) and has determinant `< 0`; the coordinate `1` is
  *tangential*, so the reflection preserves `EuclideanHalfSpace 9` (unlike the coordinate `0`);
* `intHalf` — the interior of the half-space, as an open partial homeomorphism onto
  `{v : ℝ⁹ | 0 < v 0}`;
* `halfReflOph` — the reflection of the *half-space*, on its interior;
* `flip e` — the flip of a chart in the coordinate-function convention `e : W ⇀ 𝓡∂ 9`;
* `coerceChart e` — the `ℝ⁹`-chart associated with a half-space chart (for interior points, a
  half-space chart is an honest chart into `ℝ⁹`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

open Set Function

open scoped Manifold

namespace Work.ThomBordism.PosAtlas

noncomputable section

/-- The model space `ℝ⁹`. -/
abbrev E9 : Type := EuclideanSpace ℝ (Fin 9)

/-- The reflection of `Fin 9 → ℝ` negating the coordinate `1`. -/
def reflCoordFun (v : Fin 9 → ℝ) : Fin 9 → ℝ := Function.update v 1 (-(v 1))

theorem reflCoordFun_zero (v : Fin 9 → ℝ) : reflCoordFun v 0 = v 0 := by
  rw [reflCoordFun, Function.update_apply]
  simp

theorem reflCoordFun_one (v : Fin 9 → ℝ) : reflCoordFun v 1 = -(v 1) := by
  rw [reflCoordFun, Function.update_apply]
  simp

theorem reflCoordFun_apply_of_ne (v : Fin 9 → ℝ) {i : Fin 9} (hi : i ≠ 1) :
    reflCoordFun v i = v i := by
  rw [reflCoordFun, Function.update_apply]
  simp [hi]

theorem reflCoordFun_involutive (v : Fin 9 → ℝ) : reflCoordFun (reflCoordFun v) = v := by
  funext i
  by_cases hi : i = 1
  · subst hi; rw [reflCoordFun_one, reflCoordFun_one, neg_neg]
  · rw [reflCoordFun_apply_of_ne _ hi, reflCoordFun_apply_of_ne _ hi]

/-- The reflection of `Fin 9 → ℝ` negating the coordinate `1`, as a linear equivalence. -/
def reflCoord : (Fin 9 → ℝ) ≃ₗ[ℝ] (Fin 9 → ℝ) where
  toFun := reflCoordFun
  invFun := reflCoordFun
  map_add' v w := by
    funext i
    by_cases hi : i = 1
    · subst hi
      show reflCoordFun (v + w) 1 = reflCoordFun v 1 + reflCoordFun w 1
      rw [reflCoordFun_one, reflCoordFun_one, reflCoordFun_one]
      simp only [Pi.add_apply]
      ring
    · show reflCoordFun (v + w) i = reflCoordFun v i + reflCoordFun w i
      rw [reflCoordFun_apply_of_ne (v + w) hi, reflCoordFun_apply_of_ne v hi,
        reflCoordFun_apply_of_ne w hi, Pi.add_apply]
  map_smul' c v := by
    funext i
    by_cases hi : i = 1
    · subst hi
      show reflCoordFun (c • v) 1 = c • reflCoordFun v 1
      rw [reflCoordFun_one, reflCoordFun_one]
      simp only [Pi.smul_apply, smul_neg]
    · show reflCoordFun (c • v) i = c • reflCoordFun v i
      rw [reflCoordFun_apply_of_ne (c • v) hi, reflCoordFun_apply_of_ne v hi,
        Pi.smul_apply]
  left_inv := reflCoordFun_involutive
  right_inv := reflCoordFun_involutive

theorem reflCoord_apply (v : Fin 9 → ℝ) : reflCoord v = reflCoordFun v := rfl

/-- **The reflection of `ℝ⁹` negating the coordinate `1`**, as a linear equivalence. -/
def reflLin : E9 ≃ₗ[ℝ] E9 :=
  ((EuclideanSpace.equiv (Fin 9) ℝ).toLinearEquiv).trans
    (reflCoord.trans ((EuclideanSpace.equiv (Fin 9) ℝ).symm.toLinearEquiv))

/-- **The reflection of `ℝ⁹` negating the coordinate `1`**, as a homeomorphism. -/
def reflHomeo : E9 ≃ₜ E9 := reflLin.toContinuousLinearEquiv.toHomeomorph

theorem reflLin_apply (v : E9) :
    reflLin v =
      (EuclideanSpace.equiv (Fin 9) ℝ).symm (reflCoordFun ((EuclideanSpace.equiv (Fin 9) ℝ) v)) :=
  rfl

theorem reflLin_apply_zero (v : E9) : (reflLin v) 0 = v 0 := by
  rw [reflLin_apply]
  show reflCoordFun ((EuclideanSpace.equiv (Fin 9) ℝ) v) 0 = ((EuclideanSpace.equiv (Fin 9) ℝ) v) 0
  rw [reflCoordFun_zero]

theorem reflLin_apply_one (v : E9) : (reflLin v) 1 = -(v 1) := by
  rw [reflLin_apply]
  show reflCoordFun ((EuclideanSpace.equiv (Fin 9) ℝ) v) 1
    = -(((EuclideanSpace.equiv (Fin 9) ℝ) v) 1)
  rw [reflCoordFun_one]

theorem reflLin_coord_of_ne (v : E9) {i : Fin 9} (hi : i ≠ 1) : (reflLin v) i = v i := by
  rw [reflLin_apply]
  show reflCoordFun ((EuclideanSpace.equiv (Fin 9) ℝ) v) i = ((EuclideanSpace.equiv (Fin 9) ℝ) v) i
  rw [reflCoordFun_apply_of_ne _ hi]

theorem reflLin_zero : reflLin (0 : E9) = 0 := by
  rw [reflLin_apply]
  have h : reflCoordFun ((EuclideanSpace.equiv (Fin 9) ℝ) (0 : E9)) = 0 := by
    rw [map_zero]
    funext i
    simp [reflCoordFun, Function.update_apply]
  rw [h, map_zero]

theorem reflLin_involutive (v : E9) : reflLin (reflLin v) = v := by
  rw [reflLin_apply]
  have h : (EuclideanSpace.equiv (Fin 9) ℝ) (reflLin v)
      = reflCoordFun ((EuclideanSpace.equiv (Fin 9) ℝ) v) := by
    rw [reflLin_apply, ContinuousLinearEquiv.apply_symm_apply]
  rw [h, reflCoordFun_involutive, ContinuousLinearEquiv.symm_apply_apply]

theorem reflLin_injective : Function.Injective reflLin :=
  Function.LeftInverse.injective reflLin_involutive

theorem reflLin_bijective : Function.Bijective reflLin :=
  ⟨reflLin_injective, fun y => ⟨reflLin y, reflLin_involutive y⟩⟩

/-- **The reflection of `ℝ⁹` negating the coordinate `1`**, as a continuous linear map. -/
def reflCLM : E9 →L[ℝ] E9 :=
  (reflLin : E9 ≃ₗ[ℝ] E9).toLinearMap.toContinuousLinearMap

theorem reflCLM_apply (v : E9) : reflCLM v = reflLin v := rfl

/-- **The reflection of `ℝ⁹` negating the coordinate `1`**, as a continuous map. -/
def reflCM : C(E9, E9) := ⟨reflLin, reflCLM.continuous⟩

theorem reflCM_apply (v : E9) : reflCM v = reflLin v := rfl

theorem reflCM_involutive (v : E9) : reflCM (reflCM v) = v := by
  rw [reflCM_apply, reflCM_apply, reflLin_involutive]

/-- The interior of the half-space `𝓡∂ 9`, as an open partial homeomorphism onto the open subset
`{v : ℝ⁹ | 0 < v 0}` of `ℝ⁹`. -/
def intHalf : OpenPartialHomeomorph (EuclideanHalfSpace 9) E9 where
  toFun := Subtype.val
  invFun := fun v => (𝓡∂ 9).symm v
  source := {y : EuclideanHalfSpace 9 | 0 < y.1 0}
  target := {v : E9 | 0 < v 0}
  map_source' := fun y hy => hy
  map_target' := fun v hv => by
    rw [modelWithCornersEuclideanHalfSpace_symm_apply_of_le (le_of_lt hv)]
    exact hv
  left_inv' := fun y hy => by
    show (𝓡∂ 9).symm (Subtype.val y) = y
    rw [modelWithCornersEuclideanHalfSpace_symm_apply_of_le (le_of_lt hy)]
    exact Subtype.ext rfl
  right_inv' := fun v hv => by
    show Subtype.val ((𝓡∂ 9).symm v) = v
    rw [modelWithCornersEuclideanHalfSpace_symm_apply_of_le (le_of_lt hv)]
  continuousOn_toFun := continuous_subtype_val.continuousOn
  continuousOn_invFun := (modelWithCornersEuclideanHalfSpace 9).continuous_invFun.continuousOn
  open_source := isOpen_lt continuous_const (by fun_prop)
  open_target := isOpen_lt continuous_const (by fun_prop)

/-- The reflection of the half-space, on the interior of the half-space: the conjugate of the
reflection of `ℝ⁹` by the interior chart `intHalf`. -/
def halfReflOph : OpenPartialHomeomorph (EuclideanHalfSpace 9) (EuclideanHalfSpace 9) :=
  (intHalf.transHomeomorph reflHomeo).trans intHalf.symm

/-- **The flip of a chart**, in the coordinate-function convention (`e : W ⇀ 𝓡∂ 9`): post-composition
with the reflection of the half-space. -/
def flip {W : TopCat} (e : OpenPartialHomeomorph W (EuclideanHalfSpace 9)) :
    OpenPartialHomeomorph W (EuclideanHalfSpace 9) :=
  e.trans halfReflOph

/-- **The `ℝ⁹`-chart associated with a half-space chart** (coordinate-function convention): its
composition with the interior chart of the half-space.  For a chart whose source is mapped into the
interior, this is an honest chart of `W` into `ℝ⁹`. -/
def coerceChart {W : TopCat} (e : OpenPartialHomeomorph W (EuclideanHalfSpace 9)) :
    OpenPartialHomeomorph W E9 :=
  e.trans intHalf

end

end Work.ThomBordism.PosAtlas
