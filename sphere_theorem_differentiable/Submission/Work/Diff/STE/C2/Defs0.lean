/-
# Layer C2 (DeTurck pull-back): raw definitions and elementary API

This file contains the *definitions* used by the pull-back step of the DeTurck argument
(`Work.Diff.STE.C2.ricci_of_deTurck`): the pull-back of a metric along a diffeomorphism `φ`,
the push-forward of a vector field, and the pull-back of a connection, together with the
elementary facts about `mfderiv φ` and `mfderiv φ.symm`.

They are deliberately kept free of any non-trivial proof obligation, so that the lemmas *about*
them can be stated (and delegated) before the constructions are packaged.

Notation: `SMet I M = ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)` is the
frozen notion of a smooth Riemannian metric of `Submission/Diff/Interfaces.lean`.
-/

import Mathlib
import Submission.Diff.ODE

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

namespace Work.Diff.STE.C2

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]

/-! ## The two identifications of `dφ` and `dφ⁻¹` -/

theorem mdifferentiableAt_of_diffeomorph (φ : M ≃ₘ⟮I, I⟯ M) (x : M) :
    MDifferentiableAt I I (φ : M → M) x :=
  φ.contMDiff_toFun.contMDiffAt.mdifferentiableAt (by simp)

theorem mdifferentiableAt_of_diffeomorph_symm (φ : M ≃ₘ⟮I, I⟯ M) (x : M) :
    MDifferentiableAt I I (φ.symm : M → M) x :=
  φ.symm.contMDiff_toFun.contMDiffAt.mdifferentiableAt (by simp)

/-- `d(φ⁻¹)_{φ x} (dφ_x v) = v`. -/
theorem mfderiv_symm_apply_mfderiv (φ : M ≃ₘ⟮I, I⟯ M) (x : M) (v : TangentSpace I x) :
    mfderiv I I (φ.symm : M → M) (φ x) (mfderiv I I (φ : M → M) x v) = v := by
  have h := mfderiv_comp_apply (I := I) (I' := I) (I'' := I) (x := x)
      (f := (φ : M → M)) (g := (φ.symm : M → M))
      (mdifferentiableAt_of_diffeomorph_symm φ (φ x))
      (mdifferentiableAt_of_diffeomorph φ x) v
  rw [show ((φ.symm : M → M) ∘ (φ : M → M)) = (id : M → M) from
    funext (Diffeomorph.symm_apply_apply φ), mfderiv_id] at h
  simpa using h.symm

/-- `d(φ⁻¹)_{φ x} ∘ dφ_x = id`. -/
theorem mfderiv_symm_comp_mfderiv (φ : M ≃ₘ⟮I, I⟯ M) (x : M) :
    (mfderiv I I (φ.symm : M → M) (φ x)) ∘L (mfderiv I I (φ : M → M) x)
      = ContinuousLinearMap.id ℝ (TangentSpace I x) := by
  ext u
  simp only [ContinuousLinearMap.comp_apply]
  exact mfderiv_symm_apply_mfderiv φ x u

/-- `dφ_{φ⁻¹ y} (d(φ⁻¹)_y v) = v`. -/
theorem mfderiv_apply_mfderiv_symm (φ : M ≃ₘ⟮I, I⟯ M) (y : M) (v : TangentSpace I y) :
    mfderiv I I (φ : M → M) (φ.symm y) (mfderiv I I (φ.symm : M → M) y v) = v := by
  have h := mfderiv_comp_apply (I := I) (I' := I) (I'' := I) (x := y)
      (f := (φ.symm : M → M)) (g := (φ : M → M))
      (mdifferentiableAt_of_diffeomorph φ (φ.symm y))
      (mdifferentiableAt_of_diffeomorph_symm φ y) v
  rw [show ((φ : M → M) ∘ (φ.symm : M → M)) = (id : M → M) from
    funext (Diffeomorph.apply_symm_apply φ), mfderiv_id] at h
  simpa using h.symm

/-- `dφ_{φ⁻¹ y} ∘ d(φ⁻¹)_y = id`. -/
theorem mfderiv_comp_mfderiv_symm (φ : M ≃ₘ⟮I, I⟯ M) (y : M) :
    (mfderiv I I (φ : M → M) (φ.symm y)) ∘L (mfderiv I I (φ.symm : M → M) y)
      = ContinuousLinearMap.id ℝ (TangentSpace I y) := by
  ext u
  simp only [ContinuousLinearMap.comp_apply]
  exact mfderiv_apply_mfderiv_symm φ y u

/-- `mfderiv φ x` is injective. -/
theorem mfderiv_injective (φ : M ≃ₘ⟮I, I⟯ M) (x : M) :
    Function.Injective (mfderiv I I (φ : M → M) x) := by
  intro u v huv
  have h1 := mfderiv_symm_apply_mfderiv φ x u
  have h2 := mfderiv_symm_apply_mfderiv φ x v
  rw [huv] at h1
  exact h1.symm.trans h2

/-! ## The pull-back of a metric -/

/-- **The pull-back of a metric along a diffeomorphism**, as a pointwise bilinear form:
`(pullMetBilin φ g x) u v = g (φ x) (dφ_x u) (dφ_x v)`.

The `letI` only supplies the seminormed structure on the (type-synonym) fibres that the
continuous-linear-map *operations* need; the resulting linear maps are the naive ones. -/
noncomputable def pullMetBilin (φ : M ≃ₘ⟮I, I⟯ M) (g : SMet I M) :
    (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  fun x ↦ (g.inner (φ x)).bilinearComp (mfderiv I I φ x) (mfderiv I I φ x)

@[simp] theorem pullMetBilin_apply (φ : M ≃ₘ⟮I, I⟯ M) (g : SMet I M) (x : M)
    (u v : TangentSpace I x) :
    pullMetBilin φ g x u v = g.inner (φ x) (mfderiv I I φ x u) (mfderiv I I φ x v) :=
  rfl

/-- The pull-back of a metric is symmetric. -/
theorem pullMetBilin_symm (φ : M ≃ₘ⟮I, I⟯ M) (g : SMet I M) (x : M)
    (u v : TangentSpace I x) :
    pullMetBilin φ g x u v = pullMetBilin φ g x v u := by
  simp only [pullMetBilin_apply]
  exact g.symm (φ x) _ _

/-- The pull-back of a metric is positive definite. -/
theorem pullMetBilin_pos (φ : M ≃ₘ⟮I, I⟯ M) (g : SMet I M) (x : M)
    (v : TangentSpace I x) (hv : v ≠ 0) :
    0 < pullMetBilin φ g x v v := by
  simp only [pullMetBilin_apply]
  refine g.pos (φ x) _ (fun h => hv ?_)
  exact mfderiv_injective φ x (by rw [h, map_zero])

/-! ## Push-forward of fields and pull-back of a connection -/

/-- **The push-forward of a vector field along a diffeomorphism**:
`(pushField φ σ) y = dφ_{φ⁻¹ y} (σ (φ⁻¹ y))`. -/
noncomputable def pushField (φ : M ≃ₘ⟮I, I⟯ M) (σ : Π x : M, TangentSpace I x) :
    Π x : M, TangentSpace I x :=
  fun y ↦ mfderiv I I φ (φ.symm y) (σ (φ.symm y))

@[simp] theorem pushField_apply (φ : M ≃ₘ⟮I, I⟯ M) (σ : Π x : M, TangentSpace I x) (y : M) :
    pushField φ σ y = mfderiv I I φ (φ.symm y) (σ (φ.symm y)) := rfl

/-- **The pull-back of a connection along a diffeomorphism** (as a raw function on sections):
`(pullCovFun φ ∇) σ x = dφ_{φ x}⁻¹ ( ∇_{dφ_x ·} (φ_*σ) (φ x) )`. -/
noncomputable def pullCovFun (φ : M ≃ₘ⟮I, I⟯ M)
    (cov : CovariantDerivative I E (TangentSpace I (M := M))) :
    (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x) :=
  fun σ x ↦ (mfderiv I I φ.symm (φ x)) ∘L (cov (pushField φ σ) (φ x)) ∘L (mfderiv I I φ x)

@[simp] theorem pullCovFun_apply (φ : M ≃ₘ⟮I, I⟯ M)
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (σ : Π x : M, TangentSpace I x) (x : M) (v : TangentSpace I x) :
    pullCovFun φ cov σ x v
      = mfderiv I I φ.symm (φ x) (cov (pushField φ σ) (φ x) (mfderiv I I φ x v)) := rfl

end Work.Diff.STE.C2
