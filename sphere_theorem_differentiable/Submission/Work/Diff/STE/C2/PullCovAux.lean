/-
# Layer C2 (DeTurck pull-back): the pulled-back connection is torsion-free

This file contains the *proof* of

`Work.Diff.STE.C2.pullCov_torsion_zero`,

namely that the connection `pullCovFun φ cov` obtained by pulling back a torsion-free
covariant derivative `cov : CovariantDerivative I E (TangentSpace I)` along a diffeomorphism
`φ : M ≃ₘ M` has vanishing torsion.

The mathematical content is the classical naturality of the torsion tensor under a
diffeomorphism:

* the push-forward of vector fields `pushField φ V y = dφ_{φ⁻¹y} (V (φ⁻¹ y))` commutes with the
  Lie bracket (`VectorField.mpullback_mlieBracket` for `φ.symm`, together with
  `pushField φ V = mpullback I I φ.symm V`),
* hence, writing `L = (dφ_x).inverse`, the pull-back torsion is
  `L (cov.torsion (φ x) (dφ_x a) (dφ_x b))`, which vanishes when `cov.torsion = 0`.

## Main declarations

* `Work.Diff.STE.C2.pullCov_mfderiv_inverse_eq_symm`, `Work.Diff.STE.C2.pullCov_mfderiv_symm_inverse_eq` — the inverse of `dφ_x` is
  `d(φ⁻¹)_{φ x}` and conversely.
* `Work.Diff.STE.C2.pullCov_pushField_eq_mpullback` — the push-forward is the pull-back by `φ.symm`.
* `Work.Diff.STE.C2.pullCov_mdiff_pushField` — smoothness of the push-forward of a differentiable field.
* `Work.Diff.STE.C2.pullCov_mlieBracket_pushField` — naturality of `mlieBracket` under the push-forward.
* `Work.Diff.STE.C2.pullCovFun_apply_inv` — the pull-back of a connection, written with
  `(dφ_x).inverse`.
* `Work.Diff.STE.C2.pullCov_torsion_zero_aux` — the statement of the target lemma.
-/

import Mathlib
import Submission.Work.Diff.STE.C2.Defs0

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
    [IsManifold I (⊤ : ℕ∞) M]

/-! ## The inverse of the differential of a diffeomorphism -/

/-- `(dφ_x)⁻¹ = d(φ⁻¹)_{φ x}`. -/
theorem pullCov_mfderiv_inverse_eq_symm (φ : Diffeomorph I I M M (⊤ : ℕ∞)) (x : M) :
    (mfderiv I I (φ : M → M) x).inverse = mfderiv I I (φ.symm : M → M) (φ x) := by
  refine ContinuousLinearMap.inverse_eq ?_ ?_
  · have h := mfderiv_comp_mfderiv_symm φ (φ x)
    rw [Diffeomorph.symm_apply_apply φ x] at h
    exact h
  · exact mfderiv_symm_comp_mfderiv φ x

/-- `(d(φ⁻¹)_x)⁻¹ = dφ_{φ⁻¹ x}`. -/
theorem pullCov_mfderiv_symm_inverse_eq (φ : Diffeomorph I I M M (⊤ : ℕ∞)) (x : M) :
    (mfderiv I I (φ.symm : M → M) x).inverse = mfderiv I I (φ : M → M) (φ.symm x) := by
  refine ContinuousLinearMap.inverse_eq ?_ ?_
  · have h := mfderiv_symm_comp_mfderiv φ (φ.symm x)
    rw [Diffeomorph.apply_symm_apply φ x] at h
    exact h
  · exact mfderiv_comp_mfderiv_symm φ x

/-! ## The push-forward is a pull-back -/

/-- The push-forward of a vector field along `φ` is the pull-back of that field by `φ.symm`. -/
theorem pullCov_pushField_eq_mpullback (φ : Diffeomorph I I M M (⊤ : ℕ∞)) (V : Π x : M, TangentSpace I x) :
    pushField φ V = VectorField.mpullback I I (φ.symm : M → M) V := by
  funext y
  rw [pushField_apply, VectorField.mpullback_apply, pullCov_mfderiv_symm_inverse_eq]
  rfl

/-- The push-forward of a differentiable vector field is differentiable. -/
theorem pullCov_mdiff_pushField (φ : Diffeomorph I I M M (⊤ : ℕ∞))
    {V : Π x : M, TangentSpace I x} {x : M}
    (hV : MDiffAt (T% V) x) : MDiffAt (T% (pushField φ V)) (φ x) := by
  rw [pullCov_pushField_eq_mpullback]
  exact MDifferentiableAt.mpullback_vectorField (f := (φ.symm : M → M)) (x₀ := φ x) (n := ∞)
    (by simpa only [Diffeomorph.symm_apply_apply] using hV)
    (φ.symm.contMDiffAt) (Diffeomorph.isInvertible_mfderiv φ.symm (by simp)) (by simp)

/-- The Lie bracket is natural under the push-forward by a diffeomorphism. -/
theorem pullCov_mlieBracket_pushField (φ : Diffeomorph I I M M (⊤ : ℕ∞))
    {X Y : Π x : M, TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    VectorField.mlieBracket I (pushField φ X) (pushField φ Y) (φ x)
      = mfderiv I I (φ : M → M) x (VectorField.mlieBracket I X Y x) := by
  have : IsManifold I (minSmoothness ℝ 2) M := IsManifold.of_le (n := ∞) (by simp)
  have h1 := VectorField.mpullback_mlieBracket (I := I) (I' := I) (f := (φ.symm : M → M))
    (V := X) (W := Y) (x₀ := φ x) (n := ∞)
    (by simpa only [Diffeomorph.symm_apply_apply] using hX)
    (by simpa only [Diffeomorph.symm_apply_apply] using hY)
    (φ.symm.contMDiffAt) (by simp)
  rw [← pullCov_pushField_eq_mpullback (φ := φ) X, ← pullCov_pushField_eq_mpullback (φ := φ) Y] at h1
  rw [VectorField.mpullback_apply, pullCov_mfderiv_symm_inverse_eq, Diffeomorph.symm_apply_apply] at h1
  exact h1.symm

/-! ## The pulled-back connection -/

/-- The pull-back of a connection along `φ`, with the inverse of `dφ` written as
`(dφ_x).inverse` (so that all the terms below live in syntactically matching fibres). -/
theorem pullCovFun_apply_inv (φ : Diffeomorph I I M M (⊤ : ℕ∞))
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (σ : Π x : M, TangentSpace I x) (x : M) (v : TangentSpace I x) :
    pullCovFun φ cov σ x v
      = (mfderiv I I (φ : M → M) x).inverse
          (cov (pushField φ σ) (φ x) (mfderiv I I (φ : M → M) x v)) := by
  rw [pullCovFun_apply, ← pullCov_mfderiv_inverse_eq_symm (φ := φ) x]
  rfl

/-! ## The torsion of the pulled-back connection -/

/-- **The pull-back of a torsion-free connection is torsion-free.** -/
theorem pullCov_torsion_zero_aux
    (φ : Diffeomorph I I M M (⊤ : ℕ∞)) (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (htor : cov.torsion = 0)
    (hcov : IsCovariantDerivativeOn E (Work.Diff.STE.C2.pullCovFun φ cov)) :
    ∀ (x : M) (a b : TangentSpace I x),
      IsCovariantDerivativeOn.torsion hcov x a b = 0 := by
  intro x a b
  have hf : (mfderiv I I (φ : M → M) x).IsInvertible :=
    Diffeomorph.isInvertible_mfderiv φ (by simp)
  have hfinv : ∀ w : TangentSpace I x,
      (mfderiv I I (φ : M → M) x).inverse (mfderiv I I (φ : M → M) x w) = w :=
    fun w => hf.inverse_apply_eq.mpr rfl
  have hkey : ∀ (u v : TangentSpace I x),
      IsCovariantDerivativeOn.torsion hcov x u v
        = (mfderiv I I (φ : M → M) x).inverse
            (cov.torsion (φ x) (mfderiv I I (φ : M → M) x u)
              (mfderiv I I (φ : M → M) x v)) := by
    intro u v
    rw [IsCovariantDerivativeOn.torsion_apply_eq_extend hcov u v]
    simp only [pullCovFun_apply_inv]
    have hXu : MDiffAt (T% (FiberBundle.extend E u)) x :=
      FiberBundle.mdifferentiableAt_extend (I := I) (F := E) u
    have hXv : MDiffAt (T% (FiberBundle.extend E v)) x :=
      FiberBundle.mdifferentiableAt_extend (I := I) (F := E) v
    have hpu : pushField φ (FiberBundle.extend E u) (φ x) = mfderiv I I (φ : M → M) x u := by
      rw [pushField_apply, Diffeomorph.symm_apply_apply]
      simp
    have hpv : pushField φ (FiberBundle.extend E v) (φ x) = mfderiv I I (φ : M → M) x v := by
      rw [pushField_apply, Diffeomorph.symm_apply_apply]
      simp
    have hbr := pullCov_mlieBracket_pushField (φ := φ) (X := FiberBundle.extend E u)
      (Y := FiberBundle.extend E v) (x := x) hXu hXv
    have hLbr : (mfderiv I I (φ : M → M) x).inverse
        (VectorField.mlieBracket I (pushField φ (FiberBundle.extend E u))
          (pushField φ (FiberBundle.extend E v)) (φ x))
        = VectorField.mlieBracket I (FiberBundle.extend E u) (FiberBundle.extend E v) x := by
      rw [hbr]
      exact hfinv _
    have hmvX : MDiffAt (T% (pushField φ (FiberBundle.extend E u))) (φ x) :=
      pullCov_mdiff_pushField φ hXu
    have hmvY : MDiffAt (T% (pushField φ (FiberBundle.extend E v))) (φ x) :=
      pullCov_mdiff_pushField φ hXv
    rw [← map_sub, ← hLbr, ← map_sub]
    congr 1
    rw [← hpu, ← hpv]
    rw [CovariantDerivative.torsion_apply (cov := cov)
      (X := pushField φ (FiberBundle.extend E u))
      (Y := pushField φ (FiberBundle.extend E v)) hmvX hmvY]
    try rfl
  rw [hkey a b]
  simp [htor]

end Work.Diff.STE.C2
