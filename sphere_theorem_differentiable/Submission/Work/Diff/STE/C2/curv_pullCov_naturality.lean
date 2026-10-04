/-
# Layer C2 (DeTurck pull-back): naturality of the curvature tensor

`Work.Diff.STE.C2.curv_pullCov_naturality` is the naturality of the Riemann curvature tensor of a
covariant derivative under a diffeomorphism `φ`:

`curv (φ*∇) X Y Z x = d(φ⁻¹)_{φ x} (curv ∇ (φ_*X) (φ_*Y) (φ_*Z) (φ x))`.

Unlike the naturality of the torsion (or of the Levi-Civita connection), this holds for an
*arbitrary* covariant derivative `cov`: no torsion-freeness and no metric compatibility is needed.
The reason is that the pull-back of a connection is defined using only the differential of `φ`, and
the only two structural ingredients in the definition of the curvature,

* `(φ*∇)_σ x = d(φ⁻¹)_{φ x} ∘ ∇_{dφ_x ·} (φ_*σ) ∘ dφ_x`,
* `φ_*` is compatible with the Lie bracket (`pullCov_mlieBracket_pushField`),

combine as follows.  Write `L_x = d(φ⁻¹)_{φ x}` and `d_x = dφ_x`.  The push-forward of the
pull-back of a section `σ` is the covariant derivative of the push-forward:

`φ_* ((φ*∇) σ) = ∇ (φ_*σ)`,  i.e. `d_y (L_y (∇_{d_y ·} (φ_*σ))) = ∇_{d_y ·} (φ_*σ)`,

because `d_y ∘ L_y = id` (`mfderiv_apply_mfderiv_symm`).  Applying this to the two inner terms of
`curv (φ*∇) X Y Z` and using the naturality of the Lie bracket for the third term, the two sides
of the claimed identity differ only by the positions of `L_x`, and both are clopen by
`L_x (a - b - c) = L_x a - L_x b - L_x c`.

All the technical content is the bookkeeping of the (definitionally, but not syntactically) equal
fibres `TangentSpace I z = E`; the auxiliary `symmDeriv` (from
`Submission.Work.Diff.STE.C2.pullCov_isCovariantDerivative`) is used to keep the terms well typed.
-/

import Mathlib
import Submission.Work.Diff.STE.C2.Defs
import Submission.Work.Diff.STE.C2.PullCovAux

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false
-- `TangentSpace I z` is a plain `def` equal to `E`, so definitional equality across it needs
-- full transparency.
set_option backward.isDefEq.respectTransparency false

namespace Work.Diff.STE.C2

/-- **The push-forward of the pull-back of a connection is the covariant derivative of the
push-forward.**  For any two fields `σ`, `W`,

`pushField φ (fun y ↦ pullCovFun φ cov σ y (W y))
   = fun y ↦ cov (pushField φ σ) y (pushField φ W y)`.

At a point `y` the left-hand side is `dφ_{φ⁻¹y} (L_{φ⁻¹y} (∇_{dφ_{φ⁻¹y} ·}(φ_*σ)))`, and
`dφ_{φ⁻¹y}` cancels `L_{φ⁻¹y} = d(φ⁻¹)_{φ (φ⁻¹ y)}` by `mfderiv_apply_mfderiv_symm`. -/
theorem pushField_pullCovFun
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (φ : Diffeomorph I I M M (⊤ : ℕ∞))
    (cov : CovariantDerivative I E (TangentSpace I (M := M))) (σ W : Π y : M, TangentSpace I y) :
    pushField φ (fun y : M => pullCovFun φ cov σ y (W y))
      = fun y : M => cov (pushField φ σ) y (pushField φ W y) := by
  funext y
  rw [pushField_apply]
  rw [pushField_apply]
  rw [pullCovFun_apply]
  rw [Diffeomorph.apply_symm_apply]
  exact mfderiv_apply_mfderiv_symm φ y _

theorem curv_pullCov_naturality
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (φ : Diffeomorph I I M M (⊤ : ℕ∞))
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (X Y Z : Π x : M, TangentSpace I x) (x : M)
    (hX : MDifferentiableAt I I.tangent (fun y : M ↦ (⟨y, X y⟩ : TangentBundle I M)) x)
    (hY : MDifferentiableAt I I.tangent (fun y : M ↦ (⟨y, Y y⟩ : TangentBundle I M)) x) :
    LeanEval.Geometry.SphereTheorem.curv (Work.Diff.STE.C2.pullCov φ cov) X Y Z x
      = mfderiv I I (φ.symm : M → M) (φ x)
          (LeanEval.Geometry.SphereTheorem.curv cov (Work.Diff.STE.C2.pushField φ X)
            (Work.Diff.STE.C2.pushField φ Y) (Work.Diff.STE.C2.pushField φ Z) (φ x)) := by
  have hY' : pushField φ (fun y : M => pullCovFun φ cov Z y (Y y))
      = fun y : M => cov (pushField φ Z) y (pushField φ Y y) := pushField_pullCovFun φ cov Z Y
  have hX' : pushField φ (fun y : M => pullCovFun φ cov Z y (X y))
      = fun y : M => cov (pushField φ Z) y (pushField φ X y) := pushField_pullCovFun φ cov Z X
  have hbr : VectorField.mlieBracket I (pushField φ X) (pushField φ Y) (φ x)
      = mfderiv I I (φ : M → M) x (VectorField.mlieBracket I X Y x) :=
    pullCov_mlieBracket_pushField φ hX hY
  simp only [LeanEval.Geometry.SphereTheorem.curv, pullCov]
  rw [pullCovFun_apply_symmDeriv, pullCovFun_apply_symmDeriv, pullCovFun_apply_symmDeriv]
  rw [hY', hX']
  rw [← pushField_apply_self φ X x, ← pushField_apply_self φ Y x, ← hbr]
  rw [← map_sub, ← map_sub]
  rfl

end Work.Diff.STE.C2
