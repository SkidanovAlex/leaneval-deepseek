/-
# Layer C2 (DeTurck pull-back): the pulled-back connection is a covariant derivative

This file proves that the raw pull-back `Work.Diff.STE.C2.pullCovFun φ cov` of a (bundled)
covariant derivative `cov` along a diffeomorphism `φ` satisfies `IsCovariantDerivativeOn`:
it is additive and satisfies the Leibniz rule.

The mathematical content is the naturality of a Koszul connection under a diffeomorphism:
`(φ*∇)_v σ = dφ⁻¹_{φx} ( ∇_{dφ_x v} (φ_* σ) )` where `(φ_*σ)_y = dφ_{φ⁻¹y} (σ (φ⁻¹y))`.
The only non-trivial ingredient is that `φ_*σ` is differentiable at `φ x` whenever `σ` is
differentiable at `x` (the tangent map of a diffeomorphism is smooth and `φ⁻¹` is smooth).

A note on the formalisation. `TangentSpace I z` is (deliberately) a non-reducible `def` equal
to `E`, and `mfderiv I I φ.symm (φ x)` has codomain `TangentSpace I (φ.symm (φ x))`, which is
only *definitionally* (not syntactically) equal to `TangentSpace I x`. Since `pullCovFun` is a
continuous-linear-map composite, `pullCovFun_apply` (in `Defs0`) relates terms whose types
differ in that invisible way, and rewriting inside such a goal is brittle. We therefore prove a
well-typed variant `pullCovFun_apply_symmDeriv`, written with the auxiliary `symmDeriv φ x`, a
definition whose *declared* codomain is `TangentSpace I x`.

Both structural facts about `pushField` are proved here:
* `pushField_add`, `pushField_smul` -- linearity in the field,
* `mdiffAt_pushField` -- differentiability at `φ x` of the push-forward of a differentiable field.
-/

import Mathlib
import Submission.Work.Diff.STE.C2.Defs0
import Submission.Work.Diff.STE.C2.pullCov_leibniz

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
-- `TangentSpace I z` is a plain `def` equal to `E`, so definitional equality across it needs
-- full transparency (which is what the `backward.isDefEq` switch restores).
set_option backward.isDefEq.respectTransparency false

namespace Work.Diff.STE.C2

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

section PullCov

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]

/-! ## The two identifications behind the pull-back of a connection -/

/-- `d(φ⁻¹)_{φ x}`, with its codomain *ascribed* to `TangentSpace I x`.  The point is that the
type of `mfderiv I I φ.symm (φ x)` has codomain `TangentSpace I (φ.symm (φ x))`, which is only
definitionally equal to `TangentSpace I x`; the auxiliary definition has the codomain we want
*by definition*, so that terms built from it are well typed. -/
noncomputable def symmDeriv (φ : M ≃ₘ⟮I, I⟯ M) (x : M) :
    TangentSpace I (φ x) →L[ℝ] TangentSpace I x :=
  mfderiv I I (φ.symm : M → M) (φ x)

/-- The chain rule `d(φ⁻¹)_{φ x} ∘ dφ_x = id`. -/
theorem symmDeriv_mfderiv_apply (φ : M ≃ₘ⟮I, I⟯ M) (x : M) (v : TangentSpace I x) :
    symmDeriv φ x (mfderiv I I (φ : M → M) x v) = v :=
  mfderiv_symm_apply_mfderiv φ x v

/-- The well-typed unfolding of the pulled-back connection at a vector. -/
theorem pullCovFun_apply_symmDeriv (φ : M ≃ₘ⟮I, I⟯ M)
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (σ : Π x : M, TangentSpace I x) (x : M) (v : TangentSpace I x) :
    pullCovFun φ cov σ x v
      = symmDeriv φ x (cov (pushField φ σ) (φ x) (mfderiv I I (φ : M → M) x v)) := rfl

/-! ## The push-forward of a field -/

/-- The push-forward of fields is additive in the field. -/
theorem pushField_add (φ : M ≃ₘ⟮I, I⟯ M) (σ σ' : Π x : M, TangentSpace I x) :
    pushField φ (σ + σ') = pushField φ σ + pushField φ σ' := by
  funext y
  simp only [pushField_apply, Pi.add_apply, map_add]

/-- The push-forward of fields is `C^∞(M)`-linear in the field: `φ_*(g σ) = (g ∘ φ⁻¹) (φ_*σ)`. -/
theorem pushField_smul (φ : M ≃ₘ⟮I, I⟯ M) (g : M → ℝ) (σ : Π x : M, TangentSpace I x) :
    pushField φ (g • σ) = (fun y : M ↦ g (φ.symm y)) • pushField φ σ := by
  funext y
  simp only [pushField_apply]
  exact map_smul (mfderiv I I (φ : M → M) (φ.symm y)) (g (φ.symm y)) (σ (φ.symm y))

-- (`pushField_apply_self` is declared in `Submission.Work.Diff.STE.C2.pullCov_leibniz`.)

/-- **The push-forward of a differentiable field is differentiable.** If `σ` is differentiable
at `x` then `φ_*σ = dφ ∘ σ ∘ φ⁻¹` is differentiable at `φ x`.

Indeed `T% (φ_* σ) = tangentMap φ ∘ (T% σ) ∘ φ⁻¹` and the tangent map of a diffeomorphism of
class `C^∞` is `C^∞` (`ContMDiff.contMDiff_tangentMap`). -/
theorem mdiffAt_pushField (φ : M ≃ₘ⟮I, I⟯ M) (σ : Π x : M, TangentSpace I x) (x : M)
    (hσ : MDiffAt (T% σ) x) : MDiffAt (T% (pushField φ σ)) (φ x) := by
  have htan : MDifferentiableAt I.tangent I.tangent (tangentMap I I (φ : M → M)) (T% σ x) :=
    (φ.contMDiff_toFun.contMDiff_tangentMap (m := ((⊤ : ℕ∞) : ℕ∞ω))
      (by simp)).contMDiffAt.mdifferentiableAt (by simp)
  have hσ' : MDiffAt (T% σ) (φ.symm (φ x)) := by
    rw [Diffeomorph.symm_apply_apply φ x]; exact hσ
  have hinner : MDifferentiableAt I I.tangent (fun y : M ↦ T% σ (φ.symm y)) (φ x) := by
    have h := hσ'.comp (φ x) (mdifferentiableAt_of_diffeomorph_symm φ (φ x))
    simpa [Function.comp_def] using h
  have htan' : MDifferentiableAt I.tangent I.tangent (tangentMap I I (φ : M → M))
      (T% σ (φ.symm (φ x))) := by
    rw [Diffeomorph.symm_apply_apply φ x]; exact htan
  have houter : MDifferentiableAt I I.tangent
      (fun y : M ↦ tangentMap I I (φ : M → M) (T% σ (φ.symm y))) (φ x) :=
    htan'.comp (φ x) hinner
  have hfun : T% (pushField φ σ)
      = (fun y : M ↦ tangentMap I I (φ : M → M) (T% σ (φ.symm y))) := by
    funext y
    refine TotalSpace.ext ?_ HEq.rfl
    exact (Diffeomorph.apply_symm_apply φ y).symm
  exact houter.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq hfun)

end PullCov

theorem pullCov_isCovariantDerivative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (φ : Diffeomorph I I M M (⊤ : ℕ∞)) (cov : CovariantDerivative I E (TangentSpace I (M := M))) :
    IsCovariantDerivativeOn E (Work.Diff.STE.C2.pullCovFun φ cov) := by
  refine ⟨?_, ?_⟩
  · -- additivity: `φ_*` is additive, `cov` is additive, `d(φ⁻¹)_{φ x}` is linear
    intro σ σ' x hσ hσ' _
    have h1 := mdiffAt_pushField φ σ x hσ
    have h2 := mdiffAt_pushField φ σ' x hσ'
    ext v
    rw [pullCovFun_apply_symmDeriv, add_apply, pullCovFun_apply_symmDeriv]
    rw [pushField_add, (cov.isCovariantDerivativeOn).add h1 h2]
    rw [add_apply]
    exact map_add _ _ _
  · -- the Leibniz rule: `φ_*` is `C^∞`-linear, `cov` satisfies Leibniz, and
    -- `d(g ∘ φ⁻¹)_{φ x} ∘ dφ_x = dg_x` by the chain rule
    intro σ g x hσ hg _
    have h1 := mdiffAt_pushField φ σ x hσ
    have hsymm : MDifferentiableAt I I (φ.symm : M → M) (φ x) :=
      mdifferentiableAt_of_diffeomorph_symm φ (φ x)
    have hg' : MDiffAt g (φ.symm (φ x)) := by
      rw [Diffeomorph.symm_apply_apply φ x]; exact hg
    have h2 : MDifferentiableAt I 𝓘(ℝ) (fun y : M ↦ g (φ.symm y)) (φ x) := by
      have h := hg'.comp (φ x) hsymm
      simpa [Function.comp_def] using h
    have htuple := (cov.isCovariantDerivativeOn).leibniz h1 h2
    ext v
    rw [pullCovFun_apply_symmDeriv, add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
      pullCovFun_apply_symmDeriv]
    rw [pushField_smul, htuple]
    rw [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
    rw [map_add, map_smul, map_smul]
    -- the chain rule for the scalar factor `g ∘ φ⁻¹` at `φ x`
    have hchain : d% (fun y : M ↦ g (φ.symm y)) (φ x) (mfderiv I I (φ : M → M) x v)
        = d% g x v := by
      have h := mvfderiv_comp_apply_of_eq (f := (φ.symm : M → M)) (g := g) (x := φ x) (y := x)
        hg hsymm (Diffeomorph.symm_apply_apply φ x) (mfderiv I I (φ : M → M) x v)
      rw [mfderiv_symm_apply_mfderiv φ x v] at h
      simpa [Function.comp_def] using h
    rw [pushField_apply_self, Diffeomorph.symm_apply_apply φ x]
    rw [symmDeriv_mfderiv_apply, hchain]

end Work.Diff.STE.C2
