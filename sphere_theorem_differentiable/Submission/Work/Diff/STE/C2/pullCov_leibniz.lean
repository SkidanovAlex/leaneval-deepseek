import Mathlib
import Submission.Work.Diff.STE.C2.Defs0

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Leibniz rule for the pull-back of a metric-compatible connection (Layer C2)

If a connection `∇` on `M` is metric-compatible for a smooth metric `g` (i.e. satisfies the
Leibniz rule `d(g(Y,Z)) = g(∇Y, Z) + g(Y, ∇Z)`, hypothesis `hmet` below), then the pull-back
connection `pullCovFun φ ∇` is metric-compatible for the pull-back metric `pullMetBilin φ g`.

The proof is the standard one: for a diffeomorphism `φ`, the pull-back metric evaluated on the
pull-backs of two fields is the composition of `z ↦ g(z)(W z)(V z)` with `φ`, where
`W = pushField φ Y`, `V = pushField φ Z` are the push-forwards of `Y` and `Z`; the chain rule
turns `d` into `d_{φ x}`, `hmet` gives the Leibniz rule there, and the inverse identities
`dφ ∘ dφ⁻¹ = id` transfer the terms back.

The auxiliary lemmas (smoothness of the push-forward of a vector field, the pointwise inverse
identities for `mfderiv φ` and `mfderiv φ⁻¹`, and differentiability of the metric pairing) are
proved here as well.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
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

/-! ## The pointwise inverse identities for the differential of a diffeomorphism -/

/-- The inverse of `d(φ⁻¹)_y` is `dφ_{φ⁻¹ y}`. -/
theorem mfderiv_symm_inverse (φ : M ≃ₘ⟮I, I⟯ M) (y : M) :
    (mfderiv I I (φ.symm : M → M) y).inverse = mfderiv I I (φ : M → M) (φ.symm y) := by
  refine ContinuousLinearMap.inverse_eq ?_ ?_
  · have h := mfderiv_symm_comp_mfderiv φ (φ.symm y)
    rwa [Diffeomorph.apply_symm_apply] at h
  · exact mfderiv_comp_mfderiv_symm φ y

/-- `dφ_y (d(φ⁻¹)_{φ y} v) = v`. -/
theorem mfderiv_apply_mfderiv_symm_self (φ : M ≃ₘ⟮I, I⟯ M) (y : M)
    (v : TangentSpace I (φ y)) :
    mfderiv I I (φ : M → M) y (mfderiv I I (φ.symm : M → M) (φ y) v) = v := by
  have h := mfderiv_apply_mfderiv_symm φ (φ y) v
  rw [Diffeomorph.symm_apply_apply] at h
  exact h

/-! ## The push-forward of a vector field -/

/-- The push-forward of a vector field is Mathlib's pull-back along the inverse diffeomorphism. -/
theorem pushField_eq_mpullback (φ : M ≃ₘ⟮I, I⟯ M) (Y : Π x : M, TangentSpace I x) :
    pushField φ Y = VectorField.mpullback I I (φ.symm : M → M) Y := by
  funext y
  rw [pushField_apply, VectorField.mpullback_apply, mfderiv_symm_inverse]
  rfl

/-- The push-forward of a smooth vector field by a diffeomorphism is smooth. -/
theorem pushField_contMDiff (φ : M ≃ₘ⟮I, I⟯ M) (Y : Π x : M, TangentSpace I x)
    (hY : ContMDiff I I.tangent ∞ (fun x : M ↦ (⟨x, Y x⟩ : TangentBundle I M))) :
    ContMDiff I I.tangent ∞ (fun x : M ↦ (⟨x, pushField φ Y x⟩ : TangentBundle I M)) := by
  rw [pushField_eq_mpullback]
  refine ContMDiff.mpullback_vectorField hY φ.symm.contMDiff_toFun (fun x => ?_) le_rfl
  exact Diffeomorph.isInvertible_mfderiv φ.symm (by simp)

/-- `pushField φ Y` evaluated at `φ y` is `dφ_y (Y y)`. -/
theorem pushField_apply_self (φ : M ≃ₘ⟮I, I⟯ M) (Y : Π x : M, TangentSpace I x) (y : M) :
    pushField φ Y (φ y) = mfderiv I I (φ : M → M) y (Y y) := by
  rw [pushField_apply, Diffeomorph.symm_apply_apply]

/-! ## Differentiability of the metric pairing of two smooth fields -/

/-- All smooth sections of the tangent bundle are differentiable. -/
theorem mdiff_inner_pairing (g : SMet I M) (W V : Π x : M, TangentSpace I x) (x : M)
    (hW : CMDiff ∞ (T% W)) (hV : CMDiff ∞ (T% V)) :
    MDiffAt (fun z : M ↦ g.inner z (W z) (V z)) x := by
  letI : RiemannianBundle (fun z : M ↦ TangentSpace I z) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I 1 E (fun z : M ↦ TangentSpace I z) := inferInstance
  exact MDifferentiableAt.inner_bundle (F := E) (E := fun z : M ↦ TangentSpace I z) (b := id)
    ((hW x).mdifferentiableAt (by simp)) ((hV x).mdifferentiableAt (by simp))

/-! ## The pull-back connection paired with the pull-back metric -/

/-- The pull-back metric paired with the pull-back connection in its first argument:
this is `g(∇_{dφ v}(φ_*Y), φ_*Z)` at `φ x`, with the push-forwards left in the form that
`hmet` produces. -/
theorem pullMetBilin_pullCovFun_fst (φ : M ≃ₘ⟮I, I⟯ M) (g : SMet I M)
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (Y Z : Π x : M, TangentSpace I x) (x : M) (v : TangentSpace I x) :
    pullMetBilin φ g x (pullCovFun φ cov Y x v) (Z x)
      = g.inner (φ x) (cov (pushField φ Y) (φ x) (mfderiv I I (φ : M → M) x v))
          (pushField φ Z (φ x)) := by
  rw [pullMetBilin_apply, pullCovFun_apply, mfderiv_apply_mfderiv_symm_self (φ := φ) x,
    ← pushField_apply_self (φ := φ) (Y := Z) x]

/-- The pull-back metric paired with the pull-back connection in its second argument. -/
theorem pullMetBilin_pullCovFun_snd (φ : M ≃ₘ⟮I, I⟯ M) (g : SMet I M)
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (Y Z : Π x : M, TangentSpace I x) (x : M) (v : TangentSpace I x) :
    pullMetBilin φ g x (Y x) (pullCovFun φ cov Z x v)
      = g.inner (φ x) (pushField φ Y (φ x))
          (cov (pushField φ Z) (φ x) (mfderiv I I (φ : M → M) x v)) := by
  rw [pullMetBilin_apply, pullCovFun_apply, mfderiv_apply_mfderiv_symm_self (φ := φ) x,
    ← pushField_apply_self (φ := φ) (Y := Y) x]

/-! ## The Leibniz rule for the pull-back connection -/

theorem pullCov_leibniz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (φ : Diffeomorph I I M M (⊤ : ℕ∞)) (g : Submission.Diff.SMet I M)
    (hmet : ∀ (Y Z : Π x : M, TangentSpace I x),
      ContMDiff I I.tangent (⊤ : ℕ∞) (fun x : M ↦ (⟨x, Y x⟩ : TangentBundle I M)) →
      ContMDiff I I.tangent (⊤ : ℕ∞) (fun x : M ↦ (⟨x, Z x⟩ : TangentBundle I M)) →
      ∀ (x : M) (v : TangentSpace I x),
        mvfderiv I (fun y : M ↦ g.inner y (Y y) (Z y)) x v
          = g.inner x ((Submission.Diff.lcOf g) Y x v) (Z x)
            + g.inner x (Y x) ((Submission.Diff.lcOf g) Z x v)) :
    ∀ (Y Z : Π x : M, TangentSpace I x),
      ContMDiff I I.tangent (⊤ : ℕ∞) (fun x : M ↦ (⟨x, Y x⟩ : TangentBundle I M)) →
      ContMDiff I I.tangent (⊤ : ℕ∞) (fun x : M ↦ (⟨x, Z x⟩ : TangentBundle I M)) →
      ∀ (x : M) (v : TangentSpace I x),
        mvfderiv I (fun y : M ↦ Work.Diff.STE.C2.pullMetBilin φ g y (Y y) (Z y)) x v
          = Work.Diff.STE.C2.pullMetBilin φ g x
              (Work.Diff.STE.C2.pullCovFun φ (Submission.Diff.lcOf g) Y x v) (Z x)
            + Work.Diff.STE.C2.pullMetBilin φ g x (Y x)
              (Work.Diff.STE.C2.pullCovFun φ (Submission.Diff.lcOf g) Z x v) := by
  intro Y Z hY hZ x v
  have hW : ContMDiff I I.tangent (⊤ : ℕ∞) (T% (pushField φ Y)) := pushField_contMDiff φ Y hY
  have hV : ContMDiff I I.tangent (⊤ : ℕ∞) (T% (pushField φ Z)) := pushField_contMDiff φ Z hZ
  -- the pulled-back metric pairs the push-forwards of the fields
  have hfun : (fun y : M ↦ pullMetBilin φ g y (Y y) (Z y))
      = (fun z : M ↦ g.inner z (pushField φ Y z) (pushField φ Z z)) ∘ φ := by
    funext y
    simp only [Function.comp_apply, pullMetBilin_apply]
    rw [pushField_apply_self (φ := φ) (Y := Y) y, pushField_apply_self (φ := φ) (Y := Z) y]
  rw [hfun]
  -- the chain rule
  have hA : MDiffAt (fun z : M ↦ g.inner z (pushField φ Y z) (pushField φ Z z)) (φ x) :=
    mdiff_inner_pairing g (pushField φ Y) (pushField φ Z) (φ x) hW hV
  have hphi : MDiffAt (φ : M → M) x := mdifferentiableAt_of_diffeomorph φ x
  rw [mvfderiv_comp_apply x hA hphi v]
  -- the Leibniz rule for `g` at `φ x`, applied to the pushed-forward fields
  rw [hmet (pushField φ Y) (pushField φ Z) hW hV (φ x) (mfderiv I I φ x v)]
  -- unfold the pull-backs and cancel `dφ ∘ dφ⁻¹`
  rw [pullMetBilin_pullCovFun_fst (φ := φ) (cov := Submission.Diff.lcOf g),
      pullMetBilin_pullCovFun_snd (φ := φ) (cov := Submission.Diff.lcOf g)]

end Work.Diff.STE.C2
