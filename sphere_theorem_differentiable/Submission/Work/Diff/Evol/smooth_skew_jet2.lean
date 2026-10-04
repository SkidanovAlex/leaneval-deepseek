import Mathlib
import Submission.Work.Diff.Evol.Vocab
import Submission.Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff
import Submission.Work.Diff.Evol.mvfderiv_clm_apply
import Submission.Work.Diff.Evol.chartMap_smooth
import Submission.Work.Diff.Evol.Q_pack

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Work.Diff.Evol

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-! ## `mvfderiv` versus `mfderiv` at the identity model -/

theorem mvfderiv_eq_mfderiv_self
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : M → F) (x : M) :
    mvfderiv I f x = mfderiv I (modelWithCornersSelf ℝ F) f x := by
  ext v
  rfl

/-! ## The quadratic model function `z ↦ ½ ⟪P z, z⟫` -/

section Quad

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The quadratic map `z ↦ ½ (P z) z` attached to a continuous linear `P : E →L (E →L F)`. -/
noncomputable def quadMap (P : E →L[ℝ] (E →L[ℝ] F)) : E → F :=
  fun z => (1 / 2 : ℝ) • ((P z) z)

/-- Its derivative, `z ↦ ½ (P z + P.flip z)`, which is linear in `z`. -/
noncomputable def quadDeriv (P : E →L[ℝ] (E →L[ℝ] F)) : E →L[ℝ] (E →L[ℝ] F) :=
  (1 / 2 : ℝ) • (P + P.flip)

theorem contDiff_quadMap (P : E →L[ℝ] (E →L[ℝ] F)) : ContDiff ℝ ∞ (quadMap P) := by
  have h : ContDiff ℝ ∞ (fun z : E => (P z) z) := P.contDiff.clm_apply contDiff_id
  exact h.const_smul (1 / 2 : ℝ)

theorem hasFDerivAt_quadMap (P : E →L[ℝ] (E →L[ℝ] F)) (z : E) :
    HasFDerivAt (quadMap P) (quadDeriv P z) z := by
  have h1 : HasFDerivAt (fun z : E => (P z) z)
      ((P z).comp (ContinuousLinearMap.id ℝ E) + P.flip z) z :=
    (ContinuousLinearMap.hasFDerivAt P (x := z)).clm_apply (hasFDerivAt_id z)
  have h2 : quadDeriv P z
      = (1 / 2 : ℝ) • ((P z).comp (ContinuousLinearMap.id ℝ E) + P.flip z) := by
    simp only [quadDeriv, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_id]
  have h3 : quadMap P = (1 / 2 : ℝ) • (fun z : E => (P z) z) := rfl
  rw [h3, h2]
  exact h1.const_smul (1 / 2 : ℝ)

theorem fderiv_quadMap (P : E →L[ℝ] (E →L[ℝ] F)) (z : E) :
    fderiv ℝ (quadMap P) z = quadDeriv P z :=
  (hasFDerivAt_quadMap P z).fderiv

theorem mdifferentiableAt_quadMap (P : E →L[ℝ] (E →L[ℝ] F)) (z : E) :
    MDifferentiableAt (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ F) (quadMap P) z := by
  rw [mdifferentiableAt_iff_differentiableAt]
  exact ((P.differentiable.clm_apply differentiable_id).const_smul (1 / 2)).differentiableAt

theorem mdifferentiableAt_quadDeriv (P : E →L[ℝ] (E →L[ℝ] F)) (z : E) :
    MDifferentiableAt (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ (E →L[ℝ] F))
      (quadDeriv P) z := by
  rw [mdifferentiableAt_iff_differentiableAt]
  exact (ContinuousLinearMap.differentiable (quadDeriv P)).differentiableAt

theorem quadDeriv_apply_self (P : E →L[ℝ] (E →L[ℝ] F)) (h : E) :
    (quadDeriv P h) h = (P h) h := by
  rw [quadDeriv]
  simp only [smul_apply, add_apply, ContinuousLinearMap.flip_apply]
  rw [← two_smul ℝ ((P h) h), smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul]

theorem quadMap_zero (P : E →L[ℝ] (E →L[ℝ] F)) : quadMap P 0 = 0 := by
  simp [quadMap]

theorem quadDeriv_zero (P : E →L[ℝ] (E →L[ℝ] F)) : quadDeriv P 0 = 0 := by
  ext k
  simp only [quadDeriv, smul_apply, add_apply, ContinuousLinearMap.flip_apply, map_zero,
    zero_apply, add_zero, smul_zero]

theorem fderiv_fderiv_quadMap_zero (P : E →L[ℝ] (E →L[ℝ] F)) :
    fderiv ℝ (fun z : E => fderiv ℝ (quadMap P) z) 0 = quadDeriv P := by
  have h : (fun z : E => fderiv ℝ (quadMap P) z) = quadDeriv P := by
    funext z
    exact fderiv_quadMap P z
  rw [h]
  exact ContinuousLinearMap.fderiv (quadDeriv P) (x := 0)

end Quad

/-! ## The main theorem -/

theorem smooth_skew_jet2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (((⊤ : ℕ∞) : WithTop ℕ∞)) M] [I.Boundaryless] [T2Space M]
    {n : ℕ} (x : M) (Q : TangentSpace I x → TangentSpace I x → (Fin n → Fin n → ℝ))
    (hQlin1 : ∀ (r s : ℝ) (v₁ v₂ : TangentSpace I x) (w : TangentSpace I x),
      Q (r • v₁ + s • v₂) w = r • Q v₁ w + s • Q v₂ w)
    (hQlin2 : ∀ (r s : ℝ) (v : TangentSpace I x) (w₁ w₂ : TangentSpace I x),
      Q v (r • w₁ + s • w₂) = r • Q v w₁ + s • Q v w₂)
    (hQsym : ∀ v w : TangentSpace I x, Q v w = Q w v)
    (hQsk : ∀ (v w : TangentSpace I x) (p i : Fin n), Q v w i p = -(Q v w p i)) :
    ∃ B : M → (Fin n → Fin n → ℝ),
      Work.Diff.Evol.SmoothMap I M B ∧ B x = 0 ∧
      (∀ (y : M) (p i : Fin n), B y i p = -(B y p i)) ∧
      (∀ v : TangentSpace I x, mvfderiv I B x v = 0) ∧
      (∀ (W : Π y : M, TangentSpace I y), Work.Diff.Evol.SmoothField I M W →
        mvfderiv I (fun y : M => mvfderiv I B y (W y)) x (W x) = Q (W x) (W x)) := by
  classical
  -- The chart map: globally smooth, vanishing at `x`, with the chart's derivative there.
  obtain ⟨φ, hφsm, hφx, hφderiv⟩ := chartMap_smooth (I := I) (M := M) x
  -- Packing `Q` into a continuous linear map (with `V := E`, since `TangentSpace I x` is `E`).
  obtain ⟨Qp, hQp⟩ :=
    Q_pack (V := E) (F := (Fin n → Fin n → ℝ)) Q hQlin1 hQlin2
  -- The derivative of the chart at `x` is invertible; `S` is its inverse.
  have hTinv : (mvfderiv I (extChartAt I x) x).IsInvertible := by
    rw [mvfderiv_eq_mfderiv_self]
    exact isInvertible_mfderiv_extChartAt (mem_extChartAt_source x)
  have hφinv : (mvfderiv I φ x).IsInvertible := by
    rw [hφderiv]
    exact hTinv
  set S : E →L[ℝ] E := (mvfderiv I φ x).inverse with hSdef
  have hST : ∀ v : TangentSpace I x, S (mvfderiv I φ x v) = v := fun v =>
    hφinv.inverse_apply_self v
  -- The bilinear form `P` on `E`.
  let P₀ : E →ₗ[ℝ] (E →L[ℝ] (Fin n → Fin n → ℝ)) :=
    { toFun := fun z => (Qp (S z)).comp S
      map_add' := by
        intro a b
        ext h
        simp only [ContinuousLinearMap.comp_apply, add_apply, map_add]
      map_smul' := by
        intro c a
        refine ContinuousLinearMap.ext fun h => ?_
        show (Qp (S (c • a))) (S h) = c • ((Qp (S a)) (S h))
        rw [map_smul, map_smul, ContinuousLinearMap.smul_apply] }
  let P : E →L[ℝ] (E →L[ℝ] (Fin n → Fin n → ℝ)) := P₀.toContinuousLinearMap
  have hP : ∀ z : E, P z = (Qp (S z)).comp S := fun z => rfl
  have hPz : ∀ z : E, (P z) z = Qp (S z) (S z) := by
    intro z
    simp only [hP, ContinuousLinearMap.comp_apply]
  have hQpsk : ∀ (v w : E) (p i : Fin n), Qp v w i p = -(Qp v w p i) := by
    intro v w p i
    rw [hQp v w]
    exact hQsk v w p i
  have hφmd : MDifferentiableAt I (modelWithCornersSelf ℝ E) φ x :=
    hφsm.mdifferentiableAt (by simp)
  refine ⟨quadMap P ∘ φ, ?_, ?_, ?_, ?_, ?_⟩
  · -- smoothness
    exact (contDiff_quadMap P).contMDiff.comp hφsm
  · -- value at `x`
    show quadMap P (φ x) = 0
    rw [hφx, quadMap_zero]
  · -- skew-symmetry
    intro y p i
    show (quadMap P (φ y)) i p = -((quadMap P (φ y)) p i)
    have h1 : quadMap P (φ y) = (1 / 2 : ℝ) • (Qp (S (φ y)) (S (φ y))) := by
      rw [quadMap, hPz]
    rw [h1]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hQpsk]
    ring
  · -- vanishing differential at `x`
    intro v
    have hpoint0 : mvfderiv I (quadMap P ∘ φ) x v
        = (fderiv ℝ (quadMap P) (φ x)) (mvfderiv I φ x v) := by
      rw [mvfderiv_comp (x := x) (mdifferentiableAt_quadMap P (φ x)) hφmd,
        mvfderiv_eq_fderiv]
      rfl
    rw [hpoint0, fderiv_quadMap, hφx, quadDeriv_zero]
    exact ContinuousLinearMap.zero_apply (mvfderiv I φ x v)
  · -- the second derivative
    intro W hW
    set V : M → E := fun y : M => mvfderiv I φ y (W y) with hVdef
    have hVsm : ContMDiff I (modelWithCornersSelf ℝ E) ∞ V := by
      rw [hVdef]
      exact Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff hφsm hW
    have hVmd : MDifferentiableAt I (modelWithCornersSelf ℝ E) V x :=
      hVsm.mdifferentiableAt (by simp)
    have hAmd : MDifferentiableAt I (modelWithCornersSelf ℝ (E →L[ℝ] (Fin n → Fin n → ℝ)))
        (quadDeriv P ∘ φ) x :=
      (((quadDeriv P).contMDiff.comp hφsm).contMDiffAt).mdifferentiableAt (by simp)
    -- pointwise chain rule
    have hpoint : ∀ y : M,
        mvfderiv I (quadMap P ∘ φ) y (W y) = (quadDeriv P ∘ φ) y (V y) := by
      intro y
      have hfy : MDifferentiableAt I (modelWithCornersSelf ℝ E) φ y :=
        hφsm.mdifferentiableAt (by simp)
      rw [mvfderiv_comp (x := y) (mdifferentiableAt_quadMap P (φ y)) hfy,
        mvfderiv_eq_fderiv, fderiv_quadMap]
      rfl
    rw [show (fun y : M => mvfderiv I (quadMap P ∘ φ) y (W y))
        = (fun y : M => (quadDeriv P ∘ φ) y (V y)) from funext hpoint]
    rw [mvfderiv_clm_apply hAmd hVmd (W x)]
    -- the second factor vanishes since `fderiv (quadMap P) 0 = 0`
    have hAx : (quadDeriv P ∘ φ) x = 0 := by
      show quadDeriv P (φ x) = 0
      rw [hφx, quadDeriv_zero]
    rw [hAx, zero_apply, add_zero]
    -- the first factor: chain rule for `quadDeriv P ∘ φ`
    have hAval : mvfderiv I (quadDeriv P ∘ φ) x (W x) = quadDeriv P (V x) := by
      rw [mvfderiv_comp (x := x) (mdifferentiableAt_quadDeriv P (φ x)) hφmd,
        mvfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
      rfl
    have hVx : V x = mvfderiv I φ x (W x) := by rw [hVdef]
    rw [hAval, hVx, quadDeriv_apply_self, hPz, hST]
    exact hQp (W x) (W x)

end Work.Diff.Evol
