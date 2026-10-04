import Mathlib
import Submission.Work.Diff.GE.deps
import Submission.Work.Diff.C.mvfderiv_contMDiffAt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The tangent vector `(0, v)` of `ℝ × M` at the point `(t, x)`. -/
noncomputable def sndVec (t : ℝ) (x : M) (v : TangentSpace I x) :
    TangentSpace (𝓘(ℝ,ℝ).prod I) (t, x) :=
  ((0 : TangentSpace (𝓘(ℝ,ℝ)) t), v)

/-- The section `p ↦ (0, X p.2)` of the tangent bundle of `ℝ × M`. -/
noncomputable def towerSection (X : Π y : M, TangentSpace I y) :
    Π p : ℝ × M, TangentSpace (𝓘(ℝ,ℝ).prod I) p :=
  fun p ↦ ((0 : TangentSpace (𝓘(ℝ,ℝ)) p.1), X p.2)

lemma towerSection_eq_sndVec (X : Π y : M, TangentSpace I y) (p : ℝ × M) :
    towerSection (I := I) X p = sndVec (I := I) p.1 p.2 (X p.2) := rfl

/-- **Differentiating in the manifold variable along the time-independent vector `(0, v)`.**
This is the chain rule for `F : ℝ × M → ℝ` along the curve `y ↦ (t, y)`, together with
`mfderiv_prod_eq_add_apply`. -/
theorem mvfderiv_prod_snd {F : ℝ × M → ℝ} {t : ℝ} {x : M}
    (hF : MDifferentiableAt (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) F (t,x)) (v : TangentSpace I x) :
    mvfderiv (𝓘(ℝ,ℝ).prod I) F (t,x) (sndVec (I := I) t x v)
      = mvfderiv I (fun y ↦ F (t,y)) x v := by
  have h := mfderiv_prod_eq_add_apply (f := F) (p := (t,x))
    (v := (sndVec (I := I) t x v)) hF
  simp only [mvfderiv, ContinuousLinearMap.comp_apply] at h ⊢
  rw [h]
  simp [sndVec]

/-- **Smoothness of the section `p ↦ (0, X p.2)`.**  Via the canonical identification of the
tangent bundle of a product with the product of the tangent bundles. -/
theorem contMDiff_towerSection {X : Π y : M, TangentSpace I y} (hX : CMDiff ∞ (T% X)) :
    CMDiff ∞ (T% (towerSection (I := I) X)) := by
  have h1 : CMDiff ∞ (fun p : ℝ × M ↦
      (zeroSection ℝ (TangentSpace (𝓘(ℝ,ℝ))) p.1 : TangentBundle (𝓘(ℝ,ℝ)) ℝ)) :=
    (contMDiff_zeroSection ℝ (TangentSpace (𝓘(ℝ,ℝ)))).comp contMDiff_fst
  have h2 : CMDiff ∞ (fun p : ℝ × M ↦ ((T% X) p.2 : TangentBundle I M)) :=
    hX.comp contMDiff_snd
  have hZ : CMDiff ∞ (fun p : ℝ × M ↦
      ((zeroSection ℝ (TangentSpace (𝓘(ℝ,ℝ))) p.1 : TangentBundle (𝓘(ℝ,ℝ)) ℝ),
        ((T% X) p.2 : TangentBundle I M))) := h1.prodMk h2
  have hV := (contMDiff_equivTangentBundleProd_symm (n := ∞)).comp hZ
  have hEq : ((equivTangentBundleProd 𝓘(ℝ,ℝ) ℝ I M).symm ∘ fun p : ℝ × M ↦
      ((zeroSection ℝ (TangentSpace (𝓘(ℝ,ℝ))) p.1 : TangentBundle (𝓘(ℝ,ℝ)) ℝ),
        ((T% X) p.2 : TangentBundle I M)))
      = (T% (towerSection (I := I) X)) := by
    funext p
    simp only [Function.comp_apply, towerSection, zeroSection, equivTangentBundleProd,
      Equiv.coe_fn_symm_mk]
  rw [hEq] at hV
  exact hV

theorem tower_jointSmooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless]
    {J : Set ℝ} (hJ : IsOpen J) {u : ℝ → M → ℝ}
    (hu : ContMDiffOn (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞ (fun p : ℝ × M ↦ u p.1 p.2) (J ×ˢ univ))
    {X : Π y : M, TangentSpace I y} (hX : CMDiff ∞ (T% X)) :
    ContMDiffOn (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞
      (fun p : ℝ × M ↦ mvfderiv I (u p.1) p.2 (X p.2)) (J ×ˢ univ) := by
  intro p₀ hp₀
  have hJs : IsOpen (J ×ˢ (univ : Set M)) := hJ.prod isOpen_univ
  have hmem : (J ×ˢ (univ : Set M)) ∈ 𝓝 p₀ := hJs.mem_nhds hp₀
  -- the joint function is smooth at `p₀`
  have hFat : CMDiffAt ∞ (fun p : ℝ × M ↦ u p.1 p.2) p₀ := hu.contMDiffAt hmem
  -- the section `(0, X ·)` is a smooth section of the tangent bundle of `ℝ × M`
  have hVsm : CMDiff ∞ (T% (towerSection (I := I) X)) := contMDiff_towerSection (I := I) hX
  have hVat : CMDiffAt ∞ (T% (towerSection (I := I) X)) p₀ := hVsm.contMDiffAt
  -- hence the derivative on `ℝ × M` along that section is smooth at `p₀`
  have hpt := Work.Diff.C.mvfderiv_contMDiffAt (I := 𝓘(ℝ,ℝ).prod I)
    (F := fun p : ℝ × M ↦ u p.1 p.2) (X := towerSection (I := I) X) hFat hVat
  -- and it agrees with the requested function near `p₀`
  refine (hpt.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [hmem] with p hp
  have hFp : MDifferentiableAt (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) (fun p : ℝ × M ↦ u p.1 p.2) p :=
    (hu.contMDiffAt (hJs.mem_nhds hp)).mdifferentiableAt (by simp)
  rw [towerSection_eq_sndVec, ← mvfderiv_prod_snd (I := I) hFp (X p.2)]

end Work.Diff.GE
