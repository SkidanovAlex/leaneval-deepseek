import Mathlib
import Submission.Work.TangentClasses.Examples
import Submission.Work.Thom.ThomAPI

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# Stable triviality of the tangent bundle of the sphere

`Work.Agree.sphereStableTrivial`: the Whitney sum `TSⁿ ⊕ ε¹` of the tangent bundle of the sphere
`Sⁿ = Metric.sphere (0 : ℝ^{n+1}) 1` with the trivial line bundle is isomorphic (in the sense of
`Work.Thom.BundleIso`) to the trivial bundle with fibre `ℝ^{n+1}`.

The proof is the classical one: the tangent plane field `b ↦ b^⊥` is complementary to the normal
line `ℝ·b`, spanned by the differentiable global section `b ↦ b`; the resulting trivialisation of
`ε^{n+1}` restricts to `TSⁿ ⊕ ε¹`.
-/

namespace Work.Agree

open scoped Manifold ContDiff Topology InnerProductSpace
open Metric
open Work.TangentClasses

noncomputable section

/-- The sphere `Sⁿ ⊆ ℝ^{n+1}`, as a type. -/
abbrev Sph (n : ℕ) : Type := ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)

/-- The model space `ℝⁿ`. -/
abbrev En (n : ℕ) : Type := EuclideanSpace ℝ (Fin n)

/-- The ambient space `ℝ^{n+1}`. -/
abbrev EN (n : ℕ) : Type := EuclideanSpace ℝ (Fin (n + 1))

/-- The trivial line `ℝ¹`. -/
abbrev T1 : Type := EuclideanSpace ℝ (Fin 1)

/-- The sphere in `ℝ^{n+1}` is charted by stereographic projection on `ℝⁿ`. -/
instance instFactFinrank (n : ℕ) : Fact (Module.finrank ℝ (EN n) = n + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

/-- **The tangent bundle of the sphere `Sⁿ`**, in the standard charting by `ℝⁿ`. -/
abbrev Zsph (n : ℕ) : RealBundle (Sph n) (En n) (atlas (En n) (Sph n)) :=
  tangentSphere n

/-! ## The chart parametrisation of the sphere and its derivative -/

/-- The inverse of the chart at `b`, read in the ambient space. -/
def param (n : ℕ) (b : Sph n) : En n → EN n :=
  fun x => ((chartAt (En n) b).symm x : EN n)

/-- The orthogonal-complement isometry attached to the chart at `b`. -/
def Usp (n : ℕ) (b : Sph n) : (ℝ ∙ ((-b : Sph n) : EN n))ᗮ ≃ₗᵢ[ℝ] En n :=
  (OrthonormalBasis.fromOrthogonalSpanSingleton n (ne_zero_of_mem_unit_sphere (-b))).repr

/-- The explicit formula for the chart parametrisation. -/
lemma param_eq (n : ℕ) (b : Sph n) :
    param n b = (stereoInvFunAux ((-b : Sph n) : EN n)) ∘ (Subtype.val) ∘
      (fun x => (Usp n b).symm x) := by
  funext x
  rw [param, Function.comp_apply, Function.comp_apply,
    show chartAt (En n) b = stereographic' n (-b) from rfl]
  simp only [stereographic'_symm_apply]
  rw [stereoInvFunAux_apply, smul_add]
  rfl

/-- **The derivative of the chart parametrisation at the origin** is the inclusion of the tangent
plane `b^⊥` into the ambient space, in the chart coordinates. -/
lemma hasFDerivAt_param (n : ℕ) (b : Sph n) :
    HasFDerivAt (param n b)
      (((ℝ ∙ ((-b : Sph n) : EN n))ᗮ.subtypeL).comp
        ((Usp n b).symm : En n →L[ℝ] (ℝ ∙ ((-b : Sph n) : EN n))ᗮ)) 0 := by
  rw [param_eq n b]
  have hg : HasFDerivAt (stereoInvFunAux ((-b : Sph n) : EN n) ∘ Subtype.val)
      ((ℝ ∙ ((-b : Sph n) : EN n))ᗮ.subtypeL)
      (((Usp n b).symm : En n →L[ℝ] (ℝ ∙ ((-b : Sph n) : EN n))ᗮ) 0) := by
    rw [map_zero]
    exact hasFDerivAt_stereoInvFunAux_comp_coe ((-b : Sph n) : EN n)
  exact hg.comp (0 : En n) ((Usp n b).symm : En n →L[ℝ] (ℝ ∙ ((-b : Sph n) : EN n))ᗮ).hasFDerivAt

/-- The chart at `b` sends `b` to the origin. -/
lemma chartAt_self_apply (n : ℕ) (b : Sph n) : (chartAt (En n) b) b = 0 := by
  rw [show chartAt (En n) b = stereographic' n (-b) from rfl, stereographic',
    OpenPartialHomeomorph.trans_apply, stereographic_neg_apply]
  simp only [Homeomorph.toOpenPartialHomeomorph_apply, LinearIsometryEquiv.coe_toHomeomorph, map_zero]

/-- **The differential of the inclusion `Sⁿ ↪ ℝ^{n+1}` at `b`**, in the chart at `b`. -/
def phi (n : ℕ) (b : Sph n) : En n →L[ℝ] EN n :=
  fderiv ℝ (param n b) 0

/-- The defining formula of `phi`. -/
lemma phi_eq (n : ℕ) (b : Sph n) :
    phi n b = ((ℝ ∙ ((-b : Sph n) : EN n))ᗮ.subtypeL).comp
      ((Usp n b).symm : En n →L[ℝ] (ℝ ∙ ((-b : Sph n) : EN n))ᗮ) := by
  rw [phi, (hasFDerivAt_param n b).fderiv]

/-- The differential of the inclusion is injective. -/
lemma phi_injective (n : ℕ) (b : Sph n) : Function.Injective (phi n b) := by
  rw [phi_eq]
  exact Subtype.val_injective.comp (Usp n b).symm.injective

/-- The differential of the inclusion is orthogonal to the base point. -/
lemma phi_inner (n : ℕ) (b : Sph n) (u : En n) : ⟪phi n b u, (b : EN n)⟫_ℝ = 0 := by
  rw [phi_eq, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
  have h' : ⟪((-b : Sph n) : EN n),
      (((Usp n b).symm u : (ℝ ∙ ((-b : Sph n) : EN n))ᗮ) : EN n)⟫_ℝ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp ((Usp n b).symm u).2
  have hb : (b : EN n) = -(((-b : Sph n) : EN n)) := by simp
  rw [hb, inner_neg_right, real_inner_comm]
  change -⟪((-b : Sph n) : EN n),
      (((Usp n b).symm u : (ℝ ∙ ((-b : Sph n) : EN n))ᗮ) : EN n)⟫_ℝ = 0
  rw [h', neg_zero]

/-! ## Smoothness of the chart parametrisations -/

/-- **The chart parametrisation `(chartAt b)⁻¹` read in the ambient space is smooth.** -/
lemma contDiff_chart_symm_coe (n : ℕ) (i : ↥(atlas (En n) (Sph n))) :
    ContDiff ℝ (⊤ : WithTop ℕ∞) (fun x : En n => ((i.1).symm x : EN n)) := by
  obtain ⟨v, hv⟩ := i.2
  set x₀ : Sph n := -v with hx₀
  have hchart : i.1 = chartAt (En n) x₀ := by
    rw [hv, hx₀]
    show stereographic' n v = chartAt (En n) (-v)
    rw [show chartAt (En n) (-v) = stereographic' n (-(-v)) from rfl, neg_neg]
  have h1 : ContMDiffOn (𝓘(ℝ, En n)) (𝓘(ℝ, En n)) (⊤ : WithTop ℕ∞)
      (⇑(extChartAt (𝓘(ℝ, En n)) x₀).symm) (extChartAt (𝓘(ℝ, En n)) x₀).target :=
    contMDiffOn_extChartAt_symm x₀
  have h2 : ContMDiff (𝓘(ℝ, En n)) (𝓘(ℝ, EN n)) (⊤ : WithTop ℕ∞) (fun y : Sph n => (y : EN n)) :=
    contMDiff_coe_sphere (n := n) (m := ⊤)
  have h3 := h2.comp_contMDiffOn h1
  have htgt : (extChartAt (𝓘(ℝ, En n)) x₀).target = Set.univ := by
    rw [show (extChartAt (𝓘(ℝ, En n)) x₀) = (chartAt (En n) x₀).extend (𝓘(ℝ, En n)) from rfl,
      show chartAt (En n) x₀ = stereographic' n (-x₀) from rfl,
      OpenPartialHomeomorph.extend_target, stereographic'_target, Set.preimage_univ, Set.univ_inter,
      ModelWithCorners.range_eq_univ]
  rw [htgt] at h3
  have h4 : ContMDiffOn (𝓘(ℝ, En n)) (𝓘(ℝ, EN n)) (⊤ : WithTop ℕ∞)
      (fun x : En n => ((i.1).symm x : EN n)) Set.univ := by
    refine h3.congr (fun x _ => ?_)
    rw [hchart]
    rfl
  exact contDiffOn_univ.mp (contMDiffOn_iff_contDiffOn.mp h4)

lemma contMDiffOn_chartAt_symm (n : ℕ) (y : Sph n) :
    ContMDiffOn (𝓘(ℝ, En n)) (𝓘(ℝ, En n)) (⊤ : WithTop ℕ∞)
      (⇑(chartAt (En n) y).symm) Set.univ := by
  have htgt : (extChartAt (𝓘(ℝ, En n)) y).target = Set.univ := by
    rw [show (extChartAt (𝓘(ℝ, En n)) y) = (chartAt (En n) y).extend (𝓘(ℝ, En n)) from rfl,
      show chartAt (En n) y = stereographic' n (-y) from rfl,
      OpenPartialHomeomorph.extend_target, stereographic'_target, Set.preimage_univ, Set.univ_inter,
      ModelWithCorners.range_eq_univ]
  rw [← htgt]
  exact contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, En n)) y

lemma contMDiffOn_chartAt (n : ℕ) (y : Sph n) :
    ContMDiffOn (𝓘(ℝ, En n)) (𝓘(ℝ, En n)) (⊤ : WithTop ℕ∞)
      (⇑(chartAt (En n) y)) (chartAt (En n) y).source :=
  contMDiffOn_extChartAt (I := 𝓘(ℝ, En n)) (x := y)

/-- **The transition between two chart parametrisations is smooth.** -/
lemma contDiffAt_chart_comp_chart_symm (n : ℕ) (i j : ↥(atlas (En n) (Sph n))) (x : En n)
    (hx' : ((i.1).symm x : Sph n) ∈ (j.1).source) :
    ContDiffAt ℝ (⊤ : WithTop ℕ∞) (fun y : En n => (j.1) ((i.1).symm y)) x := by
  obtain ⟨v, hv⟩ := i.2
  obtain ⟨w, hw⟩ := j.2
  set x₀ : Sph n := -v with hx₀
  set y₀ : Sph n := -w with hy₀
  have hchart : i.1 = chartAt (En n) x₀ := by
    rw [hv, hx₀]
    show stereographic' n v = chartAt (En n) (-v)
    rw [show chartAt (En n) (-v) = stereographic' n (-(-v)) from rfl, neg_neg]
  have hchart' : j.1 = chartAt (En n) y₀ := by
    rw [hw, hy₀]
    show stereographic' n w = chartAt (En n) (-w)
    rw [show chartAt (En n) (-w) = stereographic' n (-(-w)) from rfl, neg_neg]
  have hx'' : ((i.1).symm x : Sph n) ∈ (chartAt (En n) y₀).source := by
    rw [hchart'] at hx'; exact hx'
  have h1 : ContMDiffAt (𝓘(ℝ, En n)) (𝓘(ℝ, En n)) (⊤ : WithTop ℕ∞) (⇑(i.1).symm) x := by
    rw [hchart]
    exact (contMDiffOn_chartAt_symm n x₀).contMDiffAt Filter.univ_mem
  have h2 : ContMDiffAt (𝓘(ℝ, En n)) (𝓘(ℝ, En n)) (⊤ : WithTop ℕ∞) (⇑(j.1)) ((i.1).symm x) := by
    rw [hchart']
    exact (contMDiffOn_chartAt n y₀).contMDiffAt ((chartAt (En n) y₀).open_source.mem_nhds hx'')
  have h3 : ContMDiffAt (𝓘(ℝ, En n)) (𝓘(ℝ, En n)) (⊤ : WithTop ℕ∞)
      ((⇑(j.1)) ∘ (⇑(i.1).symm)) x := h2.comp x h1
  exact contMDiffAt_iff_contDiffAt.mp h3

/-! ## The chart expression of the differential of the inclusion -/

/-- **The chart expression of the differential of the inclusion**: in the trivialisation of the
tangent bundle by the chart `i`, the differential of the inclusion at `b` is the derivative of the
chart parametrisation of `i` at `i b`. -/
lemma phi_comp_coordChange (n : ℕ) (i : ↥(atlas (En n) (Sph n))) (b : Sph n)
    (hb : b ∈ (Zsph n).baseSet i) :
    (phi n b).comp ((Zsph n).coordChange i ((Zsph n).indexAt b) b)
      = fderiv ℝ (fun x : En n => ((i.1).symm x : EN n)) ((i.1) b) := by
  have hbs : b ∈ (i.1).source := hb
  have hsymm : ((i.1).symm ((i.1) b) : Sph n) = b := (i.1).left_inv hbs
  have hcoord : (Zsph n).coordChange i ((Zsph n).indexAt b) b
      = fderiv ℝ (fun x : En n => (chartAt (En n) b) ((i.1).symm x)) ((i.1) b) := by
    rw [show (Zsph n) = tangentBundleCore (𝓘(ℝ, En n)) (Sph n) from rfl,
      tangentBundleCore_coordChange, ModelWithCorners.range_eq_univ, fderivWithin_univ]
    rfl
  rw [hcoord]
  have h1 : HasFDerivAt (fun x : En n => ((i.1).symm x : EN n))
      (fderiv ℝ (fun x : En n => ((i.1).symm x : EN n)) ((i.1) b)) ((i.1) b) :=
    (((contDiff_chart_symm_coe n i).contDiffAt).differentiableAt (by simp)).hasFDerivAt
  have h2 : HasFDerivAt (fun x : En n => (chartAt (En n) b) ((i.1).symm x))
      (fderiv ℝ (fun x : En n => (chartAt (En n) b) ((i.1).symm x)) ((i.1) b)) ((i.1) b) :=
    (((contDiffAt_chart_comp_chart_symm n i (achart (En n) b) ((i.1) b)) (by
        change ((i.1).symm ((i.1) b) : Sph n) ∈ (chartAt (En n) b).source
        rw [hsymm]; exact mem_chart_source (En n) b)).differentiableAt (by simp)).hasFDerivAt
  have h3 : HasFDerivAt (param n b) (phi n b) ((chartAt (En n) b) ((i.1).symm ((i.1) b))) := by
    rw [hsymm, chartAt_self_apply n b, phi, (hasFDerivAt_param n b).fderiv]
    exact hasFDerivAt_param n b
  have hchain := h3.comp ((i.1) b) h2
  have hev : (fun x : En n => ((i.1).symm x : EN n)) =ᶠ[𝓝 ((i.1) b)]
      (param n b ∘ (fun x : En n => (chartAt (En n) b) ((i.1).symm x))) := by
    have hcont : ContinuousAt (fun x : En n => ((i.1).symm x : Sph n)) ((i.1) b) :=
      ((i.1).continuousOn_symm.continuousAt ((i.1).open_target.mem_nhds ((i.1).map_source hbs)))
    have hmem : ∀ᶠ x in 𝓝 ((i.1) b), ((i.1).symm x : Sph n) ∈ (chartAt (En n) b).source :=
      hcont.eventually ((chartAt (En n) b).open_source.mem_nhds (by
        change ((i.1).symm ((i.1) b) : Sph n) ∈ (chartAt (En n) b).source
        rw [hsymm]; exact mem_chart_source (En n) b))
    filter_upwards [hmem] with x hx
    show ((i.1).symm x : EN n) = ((chartAt (En n) b).symm ((chartAt (En n) b) ((i.1).symm x)) : EN n)
    rw [OpenPartialHomeomorph.left_inv _ hx]
  exact (hchain.congr_of_eventuallyEq hev).unique h1

/-! ## The geometric fibrewise maps -/

/-- The standard identification `ℝ¹ ≃ ℝ`. -/
def oneEquiv : T1 ≃L[ℝ] ℝ :=
  (EuclideanSpace.equiv (Fin 1) ℝ).trans (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ)

/-- The trivial line bundle `ε¹` over `Sⁿ`. -/
abbrev eps1 (n : ℕ) (ι₀ : Type) [Inhabited ι₀] : RealBundle (Sph n) T1 ι₀ :=
  trivialVectorBundleCore ℝ (Sph n) T1 ι₀

/-- The Whitney sum `TSⁿ ⊕ ε¹`. -/
abbrev Wsum (n : ℕ) (ι₀ : Type) [Inhabited ι₀] :
    RealBundle (Sph n) (En n × T1) (atlas (En n) (Sph n) × ι₀) :=
  Work.Thom.bundleSum (Zsph n) (eps1 n ι₀)

/-- The linear map `(u,t) ↦ φ u + t • b`. -/
def mkMap (n : ℕ) (b : Sph n) (φ : En n →L[ℝ] EN n) : (En n × T1) →L[ℝ] EN n :=
  φ.coprod ((ContinuousLinearMap.toSpanSingleton ℝ (b : EN n)).comp (oneEquiv : T1 →L[ℝ] ℝ))

theorem mkMap_apply (n : ℕ) (b : Sph n) (φ : En n →L[ℝ] EN n) (u : En n) (t : T1) :
    mkMap n b φ (u, t) = φ u + (oneEquiv t) • (b : EN n) := by
  rw [mkMap, ContinuousLinearMap.coprod_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply]
  rfl

/-- The geometric fibrewise map `(u,t) ↦ φ_b u + t • b` of the stable trivialisation. -/
def bigA (n : ℕ) (b : Sph n) : (En n × T1) →L[ℝ] EN n := mkMap n b (phi n b)

/-- `bigA`, viewed as an endomorphism of `ℝⁿ × ℝ¹` through the splitting `ρ`. -/
def tildeA (n : ℕ) (b : Sph n) : (En n × T1) →L[ℝ] (En n × T1) :=
  ((Work.Thom.rhoR n).symm : EN n →L[ℝ] (En n × T1)).comp (bigA n b)

/-- The derivative of the chart parametrisation of `i`, at `i b`. -/
def chartDeriv (n : ℕ) (i : ↥(atlas (En n) (Sph n))) (b : Sph n) : En n →L[ℝ] EN n :=
  fderiv ℝ (fun x : En n => ((i.1).symm x : EN n)) ((i.1) b)

/-- The "chart" version of `bigA`. -/
def Bchart (n : ℕ) (i : ↥(atlas (En n) (Sph n))) (b : Sph n) : (En n × T1) →L[ℝ] EN n :=
  mkMap n b (chartDeriv n i b)

/-- The transition function `Z.coordChange i (indexAt b) b × 1`. -/
def Cchart (n : ℕ) (i : ↥(atlas (En n) (Sph n))) (b : Sph n) : (En n × T1) →L[ℝ] (En n × T1) :=
  ((Zsph n).coordChange i ((Zsph n).indexAt b) b).prodMap (ContinuousLinearMap.id ℝ T1)

/-- Its two-sided inverse. -/
def CchartInv (n : ℕ) (i : ↥(atlas (En n) (Sph n))) (b : Sph n) : (En n × T1) →L[ℝ] (En n × T1) :=
  ((Zsph n).coordChange ((Zsph n).indexAt b) i b).prodMap (ContinuousLinearMap.id ℝ T1)

/-- `ρ⁻¹ ∘ Bᵢ(b)`, an endomorphism of `ℝⁿ × ℝ¹`. -/
def betaChart (n : ℕ) (i : ↥(atlas (En n) (Sph n))) (b : Sph n) :
    (En n × T1) →L[ℝ] (En n × T1) :=
  ((Work.Thom.rhoR n).symm : EN n →L[ℝ] (En n × T1)).comp (Bchart n i b)

/-- The fibrewise inverse of `bigA`: the inverse of `ρ⁻¹ ∘ bigA` composed with `ρ⁻¹`. -/
def invB (n : ℕ) (b : Sph n) : EN n →L[ℝ] (En n × T1) :=
  (Ring.inverse (tildeA n b)).comp ((Work.Thom.rhoR n).symm : EN n →L[ℝ] (En n × T1))

/-! ## The chart expression of `bigA` -/

/-- **The chart expression of `bigA`**: in the chart `(i,j)` of the Whitney sum, `bigA b` becomes
the chart derivative `Bᵢ(b)`. -/
theorem bigA_comp_Cchart (n : ℕ) (i : ↥(atlas (En n) (Sph n))) (b : Sph n)
    (hb : b ∈ (Zsph n).baseSet i) :
    (bigA n b).comp (Cchart n i b) = Bchart n i b := by
  refine ContinuousLinearMap.ext (fun v => ?_)
  obtain ⟨u, t⟩ := v
  simp only [ContinuousLinearMap.comp_apply, Cchart, ContinuousLinearMap.coe_prodMap',
    ContinuousLinearMap.id_apply, Prod.map_apply, bigA, Bchart, mkMap_apply]
  rw [show phi n b ((Zsph n).coordChange i ((Zsph n).indexAt b) b u)
      = chartDeriv n i b u from by
    rw [← ContinuousLinearMap.comp_apply, phi_comp_coordChange n i b hb]
    rfl]

theorem tildeA_comp_Cchart (n : ℕ) (i : ↥(atlas (En n) (Sph n))) (b : Sph n)
    (hb : b ∈ (Zsph n).baseSet i) :
    (tildeA n b).comp (Cchart n i b) = betaChart n i b := by
  rw [tildeA, betaChart, ContinuousLinearMap.comp_assoc, bigA_comp_Cchart n i b hb]

/-! ## Invertibility -/

theorem bigA_injective (n : ℕ) (b : Sph n) : Function.Injective (bigA n b) := by
  intro v w hvw
  obtain ⟨u, t⟩ := v
  obtain ⟨u', t'⟩ := w
  have h1 : oneEquiv t = oneEquiv t' := by
    have h := congrArg (fun z => ⟪z, (b : EN n)⟫_ℝ) hvw
    simp only [bigA, mkMap_apply, inner_add_left, inner_smul_left, phi_inner, zero_add,
      real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere, one_pow, mul_one] at h
    exact h
  obtain rfl : t = t' := oneEquiv.injective h1
  have h2 : phi n b u = phi n b u' := by
    simp only [bigA, mkMap_apply] at hvw
    exact add_right_cancel hvw
  exact Prod.ext (phi_injective n b h2) rfl

theorem Cchart_mul_CchartInv (n : ℕ) (i : ↥(atlas (En n) (Sph n))) (b : Sph n)
    (hb : b ∈ (Zsph n).baseSet i) :
    Cchart n i b * CchartInv n i b = 1 := by
  rw [ContinuousLinearMap.mul_def]
  refine ContinuousLinearMap.ext (fun v => ?_)
  obtain ⟨u, t⟩ := v
  simp only [ContinuousLinearMap.comp_apply, Cchart, CchartInv, ContinuousLinearMap.coe_prodMap',
    ContinuousLinearMap.id_apply, Prod.map_apply, ContinuousLinearMap.one_def]
  rw [(Zsph n).coordChange_comp ((Zsph n).indexAt b) i ((Zsph n).indexAt b) b
    ⟨⟨(Zsph n).mem_baseSet_at b, hb⟩, (Zsph n).mem_baseSet_at b⟩ u,
    (Zsph n).coordChange_self ((Zsph n).indexAt b) b ((Zsph n).mem_baseSet_at b) u]

theorem CchartInv_mul_Cchart (n : ℕ) (i : ↥(atlas (En n) (Sph n))) (b : Sph n)
    (hb : b ∈ (Zsph n).baseSet i) :
    CchartInv n i b * Cchart n i b = 1 := by
  rw [ContinuousLinearMap.mul_def]
  refine ContinuousLinearMap.ext (fun v => ?_)
  obtain ⟨u, t⟩ := v
  simp only [ContinuousLinearMap.comp_apply, Cchart, CchartInv, ContinuousLinearMap.coe_prodMap',
    ContinuousLinearMap.id_apply, Prod.map_apply, ContinuousLinearMap.one_def]
  rw [(Zsph n).coordChange_comp i ((Zsph n).indexAt b) i b
    ⟨⟨hb, (Zsph n).mem_baseSet_at b⟩, hb⟩ u, (Zsph n).coordChange_self i b hb u]

theorem isUnit_Cchart (n : ℕ) (i : ↥(atlas (En n) (Sph n))) (b : Sph n)
    (hb : b ∈ (Zsph n).baseSet i) : IsUnit (Cchart n i b) :=
  ⟨⟨Cchart n i b, CchartInv n i b, Cchart_mul_CchartInv n i b hb,
      CchartInv_mul_Cchart n i b hb⟩, rfl⟩

theorem isUnit_tildeA (n : ℕ) (b : Sph n) : IsUnit (tildeA n b) := by
  have hinj : Function.Injective (tildeA n b) := by
    rw [tildeA]
    exact (Work.Thom.rhoR n).symm.injective.comp (bigA_injective n b)
  have hker : (↑(tildeA n b) : (En n × T1) →ₗ[ℝ] (En n × T1)).ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr hinj
  have hsurj : Function.Surjective (tildeA n b) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).mp hinj
  have hrange : (↑(tildeA n b) : (En n × T1) →ₗ[ℝ] (En n × T1)).range = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  refine ⟨ContinuousLinearEquiv.toUnit
    (ContinuousLinearEquiv.ofBijective (tildeA n b) hker hrange), ?_⟩
  rfl

theorem betaChart_eq_mul (n : ℕ) (i : ↥(atlas (En n) (Sph n))) (b : Sph n)
    (hb : b ∈ (Zsph n).baseSet i) :
    betaChart n i b = tildeA n b * Cchart n i b := by
  rw [← tildeA_comp_Cchart n i b hb, ContinuousLinearMap.mul_def]

theorem isUnit_betaChart (n : ℕ) (i : ↥(atlas (En n) (Sph n))) (b : Sph n)
    (hb : b ∈ (Zsph n).baseSet i) : IsUnit (betaChart n i b) := by
  rw [betaChart_eq_mul n i b hb]
  exact (isUnit_tildeA n b).mul (isUnit_Cchart n i b hb)

/-- **The inverse of `ρ⁻¹ ∘ bigA` is the chart transition times the inverse of `ρ⁻¹ ∘ Bᵢ`.** -/
theorem Ring_inverse_tildeA (n : ℕ) (i : ↥(atlas (En n) (Sph n))) (b : Sph n)
    (hb : b ∈ (Zsph n).baseSet i) :
    Ring.inverse (tildeA n b) = Cchart n i b * Ring.inverse (betaChart n i b) := by
  obtain ⟨u, hu⟩ := isUnit_Cchart n i b hb
  obtain ⟨v, hv⟩ := isUnit_betaChart n i b hb
  have h1 : tildeA n b * ↑u = ↑v := by
    rw [hu, hv, ContinuousLinearMap.mul_def, tildeA_comp_Cchart n i b hb]
  have h2 : tildeA n b = ↑(v * u⁻¹) := by
    have h3 : tildeA n b * ↑(u * u⁻¹) = tildeA n b := by
      rw [Units.val_mul, Units.mul_inv, mul_one]
    calc tildeA n b = tildeA n b * ↑(u * u⁻¹) := h3.symm
      _ = tildeA n b * ↑u * ↑(u⁻¹) := by rw [Units.val_mul, mul_assoc]
      _ = ↑v * ↑(u⁻¹) := by rw [h1]
      _ = ↑(v * u⁻¹) := by rw [Units.val_mul]
  rw [h2, Ring.inverse_unit, show (v * u⁻¹)⁻¹ = u * v⁻¹ from by rw [mul_inv_rev, inv_inv],
    Units.val_mul, hu, ← Ring.inverse_unit v, hv]

/-! ## Continuity -/

theorem continuousOn_chartDeriv (n : ℕ) (i : ↥(atlas (En n) (Sph n))) :
    ContinuousOn (fun b : Sph n => chartDeriv n i b) (i.1).source :=
  (ContDiff.continuous_fderiv (contDiff_chart_symm_coe n i) (by simp)).comp_continuousOn
    (i.1).continuousOn

theorem continuousOn_Bchart (n : ℕ) (i : ↥(atlas (En n) (Sph n))) :
    ContinuousOn (fun b : Sph n => Bchart n i b) (i.1).source := by
  rw [continuousOn_iff_continuous_domRestrict]
  refine Work.Thom.continuous_clm_of_continuous_apply_gen
    (fun b : ↥(i.1).source => Bchart n i b.1) ?_
  have h1 : Continuous fun b : ↥(i.1).source => chartDeriv n i b.1 :=
    (continuousOn_iff_continuous_domRestrict.mp (continuousOn_chartDeriv n i))
  have h2 : Continuous fun p : ↥(i.1).source × (En n × T1) => (chartDeriv n i p.1.1) p.2.1 :=
    (h1.comp continuous_fst).clm_apply continuous_snd.fst
  have h3 : Continuous fun p : ↥(i.1).source × (En n × T1) => oneEquiv p.2.2 :=
    oneEquiv.continuous.comp continuous_snd.snd
  have h4 : Continuous fun p : ↥(i.1).source × (En n × T1) => ((p.1.1 : Sph n) : EN n) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst)
  refine (h2.add (h3.smul h4)).congr (fun p => ?_)
  simp only [Pi.add_apply]
  rw [Bchart]
  exact (mkMap_apply n p.1.1 (chartDeriv n i p.1.1) p.2.1 p.2.2).symm

theorem continuousOn_betaChart (n : ℕ) (i : ↥(atlas (En n) (Sph n))) :
    ContinuousOn (fun b : Sph n => betaChart n i b) (i.1).source := by
  have h := ContinuousOn.clm_comp
    (continuousOn_const (c := ((Work.Thom.rhoR n).symm : EN n →L[ℝ] (En n × T1))))
    (continuousOn_Bchart n i)
  refine h.congr (fun b _ => ?_)
  rw [betaChart]

theorem continuousOn_inv_betaChart (n : ℕ) (i : ↥(atlas (En n) (Sph n))) :
    ContinuousOn (fun b : Sph n => Ring.inverse (betaChart n i b)) (i.1).source := by
  rw [continuousOn_iff_continuous_domRestrict]
  rw [continuous_iff_continuousAt]
  intro b
  let F : ↥(i.1).source → (En n × T1) →L[ℝ] (En n × T1) := fun b => betaChart n i b.1
  have h1 : ContinuousAt F b :=
    (continuousOn_iff_continuous_domRestrict.mp (continuousOn_betaChart n i)).continuousAt
  obtain ⟨v, hv⟩ := isUnit_betaChart n i b.1 b.2
  have h2 : ContinuousAt (Ring.inverse) (F b) := by
    show ContinuousAt Ring.inverse (betaChart n i b.1)
    rw [← hv]
    exact NormedRing.inverse_continuousAt v
  exact h2.comp h1

theorem Zsph_baseSet (n : ℕ) (i : ↥(atlas (En n) (Sph n))) :
    (Zsph n).baseSet i = (i.1).source := rfl

theorem eps1_baseSet (n : ℕ) (ι₀ : Type) [Inhabited ι₀] (j : ι₀) :
    (eps1 n ι₀).baseSet j = Set.univ := rfl

theorem eps1_coordChange (n : ℕ) (ι₀ : Type) [Inhabited ι₀] (j j' : ι₀) (b : Sph n) :
    (eps1 n ι₀).coordChange j j' b = 1 := rfl

theorem trivialBaseSet (n : ℕ) (ι' : Type) [Inhabited ι'] (i : ι') :
    (trivialVectorBundleCore ℝ (Sph n) (EN n) ι').baseSet i = Set.univ := rfl

theorem trivialCoordChange (n : ℕ) (ι' : Type) [Inhabited ι'] (i j : ι') (b : Sph n) :
    (trivialVectorBundleCore ℝ (Sph n) (EN n) ι').coordChange i j b = 1 := rfl

theorem Wsum_coordChange_comp_Cchart (n : ℕ) (ι₀ : Type) [Inhabited ι₀]
    (i i' : ↥(atlas (En n) (Sph n))) (j j' : ι₀) (b : Sph n)
    (hb : b ∈ (Wsum n ι₀).baseSet (i, j)) (hb' : b ∈ (Wsum n ι₀).baseSet (i', j')) :
    (Wsum n ι₀).coordChange ((Wsum n ι₀).indexAt b) (i', j') b ∘SL Cchart n i b
      = (Wsum n ι₀).coordChange (i, j) (i', j') b := by
  have hcc : (Wsum n ι₀).coordChange (i, j) ((Wsum n ι₀).indexAt b) b = Cchart n i b := by
    rw [Cchart, show (Wsum n ι₀).indexAt b
        = ((Zsph n).indexAt b, (eps1 n ι₀).indexAt b) from rfl,
      Wsum, Work.Thom.bundleSum_coordChange, eps1_coordChange, ContinuousLinearMap.one_def]
  rw [← hcc]
  refine ContinuousLinearMap.ext (fun v => ?_)
  exact (Wsum n ι₀).coordChange_comp (i, j) ((Wsum n ι₀).indexAt b) (i', j') b
    ⟨⟨hb, (Wsum n ι₀).mem_baseSet_at b⟩, hb'⟩ v

/-- **The chart expression of `invB`**: on `baseSet (i,·)`, the fibrewise inverse of the stable
trivialisation has the chart expression `(Z.coordChange i i' b × 1) ∘ (ρ⁻¹ ∘ Bᵢ(b))⁻¹ ∘ ρ⁻¹`. -/
theorem chartExpression_invB (n : ℕ) (ι₀ : Type) [Inhabited ι₀]
    (i i' : ↥(atlas (En n) (Sph n))) (j j' : ι₀) (b : Sph n)
    (hb : b ∈ (Wsum n ι₀).baseSet (i, j)) (hb' : b ∈ (Wsum n ι₀).baseSet (i', j')) :
    (Wsum n ι₀).coordChange ((Wsum n ι₀).indexAt b) (i', j') b ∘SL invB n b
      = (Wsum n ι₀).coordChange (i, j) (i', j') b ∘SL Ring.inverse (betaChart n i b) ∘SL
          ((Work.Thom.rhoR n).symm : EN n →L[ℝ] (En n × T1)) := by
  have hZ : b ∈ (Zsph n).baseSet i :=
    (show b ∈ (Zsph n).baseSet i ∩ (eps1 n ι₀).baseSet j from hb).1
  have hcoc := Wsum_coordChange_comp_Cchart n ι₀ i i' j j' b hb hb'
  have hri : Ring.inverse (tildeA n b) = Cchart n i b * Ring.inverse (betaChart n i b) :=
    Ring_inverse_tildeA n i b hZ
  refine ContinuousLinearMap.ext (fun w => ?_)
  show (Wsum n ι₀).coordChange ((Wsum n ι₀).indexAt b) (i', j') b
      ((Ring.inverse (tildeA n b)) ((Work.Thom.rhoR n).symm w))
    = (Wsum n ι₀).coordChange (i, j) (i', j') b
      ((Ring.inverse (betaChart n i b)) ((Work.Thom.rhoR n).symm w))
  rw [hri, mul_apply_eq_comp, ← ContinuousLinearMap.comp_apply, hcoc]

/-! ## The bundle isomorphism -/

/-- **`TSⁿ ⊕ ε¹` is isomorphic to the trivial bundle with fibre `ℝ^{n+1}`.** -/
theorem nonempty_Wsum_trivial (n : ℕ) (ι₀ ι' : Type) [Inhabited ι₀] [Inhabited ι'] :
    Nonempty (Work.Thom.BundleIso (Wsum n ι₀)
      (trivialVectorBundleCore ℝ (Sph n) (EN n) ι')) := by
  refine ⟨{ hom := fun b => (bigA n b).toLinearMap
            inv := fun b => (invB n b).toLinearMap
            left_inv := ?_
            right_inv := ?_
            continuous_hom := ?_
            continuous_inv := ?_ }⟩
  · intro b x
    obtain ⟨u, hu⟩ := isUnit_tildeA n b
    show (Ring.inverse (tildeA n b)) ((Work.Thom.rhoR n).symm (bigA n b x)) = x
    have h1 : (Work.Thom.rhoR n).symm (bigA n b x) = tildeA n b x := rfl
    rw [h1, ← hu, Ring.inverse_unit, ← mul_apply_eq_comp, Units.inv_mul,
      ContinuousLinearMap.one_def, ContinuousLinearMap.id_apply]
  · intro b y
    obtain ⟨u, hu⟩ := isUnit_tildeA n b
    show bigA n b ((Ring.inverse (tildeA n b)) ((Work.Thom.rhoR n).symm y)) = y
    have h1 : bigA n b ((Ring.inverse (tildeA n b)) ((Work.Thom.rhoR n).symm y))
        = (Work.Thom.rhoR n) (tildeA n b
            ((Ring.inverse (tildeA n b)) ((Work.Thom.rhoR n).symm y))) := by
      rw [tildeA, ContinuousLinearMap.comp_apply]
      exact (ContinuousLinearEquiv.apply_symm_apply (Work.Thom.rhoR n) _).symm
    rw [h1, ← hu, Ring.inverse_unit, ← mul_apply_eq_comp, Units.mul_inv,
      ContinuousLinearMap.one_def, ContinuousLinearMap.id_apply,
      ContinuousLinearEquiv.apply_symm_apply]
  · refine Work.Thom.continuous_totalSpaceMap_clm_gen (Wsum n ι₀)
        (trivialVectorBundleCore ℝ (Sph n) (EN n) ι') (ContinuousMap.id (Sph n))
        (fun b => bigA n b) (fun i₁ i₂ => ?_)
    obtain ⟨i, j⟩ := i₁
    have hset : (Wsum n ι₀).baseSet (i, j)
        ∩ (ContinuousMap.id (Sph n)) ⁻¹'
          (trivialVectorBundleCore ℝ (Sph n) (EN n) ι').baseSet i₂ = (i.1).source := by
      have h1 : (Wsum n ι₀).baseSet (i, j) = (i.1).source := by
        rw [Wsum, Work.Thom.bundleSum_baseSet, Zsph_baseSet, eps1_baseSet, Set.inter_univ]
      rw [h1, trivialBaseSet, Set.preimage_univ, Set.inter_univ]
    rw [hset]
    simp only [ContinuousMap.id_apply, trivialCoordChange, ContinuousLinearMap.one_def,
      ContinuousLinearMap.id_comp]
    refine (continuousOn_Bchart n i).congr (fun b hb => ?_)
    rw [show (Wsum n ι₀).coordChange (i, j) ((Wsum n ι₀).indexAt b) b = Cchart n i b from by
      rw [Cchart, show (Wsum n ι₀).indexAt b
          = ((Zsph n).indexAt b, (eps1 n ι₀).indexAt b) from rfl,
        Wsum, Work.Thom.bundleSum_coordChange, eps1_coordChange, ContinuousLinearMap.one_def]]
    exact bigA_comp_Cchart n i b hb
  · refine Work.Thom.continuous_totalSpaceMap_clm_gen
        (trivialVectorBundleCore ℝ (Sph n) (EN n) ι') (Wsum n ι₀) (ContinuousMap.id (Sph n))
        (fun b => invB n b) (fun i₁ i₂ => ?_)
    obtain ⟨i', j'⟩ := i₂
    have hset : (trivialVectorBundleCore ℝ (Sph n) (EN n) ι').baseSet i₁
        ∩ (ContinuousMap.id (Sph n)) ⁻¹' (Wsum n ι₀).baseSet (i', j')
        = (Wsum n ι₀).baseSet (i', j') := by
      rw [trivialBaseSet, Set.univ_inter,
        show ⇑(ContinuousMap.id (Sph n)) = id from rfl, Set.preimage_id]
    rw [hset]
    simp only [ContinuousMap.id_apply, trivialCoordChange, ContinuousLinearMap.one_def,
      ContinuousLinearMap.comp_id]
    rw [continuousOn_iff_continuous_domRestrict, continuous_iff_continuousAt]
    intro b₀
    set i : ↥(atlas (En n) (Sph n)) := (Zsph n).indexAt b₀.1 with hi
    have hb₀i : b₀.1 ∈ (i.1).source := (Zsph n).mem_baseSet_at b₀.1
    have hb₀ : b₀.1 ∈ (Wsum n ι₀).baseSet (i, default) := by
      show b₀.1 ∈ (Zsph n).baseSet i ∩ (eps1 n ι₀).baseSet default
      exact ⟨hb₀i, Set.mem_univ _⟩
    have hloc : ContinuousAt (fun b : ↥((Wsum n ι₀).baseSet (i', j')) =>
        (Wsum n ι₀).coordChange (i, default) (i', j') b.1
          ∘SL Ring.inverse (betaChart n i b.1)
          ∘SL ((Work.Thom.rhoR n).symm : EN n →L[ℝ] (En n × T1))) b₀ := by
      have hcc : ContinuousAt (fun b : ↥((Wsum n ι₀).baseSet (i', j')) =>
          (Wsum n ι₀).coordChange (i, default) (i', j') b.1) b₀ := by
        have h1 : ContinuousAt (fun b : Sph n =>
            (Wsum n ι₀).coordChange (i, default) (i', j') b) b₀.1 :=
          (((Wsum n ι₀).continuousOn_coordChange (i, default) (i', j')).continuousWithinAt
            ⟨hb₀, b₀.2⟩).continuousAt
            (((Wsum n ι₀).isOpen_baseSet (i, default)).inter
              ((Wsum n ι₀).isOpen_baseSet (i', j')) |>.mem_nhds ⟨hb₀, b₀.2⟩)
        exact h1.comp continuous_subtype_val.continuousAt
      have hinv : ContinuousAt (fun b : ↥((Wsum n ι₀).baseSet (i', j')) =>
          Ring.inverse (betaChart n i b.1)) b₀ := by
        have h1 : ContinuousWithinAt (fun b : Sph n => Ring.inverse (betaChart n i b))
            ((i.1).source) b₀.1 :=
          (continuousOn_inv_betaChart n i).continuousWithinAt hb₀i
        exact (h1.continuousAt ((i.1).open_source.mem_nhds hb₀i)).comp
          continuous_subtype_val.continuousAt
      exact ((hcc.clm_comp hinv).clm_comp continuousAt_const)
    refine hloc.congr_of_eventuallyEq ?_
    filter_upwards [(continuous_subtype_val.continuousAt (x := b₀)).preimage_mem_nhds
      (((Wsum n ι₀).isOpen_baseSet (i, default)).mem_nhds
        (hb₀ : b₀.1 ∈ (Wsum n ι₀).baseSet (i, default)))] with b hb
    exact chartExpression_invB n ι₀ i i' default j' b.1 hb b.2

/-- **The main theorem**: `TSⁿ ⊕ ε¹` is isomorphic to the trivial bundle with fibre `ℝ^{n+1}`. -/
theorem sphereStableTrivial (n : ℕ) (ι₀ : Type) [Inhabited ι₀] (ι' : Type) [Inhabited ι'] :
    Nonempty (Work.Thom.BundleIso
      (Work.Thom.sumEpsR ι₀ (Work.TangentClasses.tangentSphere n))
      (Work.TangentClasses.RealBundle.trivial
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
        (EuclideanSpace ℝ (Fin (n + 1))) ι')) := by
  obtain ⟨e2⟩ := nonempty_Wsum_trivial n ι₀ ι'
  obtain ⟨e1⟩ := (Classical.choose_spec (Work.Thom.exists_coreMapFibre (Work.Thom.rhoR n)
    (Work.Thom.bundleSum (Zsph n) (eps1 n ι₀)))).2.2.2
  exact ⟨e1.symm.trans e2⟩

end

end Work.Agree
