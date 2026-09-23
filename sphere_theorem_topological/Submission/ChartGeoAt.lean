import Submission.RauchGen
import Submission.JacobiGen
import Submission.FlowJacobi
import Submission.GlobalExp
import Submission.Minimal

/-!
# The Jacobi and variation machinery for chart geodesics with an arbitrary base point

`Submission.RauchGen.lean` develops the whole Rauch comparison chapter for a chart geodesic with
base point the *centre* of the chart.  For the uniform local comparison theorem the base point is
an arbitrary point `q` of a fixed chart, so that the geodesic must be described in the coordinates
of a chart whose centre is *not* its starting point.

This file provides the two missing tools, both stated for the general base point:

* `exists_jacobiSystemOn` — existence of the Jacobi tensor along a chart geodesic on an interval
  `Ioo A B` (base point arbitrary);
* `variationField_eq_jacobiTensor` — the variation field of a two-parameter family of chart
  geodesics is the Jacobi field;
* `mfderiv_GExp_eq_jacobiTensor` — the differential of the *global* exponential map `GExp` at `v`
  in the direction `x` is the value at time `1` of the column `D.Y · x` of the Jacobi tensor.
-/

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal InnerProductSpace
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.ChartConnection
open Submission.ChartCurv
open Submission.Curvature
open Submission.Rauch
open Submission.JacobiTensor
open Submission.RauchGen
open Submission.JacobiGen
open Submission.FlowJacobi
open Submission.Minimal
open Submission.GlobalExp
open Commons.Analysis.ODE

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.ChartGeoAt

noncomputable section

variable [I.Boundaryless]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-! ## Existence of the Jacobi tensor along a chart geodesic with arbitrary base point -/

/-- **Existence of the Jacobi tensor** (arbitrary base point).  On `Icc a b ⊆ Ioo A B` containing
`0` there are `Y, U : ℝ → E →L[ℝ] E` with `Y 0 = 0`, `U 0 = 1` and
`Y' = U - Γ̂ ∘ Y`,  `U' = -Γ̂ ∘ U - Rop ∘ Y`. -/
theorem exists_jacobiSystemOn (htor : cov.torsion = 0)
    {x₀ q : M} {v : E} {u w : ℝ → E} {A B : ℝ}
    (h : HasChartGeodesicOn cov x₀ q v u w A B)
    {a b : ℝ} (hab : a < b) (habt : Icc a b ⊆ Ioo A B) (h0 : (0 : ℝ) ∈ Icc a b) :
    ∃ Y U : ℝ → E →L[ℝ] E, Y 0 = 0 ∧ U 0 = 1 ∧
      (∀ t ∈ Icc a b, HasDerivAt Y (U t - (gammaOp (cov := cov) x₀ u w t).comp (Y t)) t) ∧
      (∀ t ∈ Icc a b, HasDerivAt U (-((gammaOp (cov := cov) x₀ u w t).comp (U t))
        - (curvOp (cov := cov) x₀ u w t).comp (Y t)) t) := by
  have hc : ContinuousOn (jacobiSys (cov := cov) x₀ u w) (Icc a b) := by
    have hG : ContinuousOn (fun t : ℝ => gammaOp (cov := cov) x₀ u w t) (Icc a b) :=
      (Submission.JacobiGen.continuousOn_christoffelLM_along_Ioo (cov := cov) htor
        h.2.2.1 h.2.2.2.1 h.2.2.2.2).mono (fun _ hx => habt hx)
    have hw : ContinuousOn w (Icc a b) :=
      HasDerivAt.continuousOn fun t ht => h.2.2.2.2 t (habt ht)
    have hR : ContinuousOn (fun t : ℝ => curvOp (cov := cov) x₀ u w t) (Icc a b) :=
      (Submission.JacobiTensor.continuousOn_curvOp (cov := cov)
        (HasDerivAt.continuousOn fun t ht => h.2.2.2.1 t (habt ht)) hw
        (fun t ht => h.2.2.1 t (habt ht)))
    have hcomp := (continuous_jacobiSysAux (E := E)).comp_continuousOn (hG.prodMk hR)
    refine hcomp.congr fun t _ => ?_
    rfl
  obtain ⟨Z, hZ0, hZode, -⟩ :=
    Commons.Analysis.ODE.exists_linearODE_solution_Icc
      (E := (E →L[ℝ] E) × (E →L[ℝ] E)) hab hc h0
      ((0 : E →L[ℝ] E), (1 : E →L[ℝ] E))
  refine ⟨fun t => (Z t).1, fun t => (Z t).2, ?_, ?_, ?_, ?_⟩
  · simpa using congrArg Prod.fst hZ0
  · simpa using congrArg Prod.snd hZ0
  · intro t ht
    have h1 : HasDerivAt (fun s : ℝ => (Z s).1)
        ((jacobiSys (cov := cov) x₀ u w t (Z t)).1) t := (hZode t ht).fst
    rw [jacobiSys_apply] at h1
    exact h1
  · intro t ht
    have h1 : HasDerivAt (fun s : ℝ => (Z s).2)
        ((jacobiSys (cov := cov) x₀ u w t (Z t)).2) t := (hZode t ht).snd
    rw [jacobiSys_apply] at h1
    exact h1


/-- **The chain rule for a curve in the model space composed with a map to the manifold.**  If
`γ` agrees with `f ∘ σ` near `t`, the velocity of `γ` is the image of the velocity of `σ` under the
differential of `f`. -/
lemma curveVelocity_eq_mfderiv_comp {f : E → M} {σ σ' : ℝ → E} {γ : ℝ → M} {t : ℝ}
    (hσ : HasDerivAt σ (σ' t) t) (hsm : MDifferentiableAt 𝓘(ℝ, E) I f (σ t))
    (hev : γ =ᶠ[𝓝 t] (fun r => f (σ r))) :
    curveVelocity (I := I) γ t = (mfderiv 𝓘(ℝ, E) I f (σ t)) (σ' t) := by
  have h1 : mfderiv 𝓘(ℝ) I γ t
      = (mfderiv 𝓘(ℝ, E) I f (σ t)).comp (mfderiv 𝓘(ℝ) 𝓘(ℝ, E) σ t) := by
    rw [hev.mfderiv_eq]
    exact mfderiv_comp t hsm (mdifferentiableAt_iff_differentiableAt.mpr hσ.differentiableAt)
  change (mfderiv 𝓘(ℝ) I γ t) (1 : ℝ) = _
  rw [h1]
  change (mfderiv 𝓘(ℝ, E) I f (σ t)) ((mfderiv 𝓘(ℝ) 𝓘(ℝ, E) σ t) (1 : ℝ)) = _
  rw [show (mfderiv 𝓘(ℝ) 𝓘(ℝ, E) σ t) (1 : ℝ) = deriv σ t from by
    rw [mfderiv_eq_fderiv]; rfl, hσ.deriv]

/-! ## The variation field of a family of chart geodesics is the Jacobi field -/

theorem variationField_eq_jacobiTensor (htor : cov.torsion = 0)
    {x₀ q : M} {v x : E} {δ : ℝ} {Φ : ℝ × ℝ → E × E}
    (hδ : 0 < δ)
    (hΦ0 : ∀ t ∈ Ioo (-δ) δ, (Φ (0, t)).1 = (extChartAt I x₀) q)
    (hΦv : ∀ t ∈ Ioo (-δ) δ, (Φ (0, t)).2 = v + t • x)
    (hTGT : ∀ t ∈ Ioo (-δ) δ, ∀ s ∈ Ioo (-2 : ℝ) 2, (Φ (s, t)).1 ∈ (extChartAt I x₀).target)
    (hODE : ∀ t ∈ Ioo (-δ) δ, ∀ s ∈ Ioo (-2 : ℝ) 2,
      HasDerivAt (fun s' : ℝ => Φ (s', t))
        ((Φ (s, t)).2, chartGeodesicVectorField cov x₀ (Φ (s, t))) s)
    (hSM : ∀ s ∈ Ioo (-2 : ℝ) 2, ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => Φ p) (s, 0))
    (hstay : ∀ s ∈ Ioo (-2 : ℝ) 2, (gc Φ) s ∈ (extChartAt I x₀).target)
    (hu0 : ∀ s ∈ Ioo (-2 : ℝ) 2, HasDerivAt (gc Φ) (gv Φ s) s)
    (hw0 : ∀ s ∈ Ioo (-2 : ℝ) 2,
      HasDerivAt (gv Φ) (chartGeodesicVectorField cov x₀ (gc Φ s, gv Φ s)) s)
    {Y U : ℝ → E →L[ℝ] E}
    (hY : ∀ t ∈ Icc (-1 : ℝ) 1,
      HasDerivAt Y (U t - (gammaOp (cov := cov) x₀ (gc Φ) (gv Φ) t).comp (Y t)) t)
    (hU : ∀ t ∈ Icc (-1 : ℝ) 1,
      HasDerivAt U (-((gammaOp (cov := cov) x₀ (gc Φ) (gv Φ) t).comp (U t))
        - (curvOp (cov := cov) x₀ (gc Φ) (gv Φ) t).comp (Y t)) t)
    (hY0 : Y 0 = 0) (hU0 : U 0 = 1) :
    ∀ s ∈ Icc (-1 : ℝ) 1, deriv (fun t : ℝ => (Φ (s, t)).1) 0 = (Y s) x := by
  have h0 : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨by linarith, hδ⟩
  -- a bound on the coefficient on `[-1, 1]`
  have hsub : Icc (-1 : ℝ) 1 ⊆ Ioo (-2 : ℝ) 2 :=
    fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hwcont : ContinuousOn (gv Φ) (Icc (-1 : ℝ) 1) :=
    HasDerivAt.continuousOn fun t ht => hw0 t (hsub ht)
  have hGon : ContinuousOn (fun t : ℝ => gammaOp (cov := cov) x₀ (gc Φ) (gv Φ) t) (Icc (-1 : ℝ) 1) :=
    ((Submission.JacobiGen.continuousOn_christoffelLM_along_Ioo
      (cov := cov) htor (fun s hs => hstay s hs) (fun s hs => hu0 s hs)
      (fun s hs => hw0 s hs)).mono hsub)
  have hRon : ContinuousOn (fun t : ℝ => curvOp (cov := cov) x₀ (gc Φ) (gv Φ) t) (Icc (-1 : ℝ) 1) :=
    continuousOn_curvOp (cov := cov)
      (HasDerivAt.continuousOn fun t ht => hu0 t (hsub ht)) hwcont
      (fun t ht => hstay t (hsub ht))
  obtain ⟨C1, hC1⟩ := isCompact_Icc.exists_bound_of_continuousOn hGon
  obtain ⟨C2, hC2⟩ := isCompact_Icc.exists_bound_of_continuousOn hRon
  have hbound : ∀ t ∈ Icc (-1 : ℝ) 1,
      ‖jacobiSysVec (cov := cov) x₀ (gc Φ) (gv Φ) t‖
        ≤ max 0 (1 + 2 * C1 + C2) := by
    intro t ht
    have h6 : ‖jacobiSysVec (cov := cov) x₀ (gc Φ) (gv Φ) t‖
        ≤ 1 + 2 * ‖gammaOp (cov := cov) x₀ (gc Φ) (gv Φ) t‖
          + ‖curvOp (cov := cov) x₀ (gc Φ) (gv Φ) t‖ := by
      refine _root_.ContinuousLinearMap.opNorm_le_bound _
        (by positivity) fun p => ?_
      obtain ⟨y, z⟩ := p
      exact norm_jacobiSysVec_le (cov := cov) x₀ (gc Φ) (gv Φ) t y z
    have h4 : ‖gammaOp (cov := cov) x₀ (gc Φ) (gv Φ) t‖ ≤ C1 := hC1 t ht
    have h5 : ‖curvOp (cov := cov) x₀ (gc Φ) (gv Φ) t‖ ≤ C2 := hC2 t ht
    refine le_trans h6 (le_trans (by linarith) (le_max_right _ _))
  -- the second-order pair attached to the variation
  set Ufun : ℝ → E := fun r => Zp Φ r
    + chrB cov x₀ ((extChartAt I x₀).symm ((Φ (r, 0)).1)) (Yp Φ r) (gv Φ r) with hUfun
  have hpair2 : ∀ t ∈ Icc (-1 : ℝ) 1,
      HasDerivAt (fun r : ℝ => (Yp Φ r, Ufun r))
        (jacobiSysVec (cov := cov) x₀ (gc Φ) (gv Φ) t (Yp Φ t, Ufun t)) t := by
    intro t ht
    have ht2 : t ∈ Ioo (-2 : ℝ) 2 := hsub ht
    have hsrc : (extChartAt I x₀).symm ((Φ (t, 0)).1) ∈ (chartAt H x₀).source :=
      mem_source_chartCurve (I := I) (x₀ := x₀) (u := fun _ => (Φ (t, 0)).1) (t := 0)
        (hTGT 0 h0 t ht2)
    have hu : HasDerivAt (gc Φ) (gv Φ t) t := Submission.Gauss.hasDerivAt_fst (hODE 0 h0 t ht2)
    have hw : HasDerivAt (gv Φ) (chartGeodesicVectorField cov x₀ (Φ (t, 0))) t :=
      Submission.Gauss.hasDerivAt_snd (hODE 0 h0 t ht2)
    have hGCtarget : gc Φ t ∈ (extChartAt I x₀).target := hstay t ht2
    have hGCtarget_ev : ∀ᶠ r in 𝓝 t, gc Φ r ∈ (extChartAt I x₀).target := by
      filter_upwards [isOpen_Ioo.mem_nhds ht2] with r hr
      exact hstay r hr
    have hy : HasDerivAt (Yp Φ) (Zp Φ t) t :=
      hasDerivAt_variation (cov := cov) hδ hTGT hODE hSM ht2
    have hz := hasDerivAt_variation_vel (cov := cov) hδ hTGT hODE hSM ht2
    have hzval := deriv_chartGeodesicVectorField (cov := cov) hδ hTGT hODE hSM ht2
    have hchr : HasDerivAt
        (fun r : ℝ => chrB cov x₀ ((extChartAt I x₀).symm ((Φ (r, 0)).1)) (Yp Φ r) (gv Φ r))
        (dB cov x₀ ((extChartAt I x₀).symm ((Φ (t, 0)).1)) (gv Φ t) (Yp Φ t) (gv Φ t)
          + chrB cov x₀ ((extChartAt I x₀).symm ((Φ (t, 0)).1)) (Zp Φ t) (gv Φ t)
          + chrB cov x₀ ((extChartAt I x₀).symm ((Φ (t, 0)).1)) (Yp Φ t)
              (chartGeodesicVectorField cov x₀ (Φ (t, 0)))) t :=
      hasDerivAt_chrB_curve (cov := cov) (x₀ := x₀) (u := gc Φ) (a := Yp Φ) (b := gv Φ)
        (v := gv Φ t) (a' := Zp Φ t) (b' := chartGeodesicVectorField cov x₀ (Φ (t, 0)))
        hu hy hw hGCtarget hGCtarget_ev
    have hUderiv : HasDerivAt Ufun
        (deriv (fun r : ℝ => chartGeodesicVectorField cov x₀ (Φ (t, r))) 0
          + (dB cov x₀ ((extChartAt I x₀).symm ((Φ (t, 0)).1)) (gv Φ t) (Yp Φ t) (gv Φ t)
            + chrB cov x₀ ((extChartAt I x₀).symm ((Φ (t, 0)).1)) (Zp Φ t) (gv Φ t)
            + chrB cov x₀ ((extChartAt I x₀).symm ((Φ (t, 0)).1)) (Yp Φ t)
                (chartGeodesicVectorField cov x₀ (Φ (t, 0))))) t := by
      have h := hz.add hchr
      rw [hUfun]
      exact h
    have hgam : gammaOp (cov := cov) x₀ (gc Φ) (gv Φ) t (Yp Φ t)
        = chrB cov x₀ ((extChartAt I x₀).symm ((Φ (t, 0)).1)) (Yp Φ t) (gv Φ t) :=
      gammaOp_apply (cov := cov) (x₀ := x₀) (u := gc Φ) (w := gv Φ) (t := t) hsrc (Yp Φ t)
    have hgamU : gammaOp (cov := cov) x₀ (gc Φ) (gv Φ) t (Ufun t)
        = chrB cov x₀ ((extChartAt I x₀).symm ((Φ (t, 0)).1)) (Ufun t) (gv Φ t) :=
      gammaOp_apply (cov := cov) (x₀ := x₀) (u := gc Φ) (w := gv Φ) (t := t) hsrc (Ufun t)
    have hcurv : curvOp (cov := cov) x₀ (gc Φ) (gv Φ) t (Yp Φ t)
        = chartCurv cov x₀ ((extChartAt I x₀).symm ((Φ (t, 0)).1)) (Yp Φ t) (gv Φ t) :=
      curvOp_apply (cov := cov) (x₀ := x₀) (u := gc Φ) (w := gv Φ) (t := t) hsrc (Yp Φ t)
    have hbase := hy.prodMk hUderiv
    rw [jacobiSysVec_apply]
    refine hbase.congr_deriv ?_
    refine Prod.ext ?_ ?_
    · simp only [hgam, hUfun]
      abel
    · have hgv : chartGeodesicVectorField cov x₀ (Φ (t, 0))
          = - chrB cov x₀ ((extChartAt I x₀).symm ((Φ (t, 0)).1)) (gv Φ t) (gv Φ t) := rfl
      have hid := linearization_identity (cov := cov) htor x₀ hsrc (Yp Φ t) (Zp Φ t) (gv Φ t)
      rw [hzval, hgamU, hcurv, hgv, hUfun, hid]
  -- initial data
  have hYp0 : Yp Φ 0 = 0 := by
    have hev : (fun r : ℝ => (Φ (0, r)).1) =ᶠ[𝓝 (0 : ℝ)] (fun _ => (extChartAt I x₀) q) :=
      Filter.eventually_of_mem (isOpen_Ioo.mem_nhds h0) hΦ0
    rw [Yp_apply, hev.deriv_eq, deriv_const]
  have hZp0 : Zp Φ 0 = x := by
    have hev : (fun r : ℝ => (Φ (0, r)).2) =ᶠ[𝓝 (0 : ℝ)] (fun r => v + r • x) :=
      Filter.eventually_of_mem (isOpen_Ioo.mem_nhds h0) hΦv
    rw [Zp_apply, hev.deriv_eq]
    have hd : HasDerivAt (fun r : ℝ => v + r • x) x 0 := by
      have h1 : HasDerivAt (fun r : ℝ => v + r • x) ((0 : E) + (1 : ℝ) • x) 0 :=
        (hasDerivAt_const (x := (0 : ℝ)) (c := v)).add ((hasDerivAt_id (0 : ℝ)).smul_const x)
      rw [zero_add, one_smul] at h1
      exact h1
    exact hd.deriv
  have hUfun0 : Ufun 0 = x := by
    simp only [hUfun, hYp0, hZp0, map_zero, chrB_zero_fst, add_zero]
  -- the columns of the Jacobi tensor
  have hpair1 : ∀ t ∈ Icc (-1 : ℝ) 1,
      HasDerivAt (fun r : ℝ => ((Y r) x, (U r) x))
        (jacobiSysVec (cov := cov) x₀ (gc Φ) (gv Φ) t ((Y t) x, (U t) x)) t := by
    intro t ht
    have h1 : HasDerivAt (fun r : ℝ => (Y r) x)
        ((U t - (gammaOp (cov := cov) x₀ (gc Φ) (gv Φ) t).comp (Y t)) x + (Y t) 0) t :=
      (hY t ht).clm_apply (hasDerivAt_const (x := t) x)
    have h1' : HasDerivAt (fun r : ℝ => (Y r) x)
        ((U t - (gammaOp (cov := cov) x₀ (gc Φ) (gv Φ) t).comp (Y t)) x) t := by
      simpa using h1
    have h2 : HasDerivAt (fun r : ℝ => (U r) x)
        ((-((gammaOp (cov := cov) x₀ (gc Φ) (gv Φ) t).comp (U t))
          - (curvOp (cov := cov) x₀ (gc Φ) (gv Φ) t).comp (Y t)) x + (U t) 0) t :=
      (hU t ht).clm_apply (hasDerivAt_const (x := t) x)
    have h2' : HasDerivAt (fun r : ℝ => (U r) x)
        ((-((gammaOp (cov := cov) x₀ (gc Φ) (gv Φ) t).comp (U t))
          - (curvOp (cov := cov) x₀ (gc Φ) (gv Φ) t).comp (Y t)) x) t := by
      simpa using h2
    have hbase := h1'.prodMk h2'
    rw [jacobiSysVec_apply]
    refine hbase.congr_deriv ?_
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.neg_apply]
  have hinit : (Yp Φ 0, Ufun 0) = ((Y 0) x, (U 0) x) := by
    have h1 : (Y 0) x = (0 : E) := by rw [hY0]; simp
    have h2 : (U 0) x = x := by rw [hU0]; simp
    rw [hYp0, hUfun0, h1, h2]
  -- uniqueness of the linear ODE on `[-1, 1]`
  have huniq := eqOn_of_hasDerivAt_linearODE (A := jacobiSysVec (cov := cov) x₀ (gc Φ) (gv Φ))
    (M := ⟨max 0 (1 + 2 * C1 + C2), le_max_left _ _⟩) hbound
    (by norm_num : (0 : ℝ) ∈ Icc (-1 : ℝ) 1) hpair2 hpair1 hinit
  intro s hs
  have hfin : (Yp Φ s, Ufun s) = ((Y s) x, (U s) x) := huniq hs
  exact (Prod.ext_iff.mp hfin).1

theorem mfderiv_of_eq_chartFlow (htor : cov.torsion = 0)
    {x₀ q : M} {v x : E} {δ : ℝ} {Φ : ℝ × ℝ → E × E} {f : E → M}
    (hδ : 0 < δ)
    (hΦ0 : ∀ t ∈ Ioo (-δ) δ, (Φ (0, t)).1 = (extChartAt I x₀) q)
    (hΦv : ∀ t ∈ Ioo (-δ) δ, (Φ (0, t)).2 = v + t • x)
    (hTGT : ∀ t ∈ Ioo (-δ) δ, ∀ s ∈ Ioo (-2 : ℝ) 2, (Φ (s, t)).1 ∈ (extChartAt I x₀).target)
    (hODE : ∀ t ∈ Ioo (-δ) δ, ∀ s ∈ Ioo (-2 : ℝ) 2,
      HasDerivAt (fun s' : ℝ => Φ (s', t))
        ((Φ (s, t)).2, chartGeodesicVectorField cov x₀ (Φ (s, t))) s)
    (hSM : ∀ s ∈ Ioo (-2 : ℝ) 2, ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => Φ p) (s, 0))
    (hstay : ∀ s ∈ Ioo (-2 : ℝ) 2, (gc Φ) s ∈ (extChartAt I x₀).target)
    (hu0 : ∀ s ∈ Ioo (-2 : ℝ) 2, HasDerivAt (gc Φ) (gv Φ s) s)
    (hw0 : ∀ s ∈ Ioo (-2 : ℝ) 2,
      HasDerivAt (gv Φ) (chartGeodesicVectorField cov x₀ (gc Φ s, gv Φ s)) s)
    (hEXP : ∀ t ∈ Ioo (-δ) δ, f (v + t • x) = (extChartAt I x₀).symm ((Φ (1, t)).1))
    (hf : MDifferentiableAt 𝓘(ℝ, E) I f v)
    {Y U : ℝ → E →L[ℝ] E}
    (hY : ∀ t ∈ Icc (-1 : ℝ) 1,
      HasDerivAt Y (U t - (gammaOp (cov := cov) x₀ (gc Φ) (gv Φ) t).comp (Y t)) t)
    (hU : ∀ t ∈ Icc (-1 : ℝ) 1,
      HasDerivAt U (-((gammaOp (cov := cov) x₀ (gc Φ) (gv Φ) t).comp (U t))
        - (curvOp (cov := cov) x₀ (gc Φ) (gv Φ) t).comp (Y t)) t)
    (hY0 : Y 0 = 0) (hU0 : U 0 = 1) :
    (mfderiv 𝓘(ℝ, E) I f v) x = frameVector (I := I) x₀ (f v) ((Y 1) x) := by
  have h0 : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨by linarith, hδ⟩
  have h1 : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hs1 : (1 : ℝ) ∈ Ioo (-2 : ℝ) 2 := ⟨by norm_num, by norm_num⟩
  have hYval : deriv (fun t : ℝ => (Φ (1, t)).1) 0 = (Y 1) x :=
    variationField_eq_jacobiTensor (cov := cov) htor hδ hΦ0 hΦv hTGT hODE hSM hstay hu0 hw0
      hY hU hY0 hU0 1 h1
  -- the curve agrees with the chart curve near `0`
  have hγeq : (fun r : ℝ => f (v + r • x))
      =ᶠ[𝓝 (0 : ℝ)] (fun r => (extChartAt I x₀).symm ((Φ (1, r)).1)) := by
    filter_upwards [isOpen_Ioo.mem_nhds h0] with r hr
    have hh := hEXP r hr
    simpa using hh
  -- the derivative of the straight curve in the tangent space
  have hσ : HasDerivAt (fun r : ℝ => v + r • x) x 0 := by
    have h2 : HasDerivAt (fun r : ℝ => v + r • x) ((0 : E) + (1 : ℝ) • x) 0 :=
      (hasDerivAt_const (x := (0 : ℝ)) (c := v)).add ((hasDerivAt_id (0 : ℝ)).smul_const x)
    rw [zero_add, one_smul] at h2
    exact h2
  have hf' : MDifferentiableAt 𝓘(ℝ, E) I f (v + (0 : ℝ) • x) := by simpa using hf
  have hvel : curveVelocity (I := I) (fun r : ℝ => f (v + r • x)) 0
      = (mfderiv 𝓘(ℝ, E) I f v) x := by
    have h := curveVelocity_eq_mfderiv_comp (f := f)
      (σ := fun r : ℝ => v + r • x) (σ' := fun _ => x)
      (γ := fun r => f (v + r • x))
      (t := 0) hσ hf' (Filter.EventuallyEq.refl _ _)
    refine h.trans ?_
    rw [zero_smul, add_zero]
  -- the chart curve
  have htgt : (Φ (1, 0)).1 ∈ (extChartAt I x₀).target := hTGT 0 h0 1 hs1
  have hstay1 : ∀ᶠ r in 𝓝 (0 : ℝ), (Φ (1, r)).1 ∈ (extChartAt I x₀).target :=
    Filter.eventually_of_mem (isOpen_Ioo.mem_nhds h0) (fun r hr => hTGT r hr 1 hs1)
  have hdiff : DifferentiableAt ℝ (fun r : ℝ => (Φ (1, r)).1) 0 := by
    have hc : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => (Φ p).1) (1, 0) :=
      (ContinuousLinearMap.fst ℝ E E).contDiff.contDiffAt.comp (1, 0)
        ((hSM 1 hs1).of_le (by decide))
    have hcomp : ContDiffAt ℝ ∞ (fun r : ℝ => (Φ (1, r)).1) 0 :=
      hc.comp 0 (contDiffAt_const.prodMk contDiffAt_id)
    exact hcomp.differentiableAt (by norm_num)
  have hu : HasDerivAt (fun r : ℝ => (Φ (1, r)).1) ((Y 1) x) 0 := by
    have h := hdiff.hasDerivAt
    rw [hYval] at h
    exact h
  have hchartvel := curveVelocity_chartCurve (I := I) (x₀ := x₀)
    (u := fun r : ℝ => (Φ (1, r)).1) (v := (Y 1) x) (t := 0) hu htgt hstay1
  have hpoint : f v = (extChartAt I x₀).symm ((Φ (1, 0)).1) := by
    have hh := hEXP 0 h0
    simpa using hh
  calc (mfderiv 𝓘(ℝ, E) I f v) x
      = curveVelocity (I := I) (fun r : ℝ => f (v + r • x)) 0 := hvel.symm
    _ = curveVelocity (I := I) (fun r : ℝ => (extChartAt I x₀).symm ((Φ (1, r)).1)) 0 :=
        Submission.GeodesicExtend.curveVelocity_congr_of_eventuallyEq (I := I) hγeq
    _ = frameVector (I := I) x₀ ((extChartAt I x₀).symm ((Φ (1, 0)).1)) ((Y 1) x) := hchartvel
    _ = frameVector (I := I) x₀ (f v) ((Y 1) x) := by rw [hpoint]

end

end Submission.ChartGeoAt
