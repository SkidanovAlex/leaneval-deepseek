import Submission.GExpJoint
import Submission.SecondVarGeo
import Submission.GeoChartCurve
import Submission.GExpSmooth
import Submission.Commons.Analysis.Calculus.deriv_deriv_swap

/-!
# The intrinsic variation by geodesics, in one chart: the per-chart jet data

The second-variation chapter `Submission.SecondVarGeo.energy_second_deriv_chart` computes
`E''(0) = -2 ∫ indexIntegrand` for a **coordinate** family `ψ : ℝ → ℝ → E` whose `σ`-curves are
geodesics, given the six jets `ψ, w = ∂_tψ, v = ∂_σψ, a = ∂_σ²ψ, e = ∂_σ∂_tψ, ea = ∂_σ²∂_tψ` and the
two equations

* `hgeo  : a 0 t = -Γ(v 0 t, v 0 t)`  (the `σ`-curves are geodesics), and
* `hgeo' : ea 0 t = -(∂_tΓ)(v 0 t, v 0 t) + …`  (its `t`-derivative).

This file **produces** that data for the intrinsic family

`Φ(σ,t) = GExp (γ t) (σ • frameVector z₀ (γ t) (u t))`,

i.e. for the chart-coordinate family `fam D x u σ t = Hfun D (x t, σ • u t)` where `x` is the
coordinate curve of `γ` in the chart `z₀` and `u` the coordinate curve of the variation field.
All the jets are defined by `deriv` of the two sections of `fam`, so the `HasDerivAt` hypotheses of
`energy_second_deriv_chart` hold by construction; the only analytic input is

* the joint smoothness of `fam` (`ChartFlowData.hjoint`), and
* the **Clairaut–Schwarz theorem** for `ℝ × ℝ → E`
  (`Commons.Analysis.Calculus.deriv_deriv_swap`), which turns `∂_t∂_σ fam` into `∂_σ∂_t fam` (and
  the same for the `σ`-partial), i.e. `∂_t v = e` and `∂_t a = ea`.

The geodesic equation `hgeo` is `Submission.GeoChartCurve.chartGeodesicEquation_GExp` (valid in every
chart containing the ray, at every time), transported to `fam` through
`GExp_eq_symm_Hfun`; the degenerate direction `u t = 0` is handled separately (the family is then
constant in `σ`).  The `t`-derivative is obtained by differentiating the identity `hgeo` in `t` and
using the two Clairaut instances.

The final theorem is `energy_second_deriv_fam`: the second **and** first variation of the energy
`energyFam D x u L` of the family over `[0,L]`, i.e. the per-chart data needed for the global
`σ ≤ κ` (no conjugate point inside the segment domain).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.GExpFlow
open Submission.ChartFlowHom
open Submission.ChartBounds
open Submission.ChartConnection
open Submission.UniformInj
open Submission.GExpJoint
open Submission.ChartCurv
open Submission.GeoChartCurve
open Submission.IndexForm
open Submission.SecondVarGeo
open Submission.BonnetMyers
open Submission.ChartCurvCont

namespace Submission.IntrinsicVariation

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]
variable {z₀ : M} {Z : Set M}
variable {η : ℝ}

/-- The chart-coordinate model of the intrinsic variation
`(σ,t) ↦ GExp (γ t) (σ • frameVector z₀ (γ t) (u t))`. -/
noncomputable def fam (D : ChartFlowData (cov := cov) (I := I) z₀ Z) (x u : ℝ → E)
    (σ t : ℝ) : E :=
  Hfun D (x t, σ • u t)

lemma fam_apply (D : ChartFlowData (cov := cov) (I := I) z₀ Z) (x u : ℝ → E) (σ t : ℝ) :
    fam (cov := cov) D x u σ t = Hfun D (x t, σ • u t) := rfl

/-- Joint smoothness of the chart-coordinate family on a rectangle. -/
theorem contDiffOn_fam (D : ChartFlowData (cov := cov) (I := I) z₀ Z)
    {x u : ℝ → E} {δ L : ℝ}
    (hx : ContDiffOn ℝ ∞ x (Ioo (-η) (L + η)))
    (hu : ContDiffOn ℝ ∞ u (Ioo (-η) (L + η)))
    (hph : ∀ σ ∈ Icc (-δ) δ, ∀ t ∈ Icc (-η) (L + η),
      (x t, flowScale D • (σ • u t)) ∈ chartData (I := I) z₀ Z) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => fam (cov := cov) D x u p.1 p.2)
      (Ioo (-δ) δ ×ˢ Ioo (-η) (L + η)) := by
  intro p hp
  have hsub : Ioo (-η) (L + η) ∈ 𝓝 p.2 := isOpen_Ioo.mem_nhds hp.2
  have hK : (x p.2, flowScale D • (p.1 • u p.2)) ∈ chartData (I := I) z₀ Z :=
    hph p.1 ⟨hp.1.1.le, hp.1.2.le⟩ p.2 ⟨hp.2.1.le, hp.2.2.le⟩
  have ht : |(flowScale D)⁻¹| < D.ρ := by
    rw [inv_flowScale, abs_of_pos (div_pos D.hρ two_pos)]
    linarith [D.hρ]
  have hpair : ContDiffAt ℝ ∞
      (fun q : ℝ × ℝ => (x q.2, flowScale D • (q.1 • u q.2))) p :=
    ((hx.contDiffAt hsub).comp p contDiffAt_snd).prodMk
      (contDiffAt_const.smul (contDiffAt_fst.smul
        ((hu.contDiffAt hsub).comp p contDiffAt_snd)))
  have hinner : ContDiffAt ℝ ∞
      (fun q : ℝ × ℝ => ((x q.2, flowScale D • (q.1 • u q.2)), (flowScale D)⁻¹)) p :=
    hpair.prodMk contDiffAt_const
  have hjoint := (D.hjoint (x p.2, flowScale D • (p.1 • u p.2)) hK (flowScale D)⁻¹ ht).comp p hinner
  have hcd : ContDiffAt ℝ ∞
      (fun q : ℝ × ℝ => (D.α (x q.2, flowScale D • (q.1 • u q.2)) (flowScale D)⁻¹).1) p :=
    hjoint.fst
  have hgoal : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ => fam (cov := cov) D x u q.1 q.2) p := by
    change ContDiffAt ℝ ∞
      (fun q : ℝ × ℝ => (D.α (x q.2, flowScale D • (q.1 • u q.2)) (flowScale D)⁻¹).1) p
    exact hcd
  exact hgoal.contDiffWithinAt


/-- The first partial derivative of a `C^∞` function `ℝ × ℝ → E` is `C^∞`. -/
theorem contDiffOn_deriv_section_fst {F : ℝ × ℝ → E} {R : Set (ℝ × ℝ)} (hR : IsOpen R)
    (hF : ContDiffOn ℝ ∞ F R) :
    ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => deriv (fun s : ℝ => F (s, q.2)) q.1) R := by
  have hfd : ContDiffOn ℝ ∞ (fderiv ℝ F) R := hF.fderiv_of_isOpen hR (le_of_eq (by simp))
  have happ : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => (fderiv ℝ F q) ((1 : ℝ), (0 : ℝ))) R :=
    hfd.clm_apply contDiffOn_const
  refine happ.congr ?_
  intro q hq
  exact Commons.Analysis.Calculus.deriv_slice_fst
    ((hF.differentiableOn (by simp)).differentiableAt (hR.mem_nhds hq))

/-- The second partial derivative of a `C^∞` function `ℝ × ℝ → E` is `C^∞`. -/
theorem contDiffOn_deriv_section_snd {F : ℝ × ℝ → E} {R : Set (ℝ × ℝ)} (hR : IsOpen R)
    (hF : ContDiffOn ℝ ∞ F R) :
    ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => deriv (fun r : ℝ => F (q.1, r)) q.2) R := by
  have hfd : ContDiffOn ℝ ∞ (fderiv ℝ F) R := hF.fderiv_of_isOpen hR (le_of_eq (by simp))
  have happ : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => (fderiv ℝ F q) ((0 : ℝ), (1 : ℝ))) R :=
    hfd.clm_apply contDiffOn_const
  refine happ.congr ?_
  intro q hq
  exact Commons.Analysis.Calculus.deriv_slice_snd
    ((hF.differentiableOn (by simp)).differentiableAt (hR.mem_nhds hq))


/-- `fam` as a function of the pair `(σ,t)`. -/
noncomputable def Fam (D : ChartFlowData (cov := cov) (I := I) z₀ Z) (x u : ℝ → E) :
    ℝ × ℝ → E :=
  fun q => fam (cov := cov) D x u q.1 q.2

lemma Fam_apply (D : ChartFlowData (cov := cov) (I := I) z₀ Z) (x u : ℝ → E)
    (σ t : ℝ) : Fam (cov := cov) D x u (σ, t) = fam (cov := cov) D x u σ t := rfl

/-- The `t`-partial of the chart-coordinate family. -/
noncomputable def psiW (D : ChartFlowData (cov := cov) (I := I) z₀ Z) (x u : ℝ → E)
    (σ t : ℝ) : E :=
  deriv (fun t' : ℝ => fam (cov := cov) D x u σ t') t

/-- The `σ`-partial of the chart-coordinate family. -/
noncomputable def psiV (D : ChartFlowData (cov := cov) (I := I) z₀ Z) (x u : ℝ → E)
    (σ t : ℝ) : E :=
  deriv (fun σ' : ℝ => fam (cov := cov) D x u σ' t) σ

/-- The second `σ`-partial of the chart-coordinate family. -/
noncomputable def psiA (D : ChartFlowData (cov := cov) (I := I) z₀ Z) (x u : ℝ → E)
    (σ t : ℝ) : E :=
  deriv (fun σ' : ℝ => psiV (cov := cov) D x u σ' t) σ

/-- The `t`-derivative of the `σ`-partial (the mixed partial `∂_σ∂_t`). -/
noncomputable def psiE (D : ChartFlowData (cov := cov) (I := I) z₀ Z) (x u : ℝ → E)
    (σ t : ℝ) : E :=
  deriv (fun σ' : ℝ => psiW (cov := cov) D x u σ' t) σ

/-- The `σ`-derivative of `psiE` (the third partial `∂_σ²∂_t`). -/
noncomputable def psiEA (D : ChartFlowData (cov := cov) (I := I) z₀ Z) (x u : ℝ → E)
    (σ t : ℝ) : E :=
  deriv (fun σ' : ℝ => psiE (cov := cov) D x u σ' t) σ

section Smooth


lemma contDiffOn_psiV (D : ChartFlowData (cov := cov) (I := I) z₀ Z) {x u : ℝ → E}
    {R : Set (ℝ × ℝ)} (hR : IsOpen R) (hF : ContDiffOn ℝ ∞ (Fam (cov := cov) D x u) R) :
    ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => psiV (cov := cov) D x u q.1 q.2) R :=
  contDiffOn_deriv_section_fst hR hF

lemma contDiffOn_psiW (D : ChartFlowData (cov := cov) (I := I) z₀ Z) {x u : ℝ → E}
    {R : Set (ℝ × ℝ)} (hR : IsOpen R) (hF : ContDiffOn ℝ ∞ (Fam (cov := cov) D x u) R) :
    ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => psiW (cov := cov) D x u q.1 q.2) R :=
  contDiffOn_deriv_section_snd hR hF

lemma contDiffOn_psiA (D : ChartFlowData (cov := cov) (I := I) z₀ Z) {x u : ℝ → E}
    {R : Set (ℝ × ℝ)} (hR : IsOpen R) (hF : ContDiffOn ℝ ∞ (Fam (cov := cov) D x u) R) :
    ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => psiA (cov := cov) D x u q.1 q.2) R :=
  contDiffOn_deriv_section_fst hR (contDiffOn_psiV (cov := cov) D hR hF)

lemma contDiffOn_psiE (D : ChartFlowData (cov := cov) (I := I) z₀ Z) {x u : ℝ → E}
    {R : Set (ℝ × ℝ)} (hR : IsOpen R) (hF : ContDiffOn ℝ ∞ (Fam (cov := cov) D x u) R) :
    ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => psiE (cov := cov) D x u q.1 q.2) R :=
  contDiffOn_deriv_section_fst hR (contDiffOn_psiW (cov := cov) D hR hF)

lemma contDiffOn_psiEA (D : ChartFlowData (cov := cov) (I := I) z₀ Z) {x u : ℝ → E}
    {R : Set (ℝ × ℝ)} (hR : IsOpen R) (hF : ContDiffOn ℝ ∞ (Fam (cov := cov) D x u) R) :
    ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => psiEA (cov := cov) D x u q.1 q.2) R :=
  contDiffOn_deriv_section_fst hR (contDiffOn_psiE (cov := cov) D hR hF)

end Smooth

section HasDeriv


lemma hasDerivAt_fam_snd (D : ChartFlowData (cov := cov) (I := I) z₀ Z) {x u : ℝ → E}
    {σ t : ℝ} {R : Set (ℝ × ℝ)} (hR : IsOpen R) (hF : ContDiffOn ℝ ∞ (Fam (cov := cov) D x u) R) (h : (σ, t) ∈ R) :
    HasDerivAt (fun t' : ℝ => fam (cov := cov) D x u σ t') (psiW (cov := cov) D x u σ t) t := by
  have hsec : ContDiffAt ℝ ∞ (fun t' : ℝ => fam (cov := cov) D x u σ t') t := by
    have hc := (hF.contDiffAt (hR.mem_nhds h)).comp t
      (contDiffAt_const.prodMk (contDiffAt_id (x := t)))
    simpa only [Function.comp_def, Fam_apply, id_eq] using hc
  exact (hsec.differentiableAt (by simp)).hasDerivAt

lemma hasDerivAt_fam_fst (D : ChartFlowData (cov := cov) (I := I) z₀ Z) {x u : ℝ → E}
    {σ t : ℝ} {R : Set (ℝ × ℝ)} (hR : IsOpen R) (hF : ContDiffOn ℝ ∞ (Fam (cov := cov) D x u) R) (h : (σ, t) ∈ R) :
    HasDerivAt (fun σ' : ℝ => fam (cov := cov) D x u σ' t) (psiV (cov := cov) D x u σ t) σ := by
  have hsec : ContDiffAt ℝ ∞ (fun σ' : ℝ => fam (cov := cov) D x u σ' t) σ := by
    have hc := (hF.contDiffAt (hR.mem_nhds h)).comp σ
      ((contDiffAt_id (x := σ)).prodMk (contDiffAt_const (c := t)))
    simpa only [Function.comp_def, Fam_apply, id_eq] using hc
  exact (hsec.differentiableAt (by simp)).hasDerivAt

lemma hasDerivAt_psiV_fst (D : ChartFlowData (cov := cov) (I := I) z₀ Z) {x u : ℝ → E}
    {σ t : ℝ} {R : Set (ℝ × ℝ)} (hR : IsOpen R) (hF : ContDiffOn ℝ ∞ (Fam (cov := cov) D x u) R) (h : (σ, t) ∈ R) :
    HasDerivAt (fun σ' : ℝ => psiV (cov := cov) D x u σ' t) (psiA (cov := cov) D x u σ t) σ := by
  have hsec : ContDiffAt ℝ ∞ (fun σ' : ℝ => psiV (cov := cov) D x u σ' t) σ := by
    have hc := ((contDiffOn_psiV (cov := cov) D hR hF).contDiffAt (hR.mem_nhds h)).comp σ
      ((contDiffAt_id (x := σ)).prodMk (contDiffAt_const (c := t)))
    simpa only [Function.comp_def, id_eq] using hc
  exact (hsec.differentiableAt (by simp)).hasDerivAt

lemma hasDerivAt_psiW_fst (D : ChartFlowData (cov := cov) (I := I) z₀ Z) {x u : ℝ → E}
    {σ t : ℝ} {R : Set (ℝ × ℝ)} (hR : IsOpen R) (hF : ContDiffOn ℝ ∞ (Fam (cov := cov) D x u) R) (h : (σ, t) ∈ R) :
    HasDerivAt (fun σ' : ℝ => psiW (cov := cov) D x u σ' t) (psiE (cov := cov) D x u σ t) σ := by
  have hsec : ContDiffAt ℝ ∞ (fun σ' : ℝ => psiW (cov := cov) D x u σ' t) σ := by
    have hc := ((contDiffOn_psiW (cov := cov) D hR hF).contDiffAt (hR.mem_nhds h)).comp σ
      ((contDiffAt_id (x := σ)).prodMk (contDiffAt_const (c := t)))
    simpa only [Function.comp_def, id_eq] using hc
  exact (hsec.differentiableAt (by simp)).hasDerivAt

lemma hasDerivAt_psiE_fst (D : ChartFlowData (cov := cov) (I := I) z₀ Z) {x u : ℝ → E}
    {σ t : ℝ} {R : Set (ℝ × ℝ)} (hR : IsOpen R) (hF : ContDiffOn ℝ ∞ (Fam (cov := cov) D x u) R) (h : (σ, t) ∈ R) :
    HasDerivAt (fun σ' : ℝ => psiE (cov := cov) D x u σ' t) (psiEA (cov := cov) D x u σ t) σ := by
  have hsec : ContDiffAt ℝ ∞ (fun σ' : ℝ => psiE (cov := cov) D x u σ' t) σ := by
    have hc := ((contDiffOn_psiE (cov := cov) D hR hF).contDiffAt (hR.mem_nhds h)).comp σ
      ((contDiffAt_id (x := σ)).prodMk (contDiffAt_const (c := t)))
    simpa only [Function.comp_def, id_eq] using hc
  exact (hsec.differentiableAt (by simp)).hasDerivAt

end HasDeriv


/-- `2 ≤ ∞` in the smoothness lattice (the numeral coercions do not simplify on their own). -/
lemma two_le_infty : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
  show ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
  exact WithTop.coe_le_coe.mpr le_top

/-- The chart coordinates of a curve. -/
noncomputable def chartCoord (z₀ : M) (γ : ℝ → M) : ℝ → E :=
  fun t => (extChartAt I z₀) (γ t)

section Geo

variable {γ : ℝ → M} {u : ℝ → E} {L δ : ℝ}

/-- **The `σ`-geodesic equation of the chart-coordinate family at `σ = 0`.** -/
theorem psiA_zero_eq (hmet : IsMetricCompatible cov)
    (D : ChartFlowData (cov := cov) (I := I) z₀ Z) {hδ : 0 < δ}
    (hγsrc : ∀ t ∈ Icc (-η) (L + η), γ t ∈ (chartAt H z₀).source)
    (hγZ : ∀ t ∈ Icc (-η) (L + η), γ t ∈ Z)
    (htgt : ∀ σ ∈ Ioo (-δ) δ, ∀ t ∈ Ioo (-η) (L + η),
      fam (cov := cov) D (chartCoord (I := I) z₀ γ) u σ t ∈ (extChartAt I z₀).target)
    (hphase : ∀ σ ∈ Ioo (-δ) δ, ∀ t ∈ Ioo (-η) (L + η),
      (chartCoord (I := I) z₀ γ t, flowScale D • (σ • u t)) ∈ D.O) :
    ∀ t ∈ Ioo (-η) (L + η),
      psiA (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t
        = - chrB cov z₀ ((extChartAt I z₀).symm
            (fam (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t))
            (psiV (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t)
            (psiV (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t) := by
  intro t ht
  have ht' : t ∈ Ioo (-η) (L + η) := ht
  by_cases hu : u t = 0
  · -- degenerate direction: the family is constant in `σ`
    have hconst : ∀ σ : ℝ,
        fam (cov := cov) D (chartCoord (I := I) z₀ γ) u σ t
          = fam (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t := by
      intro σ
      show Hfun D (chartCoord (I := I) z₀ γ t, σ • u t)
        = Hfun D (chartCoord (I := I) z₀ γ t, (0 : ℝ) • u t)
      rw [hu]
      simp
    have hV0 : psiV (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t = 0 := by
      show deriv (fun σ' : ℝ => fam (cov := cov) D (chartCoord (I := I) z₀ γ) u σ' t) 0 = 0
      rw [show (fun σ' : ℝ => fam (cov := cov) D (chartCoord (I := I) z₀ γ) u σ' t)
          = fun _ => fam (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t from
        funext hconst, deriv_const']
    have hA0 : psiA (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t = 0 := by
      show deriv (fun σ' : ℝ => psiV (cov := cov) D (chartCoord (I := I) z₀ γ) u σ' t) 0 = 0
      rw [show (fun σ' : ℝ => psiV (cov := cov) D (chartCoord (I := I) z₀ γ) u σ' t)
          = fun _ => (0 : E) from by
        funext σ'
        show deriv (fun σ'' : ℝ => fam (cov := cov) D (chartCoord (I := I) z₀ γ) u σ'' t) σ'
          = 0
        rw [show (fun σ'' : ℝ => fam (cov := cov) D (chartCoord (I := I) z₀ γ) u σ'' t)
            = fun _ => fam (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t from
          funext hconst, deriv_const'], deriv_const']
    rw [hA0, hV0, chrB_zero_fst, neg_zero]
  · have hγsrc_t : γ t ∈ (chartAt H z₀).source := hγsrc t ⟨ht'.1.le, ht'.2.le⟩
    have hγsrcExt : γ t ∈ (extChartAt I z₀).source := by
      rwa [extChartAt_source]
    have hξ : frameVector (I := I) z₀ (γ t) (u t) ≠ 0 := by
      intro h
      exact hu (Submission.GExpSmooth.frameVector_eq_zero (I := I) hγsrcExt h)
    have hsrc0 : GExp (cov := cov) hmet (γ t) ((0 : ℝ) • frameVector (I := I) z₀ (γ t) (u t))
        ∈ (chartAt H z₀).source := by
      rw [zero_smul, Submission.GlobalExp.GExp_zero]
      exact hγsrc_t
    have hgeo := Submission.GeoChartCurve.chartGeodesicEquation_GExp (cov := cov) hmet
      (x₀ := z₀) (p := γ t) (ξ := frameVector (I := I) z₀ (γ t) (u t)) hξ 0 hsrc0
    -- the chart-coordinate family agrees with the ray on a neighbourhood of `0`
    have hray : ∀ σ ∈ Ioo (-δ) δ,
        (extChartAt I z₀) (GExp (cov := cov) hmet (γ t)
            (σ • frameVector (I := I) z₀ (γ t) (u t)))
          = fam (cov := cov) D (chartCoord (I := I) z₀ γ) u σ t := by
      intro σ hσ
      have hph : (chartCoord (I := I) z₀ γ t, flowScale D • (σ • u t)) ∈ D.O := hphase σ hσ t ht'
      have hrep : σ • frameVector (I := I) z₀ (γ t) (u t)
          = frameVector (I := I) z₀ (γ t) (σ • u t) := by
        rw [Submission.GExpSmooth.frameVector_smul']
      rw [hrep]
      rw [GExp_eq_symm_Hfun (cov := cov) hmet D (hγZ t ⟨ht'.1.le, ht'.2.le⟩) hγsrcExt hph]
      exact (extChartAt I z₀).right_inv (htgt σ hσ t ht')
    have hevRay : (fun σ' : ℝ => (extChartAt I z₀) (GExp (cov := cov) hmet (γ t)
          (σ' • frameVector (I := I) z₀ (γ t) (u t))))
        =ᶠ[𝓝 (0 : ℝ)] (fun σ' : ℝ => fam (cov := cov) D (chartCoord (I := I) z₀ γ) u σ' t) :=
      Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds ⟨by linarith, hδ⟩) hray
    have h1 : deriv (fun σ' : ℝ => (extChartAt I z₀) (GExp (cov := cov) hmet (γ t)
          (σ' • frameVector (I := I) z₀ (γ t) (u t)))) 0
        = deriv (fun σ' : ℝ => fam (cov := cov) D (chartCoord (I := I) z₀ γ) u σ' t) 0 :=
      hevRay.deriv_eq
    have hderFun : deriv (fun σ' : ℝ => (extChartAt I z₀) (GExp (cov := cov) hmet (γ t)
          (σ' • frameVector (I := I) z₀ (γ t) (u t))))
        =ᶠ[𝓝 (0 : ℝ)]
        deriv (fun σ' : ℝ => fam (cov := cov) D (chartCoord (I := I) z₀ γ) u σ' t) :=
      hevRay.deriv
    have h2 : deriv (deriv (fun σ' : ℝ => (extChartAt I z₀) (GExp (cov := cov) hmet (γ t)
          (σ' • frameVector (I := I) z₀ (γ t) (u t))))) 0
        = deriv (deriv (fun σ' : ℝ =>
            fam (cov := cov) D (chartCoord (I := I) z₀ γ) u σ' t)) 0 :=
      hderFun.deriv_eq
    have hpos : (extChartAt I z₀).symm ((extChartAt I z₀) (GExp (cov := cov) hmet (γ t)
          ((0 : ℝ) • frameVector (I := I) z₀ (γ t) (u t))))
        = (extChartAt I z₀).symm (fam (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t) := by
      rw [hray 0 ⟨by linarith, hδ⟩]
    rw [h2, h1, hpos] at hgeo
    simpa only [psiA, psiV] using eq_neg_of_add_eq_zero_left hgeo

end Geo


/-- The working rectangle of the intrinsic variation. -/
def Rect (η δ L : ℝ) : Set (ℝ × ℝ) := Ioo (-δ) δ ×ˢ Ioo (-η) (L + η)

lemma isOpen_Rect (η δ L : ℝ) : IsOpen (Rect η δ L) := isOpen_Ioo.prod isOpen_Ioo

section Clairaut

/-- **Clairaut on the family**: `∂_t(∂_σ fam)|_σ = ∂_σ∂_t fam|_σ`. -/
lemma deriv_psiV_eq_psiE (D : ChartFlowData (cov := cov) (I := I) z₀ Z) (x u : ℝ → E)
    {R : Set (ℝ × ℝ)} (hR : IsOpen R) (hF : ContDiffOn ℝ ∞ (Fam (cov := cov) D x u) R)
    {σ t : ℝ} (h : (σ, t) ∈ R) :
    deriv (fun t' : ℝ => psiV (cov := cov) D x u σ t') t = psiE (cov := cov) D x u σ t := by
  have hca : ContDiffAt ℝ 2 (Fam (cov := cov) D x u) (σ, t) :=
    ((hF.contDiffAt (hR.mem_nhds h))).of_le two_le_infty
  have := Commons.Analysis.Calculus.deriv_deriv_swap hca
  simpa only [psiV, psiE, psiW, Fam_apply] using this

/-- **Clairaut on the `σ`-partial**: `∂_t(∂_σ² fam)|_σ = ∂_σ²∂_t fam|_σ`. -/
lemma deriv_psiA_eq_psiEA (D : ChartFlowData (cov := cov) (I := I) z₀ Z) (x u : ℝ → E)
    {R : Set (ℝ × ℝ)} (hR : IsOpen R) (hF : ContDiffOn ℝ ∞ (Fam (cov := cov) D x u) R)
    {σ t : ℝ} (h : (σ, t) ∈ R) :
    deriv (fun t' : ℝ => psiA (cov := cov) D x u σ t') t = psiEA (cov := cov) D x u σ t := by
  have hv : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => psiV (cov := cov) D x u q.1 q.2) R :=
    contDiffOn_psiV (cov := cov) D hR hF
  have hca : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => psiV (cov := cov) D x u q.1 q.2) (σ, t) :=
    ((hv.contDiffAt (hR.mem_nhds h))).of_le two_le_infty
  have hswap := Commons.Analysis.Calculus.deriv_deriv_swap hca
  -- `s ↦ ∂_t psiV s t` agrees near `σ` with `s ↦ psiE s t`
  have hopen : {s : ℝ | (s, t) ∈ R} ∈ 𝓝 σ := by
    have hcont : Continuous (fun s : ℝ => (s, t)) := continuous_id.prodMk continuous_const
    exact hcont.continuousAt.preimage_mem_nhds (hR.mem_nhds h)
  have hev : (fun s : ℝ => deriv (fun t' : ℝ => psiV (cov := cov) D x u s t') t)
      =ᶠ[𝓝 σ] (fun s : ℝ => psiE (cov := cov) D x u s t) :=
    Filter.eventually_of_mem hopen (fun s hs => deriv_psiV_eq_psiE (cov := cov) D x u hR hF hs)
  have hder := Filter.EventuallyEq.deriv_eq hev
  have hgoal : deriv (fun s : ℝ => deriv (fun t' : ℝ => psiV (cov := cov) D x u s t') t) σ
      = deriv (fun s : ℝ => psiE (cov := cov) D x u s t) σ := hder
  simpa only [psiA, psiEA] using hswap.trans hgoal

end Clairaut

section Eta

variable {γ : ℝ → M} {u : ℝ → E} {L δ : ℝ}

/-- **The `t`-derivative of the `σ`-geodesic equation.** -/
theorem psiEA_zero_eq (hmet : IsMetricCompatible cov)
    (D : ChartFlowData (cov := cov) (I := I) z₀ Z) {hδ : 0 < δ} (hη : 0 < η)
    (hγsrc : ∀ t ∈ Icc (-η) (L + η), γ t ∈ (chartAt H z₀).source)
    (hγZ : ∀ t ∈ Icc (-η) (L + η), γ t ∈ Z)
    (htgt : ∀ σ ∈ Ioo (-δ) δ, ∀ t ∈ Ioo (-η) (L + η),
      fam (cov := cov) D (chartCoord (I := I) z₀ γ) u σ t ∈ (extChartAt I z₀).target)
    (hphase : ∀ σ ∈ Ioo (-δ) δ, ∀ t ∈ Ioo (-η) (L + η),
      (chartCoord (I := I) z₀ γ t, flowScale D • (σ • u t)) ∈ D.O)
    (hF : ContDiffOn ℝ ∞ (Fam (cov := cov) D (chartCoord (I := I) z₀ γ) u) (Rect η δ L))
    (hgeo : ∀ t ∈ Ioo (-η) (L + η),
      psiA (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t
        = - chrB cov z₀ ((extChartAt I z₀).symm
            (fam (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t))
            (psiV (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t)
            (psiV (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t)) :
    ∀ t ∈ Icc (0 : ℝ) L,
      psiEA (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t
        = - (dB cov z₀ ((extChartAt I z₀).symm
              (fam (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t))
              (psiW (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t)
              (psiV (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t)
              (psiV (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t)
            + chrB cov z₀ ((extChartAt I z₀).symm
                (fam (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t))
              (psiE (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t)
              (psiV (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t)
            + chrB cov z₀ ((extChartAt I z₀).symm
                (fam (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t))
              (psiV (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t)
              (psiE (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t)) := by
  intro t ht
  have hR := isOpen_Rect η δ L
  have ht' : t ∈ Ioo (-η) (L + η) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have h0t : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨by linarith, hδ⟩
  have h0tR : ((0 : ℝ), t) ∈ Rect η δ L := ⟨h0t, ht'⟩
  have hmemR : Rect η δ L ∈ 𝓝 ((0 : ℝ), t) := hR.mem_nhds h0tR
  have hcontA : ContinuousAt (fun s : ℝ => psiA (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 s) t := by
    have hsec : ContDiffAt ℝ ∞ (fun s : ℝ =>
        psiA (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 s) t := by
      have hc := ((contDiffOn_psiA (cov := cov) D hR hF).contDiffAt hmemR).comp t
        (contDiffAt_const.prodMk (contDiffAt_id (x := t)))
      simpa only [Function.comp_def, id_eq] using hc
    exact hsec.continuousAt
  have hcont0 : ContinuousAt (fun s : ℝ => fam (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 s) t := by
    have hsec : ContDiffAt ℝ ∞ (fun s : ℝ =>
        fam (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 s) t := by
      have hc := (hF.contDiffAt hmemR).comp t
        (contDiffAt_const.prodMk (contDiffAt_id (x := t)))
      simpa only [Function.comp_def, id_eq, Fam_apply] using hc
    exact hsec.continuousAt
  -- the identity is zero on a neighbourhood
  have hev0 : (fun s : ℝ => psiA (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 s
        + chrB cov z₀ ((extChartAt I z₀).symm
            (fam (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 s))
          (psiV (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 s)
          (psiV (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 s))
      =ᶠ[𝓝 t] (fun _ : ℝ => (0 : E)) := by
    refine Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ht') ?_
    intro s hs
    show psiA (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 s
        + chrB cov z₀ ((extChartAt I z₀).symm
            (fam (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 s))
          (psiV (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 s)
          (psiV (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 s) = 0
    rw [hgeo s hs]
    abel
  have hzero : HasDerivAt (fun s : ℝ => psiA (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 s
        + chrB cov z₀ ((extChartAt I z₀).symm
            (fam (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 s))
          (psiV (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 s)
          (psiV (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 s)) 0 t :=
    (hasDerivAt_const (x := t) (c := (0 : E))).congr_of_eventuallyEq hev0
  -- the derivative of the first term
  have hA : HasDerivAt (fun s : ℝ => psiA (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 s)
      (psiEA (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t) t := by
    have hsec : ContDiffAt ℝ ∞ (fun s : ℝ =>
        psiA (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 s) t := by
      have hc := ((contDiffOn_psiA (cov := cov) D hR hF).contDiffAt hmemR).comp t
        (contDiffAt_const.prodMk (contDiffAt_id (x := t)))
      simpa only [Function.comp_def, id_eq] using hc
    have hd := (hsec.differentiableAt (by simp)).hasDerivAt
    rwa [deriv_psiA_eq_psiEA (cov := cov) D (chartCoord (I := I) z₀ γ) u hR hF h0tR] at hd
  -- the derivative of the position term
  have hfam : HasDerivAt (fun s : ℝ => fam (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 s)
      (psiW (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t) t := by
    have hsec : ContDiffAt ℝ ∞ (fun s : ℝ =>
        fam (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 s) t := by
      have hc := (hF.contDiffAt hmemR).comp t
        (contDiffAt_const.prodMk (contDiffAt_id (x := t)))
      simpa only [Function.comp_def, id_eq, Fam_apply] using hc
    exact (hsec.differentiableAt (by simp)).hasDerivAt
  -- the derivative of the velocity term
  have hV : HasDerivAt (fun s : ℝ => psiV (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 s)
      (psiE (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t) t := by
    have hsec : ContDiffAt ℝ ∞ (fun s : ℝ =>
        psiV (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 s) t := by
      have hc := ((contDiffOn_psiV (cov := cov) D hR hF).contDiffAt hmemR).comp t
        (contDiffAt_const.prodMk (contDiffAt_id (x := t)))
      simpa only [Function.comp_def, id_eq] using hc
    have hd := (hsec.differentiableAt (by simp)).hasDerivAt
    rwa [deriv_psiV_eq_psiE (cov := cov) D (chartCoord (I := I) z₀ γ) u hR hF h0tR] at hd
  have hchrB := hasDerivAt_chrB_curve (cov := cov) (x₀ := z₀)
    (u := fun s : ℝ => fam (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 s)
    (a := fun s : ℝ => psiV (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 s)
    (b := fun s : ℝ => psiV (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 s)
    (v := psiW (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t)
    (a' := psiE (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t)
    (b' := psiE (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t) (t := t)
    hfam hV hV (htgt 0 h0t t ht')
    (hcont0.preimage_mem_nhds ((isOpen_extChartAt_target z₀).mem_nhds (htgt 0 h0t t ht')))
  have hc := (hA.add hchrB).unique hzero
  exact eq_neg_of_add_eq_zero_left hc

end Eta


section Target

variable {γ : ℝ → M} {u : ℝ → E} {L δ : ℝ}

/-- The chart-coordinate family lands in the chart target whenever its phase is a phase of `D`. -/
theorem fam_mem_target (D : ChartFlowData (cov := cov) (I := I) z₀ Z) {hδ : 0 < δ}
    (hphase : ∀ σ ∈ Icc (-δ) δ, ∀ t ∈ Icc (-η) (L + η),
      (chartCoord (I := I) z₀ γ t, flowScale D • (σ • u t)) ∈ D.O) :
    ∀ σ ∈ Icc (-δ) δ, ∀ t ∈ Icc (-η) (L + η),
      fam (cov := cov) D (chartCoord (I := I) z₀ γ) u σ t ∈ (extChartAt I z₀).target := by
  intro σ hσ t ht
  have ht' : |(flowScale D)⁻¹| ≤ D.ρ := by
    rw [inv_flowScale, abs_of_pos (div_pos D.hρ two_pos)]
    linarith [D.hρ]
  have := D.htgt (chartCoord (I := I) z₀ γ t, flowScale D • (σ • u t)) (hphase σ hσ t ht)
    (flowScale D)⁻¹ ht'
  show (D.α (chartCoord (I := I) z₀ γ t, flowScale D • (σ • u t)) (flowScale D)⁻¹).1
    ∈ (extChartAt I z₀).target
  exact this

end Target

section Continuity

/-- Continuity of the chart curve of the family. -/
lemma continuousOn_symm_fam (D : ChartFlowData (cov := cov) (I := I) z₀ Z) (x u : ℝ → E)
    {S : Set (ℝ × ℝ)} (hFam : ContinuousOn (Fam (cov := cov) D x u) S)
    (hmem : ∀ p ∈ S, Fam (cov := cov) D x u p ∈ (extChartAt I z₀).target) :
    ContinuousOn (fun p : ℝ × ℝ => (extChartAt I z₀).symm (Fam (cov := cov) D x u p)) S := by
  have h1 : ContinuousOn ((extChartAt I z₀).symm : E → M) ((extChartAt I z₀).target) :=
    (contMDiffOn_extChartAt_symm (𝕜 := ℝ) (I := I) (n := ∞) z₀).continuousOn
  refine (h1.comp' (g := (extChartAt I z₀).symm) (f := Fam (cov := cov) D x u) hFam hmem).congr
    (fun p _ => rfl)

/-- Continuity of `chrB` applied to the family data. -/
lemma continuousOn_chrB_fam
    (D : ChartFlowData (cov := cov) (I := I) z₀ Z) (x u : ℝ → E)
    {S : Set (ℝ × ℝ)}
    (hFam : ContinuousOn (Fam (cov := cov) D x u) S)
    (hmem : ∀ p ∈ S, Fam (cov := cov) D x u p ∈ (extChartAt I z₀).target)
    {a b : ℝ × ℝ → E} (ha : ContinuousOn a S) (hb : ContinuousOn b S) :
    ContinuousOn (fun p : ℝ × ℝ =>
      chrB cov z₀ ((extChartAt I z₀).symm (Fam (cov := cov) D x u p)) (a p) (b p)) S := by
  have hs := continuousOn_symm_fam (cov := cov) D x u hFam hmem
  have hsrc : ∀ p ∈ S, (extChartAt I z₀).symm (Fam (cov := cov) D x u p) ∈ (chartAt H z₀).source :=
    fun p hp => mem_source_chartCurve (I := I) (hmem p hp)
  have h3 := (continuousOn_chrB_prod3 (cov := cov) z₀).comp'
    (hs.prodMk (ha.prodMk hb)) (fun p hp => ⟨hsrc p hp, trivial⟩)
  intro p hp
  exact h3 p hp

/-- Continuity of `chartGram` applied to the family data. -/
lemma continuousOn_chartGram_fam
    (D : ChartFlowData (cov := cov) (I := I) z₀ Z) (x u : ℝ → E)
    {S : Set (ℝ × ℝ)}
    (hFam : ContinuousOn (Fam (cov := cov) D x u) S)
    (hmem : ∀ p ∈ S, Fam (cov := cov) D x u p ∈ (extChartAt I z₀).target)
    {a b : ℝ × ℝ → E} (ha : ContinuousOn a S) (hb : ContinuousOn b S) :
    ContinuousOn (fun p : ℝ × ℝ =>
      chartGram (I := I) z₀ ((extChartAt I z₀).symm (Fam (cov := cov) D x u p)) (a p) (b p)) S := by
  have hs := continuousOn_symm_fam (cov := cov) D x u hFam hmem
  have hsrc : ∀ p ∈ S, (extChartAt I z₀).symm (Fam (cov := cov) D x u p) ∈ (chartAt H z₀).source :=
    fun p hp => mem_source_chartCurve (I := I) (hmem p hp)
  have h3 := (continuousOn_chartGram_prod3 (I := I) z₀).comp'
    (hs.prodMk (ha.prodMk hb)) (fun p hp => ⟨hsrc p hp, trivial⟩)
  intro p hp
  exact h3 p hp

/-- Continuity of `dB` applied to the family data. -/
lemma continuousOn_dB_fam
    (D : ChartFlowData (cov := cov) (I := I) z₀ Z) (x u : ℝ → E)
    {S : Set (ℝ × ℝ)}
    (hFam : ContinuousOn (Fam (cov := cov) D x u) S)
    (hmem : ∀ p ∈ S, Fam (cov := cov) D x u p ∈ (extChartAt I z₀).target)
    {v a b : ℝ × ℝ → E} (hv : ContinuousOn v S) (ha : ContinuousOn a S)
    (hb : ContinuousOn b S) :
    ContinuousOn (fun p : ℝ × ℝ =>
      dB cov z₀ ((extChartAt I z₀).symm (Fam (cov := cov) D x u p)) (v p) (a p) (b p)) S := by
  have hs := continuousOn_symm_fam (cov := cov) D x u hFam hmem
  have hsrc : ∀ p ∈ S, (extChartAt I z₀).symm (Fam (cov := cov) D x u p) ∈ (chartAt H z₀).source :=
    fun p hp => mem_source_chartCurve (I := I) (hmem p hp)
  have h3 := (continuousOn_dB_prod (cov := cov) (I := I) z₀).comp'
    (hs.prodMk (hv.prodMk (ha.prodMk hb))) (fun p hp => ⟨hsrc p hp, trivial⟩)
  intro p hp
  exact h3 p hp

end Continuity


section ContIntegrands

variable {R S : Set (ℝ × ℝ)}

lemma contOn_hg (D : ChartFlowData (cov := cov) (I := I) z₀ Z) {x u : ℝ → E}
    (hR : IsOpen R) (hF : ContDiffOn ℝ ∞ (Fam (cov := cov) D x u) R)
    (hmem : ∀ p ∈ R, Fam (cov := cov) D x u p ∈ (extChartAt I z₀).target) (hS : S ⊆ R) :
    ContinuousOn (fun p : ℝ × ℝ => chartGram (I := I) z₀
      ((extChartAt I z₀).symm (Fam (cov := cov) D x u p))
      (psiW (cov := cov) D x u p.1 p.2) (psiW (cov := cov) D x u p.1 p.2)) S :=
  continuousOn_chartGram_fam (cov := cov) D x u ((hF.mono hS).continuousOn)
    (fun p hp => hmem p (hS hp))
    (((contDiffOn_psiW (cov := cov) D hR hF).mono hS).continuousOn)
    (((contDiffOn_psiW (cov := cov) D hR hF).mono hS).continuousOn)

lemma contOn_hg' (D : ChartFlowData (cov := cov) (I := I) z₀ Z) {x u : ℝ → E}
    (hR : IsOpen R) (hF : ContDiffOn ℝ ∞ (Fam (cov := cov) D x u) R)
    (hmem : ∀ p ∈ R, Fam (cov := cov) D x u p ∈ (extChartAt I z₀).target) (hS : S ⊆ R) :
    ContinuousOn (fun p : ℝ × ℝ => 2 * chartGram (I := I) z₀
      ((extChartAt I z₀).symm (Fam (cov := cov) D x u p))
      (psiE (cov := cov) D x u p.1 p.2 + chrB cov z₀
        ((extChartAt I z₀).symm (Fam (cov := cov) D x u p))
        (psiW (cov := cov) D x u p.1 p.2) (psiV (cov := cov) D x u p.1 p.2))
      (psiW (cov := cov) D x u p.1 p.2)) S := by
  have hFam := (hF.mono hS).continuousOn
  have hmem' : ∀ p ∈ S, Fam (cov := cov) D x u p ∈ (extChartAt I z₀).target :=
    fun p hp => hmem p (hS hp)
  have hE := ((contDiffOn_psiE (cov := cov) D hR hF).mono hS).continuousOn
  have hW := ((contDiffOn_psiW (cov := cov) D hR hF).mono hS).continuousOn
  have hV := ((contDiffOn_psiV (cov := cov) D hR hF).mono hS).continuousOn
  have hB := continuousOn_chrB_fam (cov := cov) D x u hFam hmem' hW hV
  exact (continuousOn_chartGram_fam (cov := cov) D x u hFam hmem' (hE.add hB) hW).const_mul 2

lemma contOn_hg'' (D : ChartFlowData (cov := cov) (I := I) z₀ Z) {x u : ℝ → E}
    (hR : IsOpen R) (hF : ContDiffOn ℝ ∞ (Fam (cov := cov) D x u) R)
    (hmem : ∀ p ∈ R, Fam (cov := cov) D x u p ∈ (extChartAt I z₀).target) (hS : S ⊆ R) :
    ContinuousOn (fun p : ℝ × ℝ => jetS2 (cov := cov) z₀ (Fam (cov := cov) D x u p)
      (psiW (cov := cov) D x u p.1 p.2) (psiV (cov := cov) D x u p.1 p.2)
      (psiA (cov := cov) D x u p.1 p.2) (psiE (cov := cov) D x u p.1 p.2)
      (psiEA (cov := cov) D x u p.1 p.2)) S := by
  have hFam := (hF.mono hS).continuousOn
  have hmem' : ∀ p ∈ S, Fam (cov := cov) D x u p ∈ (extChartAt I z₀).target :=
    fun p hp => hmem p (hS hp)
  have hW := ((contDiffOn_psiW (cov := cov) D hR hF).mono hS).continuousOn
  have hV := ((contDiffOn_psiV (cov := cov) D hR hF).mono hS).continuousOn
  have hA := ((contDiffOn_psiA (cov := cov) D hR hF).mono hS).continuousOn
  have hE := ((contDiffOn_psiE (cov := cov) D hR hF).mono hS).continuousOn
  have hEA := ((contDiffOn_psiEA (cov := cov) D hR hF).mono hS).continuousOn
  have hnabV : ContinuousOn (fun p : ℝ × ℝ => psiE (cov := cov) D x u p.1 p.2
      + chrB cov z₀ ((extChartAt I z₀).symm (Fam (cov := cov) D x u p))
        (psiW (cov := cov) D x u p.1 p.2) (psiV (cov := cov) D x u p.1 p.2)) S :=
    hE.add (continuousOn_chrB_fam (cov := cov) D x u hFam hmem' hW hV)
  have hBV : ContinuousOn (fun p : ℝ × ℝ => chrB cov z₀
      ((extChartAt I z₀).symm (Fam (cov := cov) D x u p))
      (psiE (cov := cov) D x u p.1 p.2) (psiV (cov := cov) D x u p.1 p.2)) S :=
    continuousOn_chrB_fam (cov := cov) D x u hFam hmem' hE hV
  have hBW : ContinuousOn (fun p : ℝ × ℝ => chrB cov z₀
      ((extChartAt I z₀).symm (Fam (cov := cov) D x u p))
      (psiW (cov := cov) D x u p.1 p.2) (psiA (cov := cov) D x u p.1 p.2)) S :=
    continuousOn_chrB_fam (cov := cov) D x u hFam hmem' hW hA
  have hBdV : ContinuousOn (fun p : ℝ × ℝ => dB cov z₀
      ((extChartAt I z₀).symm (Fam (cov := cov) D x u p))
      (psiV (cov := cov) D x u p.1 p.2) (psiW (cov := cov) D x u p.1 p.2)
      (psiV (cov := cov) D x u p.1 p.2)) S :=
    continuousOn_dB_fam (cov := cov) D x u hFam hmem' hV hW hV
  have hBnab : ContinuousOn (fun p : ℝ × ℝ => chrB cov z₀
      ((extChartAt I z₀).symm (Fam (cov := cov) D x u p))
      (psiE (cov := cov) D x u p.1 p.2 + chrB cov z₀
        ((extChartAt I z₀).symm (Fam (cov := cov) D x u p))
        (psiW (cov := cov) D x u p.1 p.2) (psiV (cov := cov) D x u p.1 p.2))
      (psiV (cov := cov) D x u p.1 p.2)) S :=
    continuousOn_chrB_fam (cov := cov) D x u hFam hmem' hnabV hV
  have hnabV2 : ContinuousOn (fun p : ℝ × ℝ => psiEA (cov := cov) D x u p.1 p.2
      + dB cov z₀ ((extChartAt I z₀).symm (Fam (cov := cov) D x u p))
          (psiV (cov := cov) D x u p.1 p.2) (psiW (cov := cov) D x u p.1 p.2)
          (psiV (cov := cov) D x u p.1 p.2)
      + chrB cov z₀ ((extChartAt I z₀).symm (Fam (cov := cov) D x u p))
          (psiE (cov := cov) D x u p.1 p.2) (psiV (cov := cov) D x u p.1 p.2)
      + chrB cov z₀ ((extChartAt I z₀).symm (Fam (cov := cov) D x u p))
          (psiW (cov := cov) D x u p.1 p.2) (psiA (cov := cov) D x u p.1 p.2)
      + chrB cov z₀ ((extChartAt I z₀).symm (Fam (cov := cov) D x u p))
          (psiE (cov := cov) D x u p.1 p.2 + chrB cov z₀
            ((extChartAt I z₀).symm (Fam (cov := cov) D x u p))
            (psiW (cov := cov) D x u p.1 p.2) (psiV (cov := cov) D x u p.1 p.2))
          (psiV (cov := cov) D x u p.1 p.2)) S :=
    (((hEA.add hBdV).add hBV).add hBW).add hBnab
  have h1 := continuousOn_chartGram_fam (cov := cov) D x u hFam hmem' hnabV2 hW
  have h2 := continuousOn_chartGram_fam (cov := cov) D x u hFam hmem' hnabV hnabV
  refine ((h1.add h2).const_mul 2).congr ?_
  intro p hp
  rfl

end ContIntegrands


/-- The energy of the chart-coordinate family over `[0,L]`. -/
noncomputable def energyFam (D : ChartFlowData (cov := cov) (I := I) z₀ Z) (x u : ℝ → E)
    (L : ℝ) : ℝ → ℝ :=
  fun σ => ∫ t in (0 : ℝ)..L, chartGram (I := I) z₀
    ((extChartAt I z₀).symm (Fam (cov := cov) D x u (σ, t)))
    (psiW (cov := cov) D x u σ t) (psiW (cov := cov) D x u σ t)

section Package

/-- **The second variation of the energy of the intrinsic family, in one chart** (without the
hypotheses `u 0 = 0`, `u L = 0`, which are only needed for the *first* variation). -/
theorem energy_second_deriv_fam_snd (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (D : ChartFlowData (cov := cov) (I := I) z₀ Z)
    {γ : ℝ → M} {u : ℝ → E} {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hη : 0 < η)
    (hγsrc : ∀ t ∈ Icc (-η) (L + η), γ t ∈ (chartAt H z₀).source)
    (hγZ : ∀ t ∈ Icc (-η) (L + η), γ t ∈ Z)
    (hF : ContDiffOn ℝ ∞ (Fam (cov := cov) D (chartCoord (I := I) z₀ γ) u) (Rect η δ L))
    (hphaseC : ∀ σ ∈ Icc (-δ) δ, ∀ t ∈ Icc (-η) (L + η),
      (chartCoord (I := I) z₀ γ t, flowScale D • (σ • u t)) ∈ chartData (I := I) z₀ Z)
    (hgeoB : ∀ t ∈ Icc (0 : ℝ) L, HasDerivAt
      (fun t' : ℝ => psiW (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t')
      (chartGeodesicVectorField cov z₀ (chartCoord (I := I) z₀ γ t,
        psiW (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t)) t)
    :
    HasDerivAt (deriv (energyFam (cov := cov) D (chartCoord (I := I) z₀ γ) u L))
        (-2 * ∫ t in (0 : ℝ)..L, indexIntegrand cov z₀
          (fun t => fam (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t)
          (fun t => psiV (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t)
          (fun t => psiW (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t)
          (fun t => psiE (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t) t) 0 := by
  have hδ2 : 0 < δ / 2 := by linarith
  have hR : IsOpen (Rect η δ L) := isOpen_Rect η δ L
  have hphaseI : ∀ σ ∈ Ioo (-δ) δ, ∀ t ∈ Ioo (-η) (L + η),
      (chartCoord (I := I) z₀ γ t, flowScale D • (σ • u t)) ∈ chartData (I := I) z₀ Z :=
    fun σ hσ t ht => hphaseC σ ⟨hσ.1.le, hσ.2.le⟩ t ⟨ht.1.le, ht.2.le⟩
  have hphaseOc : ∀ σ ∈ Icc (-δ) δ, ∀ t ∈ Icc (-η) (L + η),
      (chartCoord (I := I) z₀ γ t, flowScale D • (σ • u t)) ∈ D.O :=
    fun σ hσ t ht => D.hKO (hphaseC σ hσ t ht)
  have hmemi : ∀ σ ∈ Ioo (-δ) δ, ∀ t ∈ Ioo (-η) (L + η),
      fam (cov := cov) D (chartCoord (I := I) z₀ γ) u σ t ∈ (extChartAt I z₀).target :=
    fun σ hσ t ht => fam_mem_target (cov := cov) D (hδ := hδ) hphaseOc σ
      ⟨by linarith [hσ.1], by linarith [hσ.2]⟩ t ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hmemiC : ∀ σ ∈ Icc (-δ) δ, ∀ t ∈ Icc (-η) (L + η),
      fam (cov := cov) D (chartCoord (I := I) z₀ γ) u σ t ∈ (extChartAt I z₀).target :=
    fun σ hσ t ht => fam_mem_target (cov := cov) D (hδ := hδ) hphaseOc σ hσ t ht
  have hmemiR : ∀ p ∈ Rect η δ L, Fam (cov := cov) D (chartCoord (I := I) z₀ γ) u p
      ∈ (extChartAt I z₀).target :=
    fun p hp => hmemi p.1 hp.1 p.2 hp.2
  have hphaseO : ∀ σ ∈ Ioo (-δ) δ, ∀ t ∈ Ioo (-η) (L + η),
      (chartCoord (I := I) z₀ γ t, flowScale D • (σ • u t)) ∈ D.O :=
    fun σ hσ t ht => D.hKO (hphaseC σ ⟨hσ.1.le, hσ.2.le⟩ t ⟨ht.1.le, ht.2.le⟩)
  have h0δ : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨by linarith, hδ⟩
  have hmem0 : ∀ t ∈ Icc (0:ℝ) L, ((0 : ℝ), t) ∈ Rect η δ L :=
    fun t ht => ⟨h0δ, ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
  have hsub : (Icc (-(δ / 2)) (δ / 2) ×ˢ Icc (0 : ℝ) L) ⊆ Rect η δ L := by
    intro p hp
    exact ⟨⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩,
      ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩⟩
  have hgeo := psiA_zero_eq (cov := cov) hmet D (hδ := hδ) (hγsrc := hγsrc) (hγZ := hγZ)
    (htgt := hmemi) hphaseO
  have hgeo' := psiEA_zero_eq (cov := cov) hmet D (hδ := hδ) hη (hγsrc := hγsrc) (hγZ := hγZ)
    (htgt := hmemi) hphaseO hF hgeo
  -- the two `HasDerivAt` facts of the jet data
  have hDψt : ∀ σ ∈ Ioo (-(δ / 2)) (δ / 2), ∀ t ∈ Icc (0 : ℝ) L,
      HasDerivAt (fun t' : ℝ => Fam (cov := cov) D (chartCoord (I := I) z₀ γ) u (σ, t'))
        (psiW (cov := cov) D (chartCoord (I := I) z₀ γ) u σ t) t := by
    intro σ hσ t ht
    have h := hasDerivAt_fam_snd (cov := cov) D hR hF (σ := σ) (t := t)
      ⟨⟨by linarith [hσ.1], by linarith [hσ.2]⟩, ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
    exact h
  have hDψs : ∀ σ ∈ Ioo (-(δ / 2)) (δ / 2), ∀ t ∈ Icc (0 : ℝ) L,
      HasDerivAt (fun σ' : ℝ => Fam (cov := cov) D (chartCoord (I := I) z₀ γ) u (σ', t))
        (psiV (cov := cov) D (chartCoord (I := I) z₀ γ) u σ t) σ := by
    intro σ hσ t ht
    exact hasDerivAt_fam_fst (cov := cov) D hR hF
      ⟨⟨by linarith [hσ.1], by linarith [hσ.2]⟩, ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
  have hDvs : ∀ σ ∈ Ioo (-(δ / 2)) (δ / 2), ∀ t ∈ Icc (0 : ℝ) L,
      HasDerivAt (fun σ' : ℝ => psiV (cov := cov) D (chartCoord (I := I) z₀ γ) u σ' t)
        (psiA (cov := cov) D (chartCoord (I := I) z₀ γ) u σ t) σ := by
    intro σ hσ t ht
    exact hasDerivAt_psiV_fst (cov := cov) D hR hF
      ⟨⟨by linarith [hσ.1], by linarith [hσ.2]⟩, ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
  have hDws : ∀ σ ∈ Ioo (-(δ / 2)) (δ / 2), ∀ t ∈ Icc (0 : ℝ) L,
      HasDerivAt (fun σ' : ℝ => psiW (cov := cov) D (chartCoord (I := I) z₀ γ) u σ' t)
        (psiE (cov := cov) D (chartCoord (I := I) z₀ γ) u σ t) σ := by
    intro σ hσ t ht
    exact hasDerivAt_psiW_fst (cov := cov) D hR hF
      ⟨⟨by linarith [hσ.1], by linarith [hσ.2]⟩, ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
  have hDes : ∀ σ ∈ Ioo (-(δ / 2)) (δ / 2), ∀ t ∈ Icc (0 : ℝ) L,
      HasDerivAt (fun σ' : ℝ => psiE (cov := cov) D (chartCoord (I := I) z₀ γ) u σ' t)
        (psiEA (cov := cov) D (chartCoord (I := I) z₀ γ) u σ t) σ := by
    intro σ hσ t ht
    exact hasDerivAt_psiE_fst (cov := cov) D hR hF
      ⟨⟨by linarith [hσ.1], by linarith [hσ.2]⟩, ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
  have hGtgt : ∀ σ ∈ Icc (-(δ / 2)) (δ / 2), ∀ t ∈ Icc (0 : ℝ) L,
      Fam (cov := cov) D (chartCoord (I := I) z₀ γ) u (σ, t) ∈ (extChartAt I z₀).target :=
    fun σ hσ t ht => hmemiC σ ⟨by linarith [hσ.1], by linarith [hσ.2]⟩ t
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
  -- the second variation
  have hmain := energy_second_deriv_chart (cov := cov) hmet htor z₀
    (ψ := fun σ t => Fam (cov := cov) D (chartCoord (I := I) z₀ γ) u (σ, t))
    (w := fun σ t => psiW (cov := cov) D (chartCoord (I := I) z₀ γ) u σ t)
    (v := fun σ t => psiV (cov := cov) D (chartCoord (I := I) z₀ γ) u σ t)
    (a := fun σ t => psiA (cov := cov) D (chartCoord (I := I) z₀ γ) u σ t)
    (e := fun σ t => psiE (cov := cov) D (chartCoord (I := I) z₀ γ) u σ t)
    (ea := fun σ t => psiEA (cov := cov) D (chartCoord (I := I) z₀ γ) u σ t)
    hL hδ2 hDψt hDψs hDvs hDws hDes hGtgt
    (fun t ht => hgeo t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    (fun t ht => hgeo' t ht)
    (contOn_hg (cov := cov) D hR hF hmemiR hsub)
    (contOn_hg' (cov := cov) D hR hF hmemiR hsub)
    (contOn_hg'' (cov := cov) D hR hF hmemiR hsub)
  exact hmain

/-- **The second and first variation of the energy of the intrinsic family, in one chart.** -/
theorem energy_second_deriv_fam (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (D : ChartFlowData (cov := cov) (I := I) z₀ Z)
    {γ : ℝ → M} {u : ℝ → E} {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hη : 0 < η)
    (hγsrc : ∀ t ∈ Icc (-η) (L + η), γ t ∈ (chartAt H z₀).source)
    (hγZ : ∀ t ∈ Icc (-η) (L + η), γ t ∈ Z)
    (hF : ContDiffOn ℝ ∞ (Fam (cov := cov) D (chartCoord (I := I) z₀ γ) u) (Rect η δ L))
    (hphaseC : ∀ σ ∈ Icc (-δ) δ, ∀ t ∈ Icc (-η) (L + η),
      (chartCoord (I := I) z₀ γ t, flowScale D • (σ • u t)) ∈ chartData (I := I) z₀ Z)
    (hgeoB : ∀ t ∈ Icc (0 : ℝ) L, HasDerivAt
      (fun t' : ℝ => psiW (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t')
      (chartGeodesicVectorField cov z₀ (chartCoord (I := I) z₀ γ t,
        psiW (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t)) t)
    (hu0 : u 0 = 0) (huL : u L = 0) :
    HasDerivAt (deriv (energyFam (cov := cov) D (chartCoord (I := I) z₀ γ) u L))
        (-2 * ∫ t in (0 : ℝ)..L, indexIntegrand cov z₀
          (fun t => fam (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t)
          (fun t => psiV (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t)
          (fun t => psiW (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t)
          (fun t => psiE (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t) t) 0
      ∧ HasDerivAt (energyFam (cov := cov) D (chartCoord (I := I) z₀ γ) u L) 0 0 := by
  have hδ2 : 0 < δ / 2 := by linarith
  have hR : IsOpen (Rect η δ L) := isOpen_Rect η δ L
  have hphaseI : ∀ σ ∈ Ioo (-δ) δ, ∀ t ∈ Ioo (-η) (L + η),
      (chartCoord (I := I) z₀ γ t, flowScale D • (σ • u t)) ∈ chartData (I := I) z₀ Z :=
    fun σ hσ t ht => hphaseC σ ⟨hσ.1.le, hσ.2.le⟩ t ⟨ht.1.le, ht.2.le⟩
  have hphaseOc : ∀ σ ∈ Icc (-δ) δ, ∀ t ∈ Icc (-η) (L + η),
      (chartCoord (I := I) z₀ γ t, flowScale D • (σ • u t)) ∈ D.O :=
    fun σ hσ t ht => D.hKO (hphaseC σ hσ t ht)
  have hmemi : ∀ σ ∈ Ioo (-δ) δ, ∀ t ∈ Ioo (-η) (L + η),
      fam (cov := cov) D (chartCoord (I := I) z₀ γ) u σ t ∈ (extChartAt I z₀).target :=
    fun σ hσ t ht => fam_mem_target (cov := cov) D (hδ := hδ) hphaseOc σ
      ⟨by linarith [hσ.1], by linarith [hσ.2]⟩ t ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hmemiC : ∀ σ ∈ Icc (-δ) δ, ∀ t ∈ Icc (-η) (L + η),
      fam (cov := cov) D (chartCoord (I := I) z₀ γ) u σ t ∈ (extChartAt I z₀).target :=
    fun σ hσ t ht => fam_mem_target (cov := cov) D (hδ := hδ) hphaseOc σ hσ t ht
  have hmemiR : ∀ p ∈ Rect η δ L, Fam (cov := cov) D (chartCoord (I := I) z₀ γ) u p
      ∈ (extChartAt I z₀).target :=
    fun p hp => hmemi p.1 hp.1 p.2 hp.2
  have hphaseO : ∀ σ ∈ Ioo (-δ) δ, ∀ t ∈ Ioo (-η) (L + η),
      (chartCoord (I := I) z₀ γ t, flowScale D • (σ • u t)) ∈ D.O :=
    fun σ hσ t ht => D.hKO (hphaseC σ ⟨hσ.1.le, hσ.2.le⟩ t ⟨ht.1.le, ht.2.le⟩)
  have h0δ : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨by linarith, hδ⟩
  have hmem0 : ∀ t ∈ Icc (0:ℝ) L, ((0 : ℝ), t) ∈ Rect η δ L :=
    fun t ht => ⟨h0δ, ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
  have hsub : (Icc (-(δ / 2)) (δ / 2) ×ˢ Icc (0 : ℝ) L) ⊆ Rect η δ L := by
    intro p hp
    exact ⟨⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩,
      ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩⟩
  have hgeo := psiA_zero_eq (cov := cov) hmet D (hδ := hδ) (hγsrc := hγsrc) (hγZ := hγZ)
    (htgt := hmemi) hphaseO
  have hgeo' := psiEA_zero_eq (cov := cov) hmet D (hδ := hδ) hη (hγsrc := hγsrc) (hγZ := hγZ)
    (htgt := hmemi) hphaseO hF hgeo
  -- the two `HasDerivAt` facts of the jet data
  have hDψt : ∀ σ ∈ Ioo (-(δ / 2)) (δ / 2), ∀ t ∈ Icc (0 : ℝ) L,
      HasDerivAt (fun t' : ℝ => Fam (cov := cov) D (chartCoord (I := I) z₀ γ) u (σ, t'))
        (psiW (cov := cov) D (chartCoord (I := I) z₀ γ) u σ t) t := by
    intro σ hσ t ht
    have h := hasDerivAt_fam_snd (cov := cov) D hR hF (σ := σ) (t := t)
      ⟨⟨by linarith [hσ.1], by linarith [hσ.2]⟩, ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
    exact h
  have hDψs : ∀ σ ∈ Ioo (-(δ / 2)) (δ / 2), ∀ t ∈ Icc (0 : ℝ) L,
      HasDerivAt (fun σ' : ℝ => Fam (cov := cov) D (chartCoord (I := I) z₀ γ) u (σ', t))
        (psiV (cov := cov) D (chartCoord (I := I) z₀ γ) u σ t) σ := by
    intro σ hσ t ht
    exact hasDerivAt_fam_fst (cov := cov) D hR hF
      ⟨⟨by linarith [hσ.1], by linarith [hσ.2]⟩, ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
  have hDvs : ∀ σ ∈ Ioo (-(δ / 2)) (δ / 2), ∀ t ∈ Icc (0 : ℝ) L,
      HasDerivAt (fun σ' : ℝ => psiV (cov := cov) D (chartCoord (I := I) z₀ γ) u σ' t)
        (psiA (cov := cov) D (chartCoord (I := I) z₀ γ) u σ t) σ := by
    intro σ hσ t ht
    exact hasDerivAt_psiV_fst (cov := cov) D hR hF
      ⟨⟨by linarith [hσ.1], by linarith [hσ.2]⟩, ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
  have hDws : ∀ σ ∈ Ioo (-(δ / 2)) (δ / 2), ∀ t ∈ Icc (0 : ℝ) L,
      HasDerivAt (fun σ' : ℝ => psiW (cov := cov) D (chartCoord (I := I) z₀ γ) u σ' t)
        (psiE (cov := cov) D (chartCoord (I := I) z₀ γ) u σ t) σ := by
    intro σ hσ t ht
    exact hasDerivAt_psiW_fst (cov := cov) D hR hF
      ⟨⟨by linarith [hσ.1], by linarith [hσ.2]⟩, ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
  have hDes : ∀ σ ∈ Ioo (-(δ / 2)) (δ / 2), ∀ t ∈ Icc (0 : ℝ) L,
      HasDerivAt (fun σ' : ℝ => psiE (cov := cov) D (chartCoord (I := I) z₀ γ) u σ' t)
        (psiEA (cov := cov) D (chartCoord (I := I) z₀ γ) u σ t) σ := by
    intro σ hσ t ht
    exact hasDerivAt_psiE_fst (cov := cov) D hR hF
      ⟨⟨by linarith [hσ.1], by linarith [hσ.2]⟩, ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
  have hGtgt : ∀ σ ∈ Icc (-(δ / 2)) (δ / 2), ∀ t ∈ Icc (0 : ℝ) L,
      Fam (cov := cov) D (chartCoord (I := I) z₀ γ) u (σ, t) ∈ (extChartAt I z₀).target :=
    fun σ hσ t ht => hmemiC σ ⟨by linarith [hσ.1], by linarith [hσ.2]⟩ t
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
  -- the second variation
  have hmain := energy_second_deriv_chart (cov := cov) hmet htor z₀
    (ψ := fun σ t => Fam (cov := cov) D (chartCoord (I := I) z₀ γ) u (σ, t))
    (w := fun σ t => psiW (cov := cov) D (chartCoord (I := I) z₀ γ) u σ t)
    (v := fun σ t => psiV (cov := cov) D (chartCoord (I := I) z₀ γ) u σ t)
    (a := fun σ t => psiA (cov := cov) D (chartCoord (I := I) z₀ γ) u σ t)
    (e := fun σ t => psiE (cov := cov) D (chartCoord (I := I) z₀ γ) u σ t)
    (ea := fun σ t => psiEA (cov := cov) D (chartCoord (I := I) z₀ γ) u σ t)
    hL hδ2 hDψt hDψs hDvs hDws hDes hGtgt
    (fun t ht => hgeo t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    (fun t ht => hgeo' t ht)
    (contOn_hg (cov := cov) D hR hF hmemiR hsub)
    (contOn_hg' (cov := cov) D hR hF hmemiR hsub)
    (contOn_hg'' (cov := cov) D hR hF hmemiR hsub)
  -- the first variation
  have hvt : ∀ t ∈ Icc (0 : ℝ) L, HasDerivAt
      (fun t' : ℝ => psiV (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t')
      (psiE (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t) t := by
    intro t ht
    have hsec : DifferentiableAt ℝ (fun t' : ℝ =>
        psiV (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t') t := by
      have hc := ((contDiffOn_psiV (cov := cov) D hR hF).contDiffAt
        (hR.mem_nhds (hmem0 t ht))).comp t
        (contDiffAt_const.prodMk (contDiffAt_id (x := t)))
      exact (by simpa only [Function.comp_def, id_eq] using hc : ContDiffAt ℝ ∞
        (fun t' : ℝ => psiV (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t') t).differentiableAt (by simp)
    have h := hsec.hasDerivAt
    rwa [deriv_psiV_eq_psiE (cov := cov) D _ _ hR hF (hmem0 t ht)] at h
  have hv0 : psiV (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 0 = 0 := by
    have hconst : (fun σ' : ℝ => fam (cov := cov) D (chartCoord (I := I) z₀ γ) u σ' 0)
        = fun _ => fam (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 0 := by
      funext σ'
      show Hfun D (chartCoord (I := I) z₀ γ 0, σ' • u 0)
        = Hfun D (chartCoord (I := I) z₀ γ 0, (0 : ℝ) • u 0)
      rw [hu0]; simp
    show deriv (fun σ' : ℝ => fam (cov := cov) D (chartCoord (I := I) z₀ γ) u σ' 0) 0 = 0
    rw [hconst, deriv_const']
  have hvL : psiV (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 L = 0 := by
    have hconst : (fun σ' : ℝ => fam (cov := cov) D (chartCoord (I := I) z₀ γ) u σ' L)
        = fun _ => fam (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 L := by
      funext σ'
      show Hfun D (chartCoord (I := I) z₀ γ L, σ' • u L)
        = Hfun D (chartCoord (I := I) z₀ γ L, (0 : ℝ) • u L)
      rw [huL]; simp
    show deriv (fun σ' : ℝ => fam (cov := cov) D (chartCoord (I := I) z₀ γ) u σ' L) 0 = 0
    rw [hconst, deriv_const']
  have hgeoBval : ∀ t ∈ Icc (0 : ℝ) L,
      chartGeodesicVectorField cov z₀ (chartCoord (I := I) z₀ γ t,
          psiW (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t)
        + chrB cov z₀ ((extChartAt I z₀).symm
            (Fam (cov := cov) D (chartCoord (I := I) z₀ γ) u ((0 : ℝ), t)))
          (psiW (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t)
          (psiW (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t) = 0 := by
    intro t ht
    have hmemIoo : t ∈ Ioo (-η) (L + η) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hzerFun : (fun t' : ℝ => Fam (cov := cov) D (chartCoord (I := I) z₀ γ) u ((0 : ℝ), t'))
        =ᶠ[𝓝 t] (fun t' : ℝ => chartCoord (I := I) z₀ γ t') := by
      refine Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hmemIoo) ?_
      intro t' ht'
      show Hfun D (chartCoord (I := I) z₀ γ t', (0 : ℝ) • u t') = chartCoord (I := I) z₀ γ t'
      rw [zero_smul]
      exact Hfun_zero (cov := cov) D (by
        have h := hphaseC 0 ⟨by linarith, hδ.le⟩ t' ⟨ht'.1.le, ht'.2.le⟩
        simpa only [zero_smul, smul_zero] using h)
    have hw : psiW (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t
        = deriv (fun t' : ℝ => chartCoord (I := I) z₀ γ t') t := by
      show deriv (fun t' : ℝ => Fam (cov := cov) D (chartCoord (I := I) z₀ γ) u ((0 : ℝ), t')) t = _
      exact Filter.EventuallyEq.deriv_eq hzerFun
    have hzer0 : Fam (cov := cov) D (chartCoord (I := I) z₀ γ) u ((0 : ℝ), t)
        = chartCoord (I := I) z₀ γ t := hzerFun.eq_of_nhds
    rw [hzer0, hw, chartGeodesicVectorField, chrB_apply]
    simp
  have hfirst := energy_first_deriv_chart_eq_zero (cov := cov) hmet htor z₀
    (ψ := fun σ t => Fam (cov := cov) D (chartCoord (I := I) z₀ γ) u (σ, t))
    (w := fun σ t => psiW (cov := cov) D (chartCoord (I := I) z₀ γ) u σ t)
    (v := fun σ t => psiV (cov := cov) D (chartCoord (I := I) z₀ γ) u σ t)
    (a := fun σ t => psiA (cov := cov) D (chartCoord (I := I) z₀ γ) u σ t)
    (e := fun σ t => psiE (cov := cov) D (chartCoord (I := I) z₀ γ) u σ t)
    (w' := fun t => chartGeodesicVectorField cov z₀ (chartCoord (I := I) z₀ γ t,
      psiW (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t))
    hL hδ2 hDψt hDψs hDvs hDws hvt
    (fun t ht => hgeoB t ht)
    hgeoBval hGtgt hv0 hvL
    (contOn_hg (cov := cov) D hR hF hmemiR hsub)
    (contOn_hg' (cov := cov) D hR hF hmemiR hsub)
  exact ⟨hmain, hfirst⟩

end Package

section Convenience

/-- **`energy_second_deriv_fam` with the smoothness of the coordinate family produced from the
smoothness of the two coordinate curves.** -/
theorem energy_second_deriv_fam_of_smooth (hmet : IsMetricCompatible cov)
    (htor : cov.torsion = 0) (D : ChartFlowData (cov := cov) (I := I) z₀ Z)
    {γ : ℝ → M} {u : ℝ → E} {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hη : 0 < η)
    (hγsrc : ∀ t ∈ Icc (-η) (L + η), γ t ∈ (chartAt H z₀).source)
    (hγZ : ∀ t ∈ Icc (-η) (L + η), γ t ∈ Z)
    (hx : ContDiffOn ℝ ∞ (chartCoord (I := I) z₀ γ) (Ioo (-η) (L + η)))
    (hu : ContDiffOn ℝ ∞ u (Ioo (-η) (L + η)))
    (hphaseC : ∀ σ ∈ Icc (-δ) δ, ∀ t ∈ Icc (-η) (L + η),
      (chartCoord (I := I) z₀ γ t, flowScale D • (σ • u t)) ∈ chartData (I := I) z₀ Z)
    (hgeoB : ∀ t ∈ Icc (0 : ℝ) L, HasDerivAt
      (fun t' : ℝ => psiW (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t')
      (chartGeodesicVectorField cov z₀ (chartCoord (I := I) z₀ γ t,
        psiW (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t)) t)
    (hu0 : u 0 = 0) (huL : u L = 0) :
    HasDerivAt (deriv (energyFam (cov := cov) D (chartCoord (I := I) z₀ γ) u L))
        (-2 * ∫ t in (0 : ℝ)..L, indexIntegrand cov z₀
          (fun t => fam (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t)
          (fun t => psiV (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t)
          (fun t => psiW (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t)
          (fun t => psiE (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t) t) 0
      ∧ HasDerivAt (energyFam (cov := cov) D (chartCoord (I := I) z₀ γ) u L) 0 0 :=
  energy_second_deriv_fam (cov := cov) hmet htor D hL hδ hη hγsrc hγZ
    (contDiffOn_fam (cov := cov) D hx hu hphaseC) hphaseC hgeoB hu0 huL

/-- **`energy_second_deriv_fam_snd` with the smoothness of the coordinate family produced from the
smoothness of the two coordinate curves.**  (The hypotheses `u 0 = 0`, `u L = 0` are *not* needed for
the second variation.) -/
theorem energy_second_deriv_fam_of_smooth_snd (hmet : IsMetricCompatible cov)
    (htor : cov.torsion = 0) (D : ChartFlowData (cov := cov) (I := I) z₀ Z)
    {γ : ℝ → M} {u : ℝ → E} {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hη : 0 < η)
    (hγsrc : ∀ t ∈ Icc (-η) (L + η), γ t ∈ (chartAt H z₀).source)
    (hγZ : ∀ t ∈ Icc (-η) (L + η), γ t ∈ Z)
    (hx : ContDiffOn ℝ ∞ (chartCoord (I := I) z₀ γ) (Ioo (-η) (L + η)))
    (hu : ContDiffOn ℝ ∞ u (Ioo (-η) (L + η)))
    (hphaseC : ∀ σ ∈ Icc (-δ) δ, ∀ t ∈ Icc (-η) (L + η),
      (chartCoord (I := I) z₀ γ t, flowScale D • (σ • u t)) ∈ chartData (I := I) z₀ Z)
    (hgeoB : ∀ t ∈ Icc (0 : ℝ) L, HasDerivAt
      (fun t' : ℝ => psiW (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t')
      (chartGeodesicVectorField cov z₀ (chartCoord (I := I) z₀ γ t,
        psiW (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t)) t) :
    HasDerivAt (deriv (energyFam (cov := cov) D (chartCoord (I := I) z₀ γ) u L))
        (-2 * ∫ t in (0 : ℝ)..L, indexIntegrand cov z₀
          (fun t => fam (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t)
          (fun t => psiV (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t)
          (fun t => psiW (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t)
          (fun t => psiE (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t) t) 0 :=
  energy_second_deriv_fam_snd (cov := cov) hmet htor D hL hδ hη hγsrc hγZ
    (contDiffOn_fam (cov := cov) D hx hu hphaseC) hphaseC hgeoB

end Convenience

end

end Submission.IntrinsicVariation




