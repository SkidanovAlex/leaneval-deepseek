
import Submission.Work.RiemLib.IntrinsicVariation
import Submission.Work.RiemLib.IndexIntrinsic3
import Submission.Work.RiemLib.GlobalBM
import Submission.Work.RiemLib.Commons.Analysis.Calculus.exists_lt_of_deriv_eq_zero_of_hasDerivAt_deriv_neg
import Submission.Work.RiemLib.Commons.Analysis.Calculus.exists_lt_of_hasDerivAt_deriv_neg
import Submission.Work.RiemLib.Minimal
import Submission.Work.RiemLib.GeodesicSpeed
import Submission.Work.RiemLib.Length

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The second variation of the energy of an intrinsic variation by geodesics: the interval version

This module globalises `Submission.IntrinsicVariation`'s per-chart second variation of the energy to
an arbitrary interval `[a,b]`, in **intrinsic** form: for the family
`Φ_σ(s) = GExp (γ s) (σ • V s)` (where `V` is the field with chart coordinates `u` in one chart `z₀`),
`E(σ) = ∫_a^b (curveSpeed (Φ_σ) t)^2 dt` satisfies

  `E''(0) = 2 ∫_a^b idxAlong γ V Z`  and  `E'(0) = 0`,

where `Z` is the field whose chart coordinates are the covariant derivative `DtQ` of `u`.  This is
the piece of the global `σ ≤ κ` (Roadmap §99.5): the assembly over a finite chart cover only has to
sum these interval statements (the integrand `idxAlong` is intrinsic, so no telescoping is needed).

Main theorems: `energy_second_deriv_piece`; the supporting lemmas
`psiV_zero`, `psiW_zero`, `psiE_zero`, `sq_curveSpeed_fam`, `mdifferentiableAt_GExp_fam`,
`contDiffOn_fam_Ioo`, `contDiffOn_chartCoord`, `mdifferentiableAt_of_contDiffOn_chartCoord`,
`curveSpeed_comp_add_left`, `curveVelocity_comp_add_left`, `idxAlong_comp_add`, `DtQ_congr`.
-/


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter MeasureTheory
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
open Submission.SecondVariation
open Submission.Length
open Submission.GeodesicSpeed
open Submission.IntrinsicVariation
open Submission.IndexIntrinsic
open Submission.IndexIntrinsic2

namespace Submission.SecondVarGlobal

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

/-! ## The three jet identities of the intrinsic family at `σ = 0` -/

/-- **`∂_σfam|₀ = u`**: the `σ`-velocity of the chart-coordinate ray is the direction. -/
lemma psiV_zero (D : ChartFlowData (cov := cov) (I := I) z₀ Z) {x u : ℝ → E} {t : ℝ}
    (hcuO : (x t, flowScale D • u t) ∈ D.O) (hxO : (x t, (0 : E)) ∈ D.O) :
    psiV (cov := cov) D x u 0 t = u t := by
  show deriv (fun σ' : ℝ => Hfun D (x t, σ' • u t)) 0 = u t
  exact (hasDerivAt_Hfun_along (cov := cov) D hcuO hxO).deriv

/-- **`∂_t fam|₀ = (chartCoord γ)'`** whenever the family at `σ = 0` is the base curve. -/
lemma psiW_zero (D : ChartFlowData (cov := cov) (I := I) z₀ Z) {x u : ℝ → E} {t : ℝ}
    (hxZ : ∀ᶠ t' in 𝓝 t, x t' ∈ (extChartAt I z₀) '' Z) :
    psiW (cov := cov) D x u 0 t = deriv (fun t' : ℝ => x t') t := by
  have hev : (fun t' : ℝ => fam (cov := cov) D x u 0 t') =ᶠ[𝓝 t] (fun t' : ℝ => x t') := by
    filter_upwards [hxZ] with t' ht'
    show Hfun D (x t', (0 : ℝ) • u t') = x t'
    rw [zero_smul]
    exact Hfun_zero (cov := cov) D ⟨ht', by simp [Metric.mem_closedBall]⟩
  show deriv (fun t' : ℝ => fam (cov := cov) D x u 0 t') t = deriv (fun t' : ℝ => x t') t
  exact hev.deriv_eq

/-- **Clairaut for the family**: `∂_σ∂_t fam|₀ = ∂_t∂_σ fam|₀`. -/
lemma psiE_zero_eq (D : ChartFlowData (cov := cov) (I := I) z₀ Z) {x u : ℝ → E}
    {R : Set (ℝ × ℝ)} (hR : IsOpen R) (hF : ContDiffOn ℝ ∞ (Fam (cov := cov) D x u) R)
    {t : ℝ} (h : ((0 : ℝ), t) ∈ R) :
    psiE (cov := cov) D x u 0 t = deriv (fun t' : ℝ => psiV (cov := cov) D x u 0 t') t := by
  have h2 : ContDiffAt ℝ 2 (Fam (cov := cov) D x u) ((0 : ℝ), t) :=
    (hF.contDiffAt (hR.mem_nhds h)).of_le two_le_infty
  have hswap := Commons.Analysis.Calculus.deriv_deriv_swap (F := Fam (cov := cov) D x u)
    (x := (0 : ℝ)) (y := t) h2
  have hL : deriv (fun t' : ℝ => deriv (fun s : ℝ => Fam (cov := cov) D x u (s, t')) 0) t
      = deriv (fun t' : ℝ => psiV (cov := cov) D x u 0 t') t := by
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards with t'
    rfl
  have hR' : deriv (fun s : ℝ => deriv (fun t' : ℝ => Fam (cov := cov) D x u (s, t')) t) 0
      = psiE (cov := cov) D x u 0 t := by
    show deriv (fun s : ℝ => deriv (fun t' : ℝ => Fam (cov := cov) D x u (s, t')) t) 0
      = deriv (fun s : ℝ => psiW (cov := cov) D x u s t) 0
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards with s
    rfl
  rw [hL, hR'] at hswap
  exact hswap.symm

/-- **`∂_σ∂_t fam|₀ = u'`** for the intrinsic family with the base curve fixed in a chart. -/
lemma psiE_zero (D : ChartFlowData (cov := cov) (I := I) z₀ Z) {x u : ℝ → E}
    {R : Set (ℝ × ℝ)} (hR : IsOpen R) (hF : ContDiffOn ℝ ∞ (Fam (cov := cov) D x u) R)
    {t : ℝ} (h : ((0 : ℝ), t) ∈ R)
    (hVz : (fun t' : ℝ => psiV (cov := cov) D x u 0 t')
      =ᶠ[𝓝 t] (fun t' : ℝ => u t')) :
    psiE (cov := cov) D x u 0 t = deriv (fun t' : ℝ => u t') t := by
  rw [psiE_zero_eq (cov := cov) D hR hF h]
  exact Filter.EventuallyEq.deriv_eq hVz

/-- **The chart-coordinate family lands in the target.** -/
lemma fam_mem_target' (D : ChartFlowData (cov := cov) (I := I) z₀ Z) {x u : ℝ → E} {σ t : ℝ}
    (h : (x t, flowScale D • (σ • u t)) ∈ D.O) :
    fam (cov := cov) D x u σ t ∈ (extChartAt I z₀).target := by
  have ht' : |(flowScale D)⁻¹| ≤ D.ρ := by
    rw [inv_flowScale, abs_of_pos (div_pos D.hρ two_pos)]
    linarith [D.hρ]
  have := D.htgt (x t, flowScale D • (σ • u t)) h (flowScale D)⁻¹ ht'
  show (D.α (x t, flowScale D • (σ • u t)) (flowScale D)⁻¹).1 ∈ (extChartAt I z₀).target
  exact this

/-- **The energy integrand of the intrinsic family is its squared speed.**  For the family
`Φ_σ(s) = GExp (γ s) (σ • V s)` whose chart coordinates in the chart at `z₀` are
`s ↦ fam D x u σ s` (with chart velocity `psiW D x u σ s`), the chart-Gram square of the chart
velocity is the squared Riemannian speed of `Φ_σ`. -/
theorem sq_curveSpeed_fam (hmet : IsMetricCompatible cov)
    (D : ChartFlowData (cov := cov) (I := I) z₀ Z) {γ : ℝ → M} {x u : ℝ → E}
    {V : (t : ℝ) → TangentSpace I (γ t)} {σ t : ℝ} {R : Set (ℝ × ℝ)}
    (hR : IsOpen R) (hF : ContDiffOn ℝ ∞ (Fam (cov := cov) D x u) R) (h : (σ, t) ∈ R)
    (hVev : V =ᶠ[𝓝 t] (fun s => frameVector (I := I) z₀ (γ s) (u s)))
    (hγZ : ∀ᶠ s in 𝓝 t, γ s ∈ Z)
    (hγsrc : ∀ᶠ s in 𝓝 t, γ s ∈ (chartAt H z₀).source)
    (hxev : γ =ᶠ[𝓝 t] (fun s => (extChartAt I z₀).symm (x s)))
    (hph : ∀ᶠ s in 𝓝 t, (x s, flowScale D • (σ • u s)) ∈ D.O) :
    (curveSpeed (I := I) (fun s : ℝ => GExp (cov := cov) hmet (γ s) (σ • V s)) t) ^ 2
      = chartGram (I := I) z₀ ((extChartAt I z₀).symm (fam (cov := cov) D x u σ t))
          (psiW (cov := cov) D x u σ t) (psiW (cov := cov) D x u σ t) := by
  -- the eventual identification of the two curves
  have hΦ : (fun s : ℝ => GExp (cov := cov) hmet (γ s) (σ • V s))
      =ᶠ[𝓝 t] (fun s : ℝ => (extChartAt I z₀).symm (fam (cov := cov) D x u σ s)) := by
    filter_upwards [hVev, hγZ, hγsrc, hxev, hph] with s hV hZ hs hx hp
    have hxtgt : x s ∈ (extChartAt I z₀).target := (D.hOW hp).1
    have h1 : σ • V s = σ • frameVector (I := I) z₀ (γ s) (u s) := by rw [hV]
    rw [h1, ← Submission.GExpSmooth.frameVector_smul']
    have hxeq : (extChartAt I z₀) (γ s) = x s := by
      rw [hx]
      exact PartialEquiv.right_inv (extChartAt I z₀) hxtgt
    have hsrc : γ s ∈ (extChartAt I z₀).source := by rw [extChartAt_source]; exact hs
    rw [← hxeq] at hp
    have hger := GExp_eq_symm_Hfun (cov := cov) hmet D hZ hsrc hp
    rw [hger, hxeq]
    rfl
  rw [curveSpeed_congr_of_eventuallyEq (I := I) hΦ]
  -- the chart curve has derivative `psiW`
  have htgt : fam (cov := cov) D x u σ t ∈ (extChartAt I z₀).target :=
    fam_mem_target' (cov := cov) D hph.self_of_nhds
  have hstay : ∀ᶠ s in 𝓝 t, fam (cov := cov) D x u σ s ∈ (extChartAt I z₀).target :=
    hph.mono (fun s hs => fam_mem_target' (cov := cov) D hs)
  have hfam : HasDerivAt (fun s : ℝ => fam (cov := cov) D x u σ s)
      (psiW (cov := cov) D x u σ t) t :=
    hasDerivAt_fam_snd (cov := cov) D hR hF h
  rw [curveSpeed_chartCurve (I := I) (x₀ := z₀) (u := fun s : ℝ => fam (cov := cov) D x u σ s)
    (v := psiW (cov := cov) D x u σ t) (t := t) hfam htgt hstay]
  exact Real.sq_sqrt (Submission.Minimal.chartGram_self_nonneg (I := I) z₀ _ _)

/-! ## Two elementary congruence lemmas -/

/-- The speed is invariant under a translation of the parameter (`x + a` form). -/
lemma curveSpeed_comp_add_right (γ : ℝ → M) (a t : ℝ)
    (hd : MDifferentiableAt 𝓘(ℝ) I γ (t + a)) :
    curveSpeed (I := I) (fun x : ℝ => γ (x + a)) t = curveSpeed (I := I) γ (t + a) := by
  have h := curveSpeed_comp_mul_add (I := I) (γ := γ) (c := 1) (d := a) (t := t) one_pos
    (by simpa [one_mul] using hd)
  simpa using h

/-- The speed is invariant under a translation of the parameter (`a + x` form). -/
lemma curveSpeed_comp_add_left (γ : ℝ → M) (a t : ℝ)
    (hd : MDifferentiableAt 𝓘(ℝ) I γ (a + t)) :
    curveSpeed (I := I) (fun x : ℝ => γ (a + x)) t = curveSpeed (I := I) γ (a + t) := by
  have h1 : (fun x : ℝ => γ (a + x)) = (fun x : ℝ => γ (x + a)) := by
    funext x; rw [add_comm]
  rw [curveSpeed_congr_of_eventuallyEq (I := I) (Filter.EventuallyEq.of_eq h1),
    curveSpeed_comp_add_right (I := I) γ a t (by rwa [add_comm] at hd), add_comm]

/-- `DtQ` only depends on the pointwise values of its four functions. -/
lemma DtQ_congr {x₀ : M} {u₁ u₂ η₁ η₂ w₁ w₂ e₁ e₂ : ℝ → E} {t : ℝ}
    (h1 : u₁ t = u₂ t) (h2 : η₁ t = η₂ t) (h3 : w₁ t = w₂ t) (h4 : e₁ t = e₂ t) :
    DtQ cov x₀ u₁ η₁ w₁ e₁ t = DtQ cov x₀ u₂ η₂ w₂ e₂ t := by
  simp only [DtQ, covDsP, famP, Submission.SecondVariation.fam, h1, h2, h3, h4,
    zero_smul, add_zero]

/-- The chart-coordinate curve in the chart at `z₀` is `C^∞` where the curve is. -/
lemma contDiffOn_chartCoord {γ : ℝ → M} {s : Set ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ) I ∞ γ s) (hs : s ⊆ γ ⁻¹' (chartAt H z₀).source) :
    ContDiffOn ℝ ∞ (chartCoord (I := I) z₀ γ) s := by
  have h2 : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, E) ∞ (chartCoord (I := I) z₀ γ) s :=
    (contMDiffOn_extChartAt (I := I) (x := z₀)).comp hγ (fun x hx => hs hx)
  exact h2.contDiffOn

/-- The velocity is invariant under a translation of the parameter (`x + a` form). -/
lemma curveVelocity_comp_add_right (γ : ℝ → M) (a t : ℝ)
    (hd : MDifferentiableAt 𝓘(ℝ) I γ (t + a)) :
    curveVelocity (I := I) (fun x : ℝ => γ (x + a)) t = curveVelocity (I := I) γ (t + a) := by
  have hfun : (fun x : ℝ => γ (x + a)) = (fun x : ℝ => γ (1 * x + a)) := by
    funext x; rw [one_mul]
  rw [hfun]
  have h := curveVelocity_comp_mul_add (I := I) (γ := γ) (c := 1) (d := a) (t := t)
    (by simpa only [one_mul] using hd)
  rw [h]
  simp only [one_smul]
  congr 1
  ring

/-- The velocity is invariant under a translation of the parameter. -/
lemma curveVelocity_comp_add_left (γ : ℝ → M) (a t : ℝ)
    (hd : MDifferentiableAt 𝓘(ℝ) I γ (a + t)) :
    curveVelocity (I := I) (fun x : ℝ => γ (a + x)) t = curveVelocity (I := I) γ (a + t) := by
  have h1 : (fun x : ℝ => γ (a + x)) = (fun x : ℝ => γ (x + a)) := by
    funext x; rw [add_comm]
  rw [h1, curveVelocity_comp_add_right (I := I) γ a t (by rwa [add_comm] at hd)]
  rw [add_comm t a]

/-- The intrinsic index integrand is invariant under a translation of the parameter. -/
lemma idxAlong_comp_add (γ : ℝ → M) (V Z : (t : ℝ) → TangentSpace I (γ t)) (a t : ℝ)
    (hd : MDifferentiableAt 𝓘(ℝ) I γ (a + t)) :
    idxAlong (cov := cov) (fun s : ℝ => γ (a + s)) (fun s : ℝ => V (a + s))
        (fun s : ℝ => Z (a + s)) t = idxAlong (cov := cov) γ V Z (a + t) := by
  rw [idxAlong, idxAlong, curveVelocity_comp_add_left (I := I) γ a t hd]

/-- The intrinsic curve is `MDifferentiableAt` where its chart coordinate curve is smooth. -/
lemma mdifferentiableAt_of_contDiffOn_chartCoord {γ : ℝ → M} {A B t : ℝ}
    (hx : ContDiffOn ℝ ∞ (chartCoord (I := I) z₀ γ) (Ioo A B)) (ht : t ∈ Ioo A B)
    (hsrc : ∀ᶠ s in 𝓝 t, γ s ∈ (chartAt H z₀).source) :
    MDifferentiableAt 𝓘(ℝ) I γ t := by
  have hderiv : HasDerivAt (chartCoord (I := I) z₀ γ) (deriv (chartCoord (I := I) z₀ γ) t) t :=
    ((hx.contDiffAt (isOpen_Ioo.mem_nhds ht)).differentiableAt (by simp)).hasDerivAt
  have htgt : chartCoord (I := I) z₀ γ t ∈ (extChartAt I z₀).target :=
    (extChartAt I z₀).map_source (by rw [extChartAt_source]; exact hsrc.self_of_nhds)
  have hstay : ∀ᶠ s in 𝓝 t, chartCoord (I := I) z₀ γ s ∈ (extChartAt I z₀).target :=
    hderiv.continuousAt.preimage_mem_nhds ((isOpen_extChartAt_target z₀).mem_nhds htgt)
  have hmd : MDifferentiableAt 𝓘(ℝ) I (fun s : ℝ => (extChartAt I z₀).symm
      (chartCoord (I := I) z₀ γ s)) t :=
    mdifferentiableAt_chartCurve (I := I) hderiv htgt hstay
  refine hmd.congr_of_eventuallyEq ?_
  filter_upwards [hsrc] with s hs
  have hssrc : γ s ∈ (extChartAt I z₀).source := by rw [extChartAt_source]; exact hs
  exact ((extChartAt I z₀).left_inv hssrc).symm

/-- **The curve of the intrinsic family by geodesics is `MDifferentiableAt`.** -/
lemma mdifferentiableAt_GExp_fam (hmet : IsMetricCompatible cov)
    (D : ChartFlowData (cov := cov) (I := I) z₀ Z) {γ : ℝ → M} {x u : ℝ → E}
    {V : (t : ℝ) → TangentSpace I (γ t)} {σ s : ℝ} {R : Set (ℝ × ℝ)}
    (hR : IsOpen R) (hF : ContDiffOn ℝ ∞ (Fam (cov := cov) D x u) R) (h : (σ, s) ∈ R)
    (hγZ : ∀ᶠ s' in 𝓝 s, γ s' ∈ Z)
    (hγsrc : ∀ᶠ s' in 𝓝 s, γ s' ∈ (chartAt H z₀).source)
    (hxev : γ =ᶠ[𝓝 s] fun s' => (extChartAt I z₀).symm (x s'))
    (hph : ∀ᶠ s' in 𝓝 s, (x s', flowScale D • (σ • u s')) ∈ D.O)
    (hVev : V =ᶠ[𝓝 s] fun s' => frameVector (I := I) z₀ (γ s') (u s')) :
    MDifferentiableAt 𝓘(ℝ) I (fun s' : ℝ => GExp (cov := cov) hmet (γ s') (σ • V s')) s := by
  have hfam : HasDerivAt (fun s' : ℝ => fam (cov := cov) D x u σ s')
      (psiW (cov := cov) D x u σ s) s :=
    hasDerivAt_fam_snd (cov := cov) D hR hF h
  have htgt : fam (cov := cov) D x u σ s ∈ (extChartAt I z₀).target :=
    fam_mem_target' (cov := cov) D hph.self_of_nhds
  have hstay : ∀ᶠ s' in 𝓝 s, fam (cov := cov) D x u σ s' ∈ (extChartAt I z₀).target :=
    hph.mono (fun s' hs' => fam_mem_target' (cov := cov) D hs')
  have hmd1 : MDifferentiableAt 𝓘(ℝ) I
      (fun s' : ℝ => (extChartAt I z₀).symm (fam (cov := cov) D x u σ s')) s :=
    mdifferentiableAt_chartCurve (I := I) hfam htgt hstay
  refine hmd1.congr_of_eventuallyEq ?_
  filter_upwards [hVev, hγZ, hγsrc, hxev, hph] with s' hV hZ hs hx hp
  have hxtgt : x s' ∈ (extChartAt I z₀).target := (D.hOW hp).1
  have h1 : σ • V s' = σ • frameVector (I := I) z₀ (γ s') (u s') := by rw [hV]
  rw [h1, ← Submission.GExpSmooth.frameVector_smul']
  have hxeq : (extChartAt I z₀) (γ s') = x s' := by
    rw [hx]
    exact PartialEquiv.right_inv (extChartAt I z₀) hxtgt
  have hsrc : γ s' ∈ (extChartAt I z₀).source := by rw [extChartAt_source]; exact hs
  rw [← hxeq] at hp
  rw [GExp_eq_symm_Hfun (cov := cov) hmet D hZ hsrc hp, hxeq]
  rfl

/-- **Joint smoothness of the chart-coordinate family on a rectangle with an arbitrary anchor.** -/
theorem contDiffOn_fam_Ioo (D : ChartFlowData (cov := cov) (I := I) z₀ Z)
    {x u : ℝ → E} {δ A B : ℝ}
    (hx : ContDiffOn ℝ ∞ x (Ioo A B))
    (hu : ContDiffOn ℝ ∞ u (Ioo A B))
    (hph : ∀ σ ∈ Icc (-δ) δ, ∀ t ∈ Icc A B,
      (x t, flowScale D • (σ • u t)) ∈ chartData (I := I) z₀ Z) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => fam (cov := cov) D x u p.1 p.2)
      (Ioo (-δ) δ ×ˢ Ioo A B) := by
  intro p hp
  have hsub : Ioo A B ∈ 𝓝 p.2 := isOpen_Ioo.mem_nhds hp.2
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

set_option maxHeartbeats 4000000 in
/-- **The second variation of the energy of the intrinsic variation by geodesics, over a general
interval.** -/
theorem energy_second_deriv_piece (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (D : ChartFlowData (cov := cov) (I := I) z₀ Z)
    {γ : ℝ → M} {u : ℝ → E} {a b η : ℝ} (hab : a < b) (hη : 0 < η)
    (hγsrc : ∀ t ∈ Icc (a - η) (b + η), γ t ∈ (chartAt H z₀).source)
    (hγZ : ∀ t ∈ Icc (a - η) (b + η), γ t ∈ Z)
    (hx : ContDiffOn ℝ ∞ (chartCoord (I := I) z₀ γ) (Ioo (a - η) (b + η)))
    (hu : ContDiffOn ℝ ∞ u (Ioo (a - η) (b + η)))
    (hphase : ∀ σ ∈ Icc (-1 : ℝ) 1, ∀ t ∈ Icc (a - η) (b + η),
      (chartCoord (I := I) z₀ γ t, flowScale D • (σ • u t)) ∈ chartData (I := I) z₀ Z)
    (hgeoB : ∀ t ∈ Icc a b, HasDerivAt
      (fun t' : ℝ => psiW (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t')
      (chartGeodesicVectorField cov z₀ (chartCoord (I := I) z₀ γ t,
        psiW (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t)) t) :
    HasDerivAt (deriv (fun σ : ℝ => ∫ t in a..b,
        (curveSpeed (I := I) (fun s : ℝ => GExp (cov := cov) hmet (γ s)
          (σ • frameVector (I := I) z₀ (γ s) (u s))) t) ^ 2))
      (2 * ∫ t in a..b, idxAlong (cov := cov) γ
        (fun t : ℝ => frameVector (I := I) z₀ (γ t) (u t))
        (fun t : ℝ => frameVector (I := I) z₀ (γ t)
          (DtQ cov z₀ (chartCoord (I := I) z₀ γ) u (deriv (chartCoord (I := I) z₀ γ))
            (deriv u) t)) t) 0 := by
  classical
  set ℓ : ℝ := b - a with hℓdef
  have hℓ : 0 < ℓ := by rw [hℓdef]; linarith
  have hab' : a + ℓ = b := by rw [hℓdef]; ring
  set V : (t : ℝ) → TangentSpace I (γ t) := fun t => frameVector (I := I) z₀ (γ t) (u t)
    with hVdef
  set Zf : (t : ℝ) → TangentSpace I (γ t) := fun t => frameVector (I := I) z₀ (γ t)
    (DtQ cov z₀ (chartCoord (I := I) z₀ γ) u (deriv (chartCoord (I := I) z₀ γ))
      (deriv u) t) with hZdef
  set γ' : ℝ → M := fun t => γ (a + t) with hγ'def
  set u' : ℝ → E := fun t => u (a + t) with hu'def
  -- interval facts
  have hshift : ∀ t : ℝ, t ∈ Icc (-η) (ℓ + η) → a + t ∈ Icc (a - η) (b + η) := by
    intro t ht
    rw [hℓdef] at ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hshift0 : ∀ t : ℝ, t ∈ Icc (0 : ℝ) ℓ → a + t ∈ Icc (a - η) (b + η) :=
    fun t ht => hshift t ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hshiftII : ∀ t : ℝ, t ∈ Icc (0 : ℝ) ℓ → a + t ∈ Ioo (a - η) (b + η) := by
    intro t ht
    rw [hℓdef] at ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hshiftIoo2 : ∀ t : ℝ, t ∈ Ioo (-η) (ℓ + η) → a + t ∈ Ioo (a - η) (b + η) := by
    intro t ht
    rw [hℓdef] at ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hshiftIoo2c : ∀ t : ℝ, t ∈ Ioo (-η) (ℓ + η) → a + t ∈ Icc (a - η) (b + η) :=
    fun t ht => ⟨(hshiftIoo2 t ht).1.le, (hshiftIoo2 t ht).2.le⟩
  have hmid : ∀ t : ℝ, t ∈ Icc (0 : ℝ) ℓ → t ∈ Ioo (-η) (ℓ + η) := by
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  -- shifted hypotheses
  have hγsrc' : ∀ t ∈ Icc (-η) (ℓ + η), γ' t ∈ (chartAt H z₀).source :=
    fun t ht => hγsrc (a + t) (hshift t ht)
  have hγZ' : ∀ t ∈ Icc (-η) (ℓ + η), γ' t ∈ Z := fun t ht => hγZ (a + t) (hshift t ht)
  have hx' : ContDiffOn ℝ ∞ (chartCoord (I := I) z₀ γ') (Ioo (-η) (ℓ + η)) := by
    have h1 : chartCoord (I := I) z₀ γ' = (chartCoord (I := I) z₀ γ) ∘ (fun t : ℝ => a + t) := rfl
    rw [h1]
    refine hx.comp (contDiffOn_const.add contDiffOn_id) ?_
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hu'sm : ContDiffOn ℝ ∞ u' (Ioo (-η) (ℓ + η)) := by
    have h1 : u' = u ∘ (fun t : ℝ => a + t) := rfl
    rw [h1]
    refine hu.comp (contDiffOn_const.add contDiffOn_id) ?_
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hphase' : ∀ σ ∈ Icc (-1 : ℝ) 1, ∀ t ∈ Icc (-η) (ℓ + η),
      (chartCoord (I := I) z₀ γ' t, flowScale D • (σ • u' t)) ∈ chartData (I := I) z₀ Z :=
    fun σ hσ t ht => hphase σ hσ (a + t) (hshift t ht)
  -- the base geodesic equation in the shifted coordinates
  have hgeoB' : ∀ t ∈ Icc (0 : ℝ) ℓ, HasDerivAt
      (fun t' : ℝ => psiW (cov := cov) D (chartCoord (I := I) z₀ γ') u' 0 t')
      (chartGeodesicVectorField cov z₀ (chartCoord (I := I) z₀ γ' t,
        psiW (cov := cov) D (chartCoord (I := I) z₀ γ') u' 0 t)) t := by
    intro t ht
    have hII : a + t ∈ Ioo (a - η) (b + η) := hshiftII t ht
    have hmem : a + t ∈ Icc a b := by
      rw [← hab']
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    -- `psiW` at `σ = 0` is the derivative of the chart coordinate curve
    have hW' : (fun t' : ℝ => psiW (cov := cov) D (chartCoord (I := I) z₀ γ') u' 0 t')
        =ᶠ[𝓝 t] (fun t' : ℝ => deriv (chartCoord (I := I) z₀ γ) (a + t')) := by
      refine Filter.eventually_of_mem (isOpen_Ioo.mem_nhds (hmid t ht)) ?_
      intro t' ht'
      have h1 := psiW_zero (cov := cov) D (x := chartCoord (I := I) z₀ γ') (u := u') (t := t')
        (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ht')
          (fun s hs => ⟨γ (a + s), hγZ (a + s) (hshiftIoo2c s hs), rfl⟩))
      show psiW (cov := cov) D (chartCoord (I := I) z₀ γ') u' 0 t'
        = deriv (chartCoord (I := I) z₀ γ) (a + t')
      rw [h1]
      exact deriv_comp_const_add (chartCoord (I := I) z₀ γ) a t'
    have hWt : psiW (cov := cov) D (chartCoord (I := I) z₀ γ') u' 0 t
        = deriv (chartCoord (I := I) z₀ γ) (a + t) := hW'.eq_of_nhds
    rw [hWt]
    have hbase : HasDerivAt (fun t' : ℝ => psiW (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t')
        (chartGeodesicVectorField cov z₀ (chartCoord (I := I) z₀ γ (a + t),
          psiW (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 (a + t))) (a + t) := hgeoB (a + t) hmem
    have hWu : (fun t' : ℝ => psiW (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 t')
        =ᶠ[𝓝 (a + t)] (fun t' : ℝ => deriv (chartCoord (I := I) z₀ γ) t') := by
      refine Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hII) ?_
      intro t' ht'
      exact psiW_zero (cov := cov) D (x := chartCoord (I := I) z₀ γ) (u := u) (t := t')
        (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ht')
          (fun s hs => ⟨γ s, hγZ s ⟨hs.1.le, hs.2.le⟩, rfl⟩))
    have hbut : psiW (cov := cov) D (chartCoord (I := I) z₀ γ) u 0 (a + t)
        = deriv (chartCoord (I := I) z₀ γ) (a + t) := hWu.eq_of_nhds
    rw [hbut] at hbase
    have hbase' : HasDerivAt (fun t' : ℝ => deriv (chartCoord (I := I) z₀ γ) t')
        (chartGeodesicVectorField cov z₀ (chartCoord (I := I) z₀ γ (a + t),
          deriv (chartCoord (I := I) z₀ γ) (a + t))) (a + t) :=
      hbase.congr_of_eventuallyEq hWu.symm
    have h1 : HasDerivAt (fun t' : ℝ => a + t') 1 t := by
      have h0 : HasDerivAt ((fun _ : ℝ => a) + id) 1 t := by
        simpa using (hasDerivAt_const (x := t) a).add (hasDerivAt_id t)
      have h0' : ((fun _ : ℝ => a) + id) = fun t' : ℝ => a + t' := by
        funext t'; simp [Pi.add_apply]
      rwa [h0'] at h0
    have hcomp : HasDerivAt (fun t' : ℝ => deriv (chartCoord (I := I) z₀ γ) (a + t'))
        (chartGeodesicVectorField cov z₀ (chartCoord (I := I) z₀ γ (a + t),
          deriv (chartCoord (I := I) z₀ γ) (a + t))) t := by
      have hc := HasDerivAt.scomp t hbase' h1
      simpa only [Function.comp_def, one_smul] using hc
    exact hcomp.congr_of_eventuallyEq hW'
  have hmain := energy_second_deriv_fam_of_smooth_snd (cov := cov) hmet htor D
    (γ := γ') (u := u') (L := ℓ) (δ := 1) hℓ one_pos hη hγsrc' hγZ' hx' hu'sm hphase' hgeoB'
  have hF' : ContDiffOn ℝ ∞ (Fam (cov := cov) D (chartCoord (I := I) z₀ γ') u')
      (Rect (η := η) 1 ℓ) := contDiffOn_fam (cov := cov) D hx' hu'sm hphase'
  -- (1) the energy of the shifted family is the speed-squared integral
  have hE1 : energyFam (cov := cov) D (chartCoord (I := I) z₀ γ') u' ℓ
      =ᶠ[𝓝 (0 : ℝ)] (fun σ : ℝ => ∫ t in (0 : ℝ)..ℓ,
        (curveSpeed (I := I) (fun s : ℝ => GExp (cov := cov) hmet (γ' s)
          (σ • frameVector (I := I) z₀ (γ' s) (u' s))) t) ^ 2) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with σ hσ
    rw [Metric.mem_ball, dist_eq_norm, sub_zero, Real.norm_eq_abs, abs_lt] at hσ
    show (∫ t in (0 : ℝ)..ℓ, chartGram (I := I) z₀
        ((extChartAt I z₀).symm (Fam (cov := cov) D (chartCoord (I := I) z₀ γ') u' (σ, t)))
        (psiW (cov := cov) D (chartCoord (I := I) z₀ γ') u' σ t)
        (psiW (cov := cov) D (chartCoord (I := I) z₀ γ') u' σ t)) = _
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [uIcc_of_le hℓ.le] at ht
    have htI : t ∈ Ioo (-η) (ℓ + η) := hmid t ht
    exact (sq_curveSpeed_fam (cov := cov) hmet D (hR := isOpen_Rect η 1 ℓ) (hF := hF')
      (h := ⟨⟨by linarith [hσ], by linarith [hσ]⟩, htI⟩)
      (Filter.EventuallyEq.refl _ _)
      (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds htI)
        (fun s hs => hγZ (a + s) ⟨(hshiftIoo2 s hs).1.le, (hshiftIoo2 s hs).2.le⟩))
      (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds htI)
        (fun s hs => hγsrc (a + s) (hshiftIoo2c s hs)))
      (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds htI)
        (fun s hs => ((extChartAt I z₀).left_inv (by
          rw [extChartAt_source]; exact hγsrc (a + s) (hshiftIoo2c s hs))).symm))
      (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds htI)
        (fun s hs => D.hKO (hphase σ ⟨by linarith [hσ], by linarith [hσ]⟩ (a + s)
          (hshiftIoo2c s hs))))).symm
  -- (2) shift the integral back to `[a,b]`
  have hE2 : (fun σ : ℝ => ∫ t in (0 : ℝ)..ℓ,
        (curveSpeed (I := I) (fun s : ℝ => GExp (cov := cov) hmet (γ' s)
          (σ • frameVector (I := I) z₀ (γ' s) (u' s))) t) ^ 2)
      =ᶠ[𝓝 (0 : ℝ)] (fun σ : ℝ => ∫ t in a..b,
        (curveSpeed (I := I) (fun s : ℝ => GExp (cov := cov) hmet (γ s)
          (σ • frameVector (I := I) z₀ (γ s) (u s))) t) ^ 2) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with σ hσ
    rw [Metric.mem_ball, dist_eq_norm, sub_zero, Real.norm_eq_abs, abs_lt] at hσ
    have hcurve : (fun s : ℝ => GExp (cov := cov) hmet (γ' s)
          (σ • frameVector (I := I) z₀ (γ' s) (u' s)))
        = (fun s : ℝ => (fun y : ℝ => GExp (cov := cov) hmet (γ y)
            (σ • frameVector (I := I) z₀ (γ y) (u y))) (a + s)) := rfl
    rw [hcurve]
    have hpt : ∀ t ∈ Icc (0 : ℝ) ℓ, (curveSpeed (I := I) (fun s : ℝ => GExp (cov := cov) hmet
          (γ (a + s)) (σ • frameVector (I := I) z₀ (γ (a + s)) (u (a + s)))) t) ^ 2
        = (curveSpeed (I := I) (fun y : ℝ => GExp (cov := cov) hmet (γ y)
            (σ • frameVector (I := I) z₀ (γ y) (u y))) (a + t)) ^ 2 := by
      intro t ht
      have hII : a + t ∈ Ioo (a - η) (b + η) := hshiftII t ht
      rw [curveSpeed_comp_add_left (I := I) (fun y : ℝ => GExp (cov := cov) hmet (γ y)
        (σ • frameVector (I := I) z₀ (γ y) (u y))) a t ?_]
      exact mdifferentiableAt_GExp_fam (cov := cov) hmet D
        (hR := isOpen_Ioo.prod isOpen_Ioo)
        (hF := contDiffOn_fam_Ioo (cov := cov) D hx hu
          (fun σ' hσ' s hs => hphase σ' hσ' s hs))
        (h := ⟨⟨by linarith [hσ], by linarith [hσ]⟩, hII⟩)
        (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hII)
          (fun s hs => hγZ s ⟨hs.1.le, hs.2.le⟩))
        (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hII)
          (fun s hs => hγsrc s ⟨hs.1.le, hs.2.le⟩))
        (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hII)
          (fun s hs => ((extChartAt I z₀).left_inv (by
            rw [extChartAt_source]; exact hγsrc s ⟨hs.1.le, hs.2.le⟩)).symm))
        (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hII)
          (fun s hs => D.hKO (hphase σ ⟨by linarith [hσ], by linarith [hσ]⟩ s
            ⟨hs.1.le, hs.2.le⟩)))
        (Filter.EventuallyEq.refl _ _)
    rw [intervalIntegral.integral_congr
        (fun t ht => hpt t (by rwa [uIcc_of_le hℓ.le] at ht))]
    have hcomp := intervalIntegral.integral_comp_add_left (a := (0 : ℝ)) (b := ℓ) (d := a)
      (f := fun y : ℝ => (curveSpeed (I := I) (fun s : ℝ => GExp (cov := cov) hmet (γ s)
        (σ • frameVector (I := I) z₀ (γ s) (u s))) y) ^ 2)
    rw [hcomp, add_zero, hab']
  -- (3) the shifted `Z` field is the translate of `Zf`
  have hZshift : (fun t : ℝ => frameVector (I := I) z₀ (γ' t)
        (DtQ cov z₀ (chartCoord (I := I) z₀ γ') u' (deriv (chartCoord (I := I) z₀ γ'))
          (deriv u') t)) = (fun t : ℝ => Zf (a + t)) := by
    funext t
    show frameVector (I := I) z₀ (γ (a + t))
      (DtQ cov z₀ (chartCoord (I := I) z₀ γ') u' (deriv (chartCoord (I := I) z₀ γ'))
        (deriv u') t) = Zf (a + t)
    congr 1
    have hderivx : deriv (chartCoord (I := I) z₀ γ')
        = fun t : ℝ => deriv (chartCoord (I := I) z₀ γ) (a + t) :=
      funext (fun t => deriv_comp_const_add (chartCoord (I := I) z₀ γ) a t)
    have hderivu : deriv u' = fun t : ℝ => deriv u (a + t) :=
      funext (fun t => deriv_comp_const_add u a t)
    show DtQ cov z₀ (chartCoord (I := I) z₀ γ') u' (deriv (chartCoord (I := I) z₀ γ'))
        (deriv u') t
      = DtQ cov z₀ (chartCoord (I := I) z₀ γ) u (deriv (chartCoord (I := I) z₀ γ))
        (deriv u) (a + t)
    rw [hderivx, hderivu]
    rfl
  -- (4) the index integrand of the shifted family is minus the intrinsic one
  have hkey : ∀ t ∈ Icc (0 : ℝ) ℓ,
      indexIntegrand (I := I) cov z₀
        (fun s : ℝ => fam (cov := cov) D (chartCoord (I := I) z₀ γ') u' 0 s)
        (fun s : ℝ => psiV (cov := cov) D (chartCoord (I := I) z₀ γ') u' 0 s)
        (fun s : ℝ => psiW (cov := cov) D (chartCoord (I := I) z₀ γ') u' 0 s)
        (fun s : ℝ => psiE (cov := cov) D (chartCoord (I := I) z₀ γ') u' 0 s) t
      = - idxAlong (cov := cov) γ V Zf (a + t) := by
    intro t ht
    have htI : t ∈ Ioo (-η) (ℓ + η) := hmid t ht
    have hII : a + t ∈ Ioo (a - η) (b + η) := hshiftII t ht
    -- the phase at `σ = 1` and `σ = 0`
    have hO1 : (chartCoord (I := I) z₀ γ (a + t), flowScale D • u (a + t)) ∈ D.O :=
      D.hKO (by
        have hp := hphase 1 ⟨by norm_num, by norm_num⟩ (a + t) ⟨hII.1.le, hII.2.le⟩
        rwa [one_smul] at hp)
    have hO0 : (chartCoord (I := I) z₀ γ (a + t), (0 : E)) ∈ D.O :=
      D.hKO (by
        have hp := hphase 0 ⟨by norm_num, by norm_num⟩ (a + t) ⟨hII.1.le, hII.2.le⟩
        rwa [zero_smul, smul_zero] at hp)
    have hO1' : (chartCoord (I := I) z₀ γ' t, flowScale D • u' t) ∈ D.O := hO1
    have hO0' : (chartCoord (I := I) z₀ γ' t, (0 : E)) ∈ D.O := hO0
    have hpsiVt : psiV (cov := cov) D (chartCoord (I := I) z₀ γ') u' 0 t = u' t :=
      psiV_zero (cov := cov) D hO1' hO0'
    -- the eventual phase conditions
    have hO1ev : ∀ᶠ s in 𝓝 t, (chartCoord (I := I) z₀ γ' s, flowScale D • u' s) ∈ D.O :=
      Filter.eventually_of_mem (isOpen_Ioo.mem_nhds htI) (fun s hs =>
        D.hKO (by
          have hp := hphase 1 ⟨by norm_num, by norm_num⟩ (a + s) (hshiftIoo2c s hs)
          rwa [one_smul] at hp))
    have hO0ev : ∀ᶠ s in 𝓝 t, (chartCoord (I := I) z₀ γ' s, (0 : E)) ∈ D.O :=
      Filter.eventually_of_mem (isOpen_Ioo.mem_nhds htI) (fun s hs =>
        D.hKO (by
          have hp := hphase 0 ⟨by norm_num, by norm_num⟩ (a + s) (hshiftIoo2c s hs)
          rwa [zero_smul, smul_zero] at hp))
    -- identification of the fields
    have hVid : frameVector (I := I) z₀ (γ' t) (u' t)
        = frameVector (I := I) z₀ (γ' t)
          (psiV (cov := cov) D (chartCoord (I := I) z₀ γ') u' 0 t) := by
      rw [hpsiVt]
    have hZid : frameVector (I := I) z₀ (γ' t)
          (DtQ cov z₀ (chartCoord (I := I) z₀ γ') u' (deriv (chartCoord (I := I) z₀ γ'))
            (deriv u') t)
        = frameVector (I := I) z₀ (γ' t)
          (DtQ cov z₀ (chartCoord (I := I) z₀ γ')
            (fun s : ℝ => psiV (cov := cov) D (chartCoord (I := I) z₀ γ') u' 0 s)
            (fun s : ℝ => psiW (cov := cov) D (chartCoord (I := I) z₀ γ') u' 0 s)
            (fun s : ℝ => psiE (cov := cov) D (chartCoord (I := I) z₀ γ') u' 0 s) t) := by
      congr 1
      have hpsiVev : (fun s : ℝ => psiV (cov := cov) D (chartCoord (I := I) z₀ γ') u' 0 s)
          =ᶠ[𝓝 t] u' := by
        refine Filter.eventually_of_mem (isOpen_Ioo.mem_nhds htI) ?_
        intro s hs
        exact psiV_zero (cov := cov) D
          (D.hKO (by
            have hp := hphase 1 ⟨by norm_num, by norm_num⟩ (a + s) (hshiftIoo2c s hs)
            rwa [one_smul] at hp))
          (D.hKO (by
            have hp := hphase 0 ⟨by norm_num, by norm_num⟩ (a + s) (hshiftIoo2c s hs)
            rwa [zero_smul, smul_zero] at hp))
      refine DtQ_congr (cov := cov) (x₀ := z₀) (t := t) rfl hpsiVt.symm ?_ ?_
      · exact (psiW_zero (cov := cov) D (x := chartCoord (I := I) z₀ γ') (u := u') (t := t)
          (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds htI)
            (fun s hs => ⟨γ (a + s), hγZ (a + s) (hshiftIoo2c s hs), rfl⟩))).symm
      · exact (psiE_zero (cov := cov) D (hR := isOpen_Rect η 1 ℓ) (hF := hF')
          (h := ⟨⟨by linarith [htI.1], by linarith [htI.2]⟩, htI⟩)
          (hVz := hpsiVev)).symm
    have hid := idxAlong_eq_neg_indexIntegrand (cov := cov) htor z₀ (γ := γ')
      (u := fun s : ℝ => fam (cov := cov) D (chartCoord (I := I) z₀ γ') u' 0 s)
      (w := fun s : ℝ => psiW (cov := cov) D (chartCoord (I := I) z₀ γ') u' 0 s)
      (η := fun s : ℝ => psiV (cov := cov) D (chartCoord (I := I) z₀ γ') u' 0 s)
      (e := fun s : ℝ => psiE (cov := cov) D (chartCoord (I := I) z₀ γ') u' 0 s)
      (V := fun s : ℝ => frameVector (I := I) z₀ (γ' s) (u' s))
      (Z := fun s : ℝ => frameVector (I := I) z₀ (γ' s)
        (DtQ cov z₀ (chartCoord (I := I) z₀ γ') u' (deriv (chartCoord (I := I) z₀ γ'))
          (deriv u') s)) (t := t)
      (hsrc := hγsrc (a + t) ⟨hII.1.le, hII.2.le⟩)
      (hstay := Filter.eventually_of_mem (isOpen_Ioo.mem_nhds htI) (fun s hs =>
        fam_mem_target' (cov := cov) D
          (D.hKO (hphase 0 ⟨by norm_num, by norm_num⟩ (a + s) (hshiftIoo2c s hs)))))
      (hγeq := Filter.eventually_of_mem (isOpen_Ioo.mem_nhds htI) (fun s hs => by
        have hsrc : γ' s ∈ (extChartAt I z₀).source := by
          rw [extChartAt_source]
          exact hγsrc (a + s) (hshiftIoo2c s hs)
        have hfam0 : fam (cov := cov) D (chartCoord (I := I) z₀ γ') u' 0 s
            = chartCoord (I := I) z₀ γ' s := by
          show Hfun D (chartCoord (I := I) z₀ γ' s, (0 : ℝ) • u' s)
            = chartCoord (I := I) z₀ γ' s
          rw [zero_smul]
          exact Hfun_zero (cov := cov) D
            ⟨⟨γ' s, hγZ (a + s) (hshiftIoo2c s hs), rfl⟩, by simp [Metric.mem_closedBall]⟩
        show γ' s = (extChartAt I z₀).symm
          (fam (cov := cov) D (chartCoord (I := I) z₀ γ') u' 0 s)
        rw [hfam0]
        exact (PartialEquiv.left_inv (extChartAt I z₀) hsrc).symm))
      (hu := Filter.eventually_of_mem (isOpen_Ioo.mem_nhds htI)
        (fun s hs => hasDerivAt_fam_snd (cov := cov) D (isOpen_Rect η 1 ℓ) hF'
          ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩, hs⟩))
      (hγmd := mdifferentiableAt_of_contDiffOn_chartCoord (I := I) (z₀ := z₀) (γ := γ')
        (A := -η) (B := ℓ + η) hx' htI
        (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds htI)
          (fun s hs => hγsrc (a + s) (hshiftIoo2c s hs))))
      (hV := hVid) (hZ := by
        have hfampt : (fun s : ℝ => fam (cov := cov) D (chartCoord (I := I) z₀ γ') u' 0 s) t
            = chartCoord (I := I) z₀ γ' t := by
          show Hfun D (chartCoord (I := I) z₀ γ' t, (0 : ℝ) • u' t)
            = chartCoord (I := I) z₀ γ' t
          rw [zero_smul]
          exact Hfun_zero (cov := cov) D
            ⟨⟨γ' t, hγZ (a + t) ⟨hII.1.le, hII.2.le⟩, rfl⟩,
              by simp [Metric.mem_closedBall]⟩
        have hZid2 := hZid.trans (congrArg (fun z => frameVector (I := I) z₀ (γ' t) z)
          (DtQ_congr (cov := cov) (x₀ := z₀) (t := t) hfampt rfl rfl rfl).symm)
        exact hZid2)
    have h2 : idxAlong (cov := cov) γ' (fun s : ℝ => frameVector (I := I) z₀ (γ' s) (u' s))
        (fun s : ℝ => frameVector (I := I) z₀ (γ' s)
          (DtQ cov z₀ (chartCoord (I := I) z₀ γ') u' (deriv (chartCoord (I := I) z₀ γ'))
            (deriv u') s)) t = idxAlong (cov := cov) γ V Zf (a + t) := by
      rw [hZshift]
      exact idxAlong_comp_add (cov := cov) γ V Zf a t
        (mdifferentiableAt_of_contDiffOn_chartCoord (I := I) (z₀ := z₀) (γ := γ)
          (A := a - η) (B := b + η) hx hII
          (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hII)
            (fun s hs => hγsrc s ⟨hs.1.le, hs.2.le⟩)))
    have h3 : - indexIntegrand (I := I) cov z₀
        (fun s : ℝ => fam (cov := cov) D (chartCoord (I := I) z₀ γ') u' 0 s)
        (fun s : ℝ => psiV (cov := cov) D (chartCoord (I := I) z₀ γ') u' 0 s)
        (fun s : ℝ => psiW (cov := cov) D (chartCoord (I := I) z₀ γ') u' 0 s)
        (fun s : ℝ => psiE (cov := cov) D (chartCoord (I := I) z₀ γ') u' 0 s) t
        = idxAlong (cov := cov) γ V Zf (a + t) := by
      rw [← hid, h2]
    exact neg_eq_iff_eq_neg.mp h3
  -- (5) the integral of the index integrand
  have hI : (∫ t in (0 : ℝ)..ℓ, indexIntegrand (I := I) cov z₀
        (fun s : ℝ => fam (cov := cov) D (chartCoord (I := I) z₀ γ') u' 0 s)
        (fun s : ℝ => psiV (cov := cov) D (chartCoord (I := I) z₀ γ') u' 0 s)
        (fun s : ℝ => psiW (cov := cov) D (chartCoord (I := I) z₀ γ') u' 0 s)
        (fun s : ℝ => psiE (cov := cov) D (chartCoord (I := I) z₀ γ') u' 0 s) t)
      = -(∫ t in a..b, idxAlong (cov := cov) γ V Zf t) := by
    rw [intervalIntegral.integral_congr
      (fun t ht => hkey t (by rwa [uIcc_of_le hℓ.le] at ht))]
    rw [intervalIntegral.integral_neg]
    have hcomp := intervalIntegral.integral_comp_add_left (a := (0 : ℝ)) (b := ℓ) (d := a)
      (f := fun y : ℝ => idxAlong (cov := cov) γ V Zf y)
    rw [hcomp, add_zero, hab']
  have h := hmain
  rw [hI] at h
  have hdereq : deriv (energyFam (cov := cov) D (chartCoord (I := I) z₀ γ') u' ℓ)
      =ᶠ[𝓝 (0 : ℝ)] deriv (fun σ : ℝ => ∫ t in a..b,
        (curveSpeed (I := I) (fun s : ℝ => GExp (cov := cov) hmet (γ s)
          (σ • frameVector (I := I) z₀ (γ s) (u s))) t) ^ 2) :=
    ((hE1.trans hE2).deriv)
  refine (h.congr_of_eventuallyEq hdereq.symm).congr_deriv ?_
  ring

/-! ## The assembly over a finite partition -/

section Cover

/-- **The second variation of the energy, assembled over a finite partition.**  If a function
`σ ↦ ∫ t in 0..L, F σ t` is, on each piece of the partition `[0,L] = ⋃_k [c k, c (k+1)]`, the energy
of a variation whose second variation at `0` is `2 ∫ idxAlong γ V Z` over that piece, then the *whole*
function has second variation `2 ∫_0^L idxAlong γ V Z` at `0`, and first variation `0`.

The point is that the integrand `idxAlong γ V Z` is **intrinsic** (it does not depend on the chart used
on the piece), so the piece integrals simply add up — no telescoping, no boundary terms.  This is the
bookkeeping layer of the global `σ ≤ κ` (Roadmap §100.5): the per-piece data is produced by
`Submission.SecondVarGlobal.energy_second_deriv_piece` (energy side) and by the cover lemmas of
`Submission.IndexIntrinsic2`/`IndexIntrinsic3` (index side). -/
theorem energy_second_deriv_cover
    {γ : ℝ → M} {V Z : (t : ℝ) → TangentSpace I (γ t)} {L : ℝ}
    {N : ℕ} {c : ℕ → ℝ} {F : ℝ → ℝ → ℝ}
    (hc0 : c 0 = 0) (hcN : c N = L)
    (hint : ∀ (σ : ℝ) (k : ℕ), k < N → IntervalIntegrable (fun t : ℝ => F σ t) volume
      (c k) (c (k + 1)))
    (hintZ : ∀ k : ℕ, k < N → IntervalIntegrable (fun t : ℝ => idxAlong (cov := cov) γ V Z t)
      volume (c k) (c (k + 1)))
    (hk : ∀ k : ℕ, k < N →
      (∀ᶠ σ in 𝓝 (0 : ℝ),
        DifferentiableAt ℝ (fun σ : ℝ => ∫ t in c k..c (k + 1), F σ t) σ) ∧
      HasDerivAt (deriv (fun σ : ℝ => ∫ t in c k..c (k + 1), F σ t))
        (2 * ∫ t in c k..c (k + 1), idxAlong (cov := cov) γ V Z t) 0) :
    HasDerivAt (deriv (fun σ : ℝ => ∫ t in (0 : ℝ)..L, F σ t))
      (2 * ∫ t in (0 : ℝ)..L, idxAlong (cov := cov) γ V Z t) 0 ∧
    DifferentiableAt ℝ (fun σ : ℝ => ∫ t in (0 : ℝ)..L, F σ t) 0 := by
  classical
  -- the sum decomposition of the whole energy
  have hsum : (fun σ : ℝ => ∫ t in (0 : ℝ)..L, F σ t)
      = fun σ : ℝ => ∑ k ∈ Finset.range N, ∫ t in c k..c (k + 1), F σ t := by
    funext σ
    have h := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
      (f := fun t : ℝ => F σ t) (a := c) (n := N) (fun k hk' => hint σ k hk')
    rw [hc0, hcN] at h
    exact h.symm
  -- the derivative of the sum is the sum of the derivatives, near `0`
  have hdiff : ∀ᶠ σ in 𝓝 (0 : ℝ), ∀ k ∈ Finset.range N,
      DifferentiableAt ℝ (fun σ : ℝ => ∫ t in c k..c (k + 1), F σ t) σ := by
    rw [Finset.eventually_all]
    intro k hk'
    exact (hk k (Finset.mem_range.mp hk')).1
  have hderiv : deriv (fun σ : ℝ => ∑ k ∈ Finset.range N, ∫ t in c k..c (k + 1), F σ t)
      =ᶠ[𝓝 (0 : ℝ)] (fun σ : ℝ => ∑ k ∈ Finset.range N,
        deriv (fun σ : ℝ => ∫ t in c k..c (k + 1), F σ t) σ) := by
    filter_upwards [hdiff] with σ hσ
    exact deriv_fun_sum hσ
  have hsecond : HasDerivAt (fun σ : ℝ => ∑ k ∈ Finset.range N,
      deriv (fun σ : ℝ => ∫ t in c k..c (k + 1), F σ t) σ)
      (∑ k ∈ Finset.range N, 2 * ∫ t in c k..c (k + 1), idxAlong (cov := cov) γ V Z t) 0 :=
    HasDerivAt.fun_sum (fun k hk' => (hk k (Finset.mem_range.mp hk')).2)
  have hsecond' : HasDerivAt (deriv (fun σ : ℝ => ∑ k ∈ Finset.range N,
      ∫ t in c k..c (k + 1), F σ t))
      (∑ k ∈ Finset.range N, 2 * ∫ t in c k..c (k + 1), idxAlong (cov := cov) γ V Z t) 0 :=
    hsecond.congr_of_eventuallyEq hderiv
  -- differentiability at `0` of the sum
  have hdiff0 : DifferentiableAt ℝ (fun σ : ℝ => ∑ k ∈ Finset.range N,
      ∫ t in c k..c (k + 1), F σ t) 0 :=
    DifferentiableAt.fun_sum (fun k hk' => (hk k (Finset.mem_range.mp hk')).1.self_of_nhds)
  -- the sum of the index integrals
  have hZsum : (∑ k ∈ Finset.range N, ∫ t in c k..c (k + 1), idxAlong (cov := cov) γ V Z t)
      = ∫ t in (0 : ℝ)..L, idxAlong (cov := cov) γ V Z t := by
    have h := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
      (f := fun t : ℝ => idxAlong (cov := cov) γ V Z t) (a := c) (n := N) hintZ
    rwa [hc0, hcN] at h
  refine ⟨?_, ?_⟩
  · have h2 := hsecond'
    rw [← Finset.mul_sum, hZsum] at h2
    exact h2.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq hsum).deriv
  · rw [hsum]
    exact hdiff0

end Cover

end

end Submission.SecondVarGlobal
