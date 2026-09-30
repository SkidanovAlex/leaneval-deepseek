import Submission.Work.RiemLib.EnergyRay
import Submission.Work.RiemLib.Commons.Analysis.Calculus.eventually_differentiableAt_integral_of_contDiffOn
import Submission.Work.RiemLib.Commons.Analysis.Calculus.eventually_differentiableAt_integral_of_continuousOn
import Submission.Work.RiemLib.SmoothFieldCover
import Submission.Work.RiemLib.GExpPieceData
import Submission.Work.RiemLib.LensLoop

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory
open Submission.Geodesic
open Submission.Jacobi
open Submission.ChartCurv
open Submission.Rauch
open Submission.RauchGlobal
open Submission.GExpFlow
open Submission.JacobiCoords
open Submission.IntrinsicVariation
open Submission.SecondVarGlobal
open Submission.IndexIntrinsic
open Submission.IndexIntrinsic2
open Submission.JacobiGlobal
open Submission.IndexScale
open Submission.BonnetMyers
open Submission.IndexCorner2
open Submission.GlobalExp
open Submission.GeodesicSpeed
open Submission.Length
open Submission.ChartConnection
open Submission.LensLoop
open Submission.EnergyRay
open Submission.SecondVarGeo

/-!
# The per-piece second variation of the energy along a `GExp`-ray

Roadmap §102.6 (i).  `Submission.EnergyRay.energy_second_deriv_piece_scaled` gives, for **one** chart
piece with the `C^∞` data of the curve and of the field, a scale `c₀ > 0` below which the family
`Φ(σ,t) = GExp (γ t) (σ • (c • V t))` satisfies `E''(0) = 2 ∫ idxAlong γ (c • V) (∇(c • V))`.

This module runs that along the finite chart cover of `Submission.SmoothFieldCover`, using
`Z k := γ '' Icc (S k) (E k)` (compact, by continuity of the ray on the local interval),
`D k` from `GExpPieceData`'s producer `exists_chartFlowData`, and `hgeoB k` from
`GExpPieceData.hasDerivAt_psiW_GExp` — and takes the **minimum** of the finitely many `c₀ k`.
-/

namespace Submission.EnergyRayCover

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

/-- **A `GExp`-ray has nonvanishing velocity everywhere** (at `0` the velocity is `ξ` itself). -/
lemma curveVelocity_GExp_smul_ne_zero (hmet : IsMetricCompatible cov) {p : M}
    {ξ : TangentSpace I p} (hξ : ξ ≠ 0) (t : ℝ) :
    curveVelocity (I := I) (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ)) t ≠ 0 := by
  rcases eq_or_ne t 0 with h | h
  · subst h
    rw [Submission.GExpVelocity.curveVelocity_GExp_smul_zero (cov := cov) hmet p hξ]
    exact hξ
  · intro h0
    have hnorm := norm_curveVelocity_GExp_smul_ne (cov := cov) hmet p hξ h
    rw [h0, norm_zero] at hnorm
    exact hξ (norm_eq_zero.mp hnorm.symm)

/-! ## The pointwise identification of the piece energy with the chart integral

Roadmap §102.6 (ii-bis), step 1: on a chart piece, the square of the speed of the family
`Φ(σ,·) = GExp (γ ·) (σ • V ·)` is the chart expression `chartGram (γ t) (psiW) (psiW)`.  This is
`Submission.SecondVarGlobal.sq_curveSpeed_fam` applied pointwise, in the mould of the `hE1` step of
`energy_second_deriv_piece`; the integral identity for `σ ∈ Ioo (-δ) δ` follows by
`intervalIntegral.integral_congr`. -/

/-- **The piece energy is the chart integral**, for `σ` in the small interval. -/
lemma integral_curveSpeed_eq_chart (hmet : IsMetricCompatible cov)
    {γ : ℝ → M} {V : (t : ℝ) → TangentSpace I (γ t)} {z : M} {Z : Set M}
    (D : ChartFlowData (cov := cov) (I := I) z Z)
    {S T c₀ c₁ δ : ℝ} (hS : S < c₀) (hT : c₁ < T) (hlo : c₀ ≤ c₁)
    (hsrc : ∀ t ∈ Icc S T, γ t ∈ (chartAt H z).source)
    (hcdU : ContDiffOn ℝ ∞ (chartCoord (I := I) z γ) (Icc S T))
    (hcdV : ContDiffOn ℝ ∞ (chartCoords (I := I) z γ V) (Icc S T))
    (hVfr : ∀ t ∈ Icc S T, frameVector (I := I) z (γ t) (chartCoords (I := I) z γ V t) = V t)
    (hZev : ∀ t ∈ Ioo S T, ∀ᶠ s in 𝓝 t, γ s ∈ Z)
    (hphase : ∀ σ ∈ Icc (-δ) δ, ∀ t ∈ Icc S T,
      (chartCoord (I := I) z γ t, flowScale D • (σ • chartCoords (I := I) z γ V t))
        ∈ chartData (I := I) z Z) :
    ∀ σ ∈ Ioo (-δ) δ, ∫ t in c₀..c₁,
        (curveSpeed (I := I) (fun s : ℝ => GExp (cov := cov) hmet (γ s) (σ • V s)) t) ^ 2
      = ∫ t in c₀..c₁, chartGram (I := I) z
          ((extChartAt I z).symm (fam (cov := cov) D (chartCoord (I := I) z γ)
            (chartCoords (I := I) z γ V) σ t))
          (psiW (cov := cov) D (chartCoord (I := I) z γ) (chartCoords (I := I) z γ V) σ t)
          (psiW (cov := cov) D (chartCoord (I := I) z γ) (chartCoords (I := I) z γ V) σ t) := by
  intro σ hσ
  have hδle : σ ∈ Icc (-δ) δ := ⟨hσ.1.le, hσ.2.le⟩
  have hIo : IsOpen (Ioo S T) := isOpen_Ioo
  have hR : IsOpen (Ioo (-δ) δ ×ˢ Ioo S T) := isOpen_Ioo.prod isOpen_Ioo
  have hFcd : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => fam (cov := cov) D (chartCoord (I := I) z γ)
      (chartCoords (I := I) z γ V) p.1 p.2) (Ioo (-δ) δ ×ˢ Ioo S T) :=
    Submission.SecondVarGlobal.contDiffOn_fam_Ioo (cov := cov) D
      (hcdU.mono (fun t ht => ⟨ht.1.le, ht.2.le⟩))
      (hcdV.mono (fun t ht => ⟨ht.1.le, ht.2.le⟩)) hphase
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  rw [uIcc_of_le hlo] at ht
  have htI : t ∈ Ioo S T := ⟨by linarith [ht.1, hS], by linarith [ht.2, hT]⟩
  have hsrcev : ∀ᶠ s in 𝓝 t, γ s ∈ (chartAt H z).source := by
    filter_upwards [hIo.mem_nhds htI] with s hs
    exact hsrc s ⟨hs.1.le, hs.2.le⟩
  have hγeqev : γ =ᶠ[𝓝 t] fun s => (extChartAt I z).symm (chartCoord (I := I) z γ s) := by
    filter_upwards [hsrcev] with s hs
    exact (PartialEquiv.left_inv (extChartAt I z) (by rwa [extChartAt_source])).symm
  have hphev : ∀ᶠ s in 𝓝 t,
      (chartCoord (I := I) z γ s, flowScale D • (σ • chartCoords (I := I) z γ V s)) ∈ D.O := by
    filter_upwards [hIo.mem_nhds htI] with s hs
    exact D.hKO (hphase σ hδle s ⟨hs.1.le, hs.2.le⟩)
  have hVev : V =ᶠ[𝓝 t] (fun s => frameVector (I := I) z (γ s) (chartCoords (I := I) z γ V s)) := by
    filter_upwards [hIo.mem_nhds htI] with s hs
    exact (hVfr s ⟨hs.1.le, hs.2.le⟩).symm
  have hcurve : (fun s : ℝ => GExp (cov := cov) hmet (γ s) (σ • V s))
      =ᶠ[𝓝 t] (fun s : ℝ => GExp (cov := cov) hmet (γ s)
        (σ • frameVector (I := I) z (γ s) (chartCoords (I := I) z γ V s))) := by
    filter_upwards [hVev] with s hs
    rw [hs]
  rw [curveSpeed_congr_of_eventuallyEq (I := I) hcurve]
  exact Submission.SecondVarGlobal.sq_curveSpeed_fam (cov := cov) hmet D hR hFcd ⟨hσ, htI⟩
    (V := fun s => frameVector (I := I) z (γ s) (chartCoords (I := I) z γ V s))
    (Filter.EventuallyEq.refl _ _) (hZev t htI) hsrcev hγeqev hphev


/-! ## Continuity of the intrinsic index integrand on a piece (the `hintZ` hypothesis)

Roadmap §102.6: the last hypothesis of `EnergyCover.energy_second_deriv_cover_eventually`.  On a
chart piece, `idxAlong γ (d • V) (covAlong cov (d • V))` is the chart integrand
`- indexIntegrand`, whose continuity is `IndexIntrinsic2.continuousOn_idxAlong_weak`; the chart data
is the one already carried by the cover (`chartCoord z γ`, `chartCoords z γ V`), and the `∇`-slot is
identified by `covAlong_eq_chart_of_data`. -/

/-- **Continuity of the intrinsic index integrand on a piece.** -/
lemma continuousOn_idxAlong_piece (htor : cov.torsion = 0)
    {γ : ℝ → M} {V : (t : ℝ) → TangentSpace I (γ t)} {z : M} {Z : Set M}
    (D : ChartFlowData (cov := cov) (I := I) z Z)
    {S T ck ck1 : ℝ} (hS : S < ck) (hT : ck1 < T) (hlo : ck ≤ ck1)
    (hsrc : ∀ t ∈ Icc S T, γ t ∈ (chartAt H z).source)
    (hcdU : ContDiffOn ℝ ∞ (chartCoord (I := I) z γ) (Icc S T))
    (hcdV : ContDiffOn ℝ ∞ (chartCoords (I := I) z γ V) (Icc S T))
    (hVfr : ∀ t ∈ Icc S T, frameVector (I := I) z (γ t) (chartCoords (I := I) z γ V t) = V t)
    (hγ1 : ∀ t ∈ Icc S T, ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo (t - 1) (t + 1)))
    (hne : ∀ t ∈ Icc S T, curveVelocity (I := I) γ t ≠ 0)
    (hVs : ∀ t ∈ Icc S T, SmoothAlongAt (I := I) γ V t) (d : ℝ) :
    ContinuousOn (fun t : ℝ => idxAlong (cov := cov) γ (fun s => d • V s)
      (covAlong cov (fun s => d • V s)) t) (Icc ck ck1) := by
  set u : ℝ → E := chartCoord (I := I) z γ with hudef
  set J : ℝ → E := chartCoords (I := I) z γ (fun s => d • V s) with hJdef
  set w : ℝ → E := deriv u with hwdef
  set J' : ℝ → E := deriv J with hJ'def
  have hcdVs : ContDiffOn ℝ ∞ J (Icc S T) := by
    rw [hJdef, chartCoords_smul]
    exact hcdV.const_smul d
  have hVfrs : ∀ t ∈ Icc S T, frameVector (I := I) z (γ t) (J t) = (fun s => d • V s) t := by
    intro t ht
    rw [hJdef, chartCoords_smul]
    show frameVector (I := I) z (γ t) (d • chartCoords (I := I) z γ V t) = d • V t
    rw [frameVector_smul, hVfr t ht]
  have hUo : ContDiffOn ℝ ∞ u (Ioo S T) :=
    hcdU.mono (fun t ht => ⟨ht.1.le, ht.2.le⟩)
  have hJo : ContDiffOn ℝ ∞ J (Ioo S T) :=
    hcdVs.mono (fun t ht => ⟨ht.1.le, ht.2.le⟩)
  -- the enlarged piece, still inside the open local interval
  set η : ℝ := min (ck - S) (T - ck1) / 2 with hηdef
  have hηpos : 0 < η := by
    rw [hηdef]
    exact div_pos (lt_min (by linarith) (by linarith)) two_pos
  have h2η1 : 2 * η ≤ ck - S := by
    rw [hηdef]; have h := min_le_left (ck - S) (T - ck1); linarith
  have h2η2 : 2 * η ≤ T - ck1 := by
    rw [hηdef]; have h := min_le_right (ck - S) (T - ck1); linarith
  have hηs1 : S < ck - η := by linarith [h2η1, hηpos]
  have hηs2 : ck1 + η < T := by linarith [h2η2, hηpos]
  have hsub : Icc (ck - η) (ck1 + η) ⊆ Icc S T := by
    intro t ht
    exact ⟨by linarith [ht.1, hηs1], by linarith [ht.2, hηs2]⟩
  have hsubU : Icc (ck - η) (ck1 + η) ⊆ Ioo S T :=
    fun t ht => ⟨by linarith [ht.1, hηs1], by linarith [ht.2, hηs2]⟩
  -- the chart data of `continuousOn_idxAlong_weak`
  have hγeq : ∀ t ∈ Icc (ck - η) (ck1 + η), γ t = (extChartAt I z).symm (u t) := by
    intro t ht
    have hst : γ t ∈ (chartAt H z).source := hsrc t (hsub ht)
    rw [hudef]
    show γ t = (extChartAt I z).symm ((extChartAt I z) (γ t))
    exact (PartialEquiv.left_inv (extChartAt I z) (by rwa [extChartAt_source])).symm
  have hu : ∀ t ∈ Icc (ck - η) (ck1 + η), HasDerivAt u (w t) t := by
    intro t ht
    rw [hudef, hwdef]
    exact (Submission.JacobiGlobal.eventually_hasDerivAt_of_contDiffOn isOpen_Ioo
      (hsubU ht) hUo).self_of_nhds
  have hJCder : ∀ t ∈ Icc (ck - η) (ck1 + η), HasDerivAt J (J' t) t := by
    intro t ht
    rw [hJ'def]
    exact (Submission.JacobiGlobal.eventually_hasDerivAt_of_contDiffOn isOpen_Ioo
      (hsubU ht) hJo).self_of_nhds
  have hpiece : Icc ck ck1 ⊆ Ioo S T :=
    fun t ht => ⟨by linarith [ht.1, hS], by linarith [ht.2, hT]⟩
  have huC : ContinuousOn u (Icc ck ck1) := hUo.continuousOn.mono hpiece
  have hJC : ContinuousOn J (Icc ck ck1) := hJo.continuousOn.mono hpiece
  have hwCd : ContDiffOn ℝ ∞ w (Ioo S T) := by
    rw [hwdef]
    exact hUo.deriv_of_isOpen isOpen_Ioo (le_of_eq (by simp))
  have hwC : ContinuousOn w (Icc ck ck1) := (hwCd.continuousOn).mono hpiece
  have hJ'Cd : ContDiffOn ℝ ∞ J' (Ioo S T) := by
    rw [hJ'def]
    exact hJo.deriv_of_isOpen isOpen_Ioo (le_of_eq (by simp))
  have hJ'C : ContinuousOn J' (Icc ck ck1) := (hJ'Cd.continuousOn).mono hpiece
  have htgt : ∀ t ∈ Icc (ck - η) (ck1 + η), u t ∈ (extChartAt I z).target := by
    intro t ht
    rw [hudef]
    exact (extChartAt I z).map_source (by
      rw [extChartAt_source]; exact hsrc t (hsub ht))
  have hZ : ∀ t ∈ Icc (ck - η) (ck1 + η), covAlong cov (fun s => d • V s) t
      = frameVector (I := I) z (γ t) (DtQ cov z u J w J' t) := by
    intro t ht
    have htI : t ∈ Ioo S T := hsubU ht
    exact covAlong_eq_chart_of_data (cov := cov) (V := fun s => d • V s) htor htI hsrc hcdU
      hcdVs hVfrs (hγ1 t (hsub ht)) (hne t (hsub ht)) (SmoothAlongAt_smul (I := I) d (hVs t (hsub ht)))
  exact Submission.IndexIntrinsic2.continuousOn_idxAlong_weak (cov := cov) htor z
    (A := ck - η) (B := ck1 + η) (a := ck) (b := ck1)
    (by linarith [hηpos]) hlo (by linarith [hηpos]) hγeq hu huC hJC hwC hJ'C htgt
    (fun t ht => (hVfrs t (hsub ht)).symm) hZ

/-! ## Continuity of the piece energy in `t` (the `hint` hypothesis of the assembly)

Roadmap §102.6: the first of the two remaining hypotheses of
`EnergyCover.energy_second_deriv_cover_eventually`.  For `σ` in the small interval, the slice
`t ↦ (curveSpeed (fun s ↦ GExp (γ s) (σ • V s)) t)²` is continuous on the piece: by
`SecondVarGlobal.sq_curveSpeed_fam` it equals the chart integrand
`chartGram z (symm (fam σ t)) (psiW σ t) (psiW σ t)`, which is continuous on the closed box by
`IntrinsicVariation.contOn_hg`, and continuity passes to the slice `t ↦ (σ, t)`. -/

/-- **Continuity of the piece energy in `t`.** -/
lemma continuousOn_piece_energy (hmet : IsMetricCompatible cov)
    {γ : ℝ → M} {V : (t : ℝ) → TangentSpace I (γ t)} {z : M} {Z : Set M}
    (D : ChartFlowData (cov := cov) (I := I) z Z)
    {S T c₀ c₁ δ : ℝ} (hS : S < c₀) (hT : c₁ < T) (hlo : c₀ ≤ c₁) (hδ : 0 < δ)
    (hsrc : ∀ t ∈ Icc S T, γ t ∈ (chartAt H z).source)
    (hcdU : ContDiffOn ℝ ∞ (chartCoord (I := I) z γ) (Icc S T))
    (hcdV : ContDiffOn ℝ ∞ (chartCoords (I := I) z γ V) (Icc S T))
    (hVfr : ∀ t ∈ Icc S T, frameVector (I := I) z (γ t) (chartCoords (I := I) z γ V t) = V t)
    (hZ : ∀ t ∈ Icc S T, γ t ∈ Z)
    (hphase : ∀ σ ∈ Icc (-δ) δ, ∀ t ∈ Icc S T,
      (chartCoord (I := I) z γ t, flowScale D • (σ • chartCoords (I := I) z γ V t))
        ∈ chartData (I := I) z Z) :
    ∀ σ ∈ Ioo (-(δ / 2)) (δ / 2), ContinuousOn (fun t : ℝ =>
      (curveSpeed (I := I) (fun s : ℝ => GExp (cov := cov) hmet (γ s) (σ • V s)) t) ^ 2)
      (Icc c₀ c₁) := by
  intro σ hσ
  set x : ℝ → E := chartCoord (I := I) z γ with hxdef
  set u : ℝ → E := chartCoords (I := I) z γ V with hudef
  set R : Set (ℝ × ℝ) := Ioo (-δ) δ ×ˢ Ioo S T with hRdef
  have hR : IsOpen R := isOpen_Ioo.prod isOpen_Ioo
  have hFcd : ContDiffOn ℝ ∞ (Fam (cov := cov) D x u) R :=
    Submission.SecondVarGlobal.contDiffOn_fam_Ioo (cov := cov) D
      (hcdU.mono (fun t ht => ⟨ht.1.le, ht.2.le⟩))
      (hcdV.mono (fun t ht => ⟨ht.1.le, ht.2.le⟩)) hphase
  have hmem : ∀ p ∈ R, fam (cov := cov) D x u p.1 p.2 ∈ (extChartAt I z).target := by
    intro p hp
    have hσ' : p.1 ∈ Icc (-δ) δ := ⟨by linarith [hp.1.1, hδ], by linarith [hp.1.2, hδ]⟩
    exact Submission.SecondVarGlobal.fam_mem_target' (cov := cov) D (x := x) (u := u)
      (σ := p.1) (t := p.2)
      (D.hKO (hphase p.1 hσ' p.2 ⟨hp.2.1.le, hp.2.2.le⟩))
  have hboxR : Icc (-(δ / 2)) (δ / 2) ×ˢ Icc c₀ c₁ ⊆ R := by
    intro p hp
    exact ⟨⟨by linarith [hp.1.1, hδ], by linarith [hp.1.2, hδ]⟩,
      ⟨by linarith [hp.2.1, hS], by linarith [hp.2.2, hT]⟩⟩
  have hσδ : σ ∈ Icc (-(δ / 2)) (δ / 2) := ⟨hσ.1.le, hσ.2.le⟩
  have hslice : ContinuousOn (fun t : ℝ => (σ, t)) (Icc c₀ c₁) :=
    (continuous_const.prodMk continuous_id).continuousOn
  have hbase : ContinuousOn (fun p : ℝ × ℝ => chartGram (I := I) z
      ((extChartAt I z).symm (Fam (cov := cov) D x u p))
      (psiW (cov := cov) D x u p.1 p.2) (psiW (cov := cov) D x u p.1 p.2))
      (Icc (-(δ / 2)) (δ / 2) ×ˢ Icc c₀ c₁) :=
    Submission.IntrinsicVariation.contOn_hg (cov := cov) (x := x) (u := u) D hR hFcd hmem hboxR
  have hch : ContinuousOn (fun t : ℝ => chartGram (I := I) z
      ((extChartAt I z).symm (Fam (cov := cov) D x u (σ, t)))
      (psiW (cov := cov) D x u σ t) (psiW (cov := cov) D x u σ t)) (Icc c₀ c₁) :=
    hbase.comp (s := Icc c₀ c₁) (t := Icc (-(δ / 2)) (δ / 2) ×ˢ Icc c₀ c₁) hslice
      (fun t ht => ⟨hσδ, ht⟩)
  refine hch.congr (fun t ht => ?_)
  have htI : t ∈ Ioo S T := ⟨by linarith [ht.1, hS], by linarith [ht.2, hT]⟩
  have hIo : IsOpen (Ioo S T) := isOpen_Ioo
  have hsrcev : ∀ᶠ s in 𝓝 t, γ s ∈ (chartAt H z).source := by
    filter_upwards [hIo.mem_nhds htI] with s hs
    exact hsrc s ⟨hs.1.le, hs.2.le⟩
  have hγeqev : γ =ᶠ[𝓝 t] fun s => (extChartAt I z).symm (chartCoord (I := I) z γ s) := by
    filter_upwards [hsrcev] with s hs
    exact (PartialEquiv.left_inv (extChartAt I z) (by rwa [extChartAt_source])).symm
  have hZev : ∀ᶠ s in 𝓝 t, γ s ∈ Z := by
    filter_upwards [hIo.mem_nhds htI] with s hs
    exact hZ s ⟨hs.1.le, hs.2.le⟩
  have hphev : ∀ᶠ s in 𝓝 t,
      (chartCoord (I := I) z γ s, flowScale D • (σ • chartCoords (I := I) z γ V s)) ∈ D.O := by
    filter_upwards [hIo.mem_nhds htI] with s hs
    exact D.hKO (hphase σ ⟨by linarith [hσ.1, hδ], by linarith [hσ.2, hδ]⟩ s
      ⟨hs.1.le, hs.2.le⟩)
  have hVev : V =ᶠ[𝓝 t] (fun s => frameVector (I := I) z (γ s) (chartCoords (I := I) z γ V s)) := by
    filter_upwards [hIo.mem_nhds htI] with s hs
    exact (hVfr s ⟨hs.1.le, hs.2.le⟩).symm
  have hcurve : (fun s : ℝ => GExp (cov := cov) hmet (γ s) (σ • V s))
      =ᶠ[𝓝 t] (fun s : ℝ => GExp (cov := cov) hmet (γ s)
        (σ • frameVector (I := I) z (γ s) (chartCoords (I := I) z γ V s))) := by
    filter_upwards [hVev] with s hs
    rw [hs]
  rw [curveSpeed_congr_of_eventuallyEq (I := I) hcurve]
  exact Submission.SecondVarGlobal.sq_curveSpeed_fam (cov := cov) hmet D hR hFcd
    ⟨⟨by linarith [hσ.1, hδ], by linarith [hσ.2, hδ]⟩, htI⟩
    (V := fun s => frameVector (I := I) z (γ s) (chartCoords (I := I) z γ V s))
    (Filter.EventuallyEq.refl _ _) hZev hsrcev hγeqev hphev

/-! ## Step 2: the `∀ᶠ`-differentiability of the piece energy

Roadmap §102.6 (ii-bis), step 2.  With the pointwise identification
`integral_curveSpeed_eq_chart` in hand, the differentiability of `σ ↦ ∫_{piece} F σ t` near `0` is
the parametrized-integral statement `eventually_differentiableAt_integral_of_continuousOn`, applied to
the chart integrand `ch` and its `σ`-derivative `chi`.  The continuity hypotheses on the closed box are
exactly `IntrinsicVariation.contOn_hg` and `contOn_hg'`; the pointwise derivative is
`SecondVarGeo.hasDerivAt_chartGram_fam_s` (whose `nabla` slot `nabS` unfolds to
`psiE + chrB(…) psiW psiV`, matching `contOn_hg'`). -/

/-- **The piece energy is differentiable near `0`** (differentiation under the integral sign). -/
lemma eventually_differentiableAt_piece_energy (hmet : IsMetricCompatible cov)
    {γ : ℝ → M} {V : (t : ℝ) → TangentSpace I (γ t)} {z : M} {Z : Set M}
    (D : ChartFlowData (cov := cov) (I := I) z Z)
    {S T c₀ c₁ δ : ℝ} (hS : S < c₀) (hT : c₁ < T) (hlo : c₀ ≤ c₁) (hδ : 0 < δ)
    (hsrc : ∀ t ∈ Icc S T, γ t ∈ (chartAt H z).source)
    (hcdU : ContDiffOn ℝ ∞ (chartCoord (I := I) z γ) (Icc S T))
    (hcdV : ContDiffOn ℝ ∞ (chartCoords (I := I) z γ V) (Icc S T))
    (hVfr : ∀ t ∈ Icc S T, frameVector (I := I) z (γ t) (chartCoords (I := I) z γ V t) = V t)
    (hZev : ∀ t ∈ Ioo S T, ∀ᶠ s in 𝓝 t, γ s ∈ Z)
    (hphase : ∀ σ ∈ Icc (-δ) δ, ∀ t ∈ Icc S T,
      (chartCoord (I := I) z γ t, flowScale D • (σ • chartCoords (I := I) z γ V t))
        ∈ chartData (I := I) z Z) :
    ∀ᶠ σ in 𝓝 (0 : ℝ), DifferentiableAt ℝ (fun σ : ℝ => ∫ t in c₀..c₁,
        (curveSpeed (I := I) (fun s : ℝ => GExp (cov := cov) hmet (γ s) (σ • V s)) t) ^ 2) σ := by
  set x : ℝ → E := chartCoord (I := I) z γ with hxdef
  set u : ℝ → E := chartCoords (I := I) z γ V with hudef
  set R : Set (ℝ × ℝ) := Ioo (-δ) δ ×ˢ Ioo S T with hRdef
  have hR : IsOpen R := isOpen_Ioo.prod isOpen_Ioo
  have hδ2 : 0 < δ / 2 := by linarith
  have hFcd : ContDiffOn ℝ ∞ (Fam (cov := cov) D x u) R :=
    Submission.SecondVarGlobal.contDiffOn_fam_Ioo (cov := cov) D
      (hcdU.mono (fun t ht => ⟨ht.1.le, ht.2.le⟩))
      (hcdV.mono (fun t ht => ⟨ht.1.le, ht.2.le⟩)) hphase
  have hmem : ∀ p ∈ R, fam (cov := cov) D x u p.1 p.2 ∈ (extChartAt I z).target := by
    intro p hp
    have hσ : p.1 ∈ Icc (-δ) δ := ⟨by linarith [hp.1.1, hδ], by linarith [hp.1.2, hδ]⟩
    exact Submission.SecondVarGlobal.fam_mem_target' (cov := cov) D (x := x) (u := u)
      (σ := p.1) (t := p.2)
      (D.hKO (hphase p.1 hσ p.2 ⟨hp.2.1.le, hp.2.2.le⟩))
  -- the closed box inside the open rectangle
  have hboxR : Icc (-(δ / 2)) (δ / 2) ×ˢ Icc c₀ c₁ ⊆ R := by
    intro p hp
    exact ⟨⟨by linarith [hp.1.1, hδ], by linarith [hp.1.2, hδ]⟩,
      ⟨by linarith [hp.2.1, hS], by linarith [hp.2.2, hT]⟩⟩
  -- the two continuous integrands
  have hg : ContinuousOn (fun p : ℝ × ℝ => chartGram (I := I) z
      ((extChartAt I z).symm (Fam (cov := cov) D x u p))
      (psiW (cov := cov) D x u p.1 p.2) (psiW (cov := cov) D x u p.1 p.2))
      (Icc (-(δ / 2)) (δ / 2) ×ˢ Icc c₀ c₁) :=
    Submission.IntrinsicVariation.contOn_hg (cov := cov) (x := x) (u := u) D hR hFcd hmem hboxR
  have hg' : ContinuousOn (fun p : ℝ × ℝ => 2 * chartGram (I := I) z
      ((extChartAt I z).symm (Fam (cov := cov) D x u p))
      (psiE (cov := cov) D x u p.1 p.2 + chrB cov z ((extChartAt I z).symm (Fam (cov := cov) D x u p))
        (psiW (cov := cov) D x u p.1 p.2) (psiV (cov := cov) D x u p.1 p.2))
      (psiW (cov := cov) D x u p.1 p.2))
      (Icc (-(δ / 2)) (δ / 2) ×ˢ Icc c₀ c₁) :=
    Submission.IntrinsicVariation.contOn_hg' (cov := cov) (x := x) (u := u) D hR hFcd hmem hboxR
  -- the pointwise `σ`-derivative on the box
  have hderiv : ∀ σ ∈ Ioo (-(δ / 2)) (δ / 2), ∀ t ∈ Icc c₀ c₁,
      HasDerivAt (fun σ' : ℝ => chartGram (I := I) z
          ((extChartAt I z).symm (Fam (cov := cov) D x u (σ', t)))
          (psiW (cov := cov) D x u σ' t) (psiW (cov := cov) D x u σ' t))
        (2 * chartGram (I := I) z ((extChartAt I z).symm (Fam (cov := cov) D x u (σ, t)))
          (psiE (cov := cov) D x u σ t + chrB cov z ((extChartAt I z).symm (Fam (cov := cov) D x u (σ, t)))
            (psiW (cov := cov) D x u σ t) (psiV (cov := cov) D x u σ t))
          (psiW (cov := cov) D x u σ t)) σ := by
    intro σ hσ t ht
    have hp : (σ, t) ∈ R := ⟨⟨by linarith [hσ.1, hδ], by linarith [hσ.2, hδ]⟩,
      ⟨by linarith [ht.1, hS], by linarith [ht.2, hT]⟩⟩
    have hψ := Submission.IntrinsicVariation.hasDerivAt_fam_fst (cov := cov) (x := x) (u := u)
      D hR hFcd hp
    have hw := Submission.IntrinsicVariation.hasDerivAt_psiW_fst (cov := cov) (x := x) (u := u)
      D hR hFcd hp
    have htgt : fam (cov := cov) D x u σ t ∈ (extChartAt I z).target := hmem (σ, t) hp
    have hstay : ∀ᶠ σ' in 𝓝 σ, fam (cov := cov) D x u σ' t ∈ (extChartAt I z).target := by
      filter_upwards [isOpen_Ioo.mem_nhds hσ] with σ' hσ'
      exact hmem (σ', t) ⟨⟨by linarith [hσ'.1, hδ], by linarith [hσ'.2, hδ]⟩, hp.2⟩
    simpa only [nabS, Fam_apply] using
      Submission.SecondVarGeo.hasDerivAt_chartGram_fam_s (cov := cov) hmet z hψ hw htgt hstay
  -- the parametric-integral statement
  have hmain := Commons.Analysis.Calculus.eventually_differentiableAt_integral_of_continuousOn
    (g := fun σ t => chartGram (I := I) z
      ((extChartAt I z).symm (Fam (cov := cov) D x u (σ, t)))
      (psiW (cov := cov) D x u σ t) (psiW (cov := cov) D x u σ t))
    (g' := fun σ t => 2 * chartGram (I := I) z
      ((extChartAt I z).symm (Fam (cov := cov) D x u (σ, t)))
      (psiE (cov := cov) D x u σ t + chrB cov z ((extChartAt I z).symm (Fam (cov := cov) D x u (σ, t)))
        (psiW (cov := cov) D x u σ t) (psiV (cov := cov) D x u σ t))
      (psiW (cov := cov) D x u σ t))
    (a := c₀) (b := c₁) (δ := δ / 2) hlo hδ2 hg hg' hderiv
  -- transfer to the curve-speed form
  filter_upwards [hmain,
    isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Ioo (-δ) δ from ⟨by linarith, hδ⟩)] with σ hσ hσδ
  refine hσ.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioo.mem_nhds hσδ] with σ' hσ'
  exact integral_curveSpeed_eq_chart (cov := cov) hmet D hS hT hlo hsrc hcdU hcdV hVfr hZev
    hphase σ' hσ'

/-! ## The two interval-integrability hypotheses of the cover assembly

Roadmap §102.6: with `hint` (= `continuousOn_piece_energy`) and `hintZ`
(= `continuousOn_idxAlong_piece`) in hand, the `IntervalIntegrable` requirements of
`EnergyCover.energy_second_deriv_cover_eventually` follow from continuity on the piece
(`ContinuousOn.intervalIntegrable_of_Icc`). -/

/-- **`hint`, per piece**: the piece energy is interval-integrable for `σ` in the small interval. -/
lemma intervalIntegrable_piece_energy (hmet : IsMetricCompatible cov)
    {γ : ℝ → M} {V : (t : ℝ) → TangentSpace I (γ t)} {z : M} {Z : Set M}
    (D : ChartFlowData (cov := cov) (I := I) z Z)
    {S T c₀ c₁ : ℝ} (hS : S < c₀) (hT : c₁ < T) (hlo : c₀ ≤ c₁)
    (hsrc : ∀ t ∈ Icc S T, γ t ∈ (chartAt H z).source)
    (hcdU : ContDiffOn ℝ ∞ (chartCoord (I := I) z γ) (Icc S T))
    (hcdV : ContDiffOn ℝ ∞ (chartCoords (I := I) z γ V) (Icc S T))
    (hVfr : ∀ t ∈ Icc S T, frameVector (I := I) z (γ t) (chartCoords (I := I) z γ V t) = V t)
    (hZ : ∀ t ∈ Icc S T, γ t ∈ Z)
    (hphase : ∀ σ ∈ Icc (-1 : ℝ) 1, ∀ t ∈ Icc S T,
      (chartCoord (I := I) z γ t, flowScale D • (σ • chartCoords (I := I) z γ V t))
        ∈ chartData (I := I) z Z) :
    ∀ σ ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2), IntervalIntegrable (fun t : ℝ =>
      (curveSpeed (I := I) (fun s : ℝ => GExp (cov := cov) hmet (γ s) (σ • V s)) t) ^ 2)
      volume c₀ c₁ :=
  fun σ hσ => (continuousOn_piece_energy (cov := cov) hmet D hS hT hlo one_pos hsrc hcdU hcdV
    hVfr hZ hphase σ hσ).intervalIntegrable_of_Icc hlo

/-- **`hintZ`, per piece**: the intrinsic index integrand is interval-integrable on the piece. -/
lemma intervalIntegrable_piece_idxAlong (htor : cov.torsion = 0)
    {γ : ℝ → M} {V : (t : ℝ) → TangentSpace I (γ t)} {z : M} {Z : Set M}
    (D : ChartFlowData (cov := cov) (I := I) z Z)
    {S T ck ck1 : ℝ} (hS : S < ck) (hT : ck1 < T) (hlo : ck ≤ ck1)
    (hsrc : ∀ t ∈ Icc S T, γ t ∈ (chartAt H z).source)
    (hcdU : ContDiffOn ℝ ∞ (chartCoord (I := I) z γ) (Icc S T))
    (hcdV : ContDiffOn ℝ ∞ (chartCoords (I := I) z γ V) (Icc S T))
    (hVfr : ∀ t ∈ Icc S T, frameVector (I := I) z (γ t) (chartCoords (I := I) z γ V t) = V t)
    (hγ1 : ∀ t ∈ Icc S T, ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo (t - 1) (t + 1)))
    (hne : ∀ t ∈ Icc S T, curveVelocity (I := I) γ t ≠ 0)
    (hVs : ∀ t ∈ Icc S T, SmoothAlongAt (I := I) γ V t) (d : ℝ) :
    IntervalIntegrable (fun t : ℝ => idxAlong (cov := cov) γ (fun s => d • V s)
      (covAlong cov (fun s => d • V s)) t) volume ck ck1 :=
  (continuousOn_idxAlong_piece (cov := cov) htor D hS hT hlo hsrc hcdU hcdV hVfr hγ1 hne hVs
    d).intervalIntegrable_of_Icc hlo

/-- **The per-piece second variation along a `GExp`-ray, uniformly in the scale.**  There is a finite
partition of `[a,b]` and a scale `c₀ > 0` such that for every `c ∈ (0, c₀]` and every piece of the
partition, the second variation of the piece energy is `2 ∫ idxAlong` of the scaled field. -/
theorem exists_pos_piece_second_deriv (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {p : M} {ξ : TangentSpace I p} (hξ : ξ ≠ 0)
    {V : (t : ℝ) → TangentSpace I (GExp (cov := cov) hmet p (t • ξ))}
    {a b : ℝ}
    (hVs : ∀ s ∈ Icc (a - 1) (b + 1),
      SmoothAlongAt (I := I) (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ)) V s)
    (hab : a < b) :
    ∃ (N : ℕ) (c : ℕ → ℝ) (c₀ : ℝ), 0 < c₀ ∧ c 0 = a ∧ c N = b ∧
      (∀ k < N, c k < c (k + 1)) ∧
      ∀ d ∈ Set.Ioc (0 : ℝ) c₀,
        (∀ᶠ σ in 𝓝 (0 : ℝ), ∀ k < N, IntervalIntegrable (fun t : ℝ => (curveSpeed (I := I)
            (fun s : ℝ => GExp (cov := cov) hmet (GExp (cov := cov) hmet p (s • ξ))
              (σ • (d • V s))) t) ^ 2) volume (c k) (c (k + 1))) ∧
        (∀ k < N, IntervalIntegrable (fun t : ℝ => idxAlong (cov := cov)
            (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ)) (fun s => d • V s)
            (covAlong cov (fun s => d • V s)) t) volume (c k) (c (k + 1))) ∧
        ∀ k < N,
          (∀ᶠ σ in 𝓝 (0 : ℝ), DifferentiableAt ℝ (fun σ : ℝ =>
              ∫ t in (c k)..(c (k + 1)), (curveSpeed (I := I)
                (fun s : ℝ => GExp (cov := cov) hmet (GExp (cov := cov) hmet p (s • ξ))
                  (σ • (d • V s))) t) ^ 2) σ) ∧
          HasDerivAt (deriv (fun σ : ℝ => ∫ t in (c k)..(c (k + 1)), (curveSpeed (I := I)
              (fun s : ℝ => GExp (cov := cov) hmet (GExp (cov := cov) hmet p (s • ξ))
                (σ • (d • V s))) t) ^ 2))
            (2 * ∫ t in (c k)..(c (k + 1)), idxAlong (cov := cov)
              (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ)) (fun s => d • V s)
              (covAlong cov (fun s => d • V s)) t) 0 := by
  classical
  set γ : ℝ → M := fun s : ℝ => GExp (cov := cov) hmet p (s • ξ) with hγdef
  -- the ray is smooth on any symmetric interval; in particular on `Ioo (a-1) (b+1)`
  have hr : -(max (b + 1) (1 - a) + 1) < a - 1 ∧ b + 1 < max (b + 1) (1 - a) + 1 :=
    ⟨by linarith [le_max_right (b + 1) (1 - a)], by linarith [le_max_left (b + 1) (1 - a)]⟩
  have hγsm : ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo (a - 1) (b + 1)) := by
    rw [hγdef]
    refine (Submission.LensLoop.contMDiffOn_GExp_smul_Ioo_symm (cov := cov) hmet p hξ
      (max (b + 1) (1 - a) + 1)).mono ?_
    exact fun t ht => ⟨by linarith [ht.1, hr.1], by linarith [ht.2, hr.2]⟩
  -- the cover
  obtain ⟨N, c, S, T, z, hc0, hcN, hmono, hSB, hsrc, hcdU, hcdV, hVfr, hroomA⟩ :=
    Submission.SmoothFieldCover.exists_partition_smoothField (I := I) hab.le hγsm
      (fun s hs => hVs s ⟨by linarith [hs.1], by linarith [hs.2]⟩)
  have hNpos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · exfalso
      rw [h] at hcN
      exact absurd (hc0 ▸ hcN : a = b) (ne_of_lt hab)
    · exact h
  have hchain : ∀ l ≤ N, ∀ k ≤ l, c k ≤ c l := by
    intro l hl k hkl
    induction l with
    | zero =>
      simp only [Nat.le_zero] at hkl
      rw [hkl]
    | succ j ih =>
      rcases Nat.eq_or_lt_of_le hkl with h | h
      · rw [h]
      · have hj : j < N := Nat.lt_of_succ_le hl
        exact le_trans (ih (le_of_lt hj) (Nat.lt_succ_iff.mp h)) (le_of_lt (hmono j hj))
  -- the compact flow sets and their flow data
  have hZc : ∀ k < N, IsCompact (γ '' Icc (S k) (T k)) := by
    intro k hk
    have hγc : ContinuousOn γ (Icc (S k) (T k)) := by
      rw [hγdef]
      have h1 : ContinuousOn (fun s : ℝ => (extChartAt I (z k)).symm
          (chartCoord (I := I) (z k) γ s)) (Icc (S k) (T k)) :=
        continuousOn_chartCurve (I := I) (hcdU k hk).continuousOn
          (fun t ht => (extChartAt I (z k)).map_source (by
            rw [extChartAt_source]; exact hsrc k hk t ht))
      refine h1.congr ?_
      intro t ht
      rw [← hγdef]
      exact (PartialEquiv.left_inv (extChartAt I (z k)) (by
        rw [extChartAt_source]; exact hsrc k hk t ht)).symm
    exact isCompact_Icc.image_of_continuousOn hγc
  have hZs : ∀ k < N, γ '' Icc (S k) (T k) ⊆ (chartAt H (z k)).source := by
    rintro k hk _ ⟨t, ht, rfl⟩
    exact hsrc k hk t ht
  have hD : ∀ k < N, ∃ D : ChartFlowData (cov := cov) (I := I) (z k) (γ '' Icc (S k) (T k)), True :=
    fun k hk => exists_chartFlowData (cov := cov) (I := I) (z₀ := z k) (hZc k hk) (hZs k hk)
  choose D _ using hD
  -- the ray is smooth on every symmetric interval, hence on a neighbourhood of every
  -- local interval of the cover
  set Rg : ℝ := ∑ k ∈ Finset.range N, (|S k| + |T k| + 2) with hRgdef
  have hγglob : ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo (-Rg) Rg) := by
    rw [hγdef]
    exact Submission.LensLoop.contMDiffOn_GExp_smul_Ioo_symm (cov := cov) hmet p hξ Rg
  have hRgbound : ∀ k < N, |S k| + |T k| + 1 < Rg := by
    intro k hk
    have h := Finset.single_le_sum (f := fun k => |S k| + |T k| + 2)
      (fun i _ => by positivity) (Finset.mem_range.mpr hk)
    rw [hRgdef]
    linarith
  have hγ1glob : ∀ k < N, ∀ t ∈ Icc (S k) (T k),
      ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo (t - 1) (t + 1)) := by
    intro k hk t ht
    refine hγglob.mono ?_
    intro s hs
    have h1 : |t| ≤ |S k| + |T k| := by
      rw [abs_le]
      exact ⟨by linarith [ht.1, neg_abs_le (S k), abs_nonneg (T k)],
        by linarith [ht.2, le_abs_self (T k), abs_nonneg (S k)]⟩
    have hb := abs_le.mp h1
    exact ⟨by linarith [hs.1, hb.1, hRgbound k hk], by linarith [hs.2, hb.2, hRgbound k hk]⟩
  -- the local intervals are eventual membership sets for the image
  have hZev : ∀ k < N, ∀ t ∈ Ioo (S k) (T k), ∀ᶠ s in 𝓝 t, γ s ∈ γ '' Icc (S k) (T k) := by
    intro k hk t ht
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact ⟨s, ⟨hs.1.le, hs.2.le⟩, rfl⟩
  -- (1) the phase thresholds (in the *field* scale, at radius 1)
  have hex1 : ∀ k (hk : k < N), ∃ e : ℝ, 0 < e ∧ ∀ c ∈ Set.Ioc (0 : ℝ) e,
      ∀ σ ∈ Icc (-1 : ℝ) 1, ∀ t ∈ Icc (S k) (T k),
      (chartCoord (I := I) (z k) γ t,
          flowScale (D k hk) • (σ • chartCoords (I := I) (z k) γ (fun s => c • V s) t))
        ∈ chartData (I := I) (z k) (γ '' Icc (S k) (T k)) := by
    intro k hk
    exact Submission.EnergyPhase.exists_pos_phase_condition (cov := cov)
      (A := S k) (B := T k) (D k hk)
      (le_of_lt (lt_trans (hSB k hk).1 (lt_trans (hmono k hk) (hSB k hk).2)))
      (hcdV k hk).continuousOn (fun t ht => ⟨t, ⟨ht.1, ht.2⟩, by rw [hγdef]⟩)
  let e₁ : ℕ → ℝ := fun k => if hk : k < N then Classical.choose (hex1 k hk) else 1
  have he₁ : ∀ k (hk : k < N), 0 < e₁ k ∧ ∀ c ∈ Set.Ioc (0 : ℝ) (e₁ k),
      ∀ σ ∈ Icc (-1 : ℝ) 1, ∀ t ∈ Icc (S k) (T k),
      (chartCoord (I := I) (z k) γ t,
          flowScale (D k hk) • (σ • chartCoords (I := I) (z k) γ (fun s => c • V s) t))
        ∈ chartData (I := I) (z k) (γ '' Icc (S k) (T k)) := by
    intro k hk
    have := Classical.choose_spec (hex1 k hk)
    simpa only [e₁, dif_pos hk] using this
  -- (2) the energy thresholds
  have hex2 : ∀ k (hk : k < N), ∃ e : ℝ, 0 < e ∧ ∀ d ∈ Set.Ioc (0 : ℝ) e,
      HasDerivAt (deriv (fun σ : ℝ => ∫ t in (c k)..(c (k + 1)), (curveSpeed (I := I)
          (fun s : ℝ => GExp (cov := cov) hmet (γ s) (σ • (d • V s))) t) ^ 2))
        (2 * ∫ t in (c k)..(c (k + 1)), idxAlong (cov := cov) γ (fun s => d • V s)
          (covAlong cov (fun s => d • V s)) t) 0 := by
    intro k hk
    have hSk : S k < c k := (hSB k hk).1
    have hTk : c (k + 1) < T k := (hSB k hk).2
    have hak : c k < c (k + 1) := hmono k hk
    have hgeoB : ∀ t ∈ Icc (c k) (c (k + 1)), HasDerivAt
        (fun t' : ℝ => psiW (cov := cov) (D k hk) (chartCoord (I := I) (z k) γ)
          (chartCoords (I := I) (z k) γ V) 0 t')
        (chartGeodesicVectorField cov (z k) (chartCoord (I := I) (z k) γ t,
          psiW (cov := cov) (D k hk) (chartCoord (I := I) (z k) γ)
            (chartCoords (I := I) (z k) γ V) 0 t)) t := by
      set ε : ℝ := min (c k - S k) (T k - c (k + 1)) / 2 with hεdef
      have hε1 : ε ≤ c k - S k := by
        rw [hεdef]
        have h := min_le_left (c k - S k) (T k - c (k + 1))
        linarith
      have hε2 : ε ≤ T k - c (k + 1) := by
        rw [hεdef]
        have h := min_le_right (c k - S k) (T k - c (k + 1))
        linarith
      refine GExpPieceData.hasDerivAt_psiW_GExp (cov := cov) (ε := ε)
        (u := chartCoords (I := I) (z k) γ V) hmet (D k hk) hξ ?_ ?_ ?_
      · rw [hεdef]
        exact div_pos (lt_min (by linarith) (by linarith)) two_pos
      · intro t ht
        exact ⟨t, ⟨by linarith [ht.1, hε1], by linarith [ht.2, hε2]⟩, by rw [hγdef]⟩
      · intro t ht
        exact hsrc k hk t ⟨by linarith [ht.1, hε1], by linarith [ht.2, hε2]⟩
    have hck : a ≤ c k := hc0 ▸ hchain k (le_of_lt hk) 0 (Nat.zero_le k)
    have hck1 : c (k + 1) ≤ b := hcN ▸ hchain N le_rfl (k + 1) (Nat.succ_le_of_lt hk)
    exact energy_second_deriv_piece_scaled (cov := cov) hmet htor (D k hk) hSk hTk hak
      (fun t ht => hsrc k hk t ⟨by linarith [ht.1, hSk], by linarith [ht.2, hTk]⟩)
      (fun t ht => ⟨t, ⟨ht.1, ht.2⟩, by rw [hγdef]⟩)
      (hcdU k hk) (hcdV k hk) (hVfr k hk)
      (fun t ht => hγsm.mono (fun s hs => ⟨by linarith [hs.1, ht.1, hck],
        by linarith [hs.2, ht.2, hck1]⟩))
      (fun t ht => curveVelocity_GExp_smul_ne_zero (cov := cov) hmet hξ t)
      (fun t ht => hVs t ⟨by linarith [hck, ht.1], by linarith [hck1, ht.2]⟩)
      hgeoB
  let e₂ : ℕ → ℝ := fun k => if hk : k < N then Classical.choose (hex2 k hk) else 1
  have he₂ : ∀ k (hk : k < N), 0 < e₂ k ∧ ∀ d ∈ Set.Ioc (0 : ℝ) (e₂ k),
      HasDerivAt (deriv (fun σ : ℝ => ∫ t in (c k)..(c (k + 1)), (curveSpeed (I := I)
          (fun s : ℝ => GExp (cov := cov) hmet (γ s) (σ • (d • V s))) t) ^ 2))
        (2 * ∫ t in (c k)..(c (k + 1)), idxAlong (cov := cov) γ (fun s => d • V s)
          (covAlong cov (fun s => d • V s)) t) 0 := by
    intro k hk
    have := Classical.choose_spec (hex2 k hk)
    simpa only [e₂, dif_pos hk] using this
  -- (3) the common scale and the assembly
  let d₀ : ℕ → ℝ := fun k => min (e₁ k) (e₂ k)
  have hd₀pos : ∀ k, 0 < d₀ k := by
    intro k
    by_cases hk : k < N
    · have hval : d₀ k = min (e₁ k) (e₂ k) := by simp only [d₀]
      rw [hval]
      exact lt_min (he₁ k hk).1 (he₂ k hk).1
    · have hval : d₀ k = 1 := by simp only [d₀, e₁, e₂, dif_neg hk, min_self]
      rw [hval]
      norm_num
  have hne : ((Finset.range N).image d₀).Nonempty :=
    ⟨d₀ 0, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hNpos, rfl⟩⟩
  refine ⟨N, c, ((Finset.range N).image d₀).min' hne, ?_, hc0, hcN, hmono, ?_⟩
  · have hmem : ((Finset.range N).image d₀).min' hne ∈ (Finset.range N).image d₀ :=
      Finset.min'_mem _ hne
    obtain ⟨k, hk, hk'⟩ := Finset.mem_image.mp hmem
    rw [← hk']
    exact hd₀pos k
  · intro d hd
    have hle_of : ∀ k < N, d ≤ d₀ k := fun k hk => le_trans hd.2 (Finset.min'_le _ _
      (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩))
    have hle1 : ∀ k < N, d ≤ e₁ k := fun k hk => le_trans (hle_of k hk) (min_le_left _ _)
    have hle2 : ∀ k < N, d ≤ e₂ k := fun k hk => le_trans (hle_of k hk) (min_le_right _ _)
    have hcdVs : ∀ k < N, ContDiffOn ℝ ∞ (chartCoords (I := I) (z k) γ (fun s => d • V s))
        (Icc (S k) (T k)) := by
      intro k hk
      rw [chartCoords_smul]
      exact (hcdV k hk).const_smul d
    have hVfrs : ∀ k < N, ∀ t ∈ Icc (S k) (T k), frameVector (I := I) (z k) (γ t)
        (chartCoords (I := I) (z k) γ (fun s => d • V s) t) = (fun s => d • V s) t := by
      intro k hk t ht
      rw [chartCoords_smul]
      show frameVector (I := I) (z k) (γ t) (d • chartCoords (I := I) (z k) γ V t) = d • V t
      rw [frameVector_smul, hVfr k hk t ht]
    have hZmem : ∀ k < N, ∀ t ∈ Icc (S k) (T k), γ t ∈ γ '' Icc (S k) (T k) :=
      fun k hk t ht => ⟨t, ⟨ht.1, ht.2⟩, by rw [hγdef]⟩
    refine ⟨?_, ?_, ?_⟩
    · filter_upwards [isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Ioo (-(1 / 2)) (1 / 2) from
        ⟨by norm_num, by norm_num⟩)] with σ hσ k hk
      exact intervalIntegrable_piece_energy (cov := cov) hmet (D k hk) (hSB k hk).1 (hSB k hk).2
        (hmono k hk).le (fun t ht => hsrc k hk t ht) (hcdU k hk) (hcdVs k hk) (hVfrs k hk)
        (hZmem k hk) ((he₁ k hk).2 d ⟨hd.1, hle1 k hk⟩) σ hσ
    · intro k hk
      exact intervalIntegrable_piece_idxAlong (cov := cov) htor (D k hk) (hSB k hk).1 (hSB k hk).2
        (hmono k hk).le (fun t ht => hsrc k hk t ht) (hcdU k hk) (hcdV k hk) (hVfr k hk)
        (hγ1glob k hk) (fun t ht => curveVelocity_GExp_smul_ne_zero (cov := cov) hmet hξ t)
        (fun t ht => hVs t ⟨(hroomA k hk ht).1.le, (hroomA k hk ht).2.le⟩) d
    · intro k hk
      exact ⟨eventually_differentiableAt_piece_energy (cov := cov) hmet (D k hk) (hSB k hk).1
        (hSB k hk).2 (hmono k hk).le one_pos (fun t ht => hsrc k hk t ht) (hcdU k hk) (hcdVs k hk)
        (hVfrs k hk) (hZev k hk) ((he₁ k hk).2 d ⟨hd.1, hle1 k hk⟩),
        (he₂ k hk).2 d ⟨hd.1, hle2 k hk⟩⟩

end

end Submission.EnergyRayCover
