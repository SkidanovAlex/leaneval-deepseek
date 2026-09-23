import Submission.EnergyPhase
import Submission.SmoothFieldCover

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

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
open Submission.Length
open Submission.GlobalExp
open Submission.GeodesicSpeed
open Submission.IndexCorner2

/-!
# The per-piece second variation of the energy along a geodesic ray

This is Roadmap §102.6 (i): the per-piece assembly of the energy side of `σ ≤ κ`.

`Submission.SecondVarGlobal.energy_second_deriv_piece` computes the second variation of the energy of
the family `Φ(σ,t) = GExp (γ t) (σ • V(t))` on a chart piece, but it needs

* the chart coordinates `u` of the field and their `C^∞` on the room,
* the **phase condition** `(chartCoord z γ t, flowScale D • (σ • u t)) ∈ chartData z Z`.

For an arbitrary field `V` the phase condition fails; the theorem below shows that **shrinking the
field by a factor `c` restores it** (`Submission.EnergyPhase.exists_pos_phase_condition`), and then
transports the conclusion of `energy_second_deriv_piece` back to the chart-free form
`idxAlong γ (c • V) (covAlong cov (c • V))`.
-/

namespace Submission.EnergyRay

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

/-- A field smooth along a curve stays smooth after a scalar rescaling. -/
lemma SmoothAlongAt_smul {γ : ℝ → M} {V : (t : ℝ) → TangentSpace I (γ t)} {t : ℝ} (c : ℝ)
    (h : SmoothAlongAt (I := I) γ V t) :
    SmoothAlongAt (I := I) γ (fun s => c • V s) t := by
  obtain ⟨U, hUopen, htU, hUsrc, hUcd⟩ := h
  refine ⟨U, hUopen, htU, hUsrc, ?_⟩
  rw [chartCoords_smul]
  exact hUcd.const_smul c

/-- **The chart formula for `covAlong` on a piece**, in the exact form of the `Z`-field of
`energy_second_deriv_piece`. -/
lemma covAlong_eq_chart_of_data (htor : cov.torsion = 0)
    {γ : ℝ → M} {V : (t : ℝ) → TangentSpace I (γ t)} {z : M} {S E t : ℝ}
    (ht : t ∈ Ioo S E)
    (hsrc : ∀ s ∈ Icc S E, γ s ∈ (chartAt H z).source)
    (hcdU : ContDiffOn ℝ ∞ (chartCoord (I := I) z γ) (Icc S E))
    (hcdV : ContDiffOn ℝ ∞ (chartCoords (I := I) z γ V) (Icc S E))
    (hVframe : ∀ s ∈ Icc S E, frameVector (I := I) z (γ s) (chartCoords (I := I) z γ V s) = V s)
    (hγ1 : ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo (t - 1) (t + 1)))
    (hne : curveVelocity (I := I) γ t ≠ 0) (hVs : SmoothAlongAt (I := I) γ V t) :
    covAlong cov V t = frameVector (I := I) z (γ t)
      (DtQ cov z (chartCoord (I := I) z γ) (chartCoords (I := I) z γ V)
        (deriv (chartCoord (I := I) z γ)) (deriv (chartCoords (I := I) z γ V)) t) := by
  have hIo : IsOpen (Ioo S E) := isOpen_Ioo
  have hmem : Ioo S E ∈ 𝓝 t := hIo.mem_nhds ht
  have hsrcEv : ∀ᶠ s in 𝓝 t, γ s ∈ (chartAt H z).source := by
    filter_upwards [hmem] with s hs
    exact hsrc s ⟨hs.1.le, hs.2.le⟩
  have huTgt : ∀ᶠ s in 𝓝 t, chartCoord (I := I) z γ s ∈ (extChartAt I z).target := by
    filter_upwards [hsrcEv] with s hs
    exact (extChartAt I z).map_source (by rwa [extChartAt_source])
  have hγeq : γ =ᶠ[𝓝 t] fun s => (extChartAt I z).symm (chartCoord (I := I) z γ s) := by
    filter_upwards [hsrcEv] with s hs
    exact (PartialEquiv.left_inv (extChartAt I z) (by rwa [extChartAt_source])).symm
  have hu : ∀ᶠ s in 𝓝 t, HasDerivAt (chartCoord (I := I) z γ)
      (deriv (chartCoord (I := I) z γ) s) s :=
    Submission.JacobiGlobal.eventually_hasDerivAt_of_contDiffOn hIo ht
      (hcdU.mono (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩))
  have hy : ∀ᶠ s in 𝓝 t, frameVector (I := I) z (γ s) (chartCoords (I := I) z γ V s) = V s := by
    filter_upwards [hmem] with s hs
    exact hVframe s ⟨hs.1.le, hs.2.le⟩
  have hy' : ∀ᶠ s in 𝓝 t, HasDerivAt (chartCoords (I := I) z γ V)
      (deriv (chartCoords (I := I) z γ V) s) s :=
    Submission.JacobiGlobal.eventually_hasDerivAt_of_contDiffOn hIo ht
      (hcdV.mono (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩))
  exact Submission.JacobiGlobal.covAlong_eq_chart (cov := cov) htor hγ1 hne hVs
    (hsrc t ⟨ht.1.le, ht.2.le⟩) hsrcEv huTgt hγeq hu hy hy'


/-- **The per-piece second variation of the energy, at a small scale.**  For a chart piece carrying
`C^∞` data of the curve and of a field `V` (plus the geodesic equation for the ray), there is
`c₀ > 0` such that for every `c ∈ (0, c₀]` the family `Φ(σ,t) = GExp (γ t) (σ • (c • V t))` satisfies

`E''(0) = 2 ∫_a^b idxAlong γ (c • V) (covAlong cov (c • V))`,

where `E(σ) = ∫_a^b (curveSpeed Φ(σ,·))²`. -/
theorem energy_second_deriv_piece_scaled (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {γ : ℝ → M} {V : (t : ℝ) → TangentSpace I (γ t)} {z : M} {Z : Set M}
    (D : ChartFlowData (cov := cov) (I := I) z Z)
    {S T a b : ℝ} (hSa : S < a) (hbE : b < T) (hab : a < b)
    (hsrc : ∀ t ∈ Icc S T, γ t ∈ (chartAt H z).source)
    (hZ : ∀ t ∈ Icc S T, γ t ∈ Z)
    (hcdU : ContDiffOn ℝ ∞ (chartCoord (I := I) z γ) (Icc S T))
    (hcdV : ContDiffOn ℝ ∞ (chartCoords (I := I) z γ V) (Icc S T))
    (hVframe : ∀ t ∈ Icc S T, frameVector (I := I) z (γ t) (chartCoords (I := I) z γ V t) = V t)
    (hγ1 : ∀ t ∈ Icc a b, ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo (t - 1) (t + 1)))
    (hne : ∀ t ∈ Icc a b, curveVelocity (I := I) γ t ≠ 0)
    (hVs : ∀ t ∈ Icc a b, SmoothAlongAt (I := I) γ V t)
    (hgeoB : ∀ t ∈ Icc a b, HasDerivAt
      (fun t' : ℝ => psiW (cov := cov) D (chartCoord (I := I) z γ)
        (chartCoords (I := I) z γ V) 0 t')
      (chartGeodesicVectorField cov z (chartCoord (I := I) z γ t,
        psiW (cov := cov) D (chartCoord (I := I) z γ) (chartCoords (I := I) z γ V) 0 t)) t) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c ∈ Set.Ioc (0 : ℝ) c₀,
      HasDerivAt (deriv (fun σ : ℝ => ∫ t in a..b, (curveSpeed (I := I)
          (fun s : ℝ => GExp (cov := cov) hmet (γ s) (σ • (c • V s))) t) ^ 2))
        (2 * ∫ t in a..b, idxAlong (cov := cov) γ (fun s => c • V s)
          (covAlong cov (fun s => c • V s)) t) 0 := by
  have hSE : S ≤ T := le_of_lt (lt_trans hSa (lt_trans hab hbE))
  have haS : 0 < a - S := by linarith
  have hEb : 0 < T - b := by linarith
  set η : ℝ := min (a - S) (T - b) / 2 with hηdef
  have hηpos : 0 < η := by
    rw [hηdef]
    exact div_pos (lt_min haS hEb) two_pos
  have hη1 : η ≤ a - S := by
    rw [hηdef]; have h := min_le_left (a - S) (T - b); linarith
  have hη2 : η ≤ T - b := by
    rw [hηdef]; have h := min_le_right (a - S) (T - b); linarith
  have hsub : Icc (a - η) (b + η) ⊆ Icc S T := by
    intro t ht
    exact ⟨by linarith [ht.1, hη1, hSa], by linarith [ht.2, hη2, hbE]⟩
  have hsubI : Ioo (a - η) (b + η) ⊆ Icc S T :=
    fun t ht => hsub ⟨ht.1.le, ht.2.le⟩
  obtain ⟨c₀, hc₀pos, hc₀⟩ :=
    EnergyPhase.exists_pos_phase_condition (cov := cov) D hSE hcdV.continuousOn hZ
  refine ⟨c₀, hc₀pos, ?_⟩
  intro c hc
  set W : ℝ → E := chartCoords (I := I) z γ (fun s => c • V s) with hWdef
  have hWsm : W = fun s => c • chartCoords (I := I) z γ V s := by
    rw [hWdef]; exact chartCoords_smul z γ V c
  have hWcd : ContDiffOn ℝ ∞ W (Icc S T) := by
    rw [hWsm]
    exact hcdV.const_smul c
  -- the per-piece data of `energy_second_deriv_piece`
  have hgeoB' : ∀ t ∈ Icc a b, HasDerivAt
      (fun t' : ℝ => psiW (cov := cov) D (chartCoord (I := I) z γ) W 0 t')
      (chartGeodesicVectorField cov z (chartCoord (I := I) z γ t,
        psiW (cov := cov) D (chartCoord (I := I) z γ) W 0 t)) t := by
    intro t ht
    have hfun : (fun t' : ℝ => psiW (cov := cov) D (chartCoord (I := I) z γ) W 0 t')
        = (fun t' : ℝ => psiW (cov := cov) D (chartCoord (I := I) z γ)
            (chartCoords (I := I) z γ V) 0 t') := by
      funext t'
      simp only [psiW, fam_apply, zero_smul]
    have hpt : psiW (cov := cov) D (chartCoord (I := I) z γ) W 0 t
        = psiW (cov := cov) D (chartCoord (I := I) z γ) (chartCoords (I := I) z γ V) 0 t := by
      simp only [psiW, fam_apply, zero_smul]
    rw [hfun, hpt]
    exact hgeoB t ht
  have hmain := energy_second_deriv_piece (cov := cov) hmet htor D (γ := γ) (u := W)
    (a := a) (b := b) (η := η) hab hηpos
    (fun t ht => hsrc t (hsub ht)) (fun t ht => hZ t (hsub ht))
    (hcdU.mono hsubI) (hWcd.mono hsubI)
    (fun σ hσ t ht => hc₀ c hc σ hσ t (hsub ht)) hgeoB'
  -- (1) the family
  have hfam : (fun σ : ℝ => ∫ t in a..b, (curveSpeed (I := I) (fun s : ℝ => GExp (cov := cov) hmet
        (γ s) (σ • frameVector (I := I) z (γ s) (W s))) t) ^ 2)
      = fun σ : ℝ => ∫ t in a..b, (curveSpeed (I := I) (fun s : ℝ => GExp (cov := cov) hmet
        (γ s) (σ • (c • V s))) t) ^ 2 := by
    funext σ
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [uIcc_of_le hab.le] at ht
    have htI : t ∈ Ioo S T := ⟨by linarith [ht.1, hη1, hSa], by linarith [ht.2, hη2, hbE]⟩
    have hev : (fun s : ℝ => GExp (cov := cov) hmet (γ s)
          (σ • frameVector (I := I) z (γ s) (W s)))
        =ᶠ[𝓝 t] (fun s : ℝ => GExp (cov := cov) hmet (γ s) (σ • (c • V s))) := by
      filter_upwards [isOpen_Ioo.mem_nhds htI] with s hs
      have hsSE : s ∈ Icc S T := ⟨hs.1.le, hs.2.le⟩
      have hWs : W s = c • chartCoords (I := I) z γ V s := congrFun hWsm s
      show GExp (cov := cov) hmet (γ s) (σ • frameVector (I := I) z (γ s) (W s))
        = GExp (cov := cov) hmet (γ s) (σ • (c • V s))
      rw [hWs, frameVector_smul, hVframe s hsSE]
    rw [curveSpeed_congr_of_eventuallyEq (I := I) hev]
  -- (2) the index integrand
  have hidx : (∫ t in a..b, idxAlong (cov := cov) γ
        (fun t : ℝ => frameVector (I := I) z (γ t) (W t))
        (fun t : ℝ => frameVector (I := I) z (γ t)
          (DtQ cov z (chartCoord (I := I) z γ) W (deriv (chartCoord (I := I) z γ))
            (deriv W) t)) t)
      = ∫ t in a..b, idxAlong (cov := cov) γ (fun s => c • V s)
          (covAlong cov (fun s => c • V s)) t := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [uIcc_of_le hab.le] at ht
    have htI : t ∈ Ioo S T := ⟨by linarith [ht.1, hη1, hSa], by linarith [ht.2, hη2, hbE]⟩
    have htSE : t ∈ Icc S T := ⟨htI.1.le, htI.2.le⟩
    have hWframe : ∀ s ∈ Icc S T,
        frameVector (I := I) z (γ s) (chartCoords (I := I) z γ (fun r => c • V r) s)
          = (fun r => c • V r) s := by
      intro s hs
      rw [chartCoords_smul]
      show frameVector (I := I) z (γ s) (c • chartCoords (I := I) z γ V s) = c • V s
      rw [frameVector_smul, hVframe s hs]
    have h1 : frameVector (I := I) z (γ t) (W t) = c • V t := by
      have hWs : W t = c • chartCoords (I := I) z γ V t := congrFun hWsm t
      rw [hWs, frameVector_smul, hVframe t htSE]
    have h2a : covAlong cov V t = frameVector (I := I) z (γ t)
        (DtQ cov z (chartCoord (I := I) z γ) (chartCoords (I := I) z γ V)
          (deriv (chartCoord (I := I) z γ)) (deriv (chartCoords (I := I) z γ V)) t) :=
      covAlong_eq_chart_of_data (cov := cov) htor htI hsrc hcdU hcdV hVframe
        (hγ1 t ht) (hne t ht)
        (hVs t ht)
    have hdW : deriv W = fun s : ℝ => c • deriv (chartCoords (I := I) z γ V) s := by
      rw [hWsm]
      funext s
      exact deriv_const_smul_all c (chartCoords (I := I) z γ V) s
    have hDtQ : DtQ cov z (chartCoord (I := I) z γ) W (deriv (chartCoord (I := I) z γ)) (deriv W) t
        = c • DtQ cov z (chartCoord (I := I) z γ) (chartCoords (I := I) z γ V)
            (deriv (chartCoord (I := I) z γ)) (deriv (chartCoords (I := I) z γ V)) t := by
      rw [hdW, hWsm]
      exact DtQ_smul z (chartCoord (I := I) z γ) (deriv (chartCoord (I := I) z γ))
        (chartCoords (I := I) z γ V) (deriv (chartCoords (I := I) z γ V)) c t
    have h2 : frameVector (I := I) z (γ t)
        (DtQ cov z (chartCoord (I := I) z γ) W (deriv (chartCoord (I := I) z γ)) (deriv W) t)
        = covAlong cov (fun s => c • V s) t := by
      rw [hDtQ, frameVector_smul, ← h2a, covAlong_smul (cov := cov) htor]
    simp only [idxAlong]
    rw [h1, h2]
  have hval : 2 * (∫ t in a..b, idxAlong (cov := cov) γ
        (fun t : ℝ => frameVector (I := I) z (γ t) (W t))
        (fun t : ℝ => frameVector (I := I) z (γ t)
          (DtQ cov z (chartCoord (I := I) z γ) W (deriv (chartCoord (I := I) z γ))
            (deriv W) t)) t)
      = 2 * ∫ t in a..b, idxAlong (cov := cov) γ (fun s => c • V s)
          (covAlong cov (fun s => c • V s)) t := by
    rw [hidx]
  exact (hmain.congr_deriv hval).congr_of_eventuallyEq (EventuallyEq.of_eq hfam).deriv.symm

end

end Submission.EnergyRay
