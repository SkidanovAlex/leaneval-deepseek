import Mathlib
import Submission.Work.EvenBound.Imports

namespace Work.EvenBound.ThirdGeodesic

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

/-- **The chart velocity of the geodesic variation `F σ t = GExp (γ t) (σ • (d • V t))` converges
to the velocity of `γ`** (the "limit of the variation velocity" step of the third-geodesic
contradiction; `htor` is unused, kept for uniformity with the surrounding API).

*Proof route.*  `hVsm` at `s = 1/2` gives an open neighbourhood `U` of `1/2` and a chart `z` (the one
of the statement) in which `chartCoords z γ V` is `C^∞`; write `a τ := chartCoords z γ V τ` so that
`σ • (d • V τ) = frameVector z (γ τ) (σ • (d • a τ))` (`GExpSmooth.frameVector_smul'`,
`JacobiGlobal.frameVector_chartCoords`).  By `GExpJointPt.exists_chartFrame` (or
`GExpFlow.exists_chartFlowData` + `ChartBounds.exists_chartGram_bounds`) there is a compact chart
piece `Z ∋ γ (1/2)` and a chart-flow datum with `contMDiffOn_GExp_frameVector`:
`(q, u) ↦ GExp q (frameVector z q u)` is `C^∞` on `Z ×ˢ closedBall 0 η`.  Hence
`(σ, τ) ↦ (extChartAt I z) (GExp (γ τ) (σ • (d • V τ)))` is `C^∞` on a neighbourhood of `(0, 1/2)`
(compose with the `C^∞` maps `τ ↦ γ τ` and `τ ↦ σ • d • a τ`, and with `extChartAt I z`, smooth on
the chart source), so its `τ`-partial derivative is jointly continuous there — this is the statement
for the pair `(σn n, tn n) → (0, 1/2)`.  (Equivalently, the `IntrinsicVariation`/`SecondVarGlobal`
chart model `Fam D (chartCoord z γ) (chartCoords z γ (d • V))` is jointly `C^∞`
(`contDiffOn_fam`), its `t`-partial `psiW` is jointly `C^∞` (`contDiffOn_psiW`), it agrees with
`(extChartAt I z) ∘ F σ` through `UniformInj.GExp_eq_symm_Hfun`, and `psiW` at `σ = 0` is
`deriv (chartCoord z γ)` by `SecondVarGlobal.psiW_zero`; the two partial derivatives of a `C^∞` map
`ℝ × ℝ → E` agree with the iterated `deriv`s by `Commons.Analysis.Calculus.deriv_slice_snd`/
`contDiffOn_deriv_section_snd`.) -/
theorem tendsto_chartVel_variation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {γ : ℝ → M} (hγsm : ContMDiff 𝓘(ℝ) I ∞ γ)
    {V : (t : ℝ) → TangentSpace I (γ t)}
    (hVsm : ∀ s ∈ Set.Icc ((0:ℝ) - 1) ((1:ℝ) + 1),
      Submission.JacobiGlobal.SmoothAlongAt (I := I) γ V s)
    {d : ℝ} (hd : 0 < d)
    {z : M} (hz : γ (1 / 2) ∈ (chartAt H z).source)
    {σn : ℕ → ℝ} (hσ : Tendsto σn atTop (𝓝 0))
    {tn : ℕ → ℝ} (ht : Tendsto tn atTop (𝓝 (1 / 2))) :
    Tendsto (fun n => deriv (fun τ : ℝ => (extChartAt I z)
        (Submission.GlobalExp.GExp (cov := cov) hmet (γ τ) (σn n • (d • V τ)))) (tn n))
      atTop (𝓝 (deriv (fun τ : ℝ => (extChartAt I z) (γ τ)) (1 / 2))) := by
  -- The chart frame at `γ (1 / 2)`, with its flow datum, and the neighbourhoods of `1 / 2`.
  obtain ⟨F⟩ :=
    Submission.GExpJointPt.exists_chartFrame (cov := cov) hmet (z := z) (p := γ (1 / 2)) hz
  have hγc : ContinuousAt γ (1 / 2) := hγsm.continuous.continuousAt
  have hFZ : F.Z ∈ 𝓝 (γ (1 / 2)) := by
    refine F.nhds_of_strict hz ?_
    rw [F.hx, sub_self, norm_zero]
    exact F.hη
  -- the `SmoothAlongAt` datum at `1 / 2`, in the chart at `γ (1 / 2)`
  obtain ⟨U₀, hU₀open, hU₀mem, hU₀src, hU₀cd⟩ := hVsm (1 / 2) (by constructor <;> norm_num)
  -- a neighbourhood of `1 / 2` on which all the data live
  have hU₀ev : ∀ᶠ s in 𝓝 (1 / 2 : ℝ), s ∈ U₀ :=
    Filter.eventually_of_mem (hU₀open.mem_nhds hU₀mem) (fun x hx => hx)
  have hsrcev : ∀ᶠ s in 𝓝 (1 / 2 : ℝ), γ s ∈ (chartAt H z).source :=
    Filter.eventually_of_mem
      (hγc.preimage_mem_nhds ((chartAt H z).open_source.mem_nhds hz)) (fun x hx => hx)
  have hFZev : ∀ᶠ s in 𝓝 (1 / 2 : ℝ), γ s ∈ F.Z :=
    Filter.eventually_of_mem (hγc.preimage_mem_nhds hFZ) (fun x hx => hx)
  have hbig : ∀ᶠ s in 𝓝 (1 / 2 : ℝ),
      s ∈ U₀ ∧ γ s ∈ (chartAt H z).source ∧ γ s ∈ F.Z :=
    hU₀ev.and (hsrcev.and hFZev)
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hbig
  -- the working rectangle: `Ioo (-η) (1 + η) = Ioo (1/2 - ε/2) (1/2 + ε/2)`
  set η : ℝ := ε / 2 - 1 / 2 with hηdef
  have hnegη : -η = 1 / 2 - ε / 2 := by rw [hηdef]; ring
  have hLη : (1 : ℝ) + η = 1 / 2 + ε / 2 := by rw [hηdef]; ring
  have hIcc_ball : Set.Icc (-η) ((1 : ℝ) + η) ⊆ Metric.ball (1 / 2 : ℝ) ε := by
    intro s hs
    rw [Set.mem_Icc, hnegη, hLη] at hs
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hs.1, hs.2, hε]
  have hIoo_ball : Set.Ioo (-η) ((1 : ℝ) + η) ⊆ Metric.ball (1 / 2 : ℝ) ε :=
    Set.Ioo_subset_Icc_self.trans hIcc_ball
  have hmemIcc : ∀ s ∈ Set.Icc (-η) ((1 : ℝ) + η),
      s ∈ U₀ ∧ γ s ∈ (chartAt H z).source ∧ γ s ∈ F.Z := fun s hs => hεsub (hIcc_ball hs)
  have hmemIoo : ∀ s ∈ Set.Ioo (-η) ((1 : ℝ) + η),
      s ∈ U₀ ∧ γ s ∈ (chartAt H z).source ∧ γ s ∈ F.Z := fun s hs => hεsub (hIoo_ball hs)
  have hhalfIoo : (1 / 2 : ℝ) ∈ Set.Ioo (-η) ((1 : ℝ) + η) := by
    rw [Set.mem_Ioo, hnegη, hLη]
    constructor <;> linarith
  have hhalfIcc : (1 / 2 : ℝ) ∈ Set.Icc (-η) ((1 : ℝ) + η) :=
    ⟨le_of_lt hhalfIoo.1, le_of_lt hhalfIoo.2⟩
  -- smoothness of the coordinate data on the ball
  have hγball : ContMDiffOn 𝓘(ℝ) I ∞ γ (Metric.ball (1 / 2 : ℝ) ε) :=
    hγsm.contMDiffOn.mono (Set.subset_univ _)
  have hcd_ball : ContDiffOn ℝ ∞ (Submission.JacobiCoords.chartCoords (I := I) z γ V)
      (Metric.ball (1 / 2 : ℝ) ε) :=
    Submission.ChartCoordsTrans.contDiffOn_chartCoords_of_chartCoords (I := I)
      (z := γ (1 / 2)) (z' := z) (Metric.isOpen_ball (x := (1 / 2 : ℝ)) (ε := ε)) hγball
      (fun s hs => hU₀src s (hεsub hs).1)
      (fun s hs => (hεsub hs).2.1)
      (hU₀cd.mono (fun s hs => (hεsub hs).1))
  have hx_ball : ContDiffOn ℝ ∞ (Submission.IntrinsicVariation.chartCoord (I := I) z γ)
      (Metric.ball (1 / 2 : ℝ) ε) :=
    Submission.SecondVarGlobal.contDiffOn_chartCoord (I := I) (z₀ := z) hγball
      (fun s hs => (hεsub hs).2.1)
  -- and on the working interval
  have hx : ContDiffOn ℝ ∞ (Submission.IntrinsicVariation.chartCoord (I := I) z γ)
      (Set.Ioo (-η) ((1 : ℝ) + η)) := hx_ball.mono hIoo_ball
  have ha : ContDiffOn ℝ ∞ (Submission.JacobiCoords.chartCoords (I := I) z γ V)
      (Set.Ioo (-η) ((1 : ℝ) + η)) := hcd_ball.mono hIoo_ball
  let u : ℝ → E := fun t => d • Submission.JacobiCoords.chartCoords (I := I) z γ V t
  have hu : ContDiffOn ℝ ∞ u (Set.Ioo (-η) ((1 : ℝ) + η)) := ha.const_smul d
  -- a bound on the coordinate field on the closed interval
  obtain ⟨B, hB⟩ :=
    IsCompact.exists_bound_of_continuousOn (isCompact_Icc (a := -η) (b := (1 : ℝ) + η))
      (hcd_ball.continuousOn.mono hIcc_ball)
  set B' : ℝ := max B 0 with hB'def
  have hB'0 : 0 ≤ B' := le_max_right B 0
  have hB' : ∀ t ∈ Set.Icc (-η) ((1 : ℝ) + η),
      ‖Submission.JacobiCoords.chartCoords (I := I) z γ V t‖ ≤ B' :=
    fun t ht => le_trans (hB t ht) (le_max_left B 0)
  have hfs : 0 < Submission.GExpFlow.flowScale F.D := Submission.GExpFlow.flowScale_pos F.D
  set X : ℝ := Submission.GExpFlow.flowScale F.D * d * B' with hXdef
  have hX0 : 0 ≤ X := by
    rw [hXdef]; exact mul_nonneg (mul_nonneg hfs.le hd.le) hB'0
  have hX1 : 0 < X + 1 := by linarith
  set δ : ℝ := 1 / (X + 1) with hδdef
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have hbd : X * δ ≤ 1 := by
    rw [hδdef, mul_one_div, div_le_one hX1]
    linarith
  have hbd' : Submission.GExpFlow.flowScale F.D * δ * (d * B') ≤ 1 := by
    have h : Submission.GExpFlow.flowScale F.D * δ * (d * B') = X * δ := by
      rw [hXdef]; ring
    rw [h]; exact hbd
  have hbd'' : Submission.GExpFlow.flowScale F.D * (δ * (d * B')) ≤ 1 := by
    have h : Submission.GExpFlow.flowScale F.D * (δ * (d * B'))
        = Submission.GExpFlow.flowScale F.D * δ * (d * B') := by ring
    rw [h]; exact hbd'
  -- the phase bound
  have hgen_smul : ∀ (w : E) (σ : ℝ),
      ‖Submission.GExpFlow.flowScale F.D • (σ • w)‖
        = Submission.GExpFlow.flowScale F.D * (|σ| * ‖w‖) := by
    intro w σ
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hfs]
  have hnorm : ∀ σ ∈ Set.Icc (-δ) δ, ∀ t ∈ Set.Icc (-η) ((1 : ℝ) + η),
      ‖Submission.GExpFlow.flowScale F.D • (σ • u t)‖ ≤ 1 := by
    intro σ hσ t ht
    have hσabs : |σ| ≤ δ := abs_le.mpr hσ
    have hu_t : ‖u t‖ ≤ d * B' := by
      show ‖d • Submission.JacobiCoords.chartCoords (I := I) z γ V t‖ ≤ d * B'
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hd]
      exact mul_le_mul_of_nonneg_left (hB' t ht) hd.le
    rw [hgen_smul (u t) σ]
    calc Submission.GExpFlow.flowScale F.D * (|σ| * ‖u t‖)
        ≤ Submission.GExpFlow.flowScale F.D * (δ * (d * B')) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul hσabs hu_t (norm_nonneg (u t)) hδ.le) hfs.le
      _ ≤ 1 := hbd''
  -- the phase of the chart-flow datum
  have hph : ∀ σ ∈ Set.Icc (-δ) δ, ∀ t ∈ Set.Icc (-η) ((1 : ℝ) + η),
      (Submission.IntrinsicVariation.chartCoord (I := I) z γ t,
        Submission.GExpFlow.flowScale F.D • (σ • u t)) ∈
        Submission.GExpFlow.chartData (I := I) z F.Z := by
    intro σ hσ t ht
    rw [show Submission.GExpFlow.chartData (I := I) z F.Z
        = ((extChartAt I z) '' F.Z) ×ˢ Metric.closedBall (0 : E) 1 from rfl, Set.mem_prod]
    refine ⟨⟨γ t, (hmemIcc t ht).2.2, rfl⟩, ?_⟩
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact hnorm σ hσ t ht
  -- joint smoothness of the chart model and of its `t`-partial
  have hFam : ContDiffOn ℝ ∞ (Submission.IntrinsicVariation.Fam (cov := cov) F.D
      (Submission.IntrinsicVariation.chartCoord (I := I) z γ) u)
      (Set.Ioo (-δ) δ ×ˢ Set.Ioo (-η) ((1 : ℝ) + η)) :=
    Submission.IntrinsicVariation.contDiffOn_fam (cov := cov) (η := η) (L := 1) (δ := δ)
      (x := Submission.IntrinsicVariation.chartCoord (I := I) z γ) (u := u) F.D hx hu hph
  have hRopen : IsOpen (Set.Ioo (-δ) δ ×ˢ Set.Ioo (-η) ((1 : ℝ) + η)) :=
    isOpen_Ioo.prod isOpen_Ioo
  have hpsi : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => Submission.IntrinsicVariation.psiW (cov := cov)
      F.D (Submission.IntrinsicVariation.chartCoord (I := I) z γ) u q.1 q.2)
      (Set.Ioo (-δ) δ ×ˢ Set.Ioo (-η) ((1 : ℝ) + η)) :=
    Submission.IntrinsicVariation.contDiffOn_psiW (cov := cov) (x :=
      Submission.IntrinsicVariation.chartCoord (I := I) z γ) (u := u) F.D hRopen hFam
  have h0memIooδ : (0 : ℝ) ∈ Set.Ioo (-δ) δ := ⟨by linarith [hδ], hδ⟩
  have h0mem : ((0 : ℝ), (1 / 2 : ℝ)) ∈ Set.Ioo (-δ) δ ×ˢ Set.Ioo (-η) ((1 : ℝ) + η) :=
    Set.mk_mem_prod h0memIooδ hhalfIoo
  have hcontψ : ContinuousAt (fun q : ℝ × ℝ => Submission.IntrinsicVariation.psiW (cov := cov)
      F.D (Submission.IntrinsicVariation.chartCoord (I := I) z γ) u q.1 q.2)
      ((0 : ℝ), (1 / 2 : ℝ)) :=
    hpsi.continuousOn.continuousAt (hRopen.mem_nhds h0mem)
  -- the chart model computes the variation
  have hWfam : ∀ σ t, (σ, t) ∈ Set.Ioo (-δ) δ ×ˢ Set.Ioo (-η) ((1 : ℝ) + η) →
      (extChartAt I z) (Submission.GlobalExp.GExp (cov := cov) hmet (γ t) (σ • (d • V t)))
        = Submission.IntrinsicVariation.fam (cov := cov) F.D
            (Submission.IntrinsicVariation.chartCoord (I := I) z γ) u σ t := by
    intro σ t hσt
    rw [Set.mem_prod] at hσt
    have htIcc : t ∈ Set.Icc (-η) ((1 : ℝ) + η) := ⟨le_of_lt hσt.2.1, le_of_lt hσt.2.2⟩
    have hσIcc : σ ∈ Set.Icc (-δ) δ := ⟨le_of_lt hσt.1.1, le_of_lt hσt.1.2⟩
    have hsrc : γ t ∈ (chartAt H z).source := (hmemIcc t htIcc).2.1
    have hγZ : γ t ∈ F.Z := (hmemIcc t htIcc).2.2
    have hsrcExt : γ t ∈ (extChartAt I z).source := by
      simpa only [extChartAt_source (I := I) z] using hsrc
    have hphase : (Submission.IntrinsicVariation.chartCoord (I := I) z γ t,
        Submission.GExpFlow.flowScale F.D • (σ • u t)) ∈ F.D.O :=
      F.D.hKO (hph σ hσIcc t htIcc)
    have hVeq : V t = Submission.Geodesic.frameVector (I := I) z (γ t)
        (Submission.JacobiCoords.chartCoords (I := I) z γ V t) :=
      (Submission.JacobiCoords.frameVector_chartCoords (I := I) (x₀ := z) (J := V) hsrc).symm
    have hrep : σ • (d • V t) = Submission.Geodesic.frameVector (I := I) z (γ t) (σ • u t) := by
      have h2 : d • V t = Submission.Geodesic.frameVector (I := I) z (γ t)
          (d • Submission.JacobiCoords.chartCoords (I := I) z γ V t) := by
        rw [hVeq, ← Submission.Geodesic.frameVector_smul]
      rw [h2, ← Submission.Geodesic.frameVector_smul]
    rw [hrep, Submission.UniformInj.GExp_eq_symm_Hfun (cov := cov) hmet F.D hγZ hsrcExt hphase]
    exact (extChartAt I z).right_inv
      (Submission.SecondVarGlobal.fam_mem_target' (cov := cov) F.D hphase)
  -- the value of the model at `σ = 0`
  have hxZev : ∀ᶠ t' in 𝓝 (1 / 2 : ℝ),
      (Submission.IntrinsicVariation.chartCoord (I := I) z γ) t' ∈ (extChartAt I z) '' F.Z :=
    Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hhalfIoo)
      (fun t' ht' => ⟨γ t', (hmemIoo t' ht').2.2, rfl⟩)
  have hψzero : Submission.IntrinsicVariation.psiW (cov := cov) F.D
      (Submission.IntrinsicVariation.chartCoord (I := I) z γ) u 0 (1 / 2)
      = deriv (fun t' : ℝ => (extChartAt I z) (γ t')) (1 / 2) := by
    have h := Submission.SecondVarGlobal.psiW_zero (cov := cov)
      (x := Submission.IntrinsicVariation.chartCoord (I := I) z γ) (u := u) F.D hxZev
    simpa only [Submission.IntrinsicVariation.chartCoord] using h
  -- the two sides of the limit
  have hpairEv : (fun n => deriv (fun τ : ℝ => (extChartAt I z)
        (Submission.GlobalExp.GExp (cov := cov) hmet (γ τ) (σn n • (d • V τ)))) (tn n))
      =ᶠ[atTop] (fun n => Submission.IntrinsicVariation.psiW (cov := cov) F.D
        (Submission.IntrinsicVariation.chartCoord (I := I) z γ) u (σn n) (tn n)) := by
    filter_upwards [hσ.eventually (Filter.eventually_of_mem
        (isOpen_Ioo.mem_nhds h0memIooδ) (fun y hy => hy)),
      ht.eventually (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hhalfIoo) (fun y hy => hy))]
      with n hσn htn
    have hev : (fun τ : ℝ => (extChartAt I z)
          (Submission.GlobalExp.GExp (cov := cov) hmet (γ τ) (σn n • (d • V τ))))
        =ᶠ[𝓝 (tn n)] (fun τ : ℝ => Submission.IntrinsicVariation.fam (cov := cov) F.D
          (Submission.IntrinsicVariation.chartCoord (I := I) z γ) u (σn n) τ) :=
      Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds htn)
        (fun τ hτ => hWfam (σn n) τ (Set.mk_mem_prod hσn hτ))
    exact hev.deriv_eq
  have hpairs : Tendsto (fun n => (σn n, tn n)) atTop (𝓝 ((0 : ℝ), (1 / 2 : ℝ))) :=
    (Prod.tendsto_iff (fun n => (σn n, tn n)) ((0 : ℝ), (1 / 2 : ℝ))).mpr ⟨hσ, ht⟩
  have hlimψ : Tendsto (fun n => Submission.IntrinsicVariation.psiW (cov := cov) F.D
        (Submission.IntrinsicVariation.chartCoord (I := I) z γ) u (σn n) (tn n)) atTop
      (𝓝 (Submission.IntrinsicVariation.psiW (cov := cov) F.D
        (Submission.IntrinsicVariation.chartCoord (I := I) z γ) u 0 (1 / 2))) := by
    have h := hcontψ.tendsto.comp hpairs
    simpa only [Function.comp_def] using h
  have hmain : Tendsto (fun n => deriv (fun τ : ℝ => (extChartAt I z)
        (Submission.GlobalExp.GExp (cov := cov) hmet (γ τ) (σn n • (d • V τ)))) (tn n)) atTop
      (𝓝 (Submission.IntrinsicVariation.psiW (cov := cov) F.D
        (Submission.IntrinsicVariation.chartCoord (I := I) z γ) u 0 (1 / 2))) :=
    hlimψ.congr' hpairEv.symm
  rw [hψzero] at hmain
  exact hmain


end Work.EvenBound.ThirdGeodesic
