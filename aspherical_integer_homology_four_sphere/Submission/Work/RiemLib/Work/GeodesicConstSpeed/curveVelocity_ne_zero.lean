import Mathlib
import Submission.Work.RiemLib.RauchK
import Submission.Work.RiemLib.Geodesic
import Submission.Work.RiemLib.GeodesicSpeed
import Submission.Work.RiemLib.Length
import Submission.Work.RiemLib.Distance
import Submission.Work.RiemLib.InjRadius
import Submission.Work.RiemLib.InjBall
import Submission.Work.RiemLib.SegmentDomain
import Submission.Work.RiemLib.XuMain
import Submission.Work.RiemLib.EDist
import Submission.Work.RiemLib.GExpRay2
import Submission.Work.RiemLib.GExpJoint
import Submission.Work.RiemLib.GExpFlow
import Submission.Work.RiemLib.Commons.Geometry.Manifold.exists_finite_cover_isCompact_subset_chartAt
import Submission.Work.RiemLib.GeodesicGlobal
import Submission.Work.RiemLib.GExpLocalInj
import Submission.Work.RiemLib.CutStep2
import Submission.Work.RiemLib.XuLift
import Submission.Work.RiemLib.ChartPieces
import Submission.Work.RiemLib.ChartIndep
import Submission.Work.RiemLib.CoeffSmooth2
import Submission.Work.RiemLib.JacobiGlobal
import Submission.Work.RiemLib.Commons.Analysis.ODE.exists_linearODE_solution_Icc
import Submission.Work.RiemLib.IndexCorner2
import Submission.Work.RiemLib.InjHalf
import Submission.Work.RiemLib.LensLoop
import Submission.Work.RiemLib.UniformInj
import Submission.Work.RiemLib.ConjRadius
import Submission.Work.RiemLib.ConjCut
import Submission.Work.RiemLib.SingularConj
import Submission.Work.RiemLib.RayConj
import Submission.Work.RiemLib.Gauss
import Submission.Work.RiemLib.ExpBound2
import Submission.Work.RiemLib.JacobiGauss
import Submission.Work.RiemLib.Minimal
import Submission.Work.RiemLib.Variation
import Submission.Work.RiemLib.CurveField
import Submission.Work.RiemLib.ChartBounds
import Submission.Work.RiemLib.GlobalBM
import Submission.Work.RiemLib.Commons.Analysis.Calculus.eqOn_of_hasDerivAt_eq_zero_Icc

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.GeodesicConstSpeed

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open LeanEval.Geometry.SphereTheorem Submission.Geodesic Submission.JacobiGlobal Submission.GlobalExp Submission.Length Submission.InjRadius

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
  [I.Boundaryless]

/-! ## Auxiliary lemmas

The proof of `curveVelocity_ne_zero` rests on three facts about the squared speed
`t ↦ ⟪γ'(t), γ'(t)⟫` of a geodesic on an open interval `(a,b)`:

* it is continuous on `(a,b)` (proved by writing it, near a point, as the chart metric
  evaluated on the derivative of the coordinate curve — `continuousAt_sqSpeed`);
* it is locally constant at every point where it does not vanish: the velocity field extends
  to a *global* smooth section near such a point (`Submission.CurveField`), and metric
  compatibility applied to that section together with the geodesic equation shows that the
  derivative of the squared speed vanishes on a neighbourhood (`exists_Ioo_sqSpeed_eq`);
* a continuous function on `(a,b)` which is locally constant wherever it is nonzero is
  constant on `(a,b)` (`eqOn_Ioo_of_continuousOn_of_eventually_const`).

The last statement is proved by the usual clopen argument on the connected set `Ioo a b`. -/

/-- **A continuous function on an open interval that is locally constant wherever it is nonzero
is constant.**  With `c := f t₀` and `c ≠ 0`, the set where `f = c` is nonempty, open (local
constancy) and closed (continuity), hence all of the connected interval `Ioo a b`. -/
lemma eqOn_Ioo_of_continuousOn_of_eventually_const
    {f : ℝ → ℝ} {a b c : ℝ} (hcont : ContinuousOn f (Set.Ioo a b))
    (hloc : ∀ t ∈ Set.Ioo a b, f t = c →
      ∃ δ > 0, Set.Ioo (t - δ) (t + δ) ⊆ {s | f s = c})
    {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo a b) (hc : f t₀ = c) :
    ∀ t ∈ Set.Ioo a b, f t = c := by
  set s : Set ℝ := Set.Ioo a b with hs
  set B : Set ℝ := {t | f t = c} with hB
  set U : Set ℝ := s ∩ interior B with hU
  have hUopen : IsOpen U := IsOpen.inter isOpen_Ioo isOpen_interior
  have hUsub : U ⊆ B := fun t ht => interior_subset ht.2
  have hsU : s ∩ B ⊆ U := by
    rintro t ⟨hts, htB⟩
    obtain ⟨δ, hδ, hδB⟩ := hloc t hts (by rw [hB] at htB; exact htB)
    refine ⟨hts, mem_interior_iff_mem_nhds.mpr ?_⟩
    exact Filter.mem_of_superset (Ioo_mem_nhds (by linarith) (by linarith)) hδB
  set V : Set ℝ := (closure (B ∩ s))ᶜ with hV
  have hVopen : IsOpen V := isClosed_closure.isOpen_compl
  have hclosed : ∀ t ∈ s, t ∈ closure (B ∩ s) → t ∈ B := by
    intro t ht hmem
    rw [hB]
    have hfreq : ∃ᶠ y in 𝓝 t, y ∈ B ∩ s := mem_closure_iff_frequently.mp hmem
    have hfr : ∃ᶠ y in 𝓝 t, f y = c :=
      hfreq.mono (fun y hy => by rw [hB] at hy; exact hy.1)
    have hct : ContinuousAt f t := hcont.continuousAt (Ioo_mem_nhds ht.1 ht.2)
    by_contra htc
    have hnb : f ⁻¹' ({c}ᶜ : Set ℝ) ∈ 𝓝 t :=
      hct.preimage_mem_nhds (isClosed_singleton.isOpen_compl.mem_nhds (by simpa using htc))
    have hev : ∀ᶠ y in 𝓝 t, ¬ (f y = c) := by
      filter_upwards [hnb] with y hy h
      exact hy (by simp [h])
    exact (Filter.not_frequently.mpr hev) hfr
  have hdisj : Disjoint U V := by
    rw [Set.disjoint_left]
    intro t htU htV
    rw [hV] at htV
    exact htV (subset_closure ⟨hUsub htU, htU.1⟩)
  have hcover : s ⊆ U ∪ V := by
    intro t ht
    by_cases htB : t ∈ B
    · exact Or.inl (hsU ⟨ht, htB⟩)
    · refine Or.inr ?_
      rw [hV]
      exact fun hmem => htB (hclosed t ht hmem)
  have hne : (s ∩ U).Nonempty := ⟨t₀, ht₀, hsU ⟨ht₀, by rw [hB]; exact hc⟩⟩
  rcases isPreconnected_Ioo.subset_or_subset hUopen hVopen hdisj hcover with hsub | hsub
  · intro t ht
    exact hUsub (hsub ht)
  · obtain ⟨x, hxs, hxU⟩ := hne
    exact (Set.disjoint_left.mp hdisj hxU (hsub hxs)).elim

section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
  [I.Boundaryless]
  {a b : ℝ} {γ : ℝ → M}

/-- **The squared speed of a `C^∞` curve is continuous.**  Near a point `t₁` the curve stays in
the chart at `x₁ = γ t₁`; there the squared speed is the chart metric evaluated on the derivative
of the coordinate curve, and `chartGram` is jointly continuous (`ChartBounds`). -/
lemma continuousAt_sqSpeed
    (hsm : ContMDiffOn 𝓘(ℝ) I ∞ γ (Set.Ioo a b))
    {t₁ : ℝ} (ht₁ : t₁ ∈ Set.Ioo a b) :
    ContinuousAt (fun t : ℝ => inner ℝ (curveVelocity (I := I) γ t)
      (curveVelocity (I := I) γ t)) t₁ := by
  set x₁ : M := γ t₁ with hx₁
  have hx₁src : x₁ ∈ (chartAt H x₁).source := mem_chart_source H x₁
  set u : ℝ → E := fun t => (extChartAt I x₁) (γ t) with hu
  have hγc : ContinuousAt γ t₁ := hsm.continuousOn.continuousAt (Ioo_mem_nhds ht₁.1 ht₁.2)
  obtain ⟨ε₁, hε₁, hε₁mem⟩ := Metric.mem_nhds_iff.mp
    (hγc.preimage_mem_nhds ((chartAt H x₁).open_source.mem_nhds hx₁src))
  set ε : ℝ := min ε₁ 1 with hεdef
  have hεpos : 0 < ε := lt_min hε₁ one_pos
  have hεle : ε ≤ ε₁ := min_le_left _ _
  set J : Set ℝ := Set.Ioo (max a (t₁ - ε)) (min b (t₁ + ε)) with hJ
  have hJopen : IsOpen J := isOpen_Ioo
  have hJsub : J ⊆ Set.Ioo a b := by
    intro t ht
    exact ⟨lt_of_le_of_lt (le_max_left a (t₁ - ε)) ht.1,
      lt_of_lt_of_le ht.2 (min_le_left b (t₁ + ε))⟩
  have hJsrc : J ⊆ γ ⁻¹' (chartAt H x₁).source := by
    intro t ht
    have htlo : t₁ - ε < t := lt_of_le_of_lt (le_max_right a (t₁ - ε)) ht.1
    have hthi : t < t₁ + ε := lt_of_lt_of_le ht.2 (min_le_right b (t₁ + ε))
    have hmem : dist t t₁ < ε₁ := by
      rw [Real.dist_eq, abs_lt]
      exact ⟨by linarith, by linarith⟩
    exact hε₁mem hmem
  have hu : ContDiffOn ℝ ∞ u J := by
    have h2 : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, E) ∞ u J :=
      (contMDiffOn_extChartAt (I := I) (x := x₁)).comp (hsm.mono hJsub) (fun t ht => hJsrc ht)
    exact h2.contDiffOn
  have hv : ContDiffOn ℝ ∞ (deriv u) J := hu.deriv_of_isOpen hJopen (le_of_eq (by simp))
  have hJmem : J ∈ 𝓝 t₁ := Ioo_mem_nhds (max_lt ht₁.1 (by linarith)) (lt_min ht₁.2 (by linarith))
  have hdu : ContinuousAt (deriv u) t₁ := hv.continuousOn.continuousAt hJmem
  have hgram : ContinuousAt
      (fun t : ℝ => Submission.ChartConnection.chartGram (I := I) x₁ (γ t) (deriv u t) (deriv u t)) t₁ :=
    (Submission.ChartBounds.continuousAt_chartGram_prod (I := I) x₁ hx₁src (deriv u t₁)).comp₂
      hγc hdu
  refine hgram.congr ?_
  filter_upwards [hγc.preimage_mem_nhds ((chartAt H x₁).open_source.mem_nhds hx₁src),
    Ioo_mem_nhds ht₁.1 ht₁.2] with t hsrc ht
  have hγt : MDifferentiableAt 𝓘(ℝ) I γ t :=
    (hsm.contMDiffAt (Ioo_mem_nhds ht.1 ht.2)).mdifferentiableAt (by simp)
  have hdt : deriv u t = (trivializationAt E (TangentSpace I) x₁).continuousLinearMapAt ℝ (γ t)
      (curveVelocity (I := I) γ t) :=
    Submission.GlobalBM.deriv_extChartAt_eq_continuousLinearMapAt_curveVelocity (I := I) x₁ hγt hsrc
  rw [hdt]
  exact Submission.GExpFlow.chartGram_clm (I := I) (z₀ := x₁) (q := γ t)
    (by rwa [extChartAt_source]) _ _

variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}

/-- **The squared speed is locally constant at a point of non-vanishing velocity.**  If
`γ'(t) ≠ 0` then, near `t`, the velocity field of `γ` agrees with a globally smooth section `Z`
(`Submission.CurveField.exists_contMDiff_section_eventuallyEq_curveVelocity`).  The derivative of
`s ↦ ⟪Z (γ s), Z (γ s)⟫` is `2⟪∇_{γ'}Z, Z⟫`, which vanishes by the geodesic equation at each
point of a neighbourhood of `t` (a globally smooth section agreeing with the velocity field *near*
`s` is a legitimate test field for `IsGeodesicAt` at `s`).  Hence the squared speed is constant on
an interval around `t`. -/
lemma exists_Ioo_sqSpeed_eq
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov)
    (hsm : ContMDiffOn 𝓘(ℝ) I ∞ γ (Set.Ioo a b))
    (hgeo : ∀ t ∈ Set.Ioo a b, IsGeodesicAt cov γ t)
    {t : ℝ} (ht : t ∈ Set.Ioo a b)
    (hne : curveVelocity (I := I) γ t ≠ 0) :
    ∃ δ > 0, Set.Ioo (t - δ) (t + δ) ⊆
      {s | inner ℝ (curveVelocity (I := I) γ s) (curveVelocity (I := I) γ s)
          = inner ℝ (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t)} := by
  obtain ⟨Z, hZsm, hZev⟩ :=
    Submission.CurveField.exists_contMDiff_section_eventuallyEq_curveVelocity (I := I)
      (V := Set.Ioo a b) isOpen_Ioo ht hsm hne
  have hZev' : {s : ℝ | Z (γ s) = curveVelocity (I := I) γ s} ∈ 𝓝 t := hZev
  obtain ⟨ε, hεpos, hε⟩ := Metric.mem_nhds_iff.mp hZev'
  have hball : ∀ r ∈ Set.Ioo (t - ε) (t + ε), r ∈ Metric.ball t ε := by
    intro r hr
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hZeq : ∀ r ∈ Set.Ioo (t - ε) (t + ε),
      Z (γ r) = curveVelocity (I := I) γ r :=
    fun r hr => hε (hball r hr)
  set δ : ℝ := min ε (min (t - a) (b - t)) with hδdef
  have hδpos : 0 < δ := lt_min hεpos (lt_min (by linarith [ht.1]) (by linarith [ht.2]))
  have hδε : δ ≤ ε := min_le_left _ _
  have hδa : δ ≤ t - a := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδb : δ ≤ b - t := le_trans (min_le_right _ _) (min_le_right _ _)
  have hsub_ε : Set.Ioo (t - δ) (t + δ) ⊆ Set.Ioo (t - ε) (t + ε) :=
    Set.Ioo_subset_Ioo (by linarith) (by linarith)
  have hsub_ab : Set.Ioo (t - δ) (t + δ) ⊆ Set.Ioo a b := by
    intro r hr
    exact ⟨by linarith [hr.1, hδa], by linarith [hr.2, hδb]⟩
  refine ⟨δ, hδpos, ?_⟩
  intro s hs
  have hst : s ∈ Set.Ioo (t - ε) (t + ε) := hsub_ε hs
  have hst' : t ∈ Set.Ioo (t - ε) (t + ε) := ⟨by linarith, by linarith⟩
  have hder : ∀ r ∈ Set.Ioo (t - δ) (t + δ),
      HasDerivAt (fun r => inner ℝ (Z (γ r)) (Z (γ r))) 0 r := by
    intro r hr
    have hra : r ∈ Set.Ioo a b := hsub_ab hr
    have hrε : r ∈ Set.Ioo (t - ε) (t + ε) := hsub_ε hr
    have hγr : MDifferentiableAt 𝓘(ℝ) I γ r :=
      (hsm.contMDiffAt (Ioo_mem_nhds hra.1 hra.2)).mdifferentiableAt (by simp)
    have hevr : ∀ᶠ σ in 𝓝 r, Z (γ σ) = curveVelocity (I := I) γ σ :=
      Filter.eventually_of_mem (Ioo_mem_nhds hrε.1 hrε.2) hZeq
    have hcov := hgeo r hra Z hZsm hevr
    have h := Submission.Variation.hasDerivAt_inner_sections cov hmet hZsm hZsm hγr
    rw [hcov] at h
    simpa using h
  have hconst : inner ℝ (Z (γ s)) (Z (γ s)) = inner ℝ (Z (γ t)) (Z (γ t)) := by
    rcases le_total t s with hts | hst2
    · have hsub : Set.Icc t s ⊆ Set.Ioo (t - δ) (t + δ) := by
        intro z hz
        exact ⟨by linarith [hz.1, hδpos], by linarith [hz.2, hs.2]⟩
      exact Commons.Analysis.Calculus.eqOn_of_hasDerivAt_eq_zero_Icc hts
        (fun z hz => hder z (hsub hz)) s ⟨hts, le_rfl⟩
    · have hsub : Set.Icc s t ⊆ Set.Ioo (t - δ) (t + δ) := by
        intro z hz
        exact ⟨by linarith [hz.1, hs.1], by linarith [hz.2, hδpos]⟩
      exact (Commons.Analysis.Calculus.eqOn_of_hasDerivAt_eq_zero_Icc hst2
        (fun z hz => hder z (hsub hz)) t ⟨hst2, le_rfl⟩).symm
  calc inner ℝ (curveVelocity (I := I) γ s) (curveVelocity (I := I) γ s)
      = inner ℝ (Z (γ s)) (Z (γ s)) := by rw [hZeq s hst]
    _ = inner ℝ (Z (γ t)) (Z (γ t)) := hconst
    _ = inner ℝ (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t) := by
        rw [hZeq t hst']

end

theorem curveVelocity_ne_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov)
    {a b : ℝ} {γ : ℝ → M}
    (hsm : ContMDiffOn 𝓘(ℝ) I ∞ γ (Set.Ioo a b))
    (hgeo : ∀ t ∈ Set.Ioo a b, Submission.Geodesic.IsGeodesicAt cov γ t)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo a b)
    (hne : Submission.Geodesic.curveVelocity (I := I) γ t₀ ≠ 0) :
    ∀ t ∈ Set.Ioo a b, Submission.Geodesic.curveVelocity (I := I) γ t ≠ 0 := by
  have hc : 0 < inner ℝ (curveVelocity (I := I) γ t₀) (curveVelocity (I := I) γ t₀) :=
    lt_of_le_of_ne real_inner_self_nonneg (fun h0 => hne (inner_self_eq_zero.mp h0.symm))
  have hmain : ∀ t ∈ Set.Ioo a b,
      inner ℝ (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t)
        = inner ℝ (curveVelocity (I := I) γ t₀) (curveVelocity (I := I) γ t₀) := by
    refine eqOn_Ioo_of_continuousOn_of_eventually_const
      (f := fun s : ℝ => inner ℝ (curveVelocity (I := I) γ s) (curveVelocity (I := I) γ s))
      (c := inner ℝ (curveVelocity (I := I) γ t₀) (curveVelocity (I := I) γ t₀))
      (fun x hx => (continuousAt_sqSpeed (I := I) hsm hx).continuousWithinAt) ?_ ht₀ rfl
    intro t ht hft
    have hcne : inner ℝ (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t) ≠ 0 := by
      rw [hft]; exact ne_of_gt hc
    have hne' : curveVelocity (I := I) γ t ≠ 0 :=
      fun h0 => hcne (inner_self_eq_zero.mpr h0)
    obtain ⟨δ, hδpos, hδsub⟩ := exists_Ioo_sqSpeed_eq (I := I) hmet hsm hgeo ht hne'
    exact ⟨δ, hδpos, fun s hs => by
      have h : inner ℝ (curveVelocity (I := I) γ s) (curveVelocity (I := I) γ s)
          = inner ℝ (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t) := hδsub hs
      rw [← hft]
      exact h⟩
  intro t ht hvel
  have hz : inner ℝ (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t) = 0 :=
    inner_self_eq_zero.mpr hvel
  rw [hmain t ht] at hz
  exact absurd hz (ne_of_gt hc)

end Work.GeodesicConstSpeed
