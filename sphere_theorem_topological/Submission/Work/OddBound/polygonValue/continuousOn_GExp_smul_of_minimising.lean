import Mathlib
import Submission.Work.OddBound.LiftKit
import Submission.Work.OddBound.polygonValue.InterpAux
import Submission.GExpJointPt
import Submission.Work.OddBound.polygonValue.joint_inverse_continuity
import Submission.Work.OddBound.polygonValue.gExp_joint_tendsto

namespace Work.OddBound.polygonValue

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval

set_option autoImplicit false

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]

/-- **Joint continuity of the minimising interpolation between moving nearby points.**

`x, y : ℝ → M` are continuous and, on `[0,1]`, the point `y τ` is at Riemannian distance `< ρ` from
`x τ`, where `ρ` is a uniform lower bound for the injectivity radius (at every point of `M`).  Let
`V τ` be *the* minimising vector from `x τ` to `y τ`, i.e. any family satisfying
`GExp (x τ) (V τ) = y τ` and `d (x τ) (y τ) = ‖V τ‖` (below `ρ` such a family is unique, so `S r τ =
GExp (x τ) (r • V τ)` is the canonical minimising geodesic interpolation).  Then `S` is **jointly
continuous** on `[0,1] × [0,1]`.

Proof route (the ingredients are available in the workspace): fix `τ₀ ∈ [0,1]` and a
`(r₀, τ₀) ∈ [0,1]²`.

1. *Coordinate continuity of `V`:* in the chart at `x τ₀`, the coordinates
   `u τ = (trivializationAt E (TangentSpace I) (x τ₀)).continuousLinearMapAt ℝ (x τ) (V τ)` tend to
   `u τ₀` as `τ → τ₀` along `𝓝[Icc 0 1] τ₀`.  Fixing a compact chart piece `Z ∋ x τ₀`
   (`Submission.GSField.exists_isCompact_subset_chart_source`), the chart Gram bounds
   (`Submission.ChartBounds.exists_chartGram_bounds`) bound `‖u τ‖` by `ρ / √λ`, so any sequence
   `τ n → τ₀` has a subsequence with `u (τ n) → a∞` (Bolzano–Weierstrass,
   `IsCompact.tendsto_subseq`); the joint continuity of `(q,a) ↦ GExp q (frameVector z₀ q a)` in
   chart coordinates (`Submission.GExpJointPt.tendsto_GExp_frameVector`, which has **no** bound on the
   velocity) gives `GExp (x τ₀) (frameVector z₀ (x τ₀) a∞) = y τ₀`, and the norm identity
   `‖frameVector z₀ (x τ₀) a∞‖ = d (x τ₀) (y τ₀)` follows from the continuity of the chart Gram and of
   the Riemannian distance (`Work.OddBound.polygonValue.tendsto_riemannianDist_of_tendsto_of_metricCompatible`, in the
   `InterpAux` module); uniqueness of the minimising vector below the injectivity radius
   (`Submission.InjRadius.exists_unique_GExp_of_injAtLeast`) then identifies `a∞ = u τ₀`, and
   `Filter.tendsto_of_subseq_tendsto` upgrades "every subsequence has a sub-subsequence converging to
   `u τ₀`" to the filter statement.
2. *Assembly:* for `(s n, τ n) → (r₀, τ₀)` inside the square,
   `GExp (x (τ n)) (s n • V (τ n)) = GExp (x (τ n)) (frameVector z₀ (x (τ n)) (s n • u (τ n)))`
   (`frameVector_smul` + `frameVector_clm`), and step 1 with
   `Submission.GExpJointPt.tendsto_GExp_frameVector` gives convergence to `GExp (x τ₀) (r₀ • V τ₀)`.
   Again `Filter.tendsto_of_subseq_tendsto` + `continuousOn_iff_continuousWithinAt` finish. -/
theorem continuousOn_GExp_smul_of_minimising
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {x y : ℝ → M} (hxc : Continuous x) (hyc : Continuous y)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hinj : ∀ q : M, Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet q ρ)
    (hclose : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      Manifold.riemannianEDist I (x τ) (y τ) < ENNReal.ofReal ρ)
    (V : (τ : ℝ) → TangentSpace I (x τ))
    (hV : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      Submission.GlobalExp.GExp (cov := cov) hmet (x τ) (V τ) = y τ ∧
        Manifold.riemannianEDist I (x τ) (y τ) = ENNReal.ofReal ‖V τ‖) :
    ContinuousOn
      (fun u : ℝ × ℝ => Submission.GlobalExp.GExp (cov := cov) hmet (x u.2) (u.1 • V u.2))
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) := by
  classical
  haveI hcb : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  -- ## Bookkeeping on the minimising vectors
  have hVnorm : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖V τ‖ < ρ := by
    intro τ hτ
    have h : Manifold.riemannianEDist I (x τ) (y τ) < ENNReal.ofReal ρ := hclose τ hτ
    rw [(hV τ hτ).2] at h
    exact (ENNReal.ofReal_lt_ofReal_iff hρ).mp h
  have hVdist : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      Submission.Distance.riemannianDist (I := I) (x τ) (y τ) = ‖V τ‖ := by
    intro τ hτ
    rw [Work.OddBound.polygon.riemannianDist_eq_toReal (I := I) (x τ) (y τ), (hV τ hτ).2,
      ENNReal.toReal_ofReal (norm_nonneg _)]
  -- ## Fix a point of the square
  intro p₀ hp₀
  obtain ⟨r₀, τ₀⟩ := p₀
  simp only [Set.mem_prod, Set.mem_Icc] at hp₀
  obtain ⟨⟨hr₀0, hr₀1⟩, hτ₀0, hτ₀1⟩ := hp₀
  have hτ₀mem : τ₀ ∈ Set.Icc (0 : ℝ) 1 := ⟨hτ₀0, hτ₀1⟩
  set z₀ : M := x τ₀ with hz₀
  have hVz : Submission.GlobalExp.GExp (cov := cov) hmet z₀ (V τ₀) = y τ₀ := (hV τ₀ hτ₀mem).1
  have hVznorm : ‖V τ₀‖ < ρ := hVnorm τ₀ hτ₀mem
  have hVzdist : Submission.Distance.riemannianDist (I := I) z₀ (y τ₀) = ‖V τ₀‖ :=
    hVdist τ₀ hτ₀mem
  -- ## A compact chart frame at `z₀`
  obtain ⟨F⟩ := Submission.GExpJointPt.exists_chartFrame (cov := cov) (I := I) hmet
    (z := z₀) (p := z₀) (mem_chart_source H z₀)
  have hZc : IsCompact F.Z := F.hZc
  have hZsrc : F.Z ⊆ (chartAt H z₀).source := F.hZsrc
  have hZsrc' : F.Z ⊆ (extChartAt I z₀).source := fun q hq => by simpa using hZsrc hq
  have hFη : ‖(extChartAt I z₀) z₀ - F.x‖ < F.η := by
    rw [F.hx, sub_self, norm_zero]; exact F.hη
  have hZnhds : F.Z ∈ 𝓝 z₀ := F.nhds_of_strict (mem_chart_source H z₀) hFη
  have hz₀Z : z₀ ∈ F.Z := F.mem_of_norm (mem_chart_source H z₀) hFη
  have hz₀src : z₀ ∈ (extChartAt I z₀).source := by simpa using mem_chart_source H z₀
  -- ## The coordinate vector of the minimising vector in the chart at `z₀`
  let u : ℝ → E := fun τ =>
    (Trivialization.continuousLinearMapAt ℝ (trivializationAt E (TangentSpace I) z₀) (x τ))
      (V τ)
  have hufv : ∀ τ, x τ ∈ (extChartAt I z₀).source →
      Submission.Geodesic.frameVector (I := I) z₀ (x τ) (u τ) = V τ := by
    intro τ hτ
    exact Submission.GExpFlow.frameVector_clm (I := I) (z₀ := z₀) hτ (V τ)
  have hufvz : Submission.Geodesic.frameVector (I := I) z₀ z₀ (u τ₀) = V τ₀ := hufv τ₀ hz₀src
  -- ## Step 1: continuity of the coordinate vector
  have hu_tendsto : Tendsto u (𝓝[Set.Icc (0 : ℝ) 1] τ₀) (𝓝 (u τ₀)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    set ρ' : ℝ := (ρ + ‖V τ₀‖) / 2 with hρ'def
    have hρ'pos : 0 < ρ' := by rw [hρ'def]; linarith [norm_nonneg (V τ₀), hρ]
    have hρ'ρ : ρ' < ρ := by rw [hρ'def]; linarith
    have hVτ₀ρ' : ‖V τ₀‖ < ρ' := by rw [hρ'def]; linarith
    -- the uniform inverse-continuity statement on the compact frame
    obtain ⟨δ, hδpos, hδ⟩ := joint_inverse_continuity
      (I := I) (cov := cov) (z₀ := z₀) (Z := F.Z) hmet htor hZsrc hZc hρ'pos hρ'ρ
      (fun q _ => hinj q) hε
    -- the Riemannian distance is continuous
    have hdistcont :
        Tendsto (fun τ : ℝ => Submission.Distance.riemannianDist (I := I) (x τ) (y τ))
          (𝓝 τ₀) (𝓝 (Submission.Distance.riemannianDist (I := I) z₀ (y τ₀))) := by
      rw [Filter.tendsto_iff_seq_tendsto]
      intro seq hseq
      have h1 : Tendsto (fun n => x (seq n)) atTop (𝓝 (x τ₀)) :=
        Filter.Tendsto.comp hxc.continuousAt hseq
      have h2 : Tendsto (fun n => y (seq n)) atTop (𝓝 (y τ₀)) :=
        Filter.Tendsto.comp hyc.continuousAt hseq
      simpa only [Function.comp_def] using
        Work.OddBound.polygonValue.tendsto_riemannianDist_of_tendsto_of_metricCompatible (I := I) (cov := cov)
          hmet htor h1 h2
    have hdistEv : ∀ᶠ τ in 𝓝 (τ₀ : ℝ),
        Submission.Distance.riemannianDist (I := I) (x τ) (y τ) < ρ' := by
      refine hdistcont.eventually (isOpen_Iio.mem_nhds ?_)
      rw [Set.mem_Iio, hVzdist]; exact hVτ₀ρ'
    have hxZEv : ∀ᶠ τ in 𝓝 (τ₀ : ℝ), x τ ∈ F.Z := hxc.continuousAt hZnhds
    have hchartEv : ∀ᶠ τ in 𝓝 (τ₀ : ℝ),
        ‖(extChartAt I z₀) (x τ) - (extChartAt I z₀) z₀‖ < δ := by
      have hcont : ContinuousAt (fun τ : ℝ => (extChartAt I z₀) (x τ)) τ₀ :=
        (continuousAt_extChartAt' (I := I) (x := z₀) (x' := x τ₀) hz₀src).comp hxc.continuousAt
      simpa only [Metric.mem_ball, dist_eq_norm] using
        hcont.eventually (Metric.ball_mem_nhds ((extChartAt I z₀) z₀) hδpos)
    have hyEv : ∀ᶠ τ in 𝓝 (τ₀ : ℝ),
        Manifold.riemannianEDist I (y τ₀) (y τ) < ENNReal.ofReal δ :=
      hyc.continuousAt.eventually
        (Submission.EDist.eventually_riemannianEDist_lt (I := I) (y τ₀)
          (ENNReal.ofReal_pos.mpr hδpos))
    filter_upwards [self_mem_nhdsWithin, hxZEv.filter_mono nhdsWithin_le_nhds,
      hdistEv.filter_mono nhdsWithin_le_nhds, hchartEv.filter_mono nhdsWithin_le_nhds,
      hyEv.filter_mono nhdsWithin_le_nhds] with τ hτmem hxZ hdist hchart hy
    have hxsrc : x τ ∈ (extChartAt I z₀).source := hZsrc' hxZ
    have hVlt : ‖V τ‖ < ρ' := by rw [← hVdist τ hτmem]; exact hdist
    have hfn : ‖Submission.Geodesic.frameVector (I := I) z₀ (x τ) (u τ)‖ ≤ ρ' := by
      rw [hufv τ hxsrc]; exact hVlt.le
    have hfnz : ‖Submission.Geodesic.frameVector (I := I) z₀ z₀ (u τ₀)‖ ≤ ρ' := by
      rw [hufvz]; exact hVτ₀ρ'.le
    have hed : Manifold.riemannianEDist I
        (Submission.GlobalExp.GExp (cov := cov) hmet (x τ)
          (Submission.Geodesic.frameVector (I := I) z₀ (x τ) (u τ)))
        (Submission.GlobalExp.GExp (cov := cov) hmet z₀
          (Submission.Geodesic.frameVector (I := I) z₀ z₀ (u τ₀))) < ENNReal.ofReal δ := by
      have hsym : Manifold.riemannianEDist I (y τ) (y τ₀)
          = Manifold.riemannianEDist I (y τ₀) (y τ) :=
        Manifold.riemannianEDist_comm (I := I) (x := y τ) (y := y τ₀)
      rw [hufv τ hxsrc, hufvz, (hV τ hτmem).1, hVz, hsym]
      exact hy
    have hfin := hδ (x τ) hxZ z₀ hz₀Z (u τ) (u τ₀) hfn hfnz hchart hed
    simpa only [dist_eq_norm] using hfin
  -- ## Step 2: assembly
  have hgoal : Tendsto
      (fun p : ℝ × ℝ => Submission.GlobalExp.GExp (cov := cov) hmet (x p.2) (p.1 • V p.2))
      (𝓝[Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1] (r₀, τ₀))
      (𝓝 (Submission.GlobalExp.GExp (cov := cov) hmet z₀ (r₀ • V τ₀))) := by
    have hsnd : Tendsto (fun p : ℝ × ℝ => p.2)
        (𝓝[Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1] (r₀, τ₀))
        (𝓝[Set.Icc (0 : ℝ) 1] τ₀) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · exact (continuous_snd.tendsto (r₀, τ₀)).mono_left nhdsWithin_le_nhds
      · exact Filter.mem_of_superset self_mem_nhdsWithin (fun p hp => hp.2)
    have hq : Tendsto (fun p : ℝ × ℝ => x p.2)
        (𝓝[Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1] (r₀, τ₀)) (𝓝 z₀) :=
      ((hxc.continuousAt).mono_left nhdsWithin_le_nhds).comp hsnd
    have hu : Tendsto (fun p : ℝ × ℝ => u p.2)
        (𝓝[Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1] (r₀, τ₀)) (𝓝 (u τ₀)) :=
      hu_tendsto.comp hsnd
    have hfst : Tendsto (fun p : ℝ × ℝ => p.1)
        (𝓝[Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1] (r₀, τ₀)) (𝓝 r₀) :=
      (continuous_fst.tendsto (r₀, τ₀)).mono_left nhdsWithin_le_nhds
    have ha : Tendsto (fun p : ℝ × ℝ => p.1 • u p.2)
        (𝓝[Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1] (r₀, τ₀)) (𝓝 (r₀ • u τ₀)) :=
      hfst.smul hu
    have hkey := gExp_joint_tendsto (cov := cov) (I := I)
      (z₀ := z₀) (p := z₀) (l := 𝓝[Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1] (r₀, τ₀))
      hmet htor (mem_chart_source H z₀) hq ha
    have hlim : Submission.GlobalExp.GExp (cov := cov) hmet z₀
        (Submission.Geodesic.frameVector (I := I) z₀ z₀ (r₀ • u τ₀))
        = Submission.GlobalExp.GExp (cov := cov) hmet z₀ (r₀ • V τ₀) := by
      rw [Submission.Geodesic.frameVector_smul (I := I), hufvz]
    rw [hlim] at hkey
    refine hkey.congr' ?_
    filter_upwards [hq.eventually hZnhds] with p hpZ
    have hsrc : x p.2 ∈ (extChartAt I z₀).source := hZsrc' hpZ
    rw [Submission.Geodesic.frameVector_smul (I := I), hufv p.2 hsrc]
  show Tendsto
      (fun p : ℝ × ℝ => Submission.GlobalExp.GExp (cov := cov) hmet (x p.2) (p.1 • V p.2))
      (𝓝[Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1] (r₀, τ₀))
      (𝓝 (Submission.GlobalExp.GExp (cov := cov) hmet (x τ₀) (r₀ • V τ₀)))
  exact hgoal

end Work.OddBound.polygonValue
