import Mathlib
import Submission.Work.OddBound.LiftKit
import Submission.GExpJointPt

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

namespace Work.OddBound.polygonValue

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval
open Submission.Geodesic Submission.GlobalExp Submission.Length Submission.InjRadius
open Submission.ChartConnection

/-- **Joint inverse continuity of the exponential map in the base point.**

Let `Z` be a compact piece of the source of the chart at `z₀`, let the exponential map at every
`q ∈ Z` be injective on the ball of radius `ρ`, and let `ρ' < ρ`.  Then the map

`(q, u) ↦ (extChartAt I z₀ q, GExp q (frameVector z₀ q u))`

is *uniformly injective* on the compact set `{(q,u) | q ∈ Z, ‖frameVector z₀ q u‖ ≤ ρ'}`: two points
of that set whose chart-coordinates of the base points are close *and* whose images under the
exponential map are close have close coordinate vectors `u, u'`.

The proof is the standard compactness argument, run entirely in the model space `E` (the base
manifold `M` carries no `FirstCountableTopology` instance here).

* `Submission.ChartBounds.exists_chartGram_bounds` bounds the chart metric on the compact set `Z`
  from below, so the fibre bound `‖frameVector z₀ q u‖ ≤ ρ'` bounds the coordinate vector `u` by
  `M₀ = ρ' / √lam`; the domain is therefore a subset of the compact product
  `((extChartAt I z₀) '' Z)² × (closedBall 0 M₀)²`, where a failing sequence has a convergent
  subsequence (`IsCompact.tendsto_subseq`).
* `Submission.GExpJointPt.tendsto_GExp_frameVector` is joint continuity of
  `(q, u) ↦ GExp q (frameVector z₀ q u)` in base point and coordinates, and it turns the limits of
  the image subsequences into `GExp q₀ (frameVector z₀ q₀ u∞)`, resp. `GExp q₀ (frameVector z₀ q₀ u'∞)`.
* Equality of the chart-coordinate limits (`z.1.1 = z.1.2`) and of the two images (`riemannianEDist`
  arguments using the one-sided comparison lemmas of `Submission.EDist`) force the two limit
  coordinate vectors `u∞, u'∞` to coincide: `hinj` makes the frame vectors equal, and
  `frameVector_eq_zero_iff` makes the coordinates equal.
* This contradicts the strict separation `ε ≤ ‖u - u'‖` along the sequence. -/
theorem joint_inverse_continuity
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {z₀ : M} {Z : Set M} (hZsrc : Z ⊆ (chartAt H z₀).source) (hZc : IsCompact Z)
    {ρ ρ' : ℝ} (hρ'pos : 0 < ρ') (hρ'ρ : ρ' < ρ)
    (hinj : ∀ q ∈ Z, Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet q ρ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q ∈ Z, ∀ q' ∈ Z, ∀ u u' : E,
      ‖Submission.Geodesic.frameVector (I := I) z₀ q u‖ ≤ ρ' →
      ‖Submission.Geodesic.frameVector (I := I) z₀ q' u'‖ ≤ ρ' →
      ‖(extChartAt I z₀) q - (extChartAt I z₀) q'‖ < δ →
      Manifold.riemannianEDist I
        (Submission.GlobalExp.GExp (cov := cov) hmet q (Submission.Geodesic.frameVector (I := I) z₀ q u))
        (Submission.GlobalExp.GExp (cov := cov) hmet q' (Submission.Geodesic.frameVector (I := I) z₀ q' u'))
          < ENNReal.ofReal δ →
      ‖u - u'‖ < ε := by
  classical
  haveI hcb : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  haveI hproper : ProperSpace E := FiniteDimensional.proper ℝ E
  rcases Z.eq_empty_or_nonempty with hZemp | hZne
  · refine ⟨1, one_pos, ?_⟩
    intro q hq
    rw [hZemp] at hq
    simp at hq
  · obtain ⟨lam, hlam, Lam, hLam, hbnd⟩ :=
      Submission.ChartBounds.exists_chartGram_bounds (I := I) z₀ hZc hZne hZsrc
    have hsub : Z ⊆ (extChartAt I z₀).source := fun q hq => by simpa using hZsrc hq
    set M₀ : ℝ := ρ' / Real.sqrt lam with hM₀def
    have hM₀pos : 0 < M₀ := div_pos hρ'pos (Real.sqrt_pos.mpr hlam)
    -- the fibre bound on the velocity implies a coordinate bound
    have hbound : ∀ q ∈ Z, ∀ u : E, ‖frameVector (I := I) z₀ q u‖ ≤ ρ' → ‖u‖ ≤ M₀ := by
      intro q hq u hu
      have hg : 0 ≤ chartGram (I := I) z₀ q u u := le_trans (by positivity) (hbnd q hq u).1
      have hsq : ‖frameVector (I := I) z₀ q u‖ ^ 2 = chartGram (I := I) z₀ q u u := by
        rw [Submission.GExpFlow.norm_frameVector, Real.sq_sqrt hg]
      have h1 : lam * ‖u‖ ^ 2 ≤ ‖frameVector (I := I) z₀ q u‖ ^ 2 := by
        rw [hsq]
        exact (hbnd q hq u).1
      have h3 : ‖frameVector (I := I) z₀ q u‖ ^ 2 ≤ ρ' ^ 2 := by
        nlinarith [hu, norm_nonneg (frameVector (I := I) z₀ q u), hρ'pos.le]
      have h2 : ‖u‖ ^ 2 ≤ M₀ ^ 2 := by
        rw [hM₀def, div_pow, Real.sq_sqrt hlam.le, le_div_iff₀ hlam]
        nlinarith [h1, h3]
      have h4 := sq_le_sq.mp h2
      rwa [abs_of_nonneg (norm_nonneg u), abs_of_nonneg hM₀pos.le] at h4
    by_contra hcon
    push Not at hcon
    have hbad : ∀ n : ℕ, ∃ q ∈ Z, ∃ q' ∈ Z, ∃ u : E, ∃ u' : E,
        ‖frameVector (I := I) z₀ q u‖ ≤ ρ' ∧ ‖frameVector (I := I) z₀ q' u'‖ ≤ ρ' ∧
        ‖(extChartAt I z₀) q - (extChartAt I z₀) q'‖ < 1 / (n + 1 : ℝ) ∧
        Manifold.riemannianEDist I
          (GExp (cov := cov) hmet q (frameVector (I := I) z₀ q u))
          (GExp (cov := cov) hmet q' (frameVector (I := I) z₀ q' u'))
            < ENNReal.ofReal (1 / (n + 1 : ℝ)) ∧
        ε ≤ ‖u - u'‖ := fun n => hcon (1 / (n + 1 : ℝ)) (by positivity)
    choose q hqZ q' hq'Z u u' hspec using hbad
    have hmemK : ∀ n, (((extChartAt I z₀) (q n), (extChartAt I z₀) (q' n)), (u n, u' n)) ∈
        (((extChartAt I z₀) '' Z) ×ˢ ((extChartAt I z₀) '' Z)) ×ˢ
          (Metric.closedBall (0 : E) M₀ ×ˢ Metric.closedBall (0 : E) M₀) := by
      intro n
      refine ⟨⟨⟨q n, hqZ n, rfl⟩, ⟨q' n, hq'Z n, rfl⟩⟩, ?_, ?_⟩
      · rw [Metric.mem_closedBall, dist_zero_right]
        exact hbound (q n) (hqZ n) (u n) (hspec n).1
      · rw [Metric.mem_closedBall, dist_zero_right]
        exact hbound (q' n) (hq'Z n) (u' n) (hspec n).2.1
    obtain ⟨z, hz, φ, hφ, hzlim⟩ := IsCompact.tendsto_subseq
      (((hZc.image_of_continuousOn ((continuousOn_extChartAt (I := I) z₀).mono hsub)).prod
        (hZc.image_of_continuousOn ((continuousOn_extChartAt (I := I) z₀).mono hsub))).prod
        ((isCompact_closedBall (0 : E) M₀).prod (isCompact_closedBall (0 : E) M₀)))
      (x := fun n => (((extChartAt I z₀) (q n), (extChartAt I z₀) (q' n)), (u n, u' n))) hmemK
    obtain ⟨⟨hzZ, hzZ'⟩, -, -⟩ := hz
    obtain ⟨q₀, hq₀Z, hq₀eq⟩ := hzZ
    obtain ⟨q₁, hq₁Z, hq₁eq⟩ := hzZ'
    have hq₀src : q₀ ∈ (extChartAt I z₀).source := hsub hq₀Z
    have hq₁src : q₁ ∈ (extChartAt I z₀).source := hsub hq₁Z
    have hsubT : ∀ p ∈ Z, (extChartAt I z₀) p ∈ (extChartAt I z₀).target :=
      fun p hp => PartialEquiv.map_source _ (hsub hp)
    have hsymm : ContinuousOn (fun x : E => (extChartAt I z₀).symm x) (extChartAt I z₀).target :=
      (contMDiffOn_extChartAt_symm (I := I) (n := ∞) z₀).continuousOn
    have hzlim' : Tendsto (fun n => (((extChartAt I z₀) (q (φ n)), (extChartAt I z₀) (q' (φ n))),
        (u (φ n), u' (φ n)))) atTop (𝓝 z) := hzlim
    have hxc : Tendsto (fun n => (extChartAt I z₀) (q (φ n))) atTop (𝓝 z.1.1) :=
      (continuous_fst.tendsto z.1).comp ((continuous_fst.tendsto z).comp hzlim')
    have hxc' : Tendsto (fun n => (extChartAt I z₀) (q' (φ n))) atTop (𝓝 z.1.2) :=
      (continuous_snd.tendsto z.1).comp ((continuous_fst.tendsto z).comp hzlim')
    have huc : Tendsto (fun n => u (φ n)) atTop (𝓝 z.2.1) :=
      (continuous_fst.tendsto z.2).comp ((continuous_snd.tendsto z).comp hzlim')
    have hu'c : Tendsto (fun n => u' (φ n)) atTop (𝓝 z.2.2) :=
      (continuous_snd.tendsto z.2).comp ((continuous_snd.tendsto z).comp hzlim')
    -- the chart coordinates of the base points coincide in the limit
    have hdchart : Tendsto (fun n => ‖(extChartAt I z₀) (q (φ n)) - (extChartAt I z₀) (q' (φ n))‖)
        atTop (𝓝 ‖z.1.1 - z.1.2‖) := (hxc.sub hxc').norm
    have hchartlim : z.1.1 = z.1.2 := by
      have hsmall : Tendsto (fun n : ℕ => 1 / (φ n + 1 : ℝ)) atTop (𝓝 0) :=
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hφ.tendsto_atTop
      have h0 : ‖z.1.1 - z.1.2‖ ≤ 0 := by
        refine le_of_tendsto_of_tendsto' hdchart hsmall ?_
        intro n
        exact le_of_lt ((hspec (φ n)).2.2.1)
      exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h0 (norm_nonneg _)))
    have hqq' : q₀ = q₁ := by
      have heq : (extChartAt I z₀) q₀ = (extChartAt I z₀) q₁ := by
        rw [hq₀eq, hq₁eq]
        exact hchartlim
      have hs : (extChartAt I z₀).symm ((extChartAt I z₀) q₀)
          = (extChartAt I z₀).symm ((extChartAt I z₀) q₁) := by rw [heq]
      rwa [PartialEquiv.left_inv (extChartAt I z₀) hq₀src,
        PartialEquiv.left_inv (extChartAt I z₀) hq₁src] at hs
    subst hqq'
    -- the base points converge in `M`
    have hqc : Tendsto (fun n => q (φ n)) atTop (𝓝 q₀) := by
      have hxq : Tendsto (fun n => (extChartAt I z₀) (q (φ n))) atTop
          (𝓝 ((extChartAt I z₀) q₀)) := by
        rw [hq₀eq]
        exact hxc
      have htend : Tendsto (fun n => (extChartAt I z₀) (q (φ n))) atTop
          (𝓝[(extChartAt I z₀).target] ((extChartAt I z₀) q₀)) :=
        tendsto_nhdsWithin_iff.mpr
          ⟨hxq, Filter.Eventually.of_forall fun n => hsubT (q (φ n)) (hqZ (φ n))⟩
      have h1 : Tendsto (fun n => (extChartAt I z₀).symm ((extChartAt I z₀) (q (φ n)))) atTop
          (𝓝 ((extChartAt I z₀).symm ((extChartAt I z₀) q₀))) :=
        (hsymm.continuousWithinAt (hsubT q₀ hq₀Z)).tendsto.comp htend
      have h1' : Tendsto (fun n => (extChartAt I z₀).symm ((extChartAt I z₀) (q (φ n)))) atTop
          (𝓝 q₀) := by
        rwa [PartialEquiv.left_inv (extChartAt I z₀) hq₀src] at h1
      exact Tendsto.congr'
        (Filter.Eventually.of_forall fun n =>
          PartialEquiv.left_inv (extChartAt I z₀) (hsub (hqZ (φ n)))) h1'
    have hq'c : Tendsto (fun n => q' (φ n)) atTop (𝓝 q₀) := by
      have hxq' : Tendsto (fun n => (extChartAt I z₀) (q' (φ n))) atTop
          (𝓝 ((extChartAt I z₀) q₀)) := by
        rw [hq₁eq]
        exact hxc'
      have htend : Tendsto (fun n => (extChartAt I z₀) (q' (φ n))) atTop
          (𝓝[(extChartAt I z₀).target] ((extChartAt I z₀) q₀)) :=
        tendsto_nhdsWithin_iff.mpr
          ⟨hxq', Filter.Eventually.of_forall fun n => hsubT (q' (φ n)) (hq'Z (φ n))⟩
      have h1 : Tendsto (fun n => (extChartAt I z₀).symm ((extChartAt I z₀) (q' (φ n)))) atTop
          (𝓝 ((extChartAt I z₀).symm ((extChartAt I z₀) q₀))) :=
        (hsymm.continuousWithinAt (hsubT q₀ hq₀Z)).tendsto.comp htend
      have h1' : Tendsto (fun n => (extChartAt I z₀).symm ((extChartAt I z₀) (q' (φ n)))) atTop
          (𝓝 q₀) := by
        rwa [PartialEquiv.left_inv (extChartAt I z₀) hq₀src] at h1
      exact Tendsto.congr'
        (Filter.Eventually.of_forall fun n =>
          PartialEquiv.left_inv (extChartAt I z₀) (hsub (hq'Z (φ n)))) h1'
    -- the two image sequences
    have hlim1 : Tendsto (fun n => GExp (cov := cov) hmet (q (φ n))
          (frameVector (I := I) z₀ (q (φ n)) (u (φ n)))) atTop
        (𝓝 (GExp (cov := cov) hmet q₀ (frameVector (I := I) z₀ q₀ z.2.1))) :=
      Submission.GExpJointPt.tendsto_GExp_frameVector (cov := cov) (I := I) (z₀ := z₀) (p := q₀)
        (q := fun n => q (φ n)) (a := fun n => u (φ n)) (a₀ := z.2.1)
        hmet htor (hZsrc hq₀Z) hqc huc
    have hlim2 : Tendsto (fun n => GExp (cov := cov) hmet (q' (φ n))
          (frameVector (I := I) z₀ (q' (φ n)) (u' (φ n)))) atTop
        (𝓝 (GExp (cov := cov) hmet q₀ (frameVector (I := I) z₀ q₀ z.2.2))) :=
      Submission.GExpJointPt.tendsto_GExp_frameVector (cov := cov) (I := I) (z₀ := z₀) (p := q₀)
        (q := fun n => q' (φ n)) (a := fun n => u' (φ n)) (a₀ := z.2.2)
        hmet htor (hZsrc hq₀Z) hq'c hu'c
    -- the second sequence also tends to the first limit, because the images are close
    have hmix : Tendsto (fun n => GExp (cov := cov) hmet (q' (φ n))
          (frameVector (I := I) z₀ (q' (φ n)) (u' (φ n)))) atTop
        (𝓝 (GExp (cov := cov) hmet q₀ (frameVector (I := I) z₀ q₀ z.2.1))) := by
      refine tendsto_iff_forall_eventually_mem.mpr fun s hs => ?_
      obtain ⟨c, hc, hsubc⟩ :=
        Submission.EDist.setOf_riemannianEDist_lt_subset_nhds (I := I) hs
      have hc2 : (0 : ℝ≥0∞) < c / 2 := ENNReal.half_pos hc.ne'
      have h1 : ∀ᶠ n in atTop, Manifold.riemannianEDist I
          (GExp (cov := cov) hmet q₀ (frameVector (I := I) z₀ q₀ z.2.1))
          (GExp (cov := cov) hmet (q (φ n))
            (frameVector (I := I) z₀ (q (φ n)) (u (φ n)))) < c / 2 :=
        hlim1.eventually (Submission.EDist.eventually_riemannianEDist_lt (I := I)
          (GExp (cov := cov) hmet q₀ (frameVector (I := I) z₀ q₀ z.2.1)) hc2)
      have hsmall : ∀ᶠ n : ℕ in atTop, ENNReal.ofReal (1 / (n + 1 : ℝ)) < c / 2 := by
        have h : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / (n + 1 : ℝ))) atTop
            (𝓝 (ENNReal.ofReal (0 : ℝ))) :=
          (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp
            (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
        have hc2' : ENNReal.ofReal (0 : ℝ) < c / 2 := by simpa using hc2
        exact h.eventually_lt_const hc2'
      have h2 : ∀ᶠ n in atTop, Manifold.riemannianEDist I
          (GExp (cov := cov) hmet (q (φ n)) (frameVector (I := I) z₀ (q (φ n)) (u (φ n))))
          (GExp (cov := cov) hmet (q' (φ n))
            (frameVector (I := I) z₀ (q' (φ n)) (u' (φ n)))) < c / 2 := by
        filter_upwards [hφ.tendsto_atTop.eventually hsmall] with n hn
        exact lt_of_lt_of_le (hspec (φ n)).2.2.2.1 hn.le
      filter_upwards [h1, h2] with n hn1 hn2
      refine hsubc ?_
      calc Manifold.riemannianEDist I
            (GExp (cov := cov) hmet q₀ (frameVector (I := I) z₀ q₀ z.2.1))
            (GExp (cov := cov) hmet (q' (φ n))
              (frameVector (I := I) z₀ (q' (φ n)) (u' (φ n))))
          ≤ Manifold.riemannianEDist I
              (GExp (cov := cov) hmet q₀ (frameVector (I := I) z₀ q₀ z.2.1))
              (GExp (cov := cov) hmet (q (φ n))
                (frameVector (I := I) z₀ (q (φ n)) (u (φ n))))
            + Manifold.riemannianEDist I
              (GExp (cov := cov) hmet (q (φ n))
                (frameVector (I := I) z₀ (q (φ n)) (u (φ n))))
              (GExp (cov := cov) hmet (q' (φ n))
                (frameVector (I := I) z₀ (q' (φ n)) (u' (φ n)))) :=
            Manifold.riemannianEDist_triangle
        _ < c / 2 + c / 2 := ENNReal.add_lt_add hn1 hn2
        _ = c := ENNReal.add_halves c
    -- the images at the limit coincide
    have himg : GExp (cov := cov) hmet q₀ (frameVector (I := I) z₀ q₀ z.2.2)
        = GExp (cov := cov) hmet q₀ (frameVector (I := I) z₀ q₀ z.2.1) :=
      tendsto_nhds_unique hlim2 hmix
    -- the fibre norms at the limit are still bounded by `ρ'`
    have hframe1 : Tendsto (fun n => ‖frameVector (I := I) z₀ (q (φ n)) (u (φ n))‖) atTop
        (𝓝 ‖frameVector (I := I) z₀ q₀ z.2.1‖) := by
      have hcont := Submission.ChartBounds.continuousAt_chartGram_prod (I := I) z₀
        (hZsrc hq₀Z) z.2.1
      have hpair : Tendsto (fun n => (q (φ n), u (φ n))) atTop (𝓝 (q₀, z.2.1)) :=
        (Prod.tendsto_iff (fun n => (q (φ n), u (φ n))) (q₀, z.2.1)).mpr ⟨hqc, huc⟩
      have h1 : Tendsto (fun n => chartGram (I := I) z₀ (q (φ n)) (u (φ n)) (u (φ n))) atTop
          (𝓝 (chartGram (I := I) z₀ q₀ z.2.1 z.2.1)) := hcont.tendsto.comp hpair
      have h2 := Real.continuous_sqrt.continuousAt.tendsto.comp h1
      simpa only [Function.comp_def, Submission.GExpFlow.norm_frameVector] using h2
    have hnormlim1 : ‖frameVector (I := I) z₀ q₀ z.2.1‖ ≤ ρ' :=
      le_of_tendsto_of_tendsto' hframe1 tendsto_const_nhds (fun n => (hspec (φ n)).1)
    have hframe2 : Tendsto (fun n => ‖frameVector (I := I) z₀ (q' (φ n)) (u' (φ n))‖) atTop
        (𝓝 ‖frameVector (I := I) z₀ q₀ z.2.2‖) := by
      have hcont := Submission.ChartBounds.continuousAt_chartGram_prod (I := I) z₀
        (hZsrc hq₀Z) z.2.2
      have hpair : Tendsto (fun n => (q' (φ n), u' (φ n))) atTop (𝓝 (q₀, z.2.2)) :=
        (Prod.tendsto_iff (fun n => (q' (φ n), u' (φ n))) (q₀, z.2.2)).mpr ⟨hq'c, hu'c⟩
      have h1 : Tendsto (fun n => chartGram (I := I) z₀ (q' (φ n)) (u' (φ n)) (u' (φ n))) atTop
          (𝓝 (chartGram (I := I) z₀ q₀ z.2.2 z.2.2)) := hcont.tendsto.comp hpair
      have h2 := Real.continuous_sqrt.continuousAt.tendsto.comp h1
      simpa only [Function.comp_def, Submission.GExpFlow.norm_frameVector] using h2
    have hnormlim2 : ‖frameVector (I := I) z₀ q₀ z.2.2‖ ≤ ρ' :=
      le_of_tendsto_of_tendsto' hframe2 tendsto_const_nhds (fun n => (hspec (φ n)).2.1)
    have hfv : frameVector (I := I) z₀ q₀ z.2.2 = frameVector (I := I) z₀ q₀ z.2.1 :=
      hinj q₀ hq₀Z (frameVector (I := I) z₀ q₀ z.2.2) (frameVector (I := I) z₀ q₀ z.2.1)
        (lt_of_le_of_lt hnormlim2 hρ'ρ) (lt_of_le_of_lt hnormlim1 hρ'ρ) himg
    have hsubv : frameVector (I := I) z₀ q₀ (z.2.2 - z.2.1) = 0 := by
      have h1 : frameVector (I := I) z₀ q₀ (z.2.2 - z.2.1)
          = frameVector (I := I) z₀ q₀ z.2.2 - frameVector (I := I) z₀ q₀ z.2.1 := by
        rw [sub_eq_add_neg, ← neg_one_smul ℝ z.2.1, Submission.Geodesic.frameVector_add,
          Submission.Geodesic.frameVector_smul, neg_one_smul, sub_eq_add_neg]
      rw [h1, hfv, sub_self]
    have hzero : z.2.2 - z.2.1 = 0 :=
      (Submission.ChartBounds.frameVector_eq_zero_iff (I := I) (x₀ := z₀) (p := q₀)
        (by simpa using hq₀src) (z.2.2 - z.2.1)).mp hsubv
    have hfarlim : ε ≤ ‖z.2.1 - z.2.2‖ :=
      le_of_tendsto_of_tendsto' tendsto_const_nhds ((huc.sub hu'c).norm)
        (fun n => (hspec (φ n)).2.2.2.2)
    rw [← (sub_eq_zero.mp hzero), sub_self, norm_zero] at hfarlim
    linarith


end Work.OddBound.polygonValue
