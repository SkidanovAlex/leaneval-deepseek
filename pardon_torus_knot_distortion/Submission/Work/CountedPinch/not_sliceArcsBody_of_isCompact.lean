import Mathlib
import Submission.Work.CountedPinch.Arcs
import Submission.Work.BoxShrink.PinchOff.CompactSlice
import Submission.Work.Smooth.Plane.All
import Submission.Work.CountedPinch.exists_lt_mem_of_isOpen_Icc_zero
import Submission.Work.CountedPinch.oneSided_of_arcEndpoint

/-!
# A compact slice is not a finite disjoint union of arcs

The naive "arcs" datum `Work.CountedPinch.SliceArcsBody` of the counted chapter asks that the
*closure* of the slice be covered by finitely many pairwise disjoint embedded arcs
`a j : [0,1] → ℝ³` whose images lie in that closure.  For a slice which is not compact — the
generic case, the trace of the cutting plane leaving Pardon's open box through the box sphere —
this is the honest structure of the trace.

This module records the *other* half of the dichotomy: at a configuration whose slice is **compact**
(and non-empty, and at which the plane meets the surface transversely, so that the slice is locally
Euclidean of dimension one), the datum `SliceArcsBody` **fails**.  The mathematics is the local
structure at the endpoint `a j 0` of one of the arcs: the germ of the arc at its endpoint is a
*one-sided* open neighbourhood of the point inside the arc, whose puncture is connected; a locally
Euclidean space of dimension one has no such neighbourhood at any of its points (every open
neighbourhood of a point of `ℝ` has disconnected puncture, and this is a homeomorphism invariant).

Equivalently: a compact slice is a finite disjoint union of *circles*
(`Work.BoxShrink.PinchOff.isCircleUnion_sigma_of_isCompact`), and a non-empty finite disjoint union
of circles is not a finite disjoint union of arcs; with the datum `SliceArcsBody` the arcs would be
exactly the connected components, and a component of the locally Euclidean slice would be the range
of an embedded arc with two free ends.

## The proof

* `hA : SliceArcsBody` and `hc : IsCompact S` give `S = ⋃ j, range (a j)`, the ranges being pairwise
  disjoint and compact, hence closed (`S` is closed, so `closure S = S`);
* the non-emptiness of `S` selects an arc `a j₀`, and `x := a j₀ 0 ∈ S`;
* the chart at `x` (`isLocallyEuclidean_sigma_of_transverseSlice`) gives an open neighbourhood
  `V ∋ x` homeomorphic to `ℝ`; shrinking it away from the finitely many *other* compact ranges gives
  an open `V₃ ∋ x` with `V₃ ⊆ range (a j₀)`;
* the one-sided germ of the arc at `x` (`Work.CountedPinch.oneSided_of_arcEndpoint`, a one-sided
  open neighbourhood of the endpoint of an embedded arc whose range already fills a neighbourhood of
  it) supplies an open `U ∋ x`, `U ⊆ V₃`, with `U \ {x}` preconnected;
* pulling `U` back through the chart gives an open neighbourhood of `0` in `ℝ` with preconnected
  puncture, contradicting `not_isPreconnected_sdiff_zero_of_isOpen` here.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
set_option linter.style.haveILetI false

open scoped ENNReal

namespace Work.CountedPinch

noncomputable section

/-- The left endpoint `0` of the unit interval `ArcInterval = [0,1]`. -/
abbrev leftEnd : Work.Smooth.Plane.ArcInterval := ⟨0, by norm_num⟩

/-- **No open neighbourhood of `0` in `ℝ` has preconnected puncture**: an open `U ⊆ ℝ` containing
`0` contains `(-ε, ε)` for some `ε > 0`, so `U \ {0}` is not ord-connected (the points `±ε/2` lie in
it but the point `0` between them does not). -/
theorem not_isPreconnected_sdiff_zero_of_isOpen {U : Set ℝ} (hU : IsOpen U)
    (h0 : (0 : ℝ) ∈ U) : ¬ IsPreconnected (U \ {0}) := by
  intro hpre
  have hord : (U \ {0}).OrdConnected := isPreconnected_iff_ordConnected.mp hpre
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0)
  have hmem1 : (-ε / 2) ∈ U \ {0} := by
    refine ⟨hball ?_, by simp only [Set.mem_singleton_iff]; linarith⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    constructor <;> linarith
  have hmem2 : (ε / 2) ∈ U \ {0} := by
    refine ⟨hball ?_, by simp only [Set.mem_singleton_iff]; linarith⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    constructor <;> linarith
  have hmem0 : (0 : ℝ) ∈ U \ {0} :=
    hord.out hmem1 hmem2 ⟨by linarith, by linarith⟩
  exact hmem2.2 (by simpa using hmem0.2)

/-- **A compact, non-empty, transverse slice is not a finite disjoint union of arcs.** -/
theorem not_sliceArcsBody_of_isCompact {ψ : Submission.Diffeo}
    {β : Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ)} {s : ℝ} {c : LeanEval.KnotTheory.PardonDistortion.R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hT : Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u)
    (hc : IsCompact (Work.CountedPinch.slice (Work.Smooth.Morse.torus ψ) s c σ u))
    (hne : (Work.CountedPinch.slice (Work.Smooth.Morse.torus ψ) s c σ u).Nonempty) :
    ¬ Work.CountedPinch.SliceArcsBody (Work.Smooth.Morse.torus ψ) β s c σ u := by
  classical
  rintro hA
  rw [sliceArcsBody_def] at hA
  obtain ⟨n, a, hinj, hmem, hdisj, hcov⟩ := hA
  set S : Set R3 := Work.CountedPinch.slice (Work.Smooth.Morse.torus ψ) s c σ u with hSdef
  have hcl : IsClosed S := hc.isClosed
  have hmemS : ∀ (j : Fin n) (t : Work.Smooth.Plane.ArcInterval), a j t ∈ S := fun j t => by
    have h := hmem j t
    rwa [hcl.closure_eq] at h
  have hsub : S ⊆ ⋃ j, Set.range (a j) := by
    have h := hcov
    rwa [hcl.closure_eq] at h
  obtain ⟨x, hx⟩ := hne
  obtain ⟨j0, -⟩ := Set.mem_iUnion.mp (hsub hx)
  let f : C(Work.Smooth.Plane.ArcInterval, ↥S) :=
    ⟨fun t => ⟨a j0 t, hmemS j0 t⟩,
      Continuous.subtype_mk (a j0).continuous (fun t => hmemS j0 t)⟩
  have hfval : ∀ t : Work.Smooth.Plane.ArcInterval, ((f t : ↥S) : R3) = a j0 t := fun t => rfl
  have hfinj : Function.Injective f := fun p q h => hinj j0 (by
    have := congrArg (fun z : ↥S => (z : R3)) h
    simpa [hfval] using this)
  -- the union of the *other* arcs
  set K : Set ↥S := ⋃ j : {j : Fin n // j ≠ j0}, {z : ↥S | (z : R3) ∈ Set.range (a j.1)}
    with hKdef
  have hKclosed : IsClosed K := by
    rw [hKdef]
    refine isClosed_iUnion_of_finite fun j => ?_
    exact ((isCompact_range (a j.1).continuous).isClosed).preimage continuous_subtype_val
  have hx0K : f leftEnd ∉ K := by
    rw [hKdef]
    intro hmemK
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hmemK
    obtain ⟨t, ht⟩ := hj
    exact Set.disjoint_left.mp (hdisj j.2) ⟨t, ht⟩ ⟨leftEnd, (hfval leftEnd).symm⟩
  -- the chart at the endpoint
  have hLE : Work.Smooth.SphereJordan.IsLocallyArc ↥S :=
    Work.BoxShrink.PinchOff.isLocallyEuclidean_sigma_of_transverseSlice hT
  obtain ⟨chart⟩ := hLE (f leftEnd)
  -- an open neighbourhood of the endpoint inside the chart and inside the arc
  set V₃ : Set ↥S := {z : ↥S | z ∈ chart.V ∧ z ∉ K} with hV₃def
  have hV₃open : IsOpen V₃ := chart.isOpen_V.inter hKclosed.isOpen_compl
  have hxV₃ : f leftEnd ∈ V₃ := ⟨chart.mem_V, hx0K⟩
  have hV₃sub : V₃ ⊆ Set.range f := by
    rintro z ⟨-, hzK⟩
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hsub z.2)
    have hjj : j = j0 := by
      by_contra hcon
      exact hzK (Set.mem_iUnion.mpr ⟨⟨j, hcon⟩, hj⟩)
    subst hjj
    obtain ⟨t, ht⟩ := hj
    exact ⟨t, Subtype.ext (by rw [hfval]; exact ht)⟩
  obtain ⟨U, hUopen, hxU, hUV₃, hUpre⟩ :=
    oneSided_of_arcEndpoint f hfinj hV₃open hxV₃ hV₃sub
  have hUV : U ⊆ chart.V := fun z hz => (hUV₃ hz).1
  -- pull the one-sided neighbourhood back through the chart
  set U' : Set ↥chart.V := {z : ↥chart.V | (z : ↥S) ∈ U} with hU'def
  have hU'open : IsOpen U' := hUopen.preimage continuous_subtype_val
  have hxU' : (⟨f leftEnd, chart.mem_V⟩ : ↥chart.V) ∈ U' := hxU
  set A : Set ℝ := chart.homeo ⁻¹' U' with hAdef
  have hAopen : IsOpen A := hU'open.preimage chart.homeo.continuous
  have h0A : (0 : ℝ) ∈ A := by
    show chart.homeo 0 ∈ U'
    rw [chart.homeo_zero]
    exact hxU'
  have hApre : IsPreconnected (A \ {0}) := by
    set Φ : ↥S → ℝ := fun z => if h : z ∈ chart.V then chart.coord ⟨z, h⟩ else 0 with hΦdef
    have hΦcont : ContinuousOn Φ (U \ {f leftEnd}) := by
      rw [continuousOn_iff_continuous_domRestrict]
      have hfun : Set.domRestrict (U \ {f leftEnd}) Φ =
          fun z : ↥(U \ {f leftEnd}) => chart.coord ⟨z.1, hUV z.2.1⟩ := by
        funext z
        show (if h : (z : ↥S) ∈ chart.V then chart.coord ⟨z.1, h⟩ else 0) =
          chart.coord ⟨z.1, hUV z.2.1⟩
        rw [dif_pos (hUV z.2.1)]
      rw [hfun]
      exact chart.continuous_coord.comp
        (Continuous.subtype_mk continuous_subtype_val (fun z => hUV z.2.1))
    have himg : Φ '' (U \ {f leftEnd}) = A \ {0} := by
      ext r
      constructor
      · rintro ⟨z, hz, rfl⟩
        have hzV : z ∈ chart.V := hUV hz.1
        have hΦz : Φ z = chart.coord ⟨z, hzV⟩ := by
          show (if h : z ∈ chart.V then chart.coord ⟨z, h⟩ else 0) = chart.coord ⟨z, hzV⟩
          rw [dif_pos hzV]
        have hcoord : chart.homeo (chart.coord ⟨z, hzV⟩) = ⟨z, hzV⟩ := by
          show chart.homeo (chart.homeo.symm ⟨z, hzV⟩) = ⟨z, hzV⟩
          exact chart.homeo.apply_symm_apply ⟨z, hzV⟩
        refine ⟨?_, ?_⟩
        · show chart.homeo (Φ z) ∈ U'
          rw [hΦz, hcoord]
          exact hz.1
        · intro h0
          have h0' : Φ z = 0 := Set.mem_singleton_iff.mp h0
          refine hz.2 ?_
          have h1 : (⟨z, hzV⟩ : ↥chart.V) = ⟨f leftEnd, chart.mem_V⟩ := by
            have h2 : chart.homeo (Φ z) = chart.homeo 0 := by rw [h0']
            rw [chart.homeo_zero] at h2
            rw [hΦz, hcoord] at h2
            exact h2
          rw [Set.mem_singleton_iff]
          exact congrArg (fun w : ↥chart.V => (w : ↥S)) h1
      · rintro ⟨hrA, hr0⟩
        set z : ↥S := ((chart.homeo r : ↥chart.V) : ↥S) with hzdef
        have hzV : z ∈ chart.V := (chart.homeo r).2
        have hzU : z ∈ U := hrA
        have hzK : z ≠ f leftEnd := by
          intro hcon
          have h2 : chart.homeo r = chart.homeo 0 := by
            rw [chart.homeo_zero]
            exact Subtype.ext hcon
          exact hr0 (chart.homeo.injective h2)
        refine ⟨z, ⟨hzU, ?_⟩, ?_⟩
        · rw [Set.mem_singleton_iff]
          exact hzK
        · have hΦz : Φ z = chart.coord ⟨z, hzV⟩ := by
            show (if h : z ∈ chart.V then chart.coord ⟨z, h⟩ else 0) = chart.coord ⟨z, hzV⟩
            rw [dif_pos hzV]
          rw [hΦz]
          have hcoord : (⟨z, hzV⟩ : ↥chart.V) = chart.homeo r := Subtype.ext hzdef
          rw [hcoord]
          show chart.homeo.symm (chart.homeo r) = r
          exact chart.homeo.symm_apply_apply r
    rw [← himg]
    exact hUpre.image Φ hΦcont
  exact not_isPreconnected_sdiff_zero_of_isOpen hAopen h0A hApre

end

end Work.CountedPinch
