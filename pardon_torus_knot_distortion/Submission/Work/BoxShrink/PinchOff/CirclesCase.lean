import Submission.Work.BoxShrink.PinchOff.Tamed
import Submission.Work.BoxShrink.PinchOff.Perp
import Submission.Work.BoxShrink.Pinch.Trace
import Submission.Work.BoxShrink.PinchOff.windingSpan_sdiff_iUnion_range_eq_of_not_isEssential

/-!
# The pinch when the slice consists of circles only

The assignment names as a partial target the case in which the trace of the cutting plane is a
finite union of **circles** (no arcs), and the reviewer of the chapter asks for exactly that: an
unconditional inhabitant of the residual in the circles-only case.  This module supplies it, modulo
the *single* topological input `TracePeel` below, which is the "peeling" of an inessential simple
closed curve out of a region (delegated in this directory as
`Submission.Work.BoxShrink.PinchOff.windingSpan_sdiff_iUnion_range_eq_of_not_isEssential`).

## The argument

Let `Ω = F ∩ PBox s c σ` be the region inside the box and `Σ = Ω ∩ {G = 0}` its trace on the
cutting plane, and let `U = Ω⁺ ∪ Ω⁻ = Ω \ Σ` be the union of the two half-regions.  In the
circles-only case the trace is a finite family `γ i` of pairwise disjoint simple closed curves of
the surface, covering `Σ`; by the hypothesis `hZ` (the slice carries no essential loop of the
surface) each `γ i` is **inessential**, i.e. bounds a disc of the surface.  The trace of a loop of
`Ω` with `γ i` can therefore be cancelled: the loop crosses `γ i` an even number of times (the
algebraic intersection number with `[γ i] = 0` vanishes), and the pieces inside the disc bounded by
`γ i` — which is contractible — may be replaced by arcs of `γ i` and then pushed off it, all inside
a neighbourhood of `γ i` contained in the open set `Ω`.  This is the content of `TracePeel`.

Consequently

  `W(Ω) = W(Ω \ ⋃ range (γ i)) = W(Ω \ Σ) = W(Ω⁺ ∪ Ω⁻)`,

the first equality being the peeling (all circles at once, which is why the family form of the
peeling lemma is the one needed: the intermediate regions obtained by peeling one circle at a time
are not open in the carrier) and the last one the additivity of the winding span over the disjoint
open pieces `Ω⁺`, `Ω⁻` together with `Ω = Ω⁺ ∪ Ω⁻ ∪ Σ`.

So in the circles-only case the **first** alternative of the parent's residual `TracePerpRealisable`
holds — the strong form `W(Ω) ≤ W(Ω⁺ ∪ Ω⁻)`, not merely the dimension bound — and hence Pardon's
Lemma 3 conclusion `BubbleHalf` at those configurations, with no further input.

## What remains outside the circles-only case

The *arcs*: an arc of the trace is not a closed curve of the surface, so it does not bound a disc
and the peeling argument does not apply; this is exactly the difficulty recorded in `README.md` §6
and in the parent chapter's §18.6 (the arcs end on the sphere trace `∂Ω` and can in principle form a
wall separating `Ω` into cells, which is what the convexity of Pardon's box has to rule out).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.BoxShrink.PinchOff

noncomputable section

variable {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}

/-! ## The structural hypothesis: the trace consists of circles only -/

/-- **The slice of the configuration consists of circles only.**  There is a finite family of
pairwise disjoint simple closed curves of the surface, each carried by the slice, covering the
slice.  (This is the "no arcs" case of `Work.Smooth.Plane.TransversePlane`, restricted to the slice
region inside the box.) -/
def SliceCirclesOnly (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) : Prop :=
  ∃ (n : ℕ) (γ : Fin n → Work.CoreTopology.ClosedCurve (surface ψ)),
    (∀ i, Work.CoreTopology.IsSimple (surface ψ) (γ i)) ∧
    (∀ i j : Fin n, i ≠ j → Disjoint (Set.range (γ i).γ) (Set.range (γ j).γ)) ∧
    (∀ (i : Fin n) (t : ℝ), γ i t ∈ Sigma ψ s c σ u) ∧
    (∀ x : R3, x ∈ Sigma ψ s c σ u → ∃ i : Fin n, x ∈ Set.range (γ i).γ)

/-! ## The peeling input -/

/-- **The peeling residual**, as a single `Prop`: removing a finite family of pairwise disjoint
inessential simple closed curves from an open region of the surface does not change its winding
span.  This is the statement delegated (and proved) in this directory as
`Submission.Work.BoxShrink.PinchOff.windingSpan_sdiff_iUnion_range_eq_of_not_isEssential`; it is
recorded here as a hypothesis so that the reduction below is independent of the delegation. -/
def TracePeel : Prop :=
  ∀ (P : Work.CoreTopology.ParamTorus) (X : Set R3) (n : ℕ)
    (γ : Fin n → Work.CoreTopology.ClosedCurve P),
    Work.SurgeryInvariance.IsOpenInCarrier P X →
    (∀ i, Work.CoreTopology.IsSimple P (γ i)) →
    (∀ i, ¬ Work.CoreTopology.IsEssential P (γ i)) →
    (∀ i j : Fin n, i ≠ j → Disjoint (Set.range (γ i).γ) (Set.range (γ j).γ)) →
    (∀ (i : Fin n) (t : ℝ), γ i t ∈ X) →
    Work.SurgeryInvariance.WindingSpan P X =
      Work.SurgeryInvariance.WindingSpan P (X \ ⋃ i, Set.range (γ i).γ)

/-! ## The slice is contained in the region, and the region is open -/

/-- The region inside the box is open in the carrier. -/
theorem isOpenInCarrier_omega :
    Work.SurgeryInvariance.IsOpenInCarrier (surface ψ) (Omega ψ s c σ) :=
  Work.SurgeryInvariance.isOpenInCarrier_carrier_inter
    (P := surface ψ) (Work.Topology.SphereSlicing.isOpen_PBox s c σ)

/-- The slice is contained in the region inside the box. -/
theorem Sigma_subset_Omega : Sigma ψ s c σ u ⊆ Omega ψ s c σ := by
  intro x hx
  obtain ⟨hc, hb, -⟩ := Work.BoxShrink.Core.mem_sliceRegion.mp hx
  exact Work.BoxShrink.Core.mem_boxRegion.mpr ⟨hc, hb⟩

/-- **The two half-regions together are the region inside the box with the slice removed.** -/
theorem omega_sdiff_sigma_eq_halves :
    Omega ψ s c σ \ Sigma ψ s c σ u = Halves ψ s c σ u := by
  ext x
  constructor
  · rintro ⟨hx, hxs⟩
    obtain ⟨hc, hb⟩ := Work.BoxShrink.Core.mem_boxRegion.mp hx
    rcases lt_trichotomy (x (σ 2)) (c (σ 2) + u) with h | h | h
    · exact Or.inr (Work.BoxShrink.Core.mem_lowerRegion.mpr ⟨hc, hb, h⟩)
    · exact absurd (Work.BoxShrink.Core.mem_sliceRegion.mpr ⟨hc, hb, h⟩) hxs
    · exact Or.inl (Work.BoxShrink.Core.mem_upperRegion.mpr ⟨hc, hb, h⟩)
  · rintro (hx | hx)
    · obtain ⟨hc, hb, hgt⟩ := Work.BoxShrink.Core.mem_upperRegion.mp hx
      refine ⟨Work.BoxShrink.Core.mem_boxRegion.mpr ⟨hc, hb⟩, fun hxs => ?_⟩
      exact absurd (Work.BoxShrink.Core.mem_sliceRegion.mp hxs).2.2 hgt.ne'
    · obtain ⟨hc, hb, hlt⟩ := Work.BoxShrink.Core.mem_lowerRegion.mp hx
      refine ⟨Work.BoxShrink.Core.mem_boxRegion.mpr ⟨hc, hb⟩, fun hxs => ?_⟩
      exact absurd (Work.BoxShrink.Core.mem_sliceRegion.mp hxs).2.2 hlt.ne

/-! ## The winding span of the region is the winding span of the halves -/

/-- **The circles-only case: the region inside the box and the two half-regions together realise
the same winding vectors.**  Each trace circle bounds a disc of the surface (hypothesis `hZ`), so
all of them can be peeled away at once by `TracePeel`. -/
theorem windingSpan_omega_eq_halves_of_trace_circles (hpeel : TracePeel)
    (hZ : ¬ (surface ψ).ContainsEssentialLoop (Sigma ψ s c σ u))
    (h : SliceCirclesOnly ψ s c σ u) :
    Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ) =
      Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u) := by
  obtain ⟨n, γ, hsimple, hdisj, hmem, hcover⟩ := h
  have hsub : ∀ (i : Fin n) (t : ℝ), γ i t ∈ Omega ψ s c σ :=
    fun i t => Sigma_subset_Omega (hmem i t)
  have hiness : ∀ i, ¬ Work.CoreTopology.IsEssential (surface ψ) (γ i) := by
    intro i hess
    exact hZ ⟨γ i, hess, fun t => hmem i t⟩
  have h1 := hpeel (surface ψ) (Omega ψ s c σ) n γ isOpenInCarrier_omega hsimple hiness hdisj hsub
  have h2 : Omega ψ s c σ \ (⋃ i, Set.range (γ i).γ) = Halves ψ s c σ u := by
    rw [← omega_sdiff_sigma_eq_halves]
    apply Set.Subset.antisymm
    · rintro x ⟨hx, hxu⟩
      refine ⟨hx, fun hxs => hxu ?_⟩
      exact Set.mem_iUnion.mpr (hcover x hxs)
    · rintro x ⟨hx, hxs⟩
      refine ⟨hx, fun hxu => ?_⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxu
      obtain ⟨t, ht⟩ := hi
      exact hxs (ht ▸ hmem i t)
  rw [h2] at h1
  exact h1

/-- **Pardon's Lemma 3 conclusion in the circles-only case.** -/
theorem bubbleHalf_of_trace_circles (hpeel : TracePeel)
    (hZ : ¬ (surface ψ).ContainsEssentialLoop (Sigma ψ s c σ u))
    (h : SliceCirclesOnly ψ s c σ u) :
    Work.BoxShrink.Bubble.BubbleHalf (surface ψ) s c σ u := by
  intro hbox
  have hW : Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u) ≠ ⊥ := by
    rw [← windingSpan_omega_eq_halves_of_trace_circles hpeel hZ h]
    exact (Work.SurgeryInvariance.windingSpan_ne_bot_iff _ _).mpr hbox
  have hsplit := Work.SurgeryInvariance.Span.union_eq_sup
    (P := surface ψ) (X := HalfUp ψ s c σ u) (Y := HalfDown ψ s c σ u)
    (Work.BoxShrink.Core.isOpenInCarrier_upperRegion (surface ψ) s c σ u)
    (Work.BoxShrink.Core.isOpenInCarrier_lowerRegion (surface ψ) s c σ u)
    (Work.BoxShrink.Core.disjoint_upperRegion_lowerRegion (surface ψ) s c σ u)
  rw [hsplit] at hW
  rcases not_and_or.mp (fun hh : Work.SurgeryInvariance.WindingSpan (surface ψ)
        (HalfUp ψ s c σ u) = ⊥ ∧
      Work.SurgeryInvariance.WindingSpan (surface ψ) (HalfDown ψ s c σ u) = ⊥ =>
      hW (by rw [hh.1, hh.2, sup_bot_eq])) with hup | hlo
  · exact Or.inl ((Work.SurgeryInvariance.windingSpan_ne_bot_iff _ _).mp hup)
  · exact Or.inr ((Work.SurgeryInvariance.windingSpan_ne_bot_iff _ _).mp hlo)

/-- **The parent's factored residual `TracePerpRealisable`, first (strong) alternative, in the
circles-only case.** -/
theorem tracePerpRealisable_of_trace_circles (hpeel : TracePeel)
    (hZ : ¬ (surface ψ).ContainsEssentialLoop (Sigma ψ s c σ u))
    (h : SliceCirclesOnly ψ s c σ u) :
    Work.BoxShrink.Pinch.TracePerpRealisable (surface ψ) s c σ u :=
  Or.inl (le_of_eq (windingSpan_omega_eq_halves_of_trace_circles hpeel hZ h))

/-- **The dimension bound `KeyTame` in the circles-only case** (trivial from the equality). -/
theorem keyTame_of_trace_circles (hpeel : TracePeel)
    (hZ : ¬ (surface ψ).ContainsEssentialLoop (Sigma ψ s c σ u))
    (h : SliceCirclesOnly ψ s c σ u) :
    Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ)) ≤
      Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u)) + 1 :=
  le_trans (le_of_eq (congrArg (fun V : Submodule ℚ (ℚ × ℚ) => Module.finrank ℚ ↥V)
    (windingSpan_omega_eq_halves_of_trace_circles hpeel hZ h))) (Nat.le_succ _)

/-! ## The circles-only case, globally -/

/-- **The box-local crossing residual in the circles-only case.**  If the trace of the cutting plane
is a union of circles only at every configuration, then `TracePerpSlice` holds (with the single
topological input `TracePeel`): at such a configuration the *first* alternative of
`TracePerpRealisable` holds (the region inside the box and the two half-regions realise the same
winding vectors), and this is the first alternative with no hypothesis on the trace's line. -/
theorem tracePerpSlice_of_sliceCircles (hpeel : TracePeel)
    (h : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      SliceCirclesOnly ψ s c σ u) :
    TracePerpSlice :=
  fun ψ s c σ u _ _ hZ => tracePerpRealisable_of_trace_circles hpeel hZ (h ψ s c σ u)

/-- **End to end in the circles-only case**: Pardon's Lemma 3 with the general position of the
cutting plane (`SmoothHalfSTame`), given the general position of the box-sphere trace
(`BoxSliceNice`) and the structural hypothesis that the slice is made of circles only. -/
theorem smoothHalfSTame_of_sliceCircles (hnice : Work.BoxShrink.Pinch.BoxSliceNice)
    (hpeel : TracePeel)
    (h : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      SliceCirclesOnly ψ s c σ u) :
    SmoothHalfSTame :=
  smoothHalfSTame_of_tracePerpSlice hnice (tracePerpSlice_of_sliceCircles hpeel h)

/-- The same, in the parent chapter's own name (`Work.BoxShrink.Pinch.PushOffHalfTame`). -/
theorem pushOffHalfTame_of_sliceCircles (hnice : Work.BoxShrink.Pinch.BoxSliceNice)
    (hpeel : TracePeel)
    (h : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      SliceCirclesOnly ψ s c σ u) :
    Work.BoxShrink.Pinch.PushOffHalfTame :=
  smoothHalfSTame_of_sliceCircles hnice hpeel h

/-! ## The closed components of *any* slicing datum are peelable -/

/-- **The closed components of any slicing datum of the cut disc are peelable.**  From the tameness
of the slice (`TameSlice`, i.e. a `Work.Smooth.Plane.TransversePlane` datum for the flat disc of the
box) and the hypothesis `hZ`, the *closed* components of the datum are pairwise disjoint simple
closed curves of the surface, carried by the slice, hence inessential; removing their union from the
region inside the box does not change its winding span (`TracePeel`).

Consequently the residual's remaining content is exactly the **arcs** of the datum: the circles of
the slice can always be peeled away, and what is left is the case in which the slice carries arcs,
i.e. the open content recorded in `README.md` §18.2. -/
theorem exists_closedComponents_peeling (hTame : Work.BoxShrink.Pinch.TameSlice ψ s c σ u)
    (hZ : ¬ (surface ψ).ContainsEssentialLoop (Sigma ψ s c σ u)) :
    ∃ (ι : Type) (_ : Fintype ι) (c' : ι → Work.CoreTopology.ClosedCurve (surface ψ)),
      (∀ i, Work.CoreTopology.IsSimple (surface ψ) (c' i)) ∧
      (∀ i j : ι, i ≠ j → Disjoint (Set.range (c' i).γ) (Set.range (c' j).γ)) ∧
      (∀ (i : ι) (t : ℝ), c' i t ∈ Sigma ψ s c σ u) ∧
      Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ) =
        Work.SurgeryInvariance.WindingSpan (surface ψ)
          (Omega ψ s c σ \ ⋃ i, Set.range (c' i).γ) := by
  obtain ⟨ι, hι, c', κ, hκ, a, hsimple, hdisj, hmem, ha_inj, ha_mem, ha_surf, ha_disj, hac_disj,
    hcover⟩ := hTame
  have hmem' : ∀ (i : ι) (t : ℝ), c' i t ∈ Sigma ψ s c σ u :=
    fun i t => Work.BoxShrink.Core.mem_sliceRegion.mpr ⟨(c' i).mem t, hmem i t⟩
  have hdisj' : ∀ i j : ι, i ≠ j → Disjoint (Set.range (c' i).γ) (Set.range (c' j).γ) := hdisj
  have hiness : ∀ i : ι, ¬ Work.CoreTopology.IsEssential (surface ψ) (c' i) :=
    fun i hess => hZ ⟨c' i, hess, fun t => hmem' i t⟩
  have hsub : ∀ (i : ι) (t : ℝ), c' i t ∈ Omega ψ s c σ :=
    fun i t => Sigma_subset_Omega (hmem' i t)
  classical
  have hpeel := windingSpan_sdiff_iUnion_range_eq_of_not_isEssential
    (P := surface ψ) (X := Omega ψ s c σ)
    (γ := fun i : Fin (Fintype.card ι) => c' ((Fintype.equivFin ι).symm i))
    isOpenInCarrier_omega
    (fun i => hsimple ((Fintype.equivFin ι).symm i))
    (fun i => hiness ((Fintype.equivFin ι).symm i))
    (fun i j hij => hdisj' ((Fintype.equivFin ι).symm i) ((Fintype.equivFin ι).symm j)
      (fun h => hij ((Fintype.equivFin ι).symm.injective h)))
    (fun i t => hsub ((Fintype.equivFin ι).symm i) t)
  have hset : (⋃ i : Fin (Fintype.card ι), Set.range (c' ((Fintype.equivFin ι).symm i)).γ) =
      ⋃ i : ι, Set.range (c' i).γ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_range]
    constructor
    · rintro ⟨i, t, ht⟩
      exact ⟨(Fintype.equivFin ι).symm i, t, ht⟩
    · rintro ⟨i, t, ht⟩
      exact ⟨Fintype.equivFin ι i, t, by simpa using ht⟩
  exact ⟨ι, hι, c', hsimple, hdisj', hmem', by rw [hpeel, hset]⟩

set_option linter.unusedVariables false in
/-! ## The peeling input is a theorem -/

set_option linter.unusedVariables false in
/-- **The peeling input of this file holds**, by the delegated and proved
`Work.BoxShrink.PinchOff.windingSpan_sdiff_iUnion_range_eq_of_not_isEssential`. -/
theorem tracePeel_holds : TracePeel :=
  fun P X n γ hX hsimple hiness hdisj hsub =>
    windingSpan_sdiff_iUnion_range_eq_of_not_isEssential hX hsimple hiness hdisj hsub

/-- **The circles-only case of Pardon's Lemma 3, unconditionally**: no hypothesis beyond the
structural one (the trace is made of circles) and `hZ`. -/
theorem bubbleHalf_of_trace_circles_holds
    (hZ : ¬ (surface ψ).ContainsEssentialLoop (Sigma ψ s c σ u))
    (h : SliceCirclesOnly ψ s c σ u) :
    Work.BoxShrink.Bubble.BubbleHalf (surface ψ) s c σ u :=
  bubbleHalf_of_trace_circles tracePeel_holds hZ h

/-- **The strong form of the residual in the circles-only case, unconditionally**: the region inside
the box and the two half-regions realise the same winding vectors. -/
theorem windingSpan_omega_eq_halves_of_trace_circles_holds
    (hZ : ¬ (surface ψ).ContainsEssentialLoop (Sigma ψ s c σ u))
    (h : SliceCirclesOnly ψ s c σ u) :
    Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ) =
      Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u) :=
  windingSpan_omega_eq_halves_of_trace_circles tracePeel_holds hZ h

/-- The parent's factored residual at a circles-only configuration, first alternative. -/
theorem tracePerpRealisable_of_trace_circles_holds
    (hZ : ¬ (surface ψ).ContainsEssentialLoop (Sigma ψ s c σ u))
    (h : SliceCirclesOnly ψ s c σ u) :
    Work.BoxShrink.Pinch.TracePerpRealisable (surface ψ) s c σ u :=
  tracePerpRealisable_of_trace_circles tracePeel_holds hZ h

/-- The tamed dimension bound at a circles-only configuration. -/
theorem keyTame_of_trace_circles_holds
    (hZ : ¬ (surface ψ).ContainsEssentialLoop (Sigma ψ s c σ u))
    (h : SliceCirclesOnly ψ s c σ u) :
    Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ)) ≤
      Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u)) + 1 :=
  keyTame_of_trace_circles tracePeel_holds hZ h

/-- **The box-local crossing residual, in the circles-only case, unconditionally.** -/
theorem tracePerpSlice_of_sliceCircles_holds
    (h : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      SliceCirclesOnly ψ s c σ u) :
    TracePerpSlice :=
  tracePerpSlice_of_sliceCircles tracePeel_holds h

/-- **Pardon's Lemma 3 with the general position of the cutting plane, in the circles-only case,
unconditionally** (given the general position of the box-sphere trace `BoxSliceNice`). -/
theorem smoothHalfSTame_of_sliceCircles_holds (hnice : Work.BoxShrink.Pinch.BoxSliceNice)
    (h : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      SliceCirclesOnly ψ s c σ u) :
    SmoothHalfSTame :=
  smoothHalfSTame_of_sliceCircles hnice tracePeel_holds h

end

end Work.BoxShrink.PinchOff
