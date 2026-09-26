import Mathlib
import Submission.Work.PinchLemma3.Targets
import Submission.Work.BoxShrink.Pinch.Plane
import Submission.Work.SurgeryInvariance.Span.union_eq_sup
import Submission.Work.PinchLemma3.ClosedDiscA.windingSpan_boxRegion_le_sdiff_interior_union_boundary
import Submission.Work.PinchLemma3.ClosedDiscA.windingSpan_union_le_sup_of_isPathConnected_inter
import Submission.Work.BoxShrink.PinchOff.peel_range_eq_of_nhds
import Submission.Work.PinchLemma3.ClosedDiscA.exists_closedCurve_boundary_of_discRegion
import Submission.Work.PinchLemma3.ClosedDiscA.windingSpan_union_le_sup_of_grounded_inter
import Submission.Work.PinchLemma3.ClosedDiscA.winding_dependent_of_disjoint_curves
import Submission.Work.PinchLemma3.ClosedDiscA.exists_ne_zero_inf_span_le_of_intersection_pair_general
import Submission.Work.PinchLemma3.ClosedDiscA.exists_ne_zero_inf_span_le_of_intersection_three_pieces
import Submission.Work.PinchLemma3.ClosedDiscA.finrank_upperRegion_union_discInterior_le_one_of_three_pieces_split
import Submission.Work.PinchLemma3.ClosedDiscA.finrank_lowerRegion_union_discInterior_le_one_of_three_pieces_split

set_option maxHeartbeats 2000000

namespace Work.PinchLemma3.ClosedDiscA

/-!
# The one-class form of the wall budget in the inessential-trace case

`Work.PinchLemma3.ClosedDiscA.wall_core` is the *one-class* form of the wall budget in the case in
which the trace `Γ = F ∩ Π` of the cutting plane carries no essential loop (`hT`) and the two
half-regions carry none either (`h0`):

  `∃ v ≠ 0, W(Ω) ⊓ ℚ∙v ≤ W(Ω⁺ ∪ Ω⁻)`.

With `h0` the right-hand side is `⊥`, so the statement says exactly that the winding span of the
region inside the box *misses* a nonzero class, i.e. that `W(Ω) ≠ ⊤`: the box region's winding
span is not the whole of `H₁(T²;ℚ) = ℚ²`.

## The reduction

Everything is the linear algebra of the two-dimensional symplectic module `ℚ²`:

* the non-fullness of the box region's span,
  `Work.PinchLemma3.boxRegion_ne_top_of_halves_bot` (the trace-inessential, halves-inessential
  case of Pardon's "the invariant cannot jump from `2g` to `0`"); it is here that the geometry of
  the pinch enters;
* `W(Ω) ≠ ⊤` gives a vector `v ∉ W(Ω)` (`Submodule.eq_top_iff'`), which is nonzero because
  `0 ∈ W(Ω)`;
* `Disjoint W(Ω) (ℚ∙v)` then follows from `Submodule.disjoint_span_singleton` (a multiple of the
  outside vector `v` lies in `W(Ω)` only if it vanishes), and `disjoint_iff` turns the disjointness
  into `W(Ω) ⊓ ℚ∙v = ⊥ ≤ W(Ω⁺ ∪ Ω⁻)`.

The converse reduction is also proved (`ne_top_of_exists_inf_span_le`): the conclusion of
`wall_core` forces `W(Ω) ≠ ⊤`, so the statement *is* the residual.

## The weak form is the *honest* form (a proved negative result)

The sibling module `Submission.Work.PinchLemma3.ClosedDiscA.strong_span_form_refuted` proves, for the
standard torus with `σ = swap 0 1 * swap 1 2`, `s = 9/10`, `c = (2,0,0)`, `u = -9/10`, that

* `W (planeTrace …) = ⊥` and `W (halfRegions …) = ⊥`,  but
* `W (boxRegion …) ≠ ⊥`.

So the *strong* span form `W(Ω) ≤ W(Ω⁺ ∪ Ω⁻)` — the statement `TraceClassBoundSpanBot` of
`Work.BoxShrink.Pinch/README.md` §16.5 — is **FALSE** in exactly the regime of this module's
hypotheses, and the statement of `wall_core` (a nonzero class `v` whose multiples the box region
carries only where the halves already do) is the honest, non-vacuous target.  Any future attempt to
prove `wall_core` must therefore *not* route through the span form; and the hypotheses `hT`, `h0`
are consistent.

## Elementary consequences recorded here

* the winding span of an embedded disc of the torus is `⊥`, and so is that of any subset of it — in
  particular **`hslice` gives `W(Σ) = ⊥`**, the *slice inessentiality* endpoint hypothesis of the
  pinch, with no general-position input (`windingSpan_sliceRegion_eq_bot`);
* the two half-regions lie in the box region, so `W(Ω⁺ ∪ Ω⁻) ≤ W(Ω)`
  (`windingSpan_halfRegions_le_boxRegion`);
* the set algebra of the splitting `Ω = Ω⁺ ⊔ Σ ⊔ Ω⁻` and of the box sphere
  (`sliceRegion_disjoint_halfRegions`, `boxRegion_sdiff_sliceRegion`,
  `closedBoxRegion_eq_boxRegion_union_sphereTrace`, `boundary_subset_halves_union_sphereTrace`).
-/

open LeanEval.KnotTheory.PardonDistortion

/-- **The one-class form of the wall budget, from the non-fullness of the box region's span.**
If the winding span of the region inside the box is not the whole of `ℚ²`, then there is a nonzero
class `v` such that every multiple of `v` carried by the box region is carried by the two
half-regions: take `v` outside `W(Ω)`, so that `W(Ω) ⊓ ℚ∙v = ⊥ ≤ W(Ω⁺ ∪ Ω⁻)`. -/
theorem wall_core_of_ne_top {P : Work.CoreTopology.ParamTorus} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ≠ ⊤) :
    ∃ v : ℚ × ℚ, v ≠ 0 ∧
      Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ⊓
        Submodule.span ℚ ({v} : Set (ℚ × ℚ)) ≤
      Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) := by
  have hex : ∃ v : ℚ × ℚ,
      v ∉ Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) := by
    by_contra hcon
    push Not at hcon
    exact h (Submodule.eq_top_iff'.mpr hcon)
  obtain ⟨v, hv⟩ := hex
  refine ⟨v, ?_, ?_⟩
  · intro hv0
    exact hv (hv0 ▸ Submodule.zero_mem _)
  · have hdisj : Disjoint
        (Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ))
        (Submodule.span ℚ ({v} : Set (ℚ × ℚ))) :=
      Submodule.disjoint_span_singleton.mpr (fun hmem => absurd hmem hv)
    rw [disjoint_iff.mp hdisj]
    exact bot_le

/-- **The one-class form of the wall budget, from the dimension form.**  If `dim W(Ω) ≤ 1`, then
`W(Ω) ≠ ℚ²` and `wall_core_of_ne_top` applies.  The dimension `2` of `ℚ²` is
`Module.finrank_prod` followed by `Module.finrank_self`. -/
theorem wall_core_of_finrank_le_one {P : Work.CoreTopology.ParamTorus} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P
        (Work.BoxShrink.Core.boxRegion P s c σ)) ≤ 1) :
    ∃ v : ℚ × ℚ, v ≠ 0 ∧
      Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ⊓
        Submodule.span ℚ ({v} : Set (ℚ × ℚ)) ≤
      Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) := by
  refine wall_core_of_ne_top (P := P) (s := s) (c := c) (σ := σ) (u := u) ?_
  intro htop
  have h2 : Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.boxRegion P s c σ)) = 2 := by
    rw [htop, finrank_top, Module.finrank_prod, Module.finrank_self]
  omega

/-! ## The winding span of a disc, and of the slice -/

/-- **The winding span of an embedded disc of the torus is `⊥`.**  A closed curve lying in an
embedded disc is null-homotopic (`Work.SurgeryInvariance.DiscRegion.not_isEssential`), so the disc
realises no winding vector. -/
theorem windingSpan_carrier_eq_bot_of_discRegion {P : Work.CoreTopology.ParamTorus}
    (D : Work.SurgeryInvariance.DiscRegion P) :
    Work.SurgeryInvariance.WindingSpan P D.carrier = ⊥ := by
  rw [Work.SurgeryInvariance.WindingSpan_eq_bot_iff]
  rintro ⟨γ, hess, hγ⟩
  exact (Work.SurgeryInvariance.DiscRegion.not_isEssential D γ hγ) hess

/-- **A region contained in an embedded disc of the torus is inessential.** -/
theorem windingSpan_eq_bot_of_subset_discRegion {P : Work.CoreTopology.ParamTorus}
    {Z : Set R3} (D : Work.SurgeryInvariance.DiscRegion P) (h : Z ⊆ D.carrier) :
    Work.SurgeryInvariance.WindingSpan P Z = ⊥ := by
  rw [Work.SurgeryInvariance.WindingSpan_eq_bot_iff] at *
  rintro ⟨γ, hess, hγ⟩
  exact ((Work.SurgeryInvariance.WindingSpan_eq_bot_iff P D.carrier).mp
    (windingSpan_carrier_eq_bot_of_discRegion D)) ⟨γ, hess, fun t => h (hγ t)⟩

/-- **The slice is inessential when it lies in the interior of a disc.**  This is the *slice
inessentiality* endpoint hypothesis of Pardon's pinch, obtained here from the disc hypothesis
`hslice` alone (no general position, no classification of surfaces). -/
theorem windingSpan_sliceRegion_eq_bot {P : Work.CoreTopology.ParamTorus} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} {D : Work.SurgeryInvariance.DiscRegion P}
    (hslice : Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ D.interior) :
    Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.sliceRegion P s c σ u) = ⊥ :=
  windingSpan_eq_bot_of_subset_discRegion D (hslice.trans (D.interior_subset_carrier))

/-- **The two half-regions are contained in the region inside the box**, hence their winding span
is contained in the box region's: `W(Ω⁺ ∪ Ω⁻) ≤ W(Ω)`. -/
theorem windingSpan_halfRegions_le_boxRegion {P : Work.CoreTopology.ParamTorus} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} :
    Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) ≤
      Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) :=
  Work.SurgeryInvariance.WindingSpan_mono P
    (Work.PinchLemma3.halfRegions_subset_boxRegion P s c σ u)

/-! ## The set algebra of the splitting -/

/-- **The slice is disjoint from the two open half-regions.**  The slice lies on the cutting plane,
the half-regions off it. -/
theorem sliceRegion_disjoint_halfRegions (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Disjoint (halfRegions P s c σ u) (Work.BoxShrink.Core.sliceRegion P s c σ u) := by
  rw [Set.disjoint_left]
  intro y hy hz
  have hzy : y.ofLp (σ 2) = c.ofLp (σ 2) + u :=
    ((Work.BoxShrink.Core.mem_sliceRegion (P := P)).mp hz).2.2
  rcases hy with hu | hl
  · exact absurd hzy (ne_of_gt ((Work.BoxShrink.Core.mem_upperRegion (P := P)).mp hu).2.2)
  · exact absurd hzy (ne_of_lt ((Work.BoxShrink.Core.mem_lowerRegion (P := P)).mp hl).2.2)

/-- **The region inside the box minus the slice is the union of the two half-regions.** -/
theorem boxRegion_sdiff_sliceRegion (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Work.BoxShrink.Core.boxRegion P s c σ \ Work.BoxShrink.Core.sliceRegion P s c σ u =
      halfRegions P s c σ u := by
  have hd := sliceRegion_disjoint_halfRegions P s c σ u
  have hup : Work.BoxShrink.Core.upperRegion P s c σ u \
      Work.BoxShrink.Core.sliceRegion P s c σ u = Work.BoxShrink.Core.upperRegion P s c σ u := by
    refine Set.Subset.antisymm Set.sdiff_subset ?_
    intro y hy
    exact ⟨hy, fun h => (Set.disjoint_left.mp hd) (Or.inl hy) h⟩
  have hlo : Work.BoxShrink.Core.lowerRegion P s c σ u \
      Work.BoxShrink.Core.sliceRegion P s c σ u = Work.BoxShrink.Core.lowerRegion P s c σ u := by
    refine Set.Subset.antisymm Set.sdiff_subset ?_
    intro y hy
    exact ⟨hy, fun h => (Set.disjoint_left.mp hd) (Or.inr hy) h⟩
  rw [Work.BoxShrink.Core.boxRegion_eq_union P s c σ u, Set.union_sdiff_right,
    Set.union_sdiff_distrib, hup, hlo]
  rfl

/-- **The closed box region is the box region together with the trace of the box sphere.** -/
theorem closedBoxRegion_eq_boxRegion_union_sphereTrace (P : Work.CoreTopology.ParamTorus) (s : ℝ)
    (c : R3) (σ : Equiv.Perm (Fin 3)) :
    Work.PinchLemma3.closedBoxRegion P s c σ =
      Work.BoxShrink.Core.boxRegion P s c σ ∪
        (P.carrier ∩ {y : R3 | Submission.boxNorm c σ y = s}) := by
  ext y
  rw [Work.PinchLemma3.mem_closedBoxRegion, Set.mem_union, Work.BoxShrink.Core.mem_boxRegion,
    Submission.mem_PBox_iff, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hyc, hy⟩
    rcases lt_or_eq_of_le hy with h | h
    · exact Or.inl ⟨hyc, h⟩
    · exact Or.inr ⟨hyc, h⟩
  · rintro (⟨hyc, h⟩ | ⟨hyc, h⟩)
    · exact ⟨hyc, le_of_lt h⟩
    · exact ⟨hyc, le_of_eq h⟩

/-- **The trace of the box sphere is disjoint from the region inside the box.** -/
theorem disjoint_sphereTrace_boxRegion (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) :
    Disjoint (P.carrier ∩ {y : R3 | Submission.boxNorm c σ y = s})
      (Work.BoxShrink.Core.boxRegion P s c σ) := by
  rw [Set.disjoint_left]
  rintro y ⟨-, hy⟩ ⟨-, hyb⟩
  exact absurd ((Submission.mem_PBox_iff s c σ y).mp hyb) (by rw [hy]; exact lt_irrefl s)

/-- **The boundary circle of the disc misses the interior of the disc.** -/
theorem boundary_disjoint_interior {P : Work.CoreTopology.ParamTorus}
    (D : Work.SurgeryInvariance.DiscRegion P) : Disjoint D.boundary D.interior := by
  rw [Set.disjoint_left]
  intro y hyb hyi
  obtain ⟨z, hz, hze⟩ := hyb
  obtain ⟨z', hz', hze'⟩ := hyi
  have hzz : z = z' := D.inj (by rw [hze, hze'])
  have hval : (z : ℂ) = (z' : ℂ) := congrArg Subtype.val hzz
  have h1 : ‖(z : ℂ)‖ = 1 := hz
  have h2 : ‖(z : ℂ)‖ < 1 := by rw [hval]; exact hz'
  linarith

/-- **The boundary circle of the disc lies in the two half-regions together with the trace of the
box sphere.**  The disc lies in the closed box region (`hD`) and the slice lies in its interior
(`hslice`), so the boundary circle misses the slice; and the closed box region is the box region
together with the box-sphere trace. -/
theorem boundary_subset_halves_union_sphereTrace {P : Work.CoreTopology.ParamTorus} {s : ℝ}
    {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} {D : Work.SurgeryInvariance.DiscRegion P}
    (hD : D.carrier ⊆ Work.PinchLemma3.closedBoxRegion P s c σ)
    (hslice : Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ D.interior) :
    D.boundary ⊆ halfRegions P s c σ u ∪
      (P.carrier ∩ {y : R3 | Submission.boxNorm c σ y = s}) := by
  intro y hy
  have hycarrier : y ∈ D.carrier :=
    Work.SurgeryInvariance.DiscRegion.boundary_subset_carrier D hy
  have hynotslice : y ∉ Work.BoxShrink.Core.sliceRegion P s c σ u := fun h =>
    (Set.disjoint_left.mp (boundary_disjoint_interior D) hy) (hslice h)
  have hmem : y ∈ (Work.BoxShrink.Core.boxRegion P s c σ ∪
      (P.carrier ∩ {y : R3 | Submission.boxNorm c σ y = s})) \
        Work.BoxShrink.Core.sliceRegion P s c σ u :=
    ⟨((closedBoxRegion_eq_boxRegion_union_sphereTrace (P := P) (s := s) (c := c)
        (σ := σ)).symm ▸ hD hycarrier), hynotslice⟩
  rcases hmem with ⟨hab, hns⟩
  rcases hab with hb | hsp
  · refine Or.inl ?_
    exact (boxRegion_sdiff_sliceRegion (P := P) (s := s) (c := c) (σ := σ) (u := u)).symm ▸
      ⟨hb, hns⟩
  · exact Or.inr hsp

/-- **The conclusion of `wall_core` forces the non-fullness of the box region's span.**  Together
with `wall_core_of_ne_top` this shows that — at any configuration with `W(Ω⁺ ∪ Ω⁻) = ⊥` — the
statement of `wall_core` is *equivalent* to `W(Ω) ≠ ⊤`, i.e. to the project's residual.  Indeed if
`W(Ω) = ⊤` then `W(Ω) ⊓ ℚ∙v = ℚ∙v` for every nonzero `v`, which cannot be contained in
`W(Ω⁺ ∪ Ω⁻) = ⊥`. -/
theorem ne_top_of_exists_inf_span_le {P : Work.CoreTopology.ParamTorus} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} {D : Work.SurgeryInvariance.DiscRegion P}
    (_hD : D.carrier ⊆ Work.PinchLemma3.closedBoxRegion P s c σ)
    (_hslice : Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ D.interior)
    (hT : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Pinch.planeTrace P c σ u) = ⊥)
    (h0 : Work.SurgeryInvariance.WindingSpan P (halfRegions P s c σ u) = ⊥)
    (h : ∃ v : ℚ × ℚ, v ≠ 0 ∧
      Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ⊓
        Submodule.span ℚ ({v} : Set (ℚ × ℚ)) ≤
      Work.SurgeryInvariance.WindingSpan P (halfRegions P s c σ u)) :
    Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ≠ ⊤ := by
  intro htop
  obtain ⟨v, hv0, hv⟩ := h
  have hmem : v ∈ Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.boxRegion P s c σ) ⊓ Submodule.span ℚ ({v} : Set (ℚ × ℚ)) :=
    ⟨by rw [htop]; exact Submodule.mem_top,
      Submodule.subset_span (by simp)⟩
  have hbot : v ∈ (⊥ : Submodule ℚ (ℚ × ℚ)) := by
    rw [← h0]
    exact hv hmem
  rw [Submodule.mem_bot] at hbot
  exact hv0 hbot

/-! ## The line-confinement criterion: one coordinate is enough

The window criterion (`Work.BoxShrink.Pinch.not_containsEssentialLoop_of_component_windows`) shows
that a region whose parameter-plane preimage is covered by *windows* — rectangles of side `< 2π` in
**both** coordinates — carries no essential loop.  The two results below are the same computation
run in **one** coordinate, and they are what the residual of the pinch needs: if every connected
subset of the preimage of `X` is confined in one coordinate, then `X` realises no winding in that
coordinate, so `W(X)` is contained in a *line* — which is exactly the conclusion of `wall_core`
(a subspace of `ℚ²` contained in a line is not `⊤`).

The difference matters.  The parameter plane of the *standard* torus at the box used in
`strong_span_form_refuted` is a genuine example (`NOTES_wall_core.md` §8.1): the box confines the
longitude parameter to a band of width `< 2π` while leaving the meridian parameter free, so every
component of the preimage is a strip — unbounded, hence not a window — and the box region realises
exactly the *line* `ℚ·(0,1)`.  The criterion below is the sharp statement that this configuration
satisfies and `not_containsEssentialLoop_of_component_windows` does not. -/

/-- A **vertical strip** of the parameter plane: a set confined to a band of width `< 2π` in the
first (`Θ`) coordinate; it is unbounded in the second (`Φ`). -/
def IsStrip (S : Set (ℝ × ℝ)) : Prop :=
  ∃ a b : ℝ, b - a < 2 * Real.pi ∧ S ⊆ Set.Ioo a b ×ˢ (Set.univ : Set ℝ)

/-- A **horizontal strip** of the parameter plane: confined in the second (`Φ`) coordinate. -/
def IsStrip' (S : Set (ℝ × ℝ)) : Prop :=
  ∃ a b : ℝ, b - a < 2 * Real.pi ∧ S ⊆ (Set.univ : Set ℝ) ×ˢ Set.Ioo a b

theorem isStrip_Ioo {a b : ℝ} (h : b - a < 2 * Real.pi) :
    IsStrip (Set.Ioo a b ×ˢ (Set.univ : Set ℝ)) := ⟨a, b, h, fun _ hx => hx⟩

theorem isStrip'_Ioo {a b : ℝ} (h : b - a < 2 * Real.pi) :
    IsStrip' ((Set.univ : Set ℝ) ×ˢ Set.Ioo a b) := ⟨a, b, h, fun _ hx => hx⟩

theorem IsStrip.subset {S S' : Set (ℝ × ℝ)} (h : IsStrip S) (hsub : S' ⊆ S) : IsStrip S' := by
  obtain ⟨a, b, hab, hS⟩ := h
  exact ⟨a, b, hab, hsub.trans hS⟩

theorem IsStrip'.subset {S S' : Set (ℝ × ℝ)} (h : IsStrip' S) (hsub : S' ⊆ S) : IsStrip' S' := by
  obtain ⟨a, b, hab, hS⟩ := h
  exact ⟨a, b, hab, hsub.trans hS⟩

theorem isWindow_of_isStrip_of_isStrip' {S : Set (ℝ × ℝ)} (h : IsStrip S) (h' : IsStrip' S) :
    Work.BoxShrink.Pinch.IsWindow S := by
  obtain ⟨a, b, hab, hS⟩ := h
  obtain ⟨c, d, hcd, hS'⟩ := h'
  exact ⟨a, b, c, d, hab, hcd, fun x hx => ⟨(hS hx).1, (hS' hx).2⟩⟩

/-- **The longitude-confinement criterion.**  If every connected subset of the preimage of `X` in
the parameter plane is contained in a vertical strip, then every loop of `X` has vanishing first
(longitude) winding, i.e. `W(X) ≤ ℚ·(0,1)`. -/
theorem windingSpan_le_span_snd_of_strip {P : Work.CoreTopology.ParamTorus} {X : Set R3}
    (h : ∀ S : Set (ℝ × ℝ), IsConnected S →
      S ⊆ Work.BoxShrink.Pinch.planePreimage P X → IsStrip S) :
    Work.SurgeryInvariance.WindingSpan P X ≤ Submodule.span ℚ ({(0, 1)} : Set (ℚ × ℚ)) := by
  rw [Work.SurgeryInvariance.WindingSpan, Submodule.span_le]
  rintro v ⟨γ, hγ, rfl⟩
  obtain ⟨L⟩ := Work.TorusCover.ParamTorus_exists_liftOf P γ
  have hcont : Continuous fun t : ℝ => (L.Θ t, L.Φ t) := L.contΘ.prodMk L.contΦ
  have hconn : IsConnected (Set.range fun t : ℝ => (L.Θ t, L.Φ t)) := isConnected_range hcont
  have hsub : Set.range (fun t : ℝ => (L.Θ t, L.Φ t)) ⊆
      Work.BoxShrink.Pinch.planePreimage P X := by
    rintro _ ⟨t, rfl⟩
    simp only [Work.BoxShrink.Pinch.mem_planePreimage]
    rw [L.lifts t]
    exact hγ t
  obtain ⟨a, b, hab, hmem⟩ := h _ hconn hsub
  have hzero : (L.winding).1 = 0 :=
    Work.BoxShrink.Pinch.winding_fst_eq_zero_of_bdd L hab (fun t => (hmem ⟨t, rfl⟩).1)
  rw [Work.SurgeryInvariance.windingOf_eq P γ L, hzero]
  exact Submodule.mem_span_singleton.mpr
    ⟨((L.winding).2 : ℚ), by ext <;> simp⟩

/-- **The meridian-confinement criterion.**  If every connected subset of the preimage of `X` in
the parameter plane is contained in a horizontal strip, then every loop of `X` has vanishing
second (meridian) winding, i.e. `W(X) ≤ ℚ·(1,0)`. -/
theorem windingSpan_le_span_fst_of_strip {P : Work.CoreTopology.ParamTorus} {X : Set R3}
    (h : ∀ S : Set (ℝ × ℝ), IsConnected S →
      S ⊆ Work.BoxShrink.Pinch.planePreimage P X → IsStrip' S) :
    Work.SurgeryInvariance.WindingSpan P X ≤ Submodule.span ℚ ({(1, 0)} : Set (ℚ × ℚ)) := by
  rw [Work.SurgeryInvariance.WindingSpan, Submodule.span_le]
  rintro v ⟨γ, hγ, rfl⟩
  obtain ⟨L⟩ := Work.TorusCover.ParamTorus_exists_liftOf P γ
  have hcont : Continuous fun t : ℝ => (L.Θ t, L.Φ t) := L.contΘ.prodMk L.contΦ
  have hconn : IsConnected (Set.range fun t : ℝ => (L.Θ t, L.Φ t)) := isConnected_range hcont
  have hsub : Set.range (fun t : ℝ => (L.Θ t, L.Φ t)) ⊆
      Work.BoxShrink.Pinch.planePreimage P X := by
    rintro _ ⟨t, rfl⟩
    simp only [Work.BoxShrink.Pinch.mem_planePreimage]
    rw [L.lifts t]
    exact hγ t
  obtain ⟨a, b, hab, hmem⟩ := h _ hconn hsub
  have hzero : (L.winding).2 = 0 :=
    Work.BoxShrink.Pinch.winding_snd_eq_zero_of_bdd L hab (fun t => (hmem ⟨t, rfl⟩).2)
  rw [Work.SurgeryInvariance.windingOf_eq P γ L, hzero]
  exact Submodule.mem_span_singleton.mpr
    ⟨((L.winding).1 : ℚ), by ext <;> simp⟩

/-! ## From a line to the conclusion of `wall_core` -/

/-- **A winding span contained in a line is not the whole of `ℚ²`.**  Hence any region whose
winding span is confined to a single class satisfies the one-class conclusion of `wall_core`. -/
theorem ne_top_of_le_span_singleton {P : Work.CoreTopology.ParamTorus} {X : Set R3}
    {v : ℚ × ℚ} (hv : v ≠ 0)
    (h : Work.SurgeryInvariance.WindingSpan P X ≤ Submodule.span ℚ ({v} : Set (ℚ × ℚ))) :
    Work.SurgeryInvariance.WindingSpan P X ≠ ⊤ := by
  intro htop
  have hle : (⊤ : Submodule ℚ (ℚ × ℚ)) ≤ Submodule.span ℚ ({v} : Set (ℚ × ℚ)) := by
    rw [← htop]; exact h
  have h2 : Module.finrank ℚ ↥(Submodule.span ℚ ({v} : Set (ℚ × ℚ))) = 2 := by
    rw [eq_top_iff.mpr hle, finrank_top, Module.finrank_prod, Module.finrank_self]
  have h1 : Module.finrank ℚ ↥(Submodule.span ℚ ({v} : Set (ℚ × ℚ))) = 1 := by
    rw [finrank_span_singleton]; simp [hv]
  omega

/-- **The one-class form of the wall budget, from a one-line bound on the box region.** -/
theorem wall_core_of_line {P : Work.CoreTopology.ParamTorus} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} {v : ℚ × ℚ} (hv : v ≠ 0)
    (h : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ≤
      Submodule.span ℚ ({v} : Set (ℚ × ℚ))) :
    ∃ v : ℚ × ℚ, v ≠ 0 ∧
      Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ⊓
        Submodule.span ℚ ({v} : Set (ℚ × ℚ)) ≤
      Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) :=
  wall_core_of_ne_top (ne_top_of_le_span_singleton hv h)

/-- **`wall_core` from the confinement of the box region's preimage in one coordinate.**  This is
the sufficient condition the residual's proof is expected to establish: the box confines one
parameter range, so the box region realises windings in one line only, so its span is not `⊤`. -/
theorem wall_core_of_strip_confinement (P : Work.CoreTopology.ParamTorus) (s : ℝ)
    (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (D : Work.SurgeryInvariance.DiscRegion P)
    (_hD : D.carrier ⊆ Work.PinchLemma3.closedBoxRegion P s c σ)
    (_hslice : Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ D.interior)
    (_hT : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Pinch.planeTrace P c σ u) = ⊥)
    (_h0 : Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) = ⊥)
    (h : ∀ S : Set (ℝ × ℝ), IsConnected S →
      S ⊆ Work.BoxShrink.Pinch.planePreimage P (Work.BoxShrink.Core.boxRegion P s c σ) →
        IsStrip S) :
    ∃ v : ℚ × ℚ, v ≠ 0 ∧
      Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ⊓
        Submodule.span ℚ ({v} : Set (ℚ × ℚ)) ≤
      Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) :=
  wall_core_of_line (v := (0, 1)) (by decide)
    (windingSpan_le_span_snd_of_strip h)

/-! ## The disc decomposition of the box region -/

/-- **The carrier of a disc region is closed in `ℝ³`** (it is the image of a compact set under a
continuous map, and `ℝ³` is Hausdorff). -/
theorem isClosed_carrier_of_discRegion {P : Work.CoreTopology.ParamTorus}
    (D : Work.SurgeryInvariance.DiscRegion P) : IsClosed D.carrier :=
  (isCompact_range D.e.continuous).isClosed

/-- **The interior and the boundary of a disc region are disjoint.** -/
theorem discRegion_disjoint_interior_boundary {P : Work.CoreTopology.ParamTorus}
    (D : Work.SurgeryInvariance.DiscRegion P) : Disjoint D.interior D.boundary := by
  rw [Set.disjoint_left]
  rintro y ⟨z, hz, hyz⟩ ⟨z', hz', hyz'⟩
  simp only [Set.mem_ofPred_eq] at hz hz'
  have hinj : z = z' := D.inj (hyz.trans hyz'.symm)
  have hnorm : ‖((z : ℂ))‖ = ‖((z' : ℂ))‖ := by rw [hinj]
  linarith

/-- **The carrier of a disc region is the union of its interior and its boundary.** -/
theorem discRegion_carrier_eq_interior_union_boundary {P : Work.CoreTopology.ParamTorus}
    (D : Work.SurgeryInvariance.DiscRegion P) :
    D.carrier = D.interior ∪ D.boundary := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    have hz : ‖((z : ℂ))‖ ≤ 1 := by
      have h := z.2
      rw [Metric.mem_closedBall, dist_zero_right] at h
      exact h
    rcases lt_or_eq_of_le hz with h | h
    · exact Or.inl ⟨z, h, rfl⟩
    · exact Or.inr ⟨z, h, rfl⟩
  · rintro (h | h)
    · exact D.interior_subset_carrier h
    · exact D.boundary_subset_carrier h

/-- **The complement of the boundary circle inside the box region splits into the two open
pieces** (the part inside the disc and the part outside it). -/
theorem boxRegion_sdiff_boundary_eq {P : Work.CoreTopology.ParamTorus} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} (D : Work.SurgeryInvariance.DiscRegion P)
    (_hslice : Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ D.interior) :
    Work.BoxShrink.Core.boxRegion P s c σ \ D.boundary =
      (Work.BoxShrink.Core.boxRegion P s c σ ∩ D.interior) ∪
        (Work.BoxShrink.Core.boxRegion P s c σ \ D.carrier) := by
  have hdec := discRegion_carrier_eq_interior_union_boundary D
  ext x
  constructor
  · rintro ⟨hx, hxb⟩
    by_cases hc : x ∈ D.carrier
    · refine Or.inl ⟨hx, ?_⟩
      rcases (show x ∈ D.interior ∪ D.boundary from hdec ▸ hc) with h | h
      · exact h
      · exact absurd h hxb
    · exact Or.inr ⟨hx, hc⟩
  · rintro (⟨hx, hxi⟩ | ⟨hx, hxc⟩)
    · exact ⟨hx, fun hb => (Set.disjoint_left.mp (discRegion_disjoint_interior_boundary D)) hxi hb⟩
    · exact ⟨hx, fun hb => hxc (D.boundary_subset_carrier hb)⟩

/-- **The box region with the boundary circle of a disc containing the slice removed is
inessential.**  The two pieces are each contained in an inessential region — the first in the disc
(`W(disc) = ⊥`), the second in the union of the two half-regions (`h0`) — and they are disjoint and
open, so `WindingSpan` is additive over them. -/
theorem windingSpan_sdiff_boundary_eq_bot {P : Work.CoreTopology.ParamTorus} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} (D : Work.SurgeryInvariance.DiscRegion P)
    (hslice : Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ D.interior)
    (h0 : Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) = ⊥) :
    Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.boxRegion P s c σ \ D.boundary) = ⊥ := by
  have hopenD : Work.SurgeryInvariance.IsOpenInCarrier P D.carrierᶜ := by
    rw [Work.SurgeryInvariance.IsOpenInCarrier, Set.preimage_compl]
    exact ((isClosed_carrier_of_discRegion D).preimage continuous_subtype_val).isOpen_compl
  have hA : Work.SurgeryInvariance.IsOpenInCarrier P
      (Work.BoxShrink.Core.boxRegion P s c σ ∩ D.interior) :=
    Work.SurgeryInvariance.isOpenInCarrier_inter (P := P)
      (Work.BoxShrink.Core.isOpenInCarrier_boxRegion P s c σ) D.open_interior'
  have hB : Work.SurgeryInvariance.IsOpenInCarrier P
      (Work.BoxShrink.Core.boxRegion P s c σ \ D.carrier) := by
    rw [Set.sdiff_eq]
    exact Work.SurgeryInvariance.isOpenInCarrier_inter (P := P)
      (Work.BoxShrink.Core.isOpenInCarrier_boxRegion P s c σ) hopenD
  have hdisj : Disjoint (Work.BoxShrink.Core.boxRegion P s c σ ∩ D.interior)
      (Work.BoxShrink.Core.boxRegion P s c σ \ D.carrier) := by
    rw [Set.disjoint_left]
    rintro x ⟨-, hxi⟩ ⟨-, hxc⟩
    exact hxc (D.interior_subset_carrier hxi)
  have hAle : Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.boxRegion P s c σ ∩ D.interior) ≤ ⊥ :=
    le_trans (Work.SurgeryInvariance.WindingSpan_mono P Set.inter_subset_right)
      (le_of_eq (windingSpan_eq_bot_of_subset_discRegion D D.interior_subset_carrier))
  have hBle : Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.boxRegion P s c σ \ D.carrier) ≤ ⊥ := by
    have hsub : Work.BoxShrink.Core.boxRegion P s c σ \ D.carrier ⊆
        Work.PinchLemma3.halfRegions P s c σ u := by
      rw [← boxRegion_sdiff_sliceRegion (P := P) (s := s) (c := c) (σ := σ) (u := u)]
      rintro x ⟨hxΩ, hxc⟩
      exact ⟨hxΩ, fun hs => hxc (D.interior_subset_carrier (hslice hs))⟩
    calc Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ \ D.carrier)
        ≤ Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) :=
          Work.SurgeryInvariance.WindingSpan_mono P hsub
      _ = ⊥ := h0
  rw [boxRegion_sdiff_boundary_eq (P := P) (s := s) (c := c) (σ := σ) (u := u) D hslice,
    Work.SurgeryInvariance.Span.union_eq_sup hA hB hdisj]
  exact le_antisymm (sup_le hAle hBle) bot_le

/-- **`wall_core` when the boundary circle of the disc misses the region inside the box.**  Then no
loop of the box region crosses the boundary circle, so the box region is the disjoint union of its
parts inside and outside the disc, both inessential: the strong conclusion `W(Ω) = ⊥` holds. -/
theorem wall_core_of_boundary_disjoint (P : Work.CoreTopology.ParamTorus) (s : ℝ)
    (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (D : Work.SurgeryInvariance.DiscRegion P)
    (_hD : D.carrier ⊆ Work.PinchLemma3.closedBoxRegion P s c σ)
    (hslice : Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ D.interior)
    (_hT : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Pinch.planeTrace P c σ u) = ⊥)
    (h0 : Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) = ⊥)
    (hdisj : Disjoint (Work.BoxShrink.Core.boxRegion P s c σ) D.boundary) :
    ∃ v : ℚ × ℚ, v ≠ 0 ∧
      Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ⊓
        Submodule.span ℚ ({v} : Set (ℚ × ℚ)) ≤
      Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) := by
  have hself : Work.BoxShrink.Core.boxRegion P s c σ \ D.boundary
      = Work.BoxShrink.Core.boxRegion P s c σ := by
    refine Set.Subset.antisymm Set.sdiff_subset ?_
    intro x hx
    exact ⟨hx, fun hb => (Set.disjoint_left.mp hdisj) hx hb⟩
  have h := windingSpan_sdiff_boundary_eq_bot (P := P) (s := s) (c := c) (σ := σ) (u := u)
    D hslice h0
  rw [hself] at h
  exact wall_core_of_ne_top (by rw [h]; exact bot_ne_top)



/-! ## The sharpened reduction: only the gates of the disc can carry a winding

The push-off `Work.PinchLemma3.ClosedDiscA.windingSpan_boxRegion_le_sdiff_interior_union_boundary`
(proved by a colleague) reroutes a loop of `Ω` off the interior of the disc `D` onto its boundary
circle.  Since the slice lies in `D.interior` and the closed box region is the box region together
with the sphere trace, the rerouted loop lies in `halfRegions` together with the *gates*
`∂D ∩ (F ∩ ∂Box)`: the points where the boundary circle of the disc meets the boundary sphere of the
box.  This is the sharpest reduction of the residual that the disc hypothesis gives. -/

/-- **The windings of the box region are realised by the half-regions together with the gates of
the disc.**  The rerouted loop of the push-off lies in `(Ω \ D°) ∪ ∂D`; the first piece is
contained in `Ω \ Σ = halves` (as `Σ ⊆ D°`), and the second in the sphere trace (as
`D.carrier ⊆ closedBoxRegion = Ω ∪ sphereTrace`), so only the gates `∂D ∩ sphereTrace` survive
outside `halves` — and where the boundary circle meets the *region*, it already lies in the halves
(`Σ ⊆ D°` while `∂D ∩ D° = ∅`). -/
theorem windingSpan_boxRegion_le_halves_union_gates {P : Work.CoreTopology.ParamTorus} {s : ℝ}
    {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} (D : Work.SurgeryInvariance.DiscRegion P)
    (hD : D.carrier ⊆ Work.PinchLemma3.closedBoxRegion P s c σ)
    (hslice : Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ D.interior) :
    Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ≤
      Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u ∪
        ((P.carrier ∩ {y : R3 | Submission.boxNorm c σ y = s}) ∩ D.boundary)) := by
  refine le_trans
    (windingSpan_boxRegion_le_sdiff_interior_union_boundary (P := P) (s := s) (c := c) (σ := σ) D)
    (Work.SurgeryInvariance.WindingSpan_mono P ?_)
  rintro x (hx | hx)
  · -- a point of the box region outside the disc's interior lies in the halves
    have hslicenot : x ∉ Work.BoxShrink.Core.sliceRegion P s c σ u := fun hs => hx.2 (hslice hs)
    exact Or.inl ((boxRegion_sdiff_sliceRegion (P := P) (s := s) (c := c) (σ := σ) (u := u)).symm ▸
      ⟨hx.1, hslicenot⟩)
  · -- a point of the disc's boundary: in the region, or in the sphere trace
    have hcarrier : x ∈ D.carrier := D.boundary_subset_carrier hx
    have hclosed : x ∈ Work.PinchLemma3.closedBoxRegion P s c σ := hD hcarrier
    have hmem : x ∈ Work.BoxShrink.Core.boxRegion P s c σ ∪
        (P.carrier ∩ {y : R3 | Submission.boxNorm c σ y = s}) := by
      rw [← closedBoxRegion_eq_boxRegion_union_sphereTrace (P := P) (s := s) (c := c) (σ := σ)]
      exact hclosed
    rcases hmem with hb | hsp
    · have hslicenot : x ∉ Work.BoxShrink.Core.sliceRegion P s c σ u := fun hs =>
        (Set.disjoint_left.mp (discRegion_disjoint_interior_boundary D)) (hslice hs) hx
      exact Or.inl ((boxRegion_sdiff_sliceRegion (P := P) (s := s) (c := c) (σ := σ) (u := u)).symm ▸
        ⟨hb, hslicenot⟩)
    · exact Or.inr ⟨hsp, hx⟩

/-- **`wall_core` when the boundary circle of the disc misses the boundary sphere of the box.**
Then the gates of `windingSpan_boxRegion_le_halves_union_gates` are empty, the box region's
winding span is contained in that of the two half-regions, and `h0` makes it vanish. -/
theorem wall_core_of_boundary_avoids_sphereTrace (P : Work.CoreTopology.ParamTorus) (s : ℝ)
    (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (D : Work.SurgeryInvariance.DiscRegion P)
    (hD : D.carrier ⊆ Work.PinchLemma3.closedBoxRegion P s c σ)
    (hslice : Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ D.interior)
    (_hT : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Pinch.planeTrace P c σ u) = ⊥)
    (h0 : Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) = ⊥)
    (hgates : Disjoint (P.carrier ∩ {y : R3 | Submission.boxNorm c σ y = s}) D.boundary) :
    ∃ v : ℚ × ℚ, v ≠ 0 ∧
      Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ⊓
        Submodule.span ℚ ({v} : Set (ℚ × ℚ)) ≤
      Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) := by
  have hsub : Work.PinchLemma3.halfRegions P s c σ u ∪
      ((P.carrier ∩ {y : R3 | Submission.boxNorm c σ y = s}) ∩ D.boundary) ⊆
      Work.PinchLemma3.halfRegions P s c σ u := by
    rintro x (hx | hx)
    · exact hx
    · exact absurd hx.2 (Set.disjoint_left.mp hgates hx.1)
  have hbot : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) = ⊥ :=
    le_bot_iff.mp (le_trans
      (windingSpan_boxRegion_le_halves_union_gates (P := P) (s := s) (c := c) (σ := σ) (u := u)
        D hD hslice)
      (le_trans (Work.SurgeryInvariance.WindingSpan_mono P hsub) (le_of_eq h0)))
  exact wall_core_of_ne_top (by rw [hbot]; exact bot_ne_top)


/-! ## The two-piece criterion, and the reduction of `wall_core` to a connectivity statement

The tool of this section is `windingSpan_eq_bot_of_subset_union`: a set covered by two pieces that
are open in the carrier, each of vanishing winding span, and whose intersection is path connected
(or empty), has vanishing winding span.  It is the curve-level van Kampen statement of the
colleague-proved `windingSpan_union_le_sup_of_isPathConnected_inter`, together with the trivial
case in which the two pieces are disjoint (then `Span.union_eq_sup` applies).

Its use here is the reduction of `wall_core` to a *connectivity* statement.  The box region is
covered by the upper half-region and the union of the lower half-region with the disc carrying the
slice; those two pieces are open in the carrier, the second is inessential (the lower half is, and
so is any subset of the disc), and their intersection is the upper half of the disc.  So *if* the
upper half of the disc is path connected (and likewise the lower half), the box region is
*inessential*, and `wall_core` follows with the strong conclusion `W(Ω) = ⊥` — with no use of `hT`
and no use of the sphere trace. -/

/-- **A set covered by two inessential pieces with path connected (or empty) intersection is
inessential.** -/
theorem windingSpan_eq_bot_of_subset_union {P : Work.CoreTopology.ParamTorus} {X A B : Set R3}
    (hAc : A ⊆ P.carrier) (hBc : B ⊆ P.carrier)
    (hA : Work.SurgeryInvariance.IsOpenInCarrier P A)
    (hB : Work.SurgeryInvariance.IsOpenInCarrier P B)
    (hconn : ∀ x ∈ A ∩ B, ∀ y ∈ A ∩ B, JoinedIn (A ∩ B) x y)
    (hWA : Work.SurgeryInvariance.WindingSpan P A = ⊥)
    (hWB : Work.SurgeryInvariance.WindingSpan P B = ⊥)
    (hX : X ⊆ A ∪ B) :
    Work.SurgeryInvariance.WindingSpan P X = ⊥ := by
  have hle : Work.SurgeryInvariance.WindingSpan P (A ∪ B) ≤
      Work.SurgeryInvariance.WindingSpan P A ⊔ Work.SurgeryInvariance.WindingSpan P B := by
    by_cases hne : (A ∩ B).Nonempty
    · exact windingSpan_union_le_sup_of_isPathConnected_inter hAc hBc hA hB
        (isPathConnected_iff.mpr ⟨hne, hconn⟩)
    · rw [← Work.SurgeryInvariance.Span.union_eq_sup hA hB
        (Set.disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp hne))]
  refine le_bot_iff.mp (le_trans (Work.SurgeryInvariance.WindingSpan_mono P hX) ?_)
  refine le_trans hle ?_
  rw [hWA, hWB]
  simp

/-- **The `JoinedIn` form of path connectedness**, for feeding the two-piece criterion. -/
theorem joinedIn_of_isPathConnected {S : Set R3} (h : IsPathConnected S) :
    ∀ x ∈ S, ∀ y ∈ S, JoinedIn S x y := (isPathConnected_iff.mp h).2

/-- **The two half-regions are disjoint**: one lies above the cutting plane, the other below. -/
theorem disjoint_upperRegion_lowerRegion (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Disjoint (Work.BoxShrink.Core.upperRegion P s c σ u)
      (Work.BoxShrink.Core.lowerRegion P s c σ u) := by
  rw [Set.disjoint_left]
  intro y hyU hyL
  rw [Work.BoxShrink.Core.mem_upperRegion] at hyU
  rw [Work.BoxShrink.Core.mem_lowerRegion] at hyL
  linarith [hyU.2.2, hyL.2.2]

/-- **The box region is inessential as soon as a disc carrying the slice has path connected halves
inside it.**  The box region is the union of the two half-regions and the slice
(`boxRegion_eq_union`), and the slice lies in the disc (`hslice`): so the box region is covered by
the upper half-region and the union of the lower half-region with the disc.  Each of those two
pieces is inessential — the first lies in `halfRegions`, whose span is `⊥` by `h0`, the second is
the union of the lower half-region with a subset of a disc, and both are inessential — and their
intersection is the *upper half of the disc* `Ω⁺ ∩ D°` (the half-regions are disjoint), which the
hypothesis `hU` makes path connected.  So the two-piece criterion applies. -/
theorem windingSpan_boxRegion_eq_bot_of_disc_pathConnected {P : Work.CoreTopology.ParamTorus}
    {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (D : Work.SurgeryInvariance.DiscRegion P)
    (hslice : Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ D.interior)
    (h0 : Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) = ⊥)
    (hU : ∀ x ∈ Work.BoxShrink.Core.upperRegion P s c σ u ∩ D.interior,
      ∀ y ∈ Work.BoxShrink.Core.upperRegion P s c σ u ∩ D.interior,
        JoinedIn (Work.BoxShrink.Core.upperRegion P s c σ u ∩ D.interior) x y)
    (hL : ∀ x ∈ Work.BoxShrink.Core.lowerRegion P s c σ u ∩ D.interior,
      ∀ y ∈ Work.BoxShrink.Core.lowerRegion P s c σ u ∩ D.interior,
        JoinedIn (Work.BoxShrink.Core.lowerRegion P s c σ u ∩ D.interior) x y) :
    Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) = ⊥ := by
  have hlower_le : Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.lowerRegion P s c σ u) = ⊥ :=
    le_bot_iff.mp (le_trans (Work.SurgeryInvariance.WindingSpan_mono P
      (fun y hy => Or.inr hy)) (le_of_eq h0))
  have hdisc_le : Work.SurgeryInvariance.WindingSpan P D.interior = ⊥ :=
    windingSpan_eq_bot_of_subset_discRegion D D.interior_subset_carrier
  have hWB : Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.lowerRegion P s c σ u ∪ D.interior) = ⊥ :=
    windingSpan_eq_bot_of_subset_union
      (fun y hy => (Work.BoxShrink.Core.mem_lowerRegion.mp hy).1)
      (fun y hy => D.interior_subset_surface hy)
      (Work.BoxShrink.Core.isOpenInCarrier_lowerRegion P s c σ u) D.open_interior'
      hL hlower_le hdisc_le subset_rfl
  have hdisj := disjoint_upperRegion_lowerRegion P s c σ u
  have hAB : (Work.BoxShrink.Core.upperRegion P s c σ u ∩
        (Work.BoxShrink.Core.lowerRegion P s c σ u ∪ D.interior)) =
      Work.BoxShrink.Core.upperRegion P s c σ u ∩ D.interior := by
    rw [Set.inter_union_distrib_left, Set.disjoint_iff_inter_eq_empty.mp hdisj, Set.empty_union]
  refine windingSpan_eq_bot_of_subset_union
    (fun y hy => (Work.BoxShrink.Core.mem_upperRegion.mp hy).1)
    (fun y hy => hy.elim (fun h => (Work.BoxShrink.Core.mem_lowerRegion.mp h).1)
      (fun h => D.interior_subset_surface h))
    (Work.BoxShrink.Core.isOpenInCarrier_upperRegion P s c σ u)
    (Work.SurgeryInvariance.isOpenInCarrier_union P
      (Work.BoxShrink.Core.isOpenInCarrier_lowerRegion P s c σ u) D.open_interior')
    ?_ (le_bot_iff.mp (le_trans (Work.SurgeryInvariance.WindingSpan_mono P
      (fun y hy => Or.inl hy)) (le_of_eq h0))) hWB ?_
  · intro x hx y hy
    rw [hAB] at hx hy ⊢
    exact hU x hx y hy
  · intro y hy
    rw [Work.BoxShrink.Core.boxRegion_eq_union P s c σ u] at hy
    rcases hy with (hy | hy) | hy
    · exact Or.inl hy
    · exact Or.inr (Or.inl hy)
    · exact Or.inr (Or.inr (hslice hy))

/-- **`wall_core` from the path connectedness of the two halves of the disc carrying the slice.**
The strong conclusion `W(Ω) = ⊥` is obtained; `hT` is not used. -/
theorem wall_core_of_halves_inter_disc_pathConnected (P : Work.CoreTopology.ParamTorus) (s : ℝ)
    (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (D : Work.SurgeryInvariance.DiscRegion P)
    (hslice : Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ D.interior)
    (_hT : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Pinch.planeTrace P c σ u) = ⊥)
    (h0 : Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) = ⊥)
    (hU : ∀ x ∈ Work.BoxShrink.Core.upperRegion P s c σ u ∩ D.interior,
      ∀ y ∈ Work.BoxShrink.Core.upperRegion P s c σ u ∩ D.interior,
        JoinedIn (Work.BoxShrink.Core.upperRegion P s c σ u ∩ D.interior) x y)
    (hL : ∀ x ∈ Work.BoxShrink.Core.lowerRegion P s c σ u ∩ D.interior,
      ∀ y ∈ Work.BoxShrink.Core.lowerRegion P s c σ u ∩ D.interior,
        JoinedIn (Work.BoxShrink.Core.lowerRegion P s c σ u ∩ D.interior) x y) :
    ∃ v : ℚ × ℚ, v ≠ 0 ∧
      Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ⊓
        Submodule.span ℚ ({v} : Set (ℚ × ℚ)) ≤
      Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) :=
  wall_core_of_ne_top (by
    rw [windingSpan_boxRegion_eq_bot_of_disc_pathConnected D hslice h0 hU hL]
    exact bot_ne_top)

/-! ## The general push-off, the inessentiality of the disc's boundary, and the peel-based form of
the reduction

`windingSpan_le_sdiff_interior_union_boundary` is the push-off for an *arbitrary* set `X` (the
sibling lemma is the case `X = Ω`), and `windingSpan_boundary_eq_bot_of_discRegion` /
`windingSpan_gates_eq_bot` record that the boundary circle of the disc, and hence the *gates*
`∂D ∩ (F ∩ ∂Box)`, carry no winding at all: they lie in the carrier of the disc, which is
contractible.

`sliceRegion_subset_interiorInCarrier_closedBoxRegion` is the *exact* content of the two hypotheses
`hD`, `hslice`: every point of the slice has a neighbourhood in the carrier contained in the closed
box region.  In particular **no slice point is a limit point of the caps of the box**: a slice point
whose `F`-neighbourhoods all meet the complement of the closed box would make `hD + hslice`
impossible.  This is why the hypotheses of `wall_core` are *much* stronger than the trace- and
halves-inessentiality of the sibling refutations: at the standard-torus configuration of
`strong_span_form_refuted` (where `W(Ω) ≠ ⊥`) the endpoints of the slice arcs are *transversal*
crossings of the box sphere, so the slice is not contained in the interior of the closed box and
`hslice` fails there. -/

/-- **The interior of a set of the surface, in the carrier topology**, in the form of a set of
points of `ℝ³`: the points all of whose carrier-neighbourhoods-to-be are contained in the set. -/
def interiorInCarrier (P : Work.CoreTopology.ParamTorus) (Z : Set R3) : Set R3 :=
  {y : R3 | ∃ V : Set R3, Work.SurgeryInvariance.IsOpenInCarrier P V ∧ y ∈ V ∧ V ⊆ Z}

theorem mem_interiorInCarrier {P : Work.CoreTopology.ParamTorus} {Z : Set R3} {y : R3} :
    y ∈ interiorInCarrier P Z ↔
      ∃ V : Set R3, Work.SurgeryInvariance.IsOpenInCarrier P V ∧ y ∈ V ∧ V ⊆ Z := Iff.rfl

theorem interiorInCarrier_subset {P : Work.CoreTopology.ParamTorus} {Z : Set R3} :
    interiorInCarrier P Z ⊆ Z := by
  rintro y ⟨V, -, hy, hV⟩
  exact hV hy

/-- **Every slice point has a neighbourhood contained in the closed box region.**  This is what
`hD` (the disc lies in the closed box) and `hslice` (the slice lies in the interior of the disc)
say together: the interior of the disc is open in the carrier, and it is contained in the closed box
region. -/
theorem sliceRegion_subset_interiorInCarrier_closedBoxRegion {P : Work.CoreTopology.ParamTorus}
    {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (D : Work.SurgeryInvariance.DiscRegion P)
    (hD : D.carrier ⊆ Work.PinchLemma3.closedBoxRegion P s c σ)
    (hslice : Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ D.interior) :
    Work.BoxShrink.Core.sliceRegion P s c σ u ⊆
      interiorInCarrier P (Work.PinchLemma3.closedBoxRegion P s c σ) :=
  fun y hy => ⟨D.interior, D.open_interior', hslice hy,
    fun z hz => hD (D.interior_subset_carrier hz)⟩

/-- **The push-off of an arbitrary set off the interior of an embedded disc.**  The general form of
`windingSpan_boxRegion_le_sdiff_interior_union_boundary` (the sibling lemma is the case
`X = Ω = boxRegion`): every loop of `X` is homotopic, in the surface, to a loop of
`(X \ D.interior) ∪ D.boundary` with the same winding vector (the disc re-route
`Work.PinchLemma3.ClosedDiscA.disc_reroute_general`). -/
theorem windingSpan_le_sdiff_interior_union_boundary {P : Work.CoreTopology.ParamTorus}
    {X : Set R3} (D : Work.SurgeryInvariance.DiscRegion P) :
    Work.SurgeryInvariance.WindingSpan P X ≤
      Work.SurgeryInvariance.WindingSpan P ((X \ D.interior) ∪ D.boundary) := by
  rw [Work.SurgeryInvariance.WindingSpan, Work.SurgeryInvariance.WindingSpan, Submodule.span_le]
  rintro v ⟨γ, hγ, rfl⟩
  obtain ⟨γ', hhom, hfix, hbnd⟩ := disc_reroute_general D γ
  have hmem : ∀ t : ℝ, γ' t ∈ (X \ D.interior) ∪ D.boundary := by
    intro t
    by_cases h : γ t ∈ D.interior
    · exact Or.inr (hbnd t h)
    · exact Or.inl ⟨by rw [hfix t h]; exact hγ t, by rw [hfix t h]; exact h⟩
  have hw : Work.SurgeryInvariance.windingOf P γ' = Work.SurgeryInvariance.windingOf P γ :=
    (Work.SurgeryInvariance.WindingOf.homotopic_eq hhom).symm
  exact Submodule.subset_span ⟨γ', hmem, by rw [hw]⟩

/-- **The boundary circle of an embedded disc carries no winding.** -/
theorem windingSpan_boundary_eq_bot_of_discRegion {P : Work.CoreTopology.ParamTorus}
    (D : Work.SurgeryInvariance.DiscRegion P) :
    Work.SurgeryInvariance.WindingSpan P D.boundary = ⊥ :=
  windingSpan_eq_bot_of_subset_discRegion D D.boundary_subset_carrier

/-- **The winding span of the gates is trivial**: the gates are a subset of the boundary circle of
the disc, which lies in the carrier of the disc. -/
theorem windingSpan_gates_eq_bot_of_discRegion {P : Work.CoreTopology.ParamTorus} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} (D : Work.SurgeryInvariance.DiscRegion P) :
    Work.SurgeryInvariance.WindingSpan P
      ((P.carrier ∩ {y : R3 | Submission.boxNorm c σ y = s}) ∩ D.boundary) = ⊥ :=
  windingSpan_eq_bot_of_subset_discRegion D (fun _ hy => D.boundary_subset_carrier hy.2)


/-! ## The peel of the boundary circle: the sharpest reduction yet

The sibling lemma `Work.BoxShrink.PinchOff.peel_range_eq_of_nhds` removes a simple *inessential*
closed curve `γ` from a region containing an open neighbourhood of it, leaving the winding span
unchanged.  The boundary circle of the disc `D` is such a curve — it bounds `D` itself — and every
*thickening* `D₂` of `D` (an embedded disc with `D.carrier ⊆ D₂.interior`, which exists by
`Work.BoxShrink.PinchOff.exists_outerDiscRegion`) contains an open neighbourhood of `∂D`.  So the
winding span of `U ∪ D₂.interior` — which contains the box region `Ω`, because the slice lies in
`D.interior ⊆ D.carrier ⊆ D₂.interior` — is unchanged when the boundary circle is deleted:

  `W(Ω) ≤ W(U ∪ D₂°) = W((U ∪ D₂°) \ ∂D) = W((U \ D.carrier) ∪ D.interior ∪ (D₂° \ D.carrier))`.

The three pieces of the last set are *all* inessential: `U \ D.carrier ⊆ U`, `D°` is a disc, and
`D₂° \ D.carrier ⊆ D₂°` is a disc; and the only overlap among them is the *collar part*
`U ∩ (D₂° \ D.carrier)`.  So the two-piece criterion `windingSpan_eq_bot_of_subset_union` gives
`W(Ω) = ⊥` as soon as that collar part is path connected — a statement only about a *thin collar*
of the boundary circle, and the sharpest form of the residual that this route produces. -/

/-- The two half-regions together are open in the carrier. -/
theorem isOpenInCarrier_halfRegions (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Work.SurgeryInvariance.IsOpenInCarrier P (Work.PinchLemma3.halfRegions P s c σ u) :=
  Work.SurgeryInvariance.isOpenInCarrier_union P
    (Work.BoxShrink.Core.isOpenInCarrier_upperRegion P s c σ u)
    (Work.BoxShrink.Core.isOpenInCarrier_lowerRegion P s c σ u)

/-- **Peeling the boundary circle of the disc.**  If `D₂` is an embedded disc containing the closed
disc `D` in its interior, and `γ` is a closed curve whose image is the boundary circle of `D`, then
deleting that circle from `halfRegions ∪ D₂.interior` leaves the winding span unchanged. -/
theorem windingSpan_halves_union_disc_eq_sdiff_boundary {P : Work.CoreTopology.ParamTorus} {s : ℝ}
    {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} (D D₂ : Work.SurgeryInvariance.DiscRegion P)
    (hD₂ : D.carrier ⊆ D₂.interior) {γ : Work.CoreTopology.ClosedCurve P}
    (hγrange : Set.range γ.γ = D.boundary)
    (hsimple : Work.CoreTopology.IsSimple P γ)
    (hiness : ¬ Work.CoreTopology.IsEssential P γ) :
    Work.SurgeryInvariance.WindingSpan P
        (Work.PinchLemma3.halfRegions P s c σ u ∪ D₂.interior) =
      Work.SurgeryInvariance.WindingSpan P
        ((Work.PinchLemma3.halfRegions P s c σ u ∪ D₂.interior) \ D.boundary) := by
  have hmem : Set.range γ.γ ⊆ D₂.interior := by
    rw [hγrange]
    exact fun x hx => hD₂ (D.boundary_subset_carrier hx)
  rw [← hγrange]
  exact Work.BoxShrink.PinchOff.peel_range_eq_of_nhds hsimple hiness
    ⟨D₂.interior, D₂.open_interior', hmem, Set.subset_union_right⟩

/-- **The box region is inessential as soon as the collar of the boundary circle inside the halves
is path connected.**  This is the sharpened form of the residual obtained by peeling `∂D`: the
hypothesis speaks only about the *collar* `U ∩ (D₂° \ D.carrier)` of the boundary circle, all
other pieces of the cover being discs or parts of the halves. -/
theorem windingSpan_boxRegion_eq_bot_of_annulus_connected {P : Work.CoreTopology.ParamTorus}
    {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} (D : Work.SurgeryInvariance.DiscRegion P)
    (hslice : Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ D.interior)
    (h0 : Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) = ⊥)
    (D₂ : Work.SurgeryInvariance.DiscRegion P) (hD₂ : D.carrier ⊆ D₂.interior)
    {γ : Work.CoreTopology.ClosedCurve P} (hγrange : Set.range γ.γ = D.boundary)
    (hsimple : Work.CoreTopology.IsSimple P γ)
    (hiness : ¬ Work.CoreTopology.IsEssential P γ)
    (hconn : ∀ x ∈ Work.PinchLemma3.halfRegions P s c σ u ∩ (D₂.interior \ D.carrier),
      ∀ y ∈ Work.PinchLemma3.halfRegions P s c σ u ∩ (D₂.interior \ D.carrier),
        JoinedIn (Work.PinchLemma3.halfRegions P s c σ u ∩ (D₂.interior \ D.carrier)) x y) :
    Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) = ⊥ := by
  have hΩ : Work.BoxShrink.Core.boxRegion P s c σ ⊆
      Work.PinchLemma3.halfRegions P s c σ u ∪ D₂.interior := by
    intro y hy
    rw [Work.BoxShrink.Core.boxRegion_eq_union P s c σ u] at hy
    rcases hy with (hy | hy) | hy
    · exact Or.inl (Or.inl hy)
    · exact Or.inl (Or.inr hy)
    · exact Or.inr (hD₂ (D.interior_subset_carrier (hslice hy)))
  have hpeel := windingSpan_halves_union_disc_eq_sdiff_boundary (P := P) (s := s) (c := c)
    (σ := σ) (u := u) D D₂ hD₂ hγrange hsimple hiness
  -- the complement of the boundary circle, split into two pieces
  have hkey : ∀ y : R3, y ∈ D.carrier → y ∉ D.boundary → y ∈ D.interior := by
    intro y hc hb
    rcases (Set.ext_iff.mp (discRegion_carrier_eq_interior_union_boundary D) y).mp hc with h | h
    · exact h
    · exact absurd h hb
  have hset : (Work.PinchLemma3.halfRegions P s c σ u ∪ D₂.interior) \ D.boundary =
      ((Work.PinchLemma3.halfRegions P s c σ u \ D.carrier) ∪ D.interior) ∪
        (D₂.interior \ D.carrier) := by
    ext y
    constructor
    · rintro ⟨hy | hy, hb⟩
      · by_cases hc : y ∈ D.carrier
        · exact Or.inl (Or.inr (hkey y hc hb))
        · exact Or.inl (Or.inl ⟨hy, hc⟩)
      · by_cases hc : y ∈ D.carrier
        · exact Or.inl (Or.inr (hkey y hc hb))
        · exact Or.inr ⟨hy, hc⟩
    · rintro ((⟨hy, hc⟩ | hy) | ⟨hy, hc⟩)
      · exact ⟨Or.inl hy, fun hb => hc ((discRegion_carrier_eq_interior_union_boundary D) ▸
          Or.inr hb)⟩
      · exact ⟨Or.inr (hD₂ (D.interior_subset_carrier hy)), fun hb =>
          (Set.disjoint_left.mp (discRegion_disjoint_interior_boundary D)) hy hb⟩
      · exact ⟨Or.inr hy, fun hb => hc ((discRegion_carrier_eq_interior_union_boundary D) ▸
          Or.inr hb)⟩
  -- the first piece is inessential: a part of the halves together with the disc
  have hWA : Work.SurgeryInvariance.WindingSpan P
      ((Work.PinchLemma3.halfRegions P s c σ u \ D.carrier) ∪ D.interior) = ⊥ := by
    have hs : Work.SurgeryInvariance.WindingSpan P
        ((Work.PinchLemma3.halfRegions P s c σ u \ D.carrier) ∪ D.interior) =
          Work.SurgeryInvariance.WindingSpan P
            (Work.PinchLemma3.halfRegions P s c σ u \ D.carrier) ⊔
          Work.SurgeryInvariance.WindingSpan P D.interior :=
      Work.SurgeryInvariance.Span.union_eq_sup
        (Work.BoxShrink.PinchOff.isOpenInCarrier_sdiff_of_isClosed
          (isOpenInCarrier_halfRegions P s c σ u) (isClosed_carrier_of_discRegion D))
        D.open_interior' (by
          rw [Set.disjoint_left]
          rintro y ⟨-, hc⟩ hd
          exact hc (D.interior_subset_carrier hd))
    have h1 : Work.SurgeryInvariance.WindingSpan P
        (Work.PinchLemma3.halfRegions P s c σ u \ D.carrier) = ⊥ :=
      le_bot_iff.mp (le_trans (Work.SurgeryInvariance.WindingSpan_mono P Set.sdiff_subset)
        (le_of_eq h0))
    have h2 : Work.SurgeryInvariance.WindingSpan P D.interior = ⊥ :=
      windingSpan_eq_bot_of_subset_discRegion D D.interior_subset_carrier
    rw [hs, h1, h2]
    simp
  -- the second piece is inessential: a subset of the thickening disc
  have hWB : Work.SurgeryInvariance.WindingSpan P (D₂.interior \ D.carrier) = ⊥ :=
    le_bot_iff.mp (le_trans (Work.SurgeryInvariance.WindingSpan_mono P
      (fun _ hy => D₂.interior_subset_carrier hy.1))
      (le_of_eq (windingSpan_carrier_eq_bot_of_discRegion D₂)))
  have hint : ((Work.PinchLemma3.halfRegions P s c σ u \ D.carrier) ∪ D.interior) ∩
      (D₂.interior \ D.carrier)
      = Work.PinchLemma3.halfRegions P s c σ u ∩ (D₂.interior \ D.carrier) := by
    ext y
    constructor
    · rintro ⟨hyA, hyB⟩
      rcases hyA with ⟨hy, hc⟩ | hy
      · exact ⟨hy, hyB⟩
      · exact absurd hyB.2 (fun hc' => hc' (D.interior_subset_carrier hy))
    · rintro ⟨hy, hyB⟩
      exact ⟨Or.inl ⟨hy, hyB.2⟩, hyB⟩
  refine le_bot_iff.mp (le_trans (Work.SurgeryInvariance.WindingSpan_mono P hΩ) ?_)
  rw [hpeel, hset]
  exact le_of_eq (windingSpan_eq_bot_of_subset_union
    (fun y hy => hy.elim
      (fun h => (Work.PinchLemma3.halfRegions_subset_boxRegion P s c σ u h.1).1)
      (fun h => D.interior_subset_surface h))
    (fun y hy => D₂.interior_subset_surface hy.1)
    (Work.SurgeryInvariance.isOpenInCarrier_union P
      (Work.BoxShrink.PinchOff.isOpenInCarrier_sdiff_of_isClosed
        (isOpenInCarrier_halfRegions P s c σ u) (isClosed_carrier_of_discRegion D))
      D.open_interior')
    (Work.BoxShrink.PinchOff.isOpenInCarrier_sdiff_of_isClosed D₂.open_interior'
      (isClosed_carrier_of_discRegion D))
    (by intro x hx y hy; rw [hint] at hx hy ⊢; exact hconn x hx y hy)
    hWA hWB (subset_refl _))


/-- **`wall_core` from the connectivity of the collar of the boundary circle inside the halves.**
The boundary circle of the disc is produced by the delegated
`exists_closedCurve_boundary_of_discRegion`, so the peel of `∂D` applies unconditionally, and the
whole residual is the connectivity of the collar `U ∩ (D₂.interior \ D.carrier)` of a *thickening*
`D₂` of `D`.  The conclusion is the strong one, `W(Ω) = ⊥`; `hT` is not used, `hD` is not needed
for this route (it enters only through the existence of the thickening). -/
theorem wall_core_of_collar_connected (P : Work.CoreTopology.ParamTorus) (s : ℝ)
    (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (D : Work.SurgeryInvariance.DiscRegion P)
    (_hD : D.carrier ⊆ Work.PinchLemma3.closedBoxRegion P s c σ)
    (hslice : Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ D.interior)
    (_hT : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Pinch.planeTrace P c σ u) = ⊥)
    (h0 : Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) = ⊥)
    (D₂ : Work.SurgeryInvariance.DiscRegion P) (hD₂ : D.carrier ⊆ D₂.interior)
    (hconn : ∀ x ∈ Work.PinchLemma3.halfRegions P s c σ u ∩ (D₂.interior \ D.carrier),
      ∀ y ∈ Work.PinchLemma3.halfRegions P s c σ u ∩ (D₂.interior \ D.carrier),
        JoinedIn (Work.PinchLemma3.halfRegions P s c σ u ∩ (D₂.interior \ D.carrier)) x y) :
    ∃ v : ℚ × ℚ, v ≠ 0 ∧
      Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ⊓
        Submodule.span ℚ ({v} : Set (ℚ × ℚ)) ≤
      Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) := by
  obtain ⟨γ, hγrange, hsimple, hiness⟩ := exists_closedCurve_boundary_of_discRegion D
  refine wall_core_of_ne_top (P := P) (s := s) (c := c) (σ := σ) (u := u) ?_
  rw [windingSpan_boxRegion_eq_bot_of_annulus_connected (P := P) (s := s) (c := c) (σ := σ)
    (u := u) D hslice h0 D₂ hD₂ hγrange hsimple hiness hconn]
  exact bot_ne_top

/-! ## The componentwise refinement of the collar reduction

The two-piece criterion needs the intersection of its two pieces to be *path connected*.  For the
collar `U ∩ (D₂° \ D̄)` this fails in general: in the flat local model (box = open square, `D` the
inscribed disc, the slice a diameter) the collar is the four corners of the square, one per corner,
and no thickening of `D` repairs that.  The right statement is therefore *componentwise*: the collar
is a union of sets that are open in the carrier (the components of an open subset of the locally
connected carrier) and path connected (they are connected, hence path connected, in the locally path
connected carrier), and the pieces can be added to the cover one component at a time — the
intersection of the accumulated union with the new component being that component, which lies in the
first piece `A₀` because `K ⊆ A₀`.  Compactness of a loop's image closes the gap between finite and
arbitrary covers.

The two general lemmas below are stated with the two properties of the components as hypotheses, so
that they are independent of the topology of the carrier; the instantiations are
`isOpenInCarrier_connectedComponentIn` and `isPathConnected_connectedComponentIn_carrier`. -/

/-- The empty set is open in the carrier. -/
theorem isOpenInCarrier_empty (P : Work.CoreTopology.ParamTorus) :
    Work.SurgeryInvariance.IsOpenInCarrier P (∅ : Set R3) := by
  unfold Work.SurgeryInvariance.IsOpenInCarrier
  simp

/-- The empty set realises no winding class: there is no loop in it. -/
theorem windingSpan_empty (P : Work.CoreTopology.ParamTorus) :
    Work.SurgeryInvariance.WindingSpan P (∅ : Set R3) = ⊥ := by
  rw [Work.SurgeryInvariance.WindingSpan_eq_bot_iff]
  rintro ⟨γ, -, hγ⟩
  exact absurd (hγ 0) (by simp)

/-- **A set covered by a family whose finite unions are inessential is inessential.**  A loop's
image is compact, so it lies in a finite subfamily, whose winding span vanishes. -/
theorem windingSpan_eq_bot_of_finite_unions {P : Work.CoreTopology.ParamTorus} {X : Set R3}
    {ι : Type*} (u : ι → Set R3)
    (huo : ∀ i, Work.SurgeryInvariance.IsOpenInCarrier P (u i))
    (hX : X ⊆ ⋃ i, u i)
    (hfin : ∀ s : Finset ι, Work.SurgeryInvariance.WindingSpan P (⋃ i ∈ s, u i) = ⊥) :
    Work.SurgeryInvariance.WindingSpan P X = ⊥ := by
  rw [Work.SurgeryInvariance.WindingSpan, Submodule.span_eq_bot]
  rintro v ⟨γ, hγ, rfl⟩
  have hΦ : Continuous (fun t : ℝ => (⟨γ.γ t, γ.mem t⟩ : P.carrier)) :=
    γ.cont.subtype_mk (fun t => γ.mem t)
  have hcpt : IsCompact ((fun t : ℝ => (⟨γ.γ t, γ.mem t⟩ : P.carrier)) ''
      Set.Icc 0 (2 * Real.pi)) := isCompact_Icc.image hΦ
  have hcov : ((fun t : ℝ => (⟨γ.γ t, γ.mem t⟩ : P.carrier)) '' Set.Icc 0 (2 * Real.pi)) ⊆
      ⋃ i, (Subtype.val ⁻¹' u i : Set P.carrier) := by
    rintro y ⟨t, -, rfl⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hX (hγ t))
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨s, hs⟩ := hcpt.elim_finite_subcover (fun i => (Subtype.val ⁻¹' u i : Set P.carrier))
    (fun i => huo i) hcov
  have hrange : Set.range (fun t : ℝ => (⟨γ.γ t, γ.mem t⟩ : P.carrier)) =
      (fun t : ℝ => (⟨γ.γ t, γ.mem t⟩ : P.carrier)) '' Set.Icc 0 (2 * Real.pi) := by
    apply Set.Subset.antisymm
    · rintro y ⟨t, rfl⟩
      have hmem : γ.γ t ∈ γ.γ '' Set.Ico 0 (2 * Real.pi) := by
        rw [← Work.CoreTopology.ClosedCurve.range_eq_image P γ]
        exact ⟨t, rfl⟩
      obtain ⟨t', ht', ht'eq⟩ := hmem
      exact ⟨t', Set.Ico_subset_Icc_self ht', Subtype.ext ht'eq⟩
    · rintro y ⟨t, -, rfl⟩
      exact ⟨t, rfl⟩
  have hmem : ∀ t : ℝ, γ.γ t ∈ ⋃ i ∈ s, u i := by
    intro t
    have h1 : (⟨γ.γ t, γ.mem t⟩ : P.carrier) ∈
        ⋃ i ∈ s, (Subtype.val ⁻¹' u i : Set P.carrier) := by
      apply hs
      rw [← hrange]
      exact ⟨t, rfl⟩
    obtain ⟨i, his, hiu⟩ := Set.mem_iUnion₂.mp h1
    exact Set.mem_iUnion₂.mpr ⟨i, his, hiu⟩
  by_contra hne
  have hz : Work.SurgeryInvariance.windingOf P γ ≠ (0, 0) := by
    intro h
    exact hne (by rw [h]; simp)
  have hbot := hfin s
  rw [Work.SurgeryInvariance.WindingSpan_eq_bot_iff] at hbot
  exact hbot ⟨γ, (Work.SurgeryInvariance.isEssential_iff_windingOf_ne_zero P γ).mpr hz, hmem⟩

/-- **The componentwise induction.**  If `A₀`, `K` are carrier-open and inessential with `K ⊆ A₀`,
and every connected component of `K` is carrier-open and path connected (or empty), then `A₀ ∪ K` is
inessential: each finite union of components is inessential (one component at a time, the
intersection with the accumulated union being that component, which lies in `A₀`), and a loop's
compact image is covered by finitely many components. -/
theorem windingSpan_union_components_eq_bot {P : Work.CoreTopology.ParamTorus} {A₀ K : Set R3}
    (hA₀ : Work.SurgeryInvariance.IsOpenInCarrier P A₀) (hA₀c : A₀ ⊆ P.carrier)
    (hWA₀ : Work.SurgeryInvariance.WindingSpan P A₀ = ⊥)
    (hK : Work.SurgeryInvariance.IsOpenInCarrier P K) (hKc : K ⊆ P.carrier)
    (hWK : Work.SurgeryInvariance.WindingSpan P K = ⊥)
    (hA₀K : K ⊆ A₀)
    (hopen : ∀ x : R3, Work.SurgeryInvariance.IsOpenInCarrier P (connectedComponentIn K x))
    (hpc : ∀ x ∈ K, IsPathConnected (connectedComponentIn K x)) :
    Work.SurgeryInvariance.WindingSpan P (A₀ ∪ K) = ⊥ := by
  have hcc_sub : ∀ x : R3, connectedComponentIn K x ⊆ K := fun x => connectedComponentIn_subset K x
  have hcc_carrier : ∀ x : R3, connectedComponentIn K x ⊆ P.carrier :=
    fun x y hy => hKc (hcc_sub x hy)
  have hcc_bot : ∀ x : R3, Work.SurgeryInvariance.WindingSpan P (connectedComponentIn K x) = ⊥ :=
    fun x => le_bot_iff.mp (le_trans (Work.SurgeryInvariance.WindingSpan_mono P (hcc_sub x))
      (le_of_eq hWK))
  have hopenFin : ∀ s : Finset R3,
      Work.SurgeryInvariance.IsOpenInCarrier P (⋃ x ∈ s, connectedComponentIn K x) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using isOpenInCarrier_empty P
    | insert a s ha ih => rw [Finset.set_biUnion_insert]; exact (hopen a).union ih
  have hfinite : ∀ s : Finset R3,
      Work.SurgeryInvariance.WindingSpan P (A₀ ∪ ⋃ x ∈ s, connectedComponentIn K x) = ⊥ := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hWA₀
    | insert a s ha ih =>
      rw [Finset.set_biUnion_insert]
      by_cases haK : a ∈ K
      · have hint : (A₀ ∪ ⋃ x ∈ s, connectedComponentIn K x) ∩ connectedComponentIn K a
            = connectedComponentIn K a := by
          ext y
          constructor
          · rintro ⟨-, hyB⟩
            exact hyB
          · intro hyB
            exact ⟨Or.inl (hA₀K (hcc_sub a hyB)), hyB⟩
        have hAc : (A₀ ∪ ⋃ x ∈ s, connectedComponentIn K x) ⊆ P.carrier := by
          intro y hy
          rcases hy with hyA | hyU
          · exact hA₀c hyA
          · obtain ⟨x₀, -, hx₀⟩ := Set.mem_iUnion₂.mp hyU
            exact hcc_carrier x₀ hx₀
        have hconn : ∀ x ∈ (A₀ ∪ ⋃ x ∈ s, connectedComponentIn K x) ∩ connectedComponentIn K a,
            ∀ y ∈ (A₀ ∪ ⋃ x ∈ s, connectedComponentIn K x) ∩ connectedComponentIn K a,
              JoinedIn ((A₀ ∪ ⋃ x ∈ s, connectedComponentIn K x) ∩
                connectedComponentIn K a) x y := by
          intro x hx y hy
          rw [hint] at hx hy ⊢
          exact (isPathConnected_iff.mp (hpc a haK)).2 x hx y hy
        exact windingSpan_eq_bot_of_subset_union hAc (hcc_carrier a)
          (hA₀.union (hopenFin s)) (hopen a) hconn ih (hcc_bot a)
          (by
            intro y hy
            rcases hy with hyA | hyB | hyU
            · exact Or.inl (Or.inl hyA)
            · exact Or.inr hyB
            · exact Or.inl (Or.inr hyU))
      · rw [connectedComponentIn_eq_empty haK]
        simpa using ih
  refine windingSpan_eq_bot_of_finite_unions (fun x : R3 => A₀ ∪ connectedComponentIn K x)
    (fun x => hA₀.union (hopen x)) ?_ ?_
  · intro y hy
    rcases hy with hyA | hyK
    · exact Set.mem_iUnion.mpr ⟨y, Or.inl hyA⟩
    · exact Set.mem_iUnion.mpr ⟨y, Or.inr (mem_connectedComponentIn hyK)⟩
  · intro s
    refine le_bot_iff.mp (le_trans (Work.SurgeryInvariance.WindingSpan_mono P ?_)
      (le_of_eq (hfinite s)))
    intro y hy
    obtain ⟨z, hzs, hz⟩ := Set.mem_iUnion₂.mp hy
    rcases hz with hyA | hyc
    · exact Or.inl hyA
    · exact Or.inr (Set.mem_iUnion₂.mpr ⟨z, hzs, hyc⟩)


/-- **The three-piece form of the assembly.**  If `X` is the union of a set `A₀ ∪ K` that is
inessential in the componentwise sense of `windingSpan_union_components_eq_bot` with a set `E` that
is disjoint from it and inessential, then `X` is inessential. -/
theorem windingSpan_eq_bot_of_three_pieces {P : Work.CoreTopology.ParamTorus} {X A₀ K E : Set R3}
    (hA₀ : Work.SurgeryInvariance.IsOpenInCarrier P A₀) (hA₀c : A₀ ⊆ P.carrier)
    (hWA₀ : Work.SurgeryInvariance.WindingSpan P A₀ = ⊥)
    (hK : Work.SurgeryInvariance.IsOpenInCarrier P K) (hKc : K ⊆ P.carrier)
    (hWK : Work.SurgeryInvariance.WindingSpan P K = ⊥) (hA₀K : K ⊆ A₀)
    (hopen : ∀ x : R3, Work.SurgeryInvariance.IsOpenInCarrier P (connectedComponentIn K x))
    (hpc : ∀ x ∈ K, IsPathConnected (connectedComponentIn K x))
    (hE : Work.SurgeryInvariance.IsOpenInCarrier P E)
    (hWE : Work.SurgeryInvariance.WindingSpan P E = ⊥)
    (hdisj : Disjoint E (A₀ ∪ K)) (hX : X = A₀ ∪ K ∪ E) :
    Work.SurgeryInvariance.WindingSpan P X = ⊥ := by
  have hAK : Work.SurgeryInvariance.WindingSpan P (A₀ ∪ K) = ⊥ :=
    windingSpan_union_components_eq_bot hA₀ hA₀c hWA₀ hK hKc hWK hA₀K hopen hpc
  have hsplit : Work.SurgeryInvariance.WindingSpan P ((A₀ ∪ K) ∪ E) =
      Work.SurgeryInvariance.WindingSpan P (A₀ ∪ K) ⊔ Work.SurgeryInvariance.WindingSpan P E :=
    Work.SurgeryInvariance.Span.union_eq_sup (hA₀.union hK) hE hdisj.symm
  rw [hX, hsplit, hAK, hWE]
  simp

/-- **The set algebra of the collar decomposition.**  With `A₀ = (U \ D̄) ∪ D°`,
`K = U ∩ (D₂° \ D̄)` and `E = (D₂° \ D̄) \ U`, the complement of the boundary circle in
`U ∪ D₂°` is `A₀ ∪ K ∪ E`.  (The three pieces are inessential; `E` is the part of the collar outside
the box region, and it is *not* open in the carrier, which is why it cannot be fed to the two-piece
criterion — the remaining technical step of this route.) -/
theorem halves_union_disc_sdiff_boundary_eq {P : Work.CoreTopology.ParamTorus} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} (D : Work.SurgeryInvariance.DiscRegion P)
    (D₂ : Work.SurgeryInvariance.DiscRegion P) (hD₂ : D.carrier ⊆ D₂.interior) :
    (Work.PinchLemma3.halfRegions P s c σ u ∪ D₂.interior) \ D.boundary =
      (((Work.PinchLemma3.halfRegions P s c σ u \ D.carrier) ∪ D.interior) ∪
        (Work.PinchLemma3.halfRegions P s c σ u ∩ (D₂.interior \ D.carrier))) ∪
        ((D₂.interior \ D.carrier) \ Work.PinchLemma3.halfRegions P s c σ u) := by
  have hcarrier : D.carrier = D.interior ∪ D.boundary :=
    discRegion_carrier_eq_interior_union_boundary D
  have hDsub : D.interior ⊆ D₂.interior := fun y hy => hD₂ (D.interior_subset_carrier hy)
  have hkey : ∀ y : R3, y ∈ D.carrier → y ∉ D.boundary → y ∈ D.interior := by
    intro y hc hb
    rcases (Set.ext_iff.mp hcarrier y).mp hc with h | h
    · exact h
    · exact absurd h hb
  ext y
  constructor
  · rintro ⟨hy, hb⟩
    rcases hy with hyU | hyD
    · by_cases hc : y ∈ D.carrier
      · exact Or.inl (Or.inl (Or.inr (hkey y hc hb)))
      · exact Or.inl (Or.inl (Or.inl ⟨hyU, hc⟩))
    · by_cases hc : y ∈ D.carrier
      · exact Or.inl (Or.inl (Or.inr (hkey y hc hb)))
      · by_cases hyU : y ∈ Work.PinchLemma3.halfRegions P s c σ u
        · exact Or.inl (Or.inr ⟨hyU, hyD, hc⟩)
        · exact Or.inr ⟨⟨hyD, hc⟩, hyU⟩
  · rintro ((hyA | hyK) | hyE)
    · rcases hyA with ⟨hyU, hc⟩ | hyD
      · exact ⟨Or.inl hyU, fun hb => hc ((Set.ext_iff.mp hcarrier y).mpr (Or.inr hb))⟩
      · exact ⟨Or.inr (hDsub hyD), fun hb =>
          (Set.disjoint_left.mp (discRegion_disjoint_interior_boundary D)) hyD hb⟩
    · exact ⟨Or.inl hyK.1, fun hb =>
        hyK.2.2 ((Set.ext_iff.mp hcarrier y).mpr (Or.inr hb))⟩
    · exact ⟨Or.inr hyE.1.1, fun hb =>
        hyE.1.2 ((Set.ext_iff.mp hcarrier y).mpr (Or.inr hb))⟩


/-! ## The family form of the componentwise criterion, and the sharpest reduction of `wall_core`

`windingSpan_eq_bot_of_subset_union` needs the intersection of the two pieces to be path connected;
`windingSpan_union_components_eq_bot` removes that but needs `K ⊆ A₀`, which is useless when the
second family is *not* contained in the first.  The tool below is the form the reduction of
`wall_core` needs: a pairwise disjoint family `C i` of carrier-open inessential sets, each meeting
`A₀` in a set which is path connected (or empty).  Its proof is the same induction as
`windingSpan_union_components_eq_bot`, with the disjointness of the family replacing `K ⊆ A₀` in the
computation of the intersection.  Note that the `C i` need *not* be path connected themselves. -/

/-- The union of a finite family of carrier-open sets is carrier-open. -/
theorem isOpenInCarrier_biUnion {P : Work.CoreTopology.ParamTorus} {ι : Type*}
    (s : Finset ι) {C : ι → Set R3}
    (hC : ∀ i, Work.SurgeryInvariance.IsOpenInCarrier P (C i)) :
    Work.SurgeryInvariance.IsOpenInCarrier P (⋃ i ∈ s, C i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isOpenInCarrier_empty P
  | insert a s ha ih => rw [Finset.set_biUnion_insert]; exact (hC a).union ih

/-- **The family form of the componentwise criterion.**  Let `A₀` be carrier-open and inessential and
let `C : ι → Set R3` be a family of *pairwise disjoint* carrier-open inessential sets, each meeting
`A₀` in a path connected (or empty) set.  Then every `X ⊆ A₀ ∪ ⋃ i, C i` is inessential.  (Taking
`ι` a two-element type recovers `windingSpan_eq_bot_of_subset_union`.) -/
theorem windingSpan_eq_bot_of_family_of_connected {P : Work.CoreTopology.ParamTorus} {ι : Type*}
    {X A₀ : Set R3} (C : ι → Set R3)
    (hA₀c : A₀ ⊆ P.carrier) (hA₀ : Work.SurgeryInvariance.IsOpenInCarrier P A₀)
    (hWA₀ : Work.SurgeryInvariance.WindingSpan P A₀ = ⊥)
    (hCc : ∀ i, C i ⊆ P.carrier) (hC : ∀ i, Work.SurgeryInvariance.IsOpenInCarrier P (C i))
    (hWC : ∀ i, Work.SurgeryInvariance.WindingSpan P (C i) = ⊥)
    (hdisj : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hinter : ∀ i, IsPathConnected (A₀ ∩ C i) ∨ (A₀ ∩ C i) = ∅)
    (hX : X ⊆ A₀ ∪ ⋃ i, C i) :
    Work.SurgeryInvariance.WindingSpan P X = ⊥ := by
  classical
  have hpcinter : ∀ i, ∀ x ∈ A₀ ∩ C i, ∀ y ∈ A₀ ∩ C i, JoinedIn (A₀ ∩ C i) x y := by
    intro i
    rcases hinter i with h | h
    · exact joinedIn_of_isPathConnected h
    · intro x hx
      rw [h] at hx
      exact absurd hx (by simp)
  have hstep : ∀ (s : Finset ι),
      Work.SurgeryInvariance.WindingSpan P (A₀ ∪ ⋃ i ∈ s, C i) = ⊥ := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hWA₀
    | insert a s ha ih =>
        rw [Finset.set_biUnion_insert]
        have hunion : A₀ ∪ (C a ∪ ⋃ i ∈ s, C i) =
            (A₀ ∪ ⋃ i ∈ s, C i) ∪ C a := by
          ext y; simp only [Set.mem_union]; tauto
        rw [hunion]
        have hkey : (A₀ ∪ ⋃ i ∈ s, C i) ∩ C a = A₀ ∩ C a := by
          ext y
          constructor
          · rintro ⟨hy, hyC⟩
            rcases hy with hyA | hyU
            · exact ⟨hyA, hyC⟩
            · obtain ⟨i, his, hi⟩ := Set.mem_iUnion₂.mp hyU
              exact absurd hyC (Set.disjoint_left.mp (hdisj i a (fun h => ha (h ▸ his))) hi)
          · rintro ⟨hyA, hyC⟩
            exact ⟨Or.inl hyA, hyC⟩
        have hAcar : (A₀ ∪ ⋃ i ∈ s, C i) ⊆ P.carrier := by
          intro y hy
          rcases hy with hyA | hyU
          · exact hA₀c hyA
          · obtain ⟨i, -, hi⟩ := Set.mem_iUnion₂.mp hyU
            exact hCc i hi
        have hAopen : Work.SurgeryInvariance.IsOpenInCarrier P (A₀ ∪ ⋃ i ∈ s, C i) :=
          Work.SurgeryInvariance.isOpenInCarrier_union P hA₀ (isOpenInCarrier_biUnion s hC)
        refine windingSpan_eq_bot_of_subset_union hAcar (hCc a) hAopen (hC a) ?_ ih (hWC a)
          subset_rfl
        intro x hx y hy
        rw [hkey] at hx hy ⊢
        exact hpcinter a x hx y hy
  by_cases hι : Nonempty ι
  · obtain ⟨i₀⟩ := hι
    refine windingSpan_eq_bot_of_finite_unions (fun i : ι => A₀ ∪ C i)
      (fun i => Work.SurgeryInvariance.isOpenInCarrier_union P hA₀ (hC i)) ?_ ?_
    · intro y hy
      rcases hX hy with hyA | hyU
      · exact Set.mem_iUnion.mpr ⟨i₀, Or.inl hyA⟩
      · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hyU
        exact Set.mem_iUnion.mpr ⟨i, Or.inr hi⟩
    · intro s
      by_cases hs : s = ∅
      · subst hs
        simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty]
        exact windingSpan_empty P
      · obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hs
        have hbi : (⋃ i ∈ s, (A₀ ∪ C i)) = A₀ ∪ ⋃ i ∈ s, C i := by
          ext y
          simp only [Set.mem_iUnion, Set.mem_union]
          constructor
          · rintro ⟨i, his, h | h⟩
            · exact Or.inl h
            · exact Or.inr ⟨i, his, h⟩
          · rintro (h | ⟨i, his, h⟩)
            · exact ⟨a, ha, Or.inl h⟩
            · exact ⟨i, his, Or.inr h⟩
        rw [hbi]
        exact hstep s
  · have hnil : (⋃ i, C i) = ∅ := by
      rw [Set.iUnion_eq_empty]
      intro i
      exact (hι ⟨i⟩).elim
    have hsub : X ⊆ A₀ := by
      intro y hy
      have := hX hy
      rwa [hnil, Set.union_empty] at this
    exact le_bot_iff.mp (le_trans (Work.SurgeryInvariance.WindingSpan_mono P hsub)
      (le_of_eq hWA₀))

/-- **The reduction of `wall_core` to a property of the disc, in family form.**  Let `D` be an
embedded disc whose interior carries the slice, and let `C : ι → Set R3` be a pairwise disjoint
family of carrier-open inessential sets covering the two half-regions.  If each `C i` meets the
disc's interior in a path connected (or empty) set, then the box region is inessential.

`hCov` and `hinter` are *geometric* statements about where the disc sits inside the surface; the
content is that a half-region may be cut by the disc into several pieces as long as each piece lies
in a *different* connected piece of the half-region. -/
theorem windingSpan_boxRegion_eq_bot_of_disc_family {P : Work.CoreTopology.ParamTorus} {s : ℝ}
    {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} (D : Work.SurgeryInvariance.DiscRegion P)
    (hslice : Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ D.interior)
    {ι : Type*} (C : ι → Set R3)
    (hCov : Work.PinchLemma3.halfRegions P s c σ u ⊆ ⋃ i, C i)
    (hCc : ∀ i, C i ⊆ P.carrier) (hCop : ∀ i, Work.SurgeryInvariance.IsOpenInCarrier P (C i))
    (hCW : ∀ i, Work.SurgeryInvariance.WindingSpan P (C i) = ⊥)
    (hdisj : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hinter : ∀ i, IsPathConnected (D.interior ∩ C i) ∨ (D.interior ∩ C i) = ∅) :
    Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) = ⊥ := by
  refine windingSpan_eq_bot_of_family_of_connected C D.interior_subset_surface D.open_interior'
    (windingSpan_eq_bot_of_subset_discRegion D D.interior_subset_carrier) hCc hCop hCW
    hdisj hinter ?_
  intro y hy
  rw [Work.BoxShrink.Core.boxRegion_eq_union P s c σ u] at hy
  rcases hy with (hy | hy) | hy
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hCov (Or.inl hy))
    exact Or.inr (Set.mem_iUnion.mpr ⟨i, hi⟩)
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hCov (Or.inr hy))
    exact Or.inr (Set.mem_iUnion.mpr ⟨i, hi⟩)
  · exact Or.inl (hslice hy)

/-- **`wall_core` from the family form of the disc reduction.** -/
theorem wall_core_of_disc_family (P : Work.CoreTopology.ParamTorus) (s : ℝ)
    (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (D : Work.SurgeryInvariance.DiscRegion P)
    (_hD : D.carrier ⊆ Work.PinchLemma3.closedBoxRegion P s c σ)
    (hslice : Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ D.interior)
    (_hT : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Pinch.planeTrace P c σ u) = ⊥)
    (_h0 : Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) = ⊥)
    {ι : Type*} (C : ι → Set R3)
    (hCov : Work.PinchLemma3.halfRegions P s c σ u ⊆ ⋃ i, C i)
    (hCc : ∀ i, C i ⊆ P.carrier) (hCop : ∀ i, Work.SurgeryInvariance.IsOpenInCarrier P (C i))
    (hCW : ∀ i, Work.SurgeryInvariance.WindingSpan P (C i) = ⊥)
    (hdisj : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hinter : ∀ i, IsPathConnected (D.interior ∩ C i) ∨ (D.interior ∩ C i) = ∅) :
    ∃ v : ℚ × ℚ, v ≠ 0 ∧
      Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ⊓
        Submodule.span ℚ ({v} : Set (ℚ × ℚ)) ≤
      Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) :=
  wall_core_of_ne_top (by
    rw [windingSpan_boxRegion_eq_bot_of_disc_family D hslice C hCov hCc hCop hCW hdisj hinter]
    exact bot_ne_top)


/-! ## The slice is an *open* part of the trace of the plane

The trace `Γ = F ∩ Π` of the cutting plane meets the *open* box in the slice `Σ = Ω ∩ Π`, and the
fact that `Submission.PBox` is a product of *open* intervals has a structural consequence which the
analysis of the pinch uses constantly: **`Σ` is open in `Γ`**, i.e. the slice is a union of *open*
arcs of the components of the trace.  Its relative complement in the trace -- the sphere trace
`S = F ∩ ∂B` -- is closed, and every limit point of the slice which is not itself in the slice lies
on the boundary sphere `{boxNorm = s}` of the box: these are the *gates* at which the arcs of the
slice meet `S`.

This is the formalised form of the description of the slice used throughout `NOTES_wall_core.md`
(§9.5, §12): the slice arcs run from gate to gate. -/

/-- The slice is the trace of the plane intersected with the *open* box. -/
theorem sliceRegion_eq_planeTrace_inter_PBox (P : Work.CoreTopology.ParamTorus) (s : ℝ)
    (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Work.BoxShrink.Core.sliceRegion P s c σ u =
      Work.BoxShrink.Pinch.planeTrace P c σ u ∩ Submission.PBox s c σ := by
  ext y
  simp only [Work.BoxShrink.Core.sliceRegion, Work.BoxShrink.Pinch.planeTrace, Set.mem_inter_iff,
    Set.mem_ofPred_eq]
  tauto

/-- The slice is the trace of the plane intersected with the box region. -/
theorem sliceRegion_eq_planeTrace_inter_boxRegion (P : Work.CoreTopology.ParamTorus) (s : ℝ)
    (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Work.BoxShrink.Core.sliceRegion P s c σ u =
      Work.BoxShrink.Pinch.planeTrace P c σ u ∩ Work.BoxShrink.Core.boxRegion P s c σ := by
  ext y
  simp only [Work.BoxShrink.Core.sliceRegion, Work.BoxShrink.Pinch.planeTrace,
    Work.BoxShrink.Core.boxRegion, Set.mem_inter_iff, Set.mem_ofPred_eq]
  tauto

/-- The preimage of the trace under the inclusion of the trace is everything. -/
theorem preimage_planeTrace_eq_univ (P : Work.CoreTopology.ParamTorus) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    (Subtype.val ⁻¹' (Work.BoxShrink.Pinch.planeTrace P c σ u : Set R3) :
      Set ↥(Work.BoxShrink.Pinch.planeTrace P c σ u)) = Set.univ := by
  ext q
  exact ⟨fun _ => trivial, fun _ => q.2⟩

/-- The preimage of the slice under the inclusion of the trace is the preimage of the box. -/
theorem preimage_sliceRegion_eq_preimage_PBox (P : Work.CoreTopology.ParamTorus) (s : ℝ)
    (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    (Subtype.val ⁻¹' (Work.BoxShrink.Core.sliceRegion P s c σ u : Set R3) :
        Set ↥(Work.BoxShrink.Pinch.planeTrace P c σ u)) =
      Subtype.val ⁻¹' (Submission.PBox s c σ : Set R3) := by
  ext q
  rw [sliceRegion_eq_planeTrace_inter_PBox]
  exact ⟨fun h => h.2, fun h => ⟨q.2, h⟩⟩

/-- **The slice is open in the trace of the plane.**  Its points are those of the trace that lie in
the *open* box, so the slice is a union of open arcs of the trace. -/
theorem isOpen_sliceRegion_in_planeTrace (P : Work.CoreTopology.ParamTorus) (s : ℝ)
    (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    IsOpen (Subtype.val ⁻¹' (Work.BoxShrink.Core.sliceRegion P s c σ u :
      Set R3) : Set ↥(Work.BoxShrink.Pinch.planeTrace P c σ u)) := by
  rw [preimage_sliceRegion_eq_preimage_PBox]
  exact (Work.Topology.SphereSlicing.isOpen_PBox s c σ).preimage continuous_subtype_val

/-- The closure of the open box is contained in the closed box. -/
theorem closure_PBox_subset_closedBox (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) :
    closure (Submission.PBox s c σ) ⊆ {y : R3 | Submission.boxNorm c σ y ≤ s} := by
  intro y hy
  have hi : ∀ i : Fin 3, |y (σ i) - c (σ i)| ≤ Submission.boxSide i * s := by
    intro i
    have h1 : closure (Submission.PBox s c σ) ⊆
        closure {z : R3 | |z (σ i) - c (σ i)| < Submission.boxSide i * s} :=
      closure_mono (fun z hz => (Submission.mem_PBox.mp hz) i)
    have h2 : closure {z : R3 | |z (σ i) - c (σ i)| < Submission.boxSide i * s} ⊆
        {z : R3 | |z (σ i) - c (σ i)| ≤ Submission.boxSide i * s} := by
      refine closure_lt_subset_le (f := fun z : R3 => |z (σ i) - c (σ i)|)
        (g := fun _ : R3 => Submission.boxSide i * s) ?_ continuous_const
      fun_prop
    exact h2 (h1 hy)
  show max (max (|y (σ 0) - c (σ 0)| / Submission.boxSide 0)
      (|y (σ 1) - c (σ 1)| / Submission.boxSide 1))
      (|y (σ 2) - c (σ 2)| / Submission.boxSide 2) ≤ s
  rw [max_le_iff, max_le_iff, div_le_iff₀ (Submission.boxSide_pos 0),
    div_le_iff₀ (Submission.boxSide_pos 1), div_le_iff₀ (Submission.boxSide_pos 2)]
  exact ⟨⟨by simpa [mul_comm] using hi 0, by simpa [mul_comm] using hi 1⟩,
    by simpa [mul_comm] using hi 2⟩

/-- **The limit points of the slice in the trace lie in the closed box.** -/
theorem closure_sliceRegion_subset_closedBoxRegion (P : Work.CoreTopology.ParamTorus) (s : ℝ)
    (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    closure (Subtype.val ⁻¹' (Work.BoxShrink.Core.sliceRegion P s c σ u : Set R3) :
        Set ↥(Work.BoxShrink.Pinch.planeTrace P c σ u)) ⊆
      Subtype.val ⁻¹' (Work.PinchLemma3.closedBoxRegion P s c σ : Set R3) := by
  intro q hq
  rw [preimage_sliceRegion_eq_preimage_PBox] at hq
  have hcl : (q : R3) ∈ closure (Submission.PBox s c σ) :=
    (continuous_subtype_val).closure_preimage_subset (Submission.PBox s c σ) hq
  exact ⟨(Work.BoxShrink.Pinch.mem_planeTrace.mp q.2).1,
    closure_PBox_subset_closedBox s c σ hcl⟩

/-- **A limit point of the slice which is not in the slice lies on the box sphere.**  The slice is
open in the trace and its closure in the trace is contained in the closed box, so a limit point of
the slice outside the slice has box norm exactly `s`: it is a *gate* of the slice, on the boundary
sphere of the box. -/
theorem mem_sphereSet_of_mem_closure_sliceRegion_not_mem (P : Work.CoreTopology.ParamTorus)
    (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    {q : ↥(Work.BoxShrink.Pinch.planeTrace P c σ u)}
    (hq : q ∈ closure (Subtype.val ⁻¹' (Work.BoxShrink.Core.sliceRegion P s c σ u :
      Set R3) : Set ↥(Work.BoxShrink.Pinch.planeTrace P c σ u)))
    (hnot : (q : R3) ∉ Work.BoxShrink.Core.sliceRegion P s c σ u) :
    (q : R3) ∈ Work.BoxShrink.Core.sphereSet c σ s := by
  have hcl := closure_sliceRegion_subset_closedBoxRegion P s c σ u hq
  have hcar : (q : R3) ∈ P.carrier := (Work.BoxShrink.Pinch.mem_planeTrace.mp q.2).1
  have hle : Submission.boxNorm c σ (q : R3) ≤ s := hcl.2
  have hge : s ≤ Submission.boxNorm c σ (q : R3) := by
    by_contra hlt
    have hlt' : Submission.boxNorm c σ (q : R3) < s := not_le.mp hlt
    exact hnot (by
      rw [sliceRegion_eq_planeTrace_inter_boxRegion]
      exact ⟨q.2, hcar, (Submission.mem_PBox_iff s c σ _).mpr hlt'⟩)
  show Submission.boxNorm c σ (q : R3) = s
  exact le_antisymm hle hge

/-- The slice is contained in the interior of the disc and in the trace. -/
theorem sliceRegion_subset_interior_inter_planeTrace (P : Work.CoreTopology.ParamTorus) (s : ℝ)
    (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) (D : Work.SurgeryInvariance.DiscRegion P)
    (hslice : Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ D.interior) :
    Work.BoxShrink.Core.sliceRegion P s c σ u ⊆
      D.interior ∩ Work.BoxShrink.Pinch.planeTrace P c σ u :=
  fun y hy => ⟨hslice hy, by
    rw [sliceRegion_eq_planeTrace_inter_PBox] at hy
    exact hy.1⟩



/-! ## `(★)` in the *grounded* form, and `wall_core` from it

The lemma `windingSpan_union_le_sup_of_grounded_inter`
(`Submission.Work.PinchLemma3.ClosedDiscA.windingSpan_union_le_sup_of_grounded_inter`) gives the
two-piece theorem for a pair of open inessential regions whose intersection is *grounded* in the
first: every path of `A` between two points of `A ∩ B` must be realisable inside `A ∩ B`.

Applied to `A = halfRegions` and `B = D.interior` — the second a genuine disc, hence inessential
and path connected — the groundedness condition becomes the following statement about the disc and
the slice, which is exactly the sharpest gap of these notes (`(★)`, §12.2):

> no path of the two half-regions joins two points of the disc's interior that cannot already be
> joined inside the disc's interior.

Since `Ω ⊆ halfRegions ∪ D.interior` (every point of the box region is either off the cutting plane
or in the slice, and the slice lies in the disc by `hslice`), this gives the *strong* conclusion
`W(Ω) = ⊥` and hence the conclusion of `wall_core` — with no `hT`, and without the stub. -/

/-- The interior of an embedded disc of the carrier is path connected: it is the image of the open
unit disc under the embedding. -/
theorem isPathConnected_discRegion_interior {P : Work.CoreTopology.ParamTorus}
    (D : Work.SurgeryInvariance.DiscRegion P) :
    IsPathConnected D.interior := by
  have hpc : IsPathConnected {z : Metric.closedBall (0 : ℂ) 1 | ‖(z : ℂ)‖ < 1} := by
    have h := IsPathConnected.preimage_coe (X := ℂ) (U := Metric.closedBall (0 : ℂ) 1)
      (W := Metric.ball (0 : ℂ) 1) (Metric.isPathConnected_ball (by norm_num))
      Metric.ball_subset_closedBall
    simpa [Set.preimage, Metric.mem_ball] using h
  have himg : IsPathConnected
      (D.e '' {z : Metric.closedBall (0 : ℂ) 1 | ‖(z : ℂ)‖ < 1}) :=
    hpc.image D.e.continuous
  rw [Work.SurgeryInvariance.DiscRegion.interior_def]
  exact himg

/-- The two half-regions lie on the surface. -/
theorem halfRegions_subset_carrier (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) : halfRegions P s c σ u ⊆ P.carrier := by
  rintro y (hy | hy)
  · exact (Work.BoxShrink.Core.mem_upperRegion.mp hy).1
  · exact (Work.BoxShrink.Core.mem_lowerRegion.mp hy).1

/-- **The box region is covered by the two half-regions and the disc's interior.**  A point of the
box region is either off the cutting plane — hence in one of the half-regions — or in the slice,
which `hslice` puts inside the disc. -/
theorem boxRegion_subset_halfRegions_union_disc_interior (P : Work.CoreTopology.ParamTorus)
    (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (D : Work.SurgeryInvariance.DiscRegion P)
    (hslice : Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ D.interior) :
    Work.BoxShrink.Core.boxRegion P s c σ ⊆ halfRegions P s c σ u ∪ D.interior := by
  intro y hy
  rw [Work.BoxShrink.Core.boxRegion_eq_union P s c σ u] at hy
  rcases hy with (hy | hy) | hy
  · exact Or.inl (Or.inl hy)
  · exact Or.inl (Or.inr hy)
  · exact Or.inr (hslice hy)

/-- **(★), in the grounded form.**  Every path of the two half-regions between two points of the
disc's interior can be realised inside the disc's interior. -/
def DiscInteriorGrounded (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) (D : Work.SurgeryInvariance.DiscRegion P) : Prop :=
  ∀ x ∈ halfRegions P s c σ u ∩ D.interior, ∀ y ∈ halfRegions P s c σ u ∩ D.interior,
    JoinedIn (halfRegions P s c σ u) x y → JoinedIn (halfRegions P s c σ u ∩ D.interior) x y

/-- **The strong form of `wall_core` from `(★)`**: if the disc's interior is grounded in the
half-regions and carries the slice, then the box region carries no winding at all. -/
theorem windingSpan_boxRegion_eq_bot_of_discInteriorGrounded (P : Work.CoreTopology.ParamTorus)
    (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (D : Work.SurgeryInvariance.DiscRegion P)
    (hground : DiscInteriorGrounded P s c σ u D)
    (hslice : Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ D.interior)
    (h0 : Work.SurgeryInvariance.WindingSpan P (halfRegions P s c σ u) = ⊥) :
    Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) = ⊥ := by
  have hle : Work.SurgeryInvariance.WindingSpan P
      (halfRegions P s c σ u ∪ D.interior) ≤ ⊥ := by
    have h := windingSpan_union_le_sup_of_grounded_inter
      (A := halfRegions P s c σ u) (B := D.interior)
      (halfRegions_subset_carrier P s c σ u) (D.interior_subset_surface)
      (isOpenInCarrier_halfRegions P s c σ u) D.open_interior'
      (isPathConnected_discRegion_interior D)
      (by
        intro x hx y hy hxy
        exact hground x hx y hy hxy)
      h0 (Work.SurgeryInvariance.DiscRegion.windingSpan_interior_eq_bot D)
    rwa [h0, bot_sup_eq, Work.SurgeryInvariance.DiscRegion.windingSpan_interior_eq_bot D] at h
  have hmono : Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.boxRegion P s c σ) ≤
      Work.SurgeryInvariance.WindingSpan P (halfRegions P s c σ u ∪ D.interior) :=
    Work.SurgeryInvariance.WindingSpan_mono (P := P)
      (boxRegion_subset_halfRegions_union_disc_interior P s c σ u D hslice)
  exact le_bot_iff.mp (hmono.trans hle)

/-- **`wall_core` from `(★)`**, in the grounded form, with the *strong* conclusion `W(Ω) = ⊥`. -/
theorem wall_core_of_discInteriorGrounded (P : Work.CoreTopology.ParamTorus) (s : ℝ)
    (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (D : Work.SurgeryInvariance.DiscRegion P)
    (hground : DiscInteriorGrounded P s c σ u D)
    (hslice : Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ D.interior)
    (h0 : Work.SurgeryInvariance.WindingSpan P (halfRegions P s c σ u) = ⊥) :
    ∃ v : ℚ × ℚ, v ≠ 0 ∧
      Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ⊓
        Submodule.span ℚ ({v} : Set (ℚ × ℚ)) ≤
      Work.SurgeryInvariance.WindingSpan P (halfRegions P s c σ u) :=
  wall_core_of_ne_top (by
    rw [windingSpan_boxRegion_eq_bot_of_discInteriorGrounded P s c σ u D hground hslice h0]
    exact bot_ne_top)





/-! ## The third route: a class of a *disjoint* curve is orthogonal to the box region

`Work.PinchLemma3.ClosedDiscA.winding_dependent_of_disjoint_curves` is the classical fact that two
disjoint closed curves of an embedded torus have proportional winding vectors (their algebraic
intersection number vanishes, and the intersection form of `H₁(T²;ℚ) = ℚ²` is symplectic, so a
nonzero vector has a one-dimensional orthogonal complement).

Applied with `X = boxRegion` this gives the first reduction of the trace-inessential residual which
uses neither `hT` nor `h0`: **if the boundary sphere of the box, or the caps outside it, carry an
essential closed curve, then the box region is not full.**  Indeed such a curve is disjoint from the
box region, so every class realised in the box region is a multiple of its class.

So the residual only has to be proved at configurations in which the *sphere trace* and the *caps*
are inessential as well. -/

/-- A nonzero vector of `ℚ × ℚ` spans every vector with vanishing determinant. -/
theorem mem_span_singleton_of_det_eq_zero {a b : ℚ × ℚ} (h : a.1 * b.2 = a.2 * b.1) (h2 : b ≠ 0) :
    a ∈ Submodule.span ℚ ({b} : Set (ℚ × ℚ)) := by
  rw [Submodule.mem_span_singleton]
  rcases eq_or_ne b.1 0 with hb | hb
  · have hb2 : b.2 ≠ 0 := fun h0 => h2 (Prod.ext hb h0)
    have ha : a.1 = 0 := by
      have hh := h
      rw [hb, mul_zero] at hh
      exact (mul_eq_zero.mp hh).resolve_right hb2
    refine ⟨a.2 / b.2, ?_⟩
    ext <;> simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    · rw [ha, hb, mul_zero]
    · field_simp
  · refine ⟨a.1 / b.1, ?_⟩
    ext <;> simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    · field_simp
    · field_simp
      nlinarith [h]

/-- **A region admitting the class of a disjoint essential curve is not full.**  If `δ` is a closed
curve of the torus avoiding `X` and carrying a nonzero winding, then every closed curve of `X` has a
winding vector proportional to that of `δ`, so `W(X)` lies in a line. -/
theorem ne_top_of_disjoint_essential (P : Work.CoreTopology.ParamTorus) {X : Set R3}
    (hX : X ⊆ P.carrier) {δ : Work.CoreTopology.ClosedCurve P}
    (hdis : ∀ t : ℝ, δ.γ t ∉ X)
    (hδ : Work.SurgeryInvariance.windingOf P δ ≠ (0, 0)) :
    Work.SurgeryInvariance.WindingSpan P X ≠ ⊤ := by
  set w : ℚ × ℚ := ((((Work.SurgeryInvariance.windingOf P δ).1 : ℤ) : ℚ),
      (((Work.SurgeryInvariance.windingOf P δ).2 : ℤ) : ℚ)) with hw
  have hwne : w ≠ 0 := by
    rw [hw]
    intro h0
    exact hδ (Work.SurgeryInvariance.intPair_cast_eq_zero_iff _ |>.mp h0)
  have hle : Work.SurgeryInvariance.WindingSpan P X ≤
      Submodule.span ℚ ({w} : Set (ℚ × ℚ)) := by
    rw [Work.SurgeryInvariance.WindingSpan, Submodule.span_le]
    rintro v ⟨γ, hγ, rfl⟩
    have hdet : (((Work.SurgeryInvariance.windingOf P γ).1 : ℤ) : ℚ)
          * (((Work.SurgeryInvariance.windingOf P δ).2 : ℤ) : ℚ)
        = (((Work.SurgeryInvariance.windingOf P γ).2 : ℤ) : ℚ)
          * (((Work.SurgeryInvariance.windingOf P δ).1 : ℤ) : ℚ) := by
      have h := winding_dependent_of_disjoint_curves (P := P) (γ := γ) (δ := δ)
        (fun s t hcon => hdis t (hcon ▸ hγ s))
      exact_mod_cast h
    refine mem_span_singleton_of_det_eq_zero (b := w) ?_ hwne
    rw [hw]
    exact hdet
  intro htop
  have hsp : Submodule.span ℚ ({w} : Set (ℚ × ℚ)) = ⊤ := top_le_iff.mp (htop ▸ hle)
  have h1 : Module.finrank ℚ ↥(Submodule.span ℚ ({w} : Set (ℚ × ℚ))) = 1 :=
    finrank_span_singleton hwne
  rw [hsp, finrank_top, Module.finrank_prod, Module.finrank_self] at h1
  norm_num at h1

/-- **The trace of the box sphere carrying an essential curve makes the box region non-full.** -/
theorem ne_top_of_essential_sphereTrace (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) {δ : Work.CoreTopology.ClosedCurve P}
    (hδr : ∀ t : ℝ, δ.γ t ∈ Work.BoxShrink.Core.sphereSet c σ s)
    (hδ : Work.SurgeryInvariance.windingOf P δ ≠ (0, 0)) :
    Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ≠ ⊤ :=
  ne_top_of_disjoint_essential P (fun _ hy => hy.1) (fun t => by
    intro hcon
    have hlt : Submission.boxNorm c σ (δ.γ t) < s :=
      Submission.mem_PBox_iff s c σ _ |>.mp hcon.2
    have heq : Submission.boxNorm c σ (δ.γ t) = s :=
      Work.BoxShrink.Core.mem_sphereSet.mp (hδr t)
    exact absurd heq (ne_of_lt hlt)) hδ

/-- **The caps outside the closed box carrying an essential curve make the box region non-full.** -/
theorem ne_top_of_essential_caps (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) {δ : Work.CoreTopology.ClosedCurve P}
    (hδr : ∀ t : ℝ, δ.γ t ∉ Work.PinchLemma3.closedBoxRegion P s c σ)
    (hδ : Work.SurgeryInvariance.windingOf P δ ≠ (0, 0)) :
    Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ≠ ⊤ :=
  ne_top_of_disjoint_essential P (fun _ hy => hy.1) (fun t => by
    intro hcon
    exact hδr t (boxRegion_subset_closedBoxRegion P s c σ hcon)) hδ



/-! ## The seam picture: the free arcs of the boundary circle lie in the halves

The disc `D` of the hypotheses is a *sub-disc of the surface* (`D.carrier ⊆ P.carrier`, its
interior is open in the carrier) whose closure lies in the closed box and whose interior contains the
slice.  Its boundary circle `∂D` is therefore split by the box into two kinds of arcs:

* the **gate arcs** `∂D ∩ ∂Box`, the part of `∂D` on the boundary sphere of the box, and
* the **free arcs** `∂D ∩ Ω`, the part of `∂D` inside the open box region.

The elementary observation of this section is that *every free arc already lies in the two
half-regions*: a point of `Ω ∩ ∂D` is either off the cutting plane — hence in `Ω \ Σ = halves` — or
in the slice `Σ ⊆ D°`, which is impossible because `∂D` and `D°` are disjoint.  Consequently

  `Ω = (Ω ∩ D°) ∪ (Ω \ D̄) ∪ (Ω ∩ ∂D)`    (the **seam decomposition**),

with both `Ω \ D̄` and the free arcs `Ω ∩ ∂D` contained in `halves`.  In particular

  `W(Ω) ≤ W(halves ∪ D̄)`  and  `W(Ω) ≤ W(halves ∪ D°)`,

the second being the form in which the two-piece theorems of this directory consume the disc (`D°`
is carrier-open, inessential and path connected).  The seam decomposition is the sharpest expression
of the residual available from the disc hypothesis alone: the *only* part of `Ω` that is neither in
`halves` nor in the disc is the slice, and the slice is inessential (`hT` alone gives `W(Σ) = ⊥`,
by monotonicity, since `Σ = Γ ∩ Ω ⊆ Γ`). -/

/-- **The seam decomposition of the box region.**  The box region is the union of its part inside the
open disc, its part outside the closed disc, and the free arcs of the boundary circle. -/
theorem boxRegion_eq_interior_union_sdiff_union_boundary {P : Work.CoreTopology.ParamTorus} {s : ℝ}
    {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} (D : Work.SurgeryInvariance.DiscRegion P) :
    Work.BoxShrink.Core.boxRegion P s c σ =
      (Work.BoxShrink.Core.boxRegion P s c σ ∩ D.interior) ∪
        (Work.BoxShrink.Core.boxRegion P s c σ \ D.carrier) ∪
          (Work.BoxShrink.Core.boxRegion P s c σ ∩ D.boundary) := by
  have hdec := discRegion_carrier_eq_interior_union_boundary D
  ext x
  constructor
  · intro hx
    by_cases hc : x ∈ D.carrier
    · rcases (show x ∈ D.interior ∪ D.boundary from hdec ▸ hc) with h | h
      · exact Or.inl (Or.inl ⟨hx, h⟩)
      · exact Or.inr ⟨hx, h⟩
    · exact Or.inl (Or.inr ⟨hx, hc⟩)
  · rintro ((⟨hx, -⟩ | ⟨hx, -⟩) | ⟨hx, -⟩) <;> exact hx

/-- **The free arcs of the boundary circle lie in the halves.**  A point of the box region on `∂D` is
not in the slice (whose points are interior to the disc), hence in `Ω \ Σ = halves`. -/
theorem boundary_inter_boxRegion_subset_halfRegions {P : Work.CoreTopology.ParamTorus} {s : ℝ}
    {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} (D : Work.SurgeryInvariance.DiscRegion P)
    (hslice : Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ D.interior) :
    Work.BoxShrink.Core.boxRegion P s c σ ∩ D.boundary ⊆ halfRegions P s c σ u := by
  rintro x ⟨hx, hxb⟩
  rw [← boxRegion_sdiff_sliceRegion P s c σ u]
  exact ⟨hx, fun hs =>
    (Set.disjoint_left.mp (discRegion_disjoint_interior_boundary D)) (hslice hs) hxb⟩

/-- **The box region is covered by the half-regions and the closed disc.** -/
theorem boxRegion_subset_halfRegions_union_discRegion {P : Work.CoreTopology.ParamTorus} {s : ℝ}
    {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} (D : Work.SurgeryInvariance.DiscRegion P)
    (hslice : Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ D.interior) :
    Work.BoxShrink.Core.boxRegion P s c σ ⊆ halfRegions P s c σ u ∪ D.carrier := by
  rintro x hx
  by_cases hs : x ∈ Work.BoxShrink.Core.sliceRegion P s c σ u
  · exact Or.inr (D.interior_subset_carrier (hslice hs))
  · exact Or.inl ((boxRegion_sdiff_sliceRegion P s c σ u).symm ▸ ⟨hx, hs⟩)

/-- **`W(Ω) ≤ W(halves ∪ D̄)`**: the winding of the box region is carried by the two half-regions and
the closed disc. -/
theorem windingSpan_boxRegion_le_halves_union_discRegion {P : Work.CoreTopology.ParamTorus} {s : ℝ}
    {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} (D : Work.SurgeryInvariance.DiscRegion P)
    (hslice : Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ D.interior) :
    Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ≤
      Work.SurgeryInvariance.WindingSpan P (halfRegions P s c σ u ∪ D.carrier) :=
  Work.SurgeryInvariance.WindingSpan_mono P
    (boxRegion_subset_halfRegions_union_discRegion D hslice)

/-- **`W(Ω) ≤ W(halves ∪ D°)`**: the same with the *open* disc, the form the two-piece theorems of
this directory consume (`D.interior` is carrier-open, inessential and path connected). -/
theorem windingSpan_boxRegion_le_halves_union_discInterior {P : Work.CoreTopology.ParamTorus}
    {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} (D : Work.SurgeryInvariance.DiscRegion P)
    (hslice : Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ D.interior) :
    Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ≤
      Work.SurgeryInvariance.WindingSpan P (halfRegions P s c σ u ∪ D.interior) :=
  Work.SurgeryInvariance.WindingSpan_mono P
    (boxRegion_subset_halfRegions_union_disc_interior P s c σ u D hslice)

/-- **The slice is inessential as soon as the trace of the cutting plane is.**  The slice is the part
of the trace inside the box (`Σ = Γ ∩ Ω`), so `W(Σ) ≤ W(Γ)`. -/
theorem windingSpan_sliceRegion_eq_bot_of_planeTrace {P : Work.CoreTopology.ParamTorus} {s : ℝ}
    {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hT : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Pinch.planeTrace P c σ u) = ⊥) :
    Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.sliceRegion P s c σ u) = ⊥ :=
  le_bot_iff.mp (le_trans (Work.SurgeryInvariance.WindingSpan_mono P (by
    rw [sliceRegion_eq_planeTrace_inter_boxRegion P s c σ u]
    exact Set.inter_subset_left)) (le_of_eq hT))

/-- **The closure of the slice lies in the closed disc.**  The slice is contained in `D.interior`
(`hslice`) and the carrier of a disc region is closed. -/
theorem closure_sliceRegion_subset_discRegion_carrier {P : Work.CoreTopology.ParamTorus} {s : ℝ}
    {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} (D : Work.SurgeryInvariance.DiscRegion P)
    (hslice : Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ D.interior) :
    closure (Work.BoxShrink.Core.sliceRegion P s c σ u) ⊆ D.carrier :=
  closure_minimal (fun _ hx => D.interior_subset_carrier (hslice hx))
    (isClosed_carrier_of_discRegion D)

/-! ## The residual when the slice cuts the disc's interior into at most two pieces

`Ω = (Ω ∩ D°) ∪ halves` (the slice is inside the disc's interior and every other point of `Ω` is off
the cutting plane), the disc's interior is carrier-open, inessential and path connected, and the two
half-regions are carrier-open and inessential (`h0`).  So the whole geometry of the residual sits in
the *intersection* `D° ∩ halves = D° \ Σ`, and the generalised rank bound
`exists_ne_zero_inf_span_le_of_intersection_pair_general` — which, unlike its sibling, does **not**
assume that the two assembled pieces are path connected — bounds the winding span of the union by
one line as soon as that intersection is the disjoint union of at most **two** path connected pieces.

This is the case in which the *groundedness* `(★)` of `DiscInteriorGrounded` fails (two pieces of the
slice's complement in the disc joined in `halves`), so the two criteria are complementary.  The
residual which remains after this lemma is: **the slice cuts `D°` into at least three pieces**, i.e.
the plane cuts the disc in at least two chords. -/
theorem exists_ne_zero_inf_span_le_of_disc_two_pieces (P : Work.CoreTopology.ParamTorus) (s : ℝ)
    (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) (D : Work.SurgeryInvariance.DiscRegion P)
    (hslice : Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ D.interior)
    (h0 : Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) = ⊥)
    {K₁ K₂ : Set R3}
    (hK₁op : Work.SurgeryInvariance.IsOpenInCarrier P K₁)
    (hK₂op : Work.SurgeryInvariance.IsOpenInCarrier P K₂)
    (hK₁pc : IsPathConnected K₁) (hK₂pc : IsPathConnected K₂)
    (hdisj : Disjoint K₁ K₂)
    (hinter : D.interior ∩ Work.PinchLemma3.halfRegions P s c σ u = K₁ ∪ K₂) :
    ∃ v : ℚ × ℚ, v ≠ 0 ∧
      Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ⊓
        Submodule.span ℚ ({v} : Set (ℚ × ℚ)) ≤
      Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) := by
  have hWsub : Work.SurgeryInvariance.WindingSpan P D.interior = ⊥ :=
    windingSpan_eq_bot_of_subset_discRegion D D.interior_subset_carrier
  have hAc : D.interior ⊆ P.carrier :=
    fun x hx => D.carrier_subset_surface (D.interior_subset_carrier hx)
  have hK₁car : K₁ ⊆ P.carrier := by
    intro x hx
    have : x ∈ D.interior ∩ Work.PinchLemma3.halfRegions P s c σ u := by
      rw [hinter]; exact Or.inl hx
    exact hAc this.1
  have hK₂car : K₂ ⊆ P.carrier := by
    intro x hx
    have : x ∈ D.interior ∩ Work.PinchLemma3.halfRegions P s c σ u := by
      rw [hinter]; exact Or.inr hx
    exact hAc this.1
  obtain ⟨v, hv0, hvle⟩ :=
    exists_ne_zero_inf_span_le_of_intersection_pair_general
      (P := P) (A := D.interior) (B := halfRegions P s c σ u)
      (K₁ := K₁) (K₂ := K₂)
      hAc (halfRegions_subset_carrier P s c σ u)
      D.open_interior' (isOpenInCarrier_halfRegions P s c σ u)
      hWsub h0 hK₁car hK₂car hK₁op hK₂op hK₁pc hK₂pc hdisj hinter
  refine ⟨v, hv0, ?_⟩
  have h1 : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ⊓
      Submodule.span ℚ ({v} : Set (ℚ × ℚ)) ≤
      Work.SurgeryInvariance.WindingSpan P D.interior ⊔
        Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) :=
    le_trans (inf_le_inf_right _ (Work.SurgeryInvariance.WindingSpan_mono P (by
      rw [Set.union_comm]
      exact boxRegion_subset_halfRegions_union_disc_interior P s c σ u D hslice))) hvle
  rw [hWsub, h0, bot_sup_eq] at h1
  rw [h0]
  exact h1

/-- **A case of `wall_core`**: the conclusion holds as soon as the slice cuts the disc's interior
into at most two pieces.  The hypothesis `hT` of `wall_core` is not used. -/
theorem wall_core_of_disc_two_pieces (P : Work.CoreTopology.ParamTorus) (s : ℝ)
    (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (D : Work.SurgeryInvariance.DiscRegion P)
    (_hD : D.carrier ⊆ Work.PinchLemma3.closedBoxRegion P s c σ)
    (hslice : Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ D.interior)
    (_hT : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Pinch.planeTrace P c σ u) = ⊥)
    (h0 : Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) = ⊥)
    {K₁ K₂ : Set R3}
    (hK₁op : Work.SurgeryInvariance.IsOpenInCarrier P K₁)
    (hK₂op : Work.SurgeryInvariance.IsOpenInCarrier P K₂)
    (hK₁pc : IsPathConnected K₁) (hK₂pc : IsPathConnected K₂)
    (hdisj : Disjoint K₁ K₂)
    (hinter : D.interior ∩ Work.PinchLemma3.halfRegions P s c σ u = K₁ ∪ K₂) :
    ∃ v : ℚ × ℚ, v ≠ 0 ∧
      Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ⊓
        Submodule.span ℚ ({v} : Set (ℚ × ℚ)) ≤
      Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) :=
  exists_ne_zero_inf_span_le_of_disc_two_pieces P s c σ u D hslice h0
    hK₁op hK₂op hK₁pc hK₂pc hdisj hinter


/-- **A limit point of the slice which is not in the slice is a gate point lying in the disc.**
In the trace of the cutting plane, such a limit point lies on the box sphere
(`mem_sphereSet_of_mem_closure_sliceRegion_not_mem`) and, by
`closure_sliceRegion_subset_discRegion_carrier`, in the closed disc; so it is a point of
`∂D ∩ ∂Box` — a *gate* of the disc — unless it is a (tangency) point of the disc's interior on the
box sphere.  This is the formal form of "the slice runs from gate to gate", used by every route to
the residual. -/
theorem mem_sphereSet_and_carrier_of_mem_closure_sliceRegion_not_mem
    (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (D : Work.SurgeryInvariance.DiscRegion P)
    (hslice : Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ D.interior)
    {q : ↥(Work.BoxShrink.Pinch.planeTrace P c σ u)}
    (hq : q ∈ closure (Subtype.val ⁻¹' (Work.BoxShrink.Core.sliceRegion P s c σ u :
      Set R3) : Set ↥(Work.BoxShrink.Pinch.planeTrace P c σ u)))
    (hnot : (q : R3) ∉ Work.BoxShrink.Core.sliceRegion P s c σ u) :
    (q : R3) ∈ Work.BoxShrink.Core.sphereSet c σ s ∧ (q : R3) ∈ D.carrier := by
  refine ⟨mem_sphereSet_of_mem_closure_sliceRegion_not_mem P s c σ u hq hnot, ?_⟩
  refine closure_sliceRegion_subset_discRegion_carrier D hslice ?_
  exact (continuous_subtype_val).closure_preimage_subset
    (Work.BoxShrink.Core.sliceRegion P s c σ u) hq


/-! ## The complementary extreme: the boundary circle of the disc on the box sphere

`wall_core_of_boundary_avoids_sphereTrace` covers the case in which the boundary circle of the disc
misses the box sphere entirely (then the whole circle is a *free* arc, and `W(Ω) = ⊥`).  The
complementary extreme is that the boundary circle lies *entirely on* the box sphere (`∂D ∩ Ω = ∅`, no
free arcs at all): then `Ω` is the disjoint union of the two carrier-open pieces `Ω ∩ D°` and
`Ω \ D̄`, the first inessential because it lies in the disc, the second because it lies in
`Ω \ Σ = halves`; additivity of the winding span over disjoint open pieces gives `W(Ω) = ⊥` again.
So the difficulty of the residual lives exactly in the *free arcs*: the interfaces between the part of
`Ω` inside the disc and the part outside it. -/
theorem windingSpan_boxRegion_eq_bot_of_disjoint_boundary_region {P : Work.CoreTopology.ParamTorus}
    {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} (D : Work.SurgeryInvariance.DiscRegion P)
    (hslice : Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ D.interior)
    (hdisj : Disjoint D.boundary (Work.BoxShrink.Core.boxRegion P s c σ))
    (h0 : Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) = ⊥) :
    Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) = ⊥ := by
  have hdecomp : Work.BoxShrink.Core.boxRegion P s c σ =
      (Work.BoxShrink.Core.boxRegion P s c σ ∩ D.interior) ∪
        (Work.BoxShrink.Core.boxRegion P s c σ \ D.carrier) := by
    ext x
    constructor
    · intro hx
      by_cases hc : x ∈ D.carrier
      · rcases (show x ∈ D.interior ∪ D.boundary from
          discRegion_carrier_eq_interior_union_boundary D ▸ hc) with h | h
        · exact Or.inl ⟨hx, h⟩
        · exact ((Set.disjoint_left.mp hdisj) h hx).elim
      · exact Or.inr ⟨hx, hc⟩
    · rintro (⟨hx, -⟩ | ⟨hx, -⟩) <;> exact hx
  have hopenD : Work.SurgeryInvariance.IsOpenInCarrier P D.carrierᶜ := by
    rw [Work.SurgeryInvariance.IsOpenInCarrier, Set.preimage_compl]
    exact ((isClosed_carrier_of_discRegion D).preimage continuous_subtype_val).isOpen_compl
  have hAop : Work.SurgeryInvariance.IsOpenInCarrier P
      (Work.BoxShrink.Core.boxRegion P s c σ ∩ D.interior) :=
    Work.SurgeryInvariance.isOpenInCarrier_inter (P := P)
      (Work.BoxShrink.Core.isOpenInCarrier_boxRegion P s c σ) D.open_interior'
  have hBop : Work.SurgeryInvariance.IsOpenInCarrier P
      (Work.BoxShrink.Core.boxRegion P s c σ \ D.carrier) := by
    rw [Set.sdiff_eq]
    exact Work.SurgeryInvariance.isOpenInCarrier_inter (P := P)
      (Work.BoxShrink.Core.isOpenInCarrier_boxRegion P s c σ) hopenD
  have hdisjAB : Disjoint (Work.BoxShrink.Core.boxRegion P s c σ ∩ D.interior)
      (Work.BoxShrink.Core.boxRegion P s c σ \ D.carrier) := by
    rw [Set.disjoint_left]
    rintro x ⟨-, hxi⟩ ⟨-, hxc⟩
    exact hxc (D.interior_subset_carrier hxi)
  have hA : Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.boxRegion P s c σ ∩ D.interior) = ⊥ :=
    windingSpan_eq_bot_of_subset_discRegion D (Set.inter_subset_right.trans D.interior_subset_carrier)
  have hBsub : Work.BoxShrink.Core.boxRegion P s c σ \ D.carrier ⊆
      Work.PinchLemma3.halfRegions P s c σ u := by
    rintro x ⟨hx, hxc⟩
    refine (boxRegion_sdiff_sliceRegion P s c σ u).symm ▸ ⟨hx, fun hs => hxc ?_⟩
    exact D.interior_subset_carrier (hslice hs)
  have hB : Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.boxRegion P s c σ \ D.carrier) = ⊥ :=
    le_bot_iff.mp (le_trans (Work.SurgeryInvariance.WindingSpan_mono P hBsub) (le_of_eq h0))
  rw [hdecomp, Work.SurgeryInvariance.Span.union_eq_sup hAop hBop hdisjAB, hA, hB, bot_sup_eq]

/-- **`wall_core` when the boundary circle of the disc lies entirely on the box sphere** (no free
arcs): the strong conclusion `W(Ω) = ⊥`. -/
theorem wall_core_of_disjoint_boundary_region (P : Work.CoreTopology.ParamTorus) (s : ℝ)
    (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (D : Work.SurgeryInvariance.DiscRegion P)
    (_hD : D.carrier ⊆ Work.PinchLemma3.closedBoxRegion P s c σ)
    (hslice : Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ D.interior)
    (_hT : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Pinch.planeTrace P c σ u) = ⊥)
    (h0 : Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) = ⊥)
    (hdisj : Disjoint D.boundary (Work.BoxShrink.Core.boxRegion P s c σ)) :
    ∃ v : ℚ × ℚ, v ≠ 0 ∧
      Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ⊓
        Submodule.span ℚ ({v} : Set (ℚ × ℚ)) ≤
      Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) := by
  have hbot : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) = ⊥ :=
    windingSpan_boxRegion_eq_bot_of_disjoint_boundary_region D hslice hdisj h0
  exact wall_core_of_ne_top (by rw [hbot]; exact bot_ne_top)


/-! ## The three-piece case: the *distribution* of the pieces between the two half-regions

Session 10.  The rank bound `exists_ne_zero_inf_span_le_of_intersection_pair_general` (and its
wiring `wall_core_of_disc_two_pieces`) applies with `A = D°` and `B = halves` as soon as the
intersection `D° ∩ halves = D° ∖ Σ` has at most **two** path components — i.e. as long as the
slice `Σ` cuts the disc's interior in at most one chord.  Session 9 established that this cannot
be improved by looking at `D° ∖ Σ` alone: `NOTES_wall_core.md` §14.9 exhibits a configuration in
which `A`, `B` are both inessential, `A ∩ B` has *three* path components and yet
`finrank W(A ∪ B) = 2`.

What that model has and the pinch does not is the *sign* structure: there `B` is a disc, while here
`B = halves = Ω⁺ ⊔ Ω⁻` is a **disjoint union of two open pieces**, the two sides of the cutting
plane, and each component of `D° ∖ Σ` lies wholly on one side, consecutive components lying on
opposite sides.  This is what the new (delegated) theorem
`Work.PinchLemma3.ClosedDiscA.exists_ne_zero_inf_span_le_of_intersection_three_pieces` uses: if
`A ∩ B = K₁ ∪ K₂ ∪ K₃` and the three pieces are distributed `2 + 1` over the two components of `B`
(`K₁ ∪ K₂ ⊆ Ω⁺`, `K₃ ⊆ Ω⁻`), then one still gets a line outside the winding span of `A ∪ B`.  The
Mayer–Vietoris count behind it: the "extra generator" of `H₁(A ∪ B)` is the pair `K₁`, `K₂` *inside
the single component* `Ω⁺`, and the component `Ω⁻` contributes only the piece `K₃`, which carries no
extra generator.

So the covered cases of the residual now include the configuration in which **the plane cuts the
disc's interior in exactly two chords** (three pieces), which is the regime of the refutation
`strong_span_form_refuted` — there `finrank W(Ω) = 1`, consistent with the bound proved here.  The
residual is pushed to `Σ` cutting `D°` into **four or more** pieces, i.e. at least three chords.

The names of the pieces `K₁, K₂, K₃` are arbitrary: the geometric caller renames them so that the
two pieces on one side come first (only the *existence* of such a naming is used, and the naming is
supplied by the caller, who knows on which side each piece lies). -/

theorem exists_ne_zero_inf_span_le_of_disc_three_pieces (P : Work.CoreTopology.ParamTorus) (s : ℝ)
    (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) (D : Work.SurgeryInvariance.DiscRegion P)
    (hslice : Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ D.interior)
    (h0 : Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) = ⊥)
    {K₁ K₂ K₃ : Set R3}
    (hK₁op : Work.SurgeryInvariance.IsOpenInCarrier P K₁)
    (hK₂op : Work.SurgeryInvariance.IsOpenInCarrier P K₂)
    (hK₃op : Work.SurgeryInvariance.IsOpenInCarrier P K₃)
    (hK₁pc : IsPathConnected K₁) (hK₂pc : IsPathConnected K₂) (hK₃pc : IsPathConnected K₃)
    (hdisj₁₂ : Disjoint K₁ K₂) (hdisj₁₃ : Disjoint K₁ K₃) (hdisj₂₃ : Disjoint K₂ K₃)
    (hinter : D.interior ∩ Work.PinchLemma3.halfRegions P s c σ u = K₁ ∪ K₂ ∪ K₃)
    (hK₁B₁ : K₁ ⊆ Work.BoxShrink.Core.upperRegion P s c σ u)
    (hK₂B₁ : K₂ ⊆ Work.BoxShrink.Core.upperRegion P s c σ u)
    (hK₃B₂ : K₃ ⊆ Work.BoxShrink.Core.lowerRegion P s c σ u) :
    ∃ v : ℚ × ℚ, v ≠ 0 ∧
      Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ⊓
        Submodule.span ℚ ({v} : Set (ℚ × ℚ)) ≤
      Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) := by
  have hAc : D.interior ⊆ P.carrier :=
    fun x hx => D.carrier_subset_surface (D.interior_subset_carrier hx)
  have hBc : Work.PinchLemma3.halfRegions P s c σ u ⊆ P.carrier :=
    halfRegions_subset_carrier P s c σ u
  have hB₁c : Work.BoxShrink.Core.upperRegion P s c σ u ⊆ P.carrier :=
    fun x hx => (Work.BoxShrink.Core.upperRegion_subset P s c σ u hx).1
  have hB₂c : Work.BoxShrink.Core.lowerRegion P s c σ u ⊆ P.carrier :=
    fun x hx => (Work.BoxShrink.Core.lowerRegion_subset P s c σ u hx).1
  have hK₁car : K₁ ⊆ P.carrier := by
    intro x hx
    have : x ∈ D.interior ∩ Work.PinchLemma3.halfRegions P s c σ u := by
      rw [hinter]; exact Or.inl (Or.inl hx)
    exact hAc this.1
  have hK₂car : K₂ ⊆ P.carrier := by
    intro x hx
    have : x ∈ D.interior ∩ Work.PinchLemma3.halfRegions P s c σ u := by
      rw [hinter]; exact Or.inl (Or.inr hx)
    exact hAc this.1
  have hK₃car : K₃ ⊆ P.carrier := by
    intro x hx
    have : x ∈ D.interior ∩ Work.PinchLemma3.halfRegions P s c σ u := by
      rw [hinter]; exact Or.inr hx
    exact hAc this.1
  have hWsub : Work.SurgeryInvariance.WindingSpan P D.interior = ⊥ :=
    windingSpan_eq_bot_of_subset_discRegion D D.interior_subset_carrier
  obtain ⟨v, hv0, hvle⟩ :=
    exists_ne_zero_inf_span_le_of_intersection_three_pieces
      (P := P) (A := D.interior) (B := Work.PinchLemma3.halfRegions P s c σ u)
      (B₁ := Work.BoxShrink.Core.upperRegion P s c σ u)
      (B₂ := Work.BoxShrink.Core.lowerRegion P s c σ u)
      (K₁ := K₁) (K₂ := K₂) (K₃ := K₃)
      hAc hBc D.open_interior' (isOpenInCarrier_halfRegions P s c σ u)
      (isPathConnected_discRegion_interior D) hWsub h0
      hB₁c hB₂c
      (Work.BoxShrink.Core.isOpenInCarrier_upperRegion P s c σ u)
      (Work.BoxShrink.Core.isOpenInCarrier_lowerRegion P s c σ u)
      rfl (disjoint_upperRegion_lowerRegion P s c σ u)
      hK₁car hK₂car hK₃car hK₁op hK₂op hK₃op hK₁pc hK₂pc hK₃pc
      hdisj₁₂ hdisj₁₃ hdisj₂₃ hinter hK₁B₁ hK₂B₁ hK₃B₂
  refine ⟨v, hv0, ?_⟩
  have h1 : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ⊓
      Submodule.span ℚ ({v} : Set (ℚ × ℚ)) ≤
      Work.SurgeryInvariance.WindingSpan P D.interior ⊔
        Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) :=
    le_trans (inf_le_inf_right _ (Work.SurgeryInvariance.WindingSpan_mono P (by
      rw [Set.union_comm]
      exact boxRegion_subset_halfRegions_union_disc_interior P s c σ u D hslice))) hvle
  rw [hWsub, h0, bot_sup_eq] at h1
  rw [h0]
  exact h1

/-- **A case of `wall_core`**: the conclusion holds as soon as the *three* pieces of the slice's
complement in the disc's interior are distributed `2 + 1` over the two half-regions.  This extends
`wall_core_of_disc_two_pieces` by one chord of the slice; the hypothesis `hT` of `wall_core` is not
used. -/
theorem wall_core_of_disc_three_pieces (P : Work.CoreTopology.ParamTorus) (s : ℝ)
    (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (D : Work.SurgeryInvariance.DiscRegion P)
    (_hD : D.carrier ⊆ Work.PinchLemma3.closedBoxRegion P s c σ)
    (hslice : Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ D.interior)
    (_hT : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Pinch.planeTrace P c σ u) = ⊥)
    (h0 : Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) = ⊥)
    {K₁ K₂ K₃ : Set R3}
    (hK₁op : Work.SurgeryInvariance.IsOpenInCarrier P K₁)
    (hK₂op : Work.SurgeryInvariance.IsOpenInCarrier P K₂)
    (hK₃op : Work.SurgeryInvariance.IsOpenInCarrier P K₃)
    (hK₁pc : IsPathConnected K₁) (hK₂pc : IsPathConnected K₂) (hK₃pc : IsPathConnected K₃)
    (hdisj₁₂ : Disjoint K₁ K₂) (hdisj₁₃ : Disjoint K₁ K₃) (hdisj₂₃ : Disjoint K₂ K₃)
    (hinter : D.interior ∩ Work.PinchLemma3.halfRegions P s c σ u = K₁ ∪ K₂ ∪ K₃)
    (hK₁B₁ : K₁ ⊆ Work.BoxShrink.Core.upperRegion P s c σ u)
    (hK₂B₁ : K₂ ⊆ Work.BoxShrink.Core.upperRegion P s c σ u)
    (hK₃B₂ : K₃ ⊆ Work.BoxShrink.Core.lowerRegion P s c σ u) :
    ∃ v : ℚ × ℚ, v ≠ 0 ∧
      Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ⊓
        Submodule.span ℚ ({v} : Set (ℚ × ℚ)) ≤
      Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) :=
  exists_ne_zero_inf_span_le_of_disc_three_pieces P s c σ u D hslice h0
    hK₁op hK₂op hK₃op hK₁pc hK₂pc hK₃pc hdisj₁₂ hdisj₁₃ hdisj₂₃ hinter hK₁B₁ hK₂B₁ hK₃B₂

/-- **A subspace of `ℚ × ℚ` of dimension at most one misses a nonzero line.**  This is the form in
which the *general* rank bound of
`Work.PinchLemma3.ClosedDiscA.finrank_windingSpan_union_le_of_pieces_of_components` (the defect
count `finrank W(A ∪ B) ≤ #pieces − #components`, NOTES §15.2) is consumed: a bound
`finrank ≤ 1` on the winding span of a region *is* the one-class conclusion, with no need to redo
the linear algebra of `ℚ²` each time. -/
theorem exists_ne_zero_inf_span_le_of_finrank_le_one {X : Submodule ℚ (ℚ × ℚ)}
    (h : Module.finrank ℚ X ≤ 1) :
    ∃ v : ℚ × ℚ, v ≠ 0 ∧ X ⊓ Submodule.span ℚ ({v} : Set (ℚ × ℚ)) = ⊥ := by
  have hne : X ≠ ⊤ := by
    intro htop
    have h2 : Module.finrank ℚ X = 2 := by
      rw [htop, finrank_top, Module.finrank_prod, Module.finrank_self]
    omega
  obtain ⟨v, hv⟩ : ∃ v : ℚ × ℚ, v ∉ X := by
    by_contra hcon
    push Not at hcon
    exact hne (Submodule.eq_top_iff'.mpr hcon)
  refine ⟨v, fun hv0 => hv (hv0 ▸ Submodule.zero_mem _), ?_⟩
  exact disjoint_iff.mp
    (Submodule.disjoint_span_singleton.mpr (fun hmem => absurd hmem hv))

/-- The interior of a disc region lies in the carrier. -/
theorem discRegion_interior_subset_carrier {P : Work.CoreTopology.ParamTorus}
    (D : Work.SurgeryInvariance.DiscRegion P) : D.interior ⊆ P.carrier :=
  fun x hx => D.carrier_subset_surface (D.interior_subset_carrier hx)

/-! ## Session 11: the two-thickening reduction, and a new covered case of the residual

The two half-regions and the disc *thicken* each other: because the slice `Σ = Ω ∩ Γ` is carried by
the disc's interior (`hslice`), the box region is covered by the two sets

  `A := Ω⁺ ∪ D°`,   `B := Ω⁻ ∪ D°`,

whose intersection is **exactly the disc's interior** `D°`:

  `(Ω⁺ ∪ D°) ∩ (Ω⁻ ∪ D°) = D°`.

Since `D°` is path connected (it is the interior of an embedded disc), the overlapping two-piece
theorem applies, and

  `W(Ω) ≤ W(A) ⊔ W(B) = W(Ω⁺ ∪ D°) ⊔ W(Ω⁻ ∪ D°)`.

This is the sharpest form of the "split the region along the disc" reduction: instead of the two
*halves* of `Ω` (which are not open pieces of `Ω` together with the slice) it uses the two
*thickenings*, one per side, whose intersection is a single disc, and it exhibits the residual as
the *joint* size of the two one-sided spans `W(Ω^± ∪ D°)`.

Consequences proved below:

* if the upper thickening is inessential (`W(Ω⁺ ∪ D°) = ⊥`), then `W(Ω) ≤ W(Ω⁻ ∪ D°)`, so a bound
  `finrank W(Ω⁻ ∪ D°) ≤ 1` — which holds as soon as `Ω⁻ ∩ D°` has at most two path components
  (`exists_ne_zero_inf_span_le_of_intersection_pair_general`) — gives the conclusion of `wall_core`.
  The same with the two sides exchanged.  This **closes a genuinely new case of the residual**, the
  one with four pieces of `D° ∖ Σ` (three chords) in which the pieces of one half are *not* joined
  inside that half: `W(Ω⁺ ∪ D°) = ⊥` is then a consequence of the grounded criterion
  (`WindingSpan_union_le_sup_of_grounded_inter`), and the remaining side supplies at most one class.
* `W(Ω^± ∪ D°) = ⊥` is available from the *grounding* of `Ω^± ∩ D°` inside `Ω^±` (the
  `hground`-hypothesis below), which is in turn equivalent to the two pieces of `Ω^± ∩ D°` not being
  joined inside `Ω^±` (`joinedIn_inter_of_not_joinedIn`).

The residual after this section is therefore: **both** thickenings essential — equivalently, in the
`k = 3` case, both halves' pieces joined in their own half. -/

/-- **The box region is covered by the two thickenings of the half-regions by the disc's
interior** (which is the exact content of `hslice` for the slice). -/
theorem boxRegion_subset_upper_lower_thickening {P : Work.CoreTopology.ParamTorus} {s : ℝ}
    {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} {D : Work.SurgeryInvariance.DiscRegion P}
    (hslice : Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ D.interior) :
    Work.BoxShrink.Core.boxRegion P s c σ ⊆
      (Work.BoxShrink.Core.upperRegion P s c σ u ∪ D.interior) ∪
        (Work.BoxShrink.Core.lowerRegion P s c σ u ∪ D.interior) := by
  rw [Work.BoxShrink.Core.boxRegion_eq_union P s c σ u]
  rintro y (hy | hy)
  · rcases hy with h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl h)
  · exact Or.inl (Or.inr (hslice hy))

/-- **The two thickenings meet exactly in the disc's interior.** -/
theorem thickening_inter_eq (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) (D : Work.SurgeryInvariance.DiscRegion P) :
    (Work.BoxShrink.Core.upperRegion P s c σ u ∪ D.interior) ∩
        (Work.BoxShrink.Core.lowerRegion P s c σ u ∪ D.interior) = D.interior := by
  ext y
  simp only [Set.mem_inter_iff, Set.mem_union]
  constructor
  · rintro ⟨h1 | h1, h2 | h2⟩
    · exact (Set.disjoint_left.mp (disjoint_upperRegion_lowerRegion P s c σ u) h1 h2).elim
    · exact h2
    · exact h1
    · exact h1
  · intro h
    exact ⟨Or.inr h, Or.inr h⟩

/-- **The two-thickening reduction**: the box region's winding span is contained in the sum of the
two one-sided thickenings' spans. -/
theorem windingSpan_boxRegion_le_sup_of_disc_thickenings (P : Work.CoreTopology.ParamTorus)
    (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) (D : Work.SurgeryInvariance.DiscRegion P)
    (hslice : Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ D.interior) :
    Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ≤
      Work.SurgeryInvariance.WindingSpan P
          (Work.BoxShrink.Core.upperRegion P s c σ u ∪ D.interior) ⊔
        Work.SurgeryInvariance.WindingSpan P
          (Work.BoxShrink.Core.lowerRegion P s c σ u ∪ D.interior) := by
  have hUc : Work.BoxShrink.Core.upperRegion P s c σ u ⊆ P.carrier :=
    fun x hx => (Work.BoxShrink.Core.upperRegion_subset P s c σ u hx).1
  have hLc : Work.BoxShrink.Core.lowerRegion P s c σ u ⊆ P.carrier :=
    fun x hx => (Work.BoxShrink.Core.lowerRegion_subset P s c σ u hx).1
  have hAc : Work.BoxShrink.Core.upperRegion P s c σ u ∪ D.interior ⊆ P.carrier :=
    Set.union_subset hUc (discRegion_interior_subset_carrier D)
  have hBc : Work.BoxShrink.Core.lowerRegion P s c σ u ∪ D.interior ⊆ P.carrier :=
    Set.union_subset hLc (discRegion_interior_subset_carrier D)
  have hAop : Work.SurgeryInvariance.IsOpenInCarrier P
      (Work.BoxShrink.Core.upperRegion P s c σ u ∪ D.interior) :=
    Work.SurgeryInvariance.isOpenInCarrier_union P
      (Work.BoxShrink.Core.isOpenInCarrier_upperRegion P s c σ u) D.open_interior'
  have hBop : Work.SurgeryInvariance.IsOpenInCarrier P
      (Work.BoxShrink.Core.lowerRegion P s c σ u ∪ D.interior) :=
    Work.SurgeryInvariance.isOpenInCarrier_union P
      (Work.BoxShrink.Core.isOpenInCarrier_lowerRegion P s c σ u) D.open_interior'
  have hconn : IsPathConnected
      ((Work.BoxShrink.Core.upperRegion P s c σ u ∪ D.interior) ∩
        (Work.BoxShrink.Core.lowerRegion P s c σ u ∪ D.interior)) := by
    rw [thickening_inter_eq P s c σ u D]
    exact isPathConnected_discRegion_interior D
  refine le_trans (Work.SurgeryInvariance.WindingSpan_mono P ?_)
    (windingSpan_union_le_sup_of_isPathConnected_inter (P := P) hAc hBc hAop hBop hconn)
  exact boxRegion_subset_upper_lower_thickening hslice

/-- **A subspace of `ℚ × ℚ` containing no nonzero multiple of a nonzero vector has dimension at
most one.**  (Local restatement of the sibling lemma of the same shape, kept here so that the
session-11 reduction below depends only on the modules this file already imports.) -/
theorem finrank_le_one_of_inf_span_le_bot_aux {X : Submodule ℚ (ℚ × ℚ)} {v : ℚ × ℚ}
    (hv : v ≠ 0) (h : X ⊓ Submodule.span ℚ ({v} : Set (ℚ × ℚ)) ≤ ⊥) :
    Module.finrank ℚ X ≤ 1 := by
  have hbot : X ⊓ Submodule.span ℚ ({v} : Set (ℚ × ℚ)) = ⊥ := le_bot_iff.mp h
  have h1 : Module.finrank ℚ ↥(Submodule.span ℚ ({v} : Set (ℚ × ℚ))) = 1 :=
    finrank_span_singleton hv
  have hfr := Submodule.finrank_sup_add_finrank_inf_eq X (Submodule.span ℚ ({v} : Set (ℚ × ℚ)))
  rw [hbot, finrank_bot, h1] at hfr
  have h2 : Module.finrank ℚ ↥(X ⊔ Submodule.span ℚ ({v} : Set (ℚ × ℚ))) ≤ 2 := by
    have h3 := Submodule.finrank_mono (le_top : X ⊔ Submodule.span ℚ ({v} : Set (ℚ × ℚ)) ≤ ⊤)
    rwa [finrank_top, Module.finrank_prod, Module.finrank_self] at h3
  omega

/-- **The upper thickening is inessential when the upper half-region is *grounded* in it**: if every
path of `Ω⁺` between two points of `Ω⁺ ∩ D°` can be rerouted inside `Ω⁺ ∩ D°`, then the two-piece
criterion gives `W(Ω⁺ ∪ D°) ≤ W(Ω⁺) ⊔ W(D°) = ⊥`. -/
theorem windingSpan_upperRegion_union_discInterior_eq_bot_of_grounded
    (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (D : Work.SurgeryInvariance.DiscRegion P)
    (h0 : Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) = ⊥)
    (hground : ∀ x ∈ Work.BoxShrink.Core.upperRegion P s c σ u ∩ D.interior,
      ∀ y ∈ Work.BoxShrink.Core.upperRegion P s c σ u ∩ D.interior,
        JoinedIn (Work.BoxShrink.Core.upperRegion P s c σ u) x y →
          JoinedIn (Work.BoxShrink.Core.upperRegion P s c σ u ∩ D.interior) x y) :
    Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.upperRegion P s c σ u ∪ D.interior) = ⊥ := by
  have hUc : Work.BoxShrink.Core.upperRegion P s c σ u ⊆ P.carrier :=
    fun x hx => (Work.BoxShrink.Core.upperRegion_subset P s c σ u hx).1
  have hVU : Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.upperRegion P s c σ u) = ⊥ :=
    le_bot_iff.mp (le_trans (Work.SurgeryInvariance.WindingSpan_mono P
      (Set.subset_union_left : Work.BoxShrink.Core.upperRegion P s c σ u ⊆
        Work.PinchLemma3.halfRegions P s c σ u)) (le_of_eq h0))
  have h := windingSpan_union_le_sup_of_grounded_inter (P := P)
    (A := Work.BoxShrink.Core.upperRegion P s c σ u) (B := D.interior)
    hUc (discRegion_interior_subset_carrier D)
    (Work.BoxShrink.Core.isOpenInCarrier_upperRegion P s c σ u) D.open_interior'
    (isPathConnected_discRegion_interior D) hground hVU D.windingSpan_interior_eq_bot
  rw [hVU, D.windingSpan_interior_eq_bot, bot_sup_eq] at h
  exact le_bot_iff.mp h

/-- **The lower thickening is inessential when the lower half-region is grounded in it.** -/
theorem windingSpan_lowerRegion_union_discInterior_eq_bot_of_grounded
    (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (D : Work.SurgeryInvariance.DiscRegion P)
    (h0 : Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) = ⊥)
    (hground : ∀ x ∈ Work.BoxShrink.Core.lowerRegion P s c σ u ∩ D.interior,
      ∀ y ∈ Work.BoxShrink.Core.lowerRegion P s c σ u ∩ D.interior,
        JoinedIn (Work.BoxShrink.Core.lowerRegion P s c σ u) x y →
          JoinedIn (Work.BoxShrink.Core.lowerRegion P s c σ u ∩ D.interior) x y) :
    Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.lowerRegion P s c σ u ∪ D.interior) = ⊥ := by
  have hLc : Work.BoxShrink.Core.lowerRegion P s c σ u ⊆ P.carrier :=
    fun x hx => (Work.BoxShrink.Core.lowerRegion_subset P s c σ u hx).1
  have hVL : Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.lowerRegion P s c σ u) = ⊥ :=
    le_bot_iff.mp (le_trans (Work.SurgeryInvariance.WindingSpan_mono P
      (Set.subset_union_right : Work.BoxShrink.Core.lowerRegion P s c σ u ⊆
        Work.PinchLemma3.halfRegions P s c σ u)) (le_of_eq h0))
  have h := windingSpan_union_le_sup_of_grounded_inter (P := P)
    (A := Work.BoxShrink.Core.lowerRegion P s c σ u) (B := D.interior)
    hLc (discRegion_interior_subset_carrier D)
    (Work.BoxShrink.Core.isOpenInCarrier_lowerRegion P s c σ u) D.open_interior'
    (isPathConnected_discRegion_interior D) hground hVL D.windingSpan_interior_eq_bot
  rw [hVL, D.windingSpan_interior_eq_bot, bot_sup_eq] at h
  exact le_bot_iff.mp h

/-- **The lower thickening carries at most one class when `Ω⁻ ∩ D°` has at most two path
components.** -/
theorem finrank_lowerRegion_union_discInterior_le_one_of_pair
    (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (D : Work.SurgeryInvariance.DiscRegion P)
    (h0 : Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) = ⊥)
    {K₁ K₂ : Set R3}
    (hK₁op : Work.SurgeryInvariance.IsOpenInCarrier P K₁)
    (hK₂op : Work.SurgeryInvariance.IsOpenInCarrier P K₂)
    (hK₁pc : IsPathConnected K₁) (hK₂pc : IsPathConnected K₂)
    (hdisj : Disjoint K₁ K₂)
    (hinter : D.interior ∩ Work.BoxShrink.Core.lowerRegion P s c σ u = K₁ ∪ K₂) :
    Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.lowerRegion P s c σ u ∪ D.interior)) ≤ 1 := by
  have hLc : Work.BoxShrink.Core.lowerRegion P s c σ u ⊆ P.carrier :=
    fun x hx => (Work.BoxShrink.Core.lowerRegion_subset P s c σ u hx).1
  have hVL : Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.lowerRegion P s c σ u) = ⊥ :=
    le_bot_iff.mp (le_trans (Work.SurgeryInvariance.WindingSpan_mono P
      (Set.subset_union_right : Work.BoxShrink.Core.lowerRegion P s c σ u ⊆
        Work.PinchLemma3.halfRegions P s c σ u)) (le_of_eq h0))
  have hK₁c : K₁ ⊆ P.carrier := fun x hx =>
    hLc ((hinter.symm ▸ (Set.mem_union_left K₂ hx)).2)
  have hK₂c : K₂ ⊆ P.carrier := fun x hx =>
    hLc ((hinter.symm ▸ (Set.mem_union_right K₁ hx)).2)
  obtain ⟨v, hv0, hvle⟩ := exists_ne_zero_inf_span_le_of_intersection_pair_general
    (P := P) (A := Work.BoxShrink.Core.lowerRegion P s c σ u) (B := D.interior)
    hLc (discRegion_interior_subset_carrier D)
    (Work.BoxShrink.Core.isOpenInCarrier_lowerRegion P s c σ u) D.open_interior'
    hVL D.windingSpan_interior_eq_bot
    hK₁c hK₂c hK₁op hK₂op hK₁pc hK₂pc hdisj
    (Set.inter_comm D.interior _ ▸ hinter)
  rw [hVL, D.windingSpan_interior_eq_bot, bot_sup_eq] at hvle
  exact finrank_le_one_of_inf_span_le_bot_aux hv0 hvle

/-- **The upper thickening carries at most one class when `Ω⁺ ∩ D°` has at most two path
components.** -/
theorem finrank_upperRegion_union_discInterior_le_one_of_pair
    (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (D : Work.SurgeryInvariance.DiscRegion P)
    (h0 : Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) = ⊥)
    {K₁ K₂ : Set R3}
    (hK₁op : Work.SurgeryInvariance.IsOpenInCarrier P K₁)
    (hK₂op : Work.SurgeryInvariance.IsOpenInCarrier P K₂)
    (hK₁pc : IsPathConnected K₁) (hK₂pc : IsPathConnected K₂)
    (hdisj : Disjoint K₁ K₂)
    (hinter : D.interior ∩ Work.BoxShrink.Core.upperRegion P s c σ u = K₁ ∪ K₂) :
    Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.upperRegion P s c σ u ∪ D.interior)) ≤ 1 := by
  have hUc : Work.BoxShrink.Core.upperRegion P s c σ u ⊆ P.carrier :=
    fun x hx => (Work.BoxShrink.Core.upperRegion_subset P s c σ u hx).1
  have hVU : Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.upperRegion P s c σ u) = ⊥ :=
    le_bot_iff.mp (le_trans (Work.SurgeryInvariance.WindingSpan_mono P
      (Set.subset_union_left : Work.BoxShrink.Core.upperRegion P s c σ u ⊆
        Work.PinchLemma3.halfRegions P s c σ u)) (le_of_eq h0))
  have hK₁c : K₁ ⊆ P.carrier := fun x hx =>
    hUc ((hinter.symm ▸ (Set.mem_union_left K₂ hx)).2)
  have hK₂c : K₂ ⊆ P.carrier := fun x hx =>
    hUc ((hinter.symm ▸ (Set.mem_union_right K₁ hx)).2)
  obtain ⟨v, hv0, hvle⟩ := exists_ne_zero_inf_span_le_of_intersection_pair_general
    (P := P) (A := Work.BoxShrink.Core.upperRegion P s c σ u) (B := D.interior)
    hUc (discRegion_interior_subset_carrier D)
    (Work.BoxShrink.Core.isOpenInCarrier_upperRegion P s c σ u) D.open_interior'
    hVU D.windingSpan_interior_eq_bot
    hK₁c hK₂c hK₁op hK₂op hK₁pc hK₂pc hdisj
    (Set.inter_comm D.interior _ ▸ hinter)
  rw [hVU, D.windingSpan_interior_eq_bot, bot_sup_eq] at hvle
  exact finrank_le_one_of_inf_span_le_bot_aux hv0 hvle

/-- **THE NEW CASE OF THE RESIDUAL.**  If the *upper* thickening of the disc by the upper half is
inessential and the *lower* thickening carries at most one class (which holds as soon as
`Ω⁻ ∩ D°` has at most two path components), then `wall_core`'s conclusion holds.  In the four-piece
case (the slice cutting `D°` in three chords) this is exactly the configuration in which the two
pieces on one side are *not* joined inside that side.  The hypotheses `hD` and `hT` are not used. -/
theorem wall_core_of_upper_thickening_bot_of_lower_pair
    (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (D : Work.SurgeryInvariance.DiscRegion P)
    (_hD : D.carrier ⊆ Work.PinchLemma3.closedBoxRegion P s c σ)
    (hslice : Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ D.interior)
    (_hT : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Pinch.planeTrace P c σ u) = ⊥)
    (h0 : Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) = ⊥)
    (hbot : Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.upperRegion P s c σ u ∪ D.interior) = ⊥)
    {K₁ K₂ : Set R3}
    (hK₁op : Work.SurgeryInvariance.IsOpenInCarrier P K₁)
    (hK₂op : Work.SurgeryInvariance.IsOpenInCarrier P K₂)
    (hK₁pc : IsPathConnected K₁) (hK₂pc : IsPathConnected K₂)
    (hdisj : Disjoint K₁ K₂)
    (hinter : D.interior ∩ Work.BoxShrink.Core.lowerRegion P s c σ u = K₁ ∪ K₂) :
    ∃ v : ℚ × ℚ, v ≠ 0 ∧
      Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ⊓
        Submodule.span ℚ ({v} : Set (ℚ × ℚ)) ≤
      Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) := by
  have hfr : Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.lowerRegion P s c σ u ∪ D.interior)) ≤ 1 :=
    finrank_lowerRegion_union_discInterior_le_one_of_pair P s c σ u D h0
      hK₁op hK₂op hK₁pc hK₂pc hdisj hinter
  have hle := windingSpan_boxRegion_le_sup_of_disc_thickenings P s c σ u D hslice
  rw [hbot, bot_sup_eq] at hle
  have hfrΩ : Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.boxRegion P s c σ)) ≤ 1 :=
    le_trans (Submodule.finrank_mono hle) hfr
  obtain ⟨v, hv0, hvbot⟩ := exists_ne_zero_inf_span_le_of_finrank_le_one hfrΩ
  exact ⟨v, hv0, by rw [h0]; exact le_of_eq hvbot⟩

/-- **THE NEW CASE OF THE RESIDUAL, grounded form.**  Same conclusion with the inessentiality of the
upper thickening supplied by the *grounding* of `Ω⁺ ∩ D°` inside `Ω⁺`: every path of `Ω⁺` between
two points of `Ω⁺ ∩ D°` reroutes inside `Ω⁺ ∩ D°`. -/
theorem wall_core_of_upper_grounded_of_lower_pair
    (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (D : Work.SurgeryInvariance.DiscRegion P)
    (_hD : D.carrier ⊆ Work.PinchLemma3.closedBoxRegion P s c σ)
    (hslice : Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ D.interior)
    (_hT : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Pinch.planeTrace P c σ u) = ⊥)
    (h0 : Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) = ⊥)
    (hground : ∀ x ∈ Work.BoxShrink.Core.upperRegion P s c σ u ∩ D.interior,
      ∀ y ∈ Work.BoxShrink.Core.upperRegion P s c σ u ∩ D.interior,
        JoinedIn (Work.BoxShrink.Core.upperRegion P s c σ u) x y →
          JoinedIn (Work.BoxShrink.Core.upperRegion P s c σ u ∩ D.interior) x y)
    {K₁ K₂ : Set R3}
    (hK₁op : Work.SurgeryInvariance.IsOpenInCarrier P K₁)
    (hK₂op : Work.SurgeryInvariance.IsOpenInCarrier P K₂)
    (hK₁pc : IsPathConnected K₁) (hK₂pc : IsPathConnected K₂)
    (hdisj : Disjoint K₁ K₂)
    (hinter : D.interior ∩ Work.BoxShrink.Core.lowerRegion P s c σ u = K₁ ∪ K₂) :
    ∃ v : ℚ × ℚ, v ≠ 0 ∧
      Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ⊓
        Submodule.span ℚ ({v} : Set (ℚ × ℚ)) ≤
      Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) :=
  wall_core_of_upper_thickening_bot_of_lower_pair P s c σ u D _hD hslice _hT h0
    (windingSpan_upperRegion_union_discInterior_eq_bot_of_grounded P s c σ u D h0 hground)
    hK₁op hK₂op hK₁pc hK₂pc hdisj hinter

/-- **The same new case with the two sides exchanged.** -/
theorem wall_core_of_lower_thickening_bot_of_upper_pair
    (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (D : Work.SurgeryInvariance.DiscRegion P)
    (_hD : D.carrier ⊆ Work.PinchLemma3.closedBoxRegion P s c σ)
    (hslice : Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ D.interior)
    (_hT : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Pinch.planeTrace P c σ u) = ⊥)
    (h0 : Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) = ⊥)
    (hbot : Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.lowerRegion P s c σ u ∪ D.interior) = ⊥)
    {K₁ K₂ : Set R3}
    (hK₁op : Work.SurgeryInvariance.IsOpenInCarrier P K₁)
    (hK₂op : Work.SurgeryInvariance.IsOpenInCarrier P K₂)
    (hK₁pc : IsPathConnected K₁) (hK₂pc : IsPathConnected K₂)
    (hdisj : Disjoint K₁ K₂)
    (hinter : D.interior ∩ Work.BoxShrink.Core.upperRegion P s c σ u = K₁ ∪ K₂) :
    ∃ v : ℚ × ℚ, v ≠ 0 ∧
      Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ⊓
        Submodule.span ℚ ({v} : Set (ℚ × ℚ)) ≤
      Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) := by
  have hfr : Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.upperRegion P s c σ u ∪ D.interior)) ≤ 1 :=
    finrank_upperRegion_union_discInterior_le_one_of_pair P s c σ u D h0
      hK₁op hK₂op hK₁pc hK₂pc hdisj hinter
  have hle := windingSpan_boxRegion_le_sup_of_disc_thickenings P s c σ u D hslice
  rw [hbot, sup_bot_eq] at hle
  have hfrΩ : Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.boxRegion P s c σ)) ≤ 1 :=
    le_trans (Submodule.finrank_mono hle) hfr
  obtain ⟨v, hv0, hvbot⟩ := exists_ne_zero_inf_span_le_of_finrank_le_one hfrΩ
  exact ⟨v, hv0, by rw [h0]; exact le_of_eq hvbot⟩

/-- **The new case, with the grounding hypothesis discharged from the disjointness of the two
pieces**: if the two pieces of `Ω⁺ ∩ D°` are *not* joined inside `Ω⁺`, then the upper thickening is
inessential. -/
theorem wall_core_of_upper_pieces_not_joined_of_lower_pair
    (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (D : Work.SurgeryInvariance.DiscRegion P)
    (_hD : D.carrier ⊆ Work.PinchLemma3.closedBoxRegion P s c σ)
    (hslice : Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ D.interior)
    (_hT : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Pinch.planeTrace P c σ u) = ⊥)
    (h0 : Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) = ⊥)
    {K₁ K₂ : Set R3}
    (hK₁op : Work.SurgeryInvariance.IsOpenInCarrier P K₁)
    (hK₂op : Work.SurgeryInvariance.IsOpenInCarrier P K₂)
    (hK₁pc : IsPathConnected K₁) (hK₂pc : IsPathConnected K₂)
    (hdisj : Disjoint K₁ K₂)
    (hinterUp : D.interior ∩ Work.BoxShrink.Core.upperRegion P s c σ u = K₁ ∪ K₂)
    {a₀ b₀ : R3} (ha₀ : a₀ ∈ K₁) (hb₀ : b₀ ∈ K₂)
    (hno : ¬ JoinedIn (Work.BoxShrink.Core.upperRegion P s c σ u) a₀ b₀)
    {L₁ L₂ : Set R3}
    (hL₁op : Work.SurgeryInvariance.IsOpenInCarrier P L₁)
    (hL₂op : Work.SurgeryInvariance.IsOpenInCarrier P L₂)
    (hL₁pc : IsPathConnected L₁) (hL₂pc : IsPathConnected L₂)
    (hdisjL : Disjoint L₁ L₂)
    (hinterLo : D.interior ∩ Work.BoxShrink.Core.lowerRegion P s c σ u = L₁ ∪ L₂) :
    ∃ v : ℚ × ℚ, v ≠ 0 ∧
      Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ⊓
        Submodule.span ℚ ({v} : Set (ℚ × ℚ)) ≤
      Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) :=
  wall_core_of_upper_grounded_of_lower_pair P s c σ u D _hD hslice _hT h0
    (joinedIn_inter_of_not_joinedIn
      (A := Work.BoxShrink.Core.upperRegion P s c σ u) (B := D.interior)
      (K₁ := K₁) (K₂ := K₂) (Set.inter_comm D.interior _ ▸ hinterUp) hK₁pc hK₂pc ha₀ hb₀ hno)
    hL₁op hL₂op hL₁pc hL₂pc hdisjL hinterLo

/-- **The general one-sided reduction**: as soon as *one* of the two thickenings is inessential, the
box region's span is contained in the other thickening's span. -/
theorem windingSpan_boxRegion_le_lowerThickening_of_upperThickening_bot
    (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (D : Work.SurgeryInvariance.DiscRegion P)
    (hslice : Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ D.interior)
    (hbot : Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.upperRegion P s c σ u ∪ D.interior) = ⊥) :
    Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ≤
      Work.SurgeryInvariance.WindingSpan P
        (Work.BoxShrink.Core.lowerRegion P s c σ u ∪ D.interior) := by
  have hle := windingSpan_boxRegion_le_sup_of_disc_thickenings P s c σ u D hslice
  rwa [hbot, bot_sup_eq] at hle

/-- **The general one-sided reduction, other side.** -/
theorem windingSpan_boxRegion_le_upperThickening_of_lowerThickening_bot
    (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (D : Work.SurgeryInvariance.DiscRegion P)
    (hslice : Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ D.interior)
    (hbot : Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.lowerRegion P s c σ u ∪ D.interior) = ⊥) :
    Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ≤
      Work.SurgeryInvariance.WindingSpan P
        (Work.BoxShrink.Core.upperRegion P s c σ u ∪ D.interior) := by
  have hle := windingSpan_boxRegion_le_sup_of_disc_thickenings P s c σ u D
    (hslice := hslice)
  rwa [hbot, sup_bot_eq] at hle

/-- **The components form of the two-piece bound for the lower thickening**: it suffices that
`Ω⁻ ∩ D°` is covered by the components of two of its points and that the second point does not lie
in the first component. -/
theorem finrank_lowerRegion_union_discInterior_le_one_of_two_components
    (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (D : Work.SurgeryInvariance.DiscRegion P)
    (h0 : Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) = ⊥)
    {x y : R3} (hx : x ∈ D.interior ∩ Work.BoxShrink.Core.lowerRegion P s c σ u)
    (hy : y ∈ D.interior ∩ Work.BoxShrink.Core.lowerRegion P s c σ u)
    (hne : y ∉ connectedComponentIn
      (D.interior ∩ Work.BoxShrink.Core.lowerRegion P s c σ u) x)
    (hcov : D.interior ∩ Work.BoxShrink.Core.lowerRegion P s c σ u =
      connectedComponentIn (D.interior ∩ Work.BoxShrink.Core.lowerRegion P s c σ u) x ∪
        connectedComponentIn (D.interior ∩ Work.BoxShrink.Core.lowerRegion P s c σ u) y) :
    Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.lowerRegion P s c σ u ∪ D.interior)) ≤ 1 := by
  have hLc : Work.BoxShrink.Core.lowerRegion P s c σ u ⊆ P.carrier :=
    fun z hz => (Work.BoxShrink.Core.lowerRegion_subset P s c σ u hz).1
  have hZc : D.interior ∩ Work.BoxShrink.Core.lowerRegion P s c σ u ⊆ P.carrier :=
    Set.inter_subset_right.trans hLc
  have hZop : Work.SurgeryInvariance.IsOpenInCarrier P
      (D.interior ∩ Work.BoxShrink.Core.lowerRegion P s c σ u) :=
    Work.SurgeryInvariance.isOpenInCarrier_inter (P := P) D.open_interior'
      (Work.BoxShrink.Core.isOpenInCarrier_lowerRegion P s c σ u)
  have hdisj : Disjoint
      (connectedComponentIn (D.interior ∩ Work.BoxShrink.Core.lowerRegion P s c σ u) x)
      (connectedComponentIn (D.interior ∩ Work.BoxShrink.Core.lowerRegion P s c σ u) y) := by
    rw [Set.disjoint_left]
    intro z hz1 hz2
    have h1 : connectedComponentIn (D.interior ∩ Work.BoxShrink.Core.lowerRegion P s c σ u) x =
        connectedComponentIn (D.interior ∩ Work.BoxShrink.Core.lowerRegion P s c σ u) y :=
      (connectedComponentIn_eq hz1).trans (connectedComponentIn_eq hz2).symm
    exact hne (h1.symm ▸ mem_connectedComponentIn hy)
  exact finrank_lowerRegion_union_discInterior_le_one_of_pair P s c σ u D h0
    (isOpenInCarrier_connectedComponentIn hZop hZc x)
    (isOpenInCarrier_connectedComponentIn hZop hZc y)
    (isPathConnected_connectedComponentIn_carrier hZop hZc hx)
    (isPathConnected_connectedComponentIn_carrier hZop hZc hy)
    hdisj (Set.inter_comm _ _ ▸ hcov)

/-- **The new case in components form, ready for the geometric configuration**: if the two pieces of
`Ω⁻ ∩ D°` are given as the components of two of its points, and the upper thickening is
inessential, then `wall_core`'s conclusion holds. -/
theorem wall_core_of_upper_thickening_bot_of_lower_two_components
    (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (D : Work.SurgeryInvariance.DiscRegion P)
    (_hD : D.carrier ⊆ Work.PinchLemma3.closedBoxRegion P s c σ)
    (hslice : Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ D.interior)
    (_hT : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Pinch.planeTrace P c σ u) = ⊥)
    (h0 : Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) = ⊥)
    (hbot : Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.upperRegion P s c σ u ∪ D.interior) = ⊥)
    {x y : R3}
    (hx : x ∈ D.interior ∩ Work.BoxShrink.Core.lowerRegion P s c σ u)
    (hy : y ∈ D.interior ∩ Work.BoxShrink.Core.lowerRegion P s c σ u)
    (hne : y ∉ connectedComponentIn
      (D.interior ∩ Work.BoxShrink.Core.lowerRegion P s c σ u) x)
    (hcov : D.interior ∩ Work.BoxShrink.Core.lowerRegion P s c σ u =
      connectedComponentIn (D.interior ∩ Work.BoxShrink.Core.lowerRegion P s c σ u) x ∪
        connectedComponentIn (D.interior ∩ Work.BoxShrink.Core.lowerRegion P s c σ u) y) :
    ∃ v : ℚ × ℚ, v ≠ 0 ∧
      Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ⊓
        Submodule.span ℚ ({v} : Set (ℚ × ℚ)) ≤
      Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) := by
  have hle := windingSpan_boxRegion_le_lowerThickening_of_upperThickening_bot P s c σ u D
    (hslice := hslice) hbot
  have hfr : Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.lowerRegion P s c σ u ∪ D.interior)) ≤ 1 :=
    finrank_lowerRegion_union_discInterior_le_one_of_two_components P s c σ u D h0
      hx hy hne hcov
  have hfrΩ : Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.boxRegion P s c σ)) ≤ 1 :=
    le_trans (Submodule.finrank_mono hle) hfr
  obtain ⟨v, hv0, hvbot⟩ := exists_ne_zero_inf_span_le_of_finrank_le_one hfrΩ
  exact ⟨v, hv0, by rw [h0]; exact le_of_eq hvbot⟩

/-- **The decoupled form of the new case**: if the upper thickening is inessential and *any*
argument bounds `finrank W(Ω⁻ ∪ D°) ≤ 1`, then `wall_core`'s conclusion holds.  This is the
interface through which the two-piece bound, the components form, or a future "spread over
components of `Ω⁻`" bound (which improves `m₋ − 1` when the pieces of `Ω⁻ ∩ D°` are not all in one
path component of `Ω⁻`) are consumed. -/
theorem wall_core_of_upper_thickening_bot_of_lower_finrank_le_one
    (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (D : Work.SurgeryInvariance.DiscRegion P)
    (_hD : D.carrier ⊆ Work.PinchLemma3.closedBoxRegion P s c σ)
    (hslice : Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ D.interior)
    (_hT : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Pinch.planeTrace P c σ u) = ⊥)
    (h0 : Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) = ⊥)
    (hbot : Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.upperRegion P s c σ u ∪ D.interior) = ⊥)
    (hlow : Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.lowerRegion P s c σ u ∪ D.interior)) ≤ 1) :
    ∃ v : ℚ × ℚ, v ≠ 0 ∧
      Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ⊓
        Submodule.span ℚ ({v} : Set (ℚ × ℚ)) ≤
      Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) := by
  have hle := windingSpan_boxRegion_le_lowerThickening_of_upperThickening_bot P s c σ u D
    (hslice := hslice) hbot
  have hfrΩ : Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.boxRegion P s c σ)) ≤ 1 :=
    le_trans (Submodule.finrank_mono hle) hlow
  obtain ⟨v, hv0, hvbot⟩ := exists_ne_zero_inf_span_le_of_finrank_le_one hfrΩ
  exact ⟨v, hv0, by rw [h0]; exact le_of_eq hvbot⟩

/-- **The decoupled form of the new case, other side.** -/
theorem wall_core_of_lower_thickening_bot_of_upper_finrank_le_one
    (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (D : Work.SurgeryInvariance.DiscRegion P)
    (_hD : D.carrier ⊆ Work.PinchLemma3.closedBoxRegion P s c σ)
    (hslice : Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ D.interior)
    (_hT : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Pinch.planeTrace P c σ u) = ⊥)
    (h0 : Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) = ⊥)
    (hbot : Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.lowerRegion P s c σ u ∪ D.interior) = ⊥)
    (hup : Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.upperRegion P s c σ u ∪ D.interior)) ≤ 1) :
    ∃ v : ℚ × ℚ, v ≠ 0 ∧
      Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ⊓
        Submodule.span ℚ ({v} : Set (ℚ × ℚ)) ≤
      Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) := by
  have hle := windingSpan_boxRegion_le_upperThickening_of_lowerThickening_bot P s c σ u D
    (hslice := hslice) hbot
  have hfrΩ : Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.boxRegion P s c σ)) ≤ 1 :=
    le_trans (Submodule.finrank_mono hle) hup
  obtain ⟨v, hv0, hvbot⟩ := exists_ne_zero_inf_span_le_of_finrank_le_one hfrΩ
  exact ⟨v, hv0, by rw [h0]; exact le_of_eq hvbot⟩

/-- **A half-region whose intersection with the disc's interior is *one* path connected piece has
inessential thickening.**  (`windingSpan_eq_bot_of_subset_union` with `A = Ω⁻`, `B = D°`.) -/
theorem windingSpan_lowerRegion_union_discInterior_eq_bot_of_single
    (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (D : Work.SurgeryInvariance.DiscRegion P)
    (h0 : Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) = ⊥)
    {K : Set R3} (hKpc : IsPathConnected K)
    (hinter : D.interior ∩ Work.BoxShrink.Core.lowerRegion P s c σ u = K) :
    Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.lowerRegion P s c σ u ∪ D.interior) = ⊥ := by
  have hLc : Work.BoxShrink.Core.lowerRegion P s c σ u ⊆ P.carrier :=
    fun z hz => (Work.BoxShrink.Core.lowerRegion_subset P s c σ u hz).1
  have hVL : Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.lowerRegion P s c σ u) = ⊥ :=
    le_bot_iff.mp (le_trans (Work.SurgeryInvariance.WindingSpan_mono P
      (Set.subset_union_right : Work.BoxShrink.Core.lowerRegion P s c σ u ⊆
        Work.PinchLemma3.halfRegions P s c σ u)) (le_of_eq h0))
  refine windingSpan_eq_bot_of_subset_union (P := P)
    (X := Work.BoxShrink.Core.lowerRegion P s c σ u ∪ D.interior)
    (A := Work.BoxShrink.Core.lowerRegion P s c σ u) (B := D.interior)
    hLc (discRegion_interior_subset_carrier D)
    (Work.BoxShrink.Core.isOpenInCarrier_lowerRegion P s c σ u) D.open_interior' ?_ hVL
    D.windingSpan_interior_eq_bot (le_refl _)
  intro x hx y hy
  have hxK : x ∈ K := hinter ▸ (Set.inter_comm _ _ ▸ hx)
  have hyK : y ∈ K := hinter ▸ (Set.inter_comm _ _ ▸ hy)
  exact (joinedIn_of_isPathConnected hKpc x hxK y hyK).mono
    (fun z hz => Set.inter_comm _ _ ▸ (hinter.symm ▸ hz))

/-- **The upper analogue**: one piece on the lower side, three pieces on the upper side split over a
two-piece open splitting of `Ω⁺`, gives `wall_core`'s conclusion.  This is a **new covered case of
the residual**, with four pieces of `D° ∖ Σ` (three chords) arranged in the `3 + 1` distribution over
the sides. -/
theorem wall_core_of_lower_single_of_upper_three_split
    (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (D : Work.SurgeryInvariance.DiscRegion P)
    (_hD : D.carrier ⊆ Work.PinchLemma3.closedBoxRegion P s c σ)
    (hslice : Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ D.interior)
    (_hT : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Pinch.planeTrace P c σ u) = ⊥)
    (h0 : Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) = ⊥)
    {K₁ K₂ K₃ : Set R3}
    (hK₁op : Work.SurgeryInvariance.IsOpenInCarrier P K₁)
    (hK₂op : Work.SurgeryInvariance.IsOpenInCarrier P K₂)
    (hK₃op : Work.SurgeryInvariance.IsOpenInCarrier P K₃)
    (hK₁pc : IsPathConnected K₁) (hK₂pc : IsPathConnected K₂) (hK₃pc : IsPathConnected K₃)
    (hdisj₁₂ : Disjoint K₁ K₂) (hdisj₁₃ : Disjoint K₁ K₃) (hdisj₂₃ : Disjoint K₂ K₃)
    (hinterUp : D.interior ∩ Work.BoxShrink.Core.upperRegion P s c σ u = K₁ ∪ K₂ ∪ K₃)
    {U₁ U₂ : Set R3}
    (hU₁op : Work.SurgeryInvariance.IsOpenInCarrier P U₁)
    (hU₂op : Work.SurgeryInvariance.IsOpenInCarrier P U₂)
    (hU₁pc : IsPathConnected U₁) (hU₂pc : IsPathConnected U₂)
    (hUdisj : Disjoint U₁ U₂)
    (hcov : Work.BoxShrink.Core.upperRegion P s c σ u ⊆ U₁ ∪ U₂)
    (hUsub : U₁ ∪ U₂ ⊆ Work.BoxShrink.Core.upperRegion P s c σ u)
    (hK₁U₁ : K₁ ⊆ U₁) (hK₂U₁ : K₂ ⊆ U₁) (hK₃U₂ : K₃ ⊆ U₂)
    {L : Set R3} (hLpc : IsPathConnected L)
    (hinterLo : D.interior ∩ Work.BoxShrink.Core.lowerRegion P s c σ u = L) :
    ∃ v : ℚ × ℚ, v ≠ 0 ∧
      Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ⊓
        Submodule.span ℚ ({v} : Set (ℚ × ℚ)) ≤
      Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) :=
  wall_core_of_lower_thickening_bot_of_upper_finrank_le_one P s c σ u D _hD hslice _hT h0
    (windingSpan_lowerRegion_union_discInterior_eq_bot_of_single P s c σ u D h0 hLpc hinterLo)
    (finrank_upperRegion_union_discInterior_le_one_of_three_pieces_split P s c σ u D h0
      hK₁op hK₂op hK₃op hK₁pc hK₂pc hK₃pc hdisj₁₂ hdisj₁₃ hdisj₂₃ hinterUp
      hU₁op hU₂op hU₁pc hU₂pc hUdisj hcov hUsub hK₁U₁ hK₂U₁ hK₃U₂)

/-- **The upper analogue of the one-piece criterion**: a half-region whose intersection with the
disc's interior is a single path connected piece has inessential thickening. -/
theorem windingSpan_upperRegion_union_discInterior_eq_bot_of_single
    (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (D : Work.SurgeryInvariance.DiscRegion P)
    (h0 : Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) = ⊥)
    {K : Set R3} (hKpc : IsPathConnected K)
    (hinter : D.interior ∩ Work.BoxShrink.Core.upperRegion P s c σ u = K) :
    Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.upperRegion P s c σ u ∪ D.interior) = ⊥ := by
  have hUc : Work.BoxShrink.Core.upperRegion P s c σ u ⊆ P.carrier :=
    fun z hz => (Work.BoxShrink.Core.upperRegion_subset P s c σ u hz).1
  have hVU : Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.upperRegion P s c σ u) = ⊥ :=
    le_bot_iff.mp (le_trans (Work.SurgeryInvariance.WindingSpan_mono P
      (Set.subset_union_left : Work.BoxShrink.Core.upperRegion P s c σ u ⊆
        Work.PinchLemma3.halfRegions P s c σ u)) (le_of_eq h0))
  refine windingSpan_eq_bot_of_subset_union (P := P)
    (X := Work.BoxShrink.Core.upperRegion P s c σ u ∪ D.interior)
    (A := Work.BoxShrink.Core.upperRegion P s c σ u) (B := D.interior)
    hUc (discRegion_interior_subset_carrier D)
    (Work.BoxShrink.Core.isOpenInCarrier_upperRegion P s c σ u) D.open_interior' ?_ hVU
    D.windingSpan_interior_eq_bot (le_refl _)
  intro x hx y hy
  have hxK : x ∈ K := hinter ▸ (Set.inter_comm _ _ ▸ hx)
  have hyK : y ∈ K := hinter ▸ (Set.inter_comm _ _ ▸ hy)
  exact (joinedIn_of_isPathConnected hKpc x hxK y hyK).mono
    (fun z hz => Set.inter_comm _ _ ▸ (hinter.symm ▸ hz))

/-- **The mirror of `wall_core_of_lower_single_of_upper_three_split`**: one piece on the *upper*
side, three pieces on the *lower* side split over a two-piece open splitting of `Ω⁻`, where the
one-class bound for `W(Ω⁻ ∪ D°)` is supplied as a hypothesis (its three-piece-split form is the
sibling lemma `finrank_lowerRegion_union_discInterior_le_one_of_three_pieces_split`, the mirror of
the `upperRegion` one; the assembly here is the interface through which it is consumed). -/
theorem wall_core_of_upper_single_of_lower_three_split
    (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (D : Work.SurgeryInvariance.DiscRegion P)
    (_hD : D.carrier ⊆ Work.PinchLemma3.closedBoxRegion P s c σ)
    (hslice : Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ D.interior)
    (_hT : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Pinch.planeTrace P c σ u) = ⊥)
    (h0 : Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) = ⊥)
    {K : Set R3} (hKpc : IsPathConnected K)
    (hinterUp : D.interior ∩ Work.BoxShrink.Core.upperRegion P s c σ u = K)
    (hlow : Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.lowerRegion P s c σ u ∪ D.interior)) ≤ 1) :
    ∃ v : ℚ × ℚ, v ≠ 0 ∧
      Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ⊓
        Submodule.span ℚ ({v} : Set (ℚ × ℚ)) ≤
      Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) :=
  wall_core_of_upper_thickening_bot_of_lower_finrank_le_one P s c σ u D _hD hslice _hT h0
    (windingSpan_upperRegion_union_discInterior_eq_bot_of_single P s c σ u D h0 hKpc hinterUp)
    hlow
/-! ## The *avoiding-curve* criterion: a second route to the residual

`ne_top_of_disjoint_essential` shows that a region admitting a disjoint curve of nonzero winding has
span contained in a line.  Factoring that argument out gives the criterion

  `W(X) ≤ ℚ·w(δ)`   whenever `δ` is a closed curve of the torus avoiding `X` with `windingOf δ ≠ 0`
  (`windingSpan_le_span_of_avoiding_curve`),

for *any* set `X`, and hence `finrank W(X) ≤ 1`.  Applying it to the two thickenings
`A = Ω⁺ ∪ D°`, `B = Ω⁻ ∪ D°` of the two-thickening reduction, and using the disjointness of the two
avoiding curves (`winding_dependent_of_disjoint_curves`, proved), gives a **second sufficient
condition for `wall_core`** — one that never mentions the slice, the trace or the pieces of
`D° ∖ Σ`:

> **(E′)** there are closed curves `δ₁` avoiding `Ω⁺ ∪ D°` and `δ₂` avoiding `Ω⁻ ∪ D°`, disjoint from
> each other, both of nonzero winding;

then `W(Ω) ≤ W(A) ⊔ W(B) ≤ ℚw(δ₁) ⊔ ℚw(δ₂) = ℚw(δ₁)`, so `finrank W(Ω) ≤ 1` and `wall_core`
follows.  Since `F ∖ (Ω^± ∪ D°) = (Ω^∓ ∖ D°) ∪ S ∪ caps`, hypothesis **(E′)** is *not* implied by
the residual's hypotheses (`W(F ∖ Ω) = W(S) = W(caps) = ⊥`); it is an independent sufficient
condition, and it is the natural home of the "the complement of the thickening is essential"
configurations. -/

/-- **The avoiding-curve criterion.**  A closed curve `δ` of the torus avoiding `X`, with nonzero
winding, confines the winding span of `X` to a line: every loop of `X` has its winding vector
proportional to that of `δ`.  (This is the content of the proof of
`ne_top_of_disjoint_essential`, isolated.) -/
theorem windingSpan_le_span_of_avoiding_curve (P : Work.CoreTopology.ParamTorus) {X : Set R3}
    (hX : X ⊆ P.carrier) {δ : Work.CoreTopology.ClosedCurve P}
    (hdis : ∀ t : ℝ, δ.γ t ∉ X)
    (hδ : Work.SurgeryInvariance.windingOf P δ ≠ (0, 0)) :
    Work.SurgeryInvariance.WindingSpan P X ≤
      Submodule.span ℚ ({((((Work.SurgeryInvariance.windingOf P δ).1 : ℤ) : ℚ),
        (((Work.SurgeryInvariance.windingOf P δ).2 : ℤ) : ℚ))} : Set (ℚ × ℚ)) := by
  set w : ℚ × ℚ := ((((Work.SurgeryInvariance.windingOf P δ).1 : ℤ) : ℚ),
      (((Work.SurgeryInvariance.windingOf P δ).2 : ℤ) : ℚ)) with hw
  have hwne : w ≠ 0 := by
    rw [hw]
    intro h0
    exact hδ (Work.SurgeryInvariance.intPair_cast_eq_zero_iff _ |>.mp h0)
  rw [Work.SurgeryInvariance.WindingSpan, Submodule.span_le]
  rintro v ⟨γ, hγ, rfl⟩
  have hdet : (((Work.SurgeryInvariance.windingOf P γ).1 : ℤ) : ℚ)
        * (((Work.SurgeryInvariance.windingOf P δ).2 : ℤ) : ℚ)
      = (((Work.SurgeryInvariance.windingOf P γ).2 : ℤ) : ℚ)
        * (((Work.SurgeryInvariance.windingOf P δ).1 : ℤ) : ℚ) := by
    have h := winding_dependent_of_disjoint_curves (P := P) (γ := γ) (δ := δ)
      (fun s t hcon => hdis t (hcon ▸ hγ s))
    exact_mod_cast h
  exact mem_span_singleton_of_det_eq_zero (b := w) (by rw [hw]; exact hdet) hwne

/-- **`wall_core` from a pair of disjoint avoiding curves** — the second sufficient condition of the
residual, requiring no hypothesis on the slice, the trace or the pieces of `D° ∖ Σ`. -/
theorem wall_core_of_avoiding_curves
    (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (D : Work.SurgeryInvariance.DiscRegion P)
    (_hD : D.carrier ⊆ Work.PinchLemma3.closedBoxRegion P s c σ)
    (hslice : Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ D.interior)
    (_hT : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Pinch.planeTrace P c σ u) = ⊥)
    (h0 : Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) = ⊥)
    {δ₁ δ₂ : Work.CoreTopology.ClosedCurve P}
    (hδ₁ : ∀ t : ℝ, δ₁.γ t ∉
      Work.BoxShrink.Core.upperRegion P s c σ u ∪ D.interior)
    (hδ₂ : ∀ t : ℝ, δ₂.γ t ∉
      Work.BoxShrink.Core.lowerRegion P s c σ u ∪ D.interior)
    (hdisj : ∀ s t : ℝ, δ₁.γ s ≠ δ₂.γ t)
    (hw₁ : Work.SurgeryInvariance.windingOf P δ₁ ≠ (0, 0))
    (hw₂ : Work.SurgeryInvariance.windingOf P δ₂ ≠ (0, 0)) :
    ∃ v : ℚ × ℚ, v ≠ 0 ∧
      Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ⊓
        Submodule.span ℚ ({v} : Set (ℚ × ℚ)) ≤
      Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) := by
  set w₁ : ℚ × ℚ := ((((Work.SurgeryInvariance.windingOf P δ₁).1 : ℤ) : ℚ),
      (((Work.SurgeryInvariance.windingOf P δ₁).2 : ℤ) : ℚ)) with hw₁def
  set w₂ : ℚ × ℚ := ((((Work.SurgeryInvariance.windingOf P δ₂).1 : ℤ) : ℚ),
      (((Work.SurgeryInvariance.windingOf P δ₂).2 : ℤ) : ℚ)) with hw₂def
  have hw₁ne : w₁ ≠ 0 := by
    rw [hw₁def]
    intro h
    exact hw₁ (Work.SurgeryInvariance.intPair_cast_eq_zero_iff _ |>.mp h)
  have hraw : (((Work.SurgeryInvariance.windingOf P δ₂).1 : ℤ) : ℚ)
        * (((Work.SurgeryInvariance.windingOf P δ₁).2 : ℤ) : ℚ)
      = (((Work.SurgeryInvariance.windingOf P δ₂).2 : ℤ) : ℚ)
        * (((Work.SurgeryInvariance.windingOf P δ₁).1 : ℤ) : ℚ) := by
    have h := winding_dependent_of_disjoint_curves (P := P) (γ := δ₁) (δ := δ₂) hdisj
    have h2 : (((Work.SurgeryInvariance.windingOf P δ₁).1 : ℤ) : ℚ)
          * (((Work.SurgeryInvariance.windingOf P δ₂).2 : ℤ) : ℚ)
        = (((Work.SurgeryInvariance.windingOf P δ₁).2 : ℤ) : ℚ)
          * (((Work.SurgeryInvariance.windingOf P δ₂).1 : ℤ) : ℚ) := by
      exact_mod_cast h
    rw [mul_comm (((Work.SurgeryInvariance.windingOf P δ₂).1 : ℤ) : ℚ)
        (((Work.SurgeryInvariance.windingOf P δ₁).2 : ℤ) : ℚ),
      mul_comm (((Work.SurgeryInvariance.windingOf P δ₂).2 : ℤ) : ℚ)
        (((Work.SurgeryInvariance.windingOf P δ₁).1 : ℤ) : ℚ)]
    exact h2.symm
  have hdet' : w₂.1 * w₁.2 = w₂.2 * w₁.1 := by
    rw [hw₁def, hw₂def]
    simpa only [Prod.fst, Prod.snd] using hraw
  have hw₂mem : w₂ ∈ Submodule.span ℚ ({w₁} : Set (ℚ × ℚ)) :=
    mem_span_singleton_of_det_eq_zero (a := w₂) (b := w₁) hdet' hw₁ne
  have hA : Work.BoxShrink.Core.upperRegion P s c σ u ∪ D.interior ⊆ P.carrier :=
    Set.union_subset (fun x hx => (Work.BoxShrink.Core.upperRegion_subset P s c σ u hx).1)
      (discRegion_interior_subset_carrier D)
  have hB : Work.BoxShrink.Core.lowerRegion P s c σ u ∪ D.interior ⊆ P.carrier :=
    Set.union_subset (fun x hx => (Work.BoxShrink.Core.lowerRegion_subset P s c σ u hx).1)
      (discRegion_interior_subset_carrier D)
  have h2 := windingSpan_boxRegion_le_sup_of_disc_thickenings P s c σ u D hslice
  have h3 : Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.upperRegion P s c σ u ∪ D.interior) ⊔
      Work.SurgeryInvariance.WindingSpan P
        (Work.BoxShrink.Core.lowerRegion P s c σ u ∪ D.interior) ≤
      Submodule.span ℚ ({w₁} : Set (ℚ × ℚ)) := by
    refine sup_le (windingSpan_le_span_of_avoiding_curve (P := P) hA hδ₁ hw₁) ?_
    refine le_trans (windingSpan_le_span_of_avoiding_curve (P := P) hB hδ₂ hw₂) ?_
    refine Submodule.span_le.mpr ?_
    rintro y hy
    rw [Set.mem_singleton_iff] at hy
    exact hy ▸ hw₂mem
  have hle : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ≤
      Submodule.span ℚ ({w₁} : Set (ℚ × ℚ)) := le_trans h2 h3
  have hfr : Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.boxRegion P s c σ)) ≤ 1 := by
    have hmono := Submodule.finrank_mono hle
    rw [finrank_span_singleton hw₁ne] at hmono
    exact hmono
  obtain ⟨v, hv0, hvbot⟩ := exists_ne_zero_inf_span_le_of_finrank_le_one hfr
  exact ⟨v, hv0, by rw [h0]; exact le_of_eq hvbot⟩

/-- **The `1 + 3` distribution, fully instantiated** (the mirror of
`wall_core_of_lower_single_of_upper_three_split`): one piece of `Ω⁺ ∩ D°`, three pieces of
`Ω⁻ ∩ D°` split `2 + 1` over a two-piece open splitting of `Ω⁻`, gives `wall_core`'s conclusion.
Together with `wall_core_of_lower_single_of_upper_three_split` this covers the whole `3 + 1` half of
the four-piece regime in which the three pieces of one side are **not** all in one path component of
that side. -/
theorem wall_core_of_upper_single_of_lower_three_split_components
    (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (D : Work.SurgeryInvariance.DiscRegion P)
    (_hD : D.carrier ⊆ Work.PinchLemma3.closedBoxRegion P s c σ)
    (hslice : Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ D.interior)
    (_hT : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Pinch.planeTrace P c σ u) = ⊥)
    (h0 : Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) = ⊥)
    {K : Set R3} (hKpc : IsPathConnected K)
    (hinterUp : D.interior ∩ Work.BoxShrink.Core.upperRegion P s c σ u = K)
    {K₁ K₂ K₃ : Set R3}
    (hK₁op : Work.SurgeryInvariance.IsOpenInCarrier P K₁)
    (hK₂op : Work.SurgeryInvariance.IsOpenInCarrier P K₂)
    (hK₃op : Work.SurgeryInvariance.IsOpenInCarrier P K₃)
    (hK₁pc : IsPathConnected K₁) (hK₂pc : IsPathConnected K₂) (hK₃pc : IsPathConnected K₃)
    (hdisj₁₂ : Disjoint K₁ K₂) (hdisj₁₃ : Disjoint K₁ K₃) (hdisj₂₃ : Disjoint K₂ K₃)
    (hinterLo : D.interior ∩ Work.BoxShrink.Core.lowerRegion P s c σ u = K₁ ∪ K₂ ∪ K₃)
    {U₁ U₂ : Set R3}
    (hU₁op : Work.SurgeryInvariance.IsOpenInCarrier P U₁)
    (hU₂op : Work.SurgeryInvariance.IsOpenInCarrier P U₂)
    (hU₁pc : IsPathConnected U₁) (hU₂pc : IsPathConnected U₂)
    (hUdisj : Disjoint U₁ U₂)
    (hcov : Work.BoxShrink.Core.lowerRegion P s c σ u ⊆ U₁ ∪ U₂)
    (hUsub : U₁ ∪ U₂ ⊆ Work.BoxShrink.Core.lowerRegion P s c σ u)
    (hK₁U₁ : K₁ ⊆ U₁) (hK₂U₁ : K₂ ⊆ U₁) (hK₃U₂ : K₃ ⊆ U₂) :
    ∃ v : ℚ × ℚ, v ≠ 0 ∧
      Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ⊓
        Submodule.span ℚ ({v} : Set (ℚ × ℚ)) ≤
      Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) :=
  wall_core_of_upper_single_of_lower_three_split P s c σ u D _hD hslice _hT h0 hKpc hinterUp
    (finrank_lowerRegion_union_discInterior_le_one_of_three_pieces_split P s c σ u D h0
      hK₁op hK₂op hK₃op hK₁pc hK₂pc hK₃pc hdisj₁₂ hdisj₁₃ hdisj₂₃ hinterLo
      hU₁op hU₂op hU₁pc hU₂pc hUdisj hcov hUsub hK₁U₁ hK₂U₁ hK₃U₂)

/-! ## The final assembly interface: two disjoint curves spanning the two thickenings

With the two-thickening reduction, the whole `(D″)` case reduces to the following *linear algebra +
disjointness* statement: if the two thickenings' spans are contained in the lines of two curves that
are disjoint from each other, then `wall_core` holds — because
`winding_dependent_of_disjoint_curves` (proved) makes the two windings proportional, so the two lines
together are one line.  The two span hypotheses are what
`Work.PinchLemma3.ClosedDiscA.windingOf_switch_ne_zero` (together with the two-piece bound
`finrank W(Ω^± ∪ D°) ≤ 1`) supplies for the switch loops; `exists_disjoint_switch_loops` is to supply
the disjointness. -/

/-- **`wall_core` from two disjoint curves whose windings span the two thickenings.** -/
theorem wall_core_of_disjoint_spanning_curves
    (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (D : Work.SurgeryInvariance.DiscRegion P)
    (_hD : D.carrier ⊆ Work.PinchLemma3.closedBoxRegion P s c σ)
    (hslice : Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ D.interior)
    (_hT : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Pinch.planeTrace P c σ u) = ⊥)
    (h0 : Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) = ⊥)
    {γ₁ γ₂ : Work.CoreTopology.ClosedCurve P}
    (hdisj : ∀ s t : ℝ, γ₁.γ s ≠ γ₂.γ t)
    (hspan₁ : Work.SurgeryInvariance.WindingSpan P
        (Work.BoxShrink.Core.upperRegion P s c σ u ∪ D.interior) ≤
      Submodule.span ℚ ({((((Work.SurgeryInvariance.windingOf P γ₁).1 : ℤ) : ℚ),
        (((Work.SurgeryInvariance.windingOf P γ₁).2 : ℤ) : ℚ))} : Set (ℚ × ℚ)))
    (hspan₂ : Work.SurgeryInvariance.WindingSpan P
        (Work.BoxShrink.Core.lowerRegion P s c σ u ∪ D.interior) ≤
      Submodule.span ℚ ({((((Work.SurgeryInvariance.windingOf P γ₂).1 : ℤ) : ℚ),
        (((Work.SurgeryInvariance.windingOf P γ₂).2 : ℤ) : ℚ))} : Set (ℚ × ℚ))) :
    ∃ v : ℚ × ℚ, v ≠ 0 ∧
      Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ⊓
        Submodule.span ℚ ({v} : Set (ℚ × ℚ)) ≤
      Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) := by
  set w₁ : ℚ × ℚ := ((((Work.SurgeryInvariance.windingOf P γ₁).1 : ℤ) : ℚ),
      (((Work.SurgeryInvariance.windingOf P γ₁).2 : ℤ) : ℚ)) with hw₁def
  set w₂ : ℚ × ℚ := ((((Work.SurgeryInvariance.windingOf P γ₂).1 : ℤ) : ℚ),
      (((Work.SurgeryInvariance.windingOf P γ₂).2 : ℤ) : ℚ)) with hw₂def
  have hraw : (((Work.SurgeryInvariance.windingOf P γ₂).1 : ℤ) : ℚ)
        * (((Work.SurgeryInvariance.windingOf P γ₁).2 : ℤ) : ℚ)
      = (((Work.SurgeryInvariance.windingOf P γ₂).2 : ℤ) : ℚ)
        * (((Work.SurgeryInvariance.windingOf P γ₁).1 : ℤ) : ℚ) := by
    have h := winding_dependent_of_disjoint_curves (P := P) (γ := γ₁) (δ := γ₂) hdisj
    have h2 : (((Work.SurgeryInvariance.windingOf P γ₁).1 : ℤ) : ℚ)
          * (((Work.SurgeryInvariance.windingOf P γ₂).2 : ℤ) : ℚ)
        = (((Work.SurgeryInvariance.windingOf P γ₁).2 : ℤ) : ℚ)
          * (((Work.SurgeryInvariance.windingOf P γ₂).1 : ℤ) : ℚ) := by
      exact_mod_cast h
    rw [mul_comm (((Work.SurgeryInvariance.windingOf P γ₂).1 : ℤ) : ℚ)
        (((Work.SurgeryInvariance.windingOf P γ₁).2 : ℤ) : ℚ),
      mul_comm (((Work.SurgeryInvariance.windingOf P γ₂).2 : ℤ) : ℚ)
        (((Work.SurgeryInvariance.windingOf P γ₁).1 : ℤ) : ℚ)]
    exact h2.symm
  have hdet' : w₂.1 * w₁.2 = w₂.2 * w₁.1 := by
    rw [hw₁def, hw₂def]
    simpa only [Prod.fst, Prod.snd] using hraw
  have hfr : Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.boxRegion P s c σ)) ≤ 1 := by
    refine le_trans (Submodule.finrank_mono (le_trans
      (windingSpan_boxRegion_le_sup_of_disc_thickenings P s c σ u D hslice)
      (sup_le (le_trans hspan₁ le_sup_left) (le_trans hspan₂ le_sup_right)))) ?_
    by_cases h1 : w₁ = 0
    · rw [h1, Submodule.span_zero_singleton, bot_sup_eq]
      by_cases h2 : w₂ = 0
      · rw [h2, Submodule.span_zero_singleton, finrank_bot]
        exact Nat.zero_le 1
      · rw [finrank_span_singleton h2]
    · have h2le : Submodule.span ℚ ({w₂} : Set (ℚ × ℚ)) ≤
          Submodule.span ℚ ({w₁} : Set (ℚ × ℚ)) :=
        Submodule.span_le.mpr (Set.singleton_subset_iff.mpr
          (mem_span_singleton_of_det_eq_zero (a := w₂) (b := w₁) hdet' h1))
      rw [sup_eq_left.mpr h2le, finrank_span_singleton h1]
  obtain ⟨v, hv0, hvbot⟩ := exists_ne_zero_inf_span_le_of_finrank_le_one hfr
  exact ⟨v, hv0, by rw [h0]; exact le_of_eq hvbot⟩

/-- **A one-dimensional span contains every subspace of dimension `≤ 1` that contains its
generator** — the step that upgrades `finrank W(Ω^± ∪ D°) ≤ 1` plus a nonzero switch-loop winding to
the span hypothesis of `wall_core_of_disjoint_spanning_curves`. -/
theorem le_span_singleton_of_finrank_le_one {W : Submodule ℚ (ℚ × ℚ)} {w : ℚ × ℚ}
    (hw : w ∈ W) (hne : w ≠ 0) (hfr : Module.finrank ℚ ↥W ≤ 1) :
    W ≤ Submodule.span ℚ ({w} : Set (ℚ × ℚ)) := by
  have hle : Submodule.span ℚ ({w} : Set (ℚ × ℚ)) ≤ W :=
    Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hw)
  have h1 : Module.finrank ℚ ↥(Submodule.span ℚ ({w} : Set (ℚ × ℚ))) = 1 :=
    finrank_span_singleton hne
  exact (Submodule.eq_of_le_of_finrank_le hle (by rw [h1]; exact hfr)).ge

end Work.PinchLemma3.ClosedDiscA
