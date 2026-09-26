import Submission.Work.SliceArcs.Route

/-!
# The canonical collar: the components of the box region through which the slice passes

The collar residual `ArcCollar` is an *existential*: there is a collar of the slice inside the box of
vanishing winding span.  This module identifies the canonical (smallest) such collar

  `collar P s c σ u` = the union of the connected components of the box region which meet the slice,

proves that it *is* a collar of the pinch, and proves the two facts which make it the canonical
choice:

* `isPinchCollar_collar` — it is open in the surface, contains the slice, lies in the box region, and
  its complement in the box region is open (the union of the remaining components);
* `collar_subset_of_isPinchCollar` — **minimality**: every collar of the pinch contains it.  A collar
  `Z` with open complement separates the region inside the box into the two disjoint open pieces `Z`
  and `box ∖ Z`; the connected component of the box region through a point of the slice is
  preconnected, so it must lie in one of the two pieces, and it contains the point of the slice,
  which lies in `Z`.

Consequently (a) a collar of vanishing span exists **iff** the canonical collar has vanishing span
(`spanCollarBody_iff_collar_span`), so the residual can be stated with the explicit witness rather
than existentially, and (b) that componentwise spelling is *equivalent* to `ArcCollar`
(`arcCollarComponent_iff_arcCollar`).  The componentwise form is the one to attack: it says that
Pardon's pinch can only create essential loops in the components of the box region that the slice
actually passes through.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.SliceArcs

noncomputable section

variable {P : Work.CoreTopology.ParamTorus} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}

/-! ## Unions of sets open in the surface -/

theorem isOpenInCarrier_iUnion {ι : Sort*} {X : ι → Set R3}
    (h : ∀ i, Work.SurgeryInvariance.IsOpenInCarrier P (X i)) :
    Work.SurgeryInvariance.IsOpenInCarrier P (⋃ i, X i) := by
  have h' : ∀ i, IsOpen ((Subtype.val : ↥P.carrier → R3) ⁻¹' X i) := h
  show IsOpen ((Subtype.val : ↥P.carrier → R3) ⁻¹' (⋃ i, X i))
  rw [Set.preimage_iUnion]
  exact isOpen_iUnion h'

theorem box_subset_carrier (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) : box P s c σ ⊆ P.carrier :=
  fun _ hy => (Work.BoxShrink.Core.mem_boxRegion.mp hy).1

/-- An open set of the surface is, on the surface, the trace of an open set of `ℝ³`. -/
theorem exists_isOpen_inter_carrier {X : Set R3}
    (h : Work.SurgeryInvariance.IsOpenInCarrier P X) :
    ∃ W : Set R3, IsOpen W ∧ X ∩ P.carrier = W ∩ P.carrier := by
  have h' : IsOpen ((Subtype.val : ↥P.carrier → R3) ⁻¹' X) := h
  obtain ⟨W, hW, hWX⟩ := isOpen_induced_iff.mp h'
  refine ⟨W, hW, ?_⟩
  have key : ∀ y (hy : y ∈ P.carrier), (y ∈ X ↔ y ∈ W) := by
    intro y hy
    have h1 : (⟨y, hy⟩ : ↥P.carrier) ∈ (Subtype.val : ↥P.carrier → R3) ⁻¹' X ↔
        (⟨y, hy⟩ : ↥P.carrier) ∈ (Subtype.val : ↥P.carrier → R3) ⁻¹' W := by
      rw [hWX]
    simpa using h1
  ext y
  constructor
  · rintro ⟨hyX, hyc⟩
    exact ⟨(key y hyc).mp hyX, hyc⟩
  · rintro ⟨hyW, hyc⟩
    exact ⟨(key y hyc).mpr hyW, hyc⟩

/-! ## The canonical collar -/

/-- **The slice lies in the canonical collar.** -/
theorem slice_subset_collar (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) : slice P s c σ u ⊆ collar P s c σ u := by
  intro y hy
  obtain ⟨hyc, hyb, _⟩ := Work.BoxShrink.Core.mem_sliceRegion.mp hy
  exact Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr
    ⟨hy, mem_connectedComponentIn (Work.BoxShrink.Core.mem_boxRegion.mpr ⟨hyc, hyb⟩)⟩⟩

/-- **Membership in the canonical collar**: a point of the surface lies in the collar exactly when
it lies in the connected component of the box region through some point of the slice. -/
theorem mem_collar {y : R3} :
    y ∈ collar P s c σ u ↔ ∃ x ∈ slice P s c σ u, y ∈ connectedComponentIn (box P s c σ) x := by
  simp [collar, Set.mem_iUnion, exists_prop]

/-- **The canonical collar is empty exactly when the slice is.** -/
theorem collar_eq_empty_iff : collar P s c σ u = ∅ ↔ slice P s c σ u = ∅ := by
  constructor
  · intro h
    by_contra hne
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
    have hxc : x ∈ collar P s c σ u := slice_subset_collar P s c σ u hx
    rw [h] at hxc
    exact hxc
  · intro h
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx, _⟩ := mem_collar.mp hy
      rw [h] at hx
      exact hx
    · intro hy
      exact absurd hy (Set.notMem_empty y)

/-- **The canonical collar lies in the box region.** -/
theorem collar_subset_box (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) : collar P s c σ u ⊆ box P s c σ := by
  intro y hy
  obtain ⟨x, hy'⟩ := Set.mem_iUnion.mp hy
  obtain ⟨_, hyx⟩ := Set.mem_iUnion.mp hy'
  exact connectedComponentIn_subset (box P s c σ) x hyx

/-- **The canonical collar is open in the surface**: it is a union of connected components of an
open subset of the locally connected surface. -/
theorem isOpenInCarrier_collar (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Work.SurgeryInvariance.IsOpenInCarrier P (collar P s c σ u) :=
  isOpenInCarrier_iUnion fun x =>
    isOpenInCarrier_iUnion fun _ =>
      Work.PinchLemma3.ClosedDiscA.isOpenInCarrier_connectedComponentIn
        (Work.BoxShrink.Core.isOpenInCarrier_boxRegion P s c σ)
        (box_subset_carrier P s c σ) x

/-- **The complement of the canonical collar inside the box region is the union of the remaining
components**, hence open in the surface. -/
theorem box_sdiff_collar_eq_iUnion (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    box P s c σ \ collar P s c σ u =
      ⋃ x ∈ (box P s c σ \ collar P s c σ u), connectedComponentIn (box P s c σ) x := by
  ext z
  constructor
  · intro hz
    exact Set.mem_iUnion.mpr ⟨z, Set.mem_iUnion.mpr ⟨hz, mem_connectedComponentIn hz.1⟩⟩
  · intro hz
    obtain ⟨x, hz'⟩ := Set.mem_iUnion.mp hz
    obtain ⟨hx, hzx⟩ := Set.mem_iUnion.mp hz'
    refine ⟨connectedComponentIn_subset (box P s c σ) x hzx, fun hzc => ?_⟩
    obtain ⟨x', hz''⟩ := Set.mem_iUnion.mp hzc
    obtain ⟨hx', hzx'⟩ := Set.mem_iUnion.mp hz''
    have h1 : connectedComponentIn (box P s c σ) x ⊆ connectedComponentIn (box P s c σ) z :=
      IsPreconnected.subset_connectedComponentIn
        (s := connectedComponentIn (box P s c σ) x) (x := z) (F := box P s c σ)
        isPreconnected_connectedComponentIn hzx (connectedComponentIn_subset _ _)
    have h2 : connectedComponentIn (box P s c σ) x' ⊆ connectedComponentIn (box P s c σ) z :=
      IsPreconnected.subset_connectedComponentIn
        (s := connectedComponentIn (box P s c σ) x') (x := z) (F := box P s c σ)
        isPreconnected_connectedComponentIn hzx' (connectedComponentIn_subset _ _)
    have h3 : x' ∈ connectedComponentIn (box P s c σ) z :=
      h2 (mem_connectedComponentIn hx'.1)
    have h4 : connectedComponentIn (box P s c σ) z ⊆ connectedComponentIn (box P s c σ) x' :=
      IsPreconnected.subset_connectedComponentIn
        (s := connectedComponentIn (box P s c σ) z) (x := x') (F := box P s c σ)
        isPreconnected_connectedComponentIn h3 (connectedComponentIn_subset _ _)
    exact hx.2 (Set.mem_iUnion.mpr ⟨x',
      Set.mem_iUnion.mpr ⟨hx', h4 (h1 (mem_connectedComponentIn hx.1))⟩⟩)

/-- **The complement of the canonical collar inside the box region is open in the surface.** -/
theorem isOpenInCarrier_box_sdiff_collar (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Work.SurgeryInvariance.IsOpenInCarrier P (box P s c σ \ collar P s c σ u) := by
  rw [box_sdiff_collar_eq_iUnion]
  exact isOpenInCarrier_iUnion fun x => isOpenInCarrier_iUnion fun _ =>
    Work.PinchLemma3.ClosedDiscA.isOpenInCarrier_connectedComponentIn
      (Work.BoxShrink.Core.isOpenInCarrier_boxRegion P s c σ) (box_subset_carrier P s c σ) x

/-- **The canonical collar is a collar of the pinch.** -/
theorem isPinchCollar_collar (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Work.PinchFamily.IsPinchCollar P s c σ u (collar P s c σ u) :=
  ⟨isOpenInCarrier_collar P s c σ u, slice_subset_collar P s c σ u, collar_subset_box P s c σ u,
    isOpenInCarrier_box_sdiff_collar P s c σ u⟩

/-- **Minimality: every collar of the pinch contains the canonical collar.**  The two pieces `Z` and
`box ∖ Z` are open in the surface and disjoint, so a preconnected subset of the box region lies in
one of them; the connected component of the box region through a point of the slice contains that
point, which lies in `Z`. -/
theorem collar_subset_of_isPinchCollar {Z : Set R3}
    (hZ : Work.PinchFamily.IsPinchCollar P s c σ u Z) : collar P s c σ u ⊆ Z := by
  intro y hy
  obtain ⟨x, hy'⟩ := Set.mem_iUnion.mp hy
  obtain ⟨hx, hyx⟩ := Set.mem_iUnion.mp hy'
  have hxbox : x ∈ box P s c σ := hZ.subset_box (hZ.slice_subset hx)
  -- the component of `x` in the box region, as a subset of the surface
  set Sc : Set ↥P.carrier :=
    (Subtype.val : ↥P.carrier → R3) ⁻¹' connectedComponentIn (box P s c σ) x with hSc
  have hcont : Continuous (fun z : ↥(box P s c σ) =>
      (⟨(z : R3), box_subset_carrier P s c σ z.2⟩ : ↥P.carrier)) :=
    Continuous.subtype_mk continuous_subtype_val _
  have heq : Sc = (fun z : ↥(box P s c σ) =>
      (⟨(z : R3), box_subset_carrier P s c σ z.2⟩ : ↥P.carrier)) ''
        (connectedComponent ⟨x, hxbox⟩ : Set ↥(box P s c σ)) := by
    rw [hSc, connectedComponentIn_eq_image hxbox]
    ext w
    constructor
    · rintro ⟨z, hz, hzw⟩
      exact ⟨z, hz, Subtype.ext hzw⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, rfl⟩
  have hSpre : IsPreconnected Sc := by
    rw [heq]
    exact isPreconnected_connectedComponent.image _ hcont.continuousOn
  have hU : IsOpen ((Subtype.val : ↥P.carrier → R3) ⁻¹' Z) := hZ.isOpen
  have hV : IsOpen ((Subtype.val : ↥P.carrier → R3) ⁻¹' (box P s c σ \ Z)) := hZ.open_sdiff
  have hdisj : Disjoint ((Subtype.val : ↥P.carrier → R3) ⁻¹' Z)
      ((Subtype.val : ↥P.carrier → R3) ⁻¹' (box P s c σ \ Z)) :=
    Set.disjoint_left.mpr fun w hw hw' => hw'.2 hw
  have hcover : Sc ⊆ ((Subtype.val : ↥P.carrier → R3) ⁻¹' Z) ∪
      ((Subtype.val : ↥P.carrier → R3) ⁻¹' (box P s c σ \ Z)) := by
    intro w hw
    have hwb : (w : R3) ∈ box P s c σ := connectedComponentIn_subset _ _ hw
    by_cases hwZ : (w : R3) ∈ Z
    · exact Or.inl hwZ
    · exact Or.inr ⟨hwb, hwZ⟩
  have hyc : y ∈ P.carrier := (Work.BoxShrink.Core.mem_boxRegion.mp
    (connectedComponentIn_subset _ _ hyx)).1
  rcases IsPreconnected.subset_or_subset hU hV hdisj hcover hSpre with h | h
  · have : (⟨y, hyc⟩ : ↥P.carrier) ∈ Sc := hyx
    exact h this
  · have hxSc : (⟨x, (Work.BoxShrink.Core.mem_boxRegion.mp hxbox).1⟩ : ↥P.carrier) ∈ Sc :=
      mem_connectedComponentIn hxbox
    have hbad : x ∈ box P s c σ \ Z := h hxSc
    exact absurd (hZ.slice_subset hx) hbad.2

/-! ## The residual in its componentwise spelling -/

/-- **A collar of vanishing span exists iff the canonical collar has vanishing span.** -/
theorem spanCollarBody_iff_collar_span (β : Work.CoreTopology.ClosedCurve P) :
    Work.PinchFamily.SpanCollarBody P β s c σ u ↔
      Work.SurgeryInvariance.WindingSpan P (collar P s c σ u) = ⊥ := by
  constructor
  · rintro ⟨Z, hZ, hspan⟩
    have hle : Work.SurgeryInvariance.WindingSpan P (collar P s c σ u) ≤
        Work.SurgeryInvariance.WindingSpan P Z :=
      Work.SurgeryInvariance.WindingSpan_mono P (collar_subset_of_isPinchCollar hZ)
    rw [hspan] at hle
    exact le_bot_iff.mp hle
  · intro h
    exact ⟨collar P s c σ u, isPinchCollar_collar P s c σ u, h⟩

/-- **The two bodies are equivalent**: the collar form (an existential collar) and the
componentwise form (the canonical collar). -/
theorem arcCollarBody_iff_componentBody (β : Work.CoreTopology.ClosedCurve P) :
    ArcCollarBody P β s c σ u ↔ ArcCollarComponentBody P β s c σ u := by
  constructor
  · intro h hA
    exact (spanCollarBody_iff_collar_span β).mp (h hA)
  · intro h hA
    exact (spanCollarBody_iff_collar_span β).mpr (h hA)

/-- **The two residuals are equivalent**: the collar residual and its componentwise spelling. -/
theorem arcCollar_iff_arcCollarComponent : ArcCollar ↔ ArcCollarComponent := by
  constructor
  · intro h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu
      hcountS hcountU
    exact (arcCollarBody_iff_componentBody _).mp
      (h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu
        hcountS hcountU)
  · intro h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu
      hcountS hcountU
    exact (arcCollarBody_iff_componentBody _).mpr
      (h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu
        hcountS hcountU)

/-- **The componentwise residual gives Pardon's counted Lemma 3**, through the equivalence with
`ArcCollar`. -/
theorem countingHalf_of_countedSliceArcs_arcCollarComponent
    (hA : Work.CountedPinch.CountedSliceArcs) (hC : ArcCollarComponent) :
    Work.BoxShrink.Pinch.CountingHalf :=
  countingHalf_of_countedSliceArcs_arcCollar hA (arcCollar_iff_arcCollarComponent.mpr hC)

/-- **The componentwise residual gives the span containment of the box region.** -/
theorem windingSpan_box_le_halves_of_collar_span
    (h : Work.SurgeryInvariance.WindingSpan P (collar P s c σ u) = ⊥) :
    Work.SurgeryInvariance.WindingSpan P (box P s c σ) ≤
      Work.SurgeryInvariance.WindingSpan P (halves P s c σ u) :=
  windingSpan_box_le_halves_of_isPinchCollar (isPinchCollar_collar P s c σ u) h

end

end Work.SliceArcs
