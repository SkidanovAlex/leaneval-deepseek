import Submission.Work.BoxShrink.Core.Defs

/-!
# The double bubble: the elementary geometry of the two half-regions

This file collects the easy but indispensable facts about the vocabulary of
`Submission.Work.BoxShrink.Core.Defs`:

* the two half-spaces are open and disjoint, the plane is closed and is their complement;
* the region inside the sphere is **open** in the surface (the box `Submission.PBox` is open), and
  so are the two half-regions — which is what makes the winding-span algebra
  (`Work.SurgeryInvariance.Span.union_eq_sup`) applicable to the pair of half-regions;
* the region is the union of the two half-regions and the slice, the half-regions are disjoint from
  each other, and both lie in the region;
* `Submission.HasEssBox` is the same as "the region inside the sphere contains an essential loop",
  and the latter is monotone in the size of the box (so a box of size `r < s` whose intersection
  with `F` contains an essential loop makes the intersection of `F` with `PBox s c σ` essential);
* the translation of `P.ContainsEssentialLoop (upperRegion …)` into the literal form of the
  conclusion of `Work.BoxShrink.CruxStatement`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Core

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-! ## The half-spaces -/

theorem isOpen_upperHalf (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    IsOpen (upperHalf c σ u) :=
  isOpen_lt continuous_const (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (σ 2))

theorem isOpen_lowerHalf (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    IsOpen (lowerHalf c σ u) :=
  isOpen_lt (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (σ 2)) continuous_const

theorem isClosed_cutPlane (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    IsClosed (cutPlane c σ u) :=
  isClosed_eq (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (σ 2)) continuous_const

theorem disjoint_upperHalf_lowerHalf (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Disjoint (upperHalf c σ u) (lowerHalf c σ u) := by
  rw [Set.disjoint_iff_inter_eq_empty]
  ext y
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
  rintro ⟨h1, h2⟩
  exact absurd (mem_upperHalf.mp h1) (not_lt.mpr (le_of_lt (mem_lowerHalf.mp h2)))

/-- The plane is contained in the complement of the two open half-spaces (it is exactly that
complement, see `Defs.cutPlane_eq_compl_union`). -/
theorem cutPlane_subset_compl_union (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    cutPlane c σ u ⊆ (upperHalf c σ u ∪ lowerHalf c σ u)ᶜ := by
  rintro y hy (h | h)
  · exact absurd (mem_upperHalf.mp h) (by rw [hy]; exact lt_irrefl _)
  · exact absurd (mem_lowerHalf.mp h) (by rw [hy]; exact lt_irrefl _)

/-! ## The regions of the surface -/

theorem isOpenInCarrier_carrier (P : Work.CoreTopology.ParamTorus) :
    Work.SurgeryInvariance.IsOpenInCarrier P P.carrier := by
  rw [Work.SurgeryInvariance.IsOpenInCarrier]
  have h : (Subtype.val ⁻¹' P.carrier : Set P.carrier) = Set.univ := by
    ext x
    simp
  rw [h]
  exact isOpen_univ

/-- **The region inside the sphere is open in the surface** — because Pardon's box is open. -/
theorem isOpenInCarrier_boxRegion (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) :
    Work.SurgeryInvariance.IsOpenInCarrier P (boxRegion P s c σ) :=
  Work.SurgeryInvariance.isOpenInCarrier_carrier_inter (P := P)
    (Work.Topology.SphereSlicing.isOpen_PBox s c σ)

theorem isOpenInCarrier_upperRegion (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Work.SurgeryInvariance.IsOpenInCarrier P (upperRegion P s c σ u) := by
  have h : upperRegion P s c σ u =
      P.carrier ∩ (Submission.PBox s c σ ∩ upperHalf c σ u) := by
    ext y
    simp only [mem_upperRegion, Set.mem_inter_iff, mem_upperHalf]
  rw [h]
  exact Work.SurgeryInvariance.isOpenInCarrier_carrier_inter (P := P)
    ((Work.Topology.SphereSlicing.isOpen_PBox s c σ).inter (isOpen_upperHalf c σ u))

theorem isOpenInCarrier_lowerRegion (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Work.SurgeryInvariance.IsOpenInCarrier P (lowerRegion P s c σ u) := by
  have h : lowerRegion P s c σ u =
      P.carrier ∩ (Submission.PBox s c σ ∩ lowerHalf c σ u) := by
    ext y
    simp only [mem_lowerRegion, Set.mem_inter_iff, mem_lowerHalf]
  rw [h]
  exact Work.SurgeryInvariance.isOpenInCarrier_carrier_inter (P := P)
    ((Work.Topology.SphereSlicing.isOpen_PBox s c σ).inter (isOpen_lowerHalf c σ u))

theorem disjoint_upperRegion_lowerRegion (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Disjoint (upperRegion P s c σ u) (lowerRegion P s c σ u) := by
  rw [Set.disjoint_left]
  intro y hy1 hy2
  exact absurd (mem_upperHalf.mp hy1.2) (not_lt.mpr (le_of_lt (mem_lowerHalf.mp hy2.2)))

/-- The region inside a larger box contains the region inside a smaller one. -/
theorem boxRegion_mono {s s' : ℝ} (h : s ≤ s') (P : Work.CoreTopology.ParamTorus) (c : R3)
    (σ : Equiv.Perm (Fin 3)) : boxRegion P s c σ ⊆ boxRegion P s' c σ :=
  fun _ hy => ⟨hy.1, Submission.PBox_mono h hy.2⟩

/-- **`Submission.HasEssBox` is "the region inside the sphere contains an essential loop".** -/
theorem hasEssBox_iff (P : Work.CoreTopology.ParamTorus) (r : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) :
    Submission.HasEssBox P r c σ ↔ P.ContainsEssentialLoop (boxRegion P r c σ) := by
  constructor
  · rintro ⟨γ, he, hm⟩
    exact ⟨γ, he, fun t => ⟨γ.mem t, hm t⟩⟩
  · rintro ⟨γ, he, hm⟩
    exact ⟨γ, he, fun t => (hm t).2⟩

/-- A box whose intersection with the surface contains an essential loop makes the intersection of
the surface with any larger box essential. -/
theorem containsEssentialLoop_boxRegion_of_hasEssBox {r s : ℝ} (hrs : r ≤ s)
    {P : Work.CoreTopology.ParamTorus} {c : R3} {σ : Equiv.Perm (Fin 3)}
    (hbox : Submission.HasEssBox P r c σ) : P.ContainsEssentialLoop (boxRegion P s c σ) :=
  P.containsEssentialLoop_mono (boxRegion_mono hrs P c σ) ((hasEssBox_iff P r c σ).mp hbox)

/-- The upper half-region is the trace of the plane's upper side; Pardon's conclusion "there is an
essential loop of `F` in `PBox s c σ` lying in the upper half-space" is exactly
`P.ContainsEssentialLoop (upperRegion P s c σ u)`. -/
theorem containsEssentialLoop_upperRegion_iff (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    P.ContainsEssentialLoop (upperRegion P s c σ u) ↔
      ∃ γ : Work.CoreTopology.ClosedCurve P, Work.CoreTopology.IsEssential P γ ∧
        ∀ t : ℝ, γ t ∈ Submission.PBox s c σ ∧ c (σ 2) + u < γ t (σ 2) := by
  constructor
  · rintro ⟨γ, he, hm⟩
    exact ⟨γ, he, fun t => ⟨(hm t).1.2, mem_upperHalf.mp (hm t).2⟩⟩
  · rintro ⟨γ, he, hm⟩
    exact ⟨γ, he, fun t => ⟨⟨γ.mem t, (hm t).1⟩, mem_upperHalf.mpr (hm t).2⟩⟩

/-- The same for the lower half-region. -/
theorem containsEssentialLoop_lowerRegion_iff (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    P.ContainsEssentialLoop (lowerRegion P s c σ u) ↔
      ∃ γ : Work.CoreTopology.ClosedCurve P, Work.CoreTopology.IsEssential P γ ∧
        ∀ t : ℝ, γ t ∈ Submission.PBox s c σ ∧ γ t (σ 2) < c (σ 2) + u := by
  constructor
  · rintro ⟨γ, he, hm⟩
    exact ⟨γ, he, fun t => ⟨(hm t).1.2, mem_lowerHalf.mp (hm t).2⟩⟩
  · rintro ⟨γ, he, hm⟩
    exact ⟨γ, he, fun t => ⟨⟨γ.mem t, (hm t).1⟩, mem_lowerHalf.mpr (hm t).2⟩⟩

/-- "No loop of `F` inside the slicing disc is essential" is the same as "the slice contains no
essential loop". -/
theorem forall_not_isEssential_cutDisc_iff (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    (∀ γ : Work.CoreTopology.ClosedCurve P, (∀ t : ℝ, γ t ∈ cutDisc s c σ u) →
        ¬ Work.CoreTopology.IsEssential P γ) ↔
      ¬ P.ContainsEssentialLoop (sliceRegion P s c σ u) := by
  constructor
  · rintro h ⟨γ, he, hm⟩
    exact h γ (fun t => ⟨(hm t).1.2, mem_cutPlane.mp (hm t).2⟩) he
  · intro h γ hγ he
    exact h ⟨γ, he, fun t => ⟨⟨γ.mem t, (hγ t).1⟩, mem_cutPlane.mpr (hγ t).2⟩⟩

/-- The slice is closed in the surface: its trace on `F` is the intersection of `F` with the closed
set `cutPlane` and the box. -/
theorem sliceRegion_eq_carrier_inter (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    sliceRegion P s c σ u = P.carrier ∩ sliceRegion P s c σ u := by
  ext y
  exact ⟨fun h => ⟨h.1.1, h⟩, fun h => h.2⟩

end

end Work.BoxShrink.Core
