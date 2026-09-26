import Mathlib
import Submission.Work.InnermostDisk.sphereSlicing_of_isEmbeddedSphere_of_traceCurves
import Submission.Work.Drive.Mono.sphereSlicing_union_family

/-!
# Slicing a disjoint union of two spheres by one family of trace curves

`Work.InnermostDisk.SphereSlicing P S` is Pardon's first innermost datum: the components of `S ∩ F`
(`F = P.carrier`), each bounding a disc inside `S`, with the nesting of the discs.  The brick
`Work.InnermostDisk.sphereSlicing_of_isEmbeddedSphere_of_traceCurves` constructs it for a *single*
embedded sphere whose intersection with `F` is a finite family of pairwise disjoint simple curves of
`F`.

Here the trace is given on the *union* of two disjoint closed embedded spheres `S₁ ∪ S₂`:

  `(S₁ ∪ S₂) ∩ P.carrier = ⋃ i, range (cs i).γ`,

and the task is to slice the union.  Every trace curve lies in just one of the two spheres: its
image is preconnected (it is the image of `ℝ`, by `Set.range` of a continuous map) while `S₁`, `S₂`
are closed and disjoint, so a curve lying in both would give a point of `S₁ ∩ S₂ = ∅`; see
`isPreconnected_iff_subset_of_disjoint_closed`.  Hence the family splits into the subfamily of
curves lying in `S₁` and the subfamily lying in `S₂` (indexed by subtypes, so the index type is no
longer `Fin n` — this is why `sphereSlicing_of_isEmbeddedSphere_of_traceCurves_fintype` restates
the single-sphere brick for an arbitrary finite index type), and each subfamily covers the
intersection of its own sphere with `F` (a point of `S₁ ∩ F` lies in some curve of the family, and
that curve then meets `S₁`, hence lies in `S₁`).  Slicing the two spheres separately and putting the
two slicings side by side (`sphereSlicing_union_two`, from
`Work.Drive.Mono.sphereSlicing_union_family`) slices the union: the ranges of the components are
compact and pairwise disjoint, so a loop of `F` inside the union lies in one piece.
-/

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

/-- **The single-sphere slicing brick for an arbitrary finite index type.**

`Work.InnermostDisk.sphereSlicing_of_isEmbeddedSphere_of_traceCurves` is stated for families
indexed by `Fin n`; the subfamilies of the trace curves lying in the two halves of a disjoint union
are indexed by subtypes, so the statement is transported here along `Fintype.equivFin`. -/
theorem sphereSlicing_of_isEmbeddedSphere_of_traceCurves_fintype
    {P : Work.CoreTopology.ParamTorus} {S : Set R3}
    (hsphere : Work.InnermostDisk.IsEmbeddedSphere S)
    {ι : Type} [Fintype ι] (cs : ι → Work.CoreTopology.ClosedCurve P)
    (hsimple : ∀ i, Work.CoreTopology.IsSimple P (cs i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (Set.range (cs i).γ) (Set.range (cs j).γ))
    (hcover : S ∩ P.carrier = ⋃ i, Set.range (cs i).γ) :
    Nonempty (Work.InnermostDisk.SphereSlicing P S) := by
  classical
  refine Work.InnermostDisk.sphereSlicing_of_isEmbeddedSphere_of_traceCurves
    (P := P) (S := S) hsphere (Fintype.card ι)
    (fun j : Fin (Fintype.card ι) => cs ((Fintype.equivFin ι).symm j))
    (fun j => hsimple _) (fun j j' hjj => hdisj _ _ ?_) ?_
  · exact fun h => hjj ((Fintype.equivFin ι).symm.injective h)
  · ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover ▸ hx)
      exact Set.mem_iUnion.mpr ⟨(Fintype.equivFin ι) i, by simpa using hi⟩
    · intro hx
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
      exact hcover ▸ Set.mem_iUnion.mpr ⟨(Fintype.equivFin ι).symm j, by simpa using hj⟩

/-- **A slicing of a disjoint union of two separated spheres**, from slicings of the two pieces:
`Work.Drive.Mono.sphereSlicing_union_family` at the two-element index type `Bool`. -/
theorem sphereSlicing_union_two {P : Work.CoreTopology.ParamTorus} {S₁ S₂ : Set R3}
    (Sl₁ : Work.InnermostDisk.SphereSlicing P S₁)
    (Sl₂ : Work.InnermostDisk.SphereSlicing P S₂)
    (hc₁ : IsClosed S₁) (hc₂ : IsClosed S₂) (hdisj : Disjoint S₁ S₂) :
    Nonempty (Work.InnermostDisk.SphereSlicing P (S₁ ∪ S₂)) := by
  have h := Work.Drive.Mono.sphereSlicing_union_family (P := P)
    (fun b : Bool => cond b S₁ S₂)
    (fun b => by cases b with
      | false => exact Sl₂
      | true => exact Sl₁)
    (fun b => by cases b with
      | false => exact hc₂
      | true => exact hc₁)
    (fun b b' hne => by
      cases b with
      | false => cases b' with
        | false => exact (hne rfl).elim
        | true => exact hdisj.symm
      | true => cases b' with
        | false => exact hdisj
        | true => exact (hne rfl).elim)
  have hEq : (⋃ b : Bool, cond b S₁ S₂) = S₁ ∪ S₂ := by
    ext x
    rw [Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨b, hb⟩
      cases b with
      | false => exact Or.inr hb
      | true => exact Or.inl hb
    · rintro (h | h)
      · exact ⟨true, h⟩
      · exact ⟨false, h⟩
  rwa [hEq] at h

theorem sphereSlicing_union_of_curveFamily {P : Work.CoreTopology.ParamTorus}
    {S₁ S₂ : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (hsphere₁ : Work.InnermostDisk.IsEmbeddedSphere S₁)
    (hsphere₂ : Work.InnermostDisk.IsEmbeddedSphere S₂)
    (hS₁ : IsClosed S₁) (hS₂ : IsClosed S₂) (hdisj : Disjoint S₁ S₂)
    {n : ℕ} {cs : Fin n → Work.CoreTopology.ClosedCurve P}
    (hsimple : ∀ i, Work.CoreTopology.IsSimple P (cs i))
    (hdisjcs : ∀ i j, i ≠ j → Disjoint (Set.range (cs i).γ) (Set.range (cs j).γ))
    (hcover : (S₁ ∪ S₂) ∩ P.carrier = ⋃ i, Set.range (cs i).γ) :
    Nonempty (Work.InnermostDisk.SphereSlicing P (S₁ ∪ S₂)) := by
  classical
  -- every trace curve lies in one of the two spheres, being the preconnected image of `ℝ`
  have hsplit : ∀ i : Fin n, Set.range (cs i).γ ⊆ S₁ ∨ Set.range (cs i).γ ⊆ S₂ := by
    intro i
    refine (isPreconnected_iff_subset_of_disjoint_closed.mp
      (isPreconnected_range (cs i).cont)) S₁ S₂ hS₁ hS₂ ?_ ?_
    · rintro x ⟨t, ht⟩
      have hx : (cs i).γ t ∈ (S₁ ∪ S₂) ∩ P.carrier := by
        rw [hcover]
        exact Set.mem_iUnion.mpr ⟨i, ⟨t, rfl⟩⟩
      simpa [ht] using hx.1
    · rw [Set.eq_empty_iff_forall_notMem]
      rintro z ⟨-, hz⟩
      exact Set.disjoint_left.mp hdisj hz.1 hz.2
  -- the subfamily lying in `S₁` covers `S₁ ∩ F`, and likewise for `S₂`
  have hcover₁ : S₁ ∩ P.carrier =
      ⋃ i : {i : Fin n // Set.range (cs i).γ ⊆ S₁}, Set.range (cs i).γ := by
    ext x
    constructor
    · rintro ⟨hx₁, hxc⟩
      have hx : x ∈ ⋃ i, Set.range (cs i).γ := by
        rw [← hcover]
        exact ⟨Or.inl hx₁, hxc⟩
      rw [Set.mem_iUnion] at hx
      obtain ⟨i, hi⟩ := hx
      rcases hsplit i with h | h
      · exact Set.mem_iUnion.mpr ⟨⟨i, h⟩, hi⟩
      · exact absurd (h hi) (Set.disjoint_left.mp hdisj hx₁)
    · intro hx
      rw [Set.mem_iUnion] at hx
      obtain ⟨i, hi⟩ := hx
      obtain ⟨t, ht⟩ := hi
      exact ⟨i.2 ⟨t, ht⟩, ht ▸ (cs i.1).mem t⟩
  have hcover₂ : S₂ ∩ P.carrier =
      ⋃ i : {i : Fin n // Set.range (cs i).γ ⊆ S₂}, Set.range (cs i).γ := by
    ext x
    constructor
    · rintro ⟨hx₂, hxc⟩
      have hx : x ∈ ⋃ i, Set.range (cs i).γ := by
        rw [← hcover]
        exact ⟨Or.inr hx₂, hxc⟩
      rw [Set.mem_iUnion] at hx
      obtain ⟨i, hi⟩ := hx
      rcases hsplit i with h | h
      · exact absurd (h hi) (Set.disjoint_left.mp hdisj.symm hx₂)
      · exact Set.mem_iUnion.mpr ⟨⟨i, h⟩, hi⟩
    · intro hx
      rw [Set.mem_iUnion] at hx
      obtain ⟨i, hi⟩ := hx
      obtain ⟨t, ht⟩ := hi
      exact ⟨i.2 ⟨t, ht⟩, ht ▸ (cs i.1).mem t⟩
  obtain ⟨Sl₁⟩ := sphereSlicing_of_isEmbeddedSphere_of_traceCurves_fintype (P := P) hsphere₁
    (fun i : {i : Fin n // Set.range (cs i).γ ⊆ S₁} => cs i.1)
    (fun i => hsimple i.1)
    (fun i j hij => hdisjcs i.1 j.1 (fun h => hij (Subtype.ext h)))
    hcover₁
  obtain ⟨Sl₂⟩ := sphereSlicing_of_isEmbeddedSphere_of_traceCurves_fintype (P := P) hsphere₂
    (fun i : {i : Fin n // Set.range (cs i).γ ⊆ S₂} => cs i.1)
    (fun i => hsimple i.1)
    (fun i j hij => hdisjcs i.1 j.1 (fun h => hij (Subtype.ext h)))
    hcover₂
  exact sphereSlicing_union_two Sl₁ Sl₂ hS₁ hS₂ hdisj

end

end Work.Drive.Mono
