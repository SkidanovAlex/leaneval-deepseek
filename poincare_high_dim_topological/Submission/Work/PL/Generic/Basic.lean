import Mathlib
import Submission.Work.PL.Defs

/-!
# `PL/Generic/Basic`: the `DomDim` API and basic simplex lemmas.

Area A3 (`Submission/Work/PL/Generic`) of the lead blueprint.  Nothing here redefines anything
from `Submission.Work.PL.Defs`; this file only *extends* the API of `PL.DomDim` (Newman's
"dimension ≤ d" domination) and adds elementary facts about `PL.simp`.

Notation: for `s : Finset (E m)`, `PL.simp s` is the simplex spanned by `s`.
-/

open Set Metric PL

namespace PL

variable {m : ℕ}

/-! ### Membership in a `DomDim` cover -/

/-- Membership in the union of the simplices of a cover. -/
theorem mem_iUnion_simp {S : Finset (Finset (E m))} {x : E m} :
    (x ∈ ⋃ s ∈ S, PL.simp s) ↔ ∃ s ∈ S, x ∈ PL.simp s := by
  simp only [mem_iUnion, exists_prop]

/-! ### Basic API -/

theorem DomDim.mono {A B : Set (E m)} {d : ℤ} (h : A ⊆ B) (hB : DomDim B d) : DomDim A d := by
  obtain ⟨S, hS, hBS⟩ := hB
  exact ⟨S, hS, fun x hx => hBS (h hx)⟩

theorem DomDim.mono_dim {A : Set (E m)} {d d' : ℤ} (hdd : d ≤ d') (h : DomDim A d) :
    DomDim A d' := by
  obtain ⟨S, hS, hAS⟩ := h
  refine ⟨S, fun s hs => ?_, hAS⟩
  have := hS s hs
  omega

theorem DomDim.empty (d : ℤ) : DomDim (∅ : Set (E m)) d :=
  ⟨∅, by simp, by simp⟩

theorem DomDim.simp_le {s : Finset (E m)} {d : ℤ} (h : (s.card : ℤ) ≤ d + 1) :
    DomDim (PL.simp s) d := by
  refine ⟨{s}, ?_, ?_⟩
  · intro t ht
    rw [Finset.mem_singleton] at ht
    rwa [ht]
  · intro x hx
    rw [mem_iUnion_simp]
    exact ⟨s, Finset.mem_singleton_self s, hx⟩

theorem DomDim.singleton {x : E m} {d : ℤ} (h : (0 : ℤ) ≤ d) : DomDim ({x} : Set (E m)) d := by
  have h2 : (({x} : Finset (E m)).card : ℤ) ≤ d + 1 := by simp; omega
  have := DomDim.simp_le (s := {x}) h2
  simpa [PL.simp, convexHull_singleton] using this

theorem DomDim.union {A B : Set (E m)} {d : ℤ} (hA : DomDim A d) (hB : DomDim B d) :
    DomDim (A ∪ B) d := by
  obtain ⟨S, hS, hAS⟩ := hA
  obtain ⟨T, hT, hBT⟩ := hB
  refine ⟨S ∪ T, ?_, ?_⟩
  · intro s hs
    rcases Finset.mem_union.1 hs with hs | hs
    exacts [hS s hs, hT s hs]
  · intro x hx
    rw [mem_iUnion_simp]
    rcases hx with hx | hx
    · obtain ⟨s, hsS, hxs⟩ := mem_iUnion_simp.1 (hAS hx)
      exact ⟨s, Finset.mem_union_left _ hsS, hxs⟩
    · obtain ⟨s, hsT, hxs⟩ := mem_iUnion_simp.1 (hBT hx)
      exact ⟨s, Finset.mem_union_right _ hsT, hxs⟩

theorem DomDim.iUnion {ι : Type*} [Fintype ι] {A : ι → Set (E m)} {d : ℤ}
    (h : ∀ i, DomDim (A i) d) : DomDim (⋃ i, A i) d := by
  classical
  choose S hS hAS using h
  refine ⟨Finset.univ.biUnion S, ?_, ?_⟩
  · intro s hs
    obtain ⟨i, -, hsi⟩ := Finset.mem_biUnion.1 hs
    exact hS i s hsi
  · intro x hx
    rw [mem_iUnion_simp]
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hx
    obtain ⟨s, hs, hxs⟩ := mem_iUnion_simp.1 (hAS i hxi)
    exact ⟨s, Finset.mem_biUnion.2 ⟨i, Finset.mem_univ i, hs⟩, hxs⟩

theorem DomDim.biUnion {ι : Type*} {u : Finset ι} {A : ι → Set (E m)} {d : ℤ}
    (h : ∀ i ∈ u, DomDim (A i) d) : DomDim (⋃ i ∈ u, A i) d := by
  have h2 : (⋃ i ∈ u, A i) = ⋃ i : ↥u, A i.1 := by
    ext x
    simp only [mem_iUnion, exists_prop, Subtype.exists]
  rw [h2]
  exact DomDim.iUnion (A := fun i : ↥u => A i.1) fun i => h i.1 i.2

theorem DomDim.iUnion_fin {k : ℕ} {A : Fin k → Set (E m)} {d : ℤ} (h : ∀ i, DomDim (A i) d) :
    DomDim (⋃ i, A i) d :=
  DomDim.iUnion h

/-! ### Elementary facts about `PL.simp` -/

theorem simp_mono {s t : Finset (E m)} (h : s ⊆ t) : PL.simp s ⊆ PL.simp t := by
  show convexHull ℝ ((s : Set (E m))) ⊆ convexHull ℝ ((t : Set (E m)))
  exact convexHull_mono (by simpa using h)

theorem simp_empty : PL.simp (∅ : Finset (E m)) = ∅ := by
  rw [PL.simp, Finset.coe_empty, convexHull_empty]

theorem simp_subset_affineSpan (s : Finset (E m)) :
    PL.simp s ⊆ (affineSpan ℝ (s : Set (E m)) : Set _) := by
  show convexHull ℝ ((s : Set (E m))) ⊆ _
  exact convexHull_min (subset_affineSpan ℝ _) (AffineSubspace.convex _)

theorem simp_union (s t : Finset (E m)) :
    PL.simp (s ∪ t) = convexHull ℝ ((s : Set (E m)) ∪ (t : Set (E m))) := by
  rw [PL.simp, Finset.coe_union]

theorem simp_singleton (x : E m) : PL.simp ({x} : Finset (E m)) = {x} := by
  rw [PL.simp, Finset.coe_singleton, convexHull_singleton]

theorem isCompact_simp (s : Finset (E m)) : IsCompact (PL.simp s) := by
  rw [PL.simp]
  exact (Finset.finite_toSet s).isCompact_convexHull ℝ

theorem isBounded_simp (s : Finset (E m)) : Bornology.IsBounded (PL.simp s) :=
  (isCompact_simp s).isBounded

end PL
