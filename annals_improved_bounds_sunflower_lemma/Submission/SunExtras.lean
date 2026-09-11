import Mathlib
import Submission.SunBasic

/-!
# More basic sunflower facts (completing SunBasic)
-/
open Finset
open scoped BigOperators

namespace Submission.Sun

variable {α : Type*} [DecidableEq α]

/-- `A ↦ T ∪ A` is injective on a family all disjoint from `T`. -/
lemma injOn_union_left (T : Finset α) {S : Finset (Finset α)}
    (hT : ∀ A ∈ S, Disjoint A T) :
    Set.InjOn (fun A : Finset α => T ∪ A) (↑S : Set (Finset α)) := by
  intro A hA B hB h
  have hAS : A ∈ S := Finset.mem_coe.mp hA
  have hBS : B ∈ S := Finset.mem_coe.mp hB
  change T ∪ A = T ∪ B at h
  apply Finset.Subset.antisymm
  · intro x hxA
    have hxT : x ∉ T := (Finset.disjoint_left.mp (hT A hAS)) hxA
    have hxB : x ∈ B := by
      have : x ∈ T ∪ B := by
        rw [← h]
        exact Finset.mem_union.mpr (Or.inr hxA)
      rcases Finset.mem_union.mp this with hxT' | hxB
      · exact (hxT hxT').elim
      · exact hxB
    exact hxB
  · intro x hxB
    have hxT : x ∉ T := (Finset.disjoint_left.mp (hT B hBS)) hxB
    have hxA : x ∈ A := by
      have : x ∈ T ∪ A := by
        rw [h]
        exact Finset.mem_union.mpr (Or.inr hxB)
      rcases Finset.mem_union.mp this with hxT' | hxA
      · exact (hxT hxT').elim
      · exact hxA
    exact hxA

/-- when every member is disjoint from `T`, `A ↦ T ∪ A` is injective on `S`. -/
lemma image_union_inj {S : Finset (Finset α)} (T : Finset α)
    (hT : ∀ A ∈ S, Disjoint A T) :
    (S.image (fun A : Finset α => T ∪ A)).card = S.card := by
  exact Finset.card_image_of_injOn (injOn_union_left T hT)

/-- r pairwise disjoint members form an r-sunflower: statement with an indexed witness. -/
lemma hasSunflower_of_disjoint_indexed {F : Finset (Finset α)} {r : ℕ}
    (h : ∃ s : Finset (Finset α), s ⊆ F ∧ s.card = r ∧
      (∀ ⦃A B : Finset α⦄, A ∈ s → B ∈ s → A ≠ B → Disjoint A B)) :
    HasSunflower F r := by
  rcases h with ⟨s, hsub, hcard, hdisj⟩
  refine ⟨s, hsub, ?_⟩
  by_cases hr : 2 ≤ r
  · exact IsSunflower_of_pairwise_disjoint hr hcard (by
      intro A hA B hB hAB
      exact hdisj hA hB hAB)
  · have hr1 : r ≤ 1 := by omega
    refine ⟨hcard, ?_⟩
    intro A hA B hB hAB
    have hs1 : s.card ≤ 1 := by omega
    have : A = B := (Finset.card_le_one.mp hs1) A hA B hB
    exact False.elim (hAB this)

/-- sunflower-free families have no r pairwise disjoint members. -/
lemma disjoint_lt_of_sunflowerFree {F : Finset (Finset α)} {r : ℕ}
    (hfree : SunflowerFree F r) :
    ¬ ∃ s : Finset (Finset α), s ⊆ F ∧ s.card = r ∧
      (∀ ⦃A B : Finset α⦄, A ∈ s → B ∈ s → A ≠ B → Disjoint A B) := by
  intro h
  exact hfree (hasSunflower_of_disjoint_indexed h)

/-- A sunflower contained in `G` is also one in a superset family `F ⊇ G`. -/
lemma HasSunflower.mono {F G : Finset (Finset α)} {r : ℕ} (hGF : G ⊆ F)
    (hG : HasSunflower G r) : HasSunflower F r := by
  rcases hG with ⟨S, hSG, hS⟩
  refine ⟨S, ?_, hS⟩
  intro A hA
  exact hGF (hSG hA)

/-- intersection of a family lifted by a fixed `T` equals `T` union the intersection,
provided the family is nonempty (so no garbage-`∅` case). -/
lemma interAll_union_image (T : Finset α) (U : Finset (Finset α)) (hU : U.Nonempty) :
    interAll (U.image (fun A : Finset α => T ∪ A)) = T ∪ interAll U := by
  have hImg : (U.image (fun A : Finset α => T ∪ A)).Nonempty := hU.image _
  apply Finset.ext
  intro x
  constructor
  · intro hx
    have hxall : ∀ B ∈ U.image (fun A : Finset α => T ∪ A), x ∈ B :=
      (mem_interAll hImg).1 hx
    by_cases hxT : x ∈ T
    · exact Finset.mem_union.mpr (Or.inl hxT)
    · have hxU : x ∈ interAll U := by
        apply (mem_interAll hU).2
        intro A hA
        have hxTA : x ∈ T ∪ A := hxall (T ∪ A) (Finset.mem_image.mpr ⟨A, hA, rfl⟩)
        rcases Finset.mem_union.mp hxTA with hxT' | hxA
        · exact (hxT hxT').elim
        · exact hxA
      exact Finset.mem_union.mpr (Or.inr hxU)
  · intro hx
    apply (mem_interAll hImg).2
    intro B hB
    rcases Finset.mem_image.mp hB with ⟨A, hA, rfl⟩
    rcases Finset.mem_union.mp hx with hxT | hxU
    · exact Finset.mem_union.mpr (Or.inl hxT)
    · exact Finset.mem_union.mpr (Or.inr ((mem_interAll hU).1 hxU A hA))

/-- if lifting (by `T` disjoint from members) adds a sunflower, the original had one. -/
lemma hasSunflower_of_lift {S : Finset (Finset α)} {r : ℕ} (T : Finset α)
    (hT : ∀ A ∈ S, Disjoint A T)
    (hS : HasSunflower (S.image (fun A : Finset α => T ∪ A)) r) :
    HasSunflower S r := by
  let g : Finset α → Finset α := fun A => T ∪ A
  rcases hS with ⟨L, hLsub, hLsf⟩
  let U : Finset (Finset α) := S.filter (fun A => g A ∈ L)
  have hUsub : U ⊆ S := Finset.filter_subset (fun A => g A ∈ L) S
  have hgU : U.image g = L := by
    apply Finset.Subset.antisymm
    · intro B hB
      rcases Finset.mem_image.mp hB with ⟨A, hAU, rfl⟩
      exact (Finset.mem_filter.mp hAU).2
    · intro B hB
      have hBim : B ∈ S.image g := hLsub hB
      rcases Finset.mem_image.mp hBim with ⟨A, hAS, hAg⟩
      have hAU : A ∈ U := by
        apply Finset.mem_filter.mpr
        exact ⟨hAS, by simpa [hAg] using hB⟩
      exact Finset.mem_image.mpr ⟨A, hAU, hAg⟩
  have hinjS : Set.InjOn g (↑S : Set (Finset α)) := by
    simpa [g] using (injOn_union_left T hT)
  have hinj : Set.InjOn g (↑U : Set (Finset α)) := by
    exact Set.InjOn.mono (Finset.coe_subset.mpr hUsub) hinjS
  have hUsf : IsSunflower U r := by
    constructor
    · calc
        U.card = (U.image g).card := (Finset.card_image_of_injOn hinj).symm
        _ = L.card := by rw [hgU]
        _ = r := hLsf.1
    · intro A hA B hB hAB
      have hAS : A ∈ S := (Finset.mem_filter.mp hA).1
      have hBS : B ∈ S := (Finset.mem_filter.mp hB).1
      have hgAL : g A ∈ L := (Finset.mem_filter.mp hA).2
      have hgBL : g B ∈ L := (Finset.mem_filter.mp hB).2
      have hgA_ne : g A ≠ g B := by
        intro hEq
        have hAU : A ∈ (↑U : Set (Finset α)) := by simpa using hA
        have hBU : B ∈ (↑U : Set (Finset α)) := by simpa using hB
        exact hAB (hinj hAU hBU hEq)
      have hsun : g A ∩ g B = interAll L := hLsf.2 (g A) hgAL (g B) hgBL hgA_ne
      have hUnon : U.Nonempty := ⟨A, hA⟩
      have hinterL : interAll L = T ∪ interAll U := by
        rw [← hgU]
        simpa [g] using (interAll_union_image T U hUnon)
      apply Finset.ext
      intro x
      constructor
      · intro hx
        have hxA : x ∈ A := (Finset.mem_inter.mp hx).1
        have hxB : x ∈ B := (Finset.mem_inter.mp hx).2
        have hxT : x ∉ T := (Finset.disjoint_left.mp (hT A hAS)) hxA
        have hxL : x ∈ interAll L := by
          have hxAB : x ∈ g A ∩ g B := Finset.mem_inter.mpr
            ⟨by simp [g, hxA], by simp [g, hxB]⟩
          simpa [hsun] using hxAB
        have hxTU : x ∈ T ∪ interAll U := by
          simpa [hinterL] using hxL
        rcases Finset.mem_union.mp hxTU with hxT' | hxU
        · exact (hxT hxT').elim
        · exact hxU
      · intro hxU
        have hxA : x ∈ A := (interAll_subset hA) hxU
        have hxB : x ∈ B := (interAll_subset hB) hxU
        exact Finset.mem_inter.mpr ⟨hxA, hxB⟩
  exact ⟨U, hUsub, hUsf⟩

/-- subfamilies by a filter of a sunflower-free family are sunflower-free -/
lemma SunflowerFree.filter {F : Finset (Finset α)} {r : ℕ} (hfree : SunflowerFree F r)
    (p : Finset α → Prop) [DecidablePred p] : SunflowerFree (F.filter p) r := by
  intro h
  exact hfree (HasSunflower.mono (Finset.filter_subset p F) h)

end Submission.Sun
