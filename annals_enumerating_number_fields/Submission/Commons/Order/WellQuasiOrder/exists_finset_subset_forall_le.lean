import Mathlib.Order.WellFoundedSet

namespace Commons.Order.WellQuasiOrder

open Set

/-- In a well-quasi-ordered preorder, every subset `S` admits a finite subset `A ⊆ S`
whose down-closure contains `S`: every `s ∈ S` is above some `a ∈ A`. -/
theorem exists_finset_subset_forall_le {α : Type*} [Preorder α] [WellQuasiOrderedLE α]
    (S : Set α) : ∃ A : Finset α, (∀ a ∈ A, a ∈ S) ∧ ∀ s ∈ S, ∃ a ∈ A, a ≤ s := by
  classical
  have : WellQuasiOrderedLE (Antisymmetrization α (· ≤ ·)) :=
    Monotone.wellQuasiOrderedLE_of_wellQuasiOrderedLE_of_surjective
      (f := toAntisymmetrization (α := α) (· ≤ ·)) (toAntisymmetrization_mono (α := α))
      (fun b => ⟨ofAntisymmetrization (α := α) (· ≤ ·) b,
        toAntisymmetrization_ofAntisymmetrization (α := α) (r := (· ≤ ·)) b⟩)
  let T : Set (Antisymmetrization α (· ≤ ·)) := toAntisymmetrization (α := α) (· ≤ ·) '' S
  have hT : T.IsPWO := isPWO_of_wellQuasiOrderedLE T
  let M : Set (Antisymmetrization α (· ≤ ·)) := {m | Minimal (· ∈ T) m}
  have hanti : IsAntichain (· ≤ ·) M := by
    intro m hm m' hm' hne hle
    exact hne (le_antisymm hle (hm'.2 hm.1 hle))
  have hfin : M.Finite := hanti.finite_of_wellQuasiOrdered wellQuasiOrdered_le
  have hrep : ∀ m, m ∈ M →
      ∃ a ∈ S, toAntisymmetrization (α := α) (· ≤ ·) a = m := fun m hm => hm.1
  let A : Finset α := hfin.toFinset.attach.image
    (fun m => Classical.choose (hrep m.1 (hfin.mem_toFinset.mp m.2)))
  refine ⟨A, ?_, ?_⟩
  · intro a ha
    obtain ⟨m, _, rfl⟩ := Finset.mem_image.mp ha
    exact (Classical.choose_spec (hrep m.1 (hfin.mem_toFinset.mp m.2))).1
  · intro s hs
    obtain ⟨m, hle, hm⟩ := hT.exists_le_minimal
      (show toAntisymmetrization (α := α) (· ≤ ·) s ∈ T from Set.mem_image_of_mem _ hs)
    have hmM : m ∈ M := hm
    refine ⟨Classical.choose (hrep m hmM), ?_, ?_⟩
    · refine Finset.mem_image.mpr ⟨⟨m, hfin.mem_toFinset.mpr hmM⟩, Finset.mem_attach _ _, ?_⟩
      rfl
    · have hqa : toAntisymmetrization (α := α) (· ≤ ·)
          (Classical.choose (hrep m hmM)) = m := (Classical.choose_spec (hrep m hmM)).2
      have h1 : toAntisymmetrization (α := α) (· ≤ ·) (Classical.choose (hrep m hmM)) ≤
          toAntisymmetrization (α := α) (· ≤ ·) s := by rw [hqa]; exact hle
      exact toAntisymmetrization_le_toAntisymmetrization_iff.mp h1

end Commons.Order.WellQuasiOrder