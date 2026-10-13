import Mathlib
import Submission.Work.WilE2.Ebc.Defs

namespace Work.WilE2.Ebc

-- Please declare any auxiliary lemmas in this file as `private` (or with a `_`-prefix) so that
-- they cannot clash with helper names used elsewhere under Submission/Work/WilE2.
theorem hits_of_count {α : Type*} [TopologicalSpace α] {X : Set α} {M : ℕ}
    (h : ∀ t : Finset α, (↑t : Set α) ⊆ X →
      (∀ i ∈ t, ∀ j ∈ t, i ≠ j →
        connectedComponentIn X i ≠ connectedComponentIn X j) → t.card ≤ M) :
    ∃ A : Finset (Set α), A.card ≤ M ∧
      (∀ B ∈ A, B ⊆ X ∧ B.Nonempty ∧ IsPreconnected B) ∧
      X ⊆ ⋃₀ (A : Set (Set α)) := by
  classical
  by_cases hne : Nonempty α
  · -- Nonempty ambient space: pick one point per connected component.
    have x0 : α := Classical.choice hne
    let C : Set (Set α) := connectedComponentIn X '' X
    have hC_mem : ∀ B ∈ C, B.Nonempty := by
      rintro B ⟨x, hx, rfl⟩
      exact ⟨x, mem_connectedComponentIn hx⟩
    have hC_sub : ∀ B ∈ C, B ⊆ X := by
      rintro B ⟨x, hx, rfl⟩
      exact connectedComponentIn_subset X x
    -- A choice of a representative point for every (nonempty) set.
    let rep : Set α → α := fun B => if hB : B.Nonempty then hB.choose else x0
    have hrep_mem : ∀ B ∈ C, rep B ∈ B := by
      intro B hB
      have hspec : (hC_mem B hB).choose ∈ B := (hC_mem B hB).choose_spec
      simpa [rep, dite_eq_left (hC_mem B hB)] using hspec
    -- The representative of a component lies in that same component.
    have hrep_comp : ∀ B ∈ C, connectedComponentIn X (rep B) = B := by
      intro B hB
      obtain ⟨x, hx, hxB⟩ := hB
      rw [← hxB]
      exact (connectedComponentIn_eq (h := hrep_mem (connectedComponentIn X x) ⟨x, hx, rfl⟩)).symm
    -- Finite-character bound transported from points to components.
    have hcrux : ∀ t : Finset (Set α), (↑t : Set (Set α)) ⊆ C → t.card ≤ M := by
      intro t htC
      have hsub : ∀ B ∈ t, B ∈ C := fun B hB => htC (Finset.mem_coe.mpr hB)
      have huX : (↑(t.image rep) : Set α) ⊆ X := by
        intro x hx
        rw [Finset.mem_coe, Finset.mem_image] at hx
        obtain ⟨B, hB, rfl⟩ := hx
        exact hC_sub B (hsub B hB) (hrep_mem B (hsub B hB))
      have hdist : ∀ i ∈ t.image rep, ∀ j ∈ t.image rep, i ≠ j →
          connectedComponentIn X i ≠ connectedComponentIn X j := by
        intro i hi j hj hij hcon
        rw [Finset.mem_image] at hi hj
        obtain ⟨Bi, hBi, hii⟩ := hi
        obtain ⟨Bj, hBj, hjj⟩ := hj
        have hci : connectedComponentIn X i = Bi := by
          rw [← hii, hrep_comp Bi (hsub Bi hBi)]
        have hcj : connectedComponentIn X j = Bj := by
          rw [← hjj, hrep_comp Bj (hsub Bj hBj)]
        have hBij : Bi = Bj := by rw [← hci, ← hcj]; exact hcon
        apply hij
        rw [← hii, ← hjj, hBij]
      have hcard : (t.image rep).card ≤ M := h (t.image rep) huX hdist
      have hinj : Set.InjOn rep ↑t := by
        intro B hB B' hB' heq
        have h1 := hrep_comp B (hsub B (Finset.mem_coe.mp hB))
        have h2 := hrep_comp B' (hsub B' (Finset.mem_coe.mp hB'))
        calc B = connectedComponentIn X (rep B) := h1.symm
          _ = connectedComponentIn X (rep B') := by rw [heq]
          _ = B' := h2
      have htl : (t.image rep).card = t.card := Finset.card_image_of_injOn hinj
      rw [← htl]
      exact hcard
    obtain ⟨hCfin, hCncard⟩ := finite_of_forall_finset_card_le (S := C) hcrux
    refine ⟨hCfin.toFinset, ?_, ?_, ?_⟩
    · rw [← Set.ncard_eq_toFinset_card C hCfin]
      exact hCncard
    · intro B hB
      have hBC : B ∈ C := hCfin.mem_toFinset.mp (Finset.mem_coe.mp hB)
      obtain ⟨x, hx, rfl⟩ := hBC
      exact ⟨connectedComponentIn_subset X x, ⟨x, mem_connectedComponentIn hx⟩,
        isPreconnected_connectedComponentIn⟩
    · intro x hx
      rw [Set.mem_sUnion]
      refine ⟨connectedComponentIn X x, ?_, mem_connectedComponentIn hx⟩
      rw [Finset.mem_coe]
      exact hCfin.mem_toFinset.mpr ⟨x, hx, rfl⟩
  · -- Empty ambient space: `X` is empty and the empty family works.
    have hXempty : X = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp (fun hXn => hne (hXn.elim fun x _ => ⟨x⟩))
    refine ⟨∅, by simp, by simp, ?_⟩
    rw [hXempty]
    exact Set.empty_subset _

end Work.WilE2.Ebc
