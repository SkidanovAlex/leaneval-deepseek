import Mathlib

namespace Work.HP.BoundaryMain

/-- The integer interval `[-K, K]` has `2 * K + 1` elements. -/
private lemma card_Icc_neg_K_pos_K (K : ℕ) :
    (Finset.Icc (-(K : ℤ)) (K : ℤ)).card = 2 * K + 1 := by
  rw [Int.card_Icc]
  have h : (K : ℤ) + 1 - (-(K : ℤ)) = ((2 * K + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [h, Int.toNat_natCast]

theorem ncard_free_coords {ι : Type*} [Fintype ι] (T : Set ι) (K : ℕ) :
    ({g : ι → ℤ | (∀ m, m ∈ T → g m = 0) ∧ (∀ m, m ∉ T → |g m| ≤ (K : ℤ))} :
        Set (ι → ℤ)).Finite ∧
      ({g : ι → ℤ | (∀ m, m ∈ T → g m = 0) ∧ (∀ m, m ∉ T → |g m| ≤ (K : ℤ))} :
        Set (ι → ℤ)).ncard = (2 * K + 1) ^ (Tᶜ.ncard) := by
  classical
  let f : ι → Finset ℤ := fun m => if m ∈ T then {0} else Finset.Icc (-(K : ℤ)) (K : ℤ)
  have hf_pos : ∀ {m : ι}, m ∈ T → f m = {0} := by
    intro m hm; simp [f, hm]
  have hf_neg : ∀ {m : ι}, m ∉ T → f m = Finset.Icc (-(K : ℤ)) (K : ℤ) := by
    intro m hm; simp [f, hm]
  have hS : ({g : ι → ℤ | (∀ m, m ∈ T → g m = 0) ∧ (∀ m, m ∉ T → |g m| ≤ (K : ℤ))} :
      Set (ι → ℤ)) = ↑(Fintype.piFinset f) := by
    ext g
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, Fintype.mem_piFinset]
    constructor
    · rintro ⟨h1, h2⟩ m
      by_cases hm : m ∈ T
      · rw [hf_pos hm, Finset.mem_singleton]; exact h1 m hm
      · rw [hf_neg hm, Finset.mem_Icc]; exact abs_le.mp (h2 m hm)
    · intro h
      refine ⟨fun m hm => ?_, fun m hm => ?_⟩
      · have hm' := h m
        rw [hf_pos hm, Finset.mem_singleton] at hm'
        exact hm'
      · have hm' := h m
        rw [hf_neg hm, Finset.mem_Icc] at hm'
        exact abs_le.mpr hm'
  have hcard : (Fintype.piFinset f).card = (2 * K + 1) ^ (Tᶜ.ncard) := by
    rw [Fintype.card_piFinset]
    have h1 : ∀ m, (f m).card = if m ∈ T then 1 else 2 * K + 1 := by
      intro m
      by_cases hm : m ∈ T
      · rw [hf_pos hm, Finset.card_singleton]; simp [hm]
      · rw [hf_neg hm]; simp only [hm, ite_false]; exact card_Icc_neg_K_pos_K K
    rw [Finset.prod_congr rfl (fun m _ => h1 m)]
    have h2 : (∏ m : ι, (if m ∈ T then 1 else 2 * K + 1))
        = ∏ m ∈ Finset.univ.filter (fun m => m ∉ T), (2 * K + 1) := by
      rw [Finset.prod_filter]
      exact Finset.prod_congr rfl (fun m _ => by by_cases hm : m ∈ T <;> simp [hm])
    rw [h2, Finset.prod_const]
    have hcompl : (Tᶜ : Set ι) = ↑(Finset.univ.filter (fun m => m ∉ T)) := by
      ext m; simp
    have hcnt : (Tᶜ : Set ι).ncard = (Finset.univ.filter (fun m => m ∉ T)).card := by
      rw [hcompl, Set.ncard_coe_finset]
    rw [hcnt]
  refine ⟨?_, ?_⟩
  · rw [hS]; exact (Fintype.piFinset f).finite_toSet
  · rw [hS, Set.ncard_coe_finset]; exact hcard

end Work.HP.BoundaryMain
