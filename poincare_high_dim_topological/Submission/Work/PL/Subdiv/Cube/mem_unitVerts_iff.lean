import Mathlib
import Submission.Work.PL.Subdiv.Cube.Defs

namespace Work.PL.Subdiv.Cube

/-- A down-set (initial segment) `S` of `Fin n` is exactly its own first `#S` elements. -/
private lemma mem_iff_val_lt_card (n : ℕ) (S : Finset (Fin n))
    (hS : ∀ a b : Fin n, b ≤ a → a ∈ S → b ∈ S) (a : Fin n) :
    a ∈ S ↔ (a : ℕ) < S.card := by
  constructor
  · intro ha
    have hsub : (Finset.Iic a : Finset (Fin n)) ⊆ S := by
      intro b hb
      exact hS a b (Finset.mem_Iic.mp hb) ha
    have hle := Finset.card_le_card hsub
    rw [Fin.card_Iic] at hle
    exact Nat.lt_of_succ_le hle
  · intro ha
    by_contra hnot
    have hsub : S ⊆ (Finset.Iio a : Finset (Fin n)) := by
      intro b hb
      rw [Finset.mem_Iio]
      by_contra hcon
      rw [not_lt] at hcon
      exact hnot (hS b a hcon hb)
    have hle := Finset.card_le_card hsub
    rw [Fin.card_Iio] at hle
    omega

theorem mem_unitVerts_iff (n : ℕ) (π : Equiv.Perm (Fin n)) (v : PL.E n) :
    v ∈ unitVerts π ↔ (∀ i, v i = 0 ∨ v i = 1) ∧ ∀ a b : Fin n, a ≤ b → v (π a) ≤ v (π b) := by
  constructor
  · intro hv
    obtain ⟨k, -, heq⟩ := Finset.mem_image.mp hv
    rw [← heq]
    exact ⟨fun i => by rw [wvec_apply]; split <;> norm_num, wvec_monotone π k⟩
  · rintro ⟨h01, hmono⟩
    set S : Finset (Fin n) := Finset.univ.filter (fun a => v (π a) = 0) with hSdef
    have hdown : ∀ a b : Fin n, b ≤ a → a ∈ S → b ∈ S := by
      intro a b hba ha
      simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      have h := hmono b a hba
      rw [ha] at h
      rcases h01 (π b) with hb | hb <;> linarith
    have hcard : ∀ a : Fin n, a ∈ S ↔ (a : ℕ) < S.card := mem_iff_val_lt_card n S hdown
    have hkn : S.card ≤ n := by
      have := Finset.card_le_card (Finset.filter_subset (fun a => v (π a) = 0) Finset.univ)
      simpa [hSdef] using this
    have hiff : ∀ a : Fin n, v (π a) = 0 ↔ (a : ℕ) < S.card := by
      intro a
      have := hcard a
      simpa [hSdef] using this
    refine Finset.mem_image.mpr ⟨S.card, Finset.mem_range.mpr (Nat.lt_succ_of_le hkn), ?_⟩
    ext i
    have hi : i = π (π.symm i) := by simp
    rw [hi, wvec_at]
    by_cases hle : S.card ≤ ((π.symm i : Fin n) : ℕ)
    · rw [if_pos hle]
      have hnotlt : ¬ (((π.symm i : Fin n) : ℕ) < S.card) := not_lt.mpr hle
      have hvne : v (π (π.symm i)) ≠ 0 := fun h0 => hnotlt ((hiff (π.symm i)).mp h0)
      rcases h01 (π (π.symm i)) with h | h
      · exact absurd h hvne
      · exact h.symm
    · rw [if_neg hle]
      have hlt : ((π.symm i : Fin n) : ℕ) < S.card := not_le.mp hle
      exact ((hiff (π.symm i)).mpr hlt).symm

end Work.PL.Subdiv.Cube
