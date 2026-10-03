import Mathlib

namespace Work.FIArea7

/-- The number of natural numbers `m ∈ [1,K]` lying in the half-open real interval `(α, β]`
is at most `β - α + 1`, for `α ≤ β`. -/
theorem psiCardInt (α β : ℝ) (K : ℕ) (hαβ : α ≤ β) :
    (((Finset.Icc 1 K).filter (fun m : ℕ => α < (m : ℝ) ∧ (m : ℝ) ≤ β)).card : ℝ)
      ≤ β - α + 1 := by
  set S : Finset ℕ := (Finset.Icc 1 K).filter (fun m : ℕ => α < (m : ℝ) ∧ (m : ℝ) ≤ β) with hS
  rcases Finset.eq_empty_or_nonempty S with h | hne
  · rw [h]
    simp only [Finset.card_empty, Nat.cast_zero]
    linarith
  · -- `S` is nonempty: it lies in the integer interval `[min S, max S]`, so its
    -- cardinality is at most `max S - min S + 1`; the real endpoints `α < min S`
    -- and `max S ≤ β` then give the strict inequality making the bound valid.
    have hm0mem : S.min' hne ∈ S := Finset.min'_mem S hne
    have hM0mem : S.max' hne ∈ S := Finset.max'_mem S hne
    have hpred0 : α < ((S.min' hne : ℕ) : ℝ) ∧ ((S.min' hne : ℕ) : ℝ) ≤ β :=
      (Finset.mem_filter.mp hm0mem).2
    have hpredM : α < ((S.max' hne : ℕ) : ℝ) ∧ ((S.max' hne : ℕ) : ℝ) ≤ β :=
      (Finset.mem_filter.mp hM0mem).2
    have hm0le : ∀ x ∈ S, S.min' hne ≤ x := (Finset.isLeast_min' S hne).2
    have hleM0 : ∀ x ∈ S, x ≤ S.max' hne := (Finset.isGreatest_max' S hne).2
    have hm0leM0 : S.min' hne ≤ S.max' hne := hm0le _ hM0mem
    have hcard : S.card ≤ S.max' hne - S.min' hne + 1 := by
      have hsub : S ⊆ Finset.Icc (S.min' hne) (S.max' hne) :=
        fun x hx => Finset.mem_Icc.mpr ⟨hm0le x hx, hleM0 x hx⟩
      have h1 := Finset.card_le_card hsub
      rw [Nat.card_Icc] at h1
      omega
    have hcast : (((S.max' hne - S.min' hne + 1 : ℕ)) : ℝ)
        = ((S.max' hne : ℕ) : ℝ) - ((S.min' hne : ℕ) : ℝ) + 1 := by
      rw [Nat.cast_add, Nat.cast_sub hm0leM0, Nat.cast_one]
    exact le_of_lt (calc (S.card : ℝ)
          ≤ (((S.max' hne - S.min' hne + 1 : ℕ)) : ℝ) := by exact_mod_cast hcard
      _ = ((S.max' hne : ℕ) : ℝ) - ((S.min' hne : ℕ) : ℝ) + 1 := hcast
      _ < β - α + 1 := by linarith [hpredM.2, hpred0.1])

end Work.FIArea7
