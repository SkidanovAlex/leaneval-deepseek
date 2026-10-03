import Mathlib

namespace Work.BourgainPlan.IonescuWainger

open Finset

/-- Counting bound for a single insertion into a finite set.

If `S` has more than `k` elements the sum is `0`; if `S.card = k` the only
surviving terms are those with `a ∈ S`, and the hypothesis `hc` bounds their
sum by `c`; if `S.card ≤ k - 1` every term survives and the sum is `∑ a, p a`. -/
theorem sum_insert_card_le {β : Type*} [Fintype β] [DecidableEq β] (p : β → NNReal) (c : NNReal)
    (k : ℕ) (hk : 1 ≤ k) (hc : ∀ T : Finset β, T.card ≤ k → ∑ A ∈ T, p A ≤ c) (S : Finset β) :
    ∑ a : β, (if (insert a S).card ≤ k then p a else 0)
      ≤ (∑ A : β, p A) * (if S.card ≤ k - 1 then (1 : NNReal) else 0)
        + c * (if S.card = k then 1 else 0) := by
  by_cases hA : S.card ≤ k - 1
  · -- Case `S.card ≤ k - 1`: every term survives.
    have hle : ∀ a, (insert a S).card ≤ k := fun a => by
      have h1 : (insert a S).card ≤ S.card + 1 := Finset.card_insert_le a S
      omega
    have hif1 : (if S.card ≤ k - 1 then (1:NNReal) else 0) = 1 := if_pos hA
    have hne : S.card ≠ k := by omega
    have hif2 : (if S.card = k then (1:NNReal) else 0) = 0 := if_neg hne
    have hL : ∑ a : β, (if (insert a S).card ≤ k then p a else 0) = ∑ a : β, p a :=
      Finset.sum_congr rfl (fun a _ => by rw [if_pos (hle a)])
    rw [hL, hif1, hif2, mul_one, mul_zero, add_zero]
  · have hks : k ≤ S.card := by omega
    rcases eq_or_lt_of_le hks with hB | hB
    · -- Case `S.card = k`: only `a ∈ S` survive.
      have hkB : S.card = k := hB.symm
      have hmem : ∀ a, (insert a S).card ≤ k → a ∈ S := fun a ha => by
        by_contra h
        rw [Finset.card_insert_of_notMem h, hkB] at ha
        omega
      have hif1 : (if S.card ≤ k - 1 then (1:NNReal) else 0) = 0 := by
        rw [if_neg (by omega : ¬ S.card ≤ k - 1)]
      have hif2 : (if S.card = k then (1:NNReal) else 0) = 1 := if_pos hkB
      rw [hif1, hif2, mul_zero, mul_one, zero_add]
      calc ∑ a : β, (if (insert a S).card ≤ k then p a else 0)
          = ∑ a ∈ Finset.univ.filter (fun a => (insert a S).card ≤ k), p a := by
            rw [← Finset.sum_filter]
        _ ≤ ∑ a ∈ S, p a :=
            Finset.sum_le_sum_of_subset_of_nonneg
              (fun a ha => hmem a (Finset.mem_filter.mp ha).2) (fun a _ _ => zero_le)
        _ ≤ c := hc S (by omega)
    · -- Case `k < S.card`: no term survives.
      have hnone : ∀ a, ¬ (insert a S).card ≤ k := fun a ha => by
        have h1 : S.card ≤ (insert a S).card := Finset.card_le_card (Finset.subset_insert a S)
        omega
      have hif1 : (if S.card ≤ k - 1 then (1:NNReal) else 0) = 0 := by
        rw [if_neg (by omega : ¬ S.card ≤ k - 1)]
      have hif2 : (if S.card = k then (1:NNReal) else 0) = 0 := by
        rw [if_neg (by omega : ¬ S.card = k)]
      rw [hif1, hif2, mul_zero, mul_zero, add_zero]
      exact le_of_eq (Finset.sum_eq_zero (fun a _ => by rw [if_neg (hnone a)]))

end Work.BourgainPlan.IonescuWainger
