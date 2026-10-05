import Mathlib

namespace Work.RPCore.Saddle

theorem sign_split {M : ℕ} (c : Fin M → ℝ) (hc : ∀ i, c i ≠ 0) :
    ∃ (k l : ℕ) (hk : k + l = M) (φ : Fin k ⊕ Fin l ≃ Fin M),
      (∀ j : Fin k, c (φ (Sum.inl j)) < 0) ∧ (∀ j : Fin l, 0 < c (φ (Sum.inr j))) := by
  classical
  -- Partition `Fin M` into the negative-index set and its complement; the complement is
  -- exactly the positive-index set because `c` is nowhere zero.
  let k : ℕ := Fintype.card {i : Fin M // c i < 0}
  let l : ℕ := Fintype.card {i : Fin M // ¬ c i < 0}
  have hk : k + l = M := by
    have h := Fintype.card_congr (Equiv.sumCompl (fun i : Fin M => c i < 0))
    rw [Fintype.card_sum, Fintype.card_fin] at h
    simpa only [k, l] using h
  let eS : Fin k ≃ {i : Fin M // c i < 0} := (Fintype.equivFin {i : Fin M // c i < 0}).symm
  let eT : Fin l ≃ {i : Fin M // ¬ c i < 0} := (Fintype.equivFin {i : Fin M // ¬ c i < 0}).symm
  refine ⟨k, l, hk, (Equiv.sumCongr eS eT).trans (Equiv.sumCompl (fun i : Fin M => c i < 0)), ?_⟩
  constructor
  · intro j
    have h : ((Equiv.sumCongr eS eT).trans (Equiv.sumCompl (fun i : Fin M => c i < 0)))
        (Sum.inl j) = (eS j : Fin M) := by simp
    rw [h]
    exact (eS j).2
  · intro j
    have h : ((Equiv.sumCongr eS eT).trans (Equiv.sumCompl (fun i : Fin M => c i < 0)))
        (Sum.inr j) = (eT j : Fin M) := by simp
    rw [h]
    exact lt_of_le_of_ne (not_lt.mp (eT j).2) (Ne.symm (hc _))

end Work.RPCore.Saddle
