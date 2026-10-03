import Mathlib

namespace Work.ORLyndon

theorem exists_split_one_countP {α : Type*} [DecidableEq α] {x : α} {L : List (α × Bool)}
    (h : List.countP (fun p : α × Bool => decide (p.1 = x)) L = 1) :
    ∃ (b : Bool) (L₁ L₂ : List (α × Bool)),
      L = L₁ ++ (x, b) :: L₂ ∧
      (∀ p ∈ L₁, p.1 ≠ x) ∧ (∀ p ∈ L₂, p.1 ≠ x) := by
  induction L with
  | nil => simp at h
  | cons p t ih =>
    by_cases hp : p.1 = x
    · have hdec : decide (p.1 = x) = true := by simp [hp]
      rw [List.countP_cons, if_pos hdec] at h
      have ht : List.countP (fun q : α × Bool => decide (q.1 = x)) t = 0 := by omega
      refine ⟨p.2, [], t, ?_, by simp, ?_⟩
      · simp [Prod.ext_iff, hp]
      · intro q hq
        have hq' := (List.countP_eq_zero.mp ht) q hq
        simpa using hq'
    · have hneg : ¬ (decide (p.1 = x) = true) := by simp [hp]
      rw [List.countP_cons, if_neg hneg] at h
      have ht : List.countP (fun q : α × Bool => decide (q.1 = x)) t = 1 := by omega
      obtain ⟨b, L₁, L₂, hL, h₁, h₂⟩ := ih ht
      refine ⟨b, p :: L₁, L₂, ?_, ?_, h₂⟩
      · simp [hL]
      · intro q hq
        rcases List.mem_cons.mp hq with rfl | hq'
        · exact hp
        · exact h₁ q hq'

end Work.ORLyndon
