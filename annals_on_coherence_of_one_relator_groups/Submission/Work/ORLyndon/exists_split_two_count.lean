import Mathlib
import Submission.Work.ORLyndon.count_add_count_eq_countP_first
import Submission.Work.ORLyndon.exists_split_one_countP

namespace Work.ORLyndon

/-- If exactly two letters of `L` have first coordinate `x`, then `L` splits as
`L₁ ++ (x,b₁) :: L₂ ++ (x,b₂) :: L₃` with `x` absent from `L₁`, `L₂`, `L₃`. -/
theorem exists_split_two_countP {α : Type*} [DecidableEq α] {x : α} {L : List (α × Bool)}
    (h2 : List.countP (fun p : α × Bool => decide (p.1 = x)) L = 2) :
    ∃ (b₁ b₂ : Bool) (L₁ L₂ L₃ : List (α × Bool)),
      L = L₁ ++ (x, b₁) :: L₂ ++ (x, b₂) :: L₃ ∧
      (∀ p ∈ L₁, p.1 ≠ x) ∧ (∀ p ∈ L₂, p.1 ≠ x) ∧ (∀ p ∈ L₃, p.1 ≠ x) := by
  have key : ∀ L : List (α × Bool),
      List.countP (fun p : α × Bool => decide (p.1 = x)) L = 2 →
      ∃ (b₁ b₂ : Bool) (L₁ L₂ L₃ : List (α × Bool)),
        L = L₁ ++ (x, b₁) :: L₂ ++ (x, b₂) :: L₃ ∧
        (∀ p ∈ L₁, p.1 ≠ x) ∧ (∀ p ∈ L₂, p.1 ≠ x) ∧ (∀ p ∈ L₃, p.1 ≠ x) := by
    intro L
    induction L with
    | nil =>
      intro h
      exact absurd h (by rw [List.countP_eq_length_filter]; simp)
    | cons p t ih =>
      intro h
      simp only [List.countP_cons] at h
      by_cases hp : p.1 = x
      · have h1 : (if decide (p.1 = x) = true then (1 : ℕ) else 0) = 1 :=
          if_pos (decide_eq_true hp)
        rw [h1] at h
        have ht : List.countP (fun q : α × Bool => decide (q.1 = x)) t = 1 := by omega
        obtain ⟨b, L₁, L₂, hL, h₁, h₂⟩ := exists_split_one_countP (x := x) ht
        refine ⟨p.2, b, [], L₁, L₂, ?_, by simp, h₁, h₂⟩
        simp [Prod.ext_iff, hp, hL]
      · have h0 : (if decide (p.1 = x) = true then (1 : ℕ) else 0) = 0 :=
          if_neg (fun hh => hp (of_decide_eq_true hh))
        rw [h0] at h
        have ht : List.countP (fun q : α × Bool => decide (q.1 = x)) t = 2 := by omega
        obtain ⟨b₁, b₂, L₁, L₂, L₃, hL, h₁, h₂, h₃⟩ := ih ht
        refine ⟨b₁, b₂, p :: L₁, L₂, L₃, ?_, ?_, h₂, h₃⟩
        · simp [hL]
        · intro q hq
          rcases List.mem_cons.mp hq with rfl | hq'
          · exact hp
          · exact h₁ q hq'
  exact key L h2

theorem exists_split_two_count {α : Type*} [DecidableEq α] {x : α} {L : List (α × Bool)}
    (h2 : L.count (x, true) + L.count (x, false) = 2) :
    ∃ (b₁ b₂ : Bool) (L₁ L₂ L₃ : List (α × Bool)),
      L = L₁ ++ (x, b₁) :: L₂ ++ (x, b₂) :: L₃ ∧
      (∀ p ∈ L₁, p.1 ≠ x) ∧ (∀ p ∈ L₂, p.1 ≠ x) ∧ (∀ p ∈ L₃, p.1 ≠ x) := by
  rw [count_add_count_eq_countP_first x L] at h2
  exact exists_split_two_countP h2

end Work.ORLyndon
