import Mathlib
import Submission.Work.OROneRel.MagnusRewrite

namespace Work.ORLyndon

open Work.OROneRel (wordEps)

/-- Local bookkeeping: `wordEps` is additive over concatenation of words. -/
private lemma wordEps_append' {α : Type*} [DecidableEq α] (t : α) (L M : List (α × Bool)) :
    wordEps t (L ++ M) = wordEps t L + wordEps t M := by
  simp only [wordEps, List.map_append, List.sum_append]

/-- Local bookkeeping: `wordEps` read off from the first letter. -/
private lemma wordEps_cons' {α : Type*} [DecidableEq α] (t : α) (p : α × Bool)
    (L : List (α × Bool)) :
    wordEps t (p :: L)
      = (if p.1 = t then (if p.2 then (1 : ℤ) else -1) else 0) + wordEps t L := by
  rw [← List.singleton_append, wordEps_append']
  congr 1
  simp [wordEps]

/-- Local bookkeeping: a word none of whose letters is the generator `t` has exponent sum `0`. -/
private lemma wordEps_eq_zero_of {α : Type*} [DecidableEq α] (t : α) (L : List (α × Bool))
    (h : ∀ p ∈ L, p.1 ≠ t) : wordEps t L = 0 := by
  induction L with
  | nil => simp [wordEps]
  | cons p L ih =>
      rw [wordEps_cons', if_neg (h p (by simp))]
      rw [ih (fun q hq => h q (by simp [hq]))]
      ring

theorem wordEps_split_two {α : Type*} [DecidableEq α] {x : α} {b₁ b₂ : Bool}
    {L₀ L₁ L₂ : List (α × Bool)}
    (h₀ : ∀ p ∈ L₀, p.1 ≠ x) (h₁ : ∀ p ∈ L₁, p.1 ≠ x) (h₂ : ∀ p ∈ L₂, p.1 ≠ x) :
    Work.OROneRel.wordEps x (L₀ ++ (x, b₁) :: L₁ ++ (x, b₂) :: L₂)
      = (if b₁ then (1 : ℤ) else -1) + (if b₂ then (1 : ℤ) else -1) := by
  classical
  rw [wordEps_append', wordEps_cons', wordEps_append', wordEps_cons']
  rw [wordEps_eq_zero_of x L₀ h₀, wordEps_eq_zero_of x L₁ h₁, wordEps_eq_zero_of x L₂ h₂]
  norm_num

end Work.ORLyndon
