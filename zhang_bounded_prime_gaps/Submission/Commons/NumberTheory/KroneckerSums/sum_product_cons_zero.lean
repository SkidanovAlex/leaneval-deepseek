import Mathlib

set_option linter.unusedVariables false

namespace Commons.NumberTheory.KroneckerSums

/-- Sum of `g` over a list of pairs, accumulated from the left. -/
private def foldSum (g : ℕ → ℕ → ℕ) (L : List (ℕ × ℕ)) : ℕ :=
  L.foldl (fun acc pq => acc + g pq.1 pq.2) 0

/-- Adding a constant to the initial accumulator of the left fold just adds it
to the result. -/
private lemma foldl_add_shift (g : ℕ → ℕ → ℕ) (L : List (ℕ × ℕ)) (c : ℕ) :
    L.foldl (fun acc pq => acc + g pq.1 pq.2) c
      = c + L.foldl (fun acc pq => acc + g pq.1 pq.2) 0 := by
  induction L generalizing c with
  | nil => simp
  | cons pq L ih =>
      simp only [List.foldl_cons]
      rw [ih (c + g pq.1 pq.2), ih (0 + g pq.1 pq.2)]
      omega

private lemma foldSum_cons (g : ℕ → ℕ → ℕ) (pq : ℕ × ℕ) (L : List (ℕ × ℕ)) :
    foldSum g (pq :: L) = g pq.1 pq.2 + foldSum g L := by
  unfold foldSum
  simp only [List.foldl_cons]
  rw [foldl_add_shift]
  omega

private lemma foldSum_append (g : ℕ → ℕ → ℕ) (L₁ L₂ : List (ℕ × ℕ)) :
    foldSum g (L₁ ++ L₂) = foldSum g L₁ + foldSum g L₂ := by
  unfold foldSum
  rw [List.foldl_append, foldl_add_shift]

/-- Sliding a fixed first coordinate into a mapped list. -/
private lemma foldSum_map_snd (g : ℕ → ℕ → ℕ) (l' : List ℕ) (a : ℕ) :
    foldSum g (l'.map (fun q => (a, q))) = (l'.map (fun q => g a q)).sum := by
  induction l' with
  | nil => simp [foldSum]
  | cons b l' ih =>
      rw [List.map_cons, foldSum_cons, ih, List.map_cons, List.sum_cons]

/-- Summing `g` over the product of two lists. -/
private lemma foldSum_product (g : ℕ → ℕ → ℕ) (l₁ l₂ : List ℕ) :
    foldSum g (l₁ ×ˢ l₂)
      = (l₁.map (fun p => (l₂.map (fun q => g p q)).sum)).sum := by
  induction l₁ with
  | nil => simp [foldSum]
  | cons a l₁ ih =>
      rw [List.product_cons, foldSum_append, foldSum_map_snd, ih, List.map_cons, List.sum_cons]

theorem sum_product_cons_zero (l l' : List ℕ)
    (hl : ∀ p ∈ l, p ≠ 0) (hl' : ∀ q ∈ l', q ≠ 0) (g : ℕ → ℕ → ℕ) :
    ((0 :: l).product (0 :: l')).foldl (fun acc pq => acc + g pq.1 pq.2) 0
      = g 0 0
        + (l.map (fun p => g p 0)).sum
        + (l'.map (fun q => g 0 q)).sum
        + (l.product l').foldl (fun acc pq => acc + g pq.1 pq.2) 0 := by
  change foldSum g ((0 :: l) ×ˢ (0 :: l'))
      = g 0 0
        + (l.map (fun p => g p 0)).sum
        + (l'.map (fun q => g 0 q)).sum
        + foldSum g (l ×ˢ l')
  rw [foldSum_product, foldSum_product]
  simp only [List.map_cons, List.sum_cons, List.sum_map_add]
  ring

end Commons.NumberTheory.KroneckerSums
