import Mathlib
import Submission.Commons.NumberTheory.KroneckerSums.sum_fin12_ite_count_eq_sum_dedup

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

/-- `if P ∧ Q then a else 0 = if P then (if Q then a else 0) else 0`. -/
private lemma ite_and_ite {α : Type*} [Zero α] (P Q : Prop) [Decidable P] [Decidable Q] (a : α) :
    (if P ∧ Q then a else 0) = if P then (if Q then a else 0) else 0 := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

theorem sum_prod_dedup_eq_sum_fin12_fin12 (l l' : List ℕ)
    (hl : ∀ p ∈ l, ∃ i : Fin 12, p = 2 * ((i : ℕ) + 1))
    (hl' : ∀ q ∈ l', ∃ j : Fin 12, q = 2 * ((j : ℕ) + 1))
    (H : ℕ → ℕ → ℕ) (F : Fin 12 → Fin 12 → ℕ)
    (hHF : ∀ i j : Fin 12, H (2 * ((i : ℕ) + 1)) (2 * ((j : ℕ) + 1)) = F i j) :
    (l.dedup.product l'.dedup).foldl (fun a pq => a + H pq.1 pq.2) 0
      = ∑ i : Fin 12, ∑ j : Fin 12,
          (if 0 < l.count (2 * ((i : ℕ) + 1)) ∧ 0 < l'.count (2 * ((j : ℕ) + 1))
            then F i j else 0) := by
  have hL : (l.dedup.product l'.dedup).foldl (fun a pq => a + H pq.1 pq.2) 0
      = (l.dedup.map (fun p => (l'.dedup.map (fun q => H p q)).sum)).sum := by
    change foldSum H (l.dedup ×ˢ l'.dedup) = _
    rw [foldSum_product]
  rw [hL]
  have hinner : ∀ i : Fin 12,
      (∑ j : Fin 12,
          (if 0 < l.count (2 * ((i : ℕ) + 1)) ∧ 0 < l'.count (2 * ((j : ℕ) + 1))
            then F i j else 0))
        = (if 0 < l.count (2 * ((i : ℕ) + 1))
            then (l'.dedup.map (fun q => H (2 * ((i : ℕ) + 1)) q)).sum else 0) := by
    intro i
    have hstep1 :
        (∑ j : Fin 12,
            (if 0 < l.count (2 * ((i : ℕ) + 1)) ∧ 0 < l'.count (2 * ((j : ℕ) + 1))
              then F i j else 0))
          = ∑ j : Fin 12,
              (if 0 < l.count (2 * ((i : ℕ) + 1))
                then (if 0 < l'.count (2 * ((j : ℕ) + 1)) then F i j else 0) else 0) :=
      Finset.sum_congr rfl (fun j _ => ite_and_ite _ _ _)
    rw [hstep1]
    by_cases hP : 0 < l.count (2 * ((i : ℕ) + 1))
    · have h1 :
          (∑ j : Fin 12,
              (if 0 < l.count (2 * ((i : ℕ) + 1))
                then (if 0 < l'.count (2 * ((j : ℕ) + 1)) then F i j else 0) else 0))
            = ∑ j : Fin 12,
                (if 0 < l'.count (2 * ((j : ℕ) + 1)) then F i j else 0) :=
        Finset.sum_congr rfl (fun j _ => by rw [if_pos hP])
      rw [h1, if_pos hP]
      exact sum_fin12_ite_count_eq_sum_dedup l' (fun q => H (2 * ((i : ℕ) + 1)) q) hl'
        (fun j => F i j) (fun j => hHF i j)
    · have h1 :
          (∑ j : Fin 12,
              (if 0 < l.count (2 * ((i : ℕ) + 1))
                then (if 0 < l'.count (2 * ((j : ℕ) + 1)) then F i j else 0) else 0)) = 0 :=
        Finset.sum_eq_zero (fun j _ => by rw [if_neg hP])
      rw [h1, if_neg hP]
  have houter :=
    sum_fin12_ite_count_eq_sum_dedup l (fun p => (l'.dedup.map (fun q => H p q)).sum) hl
      (fun i => (l'.dedup.map (fun q => H (2 * ((i : ℕ) + 1)) q)).sum) (fun i => rfl)
  rw [← houter]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact (hinner i).symm

end Commons.NumberTheory.KroneckerSums
