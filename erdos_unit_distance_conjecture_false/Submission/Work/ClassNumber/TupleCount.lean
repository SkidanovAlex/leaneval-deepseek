import Mathlib
import Submission.Work.ClassNumber.DivSquareSum

namespace Work.ClassNumber

/-- Tuples of positive natural numbers of length `n` whose product is at most `m`. -/
def tupleSet (n m : ℕ) : Type := {t : Fin n → ℕ // (∀ i, t i ≠ 0) ∧ ∏ i, t i ≤ m}

namespace tupleSet

/-- Every entry of a tuple in `tupleSet n m` is at most `m`. -/
lemma entry_le {n m : ℕ} (t : tupleSet n m) (i : Fin n) : t.1 i ≤ m :=
  le_trans (Finset.single_le_prod (fun j _ ↦ Nat.one_le_iff_ne_zero.mpr (t.2.1 j))
    (Finset.mem_univ i)) t.2.2

instance finite (n m : ℕ) : Finite (tupleSet n m) := by
  classical
  refine Finite.of_injective (fun t i ↦ (⟨t.1 i, Nat.lt_succ_of_le (entry_le t i)⟩ : Fin (m + 1))) ?_
  intro a b h
  exact Subtype.ext (funext fun i ↦ congrArg Fin.val (congrFun h i))

/-- `tupleSet n 0` is empty: a product of nonzero naturals is positive, hence not `≤ 0`. -/
lemma isEmpty_zero (n : ℕ) : IsEmpty (tupleSet n 0) :=
  ⟨fun t ↦ by
    have hpos : 0 < ∏ i, t.1 i := Finset.prod_pos fun i _ ↦ Nat.pos_of_ne_zero (t.2.1 i)
    have hle := t.2.2
    omega⟩

/-- A tuple on `Fin (n+1)` is determined by its first entry and its tail. -/
def succMap (n m : ℕ) :
    tupleSet (n + 1) m → Σ k : {k // k ∈ Finset.Icc 1 m}, tupleSet n (m / k.1) :=
  fun t ↦
    ⟨⟨t.1 0, Finset.mem_Icc.mpr
        ⟨Nat.one_le_iff_ne_zero.mpr (t.2.1 0), entry_le t 0⟩⟩,
      ⟨fun i : Fin n ↦ t.1 (Fin.succ i),
        ⟨fun i ↦ t.2.1 (Fin.succ i), by
          have htot := t.2.2
          rw [Fin.prod_univ_succ] at htot
          exact (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero (t.2.1 0))).mpr
            (by simpa [mul_comm] using htot)⟩⟩⟩

lemma succMap_injective (n m : ℕ) : Function.Injective (succMap n m) := by
  intro a b h
  have h1 : a.1 0 = b.1 0 := congrArg (fun x ↦ x.1.1) h
  have h2 : (fun i : Fin n ↦ a.1 (Fin.succ i)) = (fun i : Fin n ↦ b.1 (Fin.succ i)) :=
    congrArg (fun x ↦ x.2.1) h
  apply Subtype.ext
  funext i
  exact Fin.cases h1 (fun j ↦ congrFun h2 j) i

/-- Recursion for the number of tuples: peel off the first entry and bound each
tail by the tuples of length `n` whose product fits into `m / k`. -/
lemma card_succ_le (n m : ℕ) :
    Nat.card (tupleSet (n + 1) m) ≤ ∑ k ∈ Finset.Icc 1 m, Nat.card (tupleSet n (m / k)) := by
  classical
  calc Nat.card (tupleSet (n + 1) m)
      ≤ Nat.card (Σ k : {k // k ∈ Finset.Icc 1 m}, tupleSet n (m / k.1)) :=
        Nat.card_le_card_of_injective (succMap n m) (succMap_injective n m)
    _ = ∑ k : {k // k ∈ Finset.Icc 1 m}, Nat.card (tupleSet n (m / k.1)) := Nat.card_sigma
    _ = ∑ k ∈ Finset.Icc 1 m, Nat.card (tupleSet n (m / k)) :=
        (Finset.sum_subtype (Finset.Icc 1 m) (fun _ ↦ Iff.rfl)
          (fun k ↦ Nat.card (tupleSet n (m / k)))).symm

/-- Base case: the empty tuple, and `m² ≥ 1` for `m ≥ 1`. -/
lemma card_zero_le (m : ℕ) : Nat.card (tupleSet 0 m) ≤ 2 ^ 0 * m ^ 2 := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    have := isEmpty_zero 0
    simp [Nat.card_of_isEmpty]
  · have hsub : Subsingleton (tupleSet 0 m) :=
      ⟨fun a b ↦ Subtype.ext (funext fun i ↦ Fin.elim0 i)⟩
    have hle1 : Nat.card (tupleSet 0 m) ≤ 1 := by
      have h := Nat.card_le_card_of_injective (β := Fin 1)
        (fun _ : tupleSet 0 m ↦ (0 : Fin 1)) (fun a b _ ↦ hsub.elim a b)
      simpa using h
    calc Nat.card (tupleSet 0 m) ≤ 1 := hle1
      _ ≤ 2 ^ 0 * m ^ 2 := by
          have h1 := Nat.one_le_pow 2 m hm
          simpa using h1

theorem tupleCount_aux : ∀ n m : ℕ, Nat.card (tupleSet n m) ≤ 2 ^ n * m ^ 2 := by
  intro n
  induction n with
  | zero => exact card_zero_le
  | succ n ih =>
      intro m
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm
        have := isEmpty_zero (n + 1)
        simp [Nat.card_of_isEmpty]
      · calc Nat.card (tupleSet (n + 1) m)
            ≤ ∑ k ∈ Finset.Icc 1 m, Nat.card (tupleSet n (m / k)) := card_succ_le n m
          _ ≤ ∑ k ∈ Finset.Icc 1 m, 2 ^ n * (m / k) ^ 2 :=
              Finset.sum_le_sum fun k _ ↦ ih (m / k)
          _ = 2 ^ n * ∑ k ∈ Finset.Icc 1 m, (m / k) ^ 2 := (Finset.mul_sum _ _ _).symm
          _ ≤ 2 ^ n * (2 * m ^ 2) := Nat.mul_le_mul_left _ (DivSquareSum m)
          _ = 2 ^ (n + 1) * m ^ 2 := by rw [pow_succ]; ring

end tupleSet

theorem TupleCount (n m : ℕ) :
    Nat.card {t : Fin n → ℕ // (∀ i, t i ≠ 0) ∧ ∏ i, t i ≤ m} ≤ 2 ^ n * m ^ 2 :=
  tupleSet.tupleCount_aux n m

end Work.ClassNumber
