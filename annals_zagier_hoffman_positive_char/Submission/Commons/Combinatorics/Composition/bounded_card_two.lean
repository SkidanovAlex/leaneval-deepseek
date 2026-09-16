import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.NormNum.Ineq

open scoped BigOperators

namespace Commons.Combinatorics.Composition

/-- Compositions of `n` all of whose blocks have size at most `2`. -/
abbrev Comp2 (n : ℕ) := {c : Composition n // ∀ b ∈ c.blocks, b ≤ 2}

namespace Comp2

variable {n : ℕ}

/-- Two elements of `Comp2 n` are equal as soon as their blocks agree. -/
lemma ext_blocks {x y : Comp2 n} (h : x.1.blocks = y.1.blocks) : x = y :=
  Subtype.ext (Composition.ext h)

/-- Prepend a block of size `1`. -/
def pre1 (y : Comp2 n) : Comp2 (n + 1) :=
  ⟨⟨1 :: y.1.blocks, by
      intro x hx
      rcases List.mem_cons.mp hx with hx | hx
      · omega
      · exact y.1.blocks_pos hx,
      by rw [List.sum_cons, y.1.blocks_sum]; omega⟩, by
      intro x hx
      rcases List.mem_cons.mp hx with hx | hx
      · omega
      · exact y.2 x hx⟩

/-- Prepend a block of size `2`. -/
def pre2 (y : Comp2 n) : Comp2 (n + 2) :=
  ⟨⟨2 :: y.1.blocks, by
      intro x hx
      rcases List.mem_cons.mp hx with hx | hx
      · omega
      · exact y.1.blocks_pos hx,
      by rw [List.sum_cons, y.1.blocks_sum]; omega⟩, by
      intro x hx
      rcases List.mem_cons.mp hx with hx | hx
      · omega
      · exact y.2 x hx⟩

/-- Split a composition of `n + 2` with parts `≤ 2` according to the size of its first block. -/
def destruct (x : Comp2 (n + 2)) : Comp2 (n + 1) ⊕ Comp2 n :=
  match hl : x.1.blocks with
  | [] => absurd (hl ▸ x.1.blocks_sum) (by simp)
  | b :: t =>
      if hb : b = 1 then
        Sum.inl ⟨⟨t,
          (by intro y hy; exact x.1.blocks_pos (hl.symm ▸ List.mem_cons_of_mem b hy)),
          (by
            have h := hl ▸ x.1.blocks_sum
            rw [List.sum_cons, hb] at h
            omega)⟩,
          (by intro y hy; exact x.2 y (hl.symm ▸ List.mem_cons_of_mem b hy))⟩
      else
        Sum.inr ⟨⟨t,
          (by intro y hy; exact x.1.blocks_pos (hl.symm ▸ List.mem_cons_of_mem b hy)),
          (by
            have h := hl ▸ x.1.blocks_sum
            rw [List.sum_cons] at h
            have hb2 : b = 2 := by
              have hle2 : b ≤ 2 := x.2 b (hl.symm ▸ List.mem_cons_self)
              have hpos2 : 0 < b := x.1.blocks_pos (hl.symm ▸ List.mem_cons_self)
              omega
            rw [hb2] at h
            omega)⟩,
          (by intro y hy; exact x.2 y (hl.symm ▸ List.mem_cons_of_mem b hy))⟩

/-- Reassemble a composition of `n + 2` from its first block and the rest. -/
def undestruct : Comp2 (n + 1) ⊕ Comp2 n → Comp2 (n + 2)
  | Sum.inl y => pre1 y
  | Sum.inr y => pre2 y

lemma destruct_pre1 (y : Comp2 (n + 1)) : destruct (pre1 y) = Sum.inl y := by
  unfold destruct
  simp only [pre1]
  rw [dif_pos trivial]

lemma destruct_pre2 (y : Comp2 n) : destruct (pre2 y) = Sum.inr y := by
  unfold destruct
  simp only [pre2]
  rw [dif_neg (by norm_num : ¬ (2 = 1))]

lemma undestruct_destruct (x : Comp2 (n + 2)) : undestruct (destruct x) = x := by
  obtain ⟨⟨l, hpos, hsum⟩, hle⟩ := x
  cases l with
  | nil => exact absurd hsum (by simp)
  | cons b t =>
    by_cases hb : b = 1
    · simp only [destruct, dif_pos hb, undestruct, pre1]
      subst hb
      exact ext_blocks rfl
    · have hb2 : b = 2 := by
        have h1 : b ≤ 2 := hle b List.mem_cons_self
        have h2 : 0 < b := hpos List.mem_cons_self
        omega
      simp only [destruct, dif_neg hb, undestruct, pre2]
      subst hb2
      exact ext_blocks rfl

/-- The recursive decomposition of compositions of `n + 2` with parts `≤ 2`. -/
def equiv (n : ℕ) : Comp2 (n + 2) ≃ Comp2 (n + 1) ⊕ Comp2 n where
  toFun := destruct
  invFun := undestruct
  left_inv := undestruct_destruct
  right_inv := by
    rintro (y | y)
    · exact destruct_pre1 y
    · exact destruct_pre2 y

/-- There is exactly one composition of `0` with parts `≤ 2`, the empty one. -/
lemma card_zero : Nat.card (Comp2 0) = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  constructor
  · refine ⟨fun x y => ?_⟩
    exact ext_blocks (by
      have hx : x.1.blocks = [] := (Composition.blocks_eq_nil x.1).mpr rfl
      have hy : y.1.blocks = [] := (Composition.blocks_eq_nil y.1).mpr rfl
      rw [hx, hy])
  · exact ⟨⟨Composition.ones 0, by intro b hb; simp at hb⟩⟩

/-- The blocks of a composition of `1` with parts `≤ 2` are `[1]`. -/
lemma blocks_eq_one (x : Comp2 1) : x.1.blocks = [1] := by
  have hlen : x.1.length = 1 := by
    have h1 : x.1.length ≤ 1 := x.1.length_le
    have h2 : 0 < x.1.length := by rw [Composition.length_pos_iff]; norm_num
    omega
  have hx : x.1 = Composition.single 1 (by norm_num) :=
    (Composition.eq_single_iff_length (by norm_num : 0 < 1)).mpr hlen
  rw [hx, Composition.single_blocks]

/-- There is exactly one composition of `1` with parts `≤ 2`, namely `[1]`. -/
lemma card_one : Nat.card (Comp2 1) = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  constructor
  · refine ⟨fun x y => ?_⟩
    exact ext_blocks (by rw [blocks_eq_one x, blocks_eq_one y])
  · exact ⟨⟨Composition.single 1 (by norm_num), by
      intro b hb
      rw [Composition.single_blocks] at hb
      simp at hb
      omega⟩⟩

theorem card_fib (n : ℕ) : Nat.card (Comp2 n) = Nat.fib (n + 1) := by
  have h : ∀ m, Nat.card (Comp2 m) = Nat.fib (m + 1) ∧
      Nat.card (Comp2 (m + 1)) = Nat.fib (m + 2) := by
    intro m
    induction m with
    | zero => exact ⟨card_zero, card_one⟩
    | succ k ih =>
      obtain ⟨h1, h2⟩ := ih
      refine ⟨h2, ?_⟩
      have hstep : Nat.card (Comp2 (k + 2)) =
          Nat.card (Comp2 (k + 1)) + Nat.card (Comp2 k) := by
        rw [Nat.card_congr (equiv k), Nat.card_sum]
      rw [hstep, h1, h2]
      show Nat.fib (k + 2) + Nat.fib (k + 1) = Nat.fib (k + 3)
      have hf : Nat.fib (k + 3) = Nat.fib (k + 2) + Nat.fib (k + 1) := by
        have hh := Nat.fib_add_two (n := k + 1)
        rw [show (k + 1) + 2 = k + 3 by omega,
            show (k + 1) + 1 = k + 2 by omega] at hh
        rw [hh, Nat.add_comm]
      rw [hf]
  exact (h n).1

end Comp2

/-- **Compositions into parts `≤ 2` are counted by the Fibonacci numbers**:
`#{compositions of n with parts 1 or 2} = fib (n+1)`. -/
theorem bounded_card_two (n : ℕ) :
    Nat.card {c : Composition n // ∀ b ∈ c.blocks, b ≤ 2} = Nat.fib (n + 1) :=
  Comp2.card_fib n

end Commons.Combinatorics.Composition