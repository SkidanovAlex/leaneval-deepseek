import Mathlib
import Submission.Work.SynFFT.axisLeafDefs

/-!
# `Work.SynFFT.leafRowL`: the pure list combinatorics of the leaf step

`lfRowL B P = ((P.drop ((P.length / B) * B)).reverse).map lfWrap` is the current partial row
accumulator of the leaf step after having processed the prefix `P` of the reversed block: the
elements of the last (possibly incomplete) block of `B` elements of `P`, in accumulation order,
each wrapped into its singleton column.

This file collects the elementary facts about `lfRowL` used by the leaf-step correctness proof:

* its length is `P.length % B` (the number of elements of the current, not yet closed, row);
* appending one element either conses the wrapped element onto the row accumulator (when the row is
  not yet full) or closes the row and starts a fresh one (when the row was full);
* the corresponding arithmetic of `List.length / B` and `List.length % B`.
-/

set_option autoImplicit false
namespace Work.SynFFT

open HvdH

/-! ## 1. Elementary Nat arithmetic for `a → a + 1` across a block boundary -/

/-- If `a % B + 1 < B` then `a + 1` does not cross a multiple of `B`. -/
theorem div_succ_of_mod_succ_lt {a B : ℕ} (hB : 0 < B) (h : a % B + 1 < B) :
    (a + 1) / B = a / B := by
  have h1 : a + 1 = B * (a / B) + (a % B + 1) := by
    have := Nat.div_add_mod a B; omega
  rw [h1, Nat.mul_add_div hB, Nat.div_eq_of_lt h, add_zero]

/-- If `a % B + 1 = B` then `a + 1` crosses a multiple of `B`. -/
theorem div_succ_of_mod_succ_eq {a B : ℕ} (hB : 0 < B) (h : a % B + 1 = B) :
    (a + 1) / B = a / B + 1 := by
  have h1 : a + 1 = B * (a / B) + B := by
    have := Nat.div_add_mod a B; omega
  have h2 : B * (a / B) + B = B * (a / B + 1) := by ring
  rw [h1, h2, Nat.mul_div_right (a / B + 1) hB]

/-- If `a % B + 1 < B` then `(a + 1) % B = a % B + 1`. -/
theorem mod_succ_of_mod_succ_lt {a B : ℕ} (h : a % B + 1 < B) :
    (a + 1) % B = a % B + 1 := by
  have h1 : a + 1 = B * (a / B) + (a % B + 1) := by
    have := Nat.div_add_mod a B; omega
  rw [h1, Nat.mul_add_mod, Nat.mod_eq_of_lt h]

/-- If `a % B + 1 = B` then `(a + 1) % B = 0`. -/
theorem mod_succ_of_mod_succ_eq {a B : ℕ} (h : a % B + 1 = B) :
    (a + 1) % B = 0 := by
  have h1 : a + 1 = B * (a / B) + B := by
    have := Nat.div_add_mod a B; omega
  have h2 : B * (a / B) + B = B * (a / B + 1) := by ring
  rw [h1, h2, Nat.mul_mod_right]

/-- `a - (a / B) * B = a % B`. -/
theorem sub_mul_div_mod (a B : ℕ) : a - a / B * B = a % B := by
  have h : a / B * B + a % B = a := by rw [Nat.mul_comm]; exact Nat.div_add_mod a B
  omega

/-! ## 2. The row accumulator -/

/-- The number of elements of the current row is `P.length % B`. -/
theorem lfRowL_length (B : ℕ) (P : List Val) : (lfRowL B P).length = P.length % B := by
  rw [lfRowL, List.length_map, List.length_reverse, List.length_drop]
  exact sub_mul_div_mod P.length B

/-- Appending an element to a prefix whose current row is not yet full conses the wrapped element
onto the current row. -/
theorem lfRowL_append_of_mod_lt {B : ℕ} {P : List Val} {x : Val} (hB : 1 ≤ B)
    (h : P.length % B < B - 1) :
    lfRowL B (P ++ [x]) = lfWrap x :: lfRowL B P := by
  have hB0 : 0 < B := hB
  have hlt : P.length % B + 1 < B := by omega
  have hdiv : (P.length + 1) / B = P.length / B := div_succ_of_mod_succ_lt hB0 hlt
  have hlen : (P ++ [x]).length = P.length + 1 := by simp
  rw [lfRowL, lfRowL, hlen, hdiv]
  have hdrop : (P ++ [x]).drop ((P.length / B) * B)
      = (P.drop ((P.length / B) * B)) ++ [x] := by
    rw [List.drop_append]
    have hz : (P.length / B) * B - P.length = 0 := by
      have := Nat.div_mul_le_self P.length B; omega
    simp [hz]
  rw [hdrop, List.reverse_append, List.reverse_singleton, List.map_append,
    List.map_singleton, List.singleton_append]

/-- Appending an element to a prefix whose current row is full closes the row and starts a fresh
one. -/
theorem lfRowL_append_of_mod_eq {B : ℕ} {P : List Val} {x : Val} (hB : 1 ≤ B)
    (h : P.length % B = B - 1) :
    lfRowL B (P ++ [x]) = [] := by
  have hB0 : 0 < B := hB
  have heq : P.length % B + 1 = B := by omega
  have hdiv : (P.length + 1) / B = P.length / B + 1 := div_succ_of_mod_succ_eq hB0 heq
  have hlen : (P ++ [x]).length = P.length + 1 := by simp
  have hq : (P.length / B + 1) * B = P.length + 1 := by
    have hm : B * (P.length / B) + P.length % B = P.length := Nat.div_add_mod P.length B
    have h3 : (P.length / B + 1) * B = B * (P.length / B) + B := by ring
    omega
  have hidx : (P.length / B + 1) * B = (P ++ [x]).length := by rw [hlen]; exact hq
  rw [lfRowL, hlen, hdiv, hidx, List.drop_length]
  simp

/-! ## 3. The target -/

theorem leafRowL :
    (∀ (B : ℕ) (P : List HvdH.Val), (Work.SynFFT.lfRowL B P).length = P.length % B) ∧
    (∀ (B : ℕ) (P : List HvdH.Val) (x : HvdH.Val), 1 ≤ B → P.length % B < B - 1 →
      Work.SynFFT.lfRowL B (P ++ [x]) = Work.SynFFT.lfWrap x :: Work.SynFFT.lfRowL B P) ∧
    (∀ (B : ℕ) (P : List HvdH.Val) (x : HvdH.Val), 1 ≤ B → P.length % B = B - 1 →
      Work.SynFFT.lfRowL B (P ++ [x]) = []) ∧
    (∀ (B : ℕ) (P : List HvdH.Val) (x : HvdH.Val), 1 ≤ B → P.length % B < B - 1 →
      (P ++ [x]).length / B = P.length / B) ∧
    (∀ (B : ℕ) (P : List HvdH.Val) (x : HvdH.Val), 1 ≤ B → P.length % B = B - 1 →
      (P ++ [x]).length / B = P.length / B + 1) ∧
    (∀ (B : ℕ) (P : List HvdH.Val) (x : HvdH.Val), 1 ≤ B → P.length % B < B - 1 →
      (P ++ [x]).length % B = P.length % B + 1) ∧
    (∀ (B : ℕ) (P : List HvdH.Val) (x : HvdH.Val), 1 ≤ B → P.length % B = B - 1 →
      (P ++ [x]).length % B = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro B P
    exact lfRowL_length B P
  · intro B P x hB h
    exact lfRowL_append_of_mod_lt hB h
  · intro B P x hB h
    exact lfRowL_append_of_mod_eq hB h
  · intro B P x hB h
    rw [List.length_append, List.length_singleton]
    exact div_succ_of_mod_succ_lt (by omega) (by omega)
  · intro B P x hB h
    rw [List.length_append, List.length_singleton]
    exact div_succ_of_mod_succ_eq (by omega) (by omega)
  · intro B P x hB h
    rw [List.length_append, List.length_singleton]
    exact mod_succ_of_mod_succ_lt (by omega)
  · intro B P x hB h
    rw [List.length_append, List.length_singleton]
    exact mod_succ_of_mod_succ_eq (by omega)

end Work.SynFFT
