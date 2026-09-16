import Submission.ZagierHoffmanProof.StepM7

set_option autoImplicit false
set_option maxHeartbeats 8000000

open Polynomial RatFunc
open scoped BigOperators WithZero
open WithZero
open Commons.Data.Nat

/-!
# Step M9: consequences of the `q = 2` degree recursion

From `val_P_iter` (`v (P_d k) = exp (−∑_{i=1}^{d} T^i(k))` for `|F| = 2`) we deduce:
* the classical form of Thakur's recursion `s_{d+1}(k) = s_d(T k) + T k`, `T k = s_1(k)`;
* strict monotonicity in the level, `v (P_{d+1} k) < v (P_d k)` — the "degree jump" that
  drives the proof that multizeta values over `F₂` do not vanish.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

section Monotone

/-- `sExp d k = ∑_{i<d} T^{i+1}(k)` is strictly increasing in `d`. -/
lemma sExp_lt_succ (d k : ℕ) : sExp d k < sExp (d + 1) k := by
  unfold sExp
  rw [Finset.sum_range_succ]
  have hpos : 0 < Nat.iterate Tmap (d + 1) k := by
    rw [Function.iterate_succ_apply']
    exact Tmap_pos _
  have : (0 : ℤ) < ((Nat.iterate Tmap (d + 1) k : ℕ) : ℤ) := by exact_mod_cast hpos
  linarith

/-- `sExp` is strictly monotone in the level. -/
lemma sExp_strictMono (k : ℕ) : StrictMono (fun d => sExp d k) :=
  strictMono_nat_of_lt_succ fun d => sExp_lt_succ d k

/-- ★ The level recursion in its classical form (Thakur's Theorem 10 at `q = 2`):
`v (P_{d+1} k) = exp (−(T k + s_d(T k)))`. -/
theorem val_P_succ (h2 : Nat.card F = 2) (d : ℕ) (k : ℕ+) :
    Valued.v (P F (d + 1) k) = exp (-((Tmap (k : ℕ) : ℤ) + sExp d (Tmap (k : ℕ)))) := by
  rw [val_P_iter F h2 (d + 1) k, sExp_succ]

/-- ★ **The degree jump** at `q = 2`: `v (P_{d+1} k) < v (P_d k)`. -/
theorem val_P_lt_succ (h2 : Nat.card F = 2) (d : ℕ) (k : ℕ+) :
    Valued.v (P F (d + 1) k) < Valued.v (P F d k) := by
  rw [val_P_iter F h2 (d + 1) k, val_P_iter F h2 d k, WithZero.exp_lt_exp]
  have := sExp_lt_succ d (k : ℕ)
  linarith

/-- Depth one: `v (P_1 k) = exp (−T k)`. -/
lemma val_P_one_q2 (h2 : Nat.card F = 2) (k : ℕ+) :
    Valued.v (P F 1 k) = exp (-(Tmap (k : ℕ) : ℤ)) := by
  rw [val_P_iter F h2 1 k]
  norm_num [sExp]

end Monotone

section Regression

attribute [local instance 100] Classical.decEq

lemma Tmap_one : Tmap 1 = 2 := by rw [Tmap_eq_step (by norm_num : (1:ℕ) ≠ 0)]; decide
lemma Tmap_two : Tmap 2 = 4 := by rw [Tmap_eq_step (by norm_num : (2:ℕ) ≠ 0)]; decide
lemma Tmap_three : Tmap 3 = 4 := by rw [Tmap_eq_step (by norm_num : (3:ℕ) ≠ 0)]; decide
lemma Tmap_four : Tmap 4 = 8 := by rw [Tmap_eq_step (by norm_num : (4:ℕ) ≠ 0)]; decide
lemma Tmap_eight : Tmap 8 = 16 := by rw [Tmap_eq_step (by norm_num : (8:ℕ) ≠ 0)]; decide

lemma sExp_two_one : sExp 2 1 = 6 := by
  rw [sExp_succ 1 1, sExp_succ 0, sExp_zero, Tmap_one, Tmap_two]
  norm_num

lemma sExp_two_two : sExp 2 2 = 12 := by
  rw [sExp_succ 1 2, sExp_succ 0, sExp_zero, Tmap_two, Tmap_four]
  norm_num

lemma sExp_two_four : sExp 2 4 = 24 := by
  rw [sExp_succ 1 4, sExp_succ 0, sExp_zero, Tmap_four, Tmap_eight]
  norm_num

lemma sExp_three_one : sExp 3 1 = 14 := by
  rw [sExp_succ 2 1, Tmap_one, sExp_two_two]
  norm_num

lemma sExp_three_three : sExp 3 3 = 28 := by
  rw [sExp_succ 2 3, Tmap_three, sExp_two_four]
  norm_num

/-- `v (P_2 1) = exp (−6)` over `F₂` (`s_2(1) = T 1 + T 2 = 2 + 4`). -/
example : Valued.v (P (ZMod 2) 2 1) = WithZero.exp (-6) := by
  have h1 : ((1 : ℕ+) : ℕ) = 1 := rfl
  rw [val_P_iter (ZMod 2) (by simp) 2 1, h1, sExp_two_one]

/-- `v (P_3 3) = exp (−28)` over `F₂` (`s_3(3) = 4 + 8 + 16`). -/
example : Valued.v (P (ZMod 2) 3 3) = WithZero.exp (-28) := by
  have h3 : ((3 : ℕ+) : ℕ) = 3 := rfl
  rw [val_P_iter (ZMod 2) (by simp) 3 3, h3, sExp_three_three]

/-- The degree jump `v (P_3 1) < v (P_2 1)` over `F₂`. -/
example : Valued.v (P (ZMod 2) 3 1) < Valued.v (P (ZMod 2) 2 1) :=
  val_P_lt_succ (ZMod 2) (by simp) 2 1

end Regression

end ZagierHoffmanPositiveChar
