import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.box_card

/-!
# `Work.HP.FM3.box_count_le`

A crude but uniform counting bound for the integer points of a Euclidean ball:
any set `s` of integer vectors in `Fin m → ℤ` has at most `(2t+3)^m` elements of
Euclidean norm `≤ t`.

The constant `3` (rather than the sharp `2⌈t⌉+1`) is what makes the statement
work for real `t ≥ 0` without case distinctions: every coordinate of a vector of
norm `≤ t` satisfies `|xᵢ| ≤ t ≤ ⌈t⌉`, so the set is contained in the coordinate
box `∏ᵢ [-⌈t⌉, ⌈t⌉]`, which has `(2⌈t⌉+1)^m ≤ (2t+3)^m` points.
-/

set_option autoImplicit false

noncomputable section

open Finset

namespace Work.HP.FM3

/-- Each coordinate of an integer vector is bounded in absolute value by its Euclidean norm. -/
private lemma abs_coord_le_eNorm (m : ℕ) (x : Fin m → ℤ) (i : Fin m) :
    |(x i : ℝ)| ≤ eNorm x := by
  have h1 : ((x i : ℝ)) ^ 2 ≤ ∑ j, ((x j : ℝ)) ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg ((x j : ℝ))) (Finset.mem_univ i)
  calc |(x i : ℝ)| = Real.sqrt (((x i : ℝ)) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (∑ j, ((x j : ℝ)) ^ 2) := Real.sqrt_le_sqrt h1
    _ = eNorm x := rfl

theorem box_count_le (m : ℕ) (s : Finset (Fin m → ℤ)) (t : ℝ) (ht : 0 ≤ t) :
    ((s.filter (fun x => eNorm x ≤ t)).card : ℝ) ≤ (2 * t + 3) ^ m := by
  have hsub : s.filter (fun x => eNorm x ≤ t) ⊆
      Fintype.piFinset (fun _ : Fin m => Finset.Icc (-(Nat.ceil t : ℤ)) (Nat.ceil t : ℤ)) := by
    intro x hx
    rw [Fintype.mem_piFinset]
    intro i
    have hxe : eNorm x ≤ t := (Finset.mem_filter.mp hx).2
    have h1 : |(x i : ℝ)| ≤ t := le_trans (abs_coord_le_eNorm m x i) hxe
    have h2 : |((x i : ℤ) : ℝ)| ≤ ((Nat.ceil t : ℤ) : ℝ) := le_trans h1 (Nat.le_ceil t)
    rw [Finset.mem_Icc]
    exact ⟨by exact_mod_cast (abs_le.mp h2).1, by exact_mod_cast (abs_le.mp h2).2⟩
  have hcard_le : ((s.filter (fun x => eNorm x ≤ t)).card : ℝ)
      ≤ ((Fintype.piFinset
            (fun _ : Fin m => Finset.Icc (-(Nat.ceil t : ℤ)) (Nat.ceil t : ℤ))).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hboxcard : ((Fintype.piFinset
        (fun _ : Fin m => Finset.Icc (-(Nat.ceil t : ℤ)) (Nat.ceil t : ℤ))).card : ℝ)
      = (2 * ((Nat.ceil t : ℕ) : ℝ) + 1) ^ m := by
    have h := (box_card (ι := Fin m) (Nat.ceil t)).1
    rwa [Fintype.card_fin] at h
  have hkey : 2 * ((Nat.ceil t : ℕ) : ℝ) + 1 ≤ 2 * t + 3 := by
    have h := Nat.ceil_lt_add_one ht
    linarith
  calc ((s.filter (fun x => eNorm x ≤ t)).card : ℝ)
      ≤ ((Fintype.piFinset
            (fun _ : Fin m => Finset.Icc (-(Nat.ceil t : ℤ)) (Nat.ceil t : ℤ))).card : ℝ) := hcard_le
    _ = (2 * ((Nat.ceil t : ℕ) : ℝ) + 1) ^ m := hboxcard
    _ ≤ (2 * t + 3) ^ m := pow_le_pow_left₀ (by positivity) hkey m

end Work.HP.FM3
