import Mathlib
import Submission.Work.OROneRel.rightPowDefs
import Submission.Work.OROneRel.psiSubstDefs
import Submission.Work.OROneRel.ntDefs
import Submission.Work.OROneRel.nonTLetters_Psi_le

/-!
# The right-multiplication substitution `y ↦ y * t ^ (-q y)` does not increase the non-`t` letters

`Work.OROneRel.rightPow t q` is the endomorphism of the free group `F α` sending every generator
`y` to `y * t ^ (-(q y))` (`rightPowFun`, extended by `FreeGroup.lift`).  This file proves that it
never increases the number of letters different from `t`:

`nonTLetters t (rightPow t q u) ≤ nonTLetters t u`.

Each letter `y` of `u` is replaced by a block `y * t ^ (-(q y))` whose reduced form has no more
than one letter different from `t` (and none when `y = t`), and neither multiplication nor free
reduction can create new letters different from `t`: `nt` is subadditive under products
(`nt_prod_le`) and the `nt`-count of `rightPow t q (mk L)` is bounded by the sum of the block
bounds.

This is the "cost-free" substitution of the all-exponent-sums-nonzero case of the Magnus step:
`σ_t (rightPow t q u) = σ_t u - Σ_y q y · σ_y u`, so `σ_t` can be made to vanish while the number
of non-`t` letters does not increase.
-/

namespace Work.OROneRel

universe u

variable {α : Type u}

attribute [local instance] Classical.propDecidable

/-- The `nt t`-count of the image of a single generator under `rightPowFun` is at most `1`, and `0`
for the letter `t` itself. -/
theorem nt_rightPowFun_le (t : α) (q : α → ℤ) (a : α) :
    nt t (rightPowFun t q a).toWord ≤ if a = t then 0 else 1 := by
  classical
  rw [rightPowFun_apply]
  by_cases ha : a = t
  · rw [if_pos ha, ha]
    rw [← zpow_one_add (FreeGroup.of t) (-(q t)), nt_of_zpow]
  · rw [if_neg ha]
    calc nt t (FreeGroup.of a * FreeGroup.of t ^ (-(q a))).toWord
        ≤ nt t (FreeGroup.of a).toWord + nt t ((FreeGroup.of t) ^ (-(q a))).toWord :=
          nt_mul_le t _ _
      _ = 1 := by
          rw [FreeGroup.toWord_of, nt_singleton, nt_of_zpow]
          simp [ha]

/-- The `nt t`-count of the image of a single letter `c : α × Bool` of a word under `rightPowFun`
is at most `1`, and `0` when `c.1 = t`. -/
theorem nt_rightPow_block_le (t : α) (q : α → ℤ) (c : α × Bool) :
    nt t (bif c.2 then rightPowFun t q c.1 else (rightPowFun t q c.1)⁻¹).toWord
      ≤ if c.1 = t then 0 else 1 := by
  classical
  obtain ⟨a, b⟩ := c
  cases b
  · change nt t ((rightPowFun t q a)⁻¹).toWord ≤ if a = t then 0 else 1
    rw [nt_inv]
    exact nt_rightPowFun_le t q a
  · change nt t (rightPowFun t q a).toWord ≤ if a = t then 0 else 1
    exact nt_rightPowFun_le t q a

/-- Summing the block bounds of `nt_rightPow_block_le` over a word. -/
theorem sum_map_rightPow_block_le (t : α) (q : α → ℤ) (L : List (α × Bool)) :
    (L.map (fun c =>
        nt t (bif c.2 then rightPowFun t q c.1 else (rightPowFun t q c.1)⁻¹).toWord)).sum
      ≤ (L.map (fun c => if c.1 = t then 0 else 1)).sum := by
  classical
  induction L with
  | nil => simp
  | cons c L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (nt_rightPow_block_le t q c) ih

/-- Summing `if c.1 = t then 0 else 1` over a word gives back `nt t` of the word. -/
theorem sum_map_ite_eq_nt (t : α) (L : List (α × Bool)) :
    (L.map (fun c => if c.1 = t then 0 else 1)).sum = nt t L := by
  classical
  induction L with
  | nil => simp [nt]
  | cons c L ih =>
    rw [List.map_cons, List.sum_cons, nt_cons, ih]

/-- The substitution `rightPow t q` does not increase `nt t`, for a group element presented as
`FreeGroup.mk L` with `L : List (α × Bool)`. -/
theorem nt_rightPow_mk_le (t : α) (q : α → ℤ) (L : List (α × Bool)) :
    nt t (rightPow t q (FreeGroup.mk L)).toWord ≤ nt t L := by
  classical
  rw [rightPow, FreeGroup.lift_mk]
  calc nt t (List.map (fun a =>
          bif a.2 then rightPowFun t q a.1 else (rightPowFun t q a.1)⁻¹) L).prod.toWord
      ≤ (List.map (fun x => nt t x.toWord) (List.map (fun a =>
          bif a.2 then rightPowFun t q a.1 else (rightPowFun t q a.1)⁻¹) L)).sum :=
        nt_prod_le t _
    _ = (List.map (fun a =>
          nt t (bif a.2 then rightPowFun t q a.1 else (rightPowFun t q a.1)⁻¹).toWord) L).sum :=
        sum_map_map _ _ _
    _ ≤ (L.map (fun a => if a.1 = t then 0 else 1)).sum := sum_map_rightPow_block_le t q L
    _ = nt t L := sum_map_ite_eq_nt t L

/-- **The right-multiplication substitution does not increase the number of non-`t` letters.** -/
theorem nonTLetters_rightPow_le {α : Type u} (t : α) (q : α → ℤ) (u : FreeGroup α) :
    Work.OROneRel.nonTLetters t (Work.OROneRel.rightPow t q u) ≤ Work.OROneRel.nonTLetters t u := by
  classical
  have h := nt_rightPow_mk_le (α := α) t q u.toWord
  rw [FreeGroup.mk_toWord] at h
  rw [nonTLetters_eq_nt, nonTLetters_eq_nt]
  exact h

end Work.OROneRel
