import Mathlib
import Submission.HvdH.Interfaces

/-!
# Assembly: cost bounds for the top-level dispatcher

The top-level program of `AssemblyProp` is

`main := peek 0 r; ite r Glyph.pos core (parse; core; emit)`

where

`core := ovh; ifZero (step) (mulS)`   (`ovh` = compute `n = max (size x) (size y)`,
push `n₀` below it, test `n < n₀`).

This file collects the definitions (flags and cost functions) shared by the
Assembly development.
-/

set_option autoImplicit false

namespace Work.Assembly

open HvdH

/-- The threshold flag: `1` if `n < n₀`, else `0` (as an integer, as produced by `IntLib.lt`). -/
def zOf (n₀ n : ℕ) : ℤ := if n < n₀ then 1 else 0

/-- A uniform constant dominating the library constants used by the dispatcher
(`Kp` pick, `Ksz` size, `Kmx` max, `Kpv` pushVal, `Ksw` swap, `Klt` lt, `Kiz` ifZero, `Kms` mulS). -/
def Sw (Kp Ksz Kmx Kpv Ksw Klt Kiz Kms : ℕ) : ℕ :=
  1000 * (Kp + Ksz + Kmx + Kpv + Ksw + Klt + Kiz + Kms + 1)

/-- The constant passed to `RecursionProp`. -/
def Kbw (Kp Ksz Kmx Kpv Ksw Klt Kiz Kms : ℕ) : ℕ :=
  100 * Sw Kp Ksz Kmx Kpv Ksw Klt Kiz Kms

/-- Overhead part of the dispatcher cost: the pick/size/max/push/swap/lt stages. -/
def overCost (S n₀ x y : ℕ) : ℕ :=
  S * (max x.size y.size + 1) + S * (n₀.size + 1)

/-- Full cost bound of the dispatcher `disp` for operands `x y` (`C` is the recursion constant,
`Km` the main-step constant, `Kiz`/`Kms` the constants of the branch words). -/
def dispCost (S Kiz Kms Km C n₀ x y : ℕ) : ℕ :=
  overCost S n₀ x y +
    (if max x.size y.size < n₀ then
      4 * Kiz + Kms * (max x.size y.size + 2) * (max x.size y.size + 2)
    else 3 * Kiz + mainCost Km (CmOf C) (max x.size y.size))

theorem zOf_eq_ite (n₀ n : ℕ) : zOf n₀ n = if n < n₀ then (1 : ℤ) else 0 := rfl

theorem zOf_eq_zero_iff {n₀ n : ℕ} : zOf n₀ n = 0 ↔ n₀ ≤ n := by
  unfold zOf
  split <;> rename_i h
  · exact ⟨fun h' => absurd h' one_ne_zero, fun h' => absurd h' (by omega)⟩
  · exact ⟨fun _ => by omega, fun _ => rfl⟩

theorem zOf_ne_zero_iff {n₀ n : ℕ} : zOf n₀ n ≠ 0 ↔ n < n₀ := by
  rw [Ne, zOf_eq_zero_iff]; omega

theorem zOf_of_lt {n₀ n : ℕ} (h : n < n₀) : zOf n₀ n = 1 := by rw [zOf_eq_ite, if_pos h]

theorem zOf_of_le {n₀ n : ℕ} (h : n₀ ≤ n) : zOf n₀ n = 0 := by
  rw [zOf_eq_ite, if_neg (by omega)]

theorem isz_zOf {n₀ n : ℕ} : isz (zOf n₀ n) = if n < n₀ then 3 else 2 := by
  by_cases h : n < n₀
  · rw [zOf_of_lt h, if_pos h]; norm_num [isz]
  · rw [zOf_of_le (by omega), if_neg h]; norm_num [isz]

/-- The flag produced by `IntLib.lt` (a ℤ-comparison) is `zOf`. -/
theorem ite_int_lt_eq_zOf (n₀ n : ℕ) :
    (if (n : ℤ) < (n₀ : ℤ) then (1 : ℤ) else 0) = zOf n₀ n := by
  by_cases h : n < n₀
  · rw [if_pos (by exact_mod_cast h), zOf_of_lt h]
  · rw [if_neg (by exact_mod_cast h), zOf_of_le (by omega)]

end Work.Assembly
