import Mathlib
import Submission.Vdw.PrimitiveCase
import Submission.Commons.Data.Nat.squarefull_radical_sq_dvd

open Polynomial Filter Asymptotics
open scoped BigOperators
open Function
open vanDerWaerdenConjecture

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# Squarefullness and the radical: `C^2 ≤ D`

For a squarefull `D` (every prime divisor occurs at least twice) the radical
`C = radical D = ∏_{p | D} p` satisfies `C^2 ∣ D` and hence `C^2 ≤ D`.  This
is the elementary arithmetic behind two steps of Bhargava's Theorem-1 proof:

* the field discriminant of a primitive-proper irreducible bad polynomial is
  squarefull (`PrimitiveBad_exists_squarefull_fieldDisc`), so
  `C_f^2 ≤ D_f`;
* consequently `C_f > H^(1+δ)` forces `D_f > H^(2+2δ)`, which is the remark
  used at the start of Case III ("`C > H^(1+δ)` implies `D > H^(2+2δ)`"), and
  which shows that the Case-III-subcase-(i) slice `SubcaseI_P3` lies in the
  `D_f > H^(2+2δ)` region.

Main statements:

* `radical_sq_le_of_squarefull`;
* `fieldDisc_radical_sq_le`;
* `fieldDisc_gt_of_radical_gt` (instance-carrying form);
* `SubcaseI_P3_subset_large_fieldDisc` — every member of `SubcaseI_P3 n H`
  (`C_f > H^(1+δ)`) has `D_f > H^(2+2δ)`.

Axioms: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw

/-- **`C^2 ≤ D` for squarefull `D`** (`C = radical D`). -/
theorem radical_sq_le_of_squarefull (D : ℕ) (hD : D ≠ 0) (hsq : Squarefull D) :
    (radical D) ^ 2 ≤ D := by
  have hdvd : (radical D) ^ 2 ∣ D := by
    simpa [radical, Squarefull, Powerful] using
      (Commons.Data.Nat.squarefull_radical_sq_dvd D (by simpa [Squarefull, Powerful] using hsq))
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero hD) hdvd

/-- The field discriminant of a monic irreducible integer polynomial is
nonzero. -/
theorem fieldDisc_ne_zero (f : ℤ[X]) [Fact (Irreducible (f.map φℚ))] :
    fieldDisc f ≠ 0 :=
  Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero (Kpoly f))

/-- **`C_f^2 ≤ D_f`** for a squarefull field discriminant. -/
theorem fieldDisc_radical_sq_le (f : ℤ[X]) [Fact (Irreducible (f.map φℚ))]
    (hsq : Squarefull (fieldDisc f)) :
    (radical (fieldDisc f)) ^ 2 ≤ fieldDisc f :=
  radical_sq_le_of_squarefull _ (fieldDisc_ne_zero f) hsq

/-- **`C_f > H^(1+δ)` forces `D_f > H^(2+2δ)`** (squarefull `D_f`):
`D_f ≥ C_f^2` and `(H^(1+δ))^2 = H^(2+2δ)`. -/
theorem fieldDisc_gt_of_radical_gt (n H : ℕ) (hn : 1 ≤ n) (f : ℤ[X])
    [Fact (Irreducible (f.map φℚ))] (hsq : Squarefull (fieldDisc f))
    (hC : (H : ℝ) ^ (1 + 1 / (2 * (n : ℝ))) < (radical (fieldDisc f) : ℝ)) :
    (H : ℝ) ^ (2 + 1 / (n : ℝ)) < (fieldDisc f : ℝ) := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hH0 : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
  have hC2 : ((radical (fieldDisc f) : ℝ)) ^ 2 ≤ (fieldDisc f : ℝ) := by
    have h := fieldDisc_radical_sq_le f hsq
    have h' : (((radical (fieldDisc f)) ^ 2 : ℕ) : ℝ) ≤ ((fieldDisc f : ℕ) : ℝ) := by
      exact_mod_cast h
    simpa using h'
  have hlt : ((H : ℝ) ^ (1 + 1 / (2 * (n : ℝ)))) ^ 2
      < ((radical (fieldDisc f) : ℝ)) ^ 2 :=
    pow_lt_pow_left₀ hC (Real.rpow_nonneg hH0 _) (by norm_num)
  have hb : (H : ℝ) ^ (2 + 1 / (n : ℝ))
      = ((H : ℝ) ^ (1 + 1 / (2 * (n : ℝ)))) ^ 2 := by
    have hexp : (2 : ℝ) + 1 / (n : ℝ) = (1 + 1 / (2 * (n : ℝ))) * 2 := by
      field_simp
    have hmul := Real.rpow_mul hH0 (1 + 1 / (2 * (n : ℝ))) (2 : ℝ)
    rw [hexp, hmul]
    exact Real.rpow_natCast _ 2
  rw [hb]
  exact lt_of_lt_of_le hlt hC2

end Submission.Vdw
