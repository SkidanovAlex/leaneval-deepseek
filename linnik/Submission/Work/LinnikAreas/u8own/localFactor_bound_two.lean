import Mathlib
import Submission.Work.LinnikAreas.u8own.corr6_twoPow_gaussTwo_le
import Submission.Work.LinnikBurgess.lfSmall.counting_two
import Submission.Work.LinnikBurgess.lfSmall.nv_le_vcapD2
import Submission.Work.LinnikBurgess.lfSmall.cap_term_le
import Submission.Work.LinnikBurgess.localFactor_bound_small
import Submission.Work.LinnikBurgess.localFactor_bound_small_trivial
import Submission.Work.LinnikBurgess.lfSmall.localFactor_lower
import Submission.Work.LinnikBurgess.lfSmall.capSet2_card_le

/-!
# U8 (Theorem L') for `p = 2`, all levels `e ≥ 2`

`‖S_{2^e}‖ ≤ 2^{e/2} · localFactor 2 e a b` for a primitive `χ` mod `2^e` and a pair `(a,b)` whose
six shifts have a unique index `i`.

* `e ≤ 12`: the menu `menuW 2 e s j` collapses to the single atom `729` at `(s,j) = (0,0)`
  (`localFactor_ge_small`), and the trivial bound `‖S‖ ≤ 2^e = 2^{e/2}·2^{e/2}` with
  `2^{e/2} ≤ 2^6 = 64 ≤ 729` closes it; if no unit class modulo `2` exists (`¬ DLp 2 0 a b`) every
  summand vanishes (`corr6_eq_zero_of_no_unit`) and `S = 0`.

* `e ≥ 13`: the two-digit peel (Lemma A₂, `corr6_twoPow_gaussTwo_le`) reduces to the graded count
  `gaussTwoRHS2 e (cubeLevel 2 e) a b ≤ localFactor 2 e a b`, which is the `p = 2` counting lemma
  `Work.LinnikBurgess.lfSmall.counting_two_partial`, assembled from the `lfSmall` modules.
-/

open scoped BigOperators
open Classical

namespace Work.LinnikAreas.u8own

/-- The `e ≤ 12` slice of U8 for `p = 2`.  Only the trivial bound is used. -/
theorem localFactor_bound_two_le12 {e : ℕ} (he : 2 ≤ e) (he12 : e ≤ 12)
    (χ : DirichletCharacter ℂ (2 ^ e)) (a b : Fin 3 → ℕ) :
    ‖∑ x : ZMod (2 ^ e), χ (∏ l : Fin 3, (x + (a l : ZMod (2 ^ e))))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (2 ^ e)))))‖
      ≤ (2 : ℝ) ^ ((e : ℝ) / 2) * Work.LinnikBurgess.localFactor 2 e a b := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp5 : ¬ 5 ≤ 2 := by norm_num
  have h64 : (2 : ℝ) ^ ((e : ℝ) / 2) ≤ 64 := by
    have h1 : (e : ℝ) / 2 ≤ (6 : ℝ) := by
      have : (e : ℝ) ≤ 12 := by exact_mod_cast he12
      linarith
    calc (2 : ℝ) ^ ((e : ℝ) / 2) ≤ (2 : ℝ) ^ (6 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
      _ = 64 := by norm_num
  have hsq : (2 : ℝ) ^ ((e : ℝ) / 2) * (2 : ℝ) ^ ((e : ℝ) / 2) = (2 : ℝ) ^ e := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), ← Real.rpow_natCast (2 : ℝ) e]
    congr 1
    push_cast
    ring
  by_cases hDL : Work.LinnikBurgess.DLp 2 0 a b
  · have hLF : (729 : ℝ) ≤ Work.LinnikBurgess.localFactor 2 e a b := by
      have h := Work.LinnikBurgess.localFactor_ge_small (p := 2) (e := e) hp5 he12 a b
      simpa only [if_pos hDL, mul_one] using h
    have htriv := Work.LinnikBurgess.corr6_norm_le (p := 2) (e := e) χ a b
    calc ‖∑ x : ZMod (2 ^ e), χ (∏ l : Fin 3, (x + (a l : ZMod (2 ^ e))))
          * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (2 ^ e)))))‖
        ≤ (2 : ℝ) ^ e := htriv
      _ = (2 : ℝ) ^ ((e : ℝ) / 2) * (2 : ℝ) ^ ((e : ℝ) / 2) := hsq.symm
      _ ≤ (2 : ℝ) ^ ((e : ℝ) / 2) * 64 :=
          mul_le_mul_of_nonneg_left h64 (Real.rpow_nonneg (by norm_num) _)
      _ ≤ (2 : ℝ) ^ ((e : ℝ) / 2) * Work.LinnikBurgess.localFactor 2 e a b :=
          mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg (by norm_num) _)
  · have hno : ∀ y : ℕ, ∃ l : Fin 3, 2 ∣ y + a l ∨ 2 ∣ y + b l := by
      intro y
      by_contra hcon
      push_neg at hcon
      exact hDL ⟨y, hcon, by norm_num, by norm_num⟩
    have hzero := Work.LinnikBurgess.corr6_eq_zero_of_no_unit (p := 2) (e := e) (by omega) a b χ hno
    rw [hzero, norm_zero]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Work.LinnikBurgess.localFactor_nonneg 2 e a b)

/-- The `p = 2` counting lemma in the shape consumed below. -/
theorem gaussTwoRHS2_le_localFactor_two {e : ℕ} (he : 13 ≤ e) (a b : Fin 3 → ℕ) (i : Fin 6)
    (hi : ∀ j : Fin 6, j ≠ i → Work.LinnikBurgess.shift a b i ≠ Work.LinnikBurgess.shift a b j) :
    Work.LinnikBurgess.gaussTwoRHS2 e (Work.LinnikBurgess.cubeLevel 2 e) a b
      ≤ Work.LinnikBurgess.localFactor 2 e a b :=
  Work.LinnikBurgess.lfSmall.counting_two
    Work.LinnikBurgess.lfSmall.two_transfer_d1
    Work.LinnikBurgess.lfSmall.two_transfer_d2
    Work.LinnikBurgess.lfSmall.nv_le_vcapD2
    Work.LinnikBurgess.lfSmall.lvlSet2_card_le
    Work.LinnikBurgess.lfSmall.capSet2_card_le
    Work.LinnikBurgess.lfSmall.content_dvd_critN
    Work.LinnikBurgess.lfSmall.dlp_of_supp
    Work.LinnikBurgess.lfSmall.localFactor_lower
    Work.LinnikBurgess.lfSmall.cap_term_le
    he a b i hi


theorem localFactor_bound_two {e : ℕ} (he : 2 ≤ e) (χ : DirichletCharacter ℂ (2 ^ e))
    (hχ : χ.IsPrimitive) (a b : Fin 3 → ℕ) (i : Fin 6)
    (hi : ∀ j : Fin 6, j ≠ i → Work.LinnikBurgess.shift a b i ≠ Work.LinnikBurgess.shift a b j) :
    ‖∑ x : ZMod (2 ^ e), χ (∏ l : Fin 3, (x + (a l : ZMod (2 ^ e))))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (2 ^ e)))))‖
      ≤ (2 : ℝ) ^ ((e : ℝ) / 2) * Work.LinnikBurgess.localFactor 2 e a b := by
  by_cases he12 : e ≤ 12
  · exact localFactor_bound_two_le12 he he12 χ a b
  · have he13' : 13 ≤ e := by omega
    have hcount := gaussTwoRHS2_le_localFactor_two he13' a b i hi
    have hpeel := corr6_twoPow_gaussTwo_le (m := Work.LinnikBurgess.cubeLevel 2 e)
      (Work.LinnikBurgess.lfSmall.one_le_cubeLevel he13')
      (Work.LinnikBurgess.lfSmall.three_mul_cubeLevel_ge (e := e))
      (Work.LinnikBurgess.lfSmall.two_mul_cubeLevel_le he13') χ hχ a b
    exact hpeel.trans (mul_le_mul_of_nonneg_left hcount (Real.rpow_nonneg (by norm_num) _))

end Work.LinnikAreas.u8own
