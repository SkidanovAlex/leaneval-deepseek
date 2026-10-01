import Mathlib
import Submission.Work.LinnikAreas.u8own.u8three_ge26
import Submission.Work.LinnikAreas.u8own.localFactor_bound_two
import Submission.Work.LinnikBurgess.localFactor_bound_small
import Submission.Work.LinnikBurgess.localFactor_bound_small_trivial

/-!
# U8 (Theorem L') in my own namespace

`Work.LinnikBurgess.localFactor_bound_small` — the small-prime local factor bound, for `p ≤ 3` and
`e ≥ 2` — assembled in `Work.LinnikAreas.u8own`:

* `p = 2`: `localFactor_bound_two` (Lemma A₂ from the second-cluster copy of
  `corr6_twoPow_gaussTwo_le`, composed with the `lfSmall` counting);
* `p = 3`, `e ≤ 12` and `p ≤ 3`, `e ≤ 12`: the trivial slice `small_e` (`‖S‖ ≤ p^e ≤ p^{e/2}·729`
  via `localFactor_ge_small`, or `S = 0` via `corr6_eq_zero_of_no_unit`);
* `p = 3`, `13 ≤ e ≤ 25`: `localFactor_bound_three_le25`;
* `p = 3`, `26 ≤ e`: the copied chain `u8three_ge26` (whose three former `sorry`s are the
  `sorry`-free `u8three.transfer_three`, `u8three.lvlSet_card_three` and
  `Work.LinnikAreas.u8three.capSet_card_three`).
-/

open scoped BigOperators
open Work.LinnikBurgess

namespace Work.LinnikAreas.u8own

/-- U8 for `p ≤ 3` and `e ≤ 12` (the trivial slice). -/
theorem small_e {p e : ℕ} [Fact p.Prime] (hp3 : p ≤ 3) (he : 2 ≤ e) (he12 : e ≤ 12)
    (χ : DirichletCharacter ℂ (p ^ e)) (a b : Fin 3 → ℕ) :
    ‖∑ x : ZMod (p ^ e), χ (∏ l : Fin 3, (x + (a l : ZMod (p ^ e))))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (p ^ e)))))‖
      ≤ (p : ℝ) ^ ((e : ℝ) / 2) * localFactor p e a b := by
  classical
  have hp : p.Prime := Fact.out
  have hpnn : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
  by_cases hDL : DLp p 0 a b
  · have h10 := localFactor_ge_small (p := p) (e := e) (by omega) he12 a b
    rw [if_pos hDL] at h10
    have hp6 : (p : ℝ) ^ ((e : ℝ) / 2) ≤ 729 := by
      have h1 : (p : ℝ) ^ ((e : ℝ) / 2) ≤ (3 : ℝ) ^ ((e : ℝ) / 2) :=
        Real.rpow_le_rpow (by positivity) (by exact_mod_cast hp3) (by positivity)
      have h2 : (3 : ℝ) ^ ((e : ℝ) / 2) ≤ (3 : ℝ) ^ (6 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
          have : (e : ℝ) ≤ 12 := by exact_mod_cast he12
          linarith)
      have h3 : (3 : ℝ) ^ (6 : ℝ) = 729 := by norm_num
      linarith [h1, h2, h3.le, h3.ge]
    calc ‖∑ x : ZMod (p ^ e), χ (∏ l : Fin 3, (x + (a l : ZMod (p ^ e))))
          * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (p ^ e)))))‖
        ≤ (p : ℝ) ^ e := corr6_norm_le χ a b
      _ = (p : ℝ) ^ ((e : ℝ) / 2) * (p : ℝ) ^ ((e : ℝ) / 2) := by
          rw [← Real.rpow_add (by exact_mod_cast hp.pos), ← Real.rpow_natCast (p : ℝ) e]
          congr 1; ring
      _ ≤ (p : ℝ) ^ ((e : ℝ) / 2) * 729 :=
          mul_le_mul_of_nonneg_left hp6 (Real.rpow_nonneg hpnn _)
      _ ≤ (p : ℝ) ^ ((e : ℝ) / 2) * localFactor p e a b :=
          mul_le_mul_of_nonneg_left (by simpa using h10) (Real.rpow_nonneg hpnn _)
  · have hno : ∀ y : ℕ, ∃ l : Fin 3, p ∣ y + a l ∨ p ∣ y + b l := by
      intro y
      by_contra hcon
      push_neg at hcon
      exact hDL ⟨y, hcon, one_dvd _, one_dvd _⟩
    have hzero := corr6_eq_zero_of_no_unit (p := p) (e := e) (by omega) a b χ hno
    rw [hzero, norm_zero]
    exact mul_nonneg (Real.rpow_nonneg hpnn _) (localFactor_nonneg p e a b)

/-- **U8 (Theorem L'), `p ≤ 3`**, in my own namespace.  Same statement as
`Work.LinnikBurgess.localFactor_bound_small`. -/
theorem localFactor_bound_small {p e : ℕ} [Fact p.Prime] (hp3 : p ≤ 3) (he : 2 ≤ e)
    (χ : DirichletCharacter ℂ (p ^ e)) (hχ : χ.IsPrimitive) (a b : Fin 3 → ℕ) (i : Fin 6)
    (hi : ∀ j : Fin 6, j ≠ i → shift a b i ≠ shift a b j) :
    ‖∑ x : ZMod (p ^ e), χ (∏ l : Fin 3, (x + (a l : ZMod (p ^ e))))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (p ^ e)))))‖
      ≤ (p : ℝ) ^ ((e : ℝ) / 2) * localFactor p e a b := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  interval_cases p
  · -- p = 2
    exact localFactor_bound_two he χ hχ a b i hi
  · -- p = 3
    by_cases he12 : e ≤ 12
    · exact small_e (by norm_num) he he12 χ a b
    · by_cases he25 : e ≤ 25
      · exact Work.LinnikBurgess.localFactor_bound_three_le25 (by omega) he25 χ a b
      · exact Work.LinnikAreas.u8three.localFactor_bound_three_ge26 (by omega) χ hχ a b i hi

end Work.LinnikAreas.u8own
