/-
# Theorem L' (U8), small primes `p ≤ 3`

Re-emission of `Work.LinnikBurgess.localFactor_bound_small` as a `sorry`-free statement in a new file
(nothing under `Submission/Work/LinnikBurgess/` is edited).

The regime `e ≥ 13` is closed here by the graded (Lemmas A / A₂ + Hensel counting) route, which is
uniform in `e`:

* `p = 3`: the odd-prime two-digit bound `Work.LinnikBurgess.corr6_primePow_gaussTwo_le`
  (`‖S‖ ≤ 3^{e/2} gaussTwoRHS 3 e (cubeLevel 3 e) a b`) together with the counting lemma
  `Work.LinnikBurgess.lfSmall.counting_three` (`gaussTwoRHS 3 e (cubeLevel 3 e) a b ≤ localFactor 3 e a b`).
* `p = 2`: the `2`-adic two-digit bound `Work.ZeroFreeTables.P9F.corr6_twoPow_gaussTwo_le_aux` together
  with the counting lemma `Work.LinnikBurgess.lfSmall.counting_two`.

The `p = 2` two-digit bound is re-proved inside `Submission/Work/ZeroFreeTables/P9F/` because the
`p = 2` counting lemmas of `lfSmall/` and the existing `p = 2` peel live in two mutually incompatible
`Commons` import bubbles (both `...charCorrelation_twoPow` and `...gaussSum_normSq_eq_conductor`
declare `Commons.NumberTheory.DirichletCharacter.sum_zmod_eq_sum_range`).

The small range `e ≤ 12` uses the `729` atom of the menu (`localFactor_ge_small`) and the trivial
bound `‖S‖ ≤ p^e ≤ 729 p^{e/2}`; if no unit class mod `p` exists at all, every summand of `S` vanishes.
-/
import Mathlib
import Submission.Work.LinnikBurgess.localFactor_bound_small
import Submission.Work.LinnikBurgess.localFactor_bound_small_trivial
import Submission.Work.LinnikBurgess.corr6_primePow_gaussTwo_le
import Submission.Work.LinnikBurgess.lfSmall.counting_three
import Submission.Work.LinnikBurgess.lfSmall.counting_two
import Submission.Work.ZeroFreeTables.P9F.twoPow_api
import Submission.Work.ZeroFreeTables.P9F.twoPow_innerSum_factor_aux
import Submission.Work.ZeroFreeTables.P9F.twoPow_gaussTwo_le_aux

open scoped BigOperators

namespace Work.ZeroFreeTables.P9F

/-- Theorem L' (U8), small primes `p ≤ 3`: re-emission of
`Work.LinnikBurgess.localFactor_bound_small` as a `sorry`-free statement in a NEW file (do NOT edit
anything under `Submission/Work/LinnikBurgess/`).  There, the cases `¬ DLp p 0 a b` (all summands
vanish) and `DLp p 0 a b ∧ e ≤ 12` (via `Work.LinnikBurgess.corr6_norm_le` and
`localFactor_ge_small`, i.e. `p^e ≤ 729 · p^(e/2)`) are proved, and the regime `e ≥ 13` is the
only gap.  Route for that regime, using only counting -- the constant of the final Burgess bound
is existential, so no Gauss-sum input is needed: with the trivial bound `‖corr6‖ ≤ p^e` it
suffices to show the elementary lower bound
`(p : ℝ) ^ (e/2) ≤ Work.LinnikBurgess.localFactor p e a b` for `p ≤ 3`, `e ≥ 13`; then
`‖corr6‖ ≤ p^e = p^(e/2)·p^(e/2) ≤ p^(e/2)·localFactor p e a b`.  A crude lower bound (e.g. from
the menus `menuW`, whose `(s,j) = (0,0)` row already contributes `729`) is enough, and
`p^(e/2) ≤ 3^(e/2)`. -/
theorem localFactor_bound_small_aux {p e : ℕ} [Fact p.Prime] (hp3 : p ≤ 3) (he : 2 ≤ e)
    (χ : DirichletCharacter ℂ (p ^ e)) (hχ : χ.IsPrimitive) (a b : Fin 3 → ℕ) (i : Fin 6)
    (hi : ∀ j : Fin 6, j ≠ i → Work.LinnikBurgess.shift a b i ≠ Work.LinnikBurgess.shift a b j) :
    ‖∑ x : ZMod (p ^ e), χ (∏ l : Fin 3, (x + (a l : ZMod (p ^ e))))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (p ^ e)))))‖
      ≤ (p : ℝ) ^ ((e : ℝ) / 2) * Work.LinnikBurgess.localFactor p e a b := by
  classical
  have hp : p.Prime := Fact.out
  have hp5 : ¬ 5 ≤ p := by omega
  have hpos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpnn : (0 : ℝ) ≤ (p : ℝ) := le_of_lt hpos
  have hpR3 : (p : ℝ) ≤ 3 := by exact_mod_cast hp3
  have hp23 : p = 2 ∨ p = 3 := by
    rcases hp.eq_two_or_odd with h | h
    · exact Or.inl h
    · right
      have h2 : 2 ≤ p := hp.two_le
      omega
  by_cases he12 : e ≤ 12
  · -- ### Small `e`: the menu collapses to the single atom `729`
    have hLF := Work.LinnikBurgess.localFactor_ge_small (p := p) (e := e) hp5 he12 a b
    by_cases hDL : Work.LinnikBurgess.DLp p 0 a b
    · have h729 : (p : ℝ) ^ ((e : ℝ) / 2) ≤ 729 := by
        calc (p : ℝ) ^ ((e : ℝ) / 2) ≤ (3 : ℝ) ^ ((e : ℝ) / 2) :=
              Real.rpow_le_rpow (le_of_lt hpos) hpR3 (by positivity)
          _ ≤ (3 : ℝ) ^ (6 : ℝ) := by
              refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
              have : (e : ℝ) ≤ 12 := by exact_mod_cast he12
              linarith
          _ = 729 := by norm_num
      have hsq : (p : ℝ) ^ ((e : ℝ) / 2) * (p : ℝ) ^ ((e : ℝ) / 2) = (p : ℝ) ^ e := by
        rw [← Real.rpow_add hpos, ← Real.rpow_natCast (p : ℝ) e]
        congr 1
        push_cast
        ring
      have htriv := Work.LinnikBurgess.corr6_norm_le (p := p) (e := e) χ a b
      have hLF' : (729 : ℝ) ≤ Work.LinnikBurgess.localFactor p e a b := by
        simpa [hDL] using hLF
      calc ‖∑ x : ZMod (p ^ e), χ (∏ l : Fin 3, (x + (a l : ZMod (p ^ e))))
            * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (p ^ e)))))‖
          ≤ (p : ℝ) ^ e := htriv
        _ = (p : ℝ) ^ ((e : ℝ) / 2) * (p : ℝ) ^ ((e : ℝ) / 2) := hsq.symm
        _ ≤ (p : ℝ) ^ ((e : ℝ) / 2) * 729 :=
            mul_le_mul_of_nonneg_left h729 (Real.rpow_nonneg hpnn _)
        _ ≤ (p : ℝ) ^ ((e : ℝ) / 2) * Work.LinnikBurgess.localFactor p e a b :=
            mul_le_mul_of_nonneg_left hLF' (Real.rpow_nonneg hpnn _)
    · have hno : ∀ y : ℕ, ∃ l : Fin 3, p ∣ y + a l ∨ p ∣ y + b l := by
        intro y
        by_contra hcon
        push Not at hcon
        exact hDL ⟨y, hcon, by norm_num, by norm_num⟩
      have hzero := Work.LinnikBurgess.corr6_eq_zero_of_no_unit (p := p) (e := e) (by omega) a b χ hno
      have hLF0 : (0 : ℝ) ≤ Work.LinnikBurgess.localFactor p e a b :=
        Work.LinnikBurgess.localFactor_nonneg p e a b
      rw [hzero, norm_zero]
      exact mul_nonneg (Real.rpow_nonneg hpnn _) hLF0
  · -- ### `e ≥ 13`: the graded bound
    have he13 : 13 ≤ e := by omega
    rcases hp23 with hp2 | hp3
    · -- #### `p = 2`
      subst hp2
      have hm1 : 1 ≤ Work.LinnikBurgess.cubeLevel 2 e :=
        Work.LinnikBurgess.lfSmall.one_le_cubeLevel he13
      have h3m : e + 1 ≤ 3 * Work.LinnikBurgess.cubeLevel 2 e :=
        Work.LinnikBurgess.lfSmall.three_mul_cubeLevel_ge (e := e)
      have h2m : 2 * Work.LinnikBurgess.cubeLevel 2 e ≤ e :=
        Work.LinnikBurgess.lfSmall.two_mul_cubeLevel_le he13
      have hAA := corr6_twoPow_gaussTwo_le_aux (e := e) (m := Work.LinnikBurgess.cubeLevel 2 e)
        hm1 h3m h2m χ hχ a b
      have hCT := Work.LinnikBurgess.lfSmall.counting_two_aux
        Work.LinnikBurgess.lfSmall.two_transfer_d1
        Work.LinnikBurgess.lfSmall.two_transfer_d2
        Work.LinnikBurgess.lfSmall.nv_le_vcapD2
        Work.LinnikBurgess.lfSmall.lvlSet2_card_le
        Work.LinnikBurgess.lfSmall.capSet2_card_le
        Work.LinnikBurgess.lfSmall.content_dvd_critN
        Work.LinnikBurgess.lfSmall.dlp_of_supp
        Work.LinnikBurgess.lfSmall.localFactor_lower
        Work.LinnikBurgess.lfSmall.cap_term_le
        he13 a b i hi
      calc ‖∑ x : ZMod (2 ^ e), χ (∏ l : Fin 3, (x + (a l : ZMod (2 ^ e))))
            * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (2 ^ e)))))‖
          ≤ (2 : ℝ) ^ ((e : ℝ) / 2) * Work.LinnikBurgess.gaussTwoRHS2 e
              (Work.LinnikBurgess.cubeLevel 2 e) a b := hAA
        _ ≤ (2 : ℝ) ^ ((e : ℝ) / 2) * Work.LinnikBurgess.localFactor 2 e a b :=
            mul_le_mul_of_nonneg_left hCT (Real.rpow_nonneg (by norm_num) _)
    · -- #### `p = 3`
      subst hp3
      have hm1 : 1 ≤ Work.LinnikBurgess.cubeLevel 3 e :=
        Work.LinnikBurgess.lfSmall.one_le_cubeLevel_three he13
      have h3m : e ≤ 3 * Work.LinnikBurgess.cubeLevel 3 e := by
        rw [Work.LinnikBurgess.lfSmall.cubeLevel_three]
        have h := Nat.div_add_mod (e + 2) 3
        have h' := Nat.mod_lt (e + 2) (by norm_num : 0 < 3)
        omega
      have h2m : 2 * Work.LinnikBurgess.cubeLevel 3 e ≤ e := by
        rw [Work.LinnikBurgess.lfSmall.cubeLevel_three]
        have h := Nat.div_add_mod (e + 2) 3
        have h' := Nat.mod_lt (e + 2) (by norm_num : 0 < 3)
        omega
      have hAA := Work.LinnikBurgess.corr6_primePow_gaussTwo_le (p := 3) (e := e)
        (m := Work.LinnikBurgess.cubeLevel 3 e) (by norm_num) hm1 h3m h2m χ hχ a b
      have hCT := Work.LinnikBurgess.lfSmall.counting_three he13 a b i hi
      calc ‖∑ x : ZMod (3 ^ e), χ (∏ l : Fin 3, (x + (a l : ZMod (3 ^ e))))
            * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (3 ^ e)))))‖
          ≤ (3 : ℝ) ^ ((e : ℝ) / 2) * Work.LinnikBurgess.gaussTwoRHS 3 e
              (Work.LinnikBurgess.cubeLevel 3 e) a b := hAA
        _ ≤ (3 : ℝ) ^ ((e : ℝ) / 2) * Work.LinnikBurgess.localFactor 3 e a b :=
            mul_le_mul_of_nonneg_left hCT (Real.rpow_nonneg (by norm_num) _)

end Work.ZeroFreeTables.P9F
