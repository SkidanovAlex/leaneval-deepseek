import Mathlib
import Submission.Work.LinnikBurgess.burgess_lead_defs
import Submission.Work.LinnikBurgess.localFactor_bound_small

/-!
# U8 (Theorem L'), the *trivial* slice

`Work.LinnikBurgess.localFactor_bound_small` (U8, `p ≤ 3`) is proved for `e ≤ 12` and missing for
`e ≥ 13`.  This file closes a whole sub-range of `e ≥ 13` with no Hensel counting at all:

`localFactor p e a b ≥ menuW p e 0 0 ≥ 10^6` whenever a unit class exists (the `(s,j) = (0,0)`
atom of the menu), and `‖S‖ ≤ p^e` always (`corr6_norm_le`); if no unit class exists then every
summand of `S` vanishes (`corr6_eq_zero_of_no_unit`).  Hence for `p ≤ 3`, `13 ≤ e` and
`p^(e/2) ≤ 10^6`,

`‖S_{p^e}‖ ≤ p^e ≤ p^(e/2)·10^6 ≤ p^(e/2)·localFactor(p,e,a,b)`.

The condition `p^(e/2) ≤ 10^6` is exactly `e/2·log p ≤ 6·log 10`, i.e. `e ≤ 39` for `p = 2` and
`e ≤ 25` for `p = 3`; the two concrete corollaries below record those shapes, which is what a
caller proving the `e ≥ 13` branch of U8 needs.  The remaining hard range is therefore
`p = 2, e ≥ 40` and `p = 3, e ≥ 26`, where the graded bound (Lemma A / A₂ plus the Hensel counts)
is genuinely required.

From `localFactor_bound_small` only the two `sorryAx`-free helpers `corr6_norm_le` and
`corr6_eq_zero_of_no_unit` are used; `#print axioms` confirms this file is `sorryAx`-free.
-/

open Classical

open scoped BigOperators

set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.LinnikBurgess

/-! ## The `(s,j) = (0,0)` atom of the menu -/

/-- For `p ≤ 3` and `e ≥ 13` the menu atom `(s,j) = (0,0)` is at least `10^6`. -/
lemma menuW_atom_ge {p e : ℕ} (hp5 : ¬ 5 ≤ p) (he13 : ¬ e ≤ 12) : (10 : ℝ) ^ 6 ≤ menuW p e 0 0 := by
  rw [menuW, if_neg hp5, if_neg he13]
  have h1 : (0 : ℕ) = 0 ∧ (0 : ℕ) ≤ capLevel p e := ⟨rfl, Nat.zero_le _⟩
  rw [if_pos h1]
  have h2 : (0 : ℝ) ≤ (if (0 : ℕ) = max (capLevel p e) 0 then
      (10 : ℝ) ^ 6 * (p : ℝ) ^ (((cubeLevel p e : ℝ) + ((0 : ℕ) : ℝ)) / 2) else 0) := by
    by_cases hc : (0 : ℕ) = max (capLevel p e) 0
    · rw [if_pos hc]
      exact mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg p) _)
    · rw [if_neg hc]
  rw [Nat.cast_zero, zero_div, Real.rpow_zero, mul_one]
  linarith

/-- For `p ≤ 3`, `e ≥ 13` and `j ≠ 0` the menu atom `(s,j) = (0,j)` vanishes. -/
lemma menuW_atom_eq_zero {p e : ℕ} (hp5 : ¬ 5 ≤ p) (he13 : ¬ e ≤ 12) {j : ℕ} (hj : j ≠ 0) :
    menuW p e 0 j = 0 := by
  rw [menuW, if_neg hp5, if_neg he13]
  have h1 : ¬ (j = 0 ∧ (0 : ℕ) ≤ capLevel p e) := fun h => hj h.1
  have h2 : ¬ ((0 : ℕ) = max (capLevel p e) j) := by
    intro h
    have hle : j ≤ 0 := h ▸ le_max_right (capLevel p e) j
    exact hj (Nat.eq_zero_of_le_zero hle)
  rw [if_neg h1, if_neg h2, add_zero]

/-- Every menu weight is nonnegative. -/
lemma menuW_nonneg (p e s j : ℕ) : (0 : ℝ) ≤ menuW p e s j := by
  rw [menuW]
  split_ifs <;> positivity

/-- If a unit class mod `p` exists then the local factor is at least the `10^6` atom. -/
lemma localFactor_ge_atom {p e : ℕ} (hp5 : ¬ 5 ≤ p) (he13 : ¬ e ≤ 12) (a b : Fin 3 → ℕ)
    (hDL : DLp p 0 a b) : (10 : ℝ) ^ 6 ≤ localFactor p e a b := by
  classical
  have hmem_s : (0 : ℕ) ∈ Finset.range (e + 2) := Finset.mem_range.mpr (by omega)
  have hmem_j : (0 : ℕ) ∈ Finset.range (e + 1) := Finset.mem_range.mpr (by omega)
  have h00 : (10 : ℝ) ^ 6 ≤ menuW p e 0 0
      * (if DLp p 0 a b ∧ p ^ 0 ∣ contAB a b then 1 else 0) := by
    rw [if_pos ⟨hDL, one_dvd _⟩, mul_one]
    exact menuW_atom_ge hp5 he13
  have hrow : menuW p e 0 0 * (if DLp p 0 a b ∧ p ^ 0 ∣ contAB a b then 1 else 0)
      = ∑ j ∈ Finset.range (e + 1),
          menuW p e 0 j * (if DLp p 0 a b ∧ p ^ j ∣ contAB a b then 1 else 0) :=
    (Finset.sum_eq_single
      (f := fun j => menuW p e 0 j * (if DLp p 0 a b ∧ p ^ j ∣ contAB a b then 1 else 0)) 0
      (fun j hj hne => by rw [menuW_atom_eq_zero hp5 he13 hne, zero_mul])
      (fun h => absurd hmem_j h)).symm
  calc (10 : ℝ) ^ 6
      ≤ menuW p e 0 0 * (if DLp p 0 a b ∧ p ^ 0 ∣ contAB a b then 1 else 0) := h00
    _ = ∑ j ∈ Finset.range (e + 1),
          menuW p e 0 j * (if DLp p 0 a b ∧ p ^ j ∣ contAB a b then 1 else 0) := hrow
    _ ≤ ∑ s ∈ Finset.range (e + 2), ∑ j ∈ Finset.range (e + 1),
          menuW p e s j * (if DLp p s a b ∧ p ^ j ∣ contAB a b then 1 else 0) :=
        Finset.single_le_sum
          (f := fun s => ∑ j ∈ Finset.range (e + 1),
            menuW p e s j * (if DLp p s a b ∧ p ^ j ∣ contAB a b then 1 else 0))
          (fun s hs => Finset.sum_nonneg (fun j hj => by
            by_cases hc : DLp p s a b ∧ p ^ j ∣ contAB a b
            · rw [if_pos hc, mul_one]
              exact menuW_nonneg p e s j
            · rw [if_neg hc, mul_zero])) hmem_s
    _ = localFactor p e a b := rfl

/-- `localFactor` is always nonnegative. -/
lemma localFactor_nonneg (p e : ℕ) (a b : Fin 3 → ℕ) : (0 : ℝ) ≤ localFactor p e a b := by
  rw [localFactor]
  refine Finset.sum_nonneg (fun s _ => Finset.sum_nonneg (fun j _ => ?_))
  by_cases hc : DLp p s a b ∧ p ^ j ∣ contAB a b
  · rw [if_pos hc, mul_one]
    exact menuW_nonneg p e s j
  · rw [if_neg hc, mul_zero]

/-! ## The trivial slice of U8 -/

/-- **U8, trivial slice.**  For `p ≤ 3`, `13 ≤ e` and `p^(e/2) ≤ 10^6`, the complete cubic
correlation is bounded by `p^(e/2) · localFactor p e a b`.  Neither primitivity of `χ` nor the
singleton hypothesis is needed here. -/
theorem localFactor_bound_small_trivial {p e : ℕ} [Fact p.Prime] (hp3 : p ≤ 3) (he : 13 ≤ e)
    (hsmall : (p : ℝ) ^ ((e : ℝ) / 2) ≤ 10 ^ 6)
    (χ : DirichletCharacter ℂ (p ^ e)) (a b : Fin 3 → ℕ) :
    ‖∑ x : ZMod (p ^ e), χ (∏ l : Fin 3, (x + (a l : ZMod (p ^ e))))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (p ^ e)))))‖
      ≤ (p : ℝ) ^ ((e : ℝ) / 2) * localFactor p e a b := by
  classical
  have hp : p.Prime := Fact.out
  have hp5 : ¬ 5 ≤ p := by omega
  have he13 : ¬ e ≤ 12 := by omega
  have hpnn : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
  by_cases hDL : DLp p 0 a b
  · have h10 := localFactor_ge_atom (p := p) (e := e) hp5 he13 a b hDL
    calc ‖∑ x : ZMod (p ^ e), χ (∏ l : Fin 3, (x + (a l : ZMod (p ^ e))))
          * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (p ^ e)))))‖
        ≤ (p : ℝ) ^ e := corr6_norm_le (p := p) (e := e) χ a b
      _ = (p : ℝ) ^ ((e : ℝ) / 2) * (p : ℝ) ^ ((e : ℝ) / 2) := by
          rw [← Real.rpow_add (by exact_mod_cast hp.pos), ← Real.rpow_natCast (p : ℝ) e]
          congr 1
          ring
      _ ≤ (p : ℝ) ^ ((e : ℝ) / 2) * 10 ^ 6 :=
          mul_le_mul_of_nonneg_left hsmall (Real.rpow_nonneg hpnn _)
      _ ≤ (p : ℝ) ^ ((e : ℝ) / 2) * localFactor p e a b :=
          mul_le_mul_of_nonneg_left h10 (Real.rpow_nonneg hpnn _)
  · have hno : ∀ y : ℕ, ∃ l : Fin 3, p ∣ y + a l ∨ p ∣ y + b l := by
      intro y
      by_contra hcon
      push Not at hcon
      exact hDL ⟨y, hcon, one_dvd _, one_dvd _⟩
    have hzero := corr6_eq_zero_of_no_unit (p := p) (e := e) (by omega) a b χ hno
    rw [hzero, norm_zero]
    exact mul_nonneg (Real.rpow_nonneg hpnn _) (localFactor_nonneg p e a b)

/-- The trivial slice in the shape U8 needs for `p = 2`: `13 ≤ e ≤ 39`. -/
theorem localFactor_bound_two_le39 {e : ℕ} (he : 13 ≤ e) (he39 : e ≤ 39)
    (χ : DirichletCharacter ℂ (2 ^ e)) (a b : Fin 3 → ℕ) :
    ‖∑ x : ZMod (2 ^ e), χ (∏ l : Fin 3, (x + (a l : ZMod (2 ^ e))))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (2 ^ e)))))‖
      ≤ (2 : ℝ) ^ ((e : ℝ) / 2) * localFactor 2 e a b := by
  refine localFactor_bound_small_trivial (p := 2) (e := e) (by norm_num) he ?_ χ a b
  have h1 : (e : ℝ) / 2 ≤ ((39 : ℕ) : ℝ) / 2 := by
    have : (e : ℝ) ≤ 39 := by exact_mod_cast he39
    linarith
  have h2 : (2 : ℝ) ^ ((e : ℝ) / 2) ≤ (2 : ℝ) ^ (((39 : ℕ) : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
  have hsq : ((2 : ℝ) ^ (((39 : ℕ) : ℝ) / 2)) ^ 2 = (2 : ℝ) ^ (((39 : ℕ) : ℝ)) := by
    rw [sq, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    norm_num
  have hle : ((2 : ℝ) ^ (((39 : ℕ) : ℝ) / 2)) ^ 2 ≤ ((10 : ℝ) ^ 6) ^ 2 := by
    rw [hsq, Real.rpow_natCast]
    norm_num
  refine h2.trans ((pow_le_pow_iff_left₀ (Real.rpow_nonneg (by norm_num) _)
    (by norm_num : (0 : ℝ) ≤ (10 : ℝ) ^ 6) (by norm_num : (2 : ℕ) ≠ 0)).mp hle)

/-- The trivial slice in the shape U8 needs for `p = 3`: `13 ≤ e ≤ 25`. -/
theorem localFactor_bound_three_le25 {e : ℕ} (he : 13 ≤ e) (he25 : e ≤ 25)
    (χ : DirichletCharacter ℂ (3 ^ e)) (a b : Fin 3 → ℕ) :
    ‖∑ x : ZMod (3 ^ e), χ (∏ l : Fin 3, (x + (a l : ZMod (3 ^ e))))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (3 ^ e)))))‖
      ≤ (3 : ℝ) ^ ((e : ℝ) / 2) * localFactor 3 e a b := by
  refine localFactor_bound_small_trivial (p := 3) (e := e) (by norm_num) he ?_ χ a b
  have h1 : (e : ℝ) / 2 ≤ ((25 : ℕ) : ℝ) / 2 := by
    have : (e : ℝ) ≤ 25 := by exact_mod_cast he25
    linarith
  have h2 : (3 : ℝ) ^ ((e : ℝ) / 2) ≤ (3 : ℝ) ^ (((25 : ℕ) : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
  have hsq : ((3 : ℝ) ^ (((25 : ℕ) : ℝ) / 2)) ^ 2 = (3 : ℝ) ^ (((25 : ℕ) : ℝ)) := by
    rw [sq, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    norm_num
  have hle : ((3 : ℝ) ^ (((25 : ℕ) : ℝ) / 2)) ^ 2 ≤ ((10 : ℝ) ^ 6) ^ 2 := by
    rw [hsq, Real.rpow_natCast]
    norm_num
  refine h2.trans ((pow_le_pow_iff_left₀ (Real.rpow_nonneg (by norm_num) _)
    (by norm_num : (0 : ℝ) ≤ (10 : ℝ) ^ 6) (by norm_num : (2 : ℕ) ≠ 0)).mp hle)

end Work.LinnikBurgess
