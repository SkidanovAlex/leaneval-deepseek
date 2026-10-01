import Mathlib
import Submission.Work.LinnikBurgess.burgess_lead_defs
import Submission.Work.LinnikBurgess.lfSmall.gaussTwo_le_odd
import Submission.Work.LinnikBurgess.lfSmall.counting_two
import Submission.Work.LinnikBurgess.lfSmall.counting_three
import Submission.Work.LinnikBurgess.lfSmall.two_transfer_d1
import Submission.Work.LinnikBurgess.lfSmall.two_transfer_d2
import Submission.Work.LinnikBurgess.lfSmall.nv_le_vcapD2
import Submission.Work.LinnikBurgess.lfSmall.lvlSet2_card_le
import Submission.Work.LinnikBurgess.lfSmall.capSet2_card_le
import Submission.Work.LinnikBurgess.lfSmall.content_dvd_critN
import Submission.Work.LinnikBurgess.lfSmall.dlp_of_supp
import Submission.Work.LinnikBurgess.lfSmall.localFactor_lower
import Submission.Work.LinnikBurgess.lfSmall.cap_term_le
import Submission.Work.ZeroFreeTables.P9F.twoPow_gaussTwo_le_aux

namespace Work.LinnikBurgess

open scoped BigOperators
open Classical

/-! ## Helpers for the small-prime local factor bound

We prove `Work.LinnikBurgess.localFactor_bound_small` in two regimes:

* `e ≤ 12`: the menu weights in `menuW` reduce to the single atom `729` at `(s,j) = (0,0)`, and the
  trivial bound `‖S‖ ≤ p^e ≤ 729 · p^{e/2}` (valid because `p ≤ 3`, `e ≤ 12`) settles it; if no unit
  class mod `p` exists at all (`¬ DLp p 0`), then every summand vanishes and `S = 0`.

* `e ≥ 13`: the stationary-phase/Gauss-sum Lemma A (`p` odd) or A₂ (`p = 2`) together with the
  Hensel root counts and the content analysis produce the graded bound.
-/

/-- A residue class of `ZMod (p^e)` whose representative is divisible by `p` is never a unit. -/
lemma not_isUnit_of_dvd_val {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) (z : ZMod (p ^ e))
    (h : p ∣ z.val) : ¬ IsUnit z := by
  haveI : NeZero (p ^ e) := ⟨pow_ne_zero e hp.pos.ne'⟩
  intro hz
  have hz' : IsUnit (((z.val : ℕ)) : ZMod (p ^ e)) := by
    rw [ZMod.natCast_zmod_val z]; exact hz
  have hc : z.val.Coprime (p ^ e) := (ZMod.isUnit_iff_coprime z.val (p ^ e)).mp hz'
  have hgcd : p ∣ Nat.gcd z.val (p ^ e) := Nat.dvd_gcd h (dvd_pow_self p (by omega : e ≠ 0))
  rw [hc.gcd_eq_one] at hgcd
  exact hp.not_dvd_one hgcd

/-- A product is a unit only if every factor is. -/
lemma not_isUnit_prod_of_not_isUnit {R : Type*} [CommMonoid R] {ι : Type*} [Fintype ι]
    {f : ι → R} {l : ι} (h : ¬ IsUnit (f l)) : ¬ IsUnit (∏ x, f x) := by
  intro hpr
  exact h (isUnit_of_dvd_unit (Finset.dvd_prod_of_mem f (Finset.mem_univ l)) hpr)

/-- If the generator `x` of a class modulo `p^e` cannot be shifted into a unit position at any of
the six shifts, then the correlation summand vanishes identically. -/
lemma corr6_eq_zero_of_no_unit {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e) (a b : Fin 3 → ℕ)
    (χ : DirichletCharacter ℂ (p ^ e))
    (h : ∀ y : ℕ, ∃ l : Fin 3, p ∣ y + a l ∨ p ∣ y + b l) :
    (∑ x : ZMod (p ^ e), χ (∏ l : Fin 3, (x + (a l : ZMod (p ^ e))))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (p ^ e)))))) = 0 := by
  have hp : p.Prime := Fact.out
  refine Finset.sum_eq_zero (fun x _ => ?_)
  have hpx : p ∣ p ^ e := dvd_pow_self p (by omega)
  obtain ⟨l, hl | hl⟩ := h x.val
  · have hcast : (x + (a l : ZMod (p ^ e))) = (((x.val + a l : ℕ)) : ZMod (p ^ e)) := by
      conv_lhs => rw [← ZMod.natCast_zmod_val x]
      push_cast
      ring
    have hdvd : p ∣ (x + (a l : ZMod (p ^ e))).val := by
      rw [hcast, ZMod.val_natCast]
      exact (Nat.dvd_mod_iff hpx).mpr hl
    have hnu : ¬ IsUnit (x + (a l : ZMod (p ^ e))) := not_isUnit_of_dvd_val hp (by omega) _ hdvd
    have hprodn : ¬ IsUnit (∏ l : Fin 3, (x + (a l : ZMod (p ^ e)))) :=
      not_isUnit_prod_of_not_isUnit (f := fun l => (x + (a l : ZMod (p ^ e)))) hnu
    rw [MulChar.map_nonunit χ hprodn, zero_mul]
  · have hcast : (x + (b l : ZMod (p ^ e))) = (((x.val + b l : ℕ)) : ZMod (p ^ e)) := by
      conv_lhs => rw [← ZMod.natCast_zmod_val x]
      push_cast
      ring
    have hdvd : p ∣ (x + (b l : ZMod (p ^ e))).val := by
      rw [hcast, ZMod.val_natCast]
      exact (Nat.dvd_mod_iff hpx).mpr hl
    have hnu : ¬ IsUnit (x + (b l : ZMod (p ^ e))) := not_isUnit_of_dvd_val hp (by omega) _ hdvd
    have hprodn : ¬ IsUnit (∏ l : Fin 3, (x + (b l : ZMod (p ^ e)))) :=
      not_isUnit_prod_of_not_isUnit (f := fun l => (x + (b l : ZMod (p ^ e)))) hnu
    rw [MulChar.map_nonunit χ hprodn]
    simp


/-- The trivial bound: the correlation sum has `p^e` summands of modulus at most `1`. -/
lemma corr6_norm_le {p e : ℕ} [Fact p.Prime] (χ : DirichletCharacter ℂ (p ^ e)) (a b : Fin 3 → ℕ) :
    ‖∑ x : ZMod (p ^ e), χ (∏ l : Fin 3, (x + (a l : ZMod (p ^ e))))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (p ^ e)))))‖ ≤ (p : ℝ) ^ e := by
  calc ‖∑ x : ZMod (p ^ e), χ (∏ l : Fin 3, (x + (a l : ZMod (p ^ e))))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (p ^ e)))))‖
      ≤ ∑ x : ZMod (p ^ e), ‖χ (∏ l : Fin 3, (x + (a l : ZMod (p ^ e))))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (p ^ e)))))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _x : ZMod (p ^ e), (1 : ℝ) := by
        refine Finset.sum_le_sum (fun x _ => ?_)
        rw [norm_mul, Complex.norm_conj]
        exact mul_le_one₀ (DirichletCharacter.norm_le_one χ _)
          (norm_nonneg _) (DirichletCharacter.norm_le_one χ _)
    _ = (p : ℝ) ^ e := by
        rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]
        push_cast
        ring

/-- The level `(e+3)/3` for `p = 2`. -/
lemma cubeLevel_eq_two (e : ℕ) : cubeLevel 2 e = (e + 3) / 3 := by simp [cubeLevel]

/-- The level `(e+2)/3` for `p = 3`. -/
lemma cubeLevel_eq_three (e : ℕ) : cubeLevel 3 e = (e + 2) / 3 := by simp [cubeLevel]

/-- `menuW` at `(s,j) = (0,0)` is `729` for `p ≤ 3`, `e ≤ 12`. -/
lemma menuW_small_atom {p e s j : ℕ} (hp5 : ¬ 5 ≤ p) (he12 : e ≤ 12) :
    menuW p e s j = (if s = 0 ∧ j = 0 then 729 else 0) := by
  rw [menuW, if_neg hp5, if_pos he12]

/-- For `p ≤ 3` and `e ≤ 12` the local factor is at least `729 · [DLp p 0 a b]`. -/
lemma localFactor_ge_small {p e : ℕ} (hp5 : ¬ 5 ≤ p) (he12 : e ≤ 12) (a b : Fin 3 → ℕ) :
    729 * (if DLp p 0 a b then 1 else 0) ≤ localFactor p e a b := by
  classical
  rw [localFactor]
  have hmem_s : (0 : ℕ) ∈ Finset.range (e + 2) := Finset.mem_range.mpr (by omega)
  have hmem_j : (0 : ℕ) ∈ Finset.range (e + 1) := Finset.mem_range.mpr (by omega)
  have hrow : (∑ j ∈ Finset.range (e + 1),
        menuW p e 0 j * (if DLp p 0 a b ∧ p ^ j ∣ contAB a b then 1 else 0))
      = 729 * (if DLp p 0 a b then 1 else 0) := by
    rw [Finset.sum_eq_single 0]
    · rw [menuW_small_atom hp5 he12]; simp [one_dvd]
    · intro j hj hne
      rw [menuW_small_atom hp5 he12]
      simp [hne]
    · intro h; exact absurd hmem_j h
  rw [← hrow]
  refine Finset.single_le_sum (f := fun s => ∑ j ∈ Finset.range (e + 1),
      menuW p e s j * (if DLp p s a b ∧ p ^ j ∣ contAB a b then 1 else 0)) ?_ hmem_s
  intro s hs
  refine Finset.sum_nonneg (fun j hj => ?_)
  rw [menuW_small_atom hp5 he12]
  by_cases h : s = 0 ∧ j = 0
  · rw [if_pos h]; positivity
  · rw [if_neg h]; norm_num


/-- Theorem L' (U8), small primes.  If a constant in `menuW` proves insufficient, enlarge it freely (route §7). -/
theorem localFactor_bound_small {p e : ℕ} [Fact p.Prime] (hp3 : p ≤ 3) (he : 2 ≤ e)
    (χ : DirichletCharacter ℂ (p ^ e)) (hχ : χ.IsPrimitive) (a b : Fin 3 → ℕ) (i : Fin 6)
    (hi : ∀ j : Fin 6, j ≠ i → shift a b i ≠ shift a b j) :
    ‖∑ x : ZMod (p ^ e), χ (∏ l : Fin 3, (x + (a l : ZMod (p ^ e))))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (p ^ e)))))‖
      ≤ (p : ℝ) ^ ((e : ℝ) / 2) * localFactor p e a b := by
  classical
  have hp : p.Prime := Fact.out
  have hp5 : ¬ 5 ≤ p := by omega
  have hpos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hp3' : (p : ℝ) ≤ 3 := by exact_mod_cast hp3
  by_cases he12 : e ≤ 12
  · -- ### Regime `e ≤ 12`: the menu collapses to the single atom `729`
    have hLF := localFactor_ge_small (p := p) (e := e) hp5 he12 a b
    by_cases hDL : DLp p 0 a b
    · have h729 : (p : ℝ) ^ ((e : ℝ) / 2) ≤ 729 := by
        calc (p : ℝ) ^ ((e : ℝ) / 2) ≤ (3 : ℝ) ^ ((e : ℝ) / 2) :=
              Real.rpow_le_rpow (le_of_lt hpos) hp3' (by positivity)
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
      have htriv := corr6_norm_le (p := p) (e := e) χ a b
      have hLF' : (729 : ℝ) ≤ localFactor p e a b := by
        simpa [hDL] using hLF
      calc ‖∑ x : ZMod (p ^ e), χ (∏ l : Fin 3, (x + (a l : ZMod (p ^ e))))
            * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (p ^ e)))))‖
          ≤ (p : ℝ) ^ e := htriv
        _ = (p : ℝ) ^ ((e : ℝ) / 2) * (p : ℝ) ^ ((e : ℝ) / 2) := hsq.symm
        _ ≤ (p : ℝ) ^ ((e : ℝ) / 2) * 729 :=
            mul_le_mul_of_nonneg_left h729 (Real.rpow_nonneg (le_of_lt hpos) _)
        _ ≤ (p : ℝ) ^ ((e : ℝ) / 2) * localFactor p e a b :=
            mul_le_mul_of_nonneg_left hLF' (Real.rpow_nonneg (le_of_lt hpos) _)
    · have hno : ∀ y : ℕ, ∃ l : Fin 3, p ∣ y + a l ∨ p ∣ y + b l := by
        intro y
        by_contra hcon
        push_neg at hcon
        exact hDL ⟨y, hcon, by norm_num, by norm_num⟩
      have hzero := corr6_eq_zero_of_no_unit (p := p) (e := e) (by omega) a b χ hno
      have hLF0 : (0 : ℝ) ≤ localFactor p e a b := by
        have := hLF
        rw [if_neg hDL] at this
        linarith
      rw [hzero, norm_zero]
      exact mul_nonneg (Real.rpow_nonneg (le_of_lt hpos) _) hLF0
  · -- ### Regime `e ≥ 13`: the graded bound
    have he13 : 13 ≤ e := by omega
    have hp23 : p = 2 ∨ p = 3 := by
      have h2 := hp.two_le
      omega
    rcases hp23 with rfl | rfl
    · -- `p = 2`: Lemma A₂ in the `gaussSum` bubble, then the `lfSmall` counting chain
      have h3 : e + 1 ≤ 3 * cubeLevel 2 e := by rw [cubeLevel_eq_two]; omega
      have h2 : 2 * cubeLevel 2 e ≤ e := by rw [cubeLevel_eq_two]; omega
      have hm : 1 ≤ cubeLevel 2 e := by rw [cubeLevel_eq_two]; omega
      have hA := Work.ZeroFreeTables.P9F.corr6_twoPow_gaussTwo_le_aux (e := e)
        (m := cubeLevel 2 e) hm h3 h2 χ hχ a b
      have hB : gaussTwoRHS2 e (cubeLevel 2 e) a b ≤ localFactor 2 e a b :=
        lfSmall.counting_two lfSmall.two_transfer_d1 lfSmall.two_transfer_d2 lfSmall.nv_le_vcapD2
          lfSmall.lvlSet2_card_le lfSmall.capSet2_card_le lfSmall.content_dvd_critN
          lfSmall.dlp_of_supp lfSmall.localFactor_lower lfSmall.cap_term_le he13 a b i hi
      calc ‖∑ x : ZMod (2 ^ e), χ (∏ l : Fin 3, (x + (a l : ZMod (2 ^ e))))
            * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (2 ^ e)))))‖
          ≤ (2 : ℝ) ^ ((e : ℝ) / 2) * gaussTwoRHS2 e (cubeLevel 2 e) a b := hA
        _ ≤ (2 : ℝ) ^ ((e : ℝ) / 2) * localFactor 2 e a b :=
            mul_le_mul_of_nonneg_left hB (by positivity)
    · -- `p = 3`: Lemma A (odd prime), then the `lfSmall` counting chain
      have h3 : e ≤ 3 * cubeLevel 3 e := by rw [cubeLevel_eq_three]; omega
      have h2 : 2 * cubeLevel 3 e ≤ e := by rw [cubeLevel_eq_three]; omega
      have hm : 1 ≤ cubeLevel 3 e := by rw [cubeLevel_eq_three]; omega
      have hA := lfSmall.gaussTwo_le_odd (p := 3) (e := e) (m := cubeLevel 3 e)
        (by norm_num) hm h3 h2 χ hχ a b
      have hB : gaussTwoRHS 3 e (cubeLevel 3 e) a b ≤ localFactor 3 e a b :=
        lfSmall.counting_three he13 a b i hi
      calc ‖∑ x : ZMod (3 ^ e), χ (∏ l : Fin 3, (x + (a l : ZMod (3 ^ e))))
            * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (3 ^ e)))))‖
          ≤ (3 : ℝ) ^ ((e : ℝ) / 2) * gaussTwoRHS 3 e (cubeLevel 3 e) a b := hA
        _ ≤ (3 : ℝ) ^ ((e : ℝ) / 2) * localFactor 3 e a b :=
            mul_le_mul_of_nonneg_left hB (by positivity)

end Work.LinnikBurgess

