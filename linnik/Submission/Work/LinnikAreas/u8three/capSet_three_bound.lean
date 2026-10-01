import Mathlib
import Submission.Work.LinnikBurgess.lfSmall.capcount_three
import Submission.Work.LinnikBurgess.lfSmall.card_lvlSet_le_three
import Submission.Work.LinnikBurgess.lfSmall.content_dvd_critN
import Submission.Work.LinnikBurgess.lfSmall.content_three
import Submission.Work.LinnikBurgess.critN_ne_zero_of_unique
import Submission.Work.LinnikBurgess.natDegree_critN_le_four

open scoped BigOperators
open Classical

namespace Work.LinnikAreas.u8three

open Work.LinnikBurgess

/-- `(z + 2) / 2 = z / 2 + 1`. -/
private lemma div2_add (z : ℕ) : (z + 2) / 2 = z / 2 + 1 := by
  have h : z + 2 = 2 * (z / 2 + 1) + z % 2 := by
    have h1 := Nat.div_add_mod z 2
    have h2 := Nat.mod_lt z (by norm_num : 0 < 2)
    omega
  rw [h, Nat.mul_add_div (by norm_num : 0 < 2)]
  have hz : z % 2 / 2 = 0 := Nat.div_eq_of_lt (Nat.mod_lt z (by norm_num))
  rw [hz, add_zero]

/-- Floor-division step used in the exponent comparison. -/
private lemma div2_step (y : ℕ) : (y + 1) / 2 ≤ (y - 1) / 2 + 1 := by
  rcases Nat.eq_zero_or_pos y with hy | hy
  · subst hy; norm_num
  · have h : y + 1 = (y - 1) + 2 := by omega
    rw [h, div2_add]

/-- Exponent comparison: the `p = 3` content bound of `lfSmall.cap_count_content_three` is indexed
by `J`; written in the `j = min J e` shape it loses at most one power of `3`. -/
theorem exp_cmp {m T J e : ℕ} (hT : T ≤ m) (hsum : m + T ≤ e) :
    max 0 (m - (m + T - J - 1) / 2)
      ≤ m - (m + T - min J e + 1) / 2 + 1 := by
  rcases le_total J e with hJe | heJ
  · rw [min_eq_left_iff.mpr hJe]
    set X := (m + T - J - 1) / 2 with hX
    set Y := (m + T - J + 1) / 2 with hY
    have hYX : Y ≤ X + 1 := by
      rcases Nat.eq_zero_or_pos (m + T - J) with h0 | hpos
      · have h1 : m + T - J - 1 = 0 := by omega
        have h2 : m + T - J + 1 = 1 := by omega
        rw [hX, hY, h1, h2]
        norm_num
      · have h3 : m + T - J + 1 = (m + T - J - 1) + 2 := by omega
        rw [hY, hX, h3, div2_add]
    refine max_le (Nat.zero_le _) ?_
    omega
  · rw [min_eq_right_iff.mpr heJ]
    have hK0 : (m + T - e + 1) / 2 = 0 := by omega
    have hJ1 : m + T - J - 1 = 0 := by omega
    rw [hK0, hJ1]
    refine max_le (Nat.zero_le _) ?_
    omega

/-- The content bound at `p = 3`, `10^3 · 3^E_J`, is dominated by the `j = min J e` shape with
constant `3000` (one extra power of `3`). -/
theorem exp_step {m T J e : ℕ} (hT : T ≤ m) (hsum : m + T ≤ e) :
    (10:ℕ)^3 * 3 ^ max 0 (m - (m + T - J - 1) / 2)
      ≤ 3000 * 3 ^ (m - (m + T - min J e + 1) / 2) := by
  have hc := exp_cmp (m := m) (T := T) (J := J) (e := e) hT hsum
  calc (10:ℕ)^3 * 3 ^ max 0 (m - (m + T - J - 1) / 2)
      = 1000 * 3 ^ max 0 (m - (m + T - J - 1) / 2) := by norm_num
    _ ≤ 1000 * 3 ^ (m - (m + T - min J e + 1) / 2 + 1) :=
        Nat.mul_le_mul (le_refl 1000) (Nat.pow_le_pow_right (by norm_num) hc)
    _ = 3000 * 3 ^ (m - (m + T - min J e + 1) / 2) := by rw [pow_succ]; ring

/-- **The `p = 3` capped-support bound in the shape used by the `e ≥ 13` regime.**  With
`J = v_3(contAB a b)` and `j = min J e`, the capped support has at most
`3000 · 3^(m - ⌈(m+T-j)/2⌉)` points (`m = cubeLevel 3 e`, `T = capLevel 3 e`).  The constant
`3000` is well below the `10^6` budget of the `(capLevel 3 e, 0)` menu term. -/
theorem capSet_three_bound {e J j : ℕ} (he : 13 ≤ e) (a b : Fin 3 → ℕ) (i : Fin 6)
    (hi : ∀ j' : Fin 6, j' ≠ i → shift a b i ≠ shift a b j')
    (hbt : SuppTransfer 3 e a b)
    (hJdef : padicValNat 3 (contAB a b) = J) (hjdef : j = min J e) :
    (capSet 3 e a b).card
      ≤ 3000 * 3 ^ (cubeLevel 3 e - (cubeLevel 3 e + capLevel 3 e - j + 1) / 2) := by
  classical
  obtain ⟨hdeg2, hc0⟩ := critN_ne_zero_of_unique a b i hi
  have hdeg : (critN a b).natDegree ≤ 4 := natDegree_critN_le_four a b
  have hJdiv : (3 ^ J : ℕ) ∣ contAB a b := by rw [← hJdef]; exact pow_padicValNat_dvd
  have hJndiv : ¬ ((3 ^ (J + 1) : ℕ) ∣ contAB a b) := by
    intro hd
    have hle : J + 1 ≤ padicValNat 3 (contAB a b) :=
      (padicValNat_dvd_iff_le (p := 3) (n := J + 1) (a := contAB a b) hc0).mp hd
    omega
  have hTle : capLevel 3 e ≤ cubeLevel 3 e := lfSmall.capLevel_le_cubeLevel_three_lvl e
  have hsum : cubeLevel 3 e + capLevel 3 e ≤ e := by
    have hm := lfSmall.cubeLevel_three_lvl e
    have hT := lfSmall.capLevel_three_lvl e
    have h2 : 2 * ((e + 2) / 3) ≤ e := by omega
    omega
  rcases Nat.eq_zero_or_pos J with hJ0 | hJpos
  · have hmod : ¬ (3 : ℕ) ∣ contAB a b := by
      intro hd
      have hle : 1 ≤ padicValNat 3 (contAB a b) :=
        (padicValNat_dvd_iff_le (p := 3) (n := 1) (a := contAB a b) hc0).mp (by simpa using hd)
      omega
    have h100 := lfSmall.cap_count_noncontent_three he a b hdeg2 hdeg hmod hbt
    have hK : (cubeLevel 3 e + capLevel 3 e - j + 1) / 2 ≤ cubeLevel 3 e := by
      rw [hjdef, hJ0, min_eq_left_iff.mpr (Nat.zero_le e)]
      omega
    have h3 : 1 ≤ 3 ^ (cubeLevel 3 e - (cubeLevel 3 e + capLevel 3 e - j + 1) / 2) :=
      Nat.one_le_pow _ _ (by norm_num)
    refine h100.trans ?_
    calc (100:ℕ) = 100 * 1 := (mul_one 100).symm
      _ ≤ 100 * 3 ^ (cubeLevel 3 e - (cubeLevel 3 e + capLevel 3 e - j + 1) / 2) :=
          Nat.mul_le_mul (le_refl 100) h3
      _ ≤ 3000 * 3 ^ (cubeLevel 3 e - (cubeLevel 3 e + capLevel 3 e - j + 1) / 2) :=
          Nat.mul_le_mul (by norm_num) (le_refl _)
  · by_cases hall : ∀ n : ℕ, ((3 ^ (J + 1) : ℕ) : ℤ) ∣ (critN a b).coeff n
    · have hprim : ∃ n : ℕ, ¬ ((3 ^ (J + 2) : ℕ) : ℤ) ∣ (critN a b).coeff n := by
        by_contra hcon
        push_neg at hcon
        exact hJndiv (by
          have hN := lfSmall.content_three (a := a) (b := b) i hi (h := J + 2) hcon
          simpa using hN)
      have hb := lfSmall.cap_count_content_three (e := e) (h := J + 1) (J := J) he a b hdeg2 hdeg
        hall hprim hbt (by omega) (le_refl _) hJdiv hJndiv
      rw [hjdef]
      exact hb.trans (exp_step hTle hsum)
    · push_neg at hall
      obtain ⟨n0, hn0⟩ := hall
      have hcontent : ∀ n : ℕ, ((3 ^ J : ℕ) : ℤ) ∣ (critN a b).coeff n :=
        fun n => lfSmall.dvd_coeff_critN_of_dvd_contAB (3 ^ J) a b hJdiv n
      have hprim : ∃ n : ℕ, ¬ ((3 ^ (J + 1) : ℕ) : ℤ) ∣ (critN a b).coeff n := ⟨n0, hn0⟩
      have hb := lfSmall.cap_count_content_three (e := e) (h := J) (J := J) he a b hdeg2 hdeg
        hcontent hprim hbt hJpos (by omega) hJdiv hJndiv
      rw [hjdef]
      exact hb.trans (exp_step hTle hsum)

end Work.LinnikAreas.u8three
