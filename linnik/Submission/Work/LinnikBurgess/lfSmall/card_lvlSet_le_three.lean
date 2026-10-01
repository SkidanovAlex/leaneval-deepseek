import Mathlib
import Submission.Work.LinnikBurgess.lf_defs
import Submission.Work.LinnikBurgess.card_hensel_le
import Submission.Work.LinnikBurgess.card_lvlSet_le

namespace Work.LinnikBurgess.lfSmall

open Polynomial

/-! ### Arithmetic of `cubeLevel 3` and `capLevel 3`

(`lfSmall/counting_three.lean` carries the same facts but is currently being rewritten; they are
reproved here so that this module is self-contained.) -/

theorem cubeLevel_three_lvl (e : ℕ) : cubeLevel 3 e = (e + 2) / 3 := by
  rw [cubeLevel, if_neg (by norm_num : ¬ (3 = 2))]

theorem capLevel_three_lvl (e : ℕ) : capLevel 3 e = e - 2 * ((e + 2) / 3) := by
  rw [capLevel, cubeLevel_three_lvl]

theorem one_le_cubeLevel_three_lvl {e : ℕ} (he : 13 ≤ e) : 1 ≤ cubeLevel 3 e := by
  rw [cubeLevel_three_lvl]; omega

theorem capLevel_le_cubeLevel_three_lvl (e : ℕ) : capLevel 3 e ≤ cubeLevel 3 e := by
  rw [capLevel_three_lvl, cubeLevel_three_lvl]
  have h := Nat.div_add_mod (e + 2) 3
  have h' := Nat.mod_lt (e + 2) (by norm_num : 0 < 3)
  omega

/-- The `p = 3` analogue of `Work.LinnikBurgess.card_lvlSet_le`: for each level `s < capLevel 3 e`,
at most `natDegree (critN a b) ≤ 4` elements `y < 3^m` of the support of Lemma A have
`v_3(N'(y)) = s` exactly.  The proof is the same Hensel-set argument: every such `y` lies in
`henselSet 3 (critN a b) (cubeLevel 3 e)`, whose cardinality is at most the number of roots of
`critN a b` in `ℤ_[3]`, hence at most `natDegree (critN a b)`. -/
theorem card_lvlSet_le_three {e : ℕ} (he : 13 ≤ e) (a b : Fin 3 → ℕ)
    (hN : critN a b ≠ 0) (hdeg : (critN a b).natDegree ≤ 4)
    (hbt : SuppTransfer 3 e a b) {s : ℕ} (hs : s < capLevel 3 e) :
    (lvlSet 3 e a b s).card ≤ 4 := by
  classical
  have hm1 : 1 ≤ cubeLevel 3 e := one_le_cubeLevel_three_lvl he
  have hTle : capLevel 3 e ≤ cubeLevel 3 e := capLevel_le_cubeLevel_three_lvl e
  have hsub : lvlSet 3 e a b s ⊆ henselSet 3 (critN a b) (cubeLevel 3 e) := by
    intro y hy
    rw [lvlSet, Finset.mem_filter] at hy
    obtain ⟨hysupp, hnval⟩ := hy
    rw [suppSet, Finset.mem_filter] at hysupp
    obtain ⟨hyrange, hpred⟩ := hysupp
    have hyrange' : y < 3 ^ cubeLevel 3 e := Finset.mem_range.1 hyrange
    have hd0 : (critN a b).derivative.eval (y : ℤ) ≠ 0 := by
      intro h
      have hh : nval 3 e a b y = capLevel 3 e + 1 := by rw [nval, if_pos h]
      omega
    have hval : padicValNat 3 (((critN a b).derivative.eval (y : ℤ)).natAbs) = s := by
      rw [nval, if_neg hd0] at hnval
      exact hnval
    rw [henselSet, Finset.mem_filter]
    refine ⟨Finset.mem_range.2 hyrange', s, ?_, ?_, ?_⟩
    · exact (Int.dvd_natAbs).1 (dvd_of_padicValNat_eq hval)
    · exact not_dvd_int_of_padicValNat hd0 hval
    · obtain ⟨hbval, hdvdeval⟩ := hbt y hpred
      have hbval_s : bval 3 e a b y = s := by
        rw [hbval, hnval]
        exact min_eq_left (le_of_lt hs)
      have hdvd_eval : ((3 ^ (cubeLevel 3 e + s) : ℕ) : ℤ) ∣ (critN a b).eval (y : ℤ) := by
        rwa [hbval_s] at hdvdeval
      have hmax : max (2 * s + 1) (cubeLevel 3 e + s) = cubeLevel 3 e + s := by
        apply max_eq_right
        have : s < cubeLevel 3 e := lt_of_lt_of_le hs hTle
        omega
      simpa [hmax] using hdvd_eval
  calc (lvlSet 3 e a b s).card
      ≤ (henselSet 3 (critN a b) (cubeLevel 3 e)).card := Finset.card_le_card hsub
    _ ≤ (critN a b).natDegree := card_hensel_le _ hN _ hm1
    _ ≤ 4 := hdeg

end Work.LinnikBurgess.lfSmall
