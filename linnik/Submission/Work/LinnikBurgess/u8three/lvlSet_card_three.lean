import Mathlib
import Submission.Work.LinnikBurgess.card_lvlSet_le
import Submission.Work.LinnikBurgess.lf_defs

namespace Work.LinnikBurgess.u8three

open Polynomial

/-- `cubeLevel 3 e = (e + 2) / 3`. -/
theorem cubeLevel_three (e : ℕ) : cubeLevel 3 e = (e + 2) / 3 := by
  rw [cubeLevel, if_neg (by norm_num : (3:ℕ) ≠ 2)]

/-- `capLevel 3 e = e - 2 * ((e + 2) / 3)`. -/
theorem capLevel_three (e : ℕ) : capLevel 3 e = e - 2 * ((e + 2) / 3) := by
  rw [capLevel, cubeLevel_three]

/-- For `e ≥ 13`, the cube level at `p = 3` is at least `1`. -/
theorem one_le_cubeLevel_three {e : ℕ} (he : 13 ≤ e) : 1 ≤ cubeLevel 3 e := by
  rw [cubeLevel_three]
  omega

/-- For `e ≥ 13`, the cap level at `p = 3` does not exceed the cube level. -/
theorem capLevel_le_cubeLevel_three {e : ℕ} (he : 13 ≤ e) :
    capLevel 3 e ≤ cubeLevel 3 e := by
  rw [capLevel_three, cubeLevel_three]
  omega

/-- For `p = 3` and `13 ≤ e`, at each level `s < capLevel 3 e` at most `4 = natDegree N`
elements `y < 3^(cubeLevel 3 e)` of the support of Lemma A have `nval y = s` exactly, where
`N = critN a b`.  This is `Work.LinnikBurgess.card_lvlSet_le` (`p ≥ 5`) specialised to `p = 3`. -/
theorem lvlSet_card_three {e : ℕ} (he : 13 ≤ e) (a b : Fin 3 → ℕ)
    (hN : critN a b ≠ 0) (hdeg : (critN a b).natDegree ≤ 4)
    (hbt : SuppTransfer 3 e a b) {s : ℕ} (hs : s < capLevel 3 e) :
    (lvlSet 3 e a b s).card ≤ 4 := by
  classical
  have hm1 : 1 ≤ cubeLevel 3 e := one_le_cubeLevel_three he
  have hTle : capLevel 3 e ≤ cubeLevel 3 e := capLevel_le_cubeLevel_three he
  have hsub : lvlSet 3 e a b s ⊆ henselSet 3 (critN a b) (cubeLevel 3 e) := by
    intro y hy
    rw [lvlSet, Finset.mem_filter] at hy
    obtain ⟨hysupp, hnval⟩ := hy
    rw [suppSet, Finset.mem_filter] at hysupp
    obtain ⟨hyrange, hpred⟩ := hysupp
    have hyrange' : y < 3 ^ cubeLevel 3 e := Finset.mem_range.1 hyrange
    have hpred2 : suppPred 3 e a b y := hpred
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
    · rw [suppPred] at hpred2
      obtain ⟨hbval, hdvdeval⟩ := hbt y hpred2
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

end Work.LinnikBurgess.u8three
