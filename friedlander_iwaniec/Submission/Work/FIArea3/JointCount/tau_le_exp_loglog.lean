import Mathlib
import Submission.Work.FIArea3.JointCount.tauDefs
import Submission.Work.FIArea3.JointCount.gn_ge
import Submission.Work.FIArea3.JointCount.g3_ge
import Submission.Work.FIArea3.JointCount.SB_int_le

namespace Work.FIArea3.JointCount

/-- The divisor function is bounded by `exp (1.5 log (n+2) / log log (n+2))`. -/
theorem tau_le_exp_loglog (n : ℕ) (hn : 1 ≤ n) :
    ((n.divisors.card : ℕ) : ℝ)
      ≤ Real.exp (1.5 * Real.log ((n : ℝ) + 2) / Real.log (Real.log ((n : ℝ) + 2))) := by
  set m : ℝ := (n:ℝ) + 2 with hm
  have hm3 : (3:ℝ) ≤ m := by
    have h1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    rw [hm]
    linarith
  have hlogm1 : (1:ℝ) < Real.log m := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    calc Real.exp 1 < 3 := Real.exp_one_lt_three
      _ ≤ m := hm3
  have hLpos : 0 < Real.log m := lt_trans one_pos hlogm1
  have hvpos : 0 < Real.log (Real.log m) := Real.log_pos hlogm1
  have hτpos : 0 < ((n.divisors.card : ℕ) : ℝ) := by
    have : 1 ≤ n.divisors.card :=
      Nat.one_le_iff_ne_zero.mpr (Finset.card_ne_zero_of_mem
        (by rw [Nat.mem_divisors]; exact ⟨one_dvd n, by omega⟩))
    exact_mod_cast this
  have hlogn : Real.log (n:ℝ) ≤ Real.log m := by
    apply Real.log_le_log (by positivity); rw [hm]; linarith
  suffices hlog : Real.log ((n.divisors.card : ℝ)) ≤ 1.5 * Real.log m / Real.log (Real.log m) by
    calc ((n.divisors.card:ℝ)) = Real.exp (Real.log ((n.divisors.card:ℝ))) := (Real.exp_log hτpos).symm
      _ ≤ Real.exp (1.5 * Real.log m / Real.log (Real.log m)) := Real.exp_le_exp.mpr hlog
  rcases lt_or_ge (Real.log (Real.log m)) 4 with hv | hv
  · have h1 := log_card_divisors_le n hn 3 (by norm_num : (0:ℝ) < 3)
    have h2 : Real.log (n:ℝ)/3 + SBtau 3 ≤ 1.5 * Real.log m / Real.log (Real.log m) := by
      have hg := g3_ge (Real.log (Real.log m)) hvpos hv
      rw [Real.exp_log hLpos] at hg
      have hb := SBtau_three_le
      have hkl : Real.log (n:ℝ)/3 ≤ Real.log m/3 := by linarith [hlogn]
      have he : Real.log m / 3 + Real.log m * (1.5 / Real.log (Real.log m) - 1 / 3)
          = 1.5 * Real.log m / Real.log (Real.log m) := by
        field_simp; ring
      linarith [hkl, hb, hg, he]
    linarith
  · set k : ℕ := Nat.floor (Real.log (Real.log m)) with hk
    have hk4 : 4 ≤ k := hk ▸ Nat.le_floor hv
    have hkge : ((k:ℕ):ℝ) ≤ Real.log (Real.log m) := Nat.floor_le (le_of_lt hvpos)
    have hklt : Real.log (Real.log m) < (k:ℝ)+1 := Nat.lt_floor_add_one _
    have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast (by omega : 0 < k)
    have h1 := log_card_divisors_le n hn (k:ℝ) hkpos
    have hSB := SB_int_le k hk4
    have hgn := gn_ge k hk4 (Real.log (Real.log m)) hkge hklt
    rw [Real.exp_log hLpos] at hgn
    have h2 : Real.log (n:ℝ)/(k:ℝ) + SBtau (k:ℝ) ≤ 1.5 * Real.log m / Real.log (Real.log m) := by
      have hkl : Real.log (n:ℝ)/(k:ℝ) ≤ Real.log m/(k:ℝ) := by
        apply div_le_div_of_nonneg_right _ (le_of_lt hkpos); linarith [hlogn]
      have he : Real.log m/(k:ℝ) + Real.log m*(1.5/Real.log (Real.log m) - 1/(k:ℝ))
          = 1.5 * Real.log m / Real.log (Real.log m) := by
        field_simp; ring
      linarith [hkl, hSB, hgn, he]
    linarith

end Work.FIArea3.JointCount
