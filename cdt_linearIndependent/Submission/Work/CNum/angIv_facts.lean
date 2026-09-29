import Mathlib
import Submission.Work.CNum.Fx

/-!
# `Work.CNum.angIv_facts` — correctness of the angle interval `angIv`

`Submission/Work/CNum/Fx.lean` defines

`angIv m = [⌊m·piLo/1024⌋, ⌈m·piHi/1024⌉]`,

where `piLo = 3373259426` and `piHi = piLo + 1` are the mantissas of `π` at scale `SC = 2^30`
(`piLo < π·SC < piHi`).  Here we prove the two facts needed downstream:

* `angIv m` really encloses the angle `m·π/1024` (for *every* `m`, no bound on `m`);
* for `m ≤ 255` the interval lies inside `[0, π/4]`, so that the Taylor remainder bounds for
  `cos`/`sin` are applied on a subinterval of `[0, π/4]`.

The only analytic inputs are `Real.pi_gt_d20` and `Real.pi_lt_d20`; everything else is integer
arithmetic carried out by `omega`/`norm_num`.
-/

namespace Work.CNum

open Work.ANum

/-! ## 1. The two `π` bounds behind `piLo` / `piHi` -/

/-- `piLo = 3373259426 ≤ π·2^30`. -/
lemma piLo_le_piSC : (piLo : ℝ) ≤ Real.pi * SC := by
  have hSC : (SC : ℝ) = 1073741824 := by norm_num [SC]
  have h := Real.pi_gt_d20
  rw [hSC]
  show (3373259426 : ℝ) ≤ Real.pi * 1073741824
  linarith

/-- `π·2^30 ≤ piHi = 3373259427`. -/
lemma piSC_le_piHi : Real.pi * SC ≤ (piHi : ℝ) := by
  have hSC : (SC : ℝ) = 1073741824 := by norm_num [SC]
  have h := Real.pi_lt_d20
  rw [hSC]
  show Real.pi * 1073741824 ≤ (3373259427 : ℝ)
  linarith

/-! ## 2. The four endpoint estimates -/

/-- The lower endpoint of `angIv m` is a lower bound for `m·π/1024`. -/
lemma angIv_lo_le (m : ℕ) : m2r (angIv m).lo ≤ (m : ℝ) * Real.pi / 1024 := by
  show m2r (Int.ediv (m * piLo) 1024) ≤ (m : ℝ) * Real.pi / 1024
  have h1 : Int.ediv (m * piLo) 1024 * 1024 ≤ m * piLo :=
    Int.ediv_mul_le _ (by norm_num)
  have h1r : ((Int.ediv (m * piLo) 1024 : ℤ) : ℝ) * 1024 ≤ (m : ℝ) * (piLo : ℝ) := by
    exact_mod_cast h1
  have h2 : (m : ℝ) * (piLo : ℝ) ≤ (m : ℝ) * (Real.pi * SC) :=
    mul_le_mul_of_nonneg_left piLo_le_piSC (Nat.cast_nonneg m)
  have key : ((Int.ediv (m * piLo) 1024 : ℤ) : ℝ) * 1024 ≤ (m : ℝ) * Real.pi * SC := by
    linarith
  simp only [m2r]
  rw [div_le_iff₀ SC_posR]
  rw [show (m : ℝ) * Real.pi / 1024 * SC = (m : ℝ) * Real.pi * SC / 1024 by ring]
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 1024)]
  exact key

/-- The upper endpoint of `angIv m` is an upper bound for `m·π/1024`. -/
lemma angIv_hi_ge (m : ℕ) : (m : ℝ) * Real.pi / 1024 ≤ m2r (angIv m).hi := by
  show (m : ℝ) * Real.pi / 1024 ≤ m2r (-Int.ediv (-(m * piHi)) 1024)
  have h1 : m * piHi ≤ (-Int.ediv (-(m * piHi)) 1024) * 1024 := by
    have h : Int.ediv (-(m * piHi)) 1024 * 1024 ≤ -(m * piHi) :=
      Int.ediv_mul_le _ (by norm_num)
    omega
  have h1r : (m : ℝ) * (piHi : ℝ) ≤ ((-Int.ediv (-(m * piHi)) 1024 : ℤ) : ℝ) * 1024 := by
    exact_mod_cast h1
  have h2 : (m : ℝ) * (Real.pi * SC) ≤ (m : ℝ) * (piHi : ℝ) :=
    mul_le_mul_of_nonneg_left piSC_le_piHi (Nat.cast_nonneg m)
  have key : (m : ℝ) * Real.pi * SC ≤ ((-Int.ediv (-(m * piHi)) 1024 : ℤ) : ℝ) * 1024 := by
    linarith
  simp only [m2r]
  rw [le_div_iff₀ SC_posR]
  rw [show (m : ℝ) * Real.pi / 1024 * SC = (m : ℝ) * Real.pi * SC / 1024 by ring]
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 1024)]
  exact key

/-- The lower endpoint of `angIv m` is nonnegative. -/
lemma angIv_lo_nonneg (m : ℕ) : 0 ≤ m2r (angIv m).lo := by
  show (0 : ℝ) ≤ m2r (Int.ediv (m * piLo) 1024)
  have hlo : (0 : ℤ) ≤ Int.ediv (m * piLo) 1024 :=
    Int.ediv_nonneg (mul_nonneg (Int.natCast_nonneg m) (by norm_num [piLo])) (by norm_num)
  rw [← m2r_zero]
  exact m2r_le hlo

/-- For `m ≤ 255` the upper endpoint of `angIv m` is at most `π/4`. -/
lemma angIv_hi_le_pi_div_four (m : ℕ) (hm : m ≤ 255) :
    m2r (angIv m).hi ≤ Real.pi / 4 := by
  show m2r (-Int.ediv (-(m * piHi)) 1024) ≤ Real.pi / 4
  have h1 : (-Int.ediv (-(m * piHi)) 1024) * 1024 ≤ m * piHi + 1023 := by
    have h : -(m * piHi) < (Int.ediv (-(m * piHi)) 1024 + 1) * 1024 :=
      Int.lt_ediv_add_one_mul_self _ (by norm_num)
    omega
  have h1r : ((-Int.ediv (-(m * piHi)) 1024 : ℤ) : ℝ) * 1024 ≤ (m : ℝ) * (piHi : ℝ) + 1023 := by
    exact_mod_cast h1
  have hmR : (m : ℝ) ≤ 255 := by exact_mod_cast hm
  have hA : (m : ℝ) * (piHi : ℝ) + 1023 ≤ 255 * (piHi : ℝ) + 1023 := by
    nlinarith [show (0 : ℝ) < (piHi : ℝ) by norm_num [piHi]]
  have hB : (255 : ℝ) * (piHi : ℝ) + 1023 ≤ 256 * (piLo : ℝ) := by
    norm_num [piHi, piLo]
  have hC : (256 : ℝ) * (piLo : ℝ) ≤ 256 * ((SC : ℝ) * Real.pi) := by
    have h := piLo_le_piSC
    linarith
  have key : ((-Int.ediv (-(m * piHi)) 1024 : ℤ) : ℝ) * 1024 ≤ 256 * (SC : ℝ) * Real.pi := by
    linarith
  simp only [m2r]
  rw [div_le_iff₀ SC_posR]
  rw [show Real.pi / 4 * SC = 256 * (SC : ℝ) * Real.pi / 1024 by ring]
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 1024)]
  exact key

/-! ## 3. The statement -/

theorem angIv_facts :
    (∀ m : ℕ, (angIv m).Mem ((m : ℝ) * Real.pi / 1024)) ∧
    (∀ m : ℕ, m ≤ 255 → 0 ≤ Work.ANum.m2r (angIv m).lo ∧ Work.ANum.m2r (angIv m).hi ≤ Real.pi / 4) := by
  exact ⟨fun m => ⟨angIv_lo_le m, angIv_hi_ge m⟩,
    fun m hm => ⟨angIv_lo_nonneg m, angIv_hi_le_pi_div_four m hm⟩⟩

end Work.CNum
