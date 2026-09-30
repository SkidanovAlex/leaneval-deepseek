import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Auxiliary numeric bound: for `r ≥ 2`, `2^(2r+4) < 11^(r-1) * r^(4r-1)`. -/
lemma two_pow_lt_eleven_pow_mul_self {r : ℕ} (hr : 2 ≤ r) :
    (2:ℝ)^(2*r+4) < (11:ℝ)^(r-1) * (r:ℝ)^(4*r-1) := by
  have hr1 : 1 ≤ r := by omega
  have hr2 : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have h11pos : (0:ℝ) < (11:ℝ)^(r-1) := by positivity
  have hA : (2:ℝ)^(2*r+4) < 128 * (11:ℝ)^(r-1) := by
    have h2 : (2:ℝ)^(2*r+4) = 64 * (4:ℝ)^(r-1) := by
      rw [show 2*r+4 = 2*r + 4 from by omega, pow_add]
      rw [pow_mul, show (2:ℝ)^2 = 4 by norm_num]
      rw [show (4:ℝ)^r = (4:ℝ)^(r-1) * 4 from by
            rw [← pow_succ, Nat.sub_add_cancel hr1]]
      ring
    rw [h2]
    have h4 : (4:ℝ)^(r-1) ≤ (11:ℝ)^(r-1) :=
      pow_le_pow_left₀ (by norm_num) (by norm_num) (r-1)
    have hle : 64 * (4:ℝ)^(r-1) ≤ 64 * (11:ℝ)^(r-1) :=
      mul_le_mul_of_nonneg_left h4 (by norm_num)
    have hlt : 64 * (11:ℝ)^(r-1) < 128 * (11:ℝ)^(r-1) :=
      mul_lt_mul_of_pos_right (by norm_num) h11pos
    linarith
  have hB : 128 ≤ (r:ℝ)^(4*r-1) := by
    have h1 : (r:ℝ)^7 ≤ (r:ℝ)^(4*r-1) := by
      apply pow_le_pow_right₀ _ _
      · exact le_trans (by norm_num) hr2
      · omega
    have h2 : (2:ℝ)^7 ≤ (r:ℝ)^7 := pow_le_pow_left₀ (by norm_num) hr2 7
    norm_num at h2
    linarith
  calc (2:ℝ)^(2*r+4) < 128 * (11:ℝ)^(r-1) := hA
    _ ≤ (11:ℝ)^(r-1) * (r:ℝ)^(4*r-1) := by
        rw [mul_comm 128]
        exact mul_le_mul_of_nonneg_left hB (le_of_lt h11pos)

theorem split_E23_numE3 {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) :
    (2:ℝ)^(8*r+7) * (r:ℝ)^(2*r+1) * (d:ℝ) < (2:ℝ)^3 * (11:ℝ)^(r-1) * (2*(r:ℝ)*d)^(6*r) := by
  have key : (2:ℝ)^(2*r+4) < (11:ℝ)^(r-1) * (r:ℝ)^(4*r-1) :=
    two_pow_lt_eleven_pow_mul_self hr
  have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hd6 : (d:ℝ) ≤ (d:ℝ)^(6*r) := by
    have h : (d:ℝ)^1 ≤ (d:ℝ)^(6*r) := pow_le_pow_right₀ hd1 (by omega)
    simpa using h
  have hP : (0:ℝ) < (2:ℝ)^(6*r+3) * (r:ℝ)^(2*r+1) * (d:ℝ)^(6*r) := by positivity
  have step1 : (2:ℝ)^(2*r+4) * ((2:ℝ)^(6*r+3) * (r:ℝ)^(2*r+1) * (d:ℝ)^(6*r))
      < ((11:ℝ)^(r-1) * (r:ℝ)^(4*r-1)) * ((2:ℝ)^(6*r+3) * (r:ℝ)^(2*r+1) * (d:ℝ)^(6*r)) :=
    mul_lt_mul_of_pos_right key hP
  have eL : (2:ℝ)^(8*r+7) * (r:ℝ)^(2*r+1) * (d:ℝ)
      ≤ (2:ℝ)^(8*r+7) * (r:ℝ)^(2*r+1) * (d:ℝ)^(6*r) :=
    mul_le_mul_of_nonneg_left hd6 (by positivity)
  have eL' : (2:ℝ)^(8*r+7) * (r:ℝ)^(2*r+1) * (d:ℝ)^(6*r)
      = (2:ℝ)^(2*r+4) * ((2:ℝ)^(6*r+3) * (r:ℝ)^(2*r+1) * (d:ℝ)^(6*r)) := by
    rw [show 8*r+7 = (2*r+4) + (6*r+3) from by omega, pow_add]
    ring
  have eR' : ((11:ℝ)^(r-1) * (r:ℝ)^(4*r-1)) * ((2:ℝ)^(6*r+3) * (r:ℝ)^(2*r+1) * (d:ℝ)^(6*r))
      = (2:ℝ)^3 * (11:ℝ)^(r-1) * (2*(r:ℝ)*d)^(6*r) := by
    rw [mul_pow, mul_pow]
    rw [show (r:ℝ)^(6*r) = (r:ℝ)^(4*r-1) * (r:ℝ)^(2*r+1) from by
          rw [← pow_add]; congr 1; omega]
    rw [show (2:ℝ)^(6*r+3) = (2:ℝ)^3 * (2:ℝ)^(6*r) from by
          rw [← pow_add]; congr 1; omega]
    ring
  calc (2:ℝ)^(8*r+7) * (r:ℝ)^(2*r+1) * (d:ℝ)
      ≤ (2:ℝ)^(8*r+7) * (r:ℝ)^(2*r+1) * (d:ℝ)^(6*r) := eL
    _ = (2:ℝ)^(2*r+4) * ((2:ℝ)^(6*r+3) * (r:ℝ)^(2*r+1) * (d:ℝ)^(6*r)) := eL'
    _ < ((11:ℝ)^(r-1) * (r:ℝ)^(4*r-1)) * ((2:ℝ)^(6*r+3) * (r:ℝ)^(2*r+1) * (d:ℝ)^(6*r)) := step1
    _ = (2:ℝ)^3 * (11:ℝ)^(r-1) * (2*(r:ℝ)*d)^(6*r) := eR'

end Work.BW
