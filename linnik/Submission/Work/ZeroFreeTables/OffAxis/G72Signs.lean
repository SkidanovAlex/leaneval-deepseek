import Submission.Work.ZeroFreeTables.OffAxis.G72Base

noncomputable section

namespace Work.ZeroFreeTables.OffAxis

open Work.ZeroFreeTables
open scoped BigOperators


/-! ## Signs of `cos (2 σ₀)`, `sin (2 σ₀)` at the seven grid columns

All seven `2 σ₀` lie in `(3π/2, 5π/2)`, so all the cosines are positive; the first four are
below `2π` (negative sine) and the last three above it (positive sine). -/

lemma cos_pos_21_8 : 0 < Real.cos (2*((21:ℝ)/8)) := by
  have hx : (2*((21:ℝ)/8) - 2*Real.pi) + 2*Real.pi = (2*((21:ℝ)/8)) := by ring
  have h := Real.cos_add_two_pi (2*((21:ℝ)/8) - 2*Real.pi)
  rw [hx] at h
  rw [h]
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith [Real.pi_gt_d2, Real.pi_lt_d2]

lemma sin_neg_21_8 : Real.sin (2*((21:ℝ)/8)) < 0 := by
  have hx : (2*((21:ℝ)/8) - 2*Real.pi) + 2*Real.pi = (2*((21:ℝ)/8)) := by ring
  have h := Real.sin_add_two_pi (2*((21:ℝ)/8) - 2*Real.pi)
  rw [hx] at h
  rw [h]
  apply Real.sin_neg_of_neg_of_neg_pi_lt
  · linarith [Real.pi_gt_d2]
  · linarith [Real.pi_lt_d2]

lemma cos_pos_111_40 : 0 < Real.cos (2*((111:ℝ)/40)) := by
  have hx : (2*((111:ℝ)/40) - 2*Real.pi) + 2*Real.pi = (2*((111:ℝ)/40)) := by ring
  have h := Real.cos_add_two_pi (2*((111:ℝ)/40) - 2*Real.pi)
  rw [hx] at h
  rw [h]
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith [Real.pi_gt_d2, Real.pi_lt_d2]

lemma sin_neg_111_40 : Real.sin (2*((111:ℝ)/40)) < 0 := by
  have hx : (2*((111:ℝ)/40) - 2*Real.pi) + 2*Real.pi = (2*((111:ℝ)/40)) := by ring
  have h := Real.sin_add_two_pi (2*((111:ℝ)/40) - 2*Real.pi)
  rw [hx] at h
  rw [h]
  apply Real.sin_neg_of_neg_of_neg_pi_lt
  · linarith [Real.pi_gt_d2]
  · linarith [Real.pi_lt_d2]

lemma cos_pos_117_40 : 0 < Real.cos (2*((117:ℝ)/40)) := by
  have hx : (2*((117:ℝ)/40) - 2*Real.pi) + 2*Real.pi = (2*((117:ℝ)/40)) := by ring
  have h := Real.cos_add_two_pi (2*((117:ℝ)/40) - 2*Real.pi)
  rw [hx] at h
  rw [h]
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith [Real.pi_gt_d2, Real.pi_lt_d2]

lemma sin_neg_117_40 : Real.sin (2*((117:ℝ)/40)) < 0 := by
  have hx : (2*((117:ℝ)/40) - 2*Real.pi) + 2*Real.pi = (2*((117:ℝ)/40)) := by ring
  have h := Real.sin_add_two_pi (2*((117:ℝ)/40) - 2*Real.pi)
  rw [hx] at h
  rw [h]
  apply Real.sin_neg_of_neg_of_neg_pi_lt
  · linarith [Real.pi_gt_d2]
  · linarith [Real.pi_lt_d2]

lemma cos_pos_123_40 : 0 < Real.cos (2*((123:ℝ)/40)) := by
  have hx : (2*((123:ℝ)/40) - 2*Real.pi) + 2*Real.pi = (2*((123:ℝ)/40)) := by ring
  have h := Real.cos_add_two_pi (2*((123:ℝ)/40) - 2*Real.pi)
  rw [hx] at h
  rw [h]
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith [Real.pi_gt_d2, Real.pi_lt_d2]

lemma sin_neg_123_40 : Real.sin (2*((123:ℝ)/40)) < 0 := by
  have hx : (2*((123:ℝ)/40) - 2*Real.pi) + 2*Real.pi = (2*((123:ℝ)/40)) := by ring
  have h := Real.sin_add_two_pi (2*((123:ℝ)/40) - 2*Real.pi)
  rw [hx] at h
  rw [h]
  apply Real.sin_neg_of_neg_of_neg_pi_lt
  · linarith [Real.pi_gt_d2]
  · linarith [Real.pi_lt_d2]

lemma cos_pos_129_40 : 0 < Real.cos (2*((129:ℝ)/40)) := by
  have hx : (2*((129:ℝ)/40) - 2*Real.pi) + 2*Real.pi = (2*((129:ℝ)/40)) := by ring
  have h := Real.cos_add_two_pi (2*((129:ℝ)/40) - 2*Real.pi)
  rw [hx] at h
  rw [h]
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith [Real.pi_gt_d2, Real.pi_lt_d2]

lemma sin_pos_129_40 : 0 < Real.sin (2*((129:ℝ)/40)) := by
  have hx : (2*((129:ℝ)/40) - 2*Real.pi) + 2*Real.pi = (2*((129:ℝ)/40)) := by ring
  have h := Real.sin_add_two_pi (2*((129:ℝ)/40) - 2*Real.pi)
  rw [hx] at h
  rw [h]
  apply Real.sin_pos_of_pos_of_lt_pi
  · linarith [Real.pi_lt_d2]
  · linarith [Real.pi_gt_d2]

lemma cos_pos_27_8 : 0 < Real.cos (2*((27:ℝ)/8)) := by
  have hx : (2*((27:ℝ)/8) - 2*Real.pi) + 2*Real.pi = (2*((27:ℝ)/8)) := by ring
  have h := Real.cos_add_two_pi (2*((27:ℝ)/8) - 2*Real.pi)
  rw [hx] at h
  rw [h]
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith [Real.pi_gt_d2, Real.pi_lt_d2]

lemma sin_pos_27_8 : 0 < Real.sin (2*((27:ℝ)/8)) := by
  have hx : (2*((27:ℝ)/8) - 2*Real.pi) + 2*Real.pi = (2*((27:ℝ)/8)) := by ring
  have h := Real.sin_add_two_pi (2*((27:ℝ)/8) - 2*Real.pi)
  rw [hx] at h
  rw [h]
  apply Real.sin_pos_of_pos_of_lt_pi
  · linarith [Real.pi_lt_d2]
  · linarith [Real.pi_gt_d2]

lemma cos_pos_141_40 : 0 < Real.cos (2*((141:ℝ)/40)) := by
  have hx : (2*((141:ℝ)/40) - 2*Real.pi) + 2*Real.pi = (2*((141:ℝ)/40)) := by ring
  have h := Real.cos_add_two_pi (2*((141:ℝ)/40) - 2*Real.pi)
  rw [hx] at h
  rw [h]
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith [Real.pi_gt_d2, Real.pi_lt_d2]

lemma sin_pos_141_40 : 0 < Real.sin (2*((141:ℝ)/40)) := by
  have hx : (2*((141:ℝ)/40) - 2*Real.pi) + 2*Real.pi = (2*((141:ℝ)/40)) := by ring
  have h := Real.sin_add_two_pi (2*((141:ℝ)/40) - 2*Real.pi)
  rw [hx] at h
  rw [h]
  apply Real.sin_pos_of_pos_of_lt_pi
  · linarith [Real.pi_lt_d2]
  · linarith [Real.pi_gt_d2]

lemma cos_half_141_40 : (1:ℝ)/2 ≤ Real.cos (2*((141:ℝ)/40)) := by
  have hx : (2*((141:ℝ)/40) - 2*Real.pi) + 2*Real.pi = 2*((141:ℝ)/40) := by ring
  have h := Real.cos_add_two_pi (2*((141:ℝ)/40) - 2*Real.pi)
  rw [hx] at h
  rw [h]
  have hle : (2*((141:ℝ)/40) - 2*Real.pi) ≤ Real.pi/3 := by linarith [Real.pi_gt_d2]
  have h0 : 0 ≤ (2*((141:ℝ)/40) - 2*Real.pi) := by linarith [Real.pi_lt_d2]
  calc (1:ℝ)/2 = Real.cos (Real.pi/3) := by rw [Real.cos_pi_div_three]
    _ ≤ Real.cos ((2*((141:ℝ)/40) - 2*Real.pi)) := Real.cos_le_cos_of_nonneg_of_le_pi h0 (by linarith [Real.pi_gt_three]) hle

lemma sin_half_141_40 : (1:ℝ)/2 ≤ Real.sin (2*((141:ℝ)/40)) := by
  have hx : (2*((141:ℝ)/40) - 2*Real.pi) + 2*Real.pi = 2*((141:ℝ)/40) := by ring
  have h := Real.sin_add_two_pi (2*((141:ℝ)/40) - 2*Real.pi)
  rw [hx] at h
  rw [h]
  have hge : Real.pi/6 ≤ (2*((141:ℝ)/40) - 2*Real.pi) := by linarith [Real.pi_lt_d2]
  have hmem1 : Real.pi/6 ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) := by
    constructor <;> linarith [Real.pi_gt_three]
  have hmem2 : (2*((141:ℝ)/40) - 2*Real.pi) ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) := by
    constructor <;> linarith [Real.pi_gt_d2, Real.pi_lt_d2]
  have hmono := Real.strictMonoOn_sin.monotoneOn hmem1 hmem2 hge
  calc (1:ℝ)/2 = Real.sin (Real.pi/6) := by rw [Real.sin_pi_div_six]
    _ ≤ Real.sin ((2*((141:ℝ)/40) - 2*Real.pi)) := hmono

end Work.ZeroFreeTables.OffAxis
end
