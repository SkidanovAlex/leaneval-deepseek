import Mathlib
import Submission.Work.CNum.Basic
import Submission.Work.CNum.C2_setup
import Submission.Work.CNum.AlpBound

namespace Work.CNum.DAux

/-- `x ≤ arcsin x` for `0 ≤ x ≤ 1`. -/
private lemma self_le_arcsin {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : x ≤ Real.arcsin x := by
  have hmem : x ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_gt_d4]⟩
  have hmem2 : x ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith, hx1⟩
  exact (Real.le_arcsin_iff_sin_le hmem hmem2).mpr (Real.sin_le hx0)

/-- The cusp angle is bounded by `π/2 - γ`, since `arcsin γ ≥ γ`. -/
private lemma alpR_le_pi_div_two_sub_gamR : Work.CNum.alpR ≤ Real.pi / 2 - Work.CNum.gamR := by
  have hgam : Work.CNum.gamR = 27559 / 395641 := Work.CNum.gamR_eq_rat
  have h0 : 0 < Work.CNum.gamR := by rw [hgam]; norm_num
  have h1 : Work.CNum.gamR ≤ 1 := by rw [hgam]; norm_num
  have harc : Work.CNum.gamR ≤ Real.arcsin Work.CNum.gamR := self_le_arcsin h0.le h1
  rw [Work.CNum.alpR, Real.arccos_eq_pi_div_two_sub_arcsin]
  linarith

/-- `11π/512 + 1/500 ≤ γ`. -/
private lemma key_rat : 11 * Real.pi / 512 + 1 / 500 ≤ Work.CNum.gamR := by
  have hnum : (11 * 3.1416 / 512 + 1 / 500 : ℝ) ≤ 27559 / 395641 := by norm_num
  have h := Real.pi_lt_d4
  rw [Work.CNum.gamR_eq_rat]
  linarith

theorem DeltaBound : (1 : ℝ) / 1000 ≤ 245 * Real.pi / 1024 - Work.CNum.alpR / 2 := by
  have h1 := alpR_le_pi_div_two_sub_gamR
  have h2 := key_rat
  linarith

end Work.CNum.DAux
