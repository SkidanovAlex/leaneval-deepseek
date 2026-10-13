import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.FTS.PhiStar.Psi0Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.PsiDivS2Sup

/-- The difference telescopes:
`(c + G₀/2)/(S²C³) - c/S² = (c(1 - C³) + G₀/2)/(S²C³)`. -/
private lemma PsiDivS2Sup_derivG_ident (c θ g : ℝ) (hS : Real.sin θ ≠ 0)
    (hC : Real.cos θ ≠ 0) :
    (c + g / 2) / (Real.sin θ ^ 2 * Real.cos θ ^ 3) - c / Real.sin θ ^ 2
      = (c * (1 - Real.cos θ ^ 3) + g / 2) / (Real.sin θ ^ 2 * Real.cos θ ^ 3) := by
  field_simp
  ring

theorem derivG_reg_bound {α c θ : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (1 / 2)) :
    |(c + Work.FTS.PhiStar.Gzero α θ / 2) / (Real.sin θ ^ 2 * Real.cos θ ^ 3)
      - c / Real.sin θ ^ 2| ≤ 24 * |c| + 7 * Real.pi ^ 2 := by
  obtain ⟨hθ0, hθh⟩ := hθ
  have hπ2 : θ ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hSpos : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [hθh, Real.pi_gt_three])
  have hCpos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [hθh, Real.pi_gt_three]⟩
  have hG := Work.FTS.PhiStar.Gzero_abs_le_sq α hα hα4 (le_of_lt hθ0) (by linarith)
  -- `cos θ ≥ 1/2` on `(0, 1/2)`
  have hChalf : (1 / 2 : ℝ) ≤ Real.cos θ := by
    have hθ3 : θ ≤ Real.pi / 3 := by linarith [Real.pi_gt_three]
    have h := Real.cos_le_cos_of_nonneg_of_le_pi (x := θ) (y := Real.pi / 3)
      (le_of_lt hθ0) (by linarith [Real.pi_pos]) hθ3
    rwa [Real.cos_pi_div_three] at h
  have hC3 : (1 / 8 : ℝ) ≤ Real.cos θ ^ 3 := by nlinarith [hChalf, sq_nonneg (Real.cos θ)]
  have hCle1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have hC3le1 : Real.cos θ ^ 3 ≤ 1 := pow_le_one₀ (le_of_lt hCpos) hCle1
  have hCm : 1 - Real.cos θ ^ 3 ≤ 3 * Real.sin θ ^ 2 := by
    have h1mC : 0 ≤ 1 - Real.cos θ := by linarith
    nlinarith [Real.sin_sq_add_cos_sq θ, h1mC, hCle1, hCpos]
  -- `sin θ ≥ 2θ/π` on `(0, 1/2)`
  have hS2 : (4 : ℝ) * θ ^ 2 / Real.pi ^ 2 ≤ Real.sin θ ^ 2 := by
    have h := Real.mul_le_sin (le_of_lt hθ0) hπ2
    have hpos : 0 ≤ 2 / Real.pi * θ := by positivity
    have h2 := pow_le_pow_left₀ hpos h 2
    have hval : (2 / Real.pi * θ) ^ 2 = 4 * θ ^ 2 / Real.pi ^ 2 := by field_simp; ring
    linarith [h2, hval.le, hval.symm.le]
  have hden : 0 < Real.sin θ ^ 2 * Real.cos θ ^ 3 :=
    mul_pos (pow_pos hSpos 2) (pow_pos hCpos 3)
  rw [PsiDivS2Sup_derivG_ident c θ (Work.FTS.PhiStar.Gzero α θ) (ne_of_gt hSpos) (ne_of_gt hCpos),
    abs_div, abs_of_pos hden, div_le_iff₀ hden]
  have hnum : |c * (1 - Real.cos θ ^ 3) + Work.FTS.PhiStar.Gzero α θ / 2|
      ≤ |c| * (3 * Real.sin θ ^ 2) + 7 * θ ^ 2 / 2 := by
    have h1 : |c * (1 - Real.cos θ ^ 3)| ≤ |c| * (3 * Real.sin θ ^ 2) := by
      rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - Real.cos θ ^ 3)]
      exact mul_le_mul_of_nonneg_left hCm (abs_nonneg c)
    have h2 : |Work.FTS.PhiStar.Gzero α θ / 2| ≤ 7 * θ ^ 2 / 2 := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith
    calc |c * (1 - Real.cos θ ^ 3) + Work.FTS.PhiStar.Gzero α θ / 2|
        ≤ |c * (1 - Real.cos θ ^ 3)| + |Work.FTS.PhiStar.Gzero α θ / 2| := abs_add_le _ _
      _ ≤ |c| * (3 * Real.sin θ ^ 2) + 7 * θ ^ 2 / 2 := by linarith
  have hrhs : |c| * (3 * Real.sin θ ^ 2) + 7 * θ ^ 2 / 2
      ≤ (24 * |c| + 7 * Real.pi ^ 2) * (Real.sin θ ^ 2 * Real.cos θ ^ 3) := by
    have hS2nn : (0 : ℝ) ≤ Real.sin θ ^ 2 := sq_nonneg _
    have h1 : |c| * (3 * Real.sin θ ^ 2) ≤ |c| * 24 * (Real.sin θ ^ 2 * Real.cos θ ^ 3) := by
      have h3 : 3 * Real.sin θ ^ 2 ≤ 24 * (Real.sin θ ^ 2 * Real.cos θ ^ 3) := by
        nlinarith [hC3, hS2nn]
      have h4 := mul_le_mul_of_nonneg_left h3 (abs_nonneg c)
      linarith [h4]
    have h2 : 7 * θ ^ 2 / 2 ≤ 7 * Real.pi ^ 2 * (Real.sin θ ^ 2 * Real.cos θ ^ 3) := by
      have hπ2pos : (0 : ℝ) < Real.pi ^ 2 := by positivity
      have hmul : 4 * θ ^ 2 / Real.pi ^ 2 * (1 / 8) ≤ Real.sin θ ^ 2 * Real.cos θ ^ 3 :=
        mul_le_mul hS2 hC3 (by norm_num) hS2nn
      have hv : 4 * θ ^ 2 / Real.pi ^ 2 * (1 / 8) = θ ^ 2 / (2 * Real.pi ^ 2) := by
        field_simp; ring
      rw [hv, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi ^ 2)] at hmul
      nlinarith [hmul, hπ2pos]
    nlinarith [h1, h2]
  linarith

end Work.FTS.PhiStar.PsiDivS2Sup
