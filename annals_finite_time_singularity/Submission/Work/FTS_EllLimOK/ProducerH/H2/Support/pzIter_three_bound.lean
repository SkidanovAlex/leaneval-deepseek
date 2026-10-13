import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.OpenPkg.ScoefOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ProducerH.H2.Support

/-- **The Stirling expansion of `D_z = z ∂_z` in the small case `n = 3`.**

`D_z^3 Ψ = z ∂_zΨ + 3 z² ∂_z²Ψ + z³ ∂_z³Ψ` on the open quadrant; the small
numerical form of `Work.FTS.OpenPkg.DzIter_eq_sum_scoef_open`. -/
private theorem DzIter_three_eq {Ψ : ℝ → ℝ → ℝ} {θ z : ℝ}
    (hslice : ContDiffOn ℝ Work.Stability.smoothOrder (fun z' => Ψ z' θ) (Set.Ioi 0))
    (hz : 0 < z) :
    Work.Spaces.DzIter 3 Ψ z θ
      = z * Work.Spaces.pzIter 1 Ψ z θ + 3 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        + z ^ 3 * Work.Spaces.pzIter 3 Ψ z θ := by
  rw [Work.FTS.OpenPkg.DzIter_eq_sum_scoef_open hslice 3 z hz]
  norm_num [Finset.sum_range_succ, Work.Spaces.scoef]

theorem pzIter_three_bound
    {Ψ : ℝ → ℝ → ℝ} {a b z θ M1 M2 M3 : ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ) (ha : 0 < a) (hzb : z ∈ Set.Icc a b)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (h1 : |Work.Spaces.mixed 3 0 Ψ z θ| ≤ M1)
    (h2 : |Work.Spaces.pz Ψ z θ| ≤ M2)
    (h3 : |Work.Spaces.pz (Work.Spaces.pz Ψ) z θ| ≤ M3) :
    |Work.Spaces.pzIter 3 Ψ z θ| ≤ (M1 + b * M2 + 3 * b ^ 2 * M3) / a ^ 3 := by
  have haz : a ≤ z := hzb.1
  have hbz : z ≤ b := hzb.2
  have hz0 : 0 < z := lt_of_lt_of_le ha haz
  have hz2 : 0 ≤ z ^ 2 := sq_nonneg z
  have hz3 : 0 ≤ z ^ 3 := pow_nonneg hz0.le 3
  -- the three input bounds, in the `pzIter`-spelling
  have h1' : |Work.Spaces.DzIter 3 Ψ z θ| ≤ M1 := by simpa using h1
  have h2' : |Work.Spaces.pzIter 1 Ψ z θ| ≤ M2 := by simpa using h2
  have h3' : |Work.Spaces.pzIter 2 Ψ z θ| ≤ M3 := by simpa using h3
  have hM2 : 0 ≤ M2 := le_trans (abs_nonneg _) h2'
  have hM3 : 0 ≤ M3 := le_trans (abs_nonneg _) h3'
  have hsum := DzIter_three_eq (hsm.curry_z hθ) hz0
  -- the elementary absolute-value bounds of the three terms
  have hb1 : |z * Work.Spaces.pzIter 1 Ψ z θ| ≤ z * M2 := by
    rw [abs_mul, abs_of_pos hz0]
    exact mul_le_mul_of_nonneg_left h2' hz0.le
  have hb2 : |3 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)| ≤ 3 * (z ^ 2 * M3) := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3), abs_mul, abs_of_nonneg hz2]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3' hz2) (by norm_num)
  -- solve for `z³ ∂_z³Ψ` and bound it
  have hkey : z ^ 3 * |Work.Spaces.pzIter 3 Ψ z θ| ≤ M1 + b * M2 + 3 * b ^ 2 * M3 := by
    have hxz : z ^ 3 * |Work.Spaces.pzIter 3 Ψ z θ| = |z ^ 3 * Work.Spaces.pzIter 3 Ψ z θ| := by
      rw [abs_mul, abs_of_nonneg hz3]
    rw [hxz]
    have hinner : |z ^ 3 * Work.Spaces.pzIter 3 Ψ z θ| ≤ M1 + z * M2 + 3 * (z ^ 2 * M3) := by
      have hrew : z ^ 3 * Work.Spaces.pzIter 3 Ψ z θ
          = Work.Spaces.DzIter 3 Ψ z θ - z * Work.Spaces.pzIter 1 Ψ z θ
            - 3 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) := by
        rw [hsum]; ring
      rw [hrew, abs_le]
      obtain ⟨hA1, hA2⟩ := abs_le.mp h1'
      obtain ⟨hB1, hB2⟩ := abs_le.mp hb1
      obtain ⟨hC1, hC2⟩ := abs_le.mp hb2
      constructor <;> linarith
    have hzM2 : z * M2 ≤ b * M2 := mul_le_mul_of_nonneg_right hbz hM2
    have hz2M3 : z ^ 2 * M3 ≤ b ^ 2 * M3 :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hz0.le hbz 2) hM3
    linarith
  rw [le_div_iff₀ (pow_pos ha 3)]
  have hlow : |Work.Spaces.pzIter 3 Ψ z θ| * a ^ 3 ≤ |Work.Spaces.pzIter 3 Ψ z θ| * z ^ 3 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha.le haz 3) (abs_nonneg _)
  have hcomm : |Work.Spaces.pzIter 3 Ψ z θ| * z ^ 3 = z ^ 3 * |Work.Spaces.pzIter 3 Ψ z θ| := by
    ring
  linarith

end Work.FTS_EllLimOK.ProducerH.H2.Support
