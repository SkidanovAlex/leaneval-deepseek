import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.RegPkgGal.Der.Lib

theorem holder_of_lipschitz_of_bounded {f : ℝ → ℝ} {C M α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hlip : ∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' → |f z - f z'| ≤ C * |z - z'|)
    (hbdd : ∀ z : ℝ, 0 ≤ z → |f z| ≤ M) :
    ∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' → |f z - f z'| ≤ max C (2 * M) * |z - z'| ^ α := by
  intro z z' hz hz'
  have hd0 : 0 ≤ |z - z'| := abs_nonneg _
  have hmax0 : 0 ≤ max C (2 * M) := le_trans hC (le_max_left _ _)
  have habs : |f z - f z'| ≤ |f z| + |f z'| := by
    simpa using abs_sub_le (f z) 0 (f z')
  -- the trivial bound: either Lipschitz or bounded
  have hmin : |f z - f z'| ≤ min (C * |z - z'|) (2 * M) := by
    refine le_min (hlip z z' hz hz') ?_
    calc |f z - f z'| ≤ |f z| + |f z'| := habs
      _ ≤ M + M := add_le_add (hbdd z hz) (hbdd z' hz')
      _ = 2 * M := by ring
  rcases le_or_gt |z - z'| 1 with hd1 | hd1
  · -- small distances: |z - z'| ≤ |z - z'| ^ α, so the Lipschitz bound wins
    have hle : |z - z'| ≤ |z - z'| ^ α := by
      rcases eq_or_lt_of_le hd0 with h0 | h0
      · simp [h0.symm, Real.zero_rpow (ne_of_gt hα)]
      · have h1 : |z - z'| ^ (1:ℝ) ≤ |z - z'| ^ α :=
          Real.rpow_le_rpow_of_exponent_ge h0 hd1 hα1
        rwa [Real.rpow_one] at h1
    calc |f z - f z'| ≤ C * |z - z'| := le_trans hmin (min_le_left _ _)
      _ ≤ max C (2 * M) * |z - z'| := mul_le_mul_of_nonneg_right (le_max_left _ _) hd0
      _ ≤ max C (2 * M) * |z - z'| ^ α := mul_le_mul_of_nonneg_left hle hmax0
  · -- large distances: |z - z'| ^ α ≥ 1, so the boundedness bound wins
    have hle : (1:ℝ) ≤ |z - z'| ^ α := Real.one_le_rpow (le_of_lt hd1) (le_of_lt hα)
    calc |f z - f z'| ≤ 2 * M := le_trans hmin (min_le_right _ _)
      _ ≤ max C (2 * M) := le_max_right _ _
      _ ≤ max C (2 * M) * |z - z'| ^ α := le_mul_of_one_le_right hmax0 hle

end Work.FTS.RegPkgGal.Der.Lib
