import Mathlib
import Submission.Work.A3.majorArcKernel

namespace Work.A3

/-- Two lower bounds for `mArcKernel N d β = (|β| + N^{-d})^{-1/d}`: in the regime `|β| ≥ N^{-d}` it dominates `2^{-1/d}|β|^{-1/d}`, and in the regime `|β| ≤ N^{-d}` (which includes `β = 0`) it dominates `2^{-1/d} N`.  Together they say that `mArcKernel N d β ≥ 2^{-1/d} min(N, |β|^{-1/d})`.  Proof: `Real.rpow_le_rpow_of_nonpos` with `|β| + N^{-d} ≤ 2|β|` resp. `|β| + N^{-d} ≤ 2N^{-d}`. -/
lemma mArcKernel_lower (N d : ℕ) (hN : 1 ≤ N) (hd : 1 ≤ d) (β : ℝ) :
    ((N:ℝ)^(-(d:ℝ)) ≤ |β| → 2^(-(1:ℝ)/(d:ℝ)) * |β|^(-(1:ℝ)/(d:ℝ)) ≤ Work.A3.mArcKernel N d β)
    ∧ (|β| ≤ (N:ℝ)^(-(d:ℝ)) → 2^(-(1:ℝ)/(d:ℝ)) * (N:ℝ) ≤ Work.A3.mArcKernel N d β) := by
  have hN0 : (0:ℝ) < (N:ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hN
  have hd0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
  have hz : (-(1:ℝ)/(d:ℝ)) ≤ 0 := by
    rw [neg_div]
    exact neg_nonpos.mpr (div_nonneg zero_le_one hd0.le)
  have hNp : (0:ℝ) < (N:ℝ)^(-(d:ℝ)) := Real.rpow_pos_of_pos hN0 _
  constructor
  · intro hβ
    -- `|β| + N^{-d} ≤ 2|β|` in this regime, so `(2|β|)^{-1/d} ≤ (|β| + N^{-d})^{-1/d}`.
    have hxpos : 0 < |β| + (N:ℝ)^(-(d:ℝ)) := by linarith
    have hxy : |β| + (N:ℝ)^(-(d:ℝ)) ≤ 2 * |β| := by linarith
    have h1 : (2 * |β|) ^ (-(1:ℝ)/(d:ℝ)) ≤ (|β| + (N:ℝ)^(-(d:ℝ))) ^ (-(1:ℝ)/(d:ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hxpos hxy hz
    rw [Real.mul_rpow (show (0:ℝ) ≤ 2 by norm_num) (abs_nonneg β)] at h1
    rw [Work.A3.mArcKernel]
    exact h1
  · intro hβ
    -- `|β| + N^{-d} ≤ 2 N^{-d}` in this regime, so `(2 N^{-d})^{-1/d} ≤ (|β| + N^{-d})^{-1/d}`,
    -- and `(2 N^{-d})^{-1/d} = 2^{-1/d} N`.
    have hxpos : 0 < |β| + (N:ℝ)^(-(d:ℝ)) := by linarith [abs_nonneg β, hNp]
    have hxy : |β| + (N:ℝ)^(-(d:ℝ)) ≤ 2 * (N:ℝ)^(-(d:ℝ)) := by linarith
    have h1 : (2 * (N:ℝ)^(-(d:ℝ))) ^ (-(1:ℝ)/(d:ℝ))
        ≤ (|β| + (N:ℝ)^(-(d:ℝ))) ^ (-(1:ℝ)/(d:ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hxpos hxy hz
    have hNpow : ((N:ℝ)^(-(d:ℝ)))^(-(1:ℝ)/(d:ℝ)) = (N:ℝ) := by
      rw [← Real.rpow_mul (le_of_lt hN0)]
      have hkey : (-(d:ℝ)) * (-(1:ℝ)/(d:ℝ)) = 1 := by rw [neg_div]; field_simp
      rw [hkey, Real.rpow_one]
    calc 2^(-(1:ℝ)/(d:ℝ)) * (N:ℝ)
        = 2^(-(1:ℝ)/(d:ℝ)) * ((N:ℝ)^(-(d:ℝ)))^(-(1:ℝ)/(d:ℝ)) := by rw [hNpow]
      _ = (2 * (N:ℝ)^(-(d:ℝ))) ^ (-(1:ℝ)/(d:ℝ)) := by
            rw [Real.mul_rpow (show (0:ℝ) ≤ 2 by norm_num) (le_of_lt hNp)]
      _ ≤ (|β| + (N:ℝ)^(-(d:ℝ))) ^ (-(1:ℝ)/(d:ℝ)) := h1
      _ = Work.A3.mArcKernel N d β := by rw [Work.A3.mArcKernel]

end Work.A3
