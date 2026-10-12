import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Submission.Work.BoseFixB1B.cutoffDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1B

theorem plateau_lip {K A δ : ℝ} (hK : 0 ≤ K)
    (hσ : ∀ x y : ℝ, |Real.smoothTransition y - Real.smoothTransition x| ≤ K * |y - x|)
    (hδ : 0 < δ) :
    ∀ t u : ℝ, |plateau A δ u - plateau A δ t| ≤ (2 * K / δ) * |u - t| := by
  intro t u
  have hδle : 0 ≤ δ := hδ.le
  -- the arguments of `σ` differ by `(u - t)/δ`, resp. `-(u - t)/δ`
  have h1 : |(u + A) / δ - (t + A) / δ| = |u - t| / δ := by
    rw [div_sub_div_same, abs_div, abs_of_pos hδ]
    have : (u + A) - (t + A) = u - t := by ring
    rw [this]
  have h2 : |(A - u) / δ - (A - t) / δ| = |u - t| / δ := by
    rw [div_sub_div_same, abs_div, abs_of_pos hδ]
    have : (A - u) - (A - t) = -(u - t) := by ring
    rw [this, abs_neg]
  -- the two one-dimensional factors are `K/δ`-Lipschitz
  have hb : |Real.smoothTransition ((u + A) / δ) - Real.smoothTransition ((t + A) / δ)|
      ≤ K * (|u - t| / δ) := by
    simpa [h1] using hσ ((t + A) / δ) ((u + A) / δ)
  have hd : |Real.smoothTransition ((A - u) / δ) - Real.smoothTransition ((A - t) / δ)|
      ≤ K * (|u - t| / δ) := by
    simpa [h2] using hσ ((A - t) / δ) ((A - u) / δ)
  -- and both are `[0,1]`-valued
  have hbnd : ∀ z : ℝ, |Real.smoothTransition z| ≤ 1 := by
    intro z
    rw [abs_of_nonneg (Real.smoothTransition.nonneg z)]
    exact Real.smoothTransition.le_one z
  have hnn : 0 ≤ K * (|u - t| / δ) :=
    mul_nonneg hK (div_nonneg (abs_nonneg _) hδle)
  simp only [plateau]
  have key : Real.smoothTransition ((u + A) / δ) * Real.smoothTransition ((A - u) / δ)
      - Real.smoothTransition ((t + A) / δ) * Real.smoothTransition ((A - t) / δ)
      = Real.smoothTransition ((u + A) / δ)
          * (Real.smoothTransition ((A - u) / δ) - Real.smoothTransition ((A - t) / δ))
        + (Real.smoothTransition ((u + A) / δ) - Real.smoothTransition ((t + A) / δ))
          * Real.smoothTransition ((A - t) / δ) := by ring
  rw [key]
  calc |Real.smoothTransition ((u + A) / δ)
          * (Real.smoothTransition ((A - u) / δ) - Real.smoothTransition ((A - t) / δ))
        + (Real.smoothTransition ((u + A) / δ) - Real.smoothTransition ((t + A) / δ))
          * Real.smoothTransition ((A - t) / δ)|
      ≤ |Real.smoothTransition ((u + A) / δ)
            * (Real.smoothTransition ((A - u) / δ) - Real.smoothTransition ((A - t) / δ))|
        + |(Real.smoothTransition ((u + A) / δ) - Real.smoothTransition ((t + A) / δ))
            * Real.smoothTransition ((A - t) / δ)| := abs_add_le _ _
    _ = |Real.smoothTransition ((u + A) / δ)|
          * |Real.smoothTransition ((A - u) / δ) - Real.smoothTransition ((A - t) / δ)|
        + |Real.smoothTransition ((u + A) / δ) - Real.smoothTransition ((t + A) / δ)|
          * |Real.smoothTransition ((A - t) / δ)| := by rw [abs_mul, abs_mul]
    _ ≤ 1 * (K * (|u - t| / δ)) + (K * (|u - t| / δ)) * 1 := by
        apply add_le_add
        · exact mul_le_mul (hbnd _) hd (abs_nonneg _) (by norm_num)
        · exact mul_le_mul hb (hbnd _) (abs_nonneg _) hnn
    _ = (2 * K / δ) * |u - t| := by ring

end Work.BoseFixB1B
