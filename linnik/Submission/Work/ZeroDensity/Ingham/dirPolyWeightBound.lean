import Mathlib

namespace Work.ZeroDensity.Ingham

/-- For `a > 0` and `σ ≥ 0`, the drop of `x ↦ x ^ (-σ)` over the unit interval starting at `a`
is at most `σ · a ^ (-σ) / a`.  This is the mean-value/concavity bound obtained from
`(1 + 1/a) ^ (-σ) ≥ 1 - σ/a`, written in exponential form. -/
lemma rpow_sub_le_of_nonneg (a : ℝ) (ha : 0 < a) (σ : ℝ) (hσ : 0 ≤ σ) :
    a ^ (-σ) - (a + 1) ^ (-σ) ≤ σ * a ^ (-σ) / a := by
  have h1 : (0:ℝ) < a + 1 := by linarith
  conv_lhs => rw [Real.rpow_def_of_pos ha (-σ), Real.rpow_def_of_pos h1 (-σ)]
  have hML : Real.log (a + 1) - Real.log a ≤ 1 / a := by
    have h2 : Real.log ((a + 1) / a) ≤ (a + 1) / a - 1 :=
      Real.log_le_sub_one_of_pos (div_pos (by linarith) ha)
    rw [Real.log_div (by linarith) (ne_of_gt ha)] at h2
    have h3 : (a + 1) / a - 1 = 1 / a := by field_simp; ring
    linarith
  have key : Real.exp (Real.log (a + 1) * -σ)
      = Real.exp (Real.log a * -σ) * Real.exp (-(σ * (Real.log (a + 1) - Real.log a))) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [key]
  have hbnd : 1 - Real.exp (-(σ * (Real.log (a + 1) - Real.log a)))
      ≤ σ * (Real.log (a + 1) - Real.log a) := by
    have := Real.add_one_le_exp (-(σ * (Real.log (a + 1) - Real.log a)))
    linarith
  have hposA : 0 < Real.exp (Real.log a * -σ) := Real.exp_pos _
  calc Real.exp (Real.log a * -σ)
        - Real.exp (Real.log a * -σ) * Real.exp (-(σ * (Real.log (a + 1) - Real.log a)))
      = Real.exp (Real.log a * -σ) * (1 - Real.exp (-(σ * (Real.log (a + 1) - Real.log a)))) := by ring
    _ ≤ Real.exp (Real.log a * -σ) * (σ * (Real.log (a + 1) - Real.log a)) :=
        mul_le_mul_of_nonneg_left hbnd hposA.le
    _ ≤ Real.exp (Real.log a * -σ) * (σ * (1 / a)) := by
        apply mul_le_mul_of_nonneg_left _ hposA.le
        exact mul_le_mul_of_nonneg_left hML hσ
    _ = σ * a ^ (-σ) / a := by
        rw [← Real.rpow_def_of_pos ha (-σ)]
        ring

/-- The weight `n ^ (-σ) - (n+1) ^ (-σ)` times `n log n` is at most `1`, for `σ ≥ 0`
and `n ≥ 2`.  This is the elementary mean-value bound used in Ingham's zero-density
argument: the drop of `x ↦ x ^ (-σ)` is controlled by the derivative `σ x ^ (-σ-1)`. -/
theorem dirPolyWeightBound :
    ∀ (σ : ℝ), 0 ≤ σ → ∀ (n : ℕ), 2 ≤ n →
      ((n : ℝ) ^ (-σ) - (((n + 1 : ℕ)) : ℝ) ^ (-σ)) * ((n : ℝ) * Real.log (n : ℝ)) ≤ 1 := by
  intro σ hσ n hn
  have hn2 : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hna : 0 < (n:ℝ) := by linarith
  have hcast : (((n + 1 : ℕ)) : ℝ) = (n:ℝ) + 1 := by push_cast; ring
  rw [hcast]
  have hlogn : 0 ≤ Real.log (n:ℝ) := le_of_lt (Real.log_pos (by linarith))
  have hmulnonneg : 0 ≤ (n:ℝ) * Real.log (n:ℝ) := mul_nonneg hna.le hlogn
  have hdiff := rpow_sub_le_of_nonneg (n:ℝ) hna σ hσ
  have hexp : (n:ℝ)^(-σ) = Real.exp (-(σ * Real.log (n:ℝ))) := by
    rw [Real.rpow_def_of_pos hna]
    congr 1
    ring
  calc ((n:ℝ)^(-σ) - ((n:ℝ)+1)^(-σ)) * ((n:ℝ) * Real.log (n:ℝ))
      ≤ (σ * (n:ℝ)^(-σ) / (n:ℝ)) * ((n:ℝ) * Real.log (n:ℝ)) :=
        mul_le_mul_of_nonneg_right hdiff hmulnonneg
    _ = σ * (n:ℝ)^(-σ) * Real.log (n:ℝ) := by
        have hb0 : (n:ℝ) ≠ 0 := ne_of_gt hna
        field_simp
    _ = (σ * Real.log (n:ℝ)) * Real.exp (-(σ * Real.log (n:ℝ))) := by
        rw [hexp]; ring
    _ ≤ Real.exp (-1) := Real.mul_exp_neg_le_exp_neg_one (σ * Real.log (n:ℝ))
    _ ≤ 1 := by rw [Real.exp_le_one_iff]; norm_num

end Work.ZeroDensity.Ingham
