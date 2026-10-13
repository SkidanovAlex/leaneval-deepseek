import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Order.CompletePartialOrder

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.EllipticEst

/-- Jordan's inequality for `cos` on `[0, π/2]` (`cos θ = sin (π/2 - θ)`). -/
private theorem cos_lower_of_mem_Icc' {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (π / 2)) :
    2 / π * (π / 2 - θ) ≤ Real.cos θ := by
  have h1 : 0 ≤ π / 2 - θ := by linarith [hθ.2]
  have h2 : π / 2 - θ ≤ π / 2 := by linarith [hθ.1]
  have h := Real.mul_le_sin h1 h2
  rwa [Real.sin_pi_div_two_sub] at h

/-- **The antiderivative extends continuously to the closed interval.**  For `f` which is `C²` on
`[0, π/2]` and vanishes at `π/2`, the function
`F(θ) = -(derivWithin f (Icc 0 (π/2)) θ)·f(θ) + (1/2)·tan θ·f(θ)²` is continuous on
`[0, π/2]`.  At `π/2` the potentially singular factor is `tan θ · f(θ)² = sin θ·(f(θ)/cos θ)·f(θ)`,
which tends to `0` because `f` vanishes to first order at `π/2`; `F(π/2) = 0` by Lean's
conventions (`Real.tan_pi_div_two`, `f (π/2) = 0`). -/
theorem continuousOn_antideriv (f : ℝ → ℝ)
    (hs : ContDiffOn ℝ 2 f (Set.Icc 0 (π / 2))) (h1 : f (π / 2) = 0) :
    ContinuousOn (fun θ => -(derivWithin f (Set.Icc 0 (π / 2)) θ) * f θ
      + (1 / 2) * Real.tan θ * (f θ) ^ 2) (Set.Icc 0 (π / 2)) := by
  have hpi : (0 : ℝ) < π / 2 := by positivity
  have huniq : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) (π / 2)) := uniqueDiffOn_Icc hpi
  have hfc : ContinuousOn f (Set.Icc (0 : ℝ) (π / 2)) := hs.continuousOn
  have hdc : ContinuousOn (derivWithin f (Set.Icc (0 : ℝ) (π / 2))) (Set.Icc (0 : ℝ) (π / 2)) :=
    hs.continuousOn_derivWithin huniq (by norm_num)
  have hdiff : DifferentiableOn ℝ f (Set.Icc (0 : ℝ) (π / 2)) := hs.differentiableOn (by norm_num)
  obtain ⟨C₀, hC₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hdc
  have hbd : ∀ x ∈ Set.Icc (0 : ℝ) (π / 2),
      ‖derivWithin f (Set.Icc (0 : ℝ) (π / 2)) x‖ ≤ max C₀ 0 :=
    fun x hx => le_trans (hC₀ x hx) (le_max_left _ _)
  -- `f` vanishes at `π/2` at least to first order
  have hslope : ∀ θ ∈ Set.Icc (0 : ℝ) (π / 2), |f θ| ≤ max C₀ 0 * (π / 2 - θ) := by
    intro θ hθ
    have hmem : (π / 2 : ℝ) ∈ Set.Icc (0 : ℝ) (π / 2) := ⟨hpi.le, le_rfl⟩
    have h := Convex.norm_image_sub_le_of_norm_derivWithin_le hdiff hbd
      (convex_Icc (0 : ℝ) (π / 2)) hmem hθ
    have hn : ‖θ - π / 2‖ = π / 2 - θ := by
      rw [Real.norm_eq_abs, abs_of_nonpos (by linarith [hθ.2])]
      ring
    rw [h1, sub_zero, hn, Real.norm_eq_abs] at h
    exact h
  -- bound on the singular term `tan θ · f θ ^ 2`
  have htanbd : ∀ θ ∈ Set.Icc (0 : ℝ) (π / 2),
      ‖Real.tan θ * (f θ) ^ 2‖ ≤ (max C₀ 0) ^ 2 * (π / 2) * (π / 2 - θ) := by
    intro θ hθ
    rcases lt_or_eq_of_le hθ.2 with hlt | heq
    · have hh : 0 < π / 2 - θ := by linarith
      have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1], hlt⟩
      have hj : 2 / π * (π / 2 - θ) ≤ Real.cos θ := cos_lower_of_mem_Icc' hθ
      have hpid : π / 2 * (2 / π) = (1 : ℝ) := by
        rw [div_mul_div_comm, mul_comm π 2, div_self (mul_ne_zero two_ne_zero Real.pi_ne_zero)]
      have hkey : π / 2 - θ ≤ π / 2 * Real.cos θ := by
        have h' : π / 2 * (2 / π * (π / 2 - θ)) ≤ π / 2 * Real.cos θ :=
          mul_le_mul_of_nonneg_left hj hpi.le
        have h2 : π / 2 * (2 / π * (π / 2 - θ)) = π / 2 - θ := by
          rw [← mul_assoc, hpid, one_mul]
        rwa [h2] at h'
      have htan : |Real.tan θ| * (π / 2 - θ) ≤ π / 2 := by
        rw [Real.tan_eq_sin_div_cos, abs_div,
          abs_of_nonneg (Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩),
          abs_of_pos hcos,
          show Real.sin θ / Real.cos θ * (π / 2 - θ)
              = Real.sin θ * (π / 2 - θ) / Real.cos θ by ring]
        rw [div_le_iff₀ hcos]
        calc Real.sin θ * (π / 2 - θ) ≤ 1 * (π / 2 - θ) :=
              mul_le_mul_of_nonneg_right (Real.sin_le_one θ) (le_of_lt hh)
          _ = π / 2 - θ := by ring
          _ ≤ π / 2 * Real.cos θ := hkey
      have hsq : (f θ) ^ 2 ≤ (max C₀ 0 * (π / 2 - θ)) ^ 2 := by
        calc (f θ) ^ 2 = |f θ| ^ 2 := (sq_abs _).symm
          _ ≤ (max C₀ 0 * (π / 2 - θ)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hslope θ hθ) 2
      have hone : ‖Real.tan θ * (f θ) ^ 2‖ = |Real.tan θ| * (f θ) ^ 2 := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (f θ))]
      calc ‖Real.tan θ * (f θ) ^ 2‖
          = |Real.tan θ| * (f θ) ^ 2 := hone
        _ ≤ |Real.tan θ| * (max C₀ 0 * (π / 2 - θ)) ^ 2 :=
            mul_le_mul_of_nonneg_left hsq (abs_nonneg _)
        _ = (|Real.tan θ| * (π / 2 - θ)) * ((max C₀ 0) ^ 2 * (π / 2 - θ)) := by ring
        _ ≤ (π / 2) * ((max C₀ 0) ^ 2 * (π / 2 - θ)) :=
            mul_le_mul_of_nonneg_right htan (mul_nonneg (sq_nonneg _) (by linarith [hθ.2]))
        _ = (max C₀ 0) ^ 2 * (π / 2) * (π / 2 - θ) := by ring
    · subst heq
      simp [Real.tan_pi_div_two, h1]
  -- continuity of the two summands
  have hT1 : ContinuousOn (fun θ => -(derivWithin f (Set.Icc (0 : ℝ) (π / 2))) θ * f θ)
      (Set.Icc (0 : ℝ) (π / 2)) := hdc.neg.mul hfc
  have hT2 : ContinuousOn (fun θ => (1 / 2) * Real.tan θ * (f θ) ^ 2)
      (Set.Icc (0 : ℝ) (π / 2)) := by
    intro θ hθ
    rcases lt_or_eq_of_le hθ.2 with hlt | heq
    · have hcos : Real.cos θ ≠ 0 :=
        ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1], hlt⟩)
      have htan : ContinuousWithinAt Real.tan (Set.Icc (0 : ℝ) (π / 2)) θ :=
        (Real.continuousAt_tan.mpr hcos).continuousWithinAt
      have hbase : ContinuousWithinAt (fun x => (1 / 2) * (Real.tan x * (f x) ^ 2))
          (Set.Icc (0 : ℝ) (π / 2)) θ :=
        (htan.mul ((hfc.continuousWithinAt hθ).pow 2)).const_mul (1 / 2)
      simpa only [mul_assoc] using hbase
    · subst heq
      have hlim : Filter.Tendsto (fun θ => Real.tan θ * (f θ) ^ 2)
          (nhdsWithin (π / 2) (Set.Icc (0 : ℝ) (π / 2))) (nhds 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        refine squeeze_zero' (g := fun θ : ℝ => (max C₀ 0) ^ 2 * (π / 2) * (π / 2 - θ))
          (Filter.Eventually.of_forall fun θ => norm_nonneg _) ?_ ?_
        · rw [eventually_nhdsWithin_iff]
          exact Filter.Eventually.of_forall fun θ hθ => htanbd θ hθ
        · have hc : Continuous fun θ : ℝ => (max C₀ 0) ^ 2 * (π / 2) * (π / 2 - θ) := by fun_prop
          have hmono := (hc.tendsto (π / 2)).mono_left
            (nhdsWithin_le_nhds (s := Set.Icc (0 : ℝ) (π / 2)))
          simpa using hmono
      have hcont_g : ContinuousWithinAt (fun x => Real.tan x * (f x) ^ 2)
          (Set.Icc (0 : ℝ) (π / 2)) (π / 2) := by
        change Filter.Tendsto (fun x : ℝ => Real.tan x * (f x) ^ 2)
          (nhdsWithin (π / 2) (Set.Icc (0 : ℝ) (π / 2)))
          (nhds (Real.tan (π / 2) * (f (π / 2)) ^ 2))
        rw [show Real.tan (π / 2) * (f (π / 2)) ^ 2 = 0 by simp [Real.tan_pi_div_two, h1]]
        exact hlim
      have hbase : ContinuousWithinAt (fun x => (1 / 2) * (Real.tan x * (f x) ^ 2))
          (Set.Icc (0 : ℝ) (π / 2)) (π / 2) := hcont_g.const_mul (1 / 2)
      simpa only [mul_assoc] using hbase
  exact hT1.add hT2

end Work.FTS.EllipticEst
