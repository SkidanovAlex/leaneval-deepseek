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

/-- **Endpoint bound for `θ ↦ f(θ)/cos θ`.**  If `f` is `C²` on `[0, π/2]` and `f(π/2) = 0`, then
`f/cos` is bounded on `[0, π/2]`.  (With Lean's totalised division the value at `π/2` is
`0/0 = 0`.)  This is the "`v` vanishes to first order at `π/2`" statement needed for the
integrability of the `(v/cos)²` term in `Work.FTS.EllipticEst.Lzero_self_form`; a proof can go
through `f θ = f θ - f(π/2) = ∫_θ^{π/2} f'` together with Jordan's inequality
`Real.mul_le_sin` for `cos θ = sin (π/2 - θ)`. -/
theorem exists_bound_div_cos (f : ℝ → ℝ)
    (hs : ContDiffOn ℝ 2 f (Set.Icc 0 (π / 2))) (h1 : f (π / 2) = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Set.Icc (0 : ℝ) (π / 2), |f θ / Real.cos θ| ≤ C := by
  have hlt : (0 : ℝ) < π / 2 := Real.pi_div_two_pos
  have hle : (0 : ℝ) ≤ π / 2 := hlt.le
  have hmem : (π / 2) ∈ Set.Icc (0 : ℝ) (π / 2) := ⟨hle, le_rfl⟩
  have hU : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) (π / 2)) := uniqueDiffOn_Icc hlt
  have hdiff : DifferentiableOn ℝ f (Set.Icc (0 : ℝ) (π / 2)) :=
    hs.differentiableOn (by norm_num)
  have hcont : ContinuousOn (derivWithin f (Set.Icc (0 : ℝ) (π / 2)))
      (Set.Icc (0 : ℝ) (π / 2)) := hs.continuousOn_derivWithin hU (by norm_num)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  set M' : ℝ := max M 0 with hM'def
  have hM'0 : 0 ≤ M' := le_max_right _ _
  have hM'b : ∀ x ∈ Set.Icc (0 : ℝ) (π / 2),
      ‖derivWithin f (Set.Icc (0 : ℝ) (π / 2)) x‖ ≤ M' :=
    fun x hx => le_trans (hM x hx) (le_max_left _ _)
  refine ⟨M' * π / 2, div_nonneg (mul_nonneg hM'0 Real.pi_pos.le) (by norm_num),
    fun θ hθ => ?_⟩
  have hmvt : ‖f θ - f (π / 2)‖ ≤ M' * ‖θ - π / 2‖ :=
    Convex.norm_image_sub_le_of_norm_derivWithin_le hdiff hM'b (convex_Icc _ _) hmem hθ
  have hnorm : ‖θ - π / 2‖ = π / 2 - θ := by
    rw [Real.norm_eq_abs, abs_of_nonpos (by linarith [hθ.2])]
    ring
  have hfθ : |f θ| ≤ M' * (π / 2 - θ) := by
    calc |f θ| = ‖f θ‖ := by rw [Real.norm_eq_abs]
      _ = ‖f θ - f (π / 2)‖ := by rw [h1, sub_zero]
      _ ≤ M' * ‖θ - π / 2‖ := hmvt
      _ = M' * (π / 2 - θ) := by rw [hnorm]
  rcases lt_or_eq_of_le hθ.2 with hlt2 | heq
  · -- interior of the interval: `f` vanishes at `π/2` at least to first order
    have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1], hlt2⟩
    have hx0 : 0 < π / 2 - θ := by linarith
    have hxle : π / 2 - θ ≤ π / 2 := by linarith [hθ.1]
    -- Jordan's inequality: `(2/π) * (π/2 - θ) ≤ sin (π/2 - θ) = cos θ`
    have hj : 2 / π * (π / 2 - θ) ≤ Real.cos θ := by
      have h := Real.mul_le_sin hx0.le hxle
      rwa [Real.sin_pi_div_two_sub] at h
    have hpid : π / 2 * (2 / π) = (1 : ℝ) := by
      rw [div_mul_div_comm, mul_comm π 2, div_self (mul_ne_zero two_ne_zero Real.pi_ne_zero)]
    have hkey : π / 2 - θ ≤ π / 2 * Real.cos θ := by
      have h' : π / 2 * (2 / π * (π / 2 - θ)) ≤ π / 2 * Real.cos θ :=
        mul_le_mul_of_nonneg_left hj hle
      have h2 : π / 2 * (2 / π * (π / 2 - θ)) = π / 2 - θ := by
        rw [← mul_assoc, hpid, one_mul]
      rw [h2] at h'
      exact h'
    rw [abs_div, abs_of_pos hcos, div_le_iff₀ hcos]
    calc |f θ| ≤ M' * (π / 2 - θ) := hfθ
      _ ≤ M' * (π / 2 * Real.cos θ) := mul_le_mul_of_nonneg_left hkey hM'0
      _ = M' * π / 2 * Real.cos θ := by ring
  · -- the endpoint `θ = π/2`, where `f(π/2)/cos(π/2) = 0/0 = 0`
    subst heq
    rw [h1, Real.cos_pi_div_two]
    simp only [div_zero, abs_zero]
    exact div_nonneg (mul_nonneg hM'0 Real.pi_pos.le) (by norm_num)

end Work.FTS.EllipticEst
