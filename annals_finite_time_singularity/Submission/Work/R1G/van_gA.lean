import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.R1G.AnG

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.R1G

/-- **The angular vanishing of the analytic perturbation.**

For `0 < α ≤ 1/2` one has `|gA z θ| ≤ 2 · Γ(α,θ)` for all `z ≥ 0` and `θ ∈ [0,π/2]`,
where `Γ(α,θ) = (sin θ · cos²θ)^α`.

The proof is elementary.  On the quadrant `θ ∈ [0,π/2]` the radial factor obeys
`0 ≤ Zf z ≤ 1` and the angular factor is `Tf θ = sin(2θ) = 2 sin θ cos θ ≥ 0`, so
`|gA z θ| ≤ 2 sin θ cos θ`.  Writing `s = sin θ`, `c = cos θ ∈ [0,1]`, the elementary
inequality `x ≤ x^y` for `x ∈ [0,1]`, `y ≤ 1` gives `s ≤ s^α` and, since `2α ≤ 1`,
`c ≤ c^{2α}`; multiplying yields `s c ≤ s^α c^{2α} = (s c²)^α = Γ(α,θ)`.  Hence `C = 2`
works. -/
theorem van_gA (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |Work.R1G.gA z θ| ≤ C * Work.ConstructionInstance.Gamma α θ := by
  refine ⟨2, by norm_num, ?_⟩
  intro z θ hz hθ
  -- basic one-variable facts on the quadrant
  have hs0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have hc0 : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, hθ.1], by linarith [Real.pi_pos, hθ.2]⟩
  have hc1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have hZ0 : 0 ≤ Work.R1G.Zf z := Work.R1G.Zf_nonneg hz
  have hZ1 : Work.R1G.Zf z ≤ 1 := Work.R1G.Zf_le_one hz
  have hT0 : 0 ≤ Work.R1G.Tf θ := Work.R1G.Tf_nonneg hθ
  have hTval : Work.R1G.Tf θ = 2 * Real.sin θ * Real.cos θ := by
    rw [Work.R1G.Tf]; exact Real.sin_two_mul θ
  -- `|gA z θ| ≤ 2 sin θ cos θ`
  have hstep1 : |Work.R1G.gA z θ| ≤ 2 * (Real.sin θ * Real.cos θ) := by
    have hga : Work.R1G.gA z θ = Work.R1G.Zf z * Work.R1G.Tf θ := rfl
    rw [hga, abs_of_nonneg (mul_nonneg hZ0 hT0), hTval]
    calc Work.R1G.Zf z * (2 * Real.sin θ * Real.cos θ)
        ≤ 1 * (2 * Real.sin θ * Real.cos θ) := by
          apply mul_le_mul_of_nonneg_right hZ1
          positivity
      _ = 2 * (Real.sin θ * Real.cos θ) := by ring
  -- the angular bound `2 sin θ cos θ ≤ 2 Γ(α,θ)`
  have hs_le : Real.sin θ ≤ Real.sin θ ^ α :=
    Real.self_le_rpow_of_le_one hs0 hs1 (by linarith)
  have hc_le : Real.cos θ ≤ Real.cos θ ^ (2 * α) :=
    Real.self_le_rpow_of_le_one hc0 hc1 (by linarith)
  have hprod : Real.sin θ * Real.cos θ ≤ Real.sin θ ^ α * Real.cos θ ^ (2 * α) :=
    mul_le_mul hs_le hc_le hc0 (Real.rpow_nonneg hs0 α)
  have hGam : Work.ConstructionInstance.Gamma α θ = Real.sin θ ^ α * Real.cos θ ^ (2 * α) := by
    rw [Work.ConstructionInstance.Gamma,
      Real.mul_rpow hs0 (by positivity : (0:ℝ) ≤ Real.cos θ ^ 2)]
    congr 1
    exact (Real.rpow_natCast_mul hc0 2 α).symm
  have hstep2 : 2 * (Real.sin θ * Real.cos θ) ≤ 2 * Work.ConstructionInstance.Gamma α θ := by
    rw [hGam]
    linarith [hprod]
  linarith [hstep1, hstep2]

end Work.R1G
