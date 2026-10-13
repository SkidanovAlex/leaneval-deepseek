import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.SB3.P2Aux

/-- Mean-value anchor near `π/2`: for `u` bounded by `K₀` on `(0, π/2)` and `k ≥ 3` there is a
point `ξ ∈ (π/2 - 2ε/k, π/2 - ε/k)`, `ε = π/2 - θ`, where the derivative of `u` is controlled by
`2K₀k/ε`. -/
theorem exists_anchor_right {u : ℝ → ℝ} {K₀ θ : ℝ} (hK₀ : 0 ≤ K₀) (hθ0 : 0 < θ)
    (hθ1 : θ < Real.pi / 2)
    (hu : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), DifferentiableAt ℝ u x)
    (hub : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |u x| ≤ K₀)
    {k : ℕ} (hk : 3 ≤ k) :
    ∃ ξ ∈ Set.Ioo (Real.pi / 2 - 2 * (Real.pi / 2 - θ) / (k : ℝ))
        (Real.pi / 2 - (Real.pi / 2 - θ) / (k : ℝ)),
      |deriv u ξ| ≤ 2 * K₀ * (k : ℝ) / (Real.pi / 2 - θ) := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by
    have : 0 < k := by omega
    exact_mod_cast this
  have hk3 : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hεpos : 0 < Real.pi / 2 - θ := by linarith
  have hεlt : Real.pi / 2 - θ < Real.pi / 2 := by linarith
  have hdpos : 0 < (Real.pi / 2 - θ) / (k : ℝ) := div_pos hεpos hkpos
  have hdlt4 : (Real.pi / 2 - θ) / (k : ℝ) < Real.pi / 4 := by
    rw [div_lt_iff₀ hkpos]
    nlinarith [hεlt, Real.pi_pos, hk3]
  have h2d : 2 * (Real.pi / 2 - θ) / (k : ℝ) = 2 * ((Real.pi / 2 - θ) / (k : ℝ)) := by
    ring
  have hapos : 0 < Real.pi / 2 - 2 * (Real.pi / 2 - θ) / (k : ℝ) := by
    rw [h2d]; linarith
  have hbpos : 0 < Real.pi / 2 - (Real.pi / 2 - θ) / (k : ℝ) := by
    linarith [Real.pi_pos]
  have hblt : Real.pi / 2 - (Real.pi / 2 - θ) / (k : ℝ) < Real.pi / 2 := by linarith
  have hab : Real.pi / 2 - 2 * (Real.pi / 2 - θ) / (k : ℝ)
      < Real.pi / 2 - (Real.pi / 2 - θ) / (k : ℝ) := by
    rw [h2d]; linarith
  have hcont : ContinuousOn u (Set.Icc (Real.pi / 2 - 2 * (Real.pi / 2 - θ) / (k : ℝ))
        (Real.pi / 2 - (Real.pi / 2 - θ) / (k : ℝ))) := by
    intro x hx
    exact (hu x ⟨lt_of_lt_of_le hapos hx.1,
      lt_of_le_of_lt hx.2 hblt⟩).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ u (Set.Ioo (Real.pi / 2 - 2 * (Real.pi / 2 - θ) / (k : ℝ))
        (Real.pi / 2 - (Real.pi / 2 - θ) / (k : ℝ))) := by
    intro x hx
    exact (hu x ⟨lt_of_lt_of_le hapos hx.1.le,
      lt_of_le_of_lt hx.2.le hblt⟩).differentiableWithinAt
  obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope u hab hcont hdiff
  refine ⟨c, hc, ?_⟩
  have hba : 0 < (Real.pi / 2 - (Real.pi / 2 - θ) / (k : ℝ))
      - (Real.pi / 2 - 2 * (Real.pi / 2 - θ) / (k : ℝ)) := sub_pos.mpr hab
  have hden : (Real.pi / 2 - (Real.pi / 2 - θ) / (k : ℝ))
      - (Real.pi / 2 - 2 * (Real.pi / 2 - θ) / (k : ℝ)) = (Real.pi / 2 - θ) / (k : ℝ) := by
    ring
  have hnum : |u (Real.pi / 2 - (Real.pi / 2 - θ) / (k : ℝ))
      - u (Real.pi / 2 - 2 * (Real.pi / 2 - θ) / (k : ℝ))| ≤ 2 * K₀ := by
    have h1 := hub (Real.pi / 2 - 2 * (Real.pi / 2 - θ) / (k : ℝ)) ⟨hapos, lt_trans hab hblt⟩
    have h2 := hub (Real.pi / 2 - (Real.pi / 2 - θ) / (k : ℝ)) ⟨hbpos, hblt⟩
    have htri : |u (Real.pi / 2 - (Real.pi / 2 - θ) / (k : ℝ))
        - u (Real.pi / 2 - 2 * (Real.pi / 2 - θ) / (k : ℝ))|
        ≤ |u (Real.pi / 2 - (Real.pi / 2 - θ) / (k : ℝ))|
          + |u (Real.pi / 2 - 2 * (Real.pi / 2 - θ) / (k : ℝ))| := by
      simpa using abs_sub_le (u (Real.pi / 2 - (Real.pi / 2 - θ) / (k : ℝ))) 0
        (u (Real.pi / 2 - 2 * (Real.pi / 2 - θ) / (k : ℝ)))
    linarith
  rw [hcd, abs_div, abs_of_pos hba]
  calc |u (Real.pi / 2 - (Real.pi / 2 - θ) / (k : ℝ))
        - u (Real.pi / 2 - 2 * (Real.pi / 2 - θ) / (k : ℝ))|
        / ((Real.pi / 2 - (Real.pi / 2 - θ) / (k : ℝ))
          - (Real.pi / 2 - 2 * (Real.pi / 2 - θ) / (k : ℝ)))
      ≤ (2 * K₀) / ((Real.pi / 2 - (Real.pi / 2 - θ) / (k : ℝ))
          - (Real.pi / 2 - 2 * (Real.pi / 2 - θ) / (k : ℝ))) :=
        div_le_div_of_nonneg_right hnum hba.le
    _ = 2 * K₀ * (k : ℝ) / (Real.pi / 2 - θ) := by
        rw [hden, div_div_eq_mul_div]; try ring

end Work.FTS_StreamBdry.SB3.P2Aux
