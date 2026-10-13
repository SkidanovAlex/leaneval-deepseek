import Mathlib.Algebra.Order.Ring.Star
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

/-- Mean-value anchor near `0`: for `u` bounded by `K₀` on `(0, π/2)` and `k ≥ 2` there is a point
`ξ ∈ (θ/(2k), θ/k)` where the derivative of `u` is controlled by `4K₀k/θ`. -/
theorem exists_anchor_left {u : ℝ → ℝ} {K₀ θ : ℝ} (hK₀ : 0 ≤ K₀) (hθ0 : 0 < θ)
    (hθ1 : θ < Real.pi / 2)
    (hu : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), DifferentiableAt ℝ u x)
    (hub : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |u x| ≤ K₀)
    {k : ℕ} (hk : 2 ≤ k) :
    ∃ ξ ∈ Set.Ioo (θ / (2 * (k : ℝ))) (θ / (k : ℝ)),
      |deriv u ξ| ≤ 4 * K₀ * (k : ℝ) / θ := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by
    have : 0 < k := by omega
    exact_mod_cast this
  have hk2 : (2 : ℝ) ≤ (k : ℝ) := by
    have h2 : 2 ≤ k := hk
    exact_mod_cast h2
  have h2k : (0 : ℝ) < 2 * (k : ℝ) := by linarith
  set a : ℝ := θ / (2 * (k : ℝ)) with ha
  set b : ℝ := θ / (k : ℝ) with hb
  have ha_pos : 0 < a := by rw [ha]; exact div_pos hθ0 h2k
  have hb_pos : 0 < b := by rw [hb]; exact div_pos hθ0 hk0
  have hb_le : b ≤ θ / 2 := by
    rw [hb]
    exact div_le_div_of_nonneg_left hθ0.le (by norm_num) hk2
  have hb_lt : b < Real.pi / 2 := by
    have h1 : θ / 2 < Real.pi / 4 := by linarith [hθ1]
    have h2 : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
    linarith [hb_le, h1, h2]
  have hab : a < b := by
    rw [ha, hb, div_lt_div_iff₀ h2k hk0]
    nlinarith [hθ0, hk0]
  have hcont : ContinuousOn u (Set.Icc a b) := by
    intro x hx
    have hx' : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨lt_of_lt_of_le ha_pos hx.1, lt_of_le_of_lt hx.2 hb_lt⟩
    exact (hu x hx').continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ u (Set.Ioo a b) := by
    intro x hx
    have hx' : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨lt_of_lt_of_le ha_pos hx.1.le, lt_of_le_of_lt hx.2.le hb_lt⟩
    exact (hu x hx').differentiableWithinAt
  obtain ⟨ξ, hξ, hξd⟩ := exists_deriv_eq_slope u hab hcont hdiff
  refine ⟨ξ, hξ, ?_⟩
  have hua : |u a| ≤ K₀ := hub a ⟨ha_pos, lt_trans hab hb_lt⟩
  have hub' : |u b| ≤ K₀ := hub b ⟨hb_pos, hb_lt⟩
  have hnum : |u b - u a| ≤ 2 * K₀ := by
    calc |u b - u a| = |u b + -u a| := by ring_nf
      _ ≤ |u b| + |-u a| := abs_add_le _ _
      _ = |u b| + |u a| := by rw [abs_neg]
      _ ≤ K₀ + K₀ := add_le_add hub' hua
      _ = 2 * K₀ := by ring
  have hden : |b - a| = θ / (2 * (k : ℝ)) := by
    rw [abs_of_pos (sub_pos.mpr hab), hb, ha]
    field_simp
    ring
  have hstep : |deriv u ξ| ≤ 2 * K₀ / (θ / (2 * (k : ℝ))) := by
    rw [hξd, abs_div, hden]
    exact div_le_div_of_nonneg_right hnum ha_pos.le
  refine le_trans hstep ?_
  have heq : 2 * K₀ / (θ / (2 * (k : ℝ))) = 4 * K₀ * (k : ℝ) / θ := by
    field_simp
    ring
  rw [heq]

end Work.FTS_StreamBdry.SB3.P2Aux
