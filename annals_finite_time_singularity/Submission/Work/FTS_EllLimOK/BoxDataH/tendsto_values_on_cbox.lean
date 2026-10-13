import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.BoxDataH

/-- Convergence of `un n z θ` to `Ψ z θ` on the *closed* box `[a,b] × [0,π/2]` (`0 < a`),
given convergence on the open quadrant `Q0 = (0,∞) × (0,π/2)` and the vanishing of both the
sequence and its limit at the two boundary angles `θ = 0` and `θ = π/2`.

The only non-trivial case is the interior one, where `(z,θ) ∈ Q0`; at `θ = 0` and `θ = π/2`
(with `z ≥ 0`) the sequence is identically zero and so is the limit. -/
theorem tendsto_values_on_cbox {Ψ : ℝ → ℝ → ℝ} {un : ℕ → ℝ → ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hconv : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Filter.Tendsto (fun n => un n z θ) Filter.atTop (nhds (Ψ z θ)))
    (hvan0 : ∀ z : ℝ, Ψ z 0 = 0) (hvan1 : ∀ z : ℝ, Ψ z (Real.pi / 2) = 0)
    (hzero : ∀ n : ℕ, ∀ z : ℝ, 0 ≤ z → un n z 0 = 0 ∧ un n z (Real.pi / 2) = 0) :
    ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (Real.pi / 2),
      Filter.Tendsto (fun n => un n z θ) Filter.atTop (nhds (Ψ z θ)) := by
  intro z hz θ hθ
  obtain ⟨hza, _⟩ := hz
  obtain ⟨hθ0, hθ2⟩ := hθ
  have hzpos : 0 < z := lt_of_lt_of_le ha hza
  have hz0 : 0 ≤ z := le_of_lt hzpos
  -- the sequence is constantly `0` when `θ = 0`
  have hvanish0 : (fun n : ℕ => un n z 0) = fun _ : ℕ => (0 : ℝ) := by
    funext n; exact (hzero n z hz0).1
  -- the sequence is constantly `0` when `θ = π/2`
  have hvanish1 : (fun n : ℕ => un n z (Real.pi / 2)) = fun _ : ℕ => (0 : ℝ) := by
    funext n; exact (hzero n z hz0).2
  by_cases h0 : θ = 0
  · -- boundary angle `θ = 0`
    rw [h0, hvan0 z, hvanish0]
    exact tendsto_const_nhds
  by_cases h2 : θ = Real.pi / 2
  · -- boundary angle `θ = π/2`
    rw [h2, hvan1 z, hvanish1]
    exact tendsto_const_nhds
  · -- interior angle: the point lies in the open quadrant
    exact hconv z θ (Work.FTS.EllipticEst.mem_Q0.mpr
      ⟨hzpos, lt_of_le_of_ne hθ0 (Ne.symm h0), lt_of_le_of_ne hθ2 h2⟩)

end Work.FTS_EllLimOK.BoxDataH
