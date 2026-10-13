import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.mixed_Jeps_tendsto

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.StrongEps.E5G

theorem Jeps_tendsto_of_modulus {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    {Y : ℕ → Work.FTS.Galerkin.Fn} {Yl : Work.FTS.Galerkin.Fn} {ε : ℕ → ℝ} {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hεpos : ∀ n : ℕ, 0 < ε n) (hε0 : Filter.Tendsto ε Filter.atTop (nhds 0))
    (hcont : ∀ n : ℕ, ContinuousOn (Function.uncurry (Y n)) Work.FTS.StrongEps.Quad)
    (hequi : ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ, ∀ p : ℝ × ℝ, ‖p‖ ≤ δ →
      |Y n (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2) - Y n z θ| ≤ η)
    (hlim : Filter.Tendsto (fun n : ℕ => Y n z θ) Filter.atTop (nhds (Yl z θ))) :
    Filter.Tendsto (fun n : ℕ => Work.FTS.StrongEps.Jeps ρ (ε n) (Y n) z θ) Filter.atTop
      (nhds (Yl z θ)) := by
  -- The equicontinuity modulus `δ` of `hequi` is independent of `n`; since `ε n → 0`, for all
  -- large `n` the ball `‖p‖ ≤ ε n` on which the kernel `Jker ρ (ε n)` lives is contained in the
  -- ball `‖p‖ ≤ δ`, so the profiles are uniformly within `η` of their value at `(z,θ)` there.
  have huc : ∀ η : ℝ, 0 < η → ∀ᶠ n in Filter.atTop, ∀ p : ℝ × ℝ, ‖p‖ ≤ ε n →
      |Y n (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2) - Y n z θ| ≤ η := by
    intro η hη
    obtain ⟨δ, hδpos, hδ⟩ := hequi η hη
    have hsmall : ∀ᶠ n in Filter.atTop, ε n < δ := by
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hε0 δ hδpos
      filter_upwards [Filter.eventually_ge_atTop N] with n hn
      have h := hN n hn
      rw [Real.dist_eq, sub_zero, abs_of_pos (hεpos n)] at h
      exact h
    filter_upwards [hsmall] with n hn p hp
    exact hδ n p (le_trans hp hn.le)
  -- The peak estimate for the mollifier turns the uniform closeness on the shrinking ball into
  -- the sequential convergence of the mollified profiles to their pointwise limit.
  exact Work.FTS.StrongEps.tendsto_Jeps_of_continuousOn ρ hρ hz hθ
    (fun n => hcont n) hεpos huc hlim

end Work.FTS.StrongEps.E5G
