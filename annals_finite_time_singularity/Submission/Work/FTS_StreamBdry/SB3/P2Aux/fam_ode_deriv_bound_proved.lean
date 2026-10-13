import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB3.P2Aux.FamOde.CaseLeft
import Submission.Work.FTS_StreamBdry.SB3.P2Aux.FamOde.CaseRight

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.SB3.P2Aux

open scoped Real Topology
open Set Filter

/-- **`z`-uniform first-order bound for the singular ODE `w' + c(θ)w = H`.**

Writing `m(θ) = sin²θ cos³θ` (= `FamOde.wfn`), `c(θ) = 4cos2θ/sin2θ - tan θ = (log m)'`
(= `FamOde.coco`), the product `W := ∂_θu · m` satisfies `W' = m·H`, whence `W` is Lipschitz
with the dominating function `Φ = m·(A/sin 2θ + C)` (= `FamOde.phfn A C`).

The two endpoints `θ = 0`, `θ = π/2` are singular (`m ~ θ²`, resp. `m ~ (π/2-θ)³`) and the
boundedness `|u| ≤ K₀` is what pins `W` down there: it forces `W` to vanish at both endpoints,
and the mean-value anchors `FamOde.case_left`/`FamOde.case_right` turn this into
`|∂_θu| ≤ 2π²(K₀ + A/2 + Cπ/4)` on `(0, π/4]` and `≤ (π³/2)(K₀ + A/2 + Cπ/4)` on
`[π/4, π/2)`.  All constants are uniform in `z`. -/
theorem fam_ode_deriv_bound_proved {u H : ℝ → ℝ → ℝ} {K₀ A C : ℝ}
    (hK₀ : 0 ≤ K₀) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hu : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      DifferentiableAt ℝ (fun θ' => u z θ') θ)
    (hode : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      HasDerivAt (deriv (fun θ' => u z θ'))
        (H z θ - (4 * Real.cos (2 * θ) / Real.sin (2 * θ) - Real.tan θ)
          * deriv (fun θ' => u z θ') θ) θ)
    (hub : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → |u z θ| ≤ K₀)
    (hH : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |H z θ| ≤ A / Real.sin (2 * θ) + C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |deriv (fun θ' => u z θ') θ| ≤ K := by
  refine ⟨(2 * Real.pi ^ 2 + Real.pi ^ 3 / 2) * (K₀ + A / 2 + C * Real.pi / 4), ?_, ?_⟩
  · have h1 : 0 ≤ K₀ + A / 2 + C * Real.pi / 4 := by
      have h2 : 0 ≤ A / 2 := by linarith
      have h3 : 0 ≤ C * (Real.pi / 4) := mul_nonneg hC (by positivity)
      linarith
    have h2 : 0 ≤ 2 * Real.pi ^ 2 + Real.pi ^ 3 / 2 := by
      have h3 : 0 ≤ Real.pi ^ 3 / 2 := by positivity
      nlinarith [Real.pi_pos, sq_nonneg Real.pi]
    exact mul_nonneg h2 h1
  · intro z θ hzθ
    obtain ⟨hz, hθ0, hθ1⟩ := mem_Qd.mp hzθ
    set F : ℝ → ℝ := fun θ' => u z θ' with hF
    set Hz : ℝ → ℝ := H z with hHz
    have hmem : ∀ x ∈ Ioo (0 : ℝ) (Real.pi / 2), (z, x) ∈ Work.Construction.Qd :=
      fun x hx => ⟨hz, hx.1, hx.2⟩
    have huF : ∀ x ∈ Ioo (0 : ℝ) (Real.pi / 2), DifferentiableAt ℝ F x := by
      intro x hx
      have := hu z x (hmem x hx)
      simpa only [hF] using this
    have hubF : ∀ x ∈ Ioo (0 : ℝ) (Real.pi / 2), |F x| ≤ K₀ := by
      intro x hx
      have := hub z x (hmem x hx)
      simpa only [hF] using this
    have hodeF : ∀ x ∈ Ioo (0 : ℝ) (Real.pi / 2),
        HasDerivAt (deriv F) (Hz x - FamOde.coco x * deriv F x) x := by
      intro x hx
      have := hode z x (hmem x hx)
      simpa only [hF, hHz, FamOde.coco] using this
    have hHF : ∀ x ∈ Ioo (0 : ℝ) (Real.pi / 2),
        |Hz x| ≤ A / Real.sin (2 * x) + C := by
      intro x hx
      have := hH z x (hmem x hx)
      simpa only [hHz] using this
    have hMnn : 0 ≤ K₀ + A / 2 + C * Real.pi / 4 := by
      have h2 : 0 ≤ A / 2 := by linarith
      have h3 : 0 ≤ C * (Real.pi / 4) := mul_nonneg hC (by positivity)
      linarith
    have hbig : 2 * Real.pi ^ 2 ≤ 2 * Real.pi ^ 2 + Real.pi ^ 3 / 2 := by
      have h3 : 0 ≤ Real.pi ^ 3 / 2 := by positivity
      linarith
    suffices hgoal : |deriv F θ| ≤ (2 * Real.pi ^ 2 + Real.pi ^ 3 / 2)
        * (K₀ + A / 2 + C * Real.pi / 4) by
      simpa only [← hF] using hgoal
    by_cases hcase : θ ≤ Real.pi / 4
    · have hle := FamOde.case_left hK₀ hA hC huF hodeF hubF hHF hθ0 hcase
      have h2 := mul_le_mul_of_nonneg_right hbig hMnn
      linarith
    · have hcase' : Real.pi / 4 < θ := not_le.mp hcase
      have hle := FamOde.case_right hK₀ hA hC huF hodeF hubF hHF (le_of_lt hcase') hθ1
      have h2 : Real.pi ^ 3 / 2 ≤ 2 * Real.pi ^ 2 + Real.pi ^ 3 / 2 := by
        have h3 : 0 ≤ 2 * Real.pi ^ 2 := by positivity
        linarith
      have h3 := mul_le_mul_of_nonneg_right h2 hMnn
      linarith

end Work.FTS_StreamBdry.SB3.P2Aux
