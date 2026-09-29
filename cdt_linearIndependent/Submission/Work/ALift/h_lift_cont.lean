import Mathlib
import Submission.CDTPlan.InterfacesA2
import Submission.Work.ALift.defs
import Submission.Work.ALift.Phi_avoid
import Submission.Work.ALift.sys_diff_A
import Submission.Work.ALift.Y0_solves_A
import Submission.Work.ALift.Phi_small
import Submission.Work.ALift.summable_norm_HU

/-!
# Area ALift — continuation of `H` along a lift of `φ_A` (`HLiftContA`)

Theorem A's function `H = a H_A + b H_B + c H_C` is holonomic: it satisfies Zagier's order-2
operator `P·H'' + Q·H' + R·H = b + c/(1-x)` with `P = x(1-x)(1-9x)`, `Q = 1-20x+27x²`,
`R = -3+9x` (`HZ_odeLHS`), and under the absurd relation `ARel a b c` its coefficients
overconverge to radius `1` (`coef_bound_A`), so `H` defines an analytic function `U₀` on the unit
disc with derivatives `U₁, U₂` up to `‖q‖ < 10/11`.

Given a lift `Φ` of `φ_A = h ∘ ψ_A` (i.e. `Φ z + Φ(-z) = Φ z · Φ(-z) = phiA (z²)`), the pullback of
Zagier's operator is the first-order system `Y' = sysA Φ z · Y + sysb b c Φ z` for
`Y = (U₀ ∘ Φ, U₁ ∘ Φ)`.  On the annulus `1/31 < ‖z‖ < 1` the map `Φ` avoids the singularities
`0, 1, 1/9` of the operator (`Phi_avoid`, using the certified numerics `ANumerics` for `1/9`), so
the system is holomorphic there (`sys_diff_A`); on the disc `‖z‖ < 1/25` the lift is bounded by
`9/10` (`Phi_small`), so `Y₀ = (U₀ ∘ Φ, U₁ ∘ Φ)` solves the system there (`Y0_solves_A`).
`OdeContinuation` then extends `Y₀` to the whole unit disc, and its first component is the
continuation `F` of the germ `Σ_k h_k Φ(z)^k` of `H ∘ Φ`.
-/

namespace Work.ALift

open Submission.CDTPlan Complex Metric

theorem h_lift_cont (hK : OdeContinuation) (hN : ANumerics) (hM : HauptFacts) (hP : PsiAFacts) : HLiftContA := by
  intro a b c hRel Φ hL
  -- `Φ` is bounded by `9/10` on the disc `‖z‖ < 1/25`
  have hsmall : ∀ z : ℂ, ‖z‖ ≤ rA1 → ‖Φ z‖ ≤ 9 / 10 := by
    intro z hz
    have hz' : ‖z‖ ≤ 1 / 25 := hz
    exact Phi_small hP Φ hL z hz'
  -- the pulled-back system is holomorphic on the annulus
  have hsys : DifferentiableOn ℂ (sysA Φ) {z : ℂ | rA0 < ‖z‖ ∧ ‖z‖ < 1} ∧
      DifferentiableOn ℂ (sysb b c Φ) {z : ℂ | rA0 < ‖z‖ ∧ ‖z‖ < 1} := by
    have h := sys_diff_A b c Φ hL.1 (Phi_avoid hN Φ hL)
    exact h
  -- the initial solution on the small disc
  obtain ⟨hY0diff, hY0ode⟩ := Y0_solves_A a b c hRel hN Φ hL hsmall
  -- continue it to the unit disc
  obtain ⟨Y, hYdiff, hYeq⟩ := hK 2 (sysA Φ) (sysb b c Φ) rA0 rA1 (Y0v a b c Φ)
    rA0_pos rA0_lt_rA1 rA1_le_one hsys.1 hsys.2 hY0diff hY0ode
  refine ⟨fun z => Y z 0, ?_, ?_⟩
  · have hproj : DifferentiableOn ℂ (fun v : Fin 2 → ℂ => v 0) Set.univ :=
      (differentiable_apply (𝕜 := ℂ) (0 : Fin 2)).differentiableOn
    have : (fun z => Y z 0) = (fun v : Fin 2 → ℂ => v 0) ∘ Y := rfl
    rw [this]
    exact hproj.comp hYdiff (fun z _ => Set.mem_univ _)
  · filter_upwards [Metric.ball_mem_nhds (0 : ℂ) rA1_pos] with z hz
    have hz' : ‖z‖ < 1 / 25 := by
      rw [mem_ball, dist_zero_right] at hz
      exact hz
    have hq : ‖Φ z‖ ≤ 9 / 10 := hsmall z (le_of_lt hz')
    have hsum : Summable (fun k : ℕ => hcoef a b c k * (Φ z) ^ k) :=
      (summable_norm_HU a b c hRel (Φ z) hq).1.of_norm
    have hval : Y z 0 = ∑' k : ℕ, hcoef a b c k * (Φ z) ^ k := by
      rw [hYeq hz, Y0v_0, HU0]
    rw [hval]
    exact hsum.hasSum

end Work.ALift
