/-
# `Work.FTS.PhiStar.Psi0Est.WlInf_psiSol` — `∂_θθψ ∈ 𝒲^{5,∞}` for the model `ψ`

For the explicit model `ψ = psiSol α` (`Psi0Ode.lean`) we prove that
`θ ↦ ∂_θθψ(θ)`, viewed as a function `(z,θ) ↦ ∂_θθψ(θ)` of the self-similar variables,
belongs to `𝒲^{5,∞}` with norm at most `6C`, whenever

* `|∂_θθψ(θ)| ≤ C` for `θ ∈ (0,π/2)`, and
* `|D_θ^j(∂_θθψ)(θ)|·sin(2θ)^{-α/5}/(α + sin 2θ) ≤ C` for `θ ∈ (0,π/2)`, `1 ≤ j ≤ 5`.

## The reduction

`F : (z,θ) ↦ g θ` with `g θ = ∂_θθψ(θ)` is independent of `z`, so `pzIter k F = 0` for
`k ≥ 1` and `DthIter j F = fun _ θ => dthU^[j] g θ`; the norm therefore collapses to
`⟨|g|⟩_{Iθ}` (the radial slot `k = 0`) plus the five angular slots `k = 0`, `1 ≤ j ≤ 5`,
each of which is bounded by `C`.  Total: `C + 5C = 6C`.

## The two endpoints

`WlInf` uses the suprema over the *closed* interval `Iθ = [0,π/2]` while the hypotheses only
control the *open* interval `(0,π/2)`.

* For `j ≥ 1`, `dthU^[j] g` vanishes at both endpoints (`dthU_apply_zero`,
  `dthU_apply_pi_half` and their iterates), so the five angular slots are `0 ≤ C` there.
* The radial slot needs `g 0 = g (π/2) = 0`, i.e. `∂_θθψ` vanishes at the endpoints.

The latter is the content of the file.  Because the totalised `deriv` of a non-differentiable
function returns the junk value `0`, it suffices to know that `(deriv (deriv ψ)) θ` at an
endpoint is either zero or the honest second derivative, and that the honest second
derivative vanishes there.  Both endpoints are treated the same way:

* `deriv ψ =ᶠ[𝓝 θ] M1 α` (`deriv_psiSol_eventuallyEq_M1`): the explicit formula for `ψ'`,
  which holds in a punctured neighbourhood by the product rule plus
  `HasDerivAt wZer (qfun α θ) θ`, and at the endpoint by the product rule with the
  coefficient of `qfun` being `sin(2θ) = 0`;
* `HasDerivAt (M1 α) 0 θ` (`hasDerivAt_M1_endpoints`), where the only input is
  `qfun α → 0` at the endpoint (`qfun_tendsto_endpoints_alt`, proved from the two
  `Gzero_rpow_*` power estimates; the sibling `qfun_tendsto_endpoints` states the same
  thing under the originally requested name).

Hence `iteratedDeriv 2 (psiSol α) 0 = 0` and `iteratedDeriv 2 (psiSol α) (π/2) = 0`.
-/
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.PhiStar.Psi0Est.Defs
import Submission.Work.FTS.PhiStar.Psi0Est.WlInf_theta_only_six
import Submission.Work.FTS.PhiStar.Psi0Est.qfun_tendsto_endpoints_alt
import Submission.Work.FTS.PhiStar.Psi0Est.deriv_psiSol_eventuallyEq_M1
import Submission.Work.FTS.PhiStar.Psi0Est.hasDerivAt_M1_endpoints

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Psi0Est

set_option autoImplicit false

/-! ## The value of `∂_θθψ` at the two endpoints -/

theorem iteratedDeriv_two_psiSol_zero (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    iteratedDeriv 2 (psiSol α) 0 = 0 := by
  obtain ⟨hq0, hqπ⟩ := qfun_tendsto_endpoints_alt α hα hα1
  have heq := (deriv_psiSol_eventuallyEq_M1 α hα hα1 hq0 hqπ).1
  have hder := (hasDerivAt_M1_endpoints α hα hα1 hq0 hqπ).1
  have h := HasDerivAt.congr_of_eventuallyEq hder heq
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_succ,
    iteratedDeriv_zero]
  exact h.deriv

theorem iteratedDeriv_two_psiSol_pi_div_two (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    iteratedDeriv 2 (psiSol α) (Real.pi / 2) = 0 := by
  obtain ⟨hq0, hqπ⟩ := qfun_tendsto_endpoints_alt α hα hα1
  have heq := (deriv_psiSol_eventuallyEq_M1 α hα hα1 hq0 hqπ).2
  have hder := (hasDerivAt_M1_endpoints α hα hα1 hq0 hqπ).2
  have h := HasDerivAt.congr_of_eventuallyEq hder heq
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_succ,
    iteratedDeriv_zero]
  exact h.deriv

/-! ## The target -/

theorem WlInf_psiSol (C : ℝ) (hC : 0 < C) :
    ∀ α : ℝ, 0 < α → α ≤ 1 / 4 →
    (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |iteratedDeriv 2 (psiSol α) θ| ≤ C) →
    (∀ j : ℕ, 1 ≤ j → j ≤ 5 → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Spaces.dthU^[j] (fun θ' : ℝ => iteratedDeriv 2 (psiSol α) θ') θ|
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)) ≤ C) →
    Work.Spaces.WlInfMem α 5 (fun _ θ => iteratedDeriv 2 (psiSol α) θ) ∧
    Work.Spaces.WlInf α 5 (fun _ θ => iteratedDeriv 2 (psiSol α) θ) ≤ 6 * C := by
  intro α hα hα14 h1 h2
  refine WlInf_theta_only_six α C hα hC (fun θ => iteratedDeriv 2 (psiSol α) θ) ?_ ?_
  · intro θ hθ
    rcases eq_or_lt_of_le hθ.1 with h | h
    · rw [← h, iteratedDeriv_two_psiSol_zero α hα hα14, abs_zero]
      exact le_of_lt hC
    rcases eq_or_lt_of_le hθ.2 with h2' | h2'
    · rw [h2', iteratedDeriv_two_psiSol_pi_div_two α hα hα14, abs_zero]
      exact le_of_lt hC
    · exact h1 θ ⟨h, h2'⟩
  · intro j hj1 hj5 θ hθ
    rcases eq_or_lt_of_le hθ.1 with h | h
    · rw [← h, dthU_iter_apply_zero (fun θ' => iteratedDeriv 2 (psiSol α) θ') hj1]
      simp only [abs_zero, zero_mul, zero_div]
      exact le_of_lt hC
    rcases eq_or_lt_of_le hθ.2 with h2' | h2'
    · rw [h2', dthU_iter_apply_pi_half (fun θ' => iteratedDeriv 2 (psiSol α) θ') hj1]
      simp only [abs_zero, zero_mul, zero_div]
      exact le_of_lt hC
    · exact h2 j hj1 hj5 θ ⟨h, h2'⟩


end Work.FTS.PhiStar.Psi0Est
