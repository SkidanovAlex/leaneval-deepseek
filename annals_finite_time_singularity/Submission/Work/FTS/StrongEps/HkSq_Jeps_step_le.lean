import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.StepFacts.AssemblyStep

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps

/-- **One-order smoothing of `J_ε` at the price of `ε⁻²`** (the regularising property of the
log-coordinate mollifier, in the paper's weighted norm `HkSq`).

For `2 ≤ m ≤ 8`, a profile `u` smooth on the open quadrant with `HkMem α (m-1) u` has
`HkMem α m (J_ε u)` and `HkSq α m (J_ε u) ≤ C (ε⁻¹)² HkSq α (m-1) u`, with `C` absolute.

*Proof route.*  Per slot: for `(j,i)` with `i + j = m`,
* if `j ≥ 1`: route exactly *one* `z`-derivative onto the kernel,
  `D_z^jD_θ^i (J_ε u) = ∫ (∂_{p₁}Jker)(p) · (D_z^{j-1}D_θ^i u)(shift) dp`, leaving the order-`m-1`
  slot `(j-1,i)` of `u` (same weight type: the `η`-weight if `i = 0`, the `Wt`-weight if `i ≥ 1`);
* if `j = 0`, `i ≥ 2`: route exactly *one* `θ`-derivative,
  `D_θ^i (J_ε u) = 2 ∫ (∂_{p₂}Jker)(p) · (D_θ^{i-1}u)(shift) dp`, leaving `(0,i-1)`, `i-1 ≥ 1`
  (the `Wt`-weight on both sides);
* the only slot with `j = 0`, `i = 1` occurs at `m = 1` and is excluded by `m ≥ 2`; at `m = 2` the
  slots are `(2,0)`, `(1,1)` and `(0,2)`, all covered by the two rules above.

Each routed derivative costs `ε⁻¹` twice: once in `(∫|∂Jker|)^{1/2}` (since
`∫|∂_{p₁}Jker| = ε⁻¹∫|∂_{p₁}ρ|`) and once in `∫ |∂Jker| e^{c|p|} dp` after the change of
variables; the *unrouted* slots are Jensen with the probability kernel (`∫ Jker = 1`, no `ε`).
Then Jensen/`slot_sq_bound`, the two shift comparisons of the `HkIntegrand` weights
(`wdiv_shift_le`, `Wt_shift_le`), the log-coordinate Jacobian (`logJac_shift_le`) and
`HkIntegrand_mono`-type monotonicity `HkSq α 1 ≤ HkSq α (m-1)` finish it -- the *same* chain as
the proved `HkSqAux/HkIntegrand_Jeps_le_integral`.  The per-slot identity is
`mixed_Jeps_kernel_partial` with `(j',i') = (j-1,i)` resp. `(0,i-1)`.

Do **not** state this with `HkSq α 0` on the right, nor for `m = 1`: every `Wt`-weighted slot can
only be routed onto a leftover of `u` that still carries a `θ`-derivative (the `ℋ⁰`-version is
false: a profile oscillating in `θ` at frequency `≫ 1/ε` has
`HkSq α 1 (J_ε u) / HkSq α 0 u → ∞`). -/
theorem HkSq_Jeps_step_le (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), α ∈ Set.Ioc 0 1 → ∀ (m : ℕ), 2 ≤ m → m ≤ 8 →
      ∀ (ε : ℝ), ε ∈ Set.Ioc 0 1 → ∀ u : Work.FTS.Galerkin.Fn,
        (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) Work.FTS.StrongEps.Quad) →
        Work.Spaces.HkMem α (m - 1) u →
        Work.Spaces.HkMem α m (Work.FTS.StrongEps.Jeps ρ ε u) ∧
          Work.Spaces.HkSq α m (Work.FTS.StrongEps.Jeps ρ ε u)
            ≤ C * (ε⁻¹) ^ 2 * Work.Spaces.HkSq α (m - 1) u :=
  Work.FTS.StrongEps.StepFacts.step_le_aux ρ hρ

end Work.FTS.StrongEps
