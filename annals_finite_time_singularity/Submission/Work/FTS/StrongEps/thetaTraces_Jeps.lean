import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.PhiStar.ThetaTraces
import Submission.Work.FTS.StrongEps.thetaTraces_Jeps_proof

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `StrongEps.thetaTraces_Jeps` — θ-traces of the log-mollified profile (lead install R6, 2026-10-11)

`cbc/fts_ellnode_ruling.md` §4.4(6), review §3(b) and fix 5 (statement = the reviewer's
type-checked `C46Rev.thetaTraces_Jeps_stmt`).  Supplies the new `thTr` field of `SoftClass` in
`softClass_Jeps`, from the level-`7` uniform θ-trace hypotheses `ht0`/`ht1` that
`softClass_Jeps` already carries.

Intended proof [A]: `D_z = z∂_z` commutes with the log-`z` shift, so for `s ≤ 9`,
`D_z^s J_ε f = ∫ ∂_{p₁}^{s-7} ρ_ε · (D_z^7 f)∘shift` (at most two derivatives on the kernel;
reuse the `TenOfEight` machinery of `HkMem_Jeps_ten_of_eight`); under the log-tan θ-shift
`sin 2θ'/sin 2θ ∈ [e^{-2ε}, e^{2ε}]`, so the weight `sin^{1-γ}` transfers with a constant
(`sin_rpow_thShift_le`); conclude with `ht0`/`ht1` at `(a,b) = (0,7)` (and `(0,s)` for `s ≤ 7`).
-/

noncomputable section
open scoped Real Topology
open Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn)

/-- **θ-traces of `J_ε f` up to order `10`** from the uniform level-`7` θ-traces of `f`. -/
theorem thetaTraces_Jeps {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) {α : ℝ}
    (hα : α ∈ Set.Ioc 0 1) {ε : ℝ} (hε : 0 < ε) {f : Fn}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad)
    (ht0 : ∀ a b : ℕ, a + b ≤ 7 → ∀ ε' > 0, ∃ δ > 0, ∀ θ : ℝ, 0 < θ → θ < δ →
      ∀ z : ℝ, 0 < z →
        Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (Work.Spaces.mixed b a f z θ) ^ 2 ≤ ε')
    (ht1 : ∀ a b : ℕ, a + b ≤ 7 → ∀ ε' > 0, ∃ δ > 0, ∀ θ : ℝ, θ < π / 2 → π / 2 - δ < θ →
      ∀ z : ℝ, 0 < z →
        Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (Work.Spaces.mixed b a f z θ) ^ 2 ≤ ε') :
    Work.FTS.PhiStar.ThetaTraces α 10 (Jeps ρ ε f) :=
  thetaTraces_Jeps_proof (ρ := ρ) hρ (α := α) hα (ε := ε) hε (f := f) hsm ht0 ht1

end Work.FTS.StrongEps
