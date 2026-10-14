import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.PggParts
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.VocabO
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.Spaces.sin_two_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Pgg` — the `gg`-row of the `L₁₂`-type estimate

The five `gg`-pieces `N₁^{gg}, …, N₅^{gg}` of the §8 nonlinearity are estimated in

  `E(f) = ∫⁻ r in Ioi 0, r⁻¹ · (∫⁻ θ in Iθ, |K(θ) · f r θ|)`,

each by a constant times `α^{p}·|g|_{ℋ⁴}²`, with `p = -1/2` for `N₁^{gg}`, `N₂^{gg}`,
`p = 1/2` for `N₃^{gg}` and `p = 0` for `N₄^{gg}`, `N₅^{gg}`.

Each piece is a product `A·B` of an elliptic coefficient (`Rop`, `Uop/sin2θ`, `Vop` of the
perturbation's stream function, or the angular moment `FK g`) and a slot (`g`, `D_θg`,
`D_zg`); the estimate is Cauchy–Schwarz in `θ` (`inner_lintegral_le`), the weighted
`H⁴`-energy bound for the slot (`Phi0/1/2_props`), and Cauchy–Schwarz in `r` with
`r⁻¹ = w^{1/2}/(1+r)` (`outer_of_inner`, `outer_of_inner_pair`).
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.rl1Pieces

set_option autoImplicit false
set_option linter.unusedVariables false

open Work.FTS.Galerkin (Fn)

theorem abs_sin_sq_le_one (θ : ℝ) : (Real.sin θ) ^ 2 ≤ 1 := Real.sin_sq_le_one θ


/-! ## The coefficient functions of the five pieces -/

/-- `A₁ = 2ℛ(Φ̃_g)`. -/
def A1 (α : ℝ) (g Φg : Fn) : ℝ → ℝ → ℝ :=
  fun z θ => 2 * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ

/-- `A₂ = -2U(Φ̃_g)/sin 2θ`. -/
def A2 (α : ℝ) (g Φg : Fn) : ℝ → ℝ → ℝ :=
  fun z θ => -2 * (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ
    / Work.Construction.s2 θ)

/-- `A₃ = -2α𝒱(Φ̃_g)`. -/
def A3 (α : ℝ) (g Φg : Fn) : ℝ → ℝ → ℝ :=
  fun z θ => -2 * α * Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg) z θ

/-- `A₄ = -(1/2)FK(g)`. -/
def A4 (g : Fn) : ℝ → ℝ → ℝ := fun z _ => -(1 / 2) * Work.Construction.FK g z

/-- `A₅ = -sin²θ·FK(g)`. -/
def A5 (g : Fn) : ℝ → ℝ → ℝ := fun z θ => -(Real.sin θ) ^ 2 * Work.Construction.FK g z






/-! ## The five piece estimates -/






/-! ## The constant and the theorem -/






end Work.FTS.Nonlinear.Pieces.rl1Pieces
