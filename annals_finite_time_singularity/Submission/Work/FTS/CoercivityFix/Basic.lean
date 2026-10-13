/-
# `Work.FTS.CoercivityFix` — the corrected coercivity of `𝓛_Γ^T` (fix of node N2)

This directory owns the **fix of node N2** of the route: the coercive inner product
obligation `Work.FTS.Nonlin.UnifIP` (frozen vocabulary, `Submission/Work/FTS/Vocab.lean`)
for the **concrete `IP4` of `Submission/Work/FTS/CoercivityStep`**, corrected as the lead's
design `Submission/Work/FTS/N45_DESIGN_LEAD.md` §5 demands.

## What is corrected, and why

The delivered node N2 proves

  `cc₁ · |g|²_{ℋⁿ} ≤ IP_n (𝓛_Γ^T g) g`   for `g ∈ HkAdm α n`,

where `HkAdm` (a) forces **analyticity** (`Spaces.SmoothNbhd = ContDiffOn ℝ ⊤`, the
analytic order), and (b) requires *all fifteen* mixed `L₁₂`-zero modes
`L₁₂(D_z^b D_θ^a g)(0) = 0` — a class the flow does not preserve (design §5 T2).  It also
runs the induction with the *unit* step coefficients and the **balance hypothesis**
`CC√κ ≤ cc/2` (design §5 T3), which is not satisfiable for the concrete constants.

The fix implemented here has three parts.

1. **The class.**  Everything is restated on the interior class
   `LocData.SmoothQuad` (genuine `C^∞` on the open quadrant) + `Spaces.HkMem` + the
   boundary traces — the frozen `RegQ`/`CoerAdm` of `Vocab.lean`.  Only the *one*
   condition `L₁₂(f)(0) = 0` is imposed on the coercivity class `CoerAdm`.

2. **The clean operator `Lhat = 𝓛 − Transport`.**  The obstruction in the paper's induction
   is that `D_θ` of the *nonlocal* term `(2zΓ/(c(1+z)²))L₁₂(f)` produces
   `(2zΓ/(c(1+z)²))L₁₂(D_θ f)`, which is *not* in `ℋⁿ` unless `L₁₂(D_θf)(0) = 0` — and
   `D_θ` does not preserve that condition.  Splitting `𝓛_Γ^T = Lhat + Corr` removes the
   obstruction exactly:

   * `D_θ (Lhat f) = Lhat (D_θ f)` — **no commutator at all** (`Dth_Lhat`);
   * `D_z (Lhat f) = Lhat (D_z f) + E2hat f` with the **explicit** defect
     `E2hat f = (2zf + 3z·D_θf)/(1+z)²`, bounded by `(2|f| + 3|D_θf|)/4` pointwise
     (`E2hat_abs_le`).  There is *no* `L₁₂`-term in the defect, so its `ℋⁿ`-norm satisfies
     `|E2hat f|_n ≤ κ(|f|_n + |D_θ f|_n)` with an absolute constant `κ` — provable by slot
     bookkeeping, and **uniform in α**.

3. **The step with the paper's small coefficients.**  Running the induction for `Lhat`
   (whose `D_θ`-commutator vanishes) with the *small* step coefficients
   `c_{1,n}`, `c_{2,n}` of the paper replaces the unsatisfiable balance `CC√κ ≤ cc/2` by
   the *coefficient smallness* `c₂·(CC·κ)² ≤ cc²/4` (`StepSmallCoeff`), which is
   satisfiable for every level by taking `c₂` small — see `Step.lean`.

The relation `𝓛_Γ^T f = Lhat f + Corr α f` with `Corr` explicit (`Corr_eq`) is what
transfers the `Lhat`-coercivity back to the frozen `UnifIP.coer` clause, on `CoerAdm`
(where `L₁₂(f)(0) = 0` makes `Corr` honest).

## Conventions

`Fn = ℝ → ℝ → ℝ` (`Work.FTS.Galerkin.Fn`), curried, applied as `f z θ`; all integrals are
over `Iz × Iθ = [0,∞) × [0,π/2]` with the measure `dz dθ`.  Nothing in this directory
redefines a frozen name: `Lhat`, `E2hat`, `Corr`, `IP1`, `IPcf` are new.
-/
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.FTS.Vocab

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## The clean operator and its defects -/

/-- **The clean operator** `𝓛̂ = 𝓛 − Transport`: the paper's `𝓛` with the angular-transport
term subtracted and **no nonlocal term**.  It is the operator whose coercivity the modified
induction propagates: `D_θ` commutes with it *exactly*, and its `D_z`-commutator is the
explicit bounded function `E2hat`. -/
def Lhat (f : Fn) : Fn := Work.Coercivity.L f - Work.Coercivity.Transport f

/-- Unfolded: `𝓛̂f = f + D_z f − 2f/(1+z) − 3 D_θ f/(1+z)`. -/
theorem Lhat_eq (f : Fn) (z θ : ℝ) :
    Lhat f z θ = f z θ + Work.Spaces.Dz f z θ - 2 * f z θ / (1 + z)
      - 3 * Work.Spaces.Dth f z θ / (1 + z) := by
  simp only [Lhat, Pi.sub_apply, Work.Coercivity.L, Work.Coercivity.Transport]

/-- **The `D_z`-commutator defect of `Lhat`**, explicitly:
`Ê₂ f = (2zf + 3z·D_θf)/(1+z)²`.  Compare with the paper's `E₂`, which contains the
nonlocal pieces `D_z[(2zΓ/(c(1+z)²))L₁₂ f]`; here they are absent, which is why this
defect is bounded by `(|f| + |D_θ f|)` with absolute constants and *uniformly in α*. -/
def E2hat (f : Fn) : Fn := fun z θ =>
  (2 * z * f z θ + 3 * z * Work.Spaces.Dth f z θ) / (1 + z) ^ 2

/-- Unfolded `E2hat`. -/
theorem E2hat_eq (f : Fn) (z θ : ℝ) :
    E2hat f z θ = (2 * z * f z θ + 3 * z * Work.Spaces.Dth f z θ) / (1 + z) ^ 2 := rfl

/-- **The pointwise bound on the `D_z`-defect**: on `z ≥ 0`, `|Ê₂ f| ≤ (2|f| + 3|D_θ f|)/4`.
This is the only estimate the induction needs about the defect, and it carries no `α`. -/
theorem E2hat_abs_le (f : Fn) {z θ : ℝ} (hz : 0 ≤ z) :
    |E2hat f z θ| ≤ (2 * |f z θ| + 3 * |Work.Spaces.Dth f z θ|) / 4 := by
  rw [E2hat_eq]
  have hden : 0 < (1 + z) ^ 2 := by positivity
  have hzle : z / (1 + z) ^ 2 ≤ 1 / 4 := by
    rw [div_le_iff₀ hden]; nlinarith [sq_nonneg (1 - z)]
  have hnum : |2 * z * f z θ + 3 * z * Work.Spaces.Dth f z θ|
      ≤ (2 * |f z θ| + 3 * |Work.Spaces.Dth f z θ|) * z := by
    calc |2 * z * f z θ + 3 * z * Work.Spaces.Dth f z θ|
        ≤ |2 * z * f z θ| + |3 * z * Work.Spaces.Dth f z θ| := abs_add_le _ _
      _ = 2 * z * |f z θ| + 3 * z * |Work.Spaces.Dth f z θ| := by
          rw [abs_mul, abs_mul, abs_mul, abs_mul,
            abs_of_nonneg (show (0:ℝ) ≤ 2 by norm_num), abs_of_nonneg hz,
            abs_of_nonneg (show (0:ℝ) ≤ 3 by norm_num)]
      _ ≤ (2 * |f z θ| + 3 * |Work.Spaces.Dth f z θ|) * z := le_of_eq (by ring)
  have hZ : 0 ≤ z / (1 + z) ^ 2 := div_nonneg hz hden.le
  calc |(2 * z * f z θ + 3 * z * Work.Spaces.Dth f z θ) / (1 + z) ^ 2|
      = |2 * z * f z θ + 3 * z * Work.Spaces.Dth f z θ| / (1 + z) ^ 2 := by
        rw [abs_div, abs_of_pos hden]
    _ ≤ ((2 * |f z θ| + 3 * |Work.Spaces.Dth f z θ|) * z) / (1 + z) ^ 2 :=
        div_le_div_of_nonneg_right hnum hden.le
    _ = (2 * |f z θ| + 3 * |Work.Spaces.Dth f z θ|) * (z / (1 + z) ^ 2) := by ring
    _ ≤ (2 * |f z θ| + 3 * |Work.Spaces.Dth f z θ|) * (1 / 4) :=
        mul_le_mul_of_nonneg_left hzle (by positivity)
    _ = (2 * |f z θ| + 3 * |Work.Spaces.Dth f z θ|) / 4 := by ring

/-- **The transfer defect** `𝓛_Γ^T f − 𝓛̂f`: everything in `𝓛_Γ^T` that is not in `𝓛̂`,
i.e. the nonlocal term `−(2zΓ/(c(1+z)²))L₁₂ f` and the projector correction
`(Γ/c)(2z²/(1+z)³)L₁₂(Transport f)(0)` (the `Proj`-part of `𝓛_Γ^T`). -/
def Corr (α : ℝ) (f : Fn) : Fn := Work.Coercivity.LGammaT α f - Lhat f

/-- Unfolded `Corr`. -/
theorem Corr_eq (α : ℝ) (f : Fn) (z θ : ℝ) :
    Corr α f z θ = -(2 * z * Work.Spaces.Gam α θ / (Work.Spaces.c α * (1 + z) ^ 2))
        * Work.Coercivity.L12f f z
      + (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3)
        * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 := by
  simp only [Corr, Pi.sub_apply, Lhat_eq, Work.Coercivity.LGammaT, Work.Coercivity.LGamma,
    Work.Coercivity.Proj, Work.Coercivity.L, Work.Coercivity.Transport]
  ring

/-- **The decomposition of the paper's operator**: `𝓛_Γ^T = 𝓛̂ + Corr`. -/
theorem LGammaT_eq_Lhat_add_Corr (α : ℝ) (f : Fn) :
    Work.Coercivity.LGammaT α f = Lhat f + Corr α f := by
  funext z θ
  simp only [Pi.add_apply, Corr, Pi.sub_apply]
  ring

/-! ## The concrete inner products -/

/-- The level-1 inner product: the paper's `ℋ¹` inner product `H1IP` (four slots, with the
coefficients `10, 10¹⁰, 10¹⁷, 10²¹`). -/
def IP1 (α : ℝ) : Fn → Fn → ℝ := Work.Coercivity.H1IP α

/-- The paper's recursion, one step, with *explicit* step coefficients. -/
def step (c₁ c₂ : ℝ) (IP : Fn → Fn → ℝ) : Fn → Fn → ℝ :=
  Work.Coercivity.HkIPStep c₁ c₂ IP

end Work.FTS.CoercivityFix
