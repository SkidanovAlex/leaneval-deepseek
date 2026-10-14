import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.Coercivity.H4Assembly
import Submission.Work.FTS.CoercivityFix.Transfer.E2norm.A_sq_prod_le
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.Spaces.bt_prod_integrable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Stability

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! ## Abbreviations -/

/-- A function of the self-similar variables `(z,θ)`. -/
abbrev F2 := ℝ → ℝ → ℝ

/-- A family `(z,θ,s) ↦ ·` of functions of the self-similar variables, parametrised by the
self-similar time `s`. -/
abbrev F3 := ℝ → ℝ → ℝ → ℝ

/-- The `s`-slice of a family: `slice g s = g(·,·,s)`. -/
def slice (g : F3) (s : ℝ) : F2 := fun z θ => g z θ s

theorem slice_apply (g : F3) (s z θ : ℝ) : slice g s z θ = g z θ s := rfl

/-! ## The reference rates and the `(μ,λ) ↔ (κ,b)` dictionary -/

/-- The reference amplitude rate `κ* = 1+μ` (Construction's `1+μ`). -/
def kappaStar (μ : ℝ) : ℝ := 1 + μ

/-- The reference space-scale rate `b* = 1+λ` with the paper's `λ = -2μ/(1+μ)`
(`Work.Construction.lamfun`). -/
def bStar (μ : ℝ) : ℝ := 1 + Work.Construction.lamfun μ

theorem kappaStar_eq (μ : ℝ) : kappaStar μ = 1 + μ := rfl

theorem bStar_eq (μ : ℝ) : bStar μ = 1 - 2 * μ / (1 + μ) := by
  rw [bStar, Work.Construction.lamfun]; ring

/-- `b* = 1+λ` in the paper's `λ`-form. -/
theorem bStar_eq_lamfun (μ : ℝ) : bStar μ = 1 + Work.Construction.lamfun μ := rfl


/-- **The dictionary identity `κ*·b* = 1-μ`**, which is exactly the paper's choice
`μ + λ + μλ = -μ` (`hlam`): it is what makes the reference forcing collapse to `-2αμ·AK`
through `F_* - D_zF_* = 2α·AK`. -/
theorem kappaStar_mul_bStar (μ : ℝ) (hμ : 1 + μ ≠ 0) :
    kappaStar μ * bStar μ = 1 - μ := by
  rw [kappaStar_eq, bStar_eq]
  field_simp
  ring

/-! ## The modulation state -/

/-- **The modulation state**: the two *rates* `(κ,b)` of the self-similar rescaling, as
functions of the self-similar time `s`.  `κ` is the amplitude rate (the coefficient of `F` in
the rescaled vorticity equation) and `b` is the space-scale rate.  The amplitude and space
*scales* are recovered from the rates by `amp` and `space` below. -/
structure ModState where
  /-- the amplitude rate `κ(s)`. -/
  kappa : ℝ → ℝ
  /-- the space-scale rate `b(s)`. -/
  b : ℝ → ℝ

namespace ModState

variable (M : ModState)

/-- The **mismatch rate** `c₁(s) = 2(κ(s) - κ*)`: twice the deviation of the amplitude rate
from the reference `κ* = 1+μ`.  It plays the role of `2μ` of the stationary problem. -/
def c1 (μ : ℝ) (M : ModState) (s : ℝ) : ℝ := 2 * (M.kappa s - kappaStar μ)

/-- The **mismatch rate** `c₂(s) = 2(κ(s)b(s) - κ*b*)`: twice the deviation of the product of
the rates from the reference product.  It plays the role of `2(μ+λ+μλ)`. -/
def c2 (μ : ℝ) (M : ModState) (s : ℝ) : ℝ :=
  2 * (M.kappa s * M.b s - kappaStar μ * bStar μ)


theorem c2_apply (μ : ℝ) (s : ℝ) :
    M.c2 μ s = 2 * (M.kappa s * M.b s - kappaStar μ * bStar μ) := rfl








end ModState

/-! ## The scales recovered from the rates -/











/-! ## The rescaling maps -/

namespace ModState








end ModState



/-! ## The perturbation `g` -/

/-- The full profile `F = F_* + g` of the modulation. -/
def Ftot (α : ℝ) (g : F3) (s : ℝ) : F2 :=
  fun z θ => Work.Construction.Fstar α z θ + g z θ s






/-! ## The orthogonality conditions -/




/-! ## The dynamical rescaled vorticity equation -/




/-! ## The physical (self-similar) vorticity equation -/


namespace ModState




end ModState


/-! ## The `g`-equation -/

/-- The right hand side of the **dynamical `g`-equation**:
`-(κ-1)F_* - (κb-1)D_zF_* + AK·L₁₂(Transport g)(0) + N₀ + N + N_*`, evaluated at the slice `s`.
This is the exact right hand side produced by substituting `f = F_*+g` into `DynEq`; St2 proves
the identity and rewrites the forcing through `c₁, c₂`. -/
def gDynRHS (α : ℝ) (M : ModState) (g φ : F3) (z θ s : ℝ) : ℝ :=
  -(M.kappa s - 1) * Work.Construction.Fstar α z θ
    - (M.kappa s * M.b s - 1) * Work.Spaces.Dz (Work.Construction.Fstar α) z θ
    + Work.Construction.AK α z θ
        * Work.Construction.L12 (Work.Coercivity.Transport (slice g s)) 0
    + Work.Construction.N0 α (Ftot α g s) (slice g s) z θ
    + Work.Construction.N α (Ftot α g s) (slice φ s) z θ
    + Work.Construction.Nstar (M.kappa s - 1) (M.b s - 1) (slice g s) z θ


/-- The `g`-equation with an extra *far-field* term: the compactly supported solution does not
satisfy the rescaled equation in the far region, and the deficit is `Far`.  This is the equation
St2 derives and St3 bootstraps with; `Far` is the single named hypothesis of the layer (see
`NOTES.md`). -/
def GEquationFar (α : ℝ) (M : ModState) (g φ : F3) (Far : F3) : Prop :=
  ∀ z θ s, (z, θ) ∈ Work.Construction.Qd →
    M.kappa s * deriv (fun u => g z θ u) s
      + Work.Coercivity.LGammaT α (slice g s) z θ = gDynRHS α M g φ z θ s + Far z θ s




end Work.Stability
