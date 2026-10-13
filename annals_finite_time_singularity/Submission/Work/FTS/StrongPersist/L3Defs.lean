/-
# `Work.FTS.StrongPersist.L3Defs` — the decomposition of `linPart` into its pieces

This module fixes the vocabulary in which the level-three estimate `L3_lin_mem` is proved.
The linear part

  `linPart α f = -𝓛_Γ^T f = -(𝓛 f) + 𝓐(α)·L₁₂(f) + Transport f - 𝓑(α)·L₁₂(Transport f)(0)`

is split into three functions of `(z,θ)`:

* `locOp f = -(𝓛 f) + Transport f` — the *local* first-order part (products of `f`'s
  `D`-derivatives with the smooth bounded coefficients `1`, `1`, `1/(1+z)`);
* `fun z θ => Acoef α z θ * Mf f z θ` — the *nonlocal* term, the product of the
  `(z,θ)`-separated coefficient `Acoef α = acoef(z)·gamCoef(α,θ)` with the *radial* function
  `Mf f = L₁₂(f)` (extended constantly in `θ`);
* `fun z θ => Bcoef α z θ * K0f f` — the projector correction, the product of the
  `(z,θ)`-separated coefficient `Bcoef α = gamCoef(α,θ)·bcoef(z)` with the *constant*
  `K0f f = L₁₂(Transport f)(0)`.

`linPart_eq` records the resulting identity; the two separations are `Acoef_eq_mul` and
`Bcoef_eq_mul`.  Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.StrongPersist.Dbd
import Submission.Work.FTS.OpenPkg.l12H_field
import Submission.Work.FTS.GalBasis.hk_sq_api
import Submission.Work.FTS.EllipticEst.HkNorm_add_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

open Work.FTS.Galerkin (Fn)
open Work.Spaces (HkMem HkSq HkNorm Dz Dth mixed pth pzIter DthIter DzIter)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The three pieces -/

/-- The angular half `Γ(θ)/c(α)` of the two `(z,θ)`-separated coefficients. -/
def gamCoef (α : ℝ) (θ : ℝ) : ℝ := Work.Spaces.Gam α θ / Work.Spaces.c α

/-- The radial half `2z/(1+z)²` of the nonlocal coefficient. -/
def acoef (z : ℝ) : ℝ := 2 * z / (1 + z) ^ 2

/-- The radial half `2z²/(1+z)³` of the projector coefficient. -/
def bcoef (z : ℝ) : ℝ := 2 * z ^ 2 / (1 + z) ^ 3

/-- The coefficient `2zΓ(θ)/(c(α)(1+z)²)` of the nonlocal term of `𝓛_Γ`, verbatim as it
appears in `Work.Coercivity.LGamma`. -/
def Acoef (α : ℝ) (z θ : ℝ) : ℝ :=
  2 * z * Work.Spaces.Gam α θ / (Work.Spaces.c α * (1 + z) ^ 2)

/-- The coefficient `(Γ(θ)/c(α))·2z²/(1+z)³` of the projector `𝕡`, verbatim as it appears in
`Work.Coercivity.Proj`. -/
def Bcoef (α : ℝ) (z θ : ℝ) : ℝ :=
  (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3)

/-- The radial function `L₁₂(f)`, extended constantly in `θ`. -/
def Mf (f : Fn) : Fn := fun z _ => Work.Coercivity.L12f f z

/-- The projector constant `L₁₂(Transport f)(0)`. -/
def K0f (f : Fn) : ℝ := Work.Coercivity.L12f (Work.Coercivity.Transport f) 0

/-- The local part `-(𝓛 f) + Transport f` of `linPart`. -/
def locOp (f : Fn) : Fn :=
  fun z θ => -(Work.Coercivity.L f z θ) + Work.Coercivity.Transport f z θ

/-! ## Identifications -/

/-- `Mf f` is the `Coercivity` tail integral `L12f f`, extended constantly in `θ`. -/
theorem Mf_eq_L12f (f : Fn) :
    Mf f = fun z _ => Work.Coercivity.L12f f z := rfl

/-- `Mf f` is the `Construction` tail integral `L12 f`, extended constantly in `θ`. -/
theorem Mf_eq_L12 (f : Fn) :
    Mf f = fun z _ => Work.Construction.L12 f z := rfl

/-- `K0f f` is the `Construction` value `L12 (Transport f) 0`. -/
theorem K0f_eq_L12 (f : Fn) :
    K0f f = Work.Construction.L12 (Work.Coercivity.Transport f) 0 := rfl

/-- **The nonlocal coefficient is `(z,θ)`-separated** (for every `z`, not only `z ≥ 0`). -/
theorem Acoef_eq_mul (α : ℝ) (z θ : ℝ) : Acoef α z θ = acoef z * gamCoef α θ := by
  rw [Acoef, gamCoef, acoef]
  rcases eq_or_ne (1 + z) 0 with h | h
  · simp [h]
  · field_simp

/-- **The projector coefficient is `(z,θ)`-separated.** -/
theorem Bcoef_eq_mul (α : ℝ) (z θ : ℝ) : Bcoef α z θ = gamCoef α θ * bcoef z := rfl

/-! ## The decomposition -/

/-- **The decomposition of `linPart` into its three pieces.**  This is a purely algebraic
identity (no hypothesis on `f`): `linPart α f = locOp f + Acoef α · Mf f - Bcoef α · K0f f`. -/
theorem linPart_eq (α : ℝ) (f : Fn) :
    linPart α f
      = fun z θ => locOp f z θ + Acoef α z θ * Mf f z θ - Bcoef α z θ * K0f f := by
  funext z θ
  simp only [linPart, Work.Coercivity.LGammaT, Work.Coercivity.LGamma, Work.Coercivity.Proj,
    Work.Coercivity.Transport, locOp, Mf, K0f, Acoef, Bcoef]
  ring

end Work.FTS.StrongPersist
