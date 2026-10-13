/-
# Auxiliary definitions for the `D_z`-commutator estimate for `𝓛_Γ^T`

This file collects the objects used by the proof of `Work.Coercivity.CommutZ_holds`:
the defect `E₂ = D_z 𝓛_Γ^T f - 𝓛_Γ^T(D_z f)` of the `D_z`-commutator, its explicit
expansion as a sum of a "z-multiplier times `f`" term, a "z-multiplier times `D_θ f`"
term, and a term `(Γ(θ)/c)·G(z)` with `G` a function of `z` built out of the
`L₁₂`-quantities, plus the one-variable version of the iterated operator `D_z = z∂_z`
and the `θ`-average `Kav`.

Nothing analytic is proved here; the statements proved in the companion files are
phrased in these terms.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Basic
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity.CommutZ

open Work.Coercivity Work.Spaces

set_option autoImplicit false

/-! ## `z`-only multiplier functions -/

/-- A function of `z` alone, viewed as a function of `(z,θ)`. -/
def mulZ (m : ℝ → ℝ) : ℝ → ℝ → ℝ := fun z _ => m z

@[simp] theorem mulZ_apply (m : ℝ → ℝ) (z θ : ℝ) : mulZ m z θ = m z := rfl

theorem mulZ_inj {m m' : ℝ → ℝ} (h : mulZ m = mulZ m') : m = m' := by
  funext z; have := congrFun (congrFun h z) 0; simpa using this

/-- The one-variable version of the iterated operator `D_z = z ∂_z`. -/
def DzIterZ : ℕ → (ℝ → ℝ) → (ℝ → ℝ)
  | 0, m => m
  | n + 1, m => fun z => z * deriv (DzIterZ n m) z

@[simp] theorem DzIterZ_zero (m : ℝ → ℝ) : DzIterZ 0 m = m := rfl

theorem DzIterZ_succ (n : ℕ) (m : ℝ → ℝ) :
    DzIterZ (n + 1) m = fun z => z * deriv (DzIterZ n m) z := rfl

/-- The iterated `D_z` applied to a `z`-only multiplier agrees with the one-variable
version. -/
theorem DzIter_mulZ (j : ℕ) (m : ℝ → ℝ) : DzIter j (mulZ m) = mulZ (DzIterZ j m) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [DzIter_succ, ih]
      funext z θ
      simp only [Dz, mulZ, DzIterZ_succ]
      congr 1

/-! ## The `K`-average -/

/-- The `K`-average in `θ` of a function of `(z,θ)`: `∫_θ K(θ) g(z,θ)`. -/
def Kav (g : ℝ → ℝ → ℝ) (z : ℝ) : ℝ := ∫ θ in Iθ, K θ * g z θ

/-! ## The explicit profiles -/

/-- The multiplier `2z/(1+z)²` of the commutator (it is the profile `F_*`). -/
def mm (z : ℝ) : ℝ := 2 * z / (1 + z) ^ 2

/-- `q(z) = 2z²/(1+z)³`, the `z`-profile of the projector correction. -/
def qfun (z : ℝ) : ℝ := 2 * z ^ 2 / (1 + z) ^ 3

/-- `z q'(z)` for `q(z) = 2z²/(1+z)³`. -/
def zdq (z : ℝ) : ℝ := 2 * z ^ 2 * (2 - z) / (1 + z) ^ 4

/-- The coefficient of `L₁₂(f)` in the `D_z`-commutator: `-2z(1-z)/(1+z)³`. -/
def cfac (z : ℝ) : ℝ := -(2 * z * (1 - z)) / (1 + z) ^ 3

/-- `-2(1-z)/(1+z)³`, so that `cfac z = z * cu z`. -/
def cu (z : ℝ) : ℝ := -(2 * (1 - z)) / (1 + z) ^ 3

theorem cfac_eq_mul_cu (z : ℝ) : cfac z = z * cu z := by
  simp only [cfac, cu]; ring

/-! ## The `L₁₂`-constants and the `z`-profile `G` -/

/-- `Λ₁ = L₁₂(3 D_θ f/(1+z))(0)`, the constant produced by the projector applied to
the transport term. -/
def Lam1 (f : ℝ → ℝ → ℝ) : ℝ := L12f (Transport f) 0

/-- `Λ₂ = L₁₂(3 D_θ(D_z f)/(1+z))(0)`. -/
def Lam2 (f : ℝ → ℝ → ℝ) : ℝ := L12f (Transport (Dz f)) 0

/-- The `z`-profile `G` of the `Γ`-part of the `D_z`-commutator `E₂`:
`G(z) = -(2z(1-z)/(1+z)³)L₁₂(f)(z) + z q'(z) Λ₁ - q(z) Λ₂`. -/
def Gfun (f : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  cfac z * L12f f z + zdq z * Lam1 f - qfun z * Lam2 f

/-! ## The analytic hypothesis behind the pointwise identity

The pointwise expansion of the defect `E₂` uses the fundamental theorem of calculus on the
tail integral `L₁₂(f)(z) = ∫_z^∞ L₁₂-density` (which needs the density to be integrable) and
the identity `L₁₂(D_z f)(z) = -(K,f)_{L²_θ}(z)`, which needs in addition that the
`K`-average of `f` vanishes at `z = ∞`.  These are the only analytic inputs; they are
discharged from `SmoothNbhd f` and `HkMem α n f` (`1 ≤ n`) in the companion file. -/

/-- The analytic hypotheses used by the pointwise `D_z`-commutator identity at the level of
`z`-functions: the `L₁₂`-densities of `f` and of `D_z f` are integrable on the half-line
and the `K`-average of `f` vanishes at infinity. -/
structure TailHyp (f : ℝ → ℝ → ℝ) : Prop where
  /-- the `L₁₂`-density of `f` is integrable on `(0,∞)`. -/
  hint : IntegrableOn (FM.L12dens Spaces.K f) (Set.Ioi 0)
  /-- the `L₁₂`-density of `D_z f` is integrable on `(0,∞)`. -/
  hintDz : IntegrableOn (FM.L12dens Spaces.K (Spaces.Dz f)) (Set.Ioi 0)
  /-- the `K`-average `∫_θ K(θ) f(z,θ)` vanishes as `z → ∞`. -/
  hlim : Tendsto (fun s => Kav f s) atTop (𝓝 0)

/-- The radial factor of the `Γ`-part of the defect: `Gfun f z / c α`, so that
`(Γ(θ)/c α)·Gfun f z = Γ(θ)·(Gfun f z / c α)`. -/
def Frad (α : ℝ) (f : ℝ → ℝ → ℝ) (z : ℝ) : ℝ := Gfun f z / c α

theorem Frad_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (z : ℝ) :
    Frad α f z = Gfun f z / c α := rfl

/-- The commutator defect `E₂ = D_z 𝓛_Γ^T f - 𝓛_Γ^T(D_z f)`. -/
def E2fun (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Dz (LGammaT α f) z θ - LGammaT α (Dz f) z θ

theorem E2fun_eq (α : ℝ) (f : ℝ → ℝ → ℝ) :
    E2fun α f = fun z θ => Dz (LGammaT α f) z θ - LGammaT α (Dz f) z θ := rfl

end Work.Coercivity.CommutZ
