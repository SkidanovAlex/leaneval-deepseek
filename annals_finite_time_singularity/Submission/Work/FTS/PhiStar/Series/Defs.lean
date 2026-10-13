/-
# `Work.FTS.PhiStar.Series.Defs` — the mode series of the solution of `bslOp α Ψ = F`

With the angular Dirichlet basis `eFam m` of `Lzero` (`Gegenbauer/Defs.lean`, eigenvalues
`lam m = 2m(2m+5)`, orthogonality `eFam_orthogonal`, completeness `eFam_complete`) and the
explicit decaying mode solution `radGreen` of the radial Euler equation
(`Radial/Defs.lean`, `Radial/radGreen_solves`), the solution of `bslOp α Ψ = F` is assembled as

  `Ψ = Σ_m a_m(z)·e_m(θ)`,   `a_m = radGreen α m (cmode m F)`,

where `cmode m F z` is the `e_m`-coefficient of the slice `F(z,·)` in the self-adjoint weight
`cos θ dθ`,

  `cmode m F z = (∫_θ F(z,θ)·e_m(θ)·cos θ)/(∫_θ e_m(θ)²·cos θ)`.

Because the source moment condition `Fstar F ≡ 0` is exactly `cmode 0 F ≡ 0`, the `m = 0` term
vanishes identically (`lam 0 = 0`, `e_0 ∝ sin 2θ`), which is why the moment condition on `F` is
the natural hypothesis; the series therefore starts at `m = 1` effectively.

`psiTrunc` is the finite partial sum, which solves the truncated equation with source
`Σ_{m≤N} cmode m F z · e_m(θ)` and whose honesty (`HkMem`) is automatic — the object on which the
truncation/Fatou argument for the honesty of `psiSeries` runs.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.Radial.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series

set_option autoImplicit false

/-- The `e_m`-coefficient of the slice `F(z,·)` for the self-adjoint weight `cos θ dθ`. -/
def cmode (m : ℕ) (F : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  (∫ θ in (0 : ℝ)..(Real.pi / 2),
      F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
    / (∫ θ in (0 : ℝ)..(Real.pi / 2),
        Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ)

/-- The mode-`m` radial coefficient of the solution: the decaying solution of the Euler equation
`-α²z²a'' - α(5+α)z a' + lam m · a = cmode m F`. -/
def acoeff (α : ℝ) (m : ℕ) (F : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  Work.FTS.PhiStar.Radial.radGreen α m (fun t => cmode m F t)

/-- The `N`-th partial sum of the mode series (source `Σ_{m≤N} cmode m F z · e_m`). -/
def psiTrunc (α : ℝ) (F : ℝ → ℝ → ℝ) (N : ℕ) (z θ : ℝ) : ℝ :=
  ∑ m ∈ Finset.range (N + 1),
    acoeff α m F z * Work.FTS.PhiStar.Gegenbauer.eFam m θ

/-- The mode series solution of `bslOp α Ψ = F`. -/
def psiSeries (α : ℝ) (F : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  ∑' m : ℕ, acoeff α m F z * Work.FTS.PhiStar.Gegenbauer.eFam m θ

end Work.FTS.PhiStar.Series
