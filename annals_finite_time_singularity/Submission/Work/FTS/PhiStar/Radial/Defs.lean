/-
# `Work.FTS.PhiStar.Radial.Defs` — the explicit mode-wise radial solutions of `bslOp`

`bslOp α Ψ = -(α²z²∂_zzΨ + α(5+α)z∂_zΨ) + LzeroΨ`.  On the mode `e_m` of the (explicit)
Dirichlet eigenbasis of `Lzero` (`Work.FTS.PhiStar.Gegenbauer`, eigenvalues `λ_m = 2m(2m+5)`)
the radial part acts as `R + λ_m` with `R = -(α²z²∂_zz + α(5+α)z∂_z)`.  The indicial equation of
`R a = λ_m a` is `α²s² + 5αs - λ_m = 0`, and since `25 + 4λ_m = (4m+5)²` its roots are
**integral in the sense of `α`**:

  `s⁺_m = 2m/α`   (growing at `∞`),   `s⁻_m = -(2m+5)/α`  (decaying at `∞`),

with `s⁺ - s⁻ = (4m+5)/α`.  The decaying solution of `(R + λ_m) a = c` is therefore the
explicit Euler Green's function

  `radGreen α m c z = 1/(α(4m+5))·[ z^{s⁻} ∫_0^z c(t) t^{-1-s⁻} dt
                                        + z^{s⁺} ∫_z^∞ c(t) t^{-1-s⁺} dt ]`

(the direct computation: the `c`-terms of `a'` cancel, and the indicial relation
`α²s² + 5αs = λ_m` turns `-α²z²a'' - α(5+α)z a'` into `-λ_m a`, leaving
`α²(s⁺-s⁻)·(that prefactor)·c = c`).
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Radial

set_option autoImplicit false

/-- The decaying-at-`∞` solution of the mode-`m` radial Euler equation
`-α²z²a'' - α(5+α)z a' + λ_m a = c`, `λ_m = 2m(2m+5)`, in explicit Green's-function form. -/
def radGreen (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (z : ℝ) : ℝ :=
  1 / (α * (4 * (m : ℝ) + 5)) *
    (z ^ (-(2 * (m : ℝ) + 5) / α) * (∫ t in (0 : ℝ)..z, c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      + z ^ (2 * (m : ℝ) / α) * (∫ t in Set.Ioi z, c t * t ^ (-(2 * (m : ℝ) / α) - 1)))

/-- The mode-`m` angular weight `λ_m = 2m(2m+5)`. -/
def lamR (m : ℕ) : ℝ := 2 * (m : ℝ) * (2 * (m : ℝ) + 5)

end Work.FTS.PhiStar.Radial
