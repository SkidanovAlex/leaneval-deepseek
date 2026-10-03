/-
# `Submission.Work.FIArea5.S16Hecke.LcontDefs`

The `L`-value read off a completed function.  Downstream (16.20)/(16.23) — the zero-free region and
the bound `1/L(s,ψ) ≪ d log²(|m|+|t|+3)` — are stated for the *analytic continuation* of `L(s,ψ)`,
which is **not** the divergent `tsum` `heckeLSeries` in the critical strip.  Given a completion `Lam`
of `LambdaHecke d chi m` (for instance the one produced by `heckeFE_primitive`), the continuation is

  `Lcont d Lam m s = Lam s / (X^s·Γ(s + m/2))`,   `X = 4d/π`,

with `completeDenom d m s = X^s·Γ(s + m/2)` the denominator.

Note (for the next session): the agreement `Lcont d Lam m s = heckeLSeries chi m s` in the
half-plane `re s > 1 + m/2` is immediate from the definitions together with
`Lam s = LambdaHecke d chi m s`; the proof needs only `X^s·Γ(s+m/2) ≠ 0` there (which holds since
`re (s + m/2) > 0`, so `Complex.Gamma_ne_zero_of_re_pos` applies, and the base `4d/π ≠ 0` for
`1 ≤ d`).  It is best proved where the nonvanishing of the `ℂ`-power is available.
-/
import Mathlib
import Submission.Work.FIArea5.S16Hecke.ThetaDefs

set_option autoImplicit false

namespace Work.FIArea5.S16Hecke

open scoped BigOperators

noncomputable section

/-- The denominator `X^s·Γ(s+m/2)` of the completed `L`-function, `X = 4d/π`. -/
def completeDenom (d : ℕ) (m : ℕ) (s : ℂ) : ℂ :=
  ((((4 * (d : ℝ)) / Real.pi) : ℂ) ^ s) * Complex.Gamma (s + (m : ℂ) / 2)

/-- The `L`-value of the completed function `Lam`: the meromorphic continuation of `L(s,ψ)`. -/
def Lcont (d : ℕ) (Lam : ℂ → ℂ) (m : ℕ) (s : ℂ) : ℂ :=
  Lam s / completeDenom d m s

end

end Work.FIArea5.S16Hecke
