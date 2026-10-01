import Mathlib

/-!
# `zeroSumK`: the partial-fraction zero sum of an entire function

For an entire function `f` with (isolated) zeros, the Hadamard partial fraction expansion of
`logDeriv f` says

`logDeriv f (s) = B + Σ_u ord_u(f) · (1/(s-u) + 1/u)`

for a constant `B`; differentiating `k ≥ 1` times kills `B` and the `1/u` terms and produces

`(logDeriv f)^{(k)}(t) = (-1)^k k! · Σ_u ord_u(f) · (t-u)^{-(k+1)}`.

The two notions used by that statement are recorded here: the zero sum `zeroSumK` (with
`ord_u(f) = analyticOrderNatAt f u`), and the property that `f` has the zero-sum expansion in
order `k` at the point `t`.
-/

open scoped BigOperators

noncomputable section

namespace Work.LinnikAreas.TuranOther

/-- The `k`-th partial-fraction zero sum of `f` at `t`:
`Σ_u ord_u(f) · (t - u) ^ (-(k+1))`, where `ord_u(f) = analyticOrderNatAt f u` is the order of
vanishing of `f` at `u` (so only zeros of `f` contribute). -/
def zeroSumK (f : ℂ → ℂ) (t : ℂ) (k : ℕ) : ℂ :=
  ∑' u : ℂ, ((analyticOrderNatAt f u : ℕ) : ℂ) * (t - u) ^ (-(k + 1) : ℤ)

/-- `f` has the zero-sum expansion in order `k` at the point `t`: the `k`-th derivative of
`logDeriv f` at `t` equals `(-1)^k k!` times the zero sum of `f` at `t`. -/
def HasZeroSumExpansion (f : ℂ → ℂ) (t : ℂ) (k : ℕ) : Prop :=
  iteratedDeriv k (logDeriv f) t = (-1 : ℂ) ^ k * (k.factorial : ℂ) * zeroSumK f t k

end Work.LinnikAreas.TuranOther
