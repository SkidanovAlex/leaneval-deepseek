/-
# `Work.FIChain.OddLayersMajorantDefs` — the explicit layer majorant

The **combinatorial core** of the Fundamental-Lemma bound is the following statement, valid for
*every* admissible density `ν` and *every* level `D` (no `LinNormK` involved):

> for odd `n = 2k+1`, every chain of primes counted by `TnB B ν n D y` has all its primes in the
> window `[D^{levB B k}, y)`, so that
> `TnB B ν n D y ≤ VfB ν (D^{levB B k}) · (Σ_{D^{levB B k} ≤ q < y} ν q)^{n} / n!`.

The exponent is `levB B k = ρ^k/(B+1)` with `ρ = (B-1)/(B+1)`: at each *pair* of recursion steps
the "budget" `D` is replaced by at least `D^ρ`, because the first of the two primes satisfies
`p^{B+1} ≤ D` while the second is smaller than the first.

Feeding the window through the two consequences of `LinNormK` (the ratio bound for `VfB` and the
measure bound for the window mass) yields the *explicit* `κ`-dimensional majorant
`layerMajorant`, whose sum over odd `n` is bounded by a constant depending only on `B, κ, C`.
-/
import Mathlib
import Submission.Work.FIChain.LamPlusBLayerDefs

set_option autoImplicit false

namespace Work.FIChain

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The budget-decay exponent `ρ = (B-1)/(B+1) ∈ (0,1)`. -/
def rhoB (B : ℝ) : ℝ := (B - 1) / (B + 1)

/-- `levB B k` is the exponent of the lower bound `D^{levB B k}` satisfied by every prime of a
chain of odd length `2k+1` counted by `TnB`. -/
def levB (B : ℝ) (k : ℕ) : ℝ := (rhoB B) ^ k / (B + 1)

/-- The window ratio `U = log y / log (max (D^{levB B k}) 2)`: the LinNormK cost of the window
`[D^{levB B k}, y)` relative to the full range `[2, y)`. -/
def layerU (B : ℝ) (k : ℕ) (D : ℝ) (y : ℝ) : ℝ :=
  Real.log y / Real.log (max (D ^ levB B k) 2)

/-- The explicit `κ`-dimensional Rosser–Iwaniec majorant for the odd layer of index `2k+1`:
`C · U^κ · (log C + κ log U)^{2k+1} / (2k+1)!`. -/
def layerMajorant (C κ B : ℝ) (k : ℕ) (D : ℝ) (y : ℝ) : ℝ :=
  C * (layerU B k D y) ^ κ
    * (Real.log C + κ * Real.log (layerU B k D y)) ^ (2 * k + 1)
    / ((2 * k + 1).factorial : ℝ)

/-- The prefix sum of `ν` over the elements of `S` strictly below `q`. -/
def chainPref (S : Finset ℕ) (ν : ℕ → ℝ) (q : ℕ) : ℝ :=
  ∑ q' ∈ S.filter (fun q' : ℕ => q' < q), ν q'

/-- The summand of the outer (`F`) window sum in the layer induction, at odd length `2k+1`. -/
def layerSummand (S : Finset ℕ) (ν : ℕ → ℝ) (k : ℕ) (q : ℕ) : ℝ :=
  ν q * ∑ q1 ∈ S.filter (fun q1 : ℕ => q1 < q), ν q1 * chainPref S ν q1 ^ (2 * k + 1)

end

end Work.FIChain
