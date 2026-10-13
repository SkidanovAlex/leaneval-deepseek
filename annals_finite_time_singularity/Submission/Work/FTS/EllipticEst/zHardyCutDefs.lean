/-
Copyright: work module for the Elgindi finite-time singularity project.

# The logarithmic cutoff of the radial weighted Hardy inequality `zHardy_sq_le`

This module fixes the vocabulary shared by the proof of

  `Work.FTS.EllipticEst.zHardy_sq_le`:
`∫ w² g² ≤ C ∫ w² (z ∂_z g)²` for every `g` smooth on `(0,∞)` with both weighted integrals
finite, where `w(z) = (1+z)²/z²` is the radial weight of the paper
(`Work.Spaces.w`, see `Submission/Work/FTS/EllipticEst/zHardyDefs.lean` for the
completion-of-squares identity `zHardy_pointwise` that is the pointwise input).

The standard route would let a small parameter tend to `0` in the boundary term of
`zHardy_pointwise`; the point of this file is the replacement of that limit by an
approximation of `g` by functions which are *compactly supported inside* `(0,∞)`, for which
the boundary term vanishes exactly.  Since the weight `w(z) = (1+z)²/z²` blows up like
`z^{-2}` at the origin while `∫_0 w²` diverges like `z^{-3}`, a cutoff at scale `1/k` must be
placed on the *logarithmic* scale `|log z| ≲ log k`: this is what makes the commutator
`z ψ'_k` of the cutoff with `z ∂_z` as small as `K / log k`, uniformly in `z`.

## The gadgets

* `IsZCut φ K`: `φ` is a `C^∞` bump on `ℝ` with `φ = 1` on `[-1,1]`, `φ = 0` outside
  `(-2,2)`, values in `[0,1]` and `|φ'| ≤ K`;
* `psiFun φ k z = φ (log z / log k)`: `= 1` on `[1/k, k]`, `= 0` on `(0,1/k²] ∪ [k²,∞)`,
  so that `z ψ'_k(z) = φ'(log z / log k)/log k` is bounded by `K/log k`;
* `smoothOrder = ∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)`, the *smooth* order of `ContDiff`, used
  everywhere here because the literal `⊤ : ℕ∞ω` is the **analytic** order `ω` (a bump is
  never analytic, so a proof of `Conjecture` written with `⊤` would be vacuous — see
  `Submission/Work/Stability/Cutoff.lean` for the same trap).
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllipticEst.zHardyDefs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false

/-- **The *smooth* order `∞` of `ContDiff`** — written as an explicit term because the literal
`⊤ : ℕ∞ω` is the *analytic* order `ω` in this Mathlib (`ℕ∞ω = WithTop ℕ∞`, `∞ = ((⊤ : ℕ∞) : ℕ∞ω)`;
see `Mathlib/Analysis/Calculus/ContDiff/Defs.lean`).  Writing `⊤` where smoothness is meant gives
the analytic class, which is a trap already recorded in `Submission/Work/Stability/Cutoff.lean`. -/
abbrev smoothOrder : WithTop ℕ∞ := ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- A `C^∞` bump on `ℝ` which is `1` on `[-1,1]`, `0` outside `(-2,2)`, takes values in
`[0,1]`, and whose derivative is bounded in absolute value by `K ≥ 0`.

The order parameter is the *smooth* order `smoothOrder = ∞`, not `⊤ = ω`: a bump is never
analytic, so with `⊤` this predicate would be unsatisfiable. -/
def IsZCut (φ : ℝ → ℝ) (K : ℝ) : Prop :=
  ContDiff ℝ smoothOrder φ ∧ (∀ t, |t| ≤ 1 → φ t = 1) ∧ (∀ t, 2 ≤ |t| → φ t = 0) ∧
    (∀ t, 0 ≤ φ t ∧ φ t ≤ 1) ∧ 0 ≤ K ∧ ∀ t, |deriv φ t| ≤ K

/-- The logarithmic cutoff `ψ_k(z) = φ(log z / log k)`. -/
def psiFun (φ : ℝ → ℝ) (k : ℕ) (z : ℝ) : ℝ := φ (Real.log z / Real.log (k : ℝ))

end Work.FTS.EllipticEst
