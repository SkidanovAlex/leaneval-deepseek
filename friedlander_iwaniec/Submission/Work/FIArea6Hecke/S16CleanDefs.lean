/-
# `Submission.Work.FIArea6Hecke.S16CleanDefs` — vocabulary of the §16 contour shift

Definitions used by the §16 assembly (`S16CleanCore_of_invBound`) and by the pieces delegated
for it.  Nothing here is a theorem to be proved; this module exists so that the lemmas can be
stated in a common vocabulary and can be worked on in parallel.

## The objects

* `NoSmallPrimesNat Pa n` — the prime-avoidance condition (5.8) on the *norm* `n = |z|²`.
* `Tsum Pa chi m p` — the Möbius-twisted Hecke sum `Σ_{(n,Π)=1} λ_m(n)μ(n)γ(n;C)p(n)`, i.e. the
  inner sum `Z` of (16.29)/(16.30) whose contour shift is the analytic heart of §16.
* `freqL Pa` — the frequency cutoff `L = ⌊exp(√log N)⌋` of (16.27).
* `heightT Pa` — the contour height `T` of (16.38), `T = 5exp(√log N) + 10 ≥ |m| + 3` for every
  frequency `|m| ≤ 4exp(√log N)` occurring in the target, and with
  `log (heightT Pa) + 1 ≤ 2√log N` for `log N ≥ 9`.
-/
import Mathlib
import Submission.Work.FIArea6Hecke.S16CoreDefs
import Submission.Work.FIArea5.S16Hecke.Defs
import Submission.Work.FITop4.Bridge.area5_6_defs

set_option autoImplicit false

namespace Work.FIArea6Hecke

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

open Work.FIArea5.S16Hecke

/-- The prime-avoidance condition (5.8) on the **norm**: `(n, Π) = 1` for `Π = ∏_{q ≤ Pz} q`.
This is the rational-integer form of `Work.FITop4.NoSmallPrimes Pa z` (for primary `z` and a
rational prime `q ≤ Pz` one has `q ∣ gnorm z ↔ q ∣ z`). -/
def NoSmallPrimesNat (Pa : Work.FITop.Params) (n : ℕ) : Prop :=
  ∀ q : ℕ, q.Prime → q ≤ Pa.Pz → ¬ q ∣ n

/-- The **Möbius-twisted Hecke sum** `Σ_{(n,Π)=1} λ_m(n)·μ(n)·γ(n;C)·p(n)` of (16.29)/(16.30),
the object whose contour shift is the analytic heart of §16.  (Effectively finitely supported
because `p` vanishes outside the segment (4.12).) -/
def Tsum (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) (p : ℝ → ℝ) : ℂ :=
  ∑' n : ℕ,
    (if NoSmallPrimesNat Pa n then
      heckeLam chi m n * (ArithmeticFunction.moebius n : ℂ) *
        (Work.FIPlan.gammaTrunc Pa.C n : ℂ) * (p n : ℂ)
     else 0)

/-- The frequency cutoff `L = ⌊exp(√log N)⌋` of (16.27). -/
def freqL (Pa : Work.FITop.Params) : ℕ := ⌊Real.exp (Real.sqrt (Real.log Pa.N))⌋₊

/-- The contour height `T` of (16.38). -/
def heightT (Pa : Work.FITop.Params) : ℝ :=
  5 * Real.exp (Real.sqrt (Real.log Pa.N)) + 10

/-- The **saving exponent** of the §16 contour shift, *FI* (16.37):

  `δ = min(c_h/(2 d^ε (log T + 1)), 1/log Pz)`.

The cap `1/log Pz` is **not** cosmetic: the local-factor product
`P(s) = ∏_{p ≤ Pz}(1-λ(p)p^{-s})⁻¹` is estimated by the trivial bound `≪ (log Pz)^3` of (16.33)
only when `|p^{-s}| = p^{-σ} < 3p^{-1}` for all `p ≤ Pz`, i.e. `δ = 1-σ ≤ 1/log Pz` (indeed
`∏_{5≤p≤Pz}(1-2p^{-σ})⁻¹ ≍ exp(c·Pz^δ/log Pz)`, which stops being polylog in `log N` as soon as
`δ > 1/log Pz`).  With this cap, (16.35) holds in the intersection of the regions (16.24) and
(16.32), and the resulting saving `exp(-ηδ log N)` is always at least `min(E1, E2)`:
writing `A = c_h/(2 d^ε(log T+1))`, `δ₁' = c(4d)^{-ε}/√log N` and `δ₂' = 1/log Pz` for a small
`c ≤ c_h 4^ε/4`, one has `A ≥ δ₁'`, so `δ = min(A, δ₂') ≥ min(δ₁', δ₂')`
(the case `δ₂' < δ₁'` additionally uses `log Pz > (4d)^ε√log N/c`, which is the case hypothesis). -/
def deltaC (Pa : Work.FITop.Params) (d : ℕ) (ε c_h : ℝ) : ℝ :=
  min (c_h / (2 * (d : ℝ) ^ ε * (Real.log (heightT Pa) + 1))) (1 / Real.log (Pa.Pz : ℝ))

end

end Work.FIArea6Hecke
