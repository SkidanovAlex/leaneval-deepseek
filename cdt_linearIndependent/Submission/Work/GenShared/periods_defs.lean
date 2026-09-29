import Mathlib
import Submission.CDT.RatFuncDeriv

/-!
# Shared vocabulary for the generic period-independence lemma (`Work.GenShared.periods_indep_gen`)

This module fixes the objects used by the whole `periods_indep_gen` development.

* `Rval f z` — the value at `z ∈ ℂ` of a rational function `f ∈ ℂ(X)`, read off from the
  canonical numerator/denominator representative `f.num / f.denom` (`= RatFunc.eval (RingHom.id ℂ) z f`).
* `Rreg f z` — `f` is finite (has no pole) at `z`, i.e. `f.denom.eval z ≠ 0`.
* `W k` — the "differential module" `K e₀ ⊕ K e₁ ⊕ ⊕ᵢ K φᵢ` (`K = ℂ(X)`) attached to an order-two
  operator `p₂ y'' + p₁ y' + p₀ y` and to period data `rᵢ = rnᵢ/rdᵢ`.
* `Dv p2 p1 p0 rn rd n` — the connection `∂` on `W k`:
  `∂(a,b,c) = (a' - (p₀/p₂)b + Σᵢ cᵢ rᵢ, a + b' - (p₁/p₂)b, (cᵢ')ᵢ)`,
  so that `∂e₀ = e₁`, `∂e₁ = -(p₀/p₂)e₀ - (p₁/p₂)e₁`, `∂φᵢ = rᵢ e₀`.
* `Wev y1 J n z` — evaluation of `n` at `z`: `a(z)y1(z) + b(z)y1'(z) + Σᵢ cᵢ(z)Jᵢ(z)`.
* `InN x0 δ y1 J n` — the vanishing condition defining the syzygy module `N = ker ev`:
  the relation holds at every point of the ball where all coefficients are regular.
-/

namespace Work.GenShared

open Complex Metric
open Submission.CDT (dRat)

noncomputable section

/-- The value at `z ∈ ℂ` of a rational function `f ∈ ℂ(X)`, read off from its canonical
numerator/denominator representative.  This is `RatFunc.eval (RingHom.id ℂ) z f`. -/
abbrev Rval (f : RatFunc ℂ) (z : ℂ) : ℂ := f.num.eval z / f.denom.eval z

/-- `f` is finite (has no pole) at `z`. -/
def Rreg (f : RatFunc ℂ) (z : ℂ) : Prop := f.denom.eval z ≠ 0

/-- The differential module `K e₀ ⊕ K e₁ ⊕ ⊕ᵢ K φᵢ` (`K = ℂ(X)`). -/
abbrev W (k : ℕ) := RatFunc ℂ × RatFunc ℂ × (Fin k → RatFunc ℂ)

/-- The connection `∂` on `W k` attached to the operator `p₂y''+p₁y'+p₀y` and the period data
`rᵢ = rnᵢ/rdᵢ`. -/
def Dv {k : ℕ} (p2 p1 p0 : Polynomial ℂ) (rn rd : Fin k → Polynomial ℂ) (n : W k) : W k :=
  (dRat n.1
      - (algebraMap (Polynomial ℂ) (RatFunc ℂ) p0
          / algebraMap (Polynomial ℂ) (RatFunc ℂ) p2) * n.2.1
      + ∑ i, n.2.2 i * (algebraMap (Polynomial ℂ) (RatFunc ℂ) (rn i)
          / algebraMap (Polynomial ℂ) (RatFunc ℂ) (rd i)),
   n.1 + dRat n.2.1
      - (algebraMap (Polynomial ℂ) (RatFunc ℂ) p1
          / algebraMap (Polynomial ℂ) (RatFunc ℂ) p2) * n.2.1,
   fun i => dRat (n.2.2 i))

/-- Evaluation of `n ∈ W k` at `z ∈ ℂ`. -/
def Wev {k : ℕ} (y1 : ℂ → ℂ) (J : Fin k → ℂ → ℂ) (n : W k) (z : ℂ) : ℂ :=
  Rval n.1 z * y1 z + Rval n.2.1 z * deriv y1 z + ∑ i, Rval (n.2.2 i) z * J i z

/-- The vanishing condition: `n` evaluates to the zero function at every point of the ball at which
all its coefficients are regular.  (`N = ker ev` of the period-independence argument.) -/
def InN {k : ℕ} (x0 : ℂ) (δ : ℝ) (y1 : ℂ → ℂ) (J : Fin k → ℂ → ℂ) (n : W k) : Prop :=
  ∀ z ∈ ball x0 δ, Rreg n.1 z → Rreg n.2.1 z → (∀ i, Rreg (n.2.2 i) z) → Wev y1 J n z = 0

end

end Work.GenShared
