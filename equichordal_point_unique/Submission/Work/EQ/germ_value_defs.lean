import Mathlib
import Submission.Work.EQ.Defs

/-!
# Value-at-a-point predicates and the polynomial shapes behind `germ_no_other_roots`

`HasVal A C w L` says that the rational function `A/C` (`C ≠ 0`) has value `L` at `w`:
the difference `A - L*C` vanishes at `w` to order at least `ord_w C + 1`.
This is a purely polynomial predicate (no limits), and it is the "value of a rational
function with cancellation" that the semi-projective argument needs.

The remaining definitions record the polynomial shape of the rational function
`X(u) = a*h(ℓu)/(h(ℓu) - h(u)) - a/2` (Rychlik's semi-projective `x`-coordinate) when
`h = N/D` is rational with `ℓ = eqLam a`:

* `P2p N D ℓ` is `P2(u) = N(ℓu)D(u) - N(u)D(ℓu)`, the common denominator of `X`;
* `Np N D ℓ` is `Ñ(u) = N(u)D(ℓu)`, so that `X = (a/2) + a*Ñ/P2`;
* `Lam N D a ℓ` is `Λ = (a/2)*P2 + a*Ñ`, so that `X = Λ/P2`;
* `Ep N D` is `E = N^2 + D^2 = 1 + R^2` over the common denominator.
-/

namespace Work.EQ

open Polynomial

/-- The rational function `A/C` (`C ≠ 0`) has value `L` at `w` iff `A - L*C` vanishes at `w`
to order at least `ord_w C + 1`. -/
def HasVal (A C : Polynomial ℂ) (w L : ℂ) : Prop :=
  (Polynomial.X - Polynomial.C w) ^ (C.rootMultiplicity w + 1) ∣ (A - Polynomial.C L * C)

/-- `P2(u) = N(ℓu) D(u) - N(u) D(ℓu)`. -/
noncomputable def P2p (N D : Polynomial ℂ) (ℓ : ℂ) : Polynomial ℂ :=
  N.comp (Polynomial.C ℓ * Polynomial.X) * D - N * D.comp (Polynomial.C ℓ * Polynomial.X)

/-- `Ñ(u) = N(u) D(ℓu)`. -/
noncomputable def Np (N D : Polynomial ℂ) (ℓ : ℂ) : Polynomial ℂ :=
  N * D.comp (Polynomial.C ℓ * Polynomial.X)

/-- `Λ(u) = (a/2)·P2(u) + a·Ñ(u)`; then `X = Λ / P2`. -/
noncomputable def Lam (N D : Polynomial ℂ) (a ℓ : ℂ) : Polynomial ℂ :=
  Polynomial.C (a / 2) * P2p N D ℓ + Polynomial.C a * Np N D ℓ

/-- `E(u) = N(u)^2 + D(u)^2`. -/
noncomputable def Ep (N D : Polynomial ℂ) : Polynomial ℂ := N ^ 2 + D ^ 2

/-- `Ψ(u) = Λ(ℓu)·P2(u) + Λ(u)·P2(ℓu)`, the numerator of `X(ℓu) + X(u)`. -/
noncomputable def Psip (N D : Polynomial ℂ) (a ℓ : ℂ) : Polynomial ℂ :=
  (Lam N D a ℓ).comp (Polynomial.C ℓ * Polynomial.X) * P2p N D ℓ
    + Lam N D a ℓ * (P2p N D ℓ).comp (Polynomial.C ℓ * Polynomial.X)

/-- `Θ(u) = P2(u)·P2(ℓu)`, the denominator of `X(ℓu) + X(u)`. -/
noncomputable def ThetaP (N D : Polynomial ℂ) (ℓ : ℂ) : Polynomial ℂ :=
  P2p N D ℓ * (P2p N D ℓ).comp (Polynomial.C ℓ * Polynomial.X)

end Work.EQ
