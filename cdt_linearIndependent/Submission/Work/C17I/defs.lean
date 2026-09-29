import Mathlib
import Submission.Work.C17.logPw_setup
import Submission.Work.C17.seventeen_defs
import Submission.CDT.LocationSing

/-!
# Definitions for the continuation of `Pfun ∘ φ` (area C17I)

This module collects the objects shared by the lemmas proving
`Work.C17I.pw_continuation`:

* `sw` — the Möbius involution `φ z = z/(z-1)`;
* `lens r` — the region `{z | ‖φ z‖ < r}` where the unlikely series converges on `φ`;
* `Sset m n` — the convex "stadium" joining the cusp `x_s = xsOf m n` to `p₀ = 1/4 + i/5`;
* `PhiC` — the composition `z ↦ Pfun (z/(z-1))` to be continued;
* `pp2, pp1, pp0, prh` — the pullbacks `P₂(φ z), P₁(φ z), P₀(φ z), ρ(φ z)` of the operator data;
* `odP, odQ, odR` — the normalised coefficients of the pulled-back equation
  `u'' + odP·u' + odQ·u = odR` (equivalently `(z-1)⁴π₂ᵖ·u'' + …`, in the "P-form");
* `A2, B2` — the companion first-order system `Y' = A z · Y + b z` with `Y = (u, u')`;
* `PhiVec` — the function `z ↦ (Φ z, Φ' z)`.
-/

namespace Work.C17I

open Polynomial

noncomputable section

/-- The Möbius involution `φ(z) = z/(z-1)` of the statement. -/
def sw (z : ℂ) : ℂ := z / (z - 1)

/-- The lens `{z | ‖φ z‖ < r}` on which the composition `Pfun ∘ φ` is given by the
convergent unlikely series. -/
def lens (r : ℝ) : Set ℂ := {z : ℂ | ‖sw z‖ < r}

/-- The stadium `Sset m n` of the statement: the union of the discs along the segment from
`x_s = xsOf m n` to `p₀`, i.e. the convex hull of `ball x_s ((1-x_s)/2)` and `ball p₀ (1/20)`. -/
def Sset (m n : ℕ) : Set ℂ :=
  Work.C17.stadiumSet (Work.C17.xsOf m n) ((1 - Work.C17.xsOf m n) / 2) (1 / 20)

/-- `Φ z = Pfun (z/(z-1))`, the composition whose continuation is the subject of
`Work.C17I.pw_continuation`. -/
def PhiC (a b : ℚ) (ra rb rab r0 : ℤ) (z : ℂ) : ℂ :=
  Work.C17.Pfun a b ra rb rab r0 (sw z)

/-- `P₂(φ z)`, the pullback of the `u''`-coefficient of the operator `M`. -/
def pp2 (a b : ℚ) (z : ℂ) : ℂ := (Work.C17.P2x a b).eval₂ (algebraMap ℚ ℂ) (sw z)

/-- `P₁(φ z)`, the pullback of the `u'`-coefficient of the operator `M`. -/
def pp1 (a b : ℚ) (z : ℂ) : ℂ := (Work.C17.P1x a b).eval₂ (algebraMap ℚ ℂ) (sw z)

/-- `P₀(φ z)`, the pullback of the `u`-coefficient of the operator `M`. -/
def pp0 (a b : ℚ) (z : ℂ) : ℂ := (Work.C17.P0x a b).eval₂ (algebraMap ℚ ℂ) (sw z)

/-- `ρ(φ z)`, the pullback of the inhomogeneity of `M`. -/
def prh (a b : ℚ) (ra rb rab : ℤ) (z : ℂ) : ℂ :=
  (Work.C17.rhoMx a b ra rb rab).eval₂ (algebraMap ℚ ℂ) (sw z)

/-- The `u'`-coefficient of the normalised pulled-back equation `u'' + odP·u' + odQ·u = odR`. -/
def odP (a b : ℚ) (z : ℂ) : ℂ := 2 / (z - 1) - pp1 a b z / (pp2 a b z * (z - 1) ^ 2)

/-- The `u`-coefficient of the normalised pulled-back equation. -/
def odQ (a b : ℚ) (z : ℂ) : ℂ := pp0 a b z / (pp2 a b z * (z - 1) ^ 4)

/-- The inhomogeneity of the normalised pulled-back equation. -/
def odR (a b : ℚ) (ra rb rab : ℤ) (z : ℂ) : ℂ :=
  prh a b ra rb rab z / (pp2 a b z * (z - 1) ^ 4)

/-- The matrix of the companion system `Y' = A z · Y + b z`, `Y = (u, u')`. -/
def A2 (a b : ℚ) (z : ℂ) : Fin 2 → Fin 2 → ℂ :=
  fun i j => if i = 0 then (if j = 0 then 0 else 1)
    else (if j = 0 then -(odQ a b z) else -(odP a b z))

/-- The inhomogeneity of the companion system `Y' = A z · Y + b z`. -/
def B2 (a b : ℚ) (ra rb rab : ℤ) (z : ℂ) : Fin 2 → ℂ :=
  fun i => if i = 0 then 0 else odR a b ra rb rab z

/-- The function `z ↦ (Φ z, Φ' z)`. -/
def PhiVec (a b : ℚ) (ra rb rab r0 : ℤ) (z : ℂ) : Fin 2 → ℂ :=
  ![PhiC a b ra rb rab r0 z, deriv (PhiC a b ra rb rab r0) z]

end

end Work.C17I
