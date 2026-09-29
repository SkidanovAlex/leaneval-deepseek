import Mathlib
import Submission.Work.TMComp.Kotani.Defs

/-!
# C8 (Kotani theory): the objects of the extension argument

This file fixes the vocabulary of the extension argument (the derivation of AJ Theorem 2.2
from the vanishing of the Lyapunov exponent on an interval).  All objects are functions of a
complex energy `E` with `0 < E.im` (written `ε = E.im`) and of a phase `x`.

* `ell E = ∫₀¹ log ‖m(E,x)‖ dx`: the averaged log-modulus of the `m`-function.
* `pSec E x = -1/m(E,x)`: AJ's `p`; its imaginary part is `Im m(E,x+α) - ε`.
* `sSec E y = 1/m(E,α-y)`: the section with values in `-ℍ` satisfying the same invariance
  relation as `m`.
* `sigSec E y = 1/conj(m(E,α-y)) = conj (sSec E y)`: the `ℍ`-valued "reflected" section.
  Its boundary value at `E₀ + i0` is `1/conj(m⁺(E₀,α-y))`.
* `N1 E x = Im m(E,x) - ε/2`, `N2 E y = Im σ(E,y) + ε/2` (both `> 0` for `ε > 0`).
* `defect E y = m(E,y) - sSec E y`.
* `glued E y`: `m` on the upper half plane, `1/conj(m(conj E, α-y))` on the lower one.
* `Psi E y = -1/(glued E y - E/2)`: the quantity whose jump across the real axis is the
  obstruction to the continuation (the route's `Ψ`).
-/

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMComp.Kotani

open Work.TMContract

/-- `ℓ(E) = ∫₀¹ log ‖m(E,x)‖ dx`. -/
def ell (α lam : ℝ) (E : ℂ) : ℝ := ∫ x in (0 : ℝ)..1, Real.log ‖mfun α lam E x‖

/-- `p = -1/m`. -/
def pSec (α lam : ℝ) (E : ℂ) (x : ℝ) : ℂ := -1 / mfun α lam E x

/-- The `(-ℍ)`-valued section `s(y) = 1/m(α-y)`. -/
def sSec (α lam : ℝ) (E : ℂ) (y : ℝ) : ℂ := 1 / mfun α lam E (α - y)

/-- The `ℍ`-valued reflected section `σ(y) = 1/conj(m(α-y)) = conj(s(y))`. -/
def sigSec (α lam : ℝ) (E : ℂ) (y : ℝ) : ℂ := 1 / star (mfun α lam E (α - y))

/-- `N₁ = Im m - ε/2`. -/
def N1 (α lam : ℝ) (E : ℂ) (x : ℝ) : ℝ := (mfun α lam E x).im - E.im / 2

/-- `N₂ = Im σ + ε/2`. -/
def N2 (α lam : ℝ) (E : ℂ) (y : ℝ) : ℝ := (sigSec α lam E y).im + E.im / 2

/-- The defect `B = m - s` between the two sections. -/
def defect (α lam : ℝ) (E : ℂ) (y : ℝ) : ℂ := mfun α lam E y - sSec α lam E y

/-- The glued function: `m` on the upper half plane and `1/conj(m(conj E, α-y))` below. -/
def glued (α lam : ℝ) (E : ℂ) (y : ℝ) : ℂ :=
  if 0 < E.im then mfun α lam E y else 1 / star (mfun α lam (star E) (α - y))

/-- `Ψ = -1/(glued - E/2)`. -/
def Psi (α lam : ℝ) (E : ℂ) (y : ℝ) : ℂ := -1 / (glued α lam E y - E / 2)

/-- `conj σ = s`. -/
theorem conj_sigSec (α lam : ℝ) (E : ℂ) (y : ℝ) :
    star (sigSec α lam E y) = sSec α lam E y := by
  rw [sigSec, sSec, star_div₀, star_one, star_star]

end Work.TMComp.Kotani
