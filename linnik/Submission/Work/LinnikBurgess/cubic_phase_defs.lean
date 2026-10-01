import Mathlib
import Submission.Commons.NumberTheory.GaussSum.quadratic_phase_prime_pow

/-!
# Definitions for the cubic `p`-adic Weyl bound

This module sets up the vocabulary used by `Work.LinnikBurgess.cubic_phase_prime_pow`:

* `CubicPhase p β γ δ R` is the explicit cubic phase `β X + γ X² + δ X³ + p R`;
* `linCoeff β γ δ r = β + 2 γ r + 3 δ r²` is the derivative of the cubic part,
  i.e. the derivative of the phase modulo `p`;
* `quadCoeff γ δ r = γ + 3 δ r` is half the second derivative of the cubic part;
* `resPoly p R c` and `shiftPhase p β γ δ R c` encode the stationary-phase reduction
  at a root `c` of `linCoeff`:  the phase `H(c + p X) - H(c)` equals `p²` times
  `shiftPhase` (see `cubic_phase_shiftPhase` for the exact identity);
* `shiftPhaseLinear` / `shiftPhaseLevel` are the two pieces of `shiftPhase` used when the
  quadratic coefficient `quadCoeff` is divisible by `p` (the doubly degenerate case).
-/

namespace Work.LinnikBurgess

open Polynomial

/-- The explicit cubic phase `β·X + γ·X² + δ·X³ + p·R`. -/
noncomputable def CubicPhase (p : ℕ) (β γ δ : ℤ) (R : Polynomial ℤ) : Polynomial ℤ :=
  Polynomial.C β * Polynomial.X + Polynomial.C γ * Polynomial.X ^ 2
    + Polynomial.C δ * Polynomial.X ^ 3 + Polynomial.C (p : ℤ) * R

/-- The derivative of the cubic part of the phase at `r`, i.e. `β + 2γr + 3δr²`.
Its vanishing modulo `p` is exactly the stationarity condition for the phase. -/
def linCoeff (β γ δ : ℤ) (r : ℕ) : ℤ := β + 2 * γ * (r : ℤ) + 3 * δ * (r : ℤ) ^ 2

/-- Half the second derivative of the cubic part of the phase at `r`, i.e. `γ + 3δr`. -/
def quadCoeff (γ δ : ℤ) (r : ℕ) : ℤ := γ + 3 * δ * (r : ℤ)

/-- `(R(c + pX) - R(c) - p R'(c) X)/p²`, written out with Hasse derivatives.  It is a
polynomial with integer coefficients; its role is the remainder term of the Taylor
expansion of the perturbation `R`. -/
noncomputable def resPoly (p : ℕ) (R : Polynomial ℤ) (c : ℕ) : Polynomial ℤ :=
  ∑ n ∈ Finset.range (R.natDegree - 1),
    Polynomial.C ((Polynomial.hasseDeriv (n + 2) R).eval (c : ℤ) * (p : ℤ) ^ n)
      * Polynomial.X ^ (n + 2)

/-- The high part of `resPoly`, i.e. `resPoly` with its `X²` and `X³` terms removed; it is
the part of the remainder of the Taylor expansion that is divisible by `p²`
(see `resPoly_expand`). -/
noncomputable def resPolyHi (p : ℕ) (R : Polynomial ℤ) (c : ℕ) : Polynomial ℤ :=
  ∑ n ∈ Finset.range (R.natDegree - 3),
    Polynomial.C ((Polynomial.hasseDeriv (n + 4) R).eval (c : ℤ) * (p : ℤ) ^ n)
      * Polynomial.X ^ (n + 4)

/-- The reduced phase of the stationary-phase step at a root `c` of `linCoeff`:
`(H(c + pX) - H(c))/p²` where `H = CubicPhase p β γ δ R`.  It has the shape
`a X + b X² + δ p X³ + p·(remainder)`, with `a = linCoeff/p + R'(c)` and
`b = quadCoeff γ δ c`. -/
noncomputable def shiftPhase (p : ℕ) (β γ δ : ℤ) (R : Polynomial ℤ) (c : ℕ) : Polynomial ℤ :=
  Polynomial.C (linCoeff β γ δ c / (p : ℤ) + (Polynomial.derivative R).eval (c : ℤ)) * Polynomial.X
    + Polynomial.C (quadCoeff γ δ c) * Polynomial.X ^ 2
    + Polynomial.C (δ * (p : ℤ)) * Polynomial.X ^ 3
    + Polynomial.C (p : ℤ) * resPoly p R c

/-- The part of `shiftPhase` of `p`-adic level one (used when `p ∣ quadCoeff`), so that
`shiftPhase = a X + p · shiftPhaseLinear`. -/
noncomputable def shiftPhaseLinear (p : ℕ) (γ δ : ℤ) (R : Polynomial ℤ) (c : ℕ) : Polynomial ℤ :=
  Polynomial.C (quadCoeff γ δ c / (p : ℤ)) * Polynomial.X ^ 2
    + Polynomial.C δ * Polynomial.X ^ 3 + resPoly p R c

/-- The genuine cubic phase `shiftPhase/p` obtained in the doubly degenerate case. -/
noncomputable def shiftPhaseLevel (p : ℕ) (β γ δ : ℤ) (R : Polynomial ℤ) (c : ℕ) : Polynomial ℤ :=
  Polynomial.C ((linCoeff β γ δ c / (p : ℤ) + (Polynomial.derivative R).eval (c : ℤ)) / (p : ℤ))
      * Polynomial.X
    + Polynomial.C (quadCoeff γ δ c / (p : ℤ)) * Polynomial.X ^ 2
    + Polynomial.C δ * Polynomial.X ^ 3 + resPoly p R c

@[simp] theorem linCoeff_zero (β γ δ : ℤ) : linCoeff β γ δ 0 = β := by
  simp [linCoeff]

@[simp] theorem quadCoeff_zero (γ δ : ℤ) : quadCoeff γ δ 0 = γ := by
  simp [quadCoeff]

/-- The shape of a genuine cubic phase, spelled out with `CubicPhase`; this is the same
predicate as `IsCubic` in `ddDefs` (see `isCubic_iff` there). -/
def IsCubicShape (p : ℕ) (H : Polynomial ℤ) : Prop :=
  ∃ β γ δ : ℤ, ∃ R : Polynomial ℤ, ¬ (p : ℤ) ∣ δ ∧ H = CubicPhase p β γ δ R

end Work.LinnikBurgess
