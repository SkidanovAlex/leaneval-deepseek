import Mathlib

/-!
# `FIArea2/R6/BSBoxDefs` — shared vocabulary for the *unweighted* box reduction

This module holds the definitions used by the corrected route to the box estimate `hbox6`
(the previous route through the `gcd`-weighted count `cruxLHS d R X Y` is **unsound**: that
count does not carry the constraint `d² ≤ |u₁h₁²-u₂h₂²|` and is therefore FALSE — the resonant
family `X = 1`, `Y = h`, `d = h²+1`, `R ≥ d` gives `cruxLHS ≥ 4R(R+1)` because every
anti-diagonal pair `(u₁,u₂) = (-u,u)` satisfies `d ∣ u(h₁²+h₂²)`, while the claimed bound is
`≍ τ(d)R²h·log¹⁰⁰/d`).

The corrected route removes the `gcd` weight *first*, by the identity
`gcd(u₁,u₂) = Σ_{g ∣ u₁, g ∣ u₂} φ(g)`: with `u₁ = gx`, `u₂ = gy` one gets

  `bulkPart R X Y ≤ Σ_{g ≤ R} φ(g)·τ(g)^4 · uboxSum ⌊R/g⌋ X Y`,

so that everything reduces to the **unweighted** sum `uboxSum r X Y` (no `1/d`, no weight).
For the latter the resonance is harmless (an anti-diagonal configuration contributes `≍ r`
rather than `≍ r²`), and the sharp per-modulus count is `ndCount d r X Y ≪ XY(r²Λ(d) + r·τ(d)log r)/d`
with the local factor `Λ(d) = Σ_{c ∣ d} φ(c)/c · τ(c)`.

* `zBox N`, `zPz N`: the box `[-N,N]` and its non-zero part;
* `T4 u₁ u₂ h₁ h₂ = τ(|u₁h₁²-u₂h₂²|)⁴`;
* `uboxSum r X Y`: the unweighted box sum;
* `lamFun d`: the local factor `Λ(d)`;
* `ndCount d r X Y`: the number of quadruples with `d ∣ xh₁²-yh₂² ≠ 0`.
-/

namespace Work.FIArea2.R6

open Finset
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The integer box `[-N,N]`. -/
abbrev zBox (N : ℕ) : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)

/-- The non-zero part of the integer box `[-N,N]`. -/
abbrev zPz (N : ℕ) : Finset ℤ := (Finset.Icc (-(N : ℤ)) (N : ℤ)).filter (fun x => x ≠ 0)

/-- `τ(|u₁h₁² − u₂h₂²|)⁴`. -/
abbrev T4 (u1 u2 h1 h2 : ℤ) : ℝ :=
  (((u1 * h1 ^ 2 - u2 * h2 ^ 2).natAbs.divisors.card : ℝ) ^ 4)

/-- **The unweighted box sum.**  `Σ_{x,y ∈ ([-r,r]\{0})} Σ_{h₁ ∈ ([-X,X]\{0})} Σ_{h₂ ∈ ([-Y,Y]\{0})}
τ(|xh₁²-yh₂²|)⁴`.  (Here `τ(0) = 0`, so the vanishing configurations contribute nothing.) -/
def uboxSum (r X Y : ℕ) : ℝ :=
  ∑ x ∈ zPz r, ∑ y ∈ zPz r, ∑ h1 ∈ zPz X, ∑ h2 ∈ zPz Y, T4 x y h1 h2

/-- The local factor `Λ(d) = Σ_{c ∣ d} (φ(c)/c)·τ(c)`.  It is `≤ Π_{p^a‖d} (a+1)(a+2)/2`, and at
primes `Λ(p) = 3 - 2/p`. -/
def lamFun (d : ℕ) : ℝ :=
  ∑ c ∈ d.divisors, (Nat.totient c : ℝ) / (c : ℝ) * ((c.divisors.card : ℝ))

/-- The number of quadruples `(x,y,h₁,h₂) ∈ ([-r,r]\{0})² × ([-X,X]\{0}) × ([-Y,Y]\{0})` with
`d ∣ xh₁² - yh₂² ≠ 0`. -/
def ndCount (d r X Y : ℕ) : ℝ :=
  ∑ x ∈ zPz r, ∑ y ∈ zPz r, ∑ h1 ∈ zPz X, ∑ h2 ∈ zPz Y,
    (if (d : ℤ) ∣ x * h1 ^ 2 - y * h2 ^ 2 ∧ x * h1 ^ 2 - y * h2 ^ 2 ≠ 0 then (1 : ℝ) else 0)

/-- The §9 box sum (the left-hand side of `hbox6`). -/
def boxSum6 (R X Y : ℕ) : ℝ :=
  ∑ u1 ∈ zBox R, ∑ u2 ∈ zBox R,
    (Nat.gcd u1.natAbs u2.natAbs : ℝ) *
      (∑ h1 ∈ zBox X, ∑ h2 ∈ zBox Y, T4 u1 u2 h1 h2)

/-- The axis part of the box sum: at least one of the four coordinates is `0`. -/
def axisPart (R X Y : ℕ) : ℝ :=
  ∑ u1 ∈ zBox R, ∑ u2 ∈ zBox R, (Nat.gcd u1.natAbs u2.natAbs : ℝ) *
    ∑ h1 ∈ zBox X, ∑ h2 ∈ zBox Y,
      (if u1 = 0 ∨ u2 = 0 ∨ h1 = 0 ∨ h2 = 0 then T4 u1 u2 h1 h2 else 0)

/-- The bulk part of the box sum: all four coordinates non-zero. -/
def bulkPart (R X Y : ℕ) : ℝ :=
  ∑ u1 ∈ zBox R, ∑ u2 ∈ zBox R, (Nat.gcd u1.natAbs u2.natAbs : ℝ) *
    ∑ h1 ∈ zBox X, ∑ h2 ∈ zBox Y,
      (if u1 ≠ 0 ∧ u2 ≠ 0 ∧ h1 ≠ 0 ∧ h2 ≠ 0 then T4 u1 u2 h1 h2 else 0)

end

end Work.FIArea2.R6
