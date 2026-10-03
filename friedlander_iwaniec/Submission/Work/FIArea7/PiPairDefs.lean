/-
# `Submission.Work.FIArea7.PiPairDefs` — the `π`-sublattice vocabulary of the pair-mass estimate

The coprimality-guard removal (`Work.FIArea7.uniModePairMass_le`) bounds the pair weight of the
non-coprime pairs of the box by grouping them along the common Gaussian prime `π` of *FI* (5.8).
This module holds the definitions of that grouping (they are shared with the delegated lemmas
`card_piDvd_filter_dvd_absDelta_le`, `uniMode_pairInner_le_sum_pairPi`, `pairPi_le_massW_rhoPi`,
`sum_massW_le`):

* `shrunkNat R π = ⌊R√2/√(gnorm π)⌋` and `rhoPi R π = 2·shrunkNat R π + 1`: the radius and the
  point count of the box cut down by the `π`-sublattice `π ℤ[i]` (a point `π w` with `|π w|∞ ≤ R`
  has `|w|∞ ≤ shrunkNat R π`), and `rhoPi` is exactly the constant of the fibre bound
  `card_piDvd_filter_dvd_absDelta_le`;
* `bigPi Pa m`: the Gaussian primes of the box in the canonical quadrant `re > 0, im ≥ 0`
  (one per associate class), of norm `> Pz` — i.e. the primes allowed by (5.8) — and coprime to `m`
  (which holds automatically for every prime that divides a pair of the support);
* `piBox Pa π m`: the points `w` with `π w` in the box and `(gnorm w, m) = 1`, i.e. the
  `π`-sublattice points that can occur as the `w` of a supported pair;
* `massW Pa β π m = ∑_{w ∈ piBox} ‖β(π w)‖²`, the mass of that sublattice;
* `pairPi Pa b e β π`: the `π`-part of the pair mass, i.e. the sum over `piBox × piBox` of the
  weights of the pairs with `4be ∣ |Δ|`;
* `piDvdAbsDeltaFinset π z₁' R c`: the `z₂ ∈ gBox R` with `π ∣ z₂` and `c ∣ |Δ(π z₁', z₂)|`,
  the set of the delegated counting lemma.
-/
import Mathlib
import Submission.Work.FIPlan.Interface
import Submission.Work.FITop.Defs

attribute [local instance] Classical.propDecidable

namespace Work.FIArea7

open Finset
open scoped BigOperators

noncomputable section

/-- The radius `⌊R√2/√(gnorm π)⌋` of the box cut down by the sublattice `π ℤ[i]`. -/
def shrunkNat (R : ℤ) (π : GaussianInt) : ℕ :=
  Nat.floor ((R : ℝ) * Real.sqrt 2 / Real.sqrt (Work.FIPlan.gnorm π))

/-- The point count `2·⌊R√2/√(gnorm π)⌋ + 1` of the fibre bound
`card_piDvd_filter_dvd_absDelta_le`. -/
def rhoPi (R : ℤ) (π : GaussianInt) : ℕ := 2 * shrunkNat R π + 1

/-- The Gaussian primes of the box, in the canonical quadrant `re > 0, im ≥ 0`, of norm `> Pz`,
and coprime to the modulus `m`. -/
def bigPi (Pa : Work.FITop.Params) (m : ℕ) : Finset GaussianInt :=
  (Work.FIPlan.gBox (Work.FITop.radN Pa)).filter (fun π =>
    Prime π ∧ 0 < π.re ∧ 0 ≤ π.im ∧ Pa.Pz < Work.FIPlan.gnorm π
      ∧ Nat.Coprime (Work.FIPlan.gnorm π) m)

/-- The `π`-sublattice points of the box, restricted to norms coprime to `m`. -/
def piBox (Pa : Work.FITop.Params) (π : GaussianInt) (m : ℕ) : Finset GaussianInt :=
  ((Work.FIPlan.gBox ((shrunkNat (Work.FITop.radN Pa) π : ℕ) : ℤ)).filter
      (fun w => π * w ∈ Work.FIPlan.gBox (Work.FITop.radN Pa))).filter
    (fun w => Nat.Coprime (Work.FIPlan.gnorm w) m)

/-- The mass `∑ ‖β(π w)‖²` of the `π`-sublattice. -/
def massW (Pa : Work.FITop.Params) (β : GaussianInt → ℂ) (π : GaussianInt) (m : ℕ) : ℝ :=
  ∑ w ∈ piBox Pa π m, ‖β (π * w)‖ ^ 2

/-- The `π`-part of the pair mass: the weights of the pairs of the `π`-sublattice whose
determinant is divisible by `4be`. -/
def pairPi (Pa : Work.FITop.Params) (b e : ℕ) (β : GaussianInt → ℂ) (π : GaussianInt) : ℝ :=
  ∑ w1 ∈ piBox Pa π (4 * b * e), ∑ w2 ∈ piBox Pa π (4 * b * e),
    (if 4 * b * e ∣ Work.FIPlan.absDelta (π * w1) (π * w2)
      then ‖β (π * w1)‖ * ‖β (π * w2)‖ else 0)

/-- The `z₂` of the box `gBox R` divisible by `π` and satisfying `c ∣ |Δ(π z₁', z₂)|`. -/
def piDvdAbsDeltaFinset (π z1' : GaussianInt) (R : ℤ) (c : ℕ) : Finset GaussianInt :=
  (Work.FIPlan.gBox R).filter (fun z2 => π ∣ z2 ∧ c ∣ Work.FIPlan.absDelta (π * z1') z2)

end

end Work.FIArea7
