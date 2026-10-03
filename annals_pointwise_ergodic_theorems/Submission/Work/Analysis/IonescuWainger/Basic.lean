/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Mathlib

/-!
# The Ionescu–Wainger height and arithmetic frequency sets

This file sets up the arithmetic side of the Ionescu–Wainger (IW) machinery used by
Krause–Mirek–Tao, *Pointwise ergodic theorems for non-conventional bilinear polynomial
averages*, Annals of Math. 195 (2022), Appendix A (`iw-app`) and §5.

The objects defined here are:

* `Circle` — the frequency circle `ℝ/ℤ`, in which arithmetic frequencies live;
* `naiveHeight α = 2^{⌈log₂ q⌉}` for an arithmetic frequency `α = a/q`;
* `iwD`, `iwEps`, `iwN0`, `iwQ0`, `iwW` — the auxiliary quantities `D_ρ`, `ε_ρ`,
  `N_0^{(l)}`, `Q_0^{(l)}` and the set `W_{≤l}` of Appendix A;
* `iwPconcrete ρ l = P_{≤l}` for `l > C⁰_ρ` and `iwP ρ l` (the paper's `P_{≤l}`,
  which is `[2^l]` for `l ≤ C⁰_ρ`);
* `iwArithFreqs ρ l = (ℚ/ℤ)_{≤l}`, the IW arithmetic frequency set of height `≤ 2^l`;
* `iwHeight ρ` and `iwHeightIndex ρ` — the IW height `Height_ρ`.

The splitting threshold `iwC0 ρ` plays the role of the paper's "sufficiently large
`C⁰_ρ`"; the precise statement of what is needed from it is
`iwPconcrete_contains_range` in `Submission.Work.Analysis.IonescuWainger.Height`.

## Main definitions

* `Work.Analysis.IonescuWainger.Circle`
* `Work.Analysis.IonescuWainger.naiveHeight`
* `Work.Analysis.IonescuWainger.iwP`
* `Work.Analysis.IonescuWainger.iwArithFreqs`
* `Work.Analysis.IonescuWainger.iwHeight`
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Analysis.IonescuWainger

instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- The frequency circle `ℝ/ℤ`; arithmetic frequencies `a/q mod 1` are elements of this group. -/
abbrev Circle : Type := AddCircle (1 : ℝ)

/-- The paper's constant `D_ρ = ⌊2/ρ⌋ + 1`. -/
noncomputable def iwD (ρ : ℝ) : ℕ := ⌊2 / ρ⌋₊ + 1

/-- The paper's `ε_ρ = ρ D_ρ / 2 - 1` (positive for `0 < ρ < 1`). -/
noncomputable def iwEps (ρ : ℝ) : ℝ := ρ * (iwD ρ : ℝ) / 2 - 1

/-- The paper's `N_0^{(l)} = ⌊2^{ρ l/2}⌋ + 1`. -/
noncomputable def iwN0 (ρ : ℝ) (l : ℕ) : ℕ := ⌊(2 : ℝ) ^ (ρ * (l : ℝ) / 2)⌋₊ + 1

/-- The paper's `Q_0^{(l)} = (N_0^{(l)}!)^{D_ρ}`. -/
noncomputable def iwQ0 (ρ : ℝ) (l : ℕ) : ℕ := (iwN0 ρ l).factorial ^ iwD ρ

/-- The primes in the interval `(N_0^{(l)}, 2^l]`. -/
noncomputable def iwPrimeRange (ρ : ℝ) (l : ℕ) : Finset ℕ :=
  (Finset.Icc (iwN0 ρ l + 1) (2 ^ l)).filter Nat.Prime

/-- The paper's `W_{≤l}`: the products of at most `D_ρ` distinct primes from
`(N_0^{(l)}, 2^l]`, each taken to a power in `[1, D_ρ]`.  Realised as the divisors of
`∏_{p ∈ (N_0^{(l)}, 2^l], p prime} p^{D_ρ}` whose number of distinct prime factors is at most
`D_ρ`. -/
noncomputable def iwW (ρ : ℝ) (l : ℕ) : Finset ℕ :=
  (Nat.divisors (∏ p ∈ iwPrimeRange ρ l, p ^ iwD ρ)).filter
    (fun w => w.factorization.support.card ≤ iwD ρ)

/-- The paper's `P_{≤l}` in the regime `l > C⁰_ρ`:
`q ∈ P_{≤l}` iff `q = Q w` with `Q ∣ Q_0^{(l)}` and `w ∈ W_{≤l}`. -/
noncomputable def iwPconcrete (ρ : ℝ) (l : ℕ) : Finset ℕ :=
  (Nat.divisors (iwQ0 ρ l)).biUnion (fun Q => (iwW ρ l).image (fun w => Q * w))

/-- The threshold `C⁰_ρ` of Appendix A: for `l ≤ iwC0 ρ` the paper *defines* `P_{≤l} = [2^l]`,
and for `l > iwC0 ρ` the concrete description `iwPconcrete` applies.  The value below is a
concrete (very generous) choice which is large enough for the Appendix A congruence argument;
see `iwPconcrete_contains_range`. -/
noncomputable def iwC0 (ρ : ℝ) : ℕ :=
  ⌈(2 / ρ) * ((1 + iwEps ρ) / iwEps ρ)⌉₊ + ⌈10 / ρ⌉₊ + 100

/-- The Ionescu–Wainger set `P_{≤l}` of admissible denominators: `[2^l]` for `l ≤ iwC0 ρ`
and `iwPconcrete ρ l` for `l > iwC0 ρ`. -/
noncomputable def iwP (ρ : ℝ) (l : ℕ) : Finset ℕ :=
  if l ≤ iwC0 ρ then Finset.Icc 1 (2 ^ l) else iwPconcrete ρ l

/-- The IW arithmetic frequency set `(ℚ/ℤ)_{≤l} = {α : Height_ρ(α) ≤ 2^l}`, realised as the
union of the `q`-torsion subgroups of `ℝ/ℤ` over `q ∈ P_{≤l}`. -/
noncomputable def iwArithFreqs (ρ : ℝ) (l : ℕ) : Finset Circle :=
  (iwP ρ l).biUnion (fun q => (Finset.range q).image (fun a : ℕ => ((a : ℝ) / (q : ℝ) : Circle)))

/-- The IW height index of a frequency: the least `l` with `q ∈ P_{≤l}` for some `q` killing `α`.
For a torsion (i.e. rational) frequency this is finite; the convention `sInf ∅ = 0` is used for
non-torsion frequencies. -/
noncomputable def iwHeightIndex (ρ : ℝ) (α : Circle) : ℕ :=
  sInf {l : ℕ | ∃ q ∈ iwP ρ l, q • α = 0}

/-- The Ionescu–Wainger height `Height_ρ(α) = 2^{iwHeightIndex ρ α} ∈ 2^ℕ`. -/
noncomputable def iwHeight (ρ : ℝ) (α : Circle) : ℕ := 2 ^ iwHeightIndex ρ α

/-- The naive height `Height_naive(a/q mod 1) = 2^{⌈log₂ q⌉} ∼ q`.  For a non-torsion frequency
`addOrderOf α = 0` and this takes the value `1`; it is only used for rational `α`. -/
noncomputable def naiveHeight (α : Circle) : ℕ := 2 ^ Nat.clog 2 (addOrderOf α)

end Work.Analysis.IonescuWainger
