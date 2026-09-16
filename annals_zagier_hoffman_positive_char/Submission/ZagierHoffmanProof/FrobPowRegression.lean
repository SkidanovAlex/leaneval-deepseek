import Submission.ZagierHoffmanProof.SuperPeriod
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Regression tests for the `FrobPow` generalisation of the Frobenius twist

Mathlib's `ExpChar R q` only exists for `q` prime, which restricted the whole `Ω`/`L`-series
chapter to finite fields `F` with `|F|` prime.  The `FrobPow` class (`FrobPow.lean`) removes the
restriction: `q = |F| = p ^ f` is always a Frobenius exponent for `F((y))`
(`frobPow_laurentSeries`), so the period function and the `L`-series are available for **every**
finite field `F`.

This file checks:

* `FrobPow` on `F((y))` for `F = ZMod 2`, `ZMod 3`, `GaloisField 2 2` (`|F| = 4`),
  `GaloisField 3 2` (`|F| = 9`) — the last two being the cases that were previously inaccessible;
* the `ExpChar`-based twist is the special case `f = 1` of the `FrobPow`-based one
  (`FrobPow.ofExpChar`), and `FrobPow.pow` produces the prime-power exponents;
* the period functional equation `(t - θ^q)Ω^{(1)} = Ω` and `Ω ∈ ε` over `F₄((y))` and
  `F₉((y))`.
-/

set_option autoImplicit false
open Filter Polynomial RatFunc
open scoped WithZero Topology
open LaurentSeries HahnSeries

namespace ZagierHoffmanPositiveChar

/-- `FrobPow` over `F((y))` for the prime field `F₂`. -/
example : FrobPow (LaurentSeries (ZMod 2)) (Nat.card (ZMod 2)) := inferInstance

/-- `FrobPow` over `F((y))` for the prime field `F₃`. -/
example : FrobPow (LaurentSeries (ZMod 3)) (Nat.card (ZMod 3)) := inferInstance

/-- **`FrobPow` over `F₄((y))` — the previously inaccessible `q = 4` case.** -/
example : FrobPow (LaurentSeries (GaloisField 2 2)) (Nat.card (GaloisField 2 2)) := inferInstance

/-- **`FrobPow` over `F₉((y))` — the previously inaccessible `q = 9` case.** -/
example : FrobPow (LaurentSeries (GaloisField 3 2)) (Nat.card (GaloisField 3 2)) := inferInstance

/-- The `q`-th power map of `F₄((y))` is additive. -/
example (x y : LaurentSeries (GaloisField 2 2)) :
    (x + y) ^ (Nat.card (GaloisField 2 2))
      = x ^ (Nat.card (GaloisField 2 2)) + y ^ (Nat.card (GaloisField 2 2)) :=
  FrobPow.add_pow x y

/-- `CharP` plus primality gives `FrobPow` at every prime power (`FrobPow.of_charP`). -/
example : FrobPow (ZMod 2) (2 ^ 3) := FrobPow.of_charP (R := ZMod 2) (p := 2) 3

/-- And `x ↦ x ^ 8` is additive in `F₂`. -/
example (x y : ZMod 2) : (x + y) ^ (2 ^ 3) = x ^ (2 ^ 3) + y ^ (2 ^ 3) := by
  haveI := FrobPow.of_charP (R := ZMod 2) (p := 2) 3
  exact FrobPow.add_pow x y

/-- The classical case: `ExpChar R p` gives `FrobPow R p`. -/
example {R : Type*} [CommRing R] {p : ℕ} [ExpChar R p] : FrobPow R p := inferInstance

/-- **The period functional equation over `F₄((y))`** (the `q = 4` case). -/
example : (PowerSeries.X
      - PowerSeries.C ((periodTheta (GaloisField 2 2)) ^ periodCard (GaloisField 2 2)))
    * frobTwist (R := LaurentSeries (GaloisField 2 2)) (p := periodCard (GaloisField 2 2)) 1
        (periodOmega (GaloisField 2 2))
  = periodOmega (GaloisField 2 2) :=
  periodDatum_twist_L (GaloisField 2 2)

/-- **The period functional equation over `F₉((y))`** (the `q = 9` case). -/
example : (PowerSeries.X
      - PowerSeries.C ((periodTheta (GaloisField 3 2)) ^ periodCard (GaloisField 3 2)))
    * frobTwist (R := LaurentSeries (GaloisField 3 2)) (p := periodCard (GaloisField 3 2)) 1
        (periodOmega (GaloisField 3 2))
  = periodOmega (GaloisField 3 2) :=
  periodDatum_twist_L (GaloisField 3 2)

/-- **`Ω ∈ ε` over `F₄((y))`** — Chang's Lemma 5.3.1 for `q = 4`. -/
example : SuperEntire (periodOmega (GaloisField 2 2)) :=
  superEntire_periodOmega (GaloisField 2 2)

/-- **`Ω ∈ ε` over `F₉((y))`**. -/
example : SuperEntire (periodOmega (GaloisField 3 2)) :=
  superEntire_periodOmega (GaloisField 3 2)

/-- The concrete `L`-series `∑_i (Ω^2 · μ)^{(q^i)}` lies in `ε` over `F₄((y))`. -/
example : SuperEntire (atL1 (periodCard (GaloisField 2 2)) (periodOmega (GaloisField 2 2)) 2
    (PowerSeries.C (periodMu (GaloisField 2 2)))) :=
  superEntire_atL1_periodOmega_mu (GaloisField 2 2) 2

end ZagierHoffmanPositiveChar
