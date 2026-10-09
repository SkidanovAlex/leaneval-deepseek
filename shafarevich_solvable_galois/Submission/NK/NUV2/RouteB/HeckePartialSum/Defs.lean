import Mathlib
import Submission.NK.HeckeL.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The congruence idèles of a modulus: definitions for the partial-sum bound

This file fixes the vocabulary for the proof of
`NK.NUV2.RouteB.heckePartialSum_ne_one`: the modulus of an open subgroup `U ≤ 𝕀 K` is a
finitely supported function `m : HeightOneSpectrum (𝓞 K) → ℕ`, and an idèle is *congruent to `1`
modulo `m`* if it is a local unit at every finite place, congruent to `1` modulo the `m 𝔮`-th power
of the maximal ideal at the finite place `𝔮`, and positive at every real place.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain
open scoped NumberField

noncomputable section

namespace NK.NUV2.RouteB

variable (K : Type) [Field K] [NumberField K]

/-- A modulo function on the primes of `𝓞 K` has **finite support**: it vanishes at all but
finitely many primes.  These are the moduli occurring in the theory. -/
def HasFiniteSupport (m : HeightOneSpectrum (RingOfIntegers K) → ℕ) : Prop :=
  ∀ᶠ q in Filter.cofinite, m q = 0

/-- A local unit `x` of the completion `K_𝔮` is `1` modulo the `n`-th power of the maximal ideal:
`x - 1 ∈ 𝔮^n`, expressed through the valuation `Valued.v` (which is order-reversing, so this is
`v (x - 1) ≤ v (π^n)`). -/
def IsCongAt (m : HeightOneSpectrum (RingOfIntegers K) → ℕ)
    (q : HeightOneSpectrum (RingOfIntegers K)) (x : (q.adicCompletion K)ˣ) : Prop :=
  Valued.v ((x : q.adicCompletion K) - 1) ≤ WithZero.exp (-(m q : ℤ))

/-- An idèle is **congruent to `1` modulo the modulus `m`**: a local unit at each finite place,
`1` modulo `m 𝔮` at the finite place `𝔮`, and positive at each real place (no condition at the
complex places). -/
def IsCongIdeles (m : HeightOneSpectrum (RingOfIntegers K) → ℕ) (x : NK.GlobalCFT.Idele K) : Prop :=
  (∀ q : HeightOneSpectrum (RingOfIntegers K),
      x (NK.GlobalCFT.Place.ofFinite q) ∈ NK.GlobalCFT.Place.localUnits K
        (NK.GlobalCFT.Place.ofFinite q) ∧ IsCongAt K m q (x (NK.GlobalCFT.Place.ofFinite q)))
  ∧ (∀ (w : InfinitePlace K) (hw : w.IsReal),
      0 < (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw)
        ((x (NK.GlobalCFT.Place.ofInfinite w) : w.Completion)))

/-- Two elements of `K` are congruent modulo the modulus `m`. -/
def CongMod (m : HeightOneSpectrum (RingOfIntegers K) → ℕ) (α β : K) : Prop :=
  ∀ q : HeightOneSpectrum (RingOfIntegers K),
    Valued.v (algebraMap K (q.adicCompletion K) (α - β)) ≤ WithZero.exp (-(m q : ℤ))

/-- An element of `Kˣ` (or of `𝓞 K`) is a unit modulo the modulus `m`: it has valuation `1` at
every prime dividing the modulus. -/
def CoprimeMod (m : HeightOneSpectrum (RingOfIntegers K) → ℕ) (α : K) : Prop :=
  ∀ q : HeightOneSpectrum (RingOfIntegers K), m q ≠ 0 →
    Valued.v (algebraMap K (q.adicCompletion K) α) = 1

/-- The set of moduli: finitely supported functions `HeightOneSpectrum (𝓞 K) → ℕ`. -/
def IsModulus (m : HeightOneSpectrum (RingOfIntegers K) → ℕ) : Prop := HasFiniteSupport K m

end NK.NUV2.RouteB
