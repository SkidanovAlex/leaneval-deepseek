/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Herbrand function in towers

For a tower `K ⊆ M ⊆ L` of fields with valuation rings `A_M ⊆ A = A_M`-over-`M`-lying-over, the
ramification filtration of `L/K` is related to those of `L/M` and `M/K` by

* the **restriction** identity `G_i(L/K) ∩ Gal(L/M) = G_i(L/M)` — in the formalisation of
  `Submission/Work/Ramification/Defs.lean` this is a statement about the *same* maximal ideal
  `𝔪_A`, so it is insensitive to the normalisation of the valuation;
* the **multiplicativity of the Herbrand function** `φ_{L/K} = φ_{M/K} ∘ φ_{L/M}`
  (Serre, *Local Fields*, IV §3, Prop. 15), for `M/K` Galois.

The herringbone of the classical theory is that the *upper* numbering is compatible with quotients
(Serre IV §3 Prop 15) while the *lower* numbering is compatible with subgroups; the multiplicativity
of `φ` is exactly the bookkeeping that converts between the two.  This file records the rational
Herbrand function `herbrandRat` (the piecewise-linear function of which `herbrand` is the restriction
to the integers) and states the multiplicativity as the named proposition
`HerbrandMultiplicativity`; the classical theorem itself is *not* proved here.

The restriction identity is not formalised as a lemma either: comparing `G_i(L/M) ⊆ Gal(L/M)` with
`G_i(L/K) ⊆ Gal(L/K)` requires transporting along `IntermediateField.fixingSubgroupEquiv`
(`Gal(L/M) ≃* M.fixingSubgroup ≤ Gal(L/K)`), and the two subgroups live in different ambient groups,
so the statement is comparatively inelegant in this framework even though its proof is short.
Both gaps are recorded in `Submission/Work/Ramification/README.md`.
-/
import Submission.NK.Ramification.Defs
import Submission.NK.Ramification.Herbrand
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical

namespace NK.Ramification

universe u

noncomputable section

variable {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]

/-- **The Herbrand function on rational arguments**: the piecewise-linear function

  `φ(u) = (g_0 + ⋯ + g_{⌊u⌋-1} + (u - ⌊u⌋)·g_{⌊u⌋}) / g_0`,

whose restriction to `ℕ` is `NK.Ramification.herbrand`. -/
def herbrandRat (A : ValuationSubring L) (u : ℚ) : ℚ :=
  ((Finset.range ⌊u⌋₊).sum (fun j => (lowerIndex (K := K) A j : ℚ)) +
      (u - (⌊u⌋₊ : ℚ)) * (lowerIndex (K := K) A ⌊u⌋₊ : ℚ)) /
    (lowerIndex (K := K) A 0 : ℚ)

/-- The Herbrand function on `ℕ` is the restriction of the rational Herbrand function. -/
theorem herbrandRat_natCast (A : ValuationSubring L) (n : ℕ) :
    herbrandRat (K := K) A n = herbrand (K := K) A n := by
  simp [herbrandRat, herbrand, Nat.floor_nat]

/-- **Multiplicativity of the Herbrand function in towers** (Serre, *Local Fields*, IV §3, Prop. 15):
for `M` an intermediate field with `M/K` Galois and `A_M = A ∩ M` the induced valuation ring,

  `φ_{L/K}(u) = φ_{M/K}(φ_{L/M}(u))`   for all `u : ℚ`,

i.e. the Herbrand function of `L/K` is the composite of the Herbrand functions of `L/M` and `M/K`.

The valuation ring of `M` is `A_M = A ∩ M = A.comap (algebraMap M L)`: with an *arbitrary* second
valuation ring `A_M` the statement is false (take `M = L` and two different `A_M`).  The hypothesis
`M/K` Galois is the classical one (Serre IV §3 Prop. 15); without it the quotient statement used in
the proof fails.

This is the bookkeeping that makes the upper numbering compatible with quotients, and is a
consequence of the *index* multiplicativity `g_i(L/K) = g_i(L/M)·g_i(M/K)` together with the
compatibility of the lower numbering with the subgroup `Gal(L/M) ≤ Gal(L/K)`. -/
def HerbrandMultiplicativity (A : ValuationSubring L) (M : IntermediateField K L)
    [Algebra ↥M L] [IsScalarTower K ↥M L] [IsGalois K ↥M] : Prop :=
  ∀ u : ℚ, herbrandRat (K := K) A u =
    herbrandRat (K := K) (A.comap (algebraMap ↥M L))
      (herbrandRat (K := ↥M) A u)

end

end NK.Ramification
