import Mathlib
import Submission.Chen.SwitchDefs

open Finset
open scoped BigOperators

namespace Work.NumberTheory.Chen.BTermCount

open Commons.NumberTheory.Chen.ChenEight

attribute [local instance] Classical.propDecidable

/-!
# The `B`-term of Chen's argument: definitions

This module sets up the vocabulary of the `B`-term, the third piece of Chen's switching
decomposition (`Submission.Chen.SwitchDefs`):

* `IsBTriple x M Y t` is the predicate on a triple `t = (q, q₂, q₃)` of natural numbers
  saying that all three are prime, `M ≤ q < Y ≤ q₂ ≤ q₃` and `q q₂ q₃ ≤ x + 2`;
* `bTripleSet x M Y` is the (finite) set of such triples, `bTripleCount x M Y` its
  cardinality — the number of *triples* rather than of primes;
* `bProdSet x M Y` is the set of products `q q₂ q₃` of such triples (i.e. the set `B̄`);
* `bTermSet x M Y` is the set of primes `p` counted by `Submission.bTermCount`
  (so that `Submission.bTermCount x M Y = (bTermSet x M Y).card` is `rfl`);
* `survivorSet x M Y` is the set of products `n ∈ bProdSet x M Y` such that `n - 2` is
  coprime to every odd prime `< Y`: the elements of the sieve sequence which survive
  sieving by `P(Y)`.  Every `p` counted by `bTermCount` with `p ≥ Y` maps into it.

The elementary layer (`Basic.lean`) proves the reductions
`bTermCount ≤ bTripleCount` and `bTermCount ≤ #(survivorSet) + Y`.
-/

/-- The predicate defining a `B`-term triple `(q, q₂, q₃)`. -/
def IsBTriple (x M Y : ℕ) (t : ℕ × ℕ × ℕ) : Prop :=
  t.1.Prime ∧ t.2.1.Prime ∧ t.2.2.Prime ∧ M ≤ t.1 ∧ t.1 < Y ∧ Y ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 ∧
    t.1 * t.2.1 * t.2.2 ≤ x + 2

/-- The predicate defining a `B`-term prime `p`: `p ∈ s0Set x M` and `p + 2` is a product
of three primes, the smallest one in `[M, Y)` and the other two `≥ Y`. -/
def IsBTerm (x M Y : ℕ) (p : ℕ) : Prop :=
  p ∈ Submission.s0Set x M ∧
    ∃ q q₂ q₃ : ℕ, q.Prime ∧ q₂.Prime ∧ q₃.Prime ∧ M ≤ q ∧ q < Y ∧ Y ≤ q₂ ∧ q₂ ≤ q₃ ∧
      p + 2 = q * q₂ * q₃

/-- The set of `B`-term triples: primes `q < Y ≤ q₂ ≤ q₃` with `M ≤ q` and `q q₂ q₃ ≤ x + 2`. -/
noncomputable def bTripleSet (x M Y : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (((Finset.Icc 2 (Y - 1)) ×ˢ (Finset.Icc 2 (x + 2) ×ˢ Finset.Icc 2 (x + 2)))).filter
    (IsBTriple x M Y)

/-- The number of `B`-term triples. -/
noncomputable def bTripleCount (x M Y : ℕ) : ℕ := (bTripleSet x M Y).card

/-- The set `B̄` of products `q q₂ q₃` over `B`-term triples. -/
noncomputable def bProdSet (x M Y : ℕ) : Finset ℕ :=
  (bTripleSet x M Y).image (fun t => t.1 * t.2.1 * t.2.2)

/-- The number of elements of `B̄`. -/
noncomputable def bProdCount (x M Y : ℕ) : ℕ := (bProdSet x M Y).card

/-- The set of primes counted by `Submission.bTermCount x M Y`. -/
noncomputable def bTermSet (x M Y : ℕ) : Finset ℕ :=
  (Submission.s0Set x M).filter (fun p => ∃ q q₂ q₃ : ℕ, q.Prime ∧ q₂.Prime ∧ q₃.Prime ∧
      M ≤ q ∧ q < Y ∧ Y ≤ q₂ ∧ q₂ ≤ q₃ ∧ p + 2 = q * q₂ * q₃)

/-- The **sieve survivors**: elements `n` of `B̄` such that `n - 2` is coprime to every odd
prime `< Y`.  These are the elements of the `B`-term sieve sequence `n ↦ n - 2` that pass
the sieve with modulus `P(Y)`. -/
noncomputable def survivorSet (x M Y : ℕ) : Finset ℕ :=
  (bProdSet x M Y).filter (fun n => ∀ q ∈ oddLt Y, ¬ q ∣ n - 2)

/-- The number of sieve survivors. -/
noncomputable def survivorCount (x M Y : ℕ) : ℕ := (survivorSet x M Y).card

@[simp] theorem bTermCount_eq_card_bTermSet (x M Y : ℕ) :
    Submission.bTermCount x M Y = (bTermSet x M Y).card := rfl

theorem bTripleCount_eq_card (x M Y : ℕ) :
    bTripleCount x M Y = (bTripleSet x M Y).card := rfl

theorem survivorCount_eq_card (x M Y : ℕ) :
    survivorCount x M Y = (survivorSet x M Y).card := rfl

end Work.NumberTheory.Chen.BTermCount
