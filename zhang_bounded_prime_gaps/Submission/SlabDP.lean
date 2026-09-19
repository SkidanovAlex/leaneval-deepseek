import Mathlib
import Submission.S2Reduction

open scoped BigOperators
open Finset

/-!
# The Slab DP engine (module 1 of the certificate's computation)

The certificate's arithmetic needs the table `Ssum α β 50` over the `272²` even-part signatures
of degree ≤ 24.  The definitional recursion in `Submission/Variational.lean` is exponential in
`k`; this module sets up the equivalent *level* form on multiplicity vectors

  `w_{k+1} = slabStep w_k`,   `w_0 = δ_{(∅,∅)}`,

with `slabStep` the "remove one part from each side (or nothing), weight `(p+q)!`" operator.
`slabStep` is a plain finite sum of shifted values, hence *memoizable*: iterating it 50 times
against a table indexed by the `272²` states is the engine of the computation.

Planned next pieces (see the roadmap §20):
* the bridge `Ssum β β' k = (the level-k value at the multiplicity vector of (β,β'))`
  (induction on `k`, matching the recursion of `Variational.Ssum`);
* the state enumeration `D2` of `Submission/PairIndexEnum.lean` as the table index;
* the per-chunk evaluation modules (each a `decide`-checked `List` fold over a slice of the
  `50 × 272²` grid) to be split across the fleet.
-/

namespace Commons.NumberTheory.MaynardSieve

/-- The multiplicity vector of a single part: the part of index `p` is `2(p+1)`. -/
def indPart (p : Fin 12) : Fin 12 → ℕ := fun i => if i = p then 1 else 0

/-- One level of the DP: from the values at level `k` produce the values at level `k+1`,
removing from each side either nothing or one occurrence of a part that is present, with the
weight `(part p + part q)!`; the parts are `2,4,…,24` (index `p ↦ 2(p+1)`). -/
def slabStep (f : (Fin 12 → ℕ) → (Fin 12 → ℕ) → ℕ) (m n : Fin 12 → ℕ) : ℕ :=
  f m n
  + (∑ p : Fin 12, if 0 < m p then (Nat.factorial (2 * ((p : ℕ) + 1))) * f (m - indPart p) n else 0)
  + (∑ q : Fin 12, if 0 < n q then (Nat.factorial (2 * ((q : ℕ) + 1))) * f m (n - indPart q) else 0)
  + (∑ p : Fin 12, ∑ q : Fin 12,
      if 0 < m p ∧ 0 < n q then
        (Nat.factorial (2 * ((p : ℕ) + 1) + 2 * ((q : ℕ) + 1))) * f (m - indPart p) (n - indPart q)
      else 0)

/-- The base level: `1` at the origin, `0` elsewhere. -/
def slabBase (m n : Fin 12 → ℕ) : ℕ := if m = 0 ∧ n = 0 then 1 else 0

/-- The level-`k` table. -/
def slabLevel : ℕ → (Fin 12 → ℕ) → (Fin 12 → ℕ) → ℕ
  | 0 => slabBase
  | (k + 1) => slabStep (slabLevel k)

@[simp] lemma slabStep_zero (m n : Fin 12 → ℕ) : slabStep (fun _ _ => 0) m n = 0 := by
  simp [slabStep]

@[simp] lemma slabLevel_zero (m n : Fin 12 → ℕ) : slabLevel 0 m n = slabBase m n := rfl

/-- The level-`1` value at a state: `(p+q)!` for the single-removal pairs, `1` at the origin. -/
lemma slabLevel_one (m n : Fin 12 → ℕ) :
    slabLevel 1 m n =
      slabBase m n
      + (∑ p : Fin 12, if 0 < m p then (Nat.factorial (2 * ((p : ℕ) + 1))) * slabBase (m - indPart p) n else 0)
      + (∑ q : Fin 12, if 0 < n q then (Nat.factorial (2 * ((q : ℕ) + 1))) * slabBase m (n - indPart q) else 0)
      + (∑ p : Fin 12, ∑ q : Fin 12,
          if 0 < m p ∧ 0 < n q then
            (Nat.factorial (2 * ((p : ℕ) + 1) + 2 * ((q : ℕ) + 1))) * slabBase (m - indPart p) (n - indPart q)
          else 0) := rfl

end Commons.NumberTheory.MaynardSieve
