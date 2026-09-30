import Mathlib
import Submission.Work.BMF.recursion.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Moment vectors of `[0,X]`-tuples

The tails of the recursion are parametrised by tuples `U` with entries in `[0, X]`
(`U r = (tail r - y)/p`), and the relevant quantity for the counting argument is the
vector of power sums of degrees `1, …, k` of `U`, indexed by `Fin k`.

This module contains only definitions (no proofs), so that lemmas about `momVec` can be
delegated without importing the (still incomplete) recursion development.
-/

set_option autoImplicit false

namespace Work.BMF.recursion

open Finset
open scoped BigOperators

noncomputable section

/-- `s`-tuples with entries in `[0,X]`. -/
abbrev UTup (s X : ℕ) : Type := Fin s → Finset.Icc 0 X

/-- The moment vector of a `U`-tuple: the power sums of degrees `1, …, k`, indexed by `Fin k`. -/
def momVec (k : ℕ) {s X : ℕ} (u : UTup s X) : Fin k → ℤ :=
  fun j => ∑ r, ((u r).1 : ℤ) ^ (j.1 + 1)

/-- The moment vector of a head tuple `m`, shifted by `y`: `Σᵢ (mᵢ - y)^(j+1)`. -/
def hMom (k y : ℕ) {Q : ℕ} (m : Tup k Q) : Fin k → ℤ :=
  fun j => ∑ i, (((m i).1 : ℤ) - (y : ℤ)) ^ (j.1 + 1)


/-- The head of an `S`-tuple: its first `k` coordinates (for `k ≤ S`). -/
def hdT {k S Q : ℕ} (hkS : k ≤ S) (x : Tup S Q) : Tup k Q := fun i => x (hIdx hkS i)

/-- The tail of an `S`-tuple: its last `S - k` coordinates (for `k ≤ S`). -/
def tlT {k S Q : ℕ} (hkS : k ≤ S) (x : Tup S Q) : Tup (S - k) Q := fun r => x (tIdx hkS r)

/-- The inverse of `x ↦ (hdT x, tlT x)`: reassemble a tuple from its head and tail. -/
def zipT {k S Q : ℕ} (hkS : k ≤ S) (q : Tup k Q × Tup (S - k) Q) : Tup S Q :=
  fun i => if h : i.1 < k then q.1 ⟨i.1, h⟩ else q.2 ⟨i.1 - k, by omega⟩

/-- The `U`-tuple attached to a tail tuple: `U r = ((t r) : ℕ) / p`. -/
def uOf (p : ℕ) {s Q : ℕ} (t : Tup s Q) : Fin s → ℕ := fun r => (t r).1 / p

/-- Head tuples whose entries are pairwise distinct modulo `p`. -/
def Hset (p k Q : ℕ) : Finset (Tup k Q) := by
  classical
  exact Finset.univ.filter (fun a => HDp p k (le_refl k) a)

/-- The set of tail tuples all of whose entries are `≡ y (mod p)`. -/
def Tails (p y : ℕ) {s Q : ℕ} (t : Tup s Q) : Prop := ∀ r : Fin s, (t r).1 % p = y % p

/-- Tail tuples with all entries `≡ y (mod p)`. -/
def Tset (p y s Q : ℕ) : Finset (Tup s Q) := by
  classical
  exact Finset.univ.filter (Tails p y)

end

end Work.BMF.recursion
