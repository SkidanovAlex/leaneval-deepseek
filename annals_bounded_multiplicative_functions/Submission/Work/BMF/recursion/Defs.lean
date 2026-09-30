import Mathlib
import Submission.Vinogradov.Orthogonality
import Submission.Vinogradov.Core

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Definitions for Wooley's Vinogradov–Linnik recursion step

This file collects the combinatorial and harmonic-analytic objects used in the proof of
`Work.BMF.recursion_step`, following Wooley, *On Vinogradov's mean value theorem II*,
Michigan Math. J. **40** (1993), 175–180, §2.

The recursion is
`J_{s,k}(X) ≤ (4k⁴)^s + 4·k!·|P|²·Y^{2s-2k+k(k-1)/2}·X^k·J_{s-k,k}(1+X/M)`.

* `Tup s X` is the set of `s`-tuples with entries in `[1,X]`, and `Matches` is the
  Vinogradov matching condition (all power sums of degrees `≤ k` agree).
* `HD h x` says the "head" (the first `k` coordinates of `x`, `k ≤ S`) are pairwise
  distinct as integers, `HDp p h x` says they are pairwise distinct mod `p`, and
  `TailEq p h y x` says every one of the remaining `S-k` coordinates is `≡ y (mod p)`.
* `fib h` is the fibre of the moment map `powerSums k` over `h`, `R1`, `R2`, `R01` are
  its cardinalities intersected with the conditions above (Wooley's `R₁(h)`, `R₂(h)` and
  the fibre of the "`x₁ = x₂`" set), and `Jsum`, `S1sum`, `S2sum` are
  `Σ_h (fib h).card²`, `Σ_h R1(h)²`, `Σ_h R2(h)²`.
* `Tdbl` is the number of matching pairs with the two first coordinates equal on both
  sides; it is the quantity bounded by the first Hölder step.
* `Ahead p Q k` is the set of head tuples with pairwise distinct residues mod `p`,
  `Weyl` the Weyl sum `Σ_{x ≤ X} e(θ·(1,x,…,x^k))`, and `WeylMod p y` the same sum
  restricted to `x ≡ y (mod p)`.
* `I1 p` and `I2 p y` are the counts of pairs with pairise distinct (mod `p`) heads and,
  respectively, arbitrary tails or tails all `≡ y (mod p)`.
-/

set_option autoImplicit false

namespace Work.BMF.recursion

open LeanEval.NumberTheory.VinogradovMeanValue
open scoped BigOperators

noncomputable section

/-- `s`-tuples of integers with entries in `[1,X]`. -/
abbrev Tup (s X : ℕ) := Fin s → Finset.Icc 1 X

/-- Pairs of `s`-tuples with entries in `[1,X]`. -/
abbrev PairSpace (s X : ℕ) := Tup s X × Tup s X

/-- The Vinogradov matching condition, degrees `≤ k`. -/
abbrev Matches (s k X : ℕ) (p : PairSpace s X) : Prop :=
  ∀ j ≤ k, ∑ i, (p.1 i).1 ^ j = ∑ i, (p.2 i).1 ^ j

/-- The full solution set counted by `J s k X`. -/
def solSet (s k X : ℕ) : Finset (PairSpace s X) := Finset.univ.filter (Matches s k X)

/-- The matching condition is symmetric. -/
lemma matches_symm {S k Q : ℕ} {p : PairSpace S Q} (h : Matches S k Q p) :
    Matches S k Q (p.2, p.1) := fun j hj => (h j hj).symm

/-- The moment vector of a single variable `x`, degrees `0,…,k` (`x^0 = 1`). -/
def mom1 (k : ℕ) (x : ℕ) : Fin (k + 1) → ℤ := fun j => (x : ℤ) ^ j.val

/-- The two distinguished list indices `0` and `1`. -/
def i0 (k : ℕ) (hk : 2 ≤ k) : Fin k := ⟨0, by omega⟩
def i1 (k : ℕ) (hk : 2 ≤ k) : Fin k := ⟨1, by omega⟩

/-- The `i`-th element of the "head" of a tuple of length `S`, for `k ≤ S`. -/
def hIdx {k S : ℕ} (h : k ≤ S) (i : Fin k) : Fin S := ⟨i.val, by omega⟩

/-- The `r`-th element of the "tail" of a tuple of length `S`, for `k ≤ S`. -/
def tIdx {k S : ℕ} (h : k ≤ S) (r : Fin (S - k)) : Fin S := ⟨k + r.val, by omega⟩

/-- The head of `x` is pairwise distinct as integers. -/
def HD {k S X : ℕ} (h : k ≤ S) (x : Tup S X) : Prop :=
  ∀ i j : Fin k, i ≠ j → x (hIdx h i) ≠ x (hIdx h j)

/-- The head of `x` is pairwise distinct modulo `p`. -/
def HDp (p k : ℕ) {S X : ℕ} (h : k ≤ S) (x : Tup S X) : Prop :=
  ∀ i j : Fin k, i ≠ j → ¬ (p : ℤ) ∣ (((x (hIdx h i)).1 : ℤ) - ((x (hIdx h j)).1 : ℤ))

/-- Every tail coordinate of `x` is congruent to `y` modulo `p`. -/
def TailEq (p : ℕ) {k S X : ℕ} (h : k ≤ S) (y : ℕ) (x : Tup S X) : Prop :=
  ∀ r : Fin (S - k), (x (tIdx h r)).1 % p = y % p

/-- The fibre of the moment map over `h`. -/
def fib (s k X : ℕ) (h : Fin (k + 1) → ℤ) : Finset (Tup s X) :=
  Finset.univ.filter (fun x => Submission.Vinogradov.powerSums k x = h)

/-- The image of the moment map. -/
def momImg (s k X : ℕ) : Finset (Fin (k + 1) → ℤ) :=
  Finset.univ.image (fun x : Tup s X => Submission.Vinogradov.powerSums k x)

/-- `R₁(h)`: the fibre at `h`, restricted to tuples whose head is distinct. -/
def R1 (S k Q : ℕ) {h : k ≤ S} (v : Fin (k + 1) → ℤ) : ℕ := by
  classical
  exact ((fib S k Q v).filter (fun x => HD h x)).card

/-- `R₂(h)`: the fibre at `h`, restricted to tuples whose head is *not* distinct. -/
def R2 (S k Q : ℕ) {h : k ≤ S} (v : Fin (k + 1) → ℤ) : ℕ := by
  classical
  exact ((fib S k Q v).filter (fun x => ¬ HD h x)).card

/-- `R₀₁(h)`: the fibre at `h`, restricted to tuples with `x₀ = x₁`. -/
def R01 (S k Q : ℕ) (hk : 2 ≤ k) (hkS : k ≤ S) (v : Fin (k + 1) → ℤ) : ℕ := by
  classical
  exact ((fib S k Q v).filter
    (fun x => x (hIdx hkS (i0 k hk)) = x (hIdx hkS (i1 k hk)))).card

/-- `Σ_h (fib h).card²`, which equals `J S k Q`. -/
def Jsum (S k Q : ℕ) : ℕ :=
  ∑ v ∈ momImg S k Q, (fib S k Q v).card ^ 2

/-- Wooley's `S₁ = Σ_h R₁(h)²`. -/
def S1sum (S k Q : ℕ) (hkS : k ≤ S) : ℕ :=
  ∑ v ∈ momImg S k Q, (R1 S k Q (h := hkS) v) ^ 2

/-- Wooley's `S₂ = Σ_h R₂(h)²`. -/
def S2sum (S k Q : ℕ) (hkS : k ≤ S) : ℕ :=
  ∑ v ∈ momImg S k Q, (R2 S k Q (h := hkS) v) ^ 2

/-- The number of matching pairs whose two first coordinates agree on *both* sides. -/
def Tdbl (S k Q : ℕ) (hk : 2 ≤ k) (hkS : k ≤ S) : ℕ := by
  classical
  exact ((Finset.univ : Finset (PairSpace S Q)).filter (fun p =>
    Matches S k Q p ∧ p.1 (hIdx hkS (i0 k hk)) = p.1 (hIdx hkS (i1 k hk)) ∧
      p.2 (hIdx hkS (i0 k hk)) = p.2 (hIdx hkS (i1 k hk)))).card

/-- Head tuples (length `k`) whose entries are pairwise distinct modulo `p`. -/
def Ahead (p k Q : ℕ) : Finset (Tup k Q) := by
  classical
  exact Finset.univ.filter (fun a => HDp p k (le_refl k) a)

/-- The number of matching pairs in both of whose tuples the head is distinct mod `p`. -/
def I1 (S k Q p : ℕ) (hkS : k ≤ S) : ℕ := by
  classical
  exact ((solSet S k Q).filter (fun q => HDp p k hkS q.1 ∧ HDp p k hkS q.2)).card

/-- The number of matching pairs with heads distinct mod `p` and every tail `≡ y (mod p)`,
on both sides. -/
def I2 (S k Q p y : ℕ) (hkS : k ≤ S) : ℕ := by
  classical
  exact ((solSet S k Q).filter (fun q => HDp p k hkS q.1 ∧ HDp p k hkS q.2 ∧
    TailEq p hkS y q.1 ∧ TailEq p hkS y q.2)).card

/-- The number of matching pairs whose power-sum *difference* on the two sides is the
prescribed vector `d` (used for the "zero representation dominates" step). -/
def Jdiff (m k X : ℕ) (d : Fin (k + 1) → ℤ) : ℕ := by
  classical
  exact ((Finset.univ : Finset (PairSpace m X)).filter (fun p =>
    Submission.Vinogradov.powerSums k p.1 - Submission.Vinogradov.powerSums k p.2 = d)).card

/-- The single-variable Weyl sum `Σ_{1 ≤ x ≤ X} e(θ₀ + θ₁x + ⋯ + θ_k x^k)`. -/
def Weyl (k X : ℕ) : UnitAddTorus (Fin (k + 1)) → ℂ :=
  Submission.Vinogradov.ExpSum (s := 1) (k := k) (X := X)

/-- The Weyl sum restricted to the residue class `y` modulo `p`. -/
def WeylMod (p k X y : ℕ) : UnitAddTorus (Fin (k + 1)) → ℂ :=
  ∑ x ∈ (Finset.Icc 1 X).filter (fun x => x % p = y % p),
    UnitAddTorus.mFourier (mom1 k x)

/-- The number of matching pairs in whose two tuples the head is distinct (as integers). -/
def S1pair (S k Q : ℕ) (hkS : k ≤ S) : ℕ := by
  classical
  exact ((solSet S k Q).filter (fun p => HD hkS p.1 ∧ HD hkS p.2)).card

/-- The number of matching pairs in whose two tuples the head is *not* distinct. -/
def S2pair (S k Q : ℕ) (hkS : k ≤ S) : ℕ := by
  classical
  exact ((solSet S k Q).filter (fun p => ¬ HD hkS p.1 ∧ ¬ HD hkS p.2)).card

/-- The number of matching pairs in which the head is non-distinct on exactly one side. -/
def mixedPair (S k Q : ℕ) (hkS : k ≤ S) : ℕ := by
  classical
  exact ((solSet S k Q).filter (fun p => (HD hkS p.1 ∧ ¬ HD hkS p.2) ∨
    (¬ HD hkS p.1 ∧ HD hkS p.2))).card

/-- The one-sided mixed count: matching pairs with a distinct head on the first side only. -/
def headMix (S k Q : ℕ) (hkS : k ≤ S) : ℕ := by
  classical
  exact ((solSet S k Q).filter (fun p => HD hkS p.1 ∧ ¬ HD hkS p.2)).card

/-- The other one-sided mixed count: matching pairs with a distinct head on the second side only. -/
def headMix2 (S k Q : ℕ) (hkS : k ≤ S) : ℕ := by
  classical
  exact ((solSet S k Q).filter (fun p => ¬ HD hkS p.1 ∧ HD hkS p.2)).card

/-- The set of tuples whose head is pairwise distinct. -/
def hdSet (S k Q : ℕ) (hkS : k ≤ S) : Finset (Tup S Q) := by
  classical
  exact Finset.univ.filter (fun x => HD hkS x)

/-- The set of tuples whose head is *not* pairwise distinct. -/
def nhdSet (S k Q : ℕ) (hkS : k ≤ S) : Finset (Tup S Q) := by
  classical
  exact Finset.univ.filter (fun x => ¬ HD hkS x)

/-- Tuples of length `S` in `[1,Q]` with two prescribed coordinates equal. -/
def eqPairSet (S k Q : ℕ) (hk : 2 ≤ k) (hkS : k ≤ S) (i j : Fin k) : Finset (Tup S Q) := by
  classical
  exact Finset.univ.filter (fun x => x (hIdx hkS i) = x (hIdx hkS j))

/-- The number of matching pairs in which the two tuples agree on two prescribed head coordinates
on both sides.  For the distinguished coordinates this is `Tdbl`. -/
def Tij (S k Q : ℕ) (hk : 2 ≤ k) (hkS : k ≤ S) (i j i' j' : Fin k) : ℕ := by
  classical
  exact ((solSet S k Q).filter (fun p => p.1 (hIdx hkS i) = p.1 (hIdx hkS j) ∧
    p.2 (hIdx hkS i') = p.2 (hIdx hkS j'))).card

end

end Work.BMF.recursion
