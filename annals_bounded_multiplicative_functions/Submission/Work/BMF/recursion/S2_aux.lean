import Mathlib
import Submission.Work.BMF.recursion.Defs
import Submission.Work.BMF.recursion.powerSums_perm

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Auxiliary objects for the count `S2pair ≤ k⁴ · Tdbl`

This file collects the finsets and the elementary bridge lemmas used in
`Work.BMF.recursion.S2_le_k4_Tdbl` (Wooley, Michigan Math. J. **40** (1993), 175–180, §2).

* `S2QPairs k` is the set of ordered pairs of ordered pairs of head indices, one ordered pair
  `(i,j)` with `i ≠ j` for each of the two tuples of a matching pair;
* `S2coll S k Q hkS i j i' j'` is the set of matching pairs whose head collides at `(i,j)` on the
  first side and at `(i',j')` on the second side; its cardinality is `Tij S k Q hk hkS i j i' j'`;
* `S2Tset S k Q hk hkS` is `S2coll` at the two *distinguished* head coordinates on each side; its
  cardinality is `Tdbl S k Q hk hkS`;
* `S2set S k Q hkS` is the set of matching pairs whose head is *non*-distinct on both sides; its
  cardinality is `S2pair S k Q hkS`.
-/

set_option autoImplicit false

namespace Work.BMF.recursion

open Finset
open scoped BigOperators

noncomputable section

/-- The `i`-th head index is injective as a function of `i`. -/
lemma hIdx_injective {k S : ℕ} (h : k ≤ S) : Function.Injective (hIdx h : Fin k → Fin S) :=
  fun a b hab => Fin.ext (by simpa [hIdx] using congrArg Fin.val hab)

/-- Distinct head indices stay distinct. -/
lemma hIdx_ne {k S : ℕ} (h : k ≤ S) {a b : Fin k} (hab : a ≠ b) : hIdx h a ≠ hIdx h b :=
  fun hc => hab (hIdx_injective h hc)

/-- Ordered pairs of ordered pairs of *distinct* head indices: one ordered pair `(i,j)` with
`i ≠ j` for each of the two tuples of a matching pair. -/
def S2QPairs (k : ℕ) : Finset ((Fin k × Fin k) × (Fin k × Fin k)) := by
  classical
  exact Finset.univ.filter (fun q => q.1.1 ≠ q.1.2 ∧ q.2.1 ≠ q.2.2)

/-- Matching pairs whose head collides at the prescribed coordinates on each side. -/
def S2coll (S k Q : ℕ) (hkS : k ≤ S) (i j i' j' : Fin k) : Finset (PairSpace S Q) := by
  classical
  exact (solSet S k Q).filter (fun p => p.1 (hIdx hkS i) = p.1 (hIdx hkS j) ∧
    p.2 (hIdx hkS i') = p.2 (hIdx hkS j'))

/-- `S2coll` at the two *distinguished* head coordinates on each side. -/
def S2Tset (S k Q : ℕ) (hk : 2 ≤ k) (hkS : k ≤ S) : Finset (PairSpace S Q) := by
  classical
  exact (solSet S k Q).filter (fun p =>
    p.1 (hIdx hkS (i0 k hk)) = p.1 (hIdx hkS (i1 k hk)) ∧
    p.2 (hIdx hkS (i0 k hk)) = p.2 (hIdx hkS (i1 k hk)))

/-- Matching pairs whose head is *non*-distinct on both sides. -/
def S2set (S k Q : ℕ) (hkS : k ≤ S) : Finset (PairSpace S Q) := by
  classical
  exact (solSet S k Q).filter (fun p => ¬ HD hkS p.1 ∧ ¬ HD hkS p.2)

/-- The cardinality of `S2coll` is `Tij`. -/
lemma S2coll_card_eq_Tij (S k Q : ℕ) (hk : 2 ≤ k) (hkS : k ≤ S) (i j i' j' : Fin k) :
    (S2coll S k Q hkS i j i' j').card = Tij S k Q hk hkS i j i' j' := by
  classical
  simp only [S2coll, Tij]

/-- The cardinality of `S2Tset` is `Tdbl`. -/
lemma S2Tset_card_eq_Tdbl (S k Q : ℕ) (hk : 2 ≤ k) (hkS : k ≤ S) :
    (S2Tset S k Q hk hkS).card = Tdbl S k Q hk hkS := by
  classical
  simp only [S2Tset, Tdbl, solSet, Finset.filter_filter]

/-- The cardinality of `S2set` is `S2pair`. -/
lemma S2set_card_eq_S2pair (S k Q : ℕ) (hkS : k ≤ S) :
    (S2set S k Q hkS).card = S2pair S k Q hkS := by
  classical
  simp only [S2set, S2pair]

/-- Membership in `S2set`. -/
lemma mem_S2set {S k Q : ℕ} {hkS : k ≤ S} {p : PairSpace S Q} :
    p ∈ S2set S k Q hkS ↔ p ∈ solSet S k Q ∧ ¬ HD hkS p.1 ∧ ¬ HD hkS p.2 := by
  classical
  simp only [S2set, Finset.mem_filter]

/-- Membership in `S2coll`. -/
lemma mem_S2coll {S k Q : ℕ} {hkS : k ≤ S} {i j i' j' : Fin k} {p : PairSpace S Q} :
    p ∈ S2coll S k Q hkS i j i' j' ↔ p ∈ solSet S k Q ∧
      p.1 (hIdx hkS i) = p.1 (hIdx hkS j) ∧ p.2 (hIdx hkS i') = p.2 (hIdx hkS j') := by
  classical
  simp only [S2coll, Finset.mem_filter]

/-- The matching condition `Matches` is invariant under a permutation of the coordinates, applied
independently to the two sides. -/
lemma Matches_comp_perm {S k Q : ℕ} (σ τ : Equiv.Perm (Fin S)) {p : PairSpace S Q}
    (hp : Matches S k Q p) :
    Matches S k Q ((fun s => p.1 (σ s)), (fun s => p.2 (τ s))) := by
  have hpw : Submission.Vinogradov.powerSums k p.1 = Submission.Vinogradov.powerSums k p.2 :=
    (Submission.Vinogradov.powerSums_eq_iff_matches p.1 p.2).mpr hp
  refine (Submission.Vinogradov.powerSums_eq_iff_matches _ _).mp ?_
  rw [powerSums_perm k S Q σ p.1, powerSums_perm k S Q τ p.2]
  exact hpw

/-- Membership in `S2Tset`. -/
lemma mem_S2Tset {S k Q : ℕ} {hk : 2 ≤ k} {hkS : k ≤ S} {p : PairSpace S Q} :
    p ∈ S2Tset S k Q hk hkS ↔ p ∈ solSet S k Q ∧
      p.1 (hIdx hkS (i0 k hk)) = p.1 (hIdx hkS (i1 k hk)) ∧
      p.2 (hIdx hkS (i0 k hk)) = p.2 (hIdx hkS (i1 k hk)) := by
  classical
  simp only [S2Tset, Finset.mem_filter]

/-- Membership in `S2QPairs`. -/
lemma mem_S2QPairs {k : ℕ} {q : (Fin k × Fin k) × (Fin k × Fin k)} :
    q ∈ S2QPairs k ↔ q.1.1 ≠ q.1.2 ∧ q.2.1 ≠ q.2.2 := by
  classical
  simp only [S2QPairs, Finset.mem_filter, Finset.mem_univ, true_and]

end

end Work.BMF.recursion
