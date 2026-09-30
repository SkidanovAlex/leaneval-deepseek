import Mathlib
import Submission.Work.BMF.recursion.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

/-!
# Auxiliary objects for the second Hölder step of the Vinogradov–Linnik recursion

This file collects the objects used in `Work.BMF.recursion.I1_le_I2`:

* `i1Set S k Q p hkS` is the set of `S`-tuples in `[1,Q]` whose head (the first `k` coordinates)
  is pairwise distinct modulo `p`;
* `i2Set S k Q p y hkS` is the subset of `i1Set` whose remaining `S-k` coordinates are all
  `≡ y (mod p)`;
* `Gw p k Q` is the "head" Weyl factor `Σ_{a ∈ Ahead p k Q} e(θ · moments a)`, where `Ahead` is the
  set of `k`-tuples in `[1,Q]` with pairwise distinct residues modulo `p`;
* `F1 S k Q p hkS` and `F2 S k Q p y hkS` are the exponential sums over `i1Set` and `i2Set`.

The counting functions `I1` and `I2` of `Defs.lean` are the `L²` mean squares of `F1` and `F2`;
the two companion lemmas `I1_eq_pairCard`, `I2_eq_pairCard` record the purely combinatorial part of
that identity, namely that `I1` (resp. `I2 y`) counts the pairs of elements of `i1Set` (resp.
`i2Set`) with equal moment vectors.
-/

namespace Work.BMF.recursion

open scoped BigOperators

noncomputable section

/-- The `S`-tuples in `[1,Q]` whose head is pairwise distinct modulo `p`. -/
def i1Set (S k Q p : ℕ) (hkS : k ≤ S) : Finset (Tup S Q) := by
  classical
  exact Finset.univ.filter (fun x => HDp p k hkS x)

/-- The `S`-tuples in `[1,Q]` whose head is pairwise distinct modulo `p` and all of whose tail
coordinates are `≡ y (mod p)`. -/
def i2Set (S k Q p y : ℕ) (hkS : k ≤ S) : Finset (Tup S Q) := by
  classical
  exact (i1Set S k Q p hkS).filter (fun x => TailEq p hkS y x)

/-- The "head" Weyl factor `G(θ) = Σ_{a ∈ Ahead} e(θ · moments a)`. -/
def Gw (p k Q : ℕ) : UnitAddTorus (Fin (k + 1)) → ℂ :=
  fun θ => ∑ a ∈ Ahead p k Q, UnitAddTorus.mFourier (Submission.Vinogradov.powerSums k a) θ

/-- The exponential sum over `i1Set`: `θ ↦ Σ_{x ∈ i1Set} e(θ · moments x)`. -/
def F1 (S k Q p : ℕ) (hkS : k ≤ S) : UnitAddTorus (Fin (k + 1)) → ℂ :=
  fun θ => ∑ x ∈ i1Set S k Q p hkS,
    UnitAddTorus.mFourier (Submission.Vinogradov.powerSums k x) θ

/-- The exponential sum over `i2Set`. -/
def F2 (S k Q p y : ℕ) (hkS : k ≤ S) : UnitAddTorus (Fin (k + 1)) → ℂ :=
  fun θ => ∑ x ∈ i2Set S k Q p y hkS,
    UnitAddTorus.mFourier (Submission.Vinogradov.powerSums k x) θ

/-- The pairs of elements of a set `s ⊆ [1,Q]^S` with equal moment vectors. -/
def pairMomSet (S k Q : ℕ) (s : Finset (Tup S Q)) : Finset (Tup S Q × Tup S Q) := by
  classical
  exact (s.product s).filter
    (fun q => Submission.Vinogradov.powerSums k q.1 = Submission.Vinogradov.powerSums k q.2)

/-- The combinatorial content of the mean-value identity for `I1`. -/
theorem I1_eq_pairCard (S k Q p : ℕ) (hkS : k ≤ S) :
    I1 S k Q p hkS = (pairMomSet S k Q (i1Set S k Q p hkS)).card := by
  classical
  have hset : (solSet S k Q).filter (fun q : PairSpace S Q => HDp p k hkS q.1 ∧ HDp p k hkS q.2)
      = pairMomSet S k Q (i1Set S k Q p hkS) := by
    ext q
    simp only [pairMomSet, solSet, i1Set, Finset.mem_filter, Finset.product_eq_sprod,
      Finset.mem_product, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hm, h1, h2⟩
      exact ⟨⟨h1, h2⟩, (Submission.Vinogradov.powerSums_eq_iff_matches q.1 q.2).mpr hm⟩
    · rintro ⟨⟨h1, h2⟩, hp⟩
      exact ⟨(Submission.Vinogradov.powerSums_eq_iff_matches q.1 q.2).mp hp, h1, h2⟩
  unfold I1
  rw [hset]

/-- The combinatorial content of the mean-value identity for `I2`. -/
theorem I2_eq_pairCard (S k Q p y : ℕ) (hkS : k ≤ S) :
    I2 S k Q p y hkS = (pairMomSet S k Q (i2Set S k Q p y hkS)).card := by
  classical
  have hset : (solSet S k Q).filter (fun q : PairSpace S Q =>
        HDp p k hkS q.1 ∧ HDp p k hkS q.2 ∧ TailEq p hkS y q.1 ∧ TailEq p hkS y q.2)
      = pairMomSet S k Q (i2Set S k Q p y hkS) := by
    ext q
    simp only [pairMomSet, solSet, i2Set, i1Set, Finset.mem_filter, Finset.product_eq_sprod,
      Finset.mem_product, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hm, h1, h2, t1, t2⟩
      exact ⟨⟨⟨h1, t1⟩, h2, t2⟩, (Submission.Vinogradov.powerSums_eq_iff_matches q.1 q.2).mpr hm⟩
    · rintro ⟨⟨⟨h1, t1⟩, h2, t2⟩, hp⟩
      exact ⟨(Submission.Vinogradov.powerSums_eq_iff_matches q.1 q.2).mp hp, h1, h2, t1, t2⟩
  unfold I2
  rw [hset]

end

end Work.BMF.recursion
