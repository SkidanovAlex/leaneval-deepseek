import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Degree of the radical of a monic polynomial over an algebraically closed field

For a monic polynomial `p` over an algebraically closed field, the radical of `p`
(the product of its distinct prime factors) has degree equal to the number of
distinct roots of `p`.

The proof proceeds as follows.  Write `r = radical p`.  Over an algebraically
closed field every polynomial splits, so `r.natDegree = r.roots.card`.  The
radical `r` is a product of distinct primes, hence squarefree, hence separable,
so `r.roots` is a multiset without duplicates and `r.roots.card =
r.roots.toFinset.card`.  Finally, an irreducible `X - C a` divides `r = radical p`
if and only if it divides `p`, which shows that `r` and `p` have the same roots,
i.e. `r.roots.toFinset = p.roots.toFinset`.
-/

open Polynomial

namespace Commons.FieldTheory.Polynomial

theorem natDegree_radical_eq_card_roots_toFinset {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]
    (p : Polynomial F) (hp : p.Monic) :
    (UniqueFactorizationMonoid.radical p).natDegree = p.roots.toFinset.card := by
  have hp0 : p ≠ 0 := hp.ne_zero
  set r := UniqueFactorizationMonoid.radical p
  have hr0 : r ≠ 0 := UniqueFactorizationMonoid.radical_ne_zero
  -- Every polynomial splits over an algebraically closed field.
  have hsplit : r.Splits := IsAlgClosed.splits r
  -- The radical is squarefree, hence separable, hence has distinct roots.
  have hnd : r.roots.Nodup := by
    have hsq : Squarefree r := UniqueFactorizationMonoid.squarefree_radical
    have hsep : Separable r := (PerfectField.separable_iff_squarefree).mpr hsq
    exact nodup_roots hsep
  -- `r` and `p` have the same roots.
  have htofinset : r.roots.toFinset = p.roots.toFinset := by
    ext a
    rw [Multiset.mem_toFinset, Multiset.mem_toFinset, mem_roots hr0, mem_roots hp0,
      ← dvd_iff_isRoot, ← dvd_iff_isRoot]
    exact UniqueFactorizationMonoid.dvd_radical_iff_of_irreducible (irreducible_X_sub_C a) hp0
  rw [hsplit.natDegree_eq_card_roots, ← Multiset.toFinset_card_of_nodup hnd, htofinset]

end Commons.FieldTheory.Polynomial