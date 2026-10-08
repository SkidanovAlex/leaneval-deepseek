/-
Area CORE4 of the Gorenstein--Walter project: vocabulary for the pure `A₇` fact `A4s`
(`Work.CORE4.A4s`, i.e. the design-pass-15 leaf `Work.CORE4.C15.A7S4ConjProp`).

## The statement

    A7S4ConjProp = ∀ (E) [Group E] [Finite E], Nonempty (E ≃* alternatingGroup (Fin 7)) →
      ∀ V : Subgroup E, IsFourGroup V → ∀ s ∈ normalizer (V : Set E), orderOf s = 2 →
        ∀ K : Subgroup E, K ≤ centralizer (V : Set E) → Nat.card K = 3 → Inverts s K →
          ∃ e : E, e * s = s * e ∧ conjSub e K ≤ normalizer (V : Set E) ∧ conjSub e K ≠ K

## How the proof goes

`IsFourGroup V` is `Nat.card V = 4 ∧ ∀ v ∈ V, v ^ 2 = 1` and `A₇` has exactly **two** classes of
four-groups, represented by the model subgroups `V1sub = ⟨t, u⟩` and `V2sub = ⟨t, v⟩` of
`Submission/Work/CORE4/A7S4Defs.lean` (`Work.CORE4.fourGroup_conj_V1_V2`, proved in
`Submission/Work/CORE4/A7S4.lean`).  The fact is conjugation-invariant and isomorphism-invariant,
so it suffices to verify it at `V1sub`.

For `V1sub`:

* `C_{A₇}(V1sub) = V1sub × ⟨(4 5 6)⟩` has order `12` and a **unique** subgroup of order `3`,
  namely `⟨k10⟩` with `k10 = (4 5 6)` (this file).  So `K = ⟨k10⟩` for every `K ≤ C(V1sub)` of
  order `3`.
* The involutions `s ∈ N(V1sub)` with `s * k10 * s⁻¹ = k10⁻¹` are the `18` elements
  `(a b)(c d)` with `{a,b} ⊆ {0,1,2,3}` and `{c,d} ⊆ {4,5,6}`; they form a **sub-**family of the
  explicit list `n1Inv` of the `21` involutions of `N(V1sub)` in `A7S4Defs.lean`.
* For each of these `18` involutions one exhibits an even permutation `e` with `e s = s e`,
  `e k10 e⁻¹ ∈ N(V1sub)` (`InN1P`) and `e k10 e⁻¹ ∉ {k10, k10 * k10}`; `e` then lifts to `A₇`.

## The sibling modules (one closed finite check each)

The three finite elementary checks are *closed decidable* statements about explicit permutations
of `Fin 7`, all proved by expanding the explicit `Finset` lists with
`simp only [n1Inv, Finset.mem_insert, Finset.mem_singleton]` and doing a case split
(`rcases hs with rfl | rfl | …`), each case being `decide`-able.  See
`Submission/Work/CORE4/A7S4/n2Check.lean` for this pattern (a `decide` over all `7! = 5040`
permutations of `Fin 7` would also work but is slow, needs `maxRecDepth 100000` and
`maxHeartbeats 0`, and costs minutes of CPU).

* `Submission/Work/CORE4/A4s/cent1.lean` -- the `26` elements of order `3` of `N(V1sub)` that
  centralize `V1sub` are exactly `k10` and `k10 * k10` (so `C(V1sub)` has the unique order-`3`
  subgroup `⟨k10⟩`);
* `Submission/Work/CORE4/A4s/cent2.lean` -- **no** element of `n2Ord3` centralizes `V2sub`
  (so `C(V2sub)` has no element, hence no subgroup, of order `3` -- this makes the `V2sub` case of
  the classification vacuous);
* `Submission/Work/CORE4/A4s/check1.lean` -- for each `s ∈ n1Inv` with `s * k10 * s⁻¹ = k10⁻¹`
  there is an even `e` with `e s = s e`, `InN1P (e k10 e⁻¹)`, `e k10 e⁻¹ ≠ k10` and
  `e k10 e⁻¹ ≠ k10 * k10`.
-/
import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.A7S4Defs

namespace Work.CORE4

/-- `k₁ = (4 5 6)`, the generator of the unique subgroup of order `3` of `C_{A₇}(V₁)`.  It is the
first element of the list `n1Ord3` of `Submission/Work/CORE4/A7S4Defs.lean`. -/
def k10 : Equiv.Perm (Fin 7) := (Equiv.swap 4 5 : Equiv.Perm (Fin 7)) * (Equiv.swap 5 6)

/-- The two elements of order `3` of `C_{A₇}(V₁)`, i.e. the non-trivial elements of the unique
order-`3` subgroup of `C_{A₇}(V₁)`. -/
def k1List : Finset (Equiv.Perm (Fin 7)) := {k10, k10 * k10}

/-- Eighteen even permutations `e` of `Fin 7` that serve as witnesses in `A4s/check1.lean`: for
each of the `18` involutions `s ∈ n1Inv` with `s * k10 * s⁻¹ = k10⁻¹` the `i`-th entry works.
(Explicitly: the entry `e` is a witness for `s` precisely when `e * s = s * e`,
`InN1P (e * k10 * e⁻¹)`, `e * k10 * e⁻¹ ≠ k10` and `e * k10 * e⁻¹ ≠ k10 * k10`; each entry has
exactly one such `s`.) -/
def wit1 : Finset (Equiv.Perm (Fin 7)) :=
  {(Equiv.swap 1 4 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 5 : Equiv.Perm (Fin 7)) * (Equiv.swap 5 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 6 : Equiv.Perm (Fin 7)),
   (Equiv.swap 1 6 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 4 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 5 : Equiv.Perm (Fin 7)),
   (Equiv.swap 1 5 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 4 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 6 : Equiv.Perm (Fin 7)),
   (Equiv.swap 1 5 : Equiv.Perm (Fin 7)) * (Equiv.swap 5 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 6 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 4 : Equiv.Perm (Fin 7)),
   (Equiv.swap 1 4 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 5 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 6 : Equiv.Perm (Fin 7)),
   (Equiv.swap 1 4 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 6 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 5 : Equiv.Perm (Fin 7)),
   (Equiv.swap 1 5 : Equiv.Perm (Fin 7)) * (Equiv.swap 5 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 6 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 4 : Equiv.Perm (Fin 7)),
   (Equiv.swap 1 4 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 5 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 6 : Equiv.Perm (Fin 7)),
   (Equiv.swap 1 4 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 6 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 5 : Equiv.Perm (Fin 7)),
   (Equiv.swap 0 5 : Equiv.Perm (Fin 7)) * (Equiv.swap 5 1 : Equiv.Perm (Fin 7)) * (Equiv.swap 1 6 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 4 : Equiv.Perm (Fin 7)),
   (Equiv.swap 0 4 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 1 : Equiv.Perm (Fin 7)) * (Equiv.swap 1 5 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 6 : Equiv.Perm (Fin 7)),
   (Equiv.swap 0 4 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 1 : Equiv.Perm (Fin 7)) * (Equiv.swap 1 6 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 5 : Equiv.Perm (Fin 7)),
   (Equiv.swap 0 5 : Equiv.Perm (Fin 7)) * (Equiv.swap 5 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 6 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 4 : Equiv.Perm (Fin 7)),
   (Equiv.swap 0 4 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 5 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 6 : Equiv.Perm (Fin 7)),
   (Equiv.swap 0 4 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 6 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 5 : Equiv.Perm (Fin 7)),
   (Equiv.swap 0 5 : Equiv.Perm (Fin 7)) * (Equiv.swap 5 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 6 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 4 : Equiv.Perm (Fin 7)),
   (Equiv.swap 0 4 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 5 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 6 : Equiv.Perm (Fin 7)),
   (Equiv.swap 0 4 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 6 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 5 : Equiv.Perm (Fin 7))}

/-- **The `A4s` property** at a four-group `V` of a group `G`: for every involution
`s ∈ N_G(V)` and every subgroup `K ≤ C_G(V)` of order `3` inverted by `s`, some `e ∈ C_G(s)`
moves `K` to a *different* subgroup of `N_G(V)`.

`Work.CORE4.C15.A7S4ConjProp` is exactly `∀ (E) [Group E] [Finite E],
Nonempty (E ≃* alternatingGroup (Fin 7)) → ∀ V, IsFourGroup V → A4sVProp E V`. -/
def A4sVProp (G : Type*) [Group G] (V : Subgroup G) : Prop :=
  ∀ s ∈ Subgroup.normalizer (V : Set G), orderOf s = 2 →
    ∀ K : Subgroup G, K ≤ Subgroup.centralizer (V : Set G) → Nat.card K = 3 →
      Work.GW2.Inverts s K →
        ∃ e : G, e * s = s * e ∧ Work.GW2.conjSub e K ≤ Subgroup.normalizer (V : Set G) ∧
          Work.GW2.conjSub e K ≠ K

end Work.CORE4
