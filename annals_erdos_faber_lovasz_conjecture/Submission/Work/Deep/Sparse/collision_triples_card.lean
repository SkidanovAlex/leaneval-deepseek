/-
# The ordered triples of same-coloured retained neighbours

The counting half of the naive colouring procedure: for the random colouring `f : V → Fin k`
and a vertex `v`, the number of ordered triples of pairwise distinct retained neighbours of `v`
carrying one and the same colour is exactly six times the paper's `T_v = ∑_c C(Col_c(v), 3)`.

The proof splits the colouring `f` into its colour classes on `N(v)`; each colour class `S_c`
contributes the ordered triples of pairwise distinct elements of `S_c`, and three of these can
be counted by splitting off the first two entries (the off-diagonal of `S_c`):

  `|{ordered triples of distinct elements of S}| = ∑_{p ∈ S.offDiag} |S \ {p.1, p.2}|`
  `= |S.offDiag| * (|S| - 2) = |S| (|S| - 1) (|S| - 2) = 6 * C(|S|, 3)`.
-/
import Submission.Work.Deep.Sparse.Prelude
import Submission.Work.Deep.Sparse.ProbModel

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.Deep.Sparse

section Triples

variable {V : Type*} [DecidableEq V]

/-- The fibres attached to the ordered pairs of distinct elements of `S` are pairwise disjoint:
each fibre records its own pair in its first two coordinates. -/
private lemma disj_of_image (S : Finset V) :
    (S.offDiag : Set (V × V)).PairwiseDisjoint
      (fun p => ((S.erase p.1).erase p.2).image (fun x => (p.1, p.2, x))) := by
  intro p _ p' _ hpp'
  rw [Function.onFun, Finset.disjoint_left]
  intro q hq hq'
  obtain ⟨x, -, hxq⟩ := Finset.mem_image.mp hq
  obtain ⟨x', -, hxq'⟩ := Finset.mem_image.mp hq'
  rw [← hxq'] at hxq
  have hp : p = p' := by
    injection hxq with h0 h1
    injection h1 with h2 h3
    exact Prod.ext h0 h2
  exact hpp' hp

/-- The ordered triples of pairwise distinct elements of `S`. -/
private def tripleSet (S : Finset V) : Finset (V × V × V) :=
  S.offDiag.disjiUnion
    (fun p => ((S.erase p.1).erase p.2).image (fun x => (p.1, p.2, x)))
    (disj_of_image S)

/-- The unfolding of `tripleSet` as the disjoint union over the ordered pairs. -/
private lemma tripleSet_eq (S : Finset V) :
    tripleSet S = S.offDiag.disjiUnion
      (fun p => ((S.erase p.1).erase p.2).image (fun x => (p.1, p.2, x)))
      (disj_of_image S) := rfl

/-- Membership in `tripleSet`: the three entries are pairwise distinct elements of `S`. -/
private lemma mem_tripleSet {S : Finset V} {q : V × V × V} :
    q ∈ tripleSet S ↔
      q.1 ∈ S ∧ q.2.1 ∈ S ∧ q.2.2 ∈ S ∧ q.1 ≠ q.2.1 ∧ q.1 ≠ q.2.2 ∧ q.2.1 ≠ q.2.2 := by
  constructor
  · intro h
    rw [tripleSet_eq] at h
    obtain ⟨p, hp, hq⟩ := Finset.mem_disjiUnion.mp h
    obtain ⟨x, hx, hxq⟩ := Finset.mem_image.mp hq
    rw [Finset.mem_offDiag] at hp
    obtain ⟨hx1, hx2⟩ := Finset.mem_erase.mp hx
    obtain ⟨hx3, hx4⟩ := Finset.mem_erase.mp hx2
    subst hxq
    exact ⟨hp.1, hp.2.1, hx4, hp.2.2, Ne.symm hx3, Ne.symm hx1⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    rw [tripleSet_eq]
    refine Finset.mem_disjiUnion.mpr ⟨(q.1, q.2.1), Finset.mem_offDiag.mpr ⟨h1, h2, h4⟩, ?_⟩
    exact Finset.mem_image.mpr ⟨q.2.2,
      Finset.mem_erase.mpr ⟨Ne.symm h6, Finset.mem_erase.mpr ⟨Ne.symm h5, h3⟩⟩, rfl⟩

/-- The off-diagonal of an `n`-element finset has `n (n - 1)` elements. -/
private lemma offDiag_card' (S : Finset V) : S.offDiag.card = S.card * (S.card - 1) := by
  rw [Finset.offDiag_card, Nat.mul_sub, Nat.mul_one]

/-- **The counting lemma.**  A finset with `n` elements has `n (n - 1) (n - 2)` ordered
triples of pairwise distinct elements. -/
private lemma card_tripleSet (S : Finset V) :
    (tripleSet S).card = S.card * (S.card - 1) * (S.card - 2) := by
  have hfib : ∀ p ∈ S.offDiag,
      (((S.erase p.1).erase p.2).image (fun x => (p.1, p.2, x))).card = S.card - 2 := by
    intro p hp
    rw [Finset.mem_offDiag] at hp
    have hinj : Function.Injective (fun x : V => (p.1, p.2, x)) :=
      fun x y h => congrArg Prod.snd (congrArg Prod.snd h)
    rw [Finset.card_image_of_injective _ hinj]
    have h1 : (S.erase p.1).card = S.card - 1 := Finset.card_erase_of_mem hp.1
    have h2 : p.2 ∈ S.erase p.1 := Finset.mem_erase.mpr ⟨Ne.symm hp.2.2, hp.2.1⟩
    rw [Finset.card_erase_of_mem h2, h1]
    omega
  rw [tripleSet_eq, Finset.card_disjiUnion]
  have hsum : ∑ p ∈ S.offDiag,
      (((S.erase p.1).erase p.2).image (fun x => (p.1, p.2, x))).card
      = ∑ p ∈ S.offDiag, (S.card - 2) :=
    Finset.sum_congr rfl fun p hp => hfib p hp
  rw [hsum, Finset.sum_const_nat (fun p _ => rfl), offDiag_card']

/-- `6 * C(n,3) = n (n - 1) (n - 2)`. -/
private theorem six_mul_choose_three (n : ℕ) : 6 * n.choose 3 = n * (n - 1) * (n - 2) := by
  have h1 : n.choose 3 * 3 = n.choose 2 * (n - 2) := by
    simpa using Nat.choose_succ_right_eq n 2
  have h2 : n.choose 2 * 2 = n * (n - 1) := by
    simpa using Nat.choose_succ_right_eq n 1
  calc 6 * n.choose 3 = 2 * (n.choose 3 * 3) := by ring
    _ = 2 * (n.choose 2 * (n - 2)) := by rw [h1]
    _ = (n.choose 2 * 2) * (n - 2) := by ring
    _ = (n * (n - 1)) * (n - 2) := by rw [h2]

end Triples

theorem collision_triples_card {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (f : V → Fin k) (v : V) : 6 * (Work.Deep.Sparse.ofColoring G f).tripleTerm v = (Work.Deep.Sparse.collisionTriples G f v).card := by
  classical
  -- The colour classes of `v`: the retained neighbours of `v` of a fixed colour.
  have hdisj : ((Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint
      (fun c => tripleSet ((G.neighborFinset v).filter (fun x => Retained G f x ∧ f x = c))) := by
    intro c _ c' _ hcc'
    rw [Function.onFun, Finset.disjoint_left]
    intro q hq hq'
    have h1 : f q.1 = c := (Finset.mem_filter.mp (mem_tripleSet.mp hq).1).2.2
    have h2 : f q.1 = c' := (Finset.mem_filter.mp (mem_tripleSet.mp hq').1).2.2
    exact hcc' (h1.symm.trans h2)
  -- `collisionTriples` is the disjoint union, over the colours, of the ordered triples of
  -- pairwise distinct elements of the colour classes.
  have hunion : collisionTriples G f v = Finset.univ.disjiUnion
      (fun c => tripleSet ((G.neighborFinset v).filter (fun x => Retained G f x ∧ f x = c)))
      hdisj := by
    ext q
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [mem_collisionTriples] at h
      obtain ⟨hN1, hN2, hN3, hd1, hd2, hd3, hR1, hR2, hR3, hc1, hc2⟩ := h
      refine Finset.mem_disjiUnion.mpr ⟨f q.1, Finset.mem_univ _, ?_⟩
      exact mem_tripleSet.mpr ⟨Finset.mem_filter.mpr ⟨hN1, hR1, rfl⟩,
        Finset.mem_filter.mpr ⟨hN2, hR2, hc1.symm⟩,
        Finset.mem_filter.mpr ⟨hN3, hR3, hc2.symm.trans hc1.symm⟩, hd1, hd2, hd3⟩
    · obtain ⟨c, -, hq⟩ := Finset.mem_disjiUnion.mp h
      obtain ⟨hq1, hq2, hq3, hd1, hd2, hd3⟩ := mem_tripleSet.mp hq
      have m1 := Finset.mem_filter.mp hq1
      have m2 := Finset.mem_filter.mp hq2
      have m3 := Finset.mem_filter.mp hq3
      rw [mem_collisionTriples]
      exact ⟨m1.1, m2.1, m3.1, hd1, hd2, hd3,
        m1.2.1, m2.2.1, m3.2.1, m1.2.2.trans m2.2.2.symm, m2.2.2.trans m3.2.2.symm⟩
  rw [hunion, Finset.card_disjiUnion, tripleTerm_ofColoring G f v, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [card_tripleSet, ← colourClassCount_eq G f v c]
  exact six_mul_choose_three _

end Work.Deep.Sparse
