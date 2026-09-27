import Mathlib
import Submission.Work.Drive.ncard_tripleMeet_cut

/-!
# The parameter triples and the cut count, in the odd-fibre case

`Work.Drive.tripleCart A B` is the set of parameter triples `(x, y, z)` at which the plane's
parameter `x` and the first sweep's parameter `y` give the same point (`(x,y) ∈ A`) and the
plane's parameter `x` and the second sweep's parameter `z` give the same point (`(x,z) ∈ B`).
`Work.Drive.cutBase A B` is the set of plane parameters that both cuts meet.

If over the base every `A`-fibre and every `B`-fibre has *odd* cardinality — what the radial
sweep produces — then the parameter triples and the base points have the same parity of count:

  `Even (tripleCart A B).ncard + (cutBase A B).ncard`.

The reason is that `tripleCart A B` is the disjoint union, over the points `x` of the base, of the
blocks `{x} × fibreA A x × fibreB B x`, whose cardinalities are the products
`#(fibreA A x) * #(fibreB B x)`; each product is odd, so each product plus `1` is even, and the
sum over the base of `#(...) + 1` is even.
-/

namespace Work.Drive

/-- **The parameter triples over an odd-fibre base have the same parity as the base.** -/
theorem even_ncard_tripleCart_add_ncard_cutBase_of_odd_fibres {X Y Z : Type*}
    (A : Set (X × Y)) (B : Set (X × Z)) (hA : A.Finite) (hB : B.Finite)
    (hfibA : ∀ x ∈ Work.Drive.cutBase A B, Odd (Work.Drive.fibreA A x).ncard)
    (hfibB : ∀ x ∈ Work.Drive.cutBase A B, Odd (Work.Drive.fibreB B x).ncard) :
    Even ((Work.Drive.tripleCart A B).ncard + (Work.Drive.cutBase A B).ncard) := by
  have hTfin : (Work.Drive.cutBase A B).Finite :=
    (hA.image Prod.fst).subset (by rintro x ⟨⟨y, hy⟩, -⟩; exact ⟨(x, y), hy, rfl⟩)
  have hfa : ∀ x, (Work.Drive.fibreA A x).Finite :=
    fun x => (hA.image Prod.snd).subset (by rintro y hy; exact ⟨(x, y), hy, rfl⟩)
  have hfb : ∀ x, (Work.Drive.fibreB B x).Finite :=
    fun x => (hB.image Prod.snd).subset (by rintro z hz; exact ⟨(x, z), hz, rfl⟩)
  -- `tripleCart` is the disjoint union of the blocks `{x} × fibreA A x × fibreB B x`.
  have hdecomp : Work.Drive.tripleCart A B
      = ⋃ x ∈ Work.Drive.cutBase A B,
          ({x} ×ˢ ((Work.Drive.fibreA A x) ×ˢ (Work.Drive.fibreB B x)) : Set (X × Y × Z)) := by
    ext p
    constructor
    · intro hp
      refine Set.mem_iUnion.mpr ⟨p.1, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
      · exact ⟨⟨p.2.1, hp.1⟩, ⟨p.2.2, hp.2⟩⟩
      · refine ⟨rfl, hp.1, hp.2⟩
    · intro hp
      rcases Set.mem_iUnion.mp hp with ⟨x, hx⟩
      rcases Set.mem_iUnion.mp hx with ⟨hxT, hxp⟩
      simp only [Set.mem_prod, Set.mem_singleton_iff, Work.Drive.fibreA, Work.Drive.fibreB,
        Set.mem_ofPred_eq] at hxp
      obtain ⟨h1, h2, h3⟩ := hxp
      subst h1
      exact ⟨h2, h3⟩
  have hpair : (Work.Drive.cutBase A B).PairwiseDisjoint
      (fun x => ({x} ×ˢ ((Work.Drive.fibreA A x) ×ˢ (Work.Drive.fibreB B x)) :
        Set (X × Y × Z))) := by
    intro x hx y hy hxy
    refine Set.disjoint_left.mpr ?_
    intro p hp hq
    simp only [Set.mem_prod, Set.mem_singleton_iff] at hp hq
    exact hxy (hp.1.symm.trans hq.1)
  -- The cardinality of the union is the sum of the block cardinalities.
  have hcard : (Work.Drive.tripleCart A B).ncard
      = ∑ x ∈ hTfin.toFinset,
          (Work.Drive.fibreA A x).ncard * (Work.Drive.fibreB B x).ncard := by
    rw [hdecomp, hTfin.ncard_biUnion
      (fun x hx => (Set.finite_singleton x).prod ((hfa x).prod (hfb x))) hpair,
      finsum_mem_eq_finite_toFinset_sum _ hTfin]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Set.ncard_prod, Set.ncard_prod, Set.ncard_singleton, one_mul]
  -- Each summand plus `1` is even; the sum over the base of `1` is the base's cardinality.
  rw [hcard, Set.ncard_eq_toFinset_card _ hTfin, Finset.card_eq_sum_ones,
    ← Finset.sum_add_distrib]
  apply Finset.even_sum
  intro x hx
  have hxbase : x ∈ Work.Drive.cutBase A B := (Set.Finite.mem_toFinset hTfin).mp hx
  exact Odd.add_odd (Odd.mul (hfibA x hxbase) (hfibB x hxbase)) odd_one

end Work.Drive
