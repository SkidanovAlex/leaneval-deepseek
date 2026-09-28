import Mathlib
import Submission.Work.RatHurewicz.finiteGraphDefs
import Submission.Work.RatHurewicz.GraphPi.spiderDefs

/-!
# The local structure of the finite graph

For the quotient `GraphX a b = (V ⊕ (E × I)) / ~` of `RatHurewicz/finiteGraphDefs`, this file
proves that the "spider" of a vertex and the "middle arc" of an edge are open, and that together
they cover the graph (`Work.RatHurewicz.GraphPi.spiderLocal`).

The proof computes the preimages of these two families of sets under the quotient map `gq a b`
explicitly:

* `(gq a b) ⁻¹' spider a b v = spiderA a v ∪ spiderB b v`, i.e.
  `{inl v} ∪ ⋃_{a e = v} ({e} × [0, 1/3)) ∪ ⋃_{b e = v} ({e} × (2/3, 1])`,
* `(gq a b) ⁻¹' midArc a b e = midParam e`, i.e. `{e} × (1/4, 3/4)`.

Both are open in `V ⊕ (E × I)` because `E` and `V` are discrete and the relevant intervals are
open in `I`, and the quotient topology is the coinduced one, so openness descends.

The identification of the preimages goes through the *canonical form* `canon a b`: the sets above
are invariant under replacing a point by its canonical form (`canon_mem_spiderAB`,
`canon_mem_midParam`), hence are saturated, and for a saturated `S` the preimage of its image is
`S` itself (`preimage_gq_image_eq`).  The cover is then checked on the canonical form of a point:
a point of an edge strip has parameter `< 1/3` (spider of the `a`-end), or `> 2/3` (spider of the
`b`-end), or lies in `[1/3, 2/3] ⊆ (1/4, 3/4)` (middle arc).
-/

namespace Work.RatHurewicz.GraphPi

open scoped unitInterval Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false

section

variable {E V : Type} [Fintype E] [Fintype V] [TopologicalSpace E] [DiscreteTopology E]
  [TopologicalSpace V] [DiscreteTopology V]

/-! ## The canonical form and the class of a point -/

/-- The canonical form of a point is equivalent to the point. -/
lemma gq_canon (a b : E → V) (p : V ⊕ (E × I)) :
    gq a b (canon a b p) = gq a b p := by
  rcases p with w | ⟨e, s⟩
  · rfl
  · rw [canon_inr]
    by_cases h0 : (s : ℝ) = 0
    · rw [if_pos h0]
      have hs : s = 0 := Subtype.ext h0
      rw [hs]
      exact (rel_ae a b e).symm
    · by_cases h1 : (s : ℝ) = 1
      · rw [if_neg h0, if_pos h1]
        have hs : s = 1 := Subtype.ext h1
        rw [hs]
        exact (rel_be a b e).symm
      · rw [if_neg h0, if_neg h1]

/-- Two points have the same canonical form iff they lie in the same class. -/
lemma canon_eq_iff_gq_eq (a b : E → V) {p q : V ⊕ (E × I)} :
    canon a b p = canon a b q ↔ gq a b p = gq a b q :=
  ⟨fun h => by rw [← gq_canon a b p, h, gq_canon a b q], canon_eq_of_eq a b⟩

/-! ## Membership in the two germs of a spider -/

lemma mem_spiderA_inl (a : E → V) (v : V) {x : V} :
    (Sum.inl x : V ⊕ (E × I)) ∈ spiderA a v ↔ x = v := by
  rw [mem_spiderA]
  constructor
  · rintro (h | ⟨e, s, -, -, he⟩)
    · exact Sum.inl.inj h
    · exact absurd he Sum.inl_ne_inr
  · rintro rfl
    exact Or.inl rfl

lemma mem_spiderA_inr (a : E → V) (v : V) {e : E} {s : I} :
    (Sum.inr (e, s) : V ⊕ (E × I)) ∈ spiderA a v ↔ a e = v ∧ (s : ℝ) < 1/3 := by
  rw [mem_spiderA]
  constructor
  · rintro (h | ⟨e', s', ha, hs, he⟩)
    · exact absurd h Sum.inr_ne_inl
    · have h' : (e, s) = (e', s') := Sum.inr.inj he
      simp only [Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl⟩ := h'
      exact ⟨ha, hs⟩
  · rintro ⟨ha, hs⟩
    exact Or.inr ⟨e, s, ha, hs, rfl⟩

lemma mem_spiderB_inl (b : E → V) (v : V) {x : V} :
    (Sum.inl x : V ⊕ (E × I)) ∈ spiderB b v ↔ x = v := by
  rw [mem_spiderB]
  constructor
  · rintro (h | ⟨e, s, -, -, he⟩)
    · exact Sum.inl.inj h
    · exact absurd he Sum.inl_ne_inr
  · rintro rfl
    exact Or.inl rfl

lemma mem_spiderB_inr (b : E → V) (v : V) {e : E} {s : I} :
    (Sum.inr (e, s) : V ⊕ (E × I)) ∈ spiderB b v ↔ b e = v ∧ 2/3 < (s : ℝ) := by
  rw [mem_spiderB]
  constructor
  · rintro (h | ⟨e', s', ha, hs, he⟩)
    · exact absurd h Sum.inr_ne_inl
    · have h' : (e, s) = (e', s') := Sum.inr.inj he
      simp only [Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl⟩ := h'
      exact ⟨ha, hs⟩
  · rintro ⟨ha, hs⟩
    exact Or.inr ⟨e, s, ha, hs, rfl⟩

lemma mem_spiderAB_inl (a b : E → V) (v : V) {x : V} :
    (Sum.inl x : V ⊕ (E × I)) ∈ spiderA a v ∪ spiderB b v ↔ x = v := by
  rw [Set.mem_union, mem_spiderA_inl a v, mem_spiderB_inl b v, or_self]

/-! ## The canonical form preserves the spider germs -/

/-- The preimage of the spider of `v` is invariant under the canonical-form reduction. -/
lemma canon_mem_spiderAB (a b : E → V) (v : V) (p : V ⊕ (E × I)) :
    p ∈ spiderA a v ∪ spiderB b v ↔ canon a b p ∈ spiderA a v ∪ spiderB b v := by
  constructor
  · intro hp
    rcases p with x | ⟨e, s⟩
    · have hx : x = v := (mem_spiderAB_inl a b v).mp hp
      show canon a b (Sum.inl x) ∈ spiderA a v ∪ spiderB b v
      rw [canon_inl, hx]
      exact Or.inl (sum_inl_mem_spiderA a v)
    · show canon a b (Sum.inr (e, s)) ∈ spiderA a v ∪ spiderB b v
      rw [canon_inr]
      rcases hp with h | h
      · obtain ⟨ha, hs⟩ := (mem_spiderA_inr a v).mp h
        by_cases h0 : (s : ℝ) = 0
        · rw [if_pos h0, ha]
          exact Or.inl (sum_inl_mem_spiderA a v)
        · rw [if_neg h0, if_neg (by intro hh; linarith : ¬ ((s : ℝ) = 1))]
          exact Or.inl (sum_inr_mem_spiderA ha hs)
      · obtain ⟨ha, hs⟩ := (mem_spiderB_inr b v).mp h
        have h0 : ¬ ((s : ℝ) = 0) := by intro hh; linarith
        by_cases h1 : (s : ℝ) = 1
        · rw [if_neg h0, if_pos h1, ha]
          exact Or.inl (sum_inl_mem_spiderA a v)
        · rw [if_neg h0, if_neg h1]
          exact Or.inr (sum_inr_mem_spiderB ha hs)
  · intro hp
    rcases p with x | ⟨e, s⟩
    · rw [canon_inl] at hp
      exact hp
    · rw [canon_inr] at hp
      by_cases h0 : (s : ℝ) = 0
      · rw [if_pos h0] at hp
        have ha : a e = v := (mem_spiderAB_inl a b v).mp hp
        exact Or.inl (sum_inr_mem_spiderA ha (by rw [h0]; norm_num))
      · rw [if_neg h0] at hp
        by_cases h1 : (s : ℝ) = 1
        · rw [if_pos h1] at hp
          have hb : b e = v := (mem_spiderAB_inl a b v).mp hp
          exact Or.inr (sum_inr_mem_spiderB hb (by rw [h1]; norm_num))
        · rw [if_neg h1] at hp
          exact hp

/-! ## The middle part of an edge strip -/

/-- The middle part `{e} × (1/4, 3/4)` of the edge strip `{e} × I`, as a subset of the disjoint
union `V ⊕ (E × I)`. -/
def midParam (e : E) : Set (V ⊕ (E × I)) :=
  {p | ∃ s : I, (1/4 : ℝ) < (s : ℝ) ∧ (s : ℝ) < 3/4 ∧ p = Sum.inr (e, s)}

lemma not_mem_midParam_inl (e : E) {x : V} : (Sum.inl x : V ⊕ (E × I)) ∉ midParam e := by
  rintro ⟨_, -, -, he⟩
  exact Sum.inl_ne_inr he

lemma mem_midParam_inr {e f : E} {t : I} :
    (Sum.inr (f, t) : V ⊕ (E × I)) ∈ midParam e ↔
      f = e ∧ (1/4 : ℝ) < (t : ℝ) ∧ (t : ℝ) < 3/4 := by
  constructor
  · rintro ⟨u, h1, h2, he⟩
    have h' : (f, t) = (e, u) := Sum.inr.inj he
    simp only [Prod.mk.injEq] at h'
    obtain ⟨rfl, rfl⟩ := h'
    exact ⟨rfl, h1, h2⟩
  · rintro ⟨rfl, h1, h2⟩
    exact ⟨t, h1, h2, rfl⟩

/-- The preimage of a middle arc is invariant under the canonical-form reduction. -/
lemma canon_mem_midParam (a b : E → V) (e : E) (p : V ⊕ (E × I)) :
    p ∈ midParam e ↔ canon a b p ∈ midParam e := by
  constructor
  · intro hp
    rcases p with x | ⟨f, t⟩
    · exact absurd hp (not_mem_midParam_inl e)
    · obtain ⟨hf, h1, h2⟩ := (mem_midParam_inr (e := e) (f := f) (t := t)).mp hp
      show canon a b (Sum.inr (f, t)) ∈ midParam e
      rw [canon_inr, if_neg (by intro hh; linarith : ¬ ((t : ℝ) = 0)),
        if_neg (by intro hh; linarith : ¬ ((t : ℝ) = 1)), hf]
      exact ⟨t, h1, h2, rfl⟩
  · intro hp
    rcases p with x | ⟨f, t⟩
    · rw [canon_inl] at hp
      exact absurd hp (not_mem_midParam_inl e)
    · rw [canon_inr] at hp
      by_cases h0 : (t : ℝ) = 0
      · rw [if_pos h0] at hp
        exact absurd hp (not_mem_midParam_inl e)
      · rw [if_neg h0] at hp
        by_cases h1 : (t : ℝ) = 1
        · rw [if_pos h1] at hp
          exact absurd hp (not_mem_midParam_inl e)
        · rw [if_neg h1] at hp
          exact hp

/-! ## Saturated sets and the preimage of their image -/

/-- If a set of representatives is invariant under the canonical-form reduction, then it is a
union of classes, and the preimage of its image under the quotient map is the set itself. -/
lemma preimage_gq_image_eq (a b : E → V) {S : Set (V ⊕ (E × I))}
    (hS : ∀ p, p ∈ S ↔ canon a b p ∈ S) :
    gq a b ⁻¹' (gq a b '' S) = S := by
  ext p
  constructor
  · intro hp
    obtain ⟨q, hq, hpq⟩ := hp
    have hc : canon a b q = canon a b p := canon_eq_of_eq a b hpq
    exact (hS p).mpr (hc ▸ ((hS q).mp hq))
  · intro hp
    exact ⟨p, hp, rfl⟩

/-- The spider of `v` is the image of the two germs. -/
lemma gq_image_spiderAB (a b : E → V) (v : V) :
    gq a b '' (spiderA a v ∪ spiderB b v) = spider a b v := by
  ext z
  constructor
  · rintro ⟨p, hp, rfl⟩
    rcases p with w | ⟨e, s⟩
    · have hw : w = v := (mem_spiderAB_inl a b v).mp hp
      rw [hw]
      exact mem_spider_center a b v
    · rcases hp with h | h
      · obtain ⟨ha, hs⟩ := (mem_spiderA_inr a v).mp h
        rw [← ha]
        exact mem_spider_of_a a b e hs
      · obtain ⟨ha, hs⟩ := (mem_spiderB_inr b v).mp h
        rw [← ha]
        exact mem_spider_of_b a b e hs
  · intro hz
    rcases hz with h | ⟨e, ha, s, hs, rfl⟩ | ⟨e, ha, s, hs, rfl⟩
    · exact ⟨Sum.inl v, Or.inl (Or.inl rfl), h.symm⟩
    · exact ⟨Sum.inr (e, s), Or.inl (Or.inr ⟨e, s, ha, hs, rfl⟩), rfl⟩
    · exact ⟨Sum.inr (e, s), Or.inr (Or.inr ⟨e, s, ha, hs, rfl⟩), rfl⟩

/-- The middle arc of `e` is the image of the middle part of its strip. -/
lemma gq_image_midParam (a b : E → V) (e : E) :
    gq a b '' midParam (V := V) e = midArc a b e := by
  ext z
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨s, h1, h2, rfl⟩ := hp
    exact ⟨s, h1, h2, rfl⟩
  · rintro ⟨s, h1, h2, rfl⟩
    exact ⟨Sum.inr (e, s), ⟨s, h1, h2, rfl⟩, rfl⟩

lemma preimage_spider (a b : E → V) (v : V) :
    gq a b ⁻¹' spider a b v = spiderA a v ∪ spiderB b v := by
  rw [← gq_image_spiderAB a b v]
  exact preimage_gq_image_eq a b (S := spiderA a v ∪ spiderB b v) (canon_mem_spiderAB a b v)

lemma preimage_midArc (a b : E → V) (e : E) :
    gq a b ⁻¹' midArc a b e = midParam (V := V) e := by
  rw [← gq_image_midParam a b e]
  exact preimage_gq_image_eq a b (S := midParam (V := V) e) (canon_mem_midParam a b e)

/-! ## Openness of the preimages -/

lemma inl_preimage_spiderA (a : E → V) (v : V) :
    Sum.inl ⁻¹' spiderA a v = {v} := by
  ext x
  rw [Set.mem_preimage, mem_spiderA_inl a v, Set.mem_singleton_iff]

lemma inr_preimage_spiderA (a : E → V) (v : V) :
    Sum.inr ⁻¹' spiderA a v = {e : E | a e = v} ×ˢ {s : I | (s : ℝ) < 1/3} := by
  ext q
  obtain ⟨e, s⟩ := q
  rw [Set.mem_preimage, mem_spiderA_inr a v, Set.mem_prod]
  simp

lemma inl_preimage_spiderB (b : E → V) (v : V) :
    Sum.inl ⁻¹' spiderB b v = {v} := by
  ext x
  rw [Set.mem_preimage, mem_spiderB_inl b v, Set.mem_singleton_iff]

lemma inr_preimage_spiderB (b : E → V) (v : V) :
    Sum.inr ⁻¹' spiderB b v = {e : E | b e = v} ×ˢ {s : I | 2/3 < (s : ℝ)} := by
  ext q
  obtain ⟨e, s⟩ := q
  rw [Set.mem_preimage, mem_spiderB_inr b v, Set.mem_prod]
  simp

lemma isOpen_spiderA (a : E → V) (v : V) : IsOpen (spiderA a v) := by
  rw [isOpen_sum_iff, inl_preimage_spiderA, inr_preimage_spiderA]
  exact ⟨isOpen_discrete {v},
    (isOpen_discrete {e : E | a e = v}).prod (isOpen_Iio.preimage continuous_subtype_val)⟩

lemma isOpen_spiderB (b : E → V) (v : V) : IsOpen (spiderB b v) := by
  rw [isOpen_sum_iff, inl_preimage_spiderB, inr_preimage_spiderB]
  exact ⟨isOpen_discrete {v},
    (isOpen_discrete {e : E | b e = v}).prod (isOpen_Ioi.preimage continuous_subtype_val)⟩

lemma isOpen_spiderAB (a b : E → V) (v : V) : IsOpen (spiderA a v ∪ spiderB b v) :=
  (isOpen_spiderA a v).union (isOpen_spiderB b v)

lemma inl_preimage_midParam (e : E) : Sum.inl ⁻¹' midParam (V := V) e = ∅ := by
  ext x
  rw [Set.mem_preimage]
  exact ⟨fun h1 => absurd h1 (not_mem_midParam_inl e), fun h2 => absurd h2 (Set.notMem_empty x)⟩

lemma inr_preimage_midParam (e : E) :
    Sum.inr ⁻¹' midParam (V := V) e =
      {e} ×ˢ {s : I | (1/4 : ℝ) < (s : ℝ) ∧ (s : ℝ) < 3/4} := by
  ext q
  obtain ⟨f, t⟩ := q
  rw [Set.mem_preimage, mem_midParam_inr, Set.mem_prod, Set.mem_singleton_iff, Set.mem_ofPred_eq]

lemma isOpen_midParam (e : E) : IsOpen (midParam (V := V) e) := by
  rw [isOpen_sum_iff, inl_preimage_midParam, inr_preimage_midParam]
  exact ⟨isOpen_empty, (isOpen_discrete ({e} : Set E)).prod
    ((isOpen_Ioi.preimage continuous_subtype_val).inter
      (isOpen_Iio.preimage continuous_subtype_val))⟩

/-! ## Openness in the quotient -/

/-- The topology of the graph is the quotient (coinduced) topology, so a set is open iff its
preimage under `gq a b` is. -/
lemma isOpen_iff_preimage_isOpen (a b : E → V) {S : Set (GraphX a b)} :
    IsOpen S ↔ IsOpen (gq a b ⁻¹' S) :=
  isOpen_coinduced (f := gq a b)

end

/-! ## The target -/

theorem spiderLocal {E V : Type} [Fintype E] [Fintype V] [TopologicalSpace E] [DiscreteTopology E] [TopologicalSpace V] [DiscreteTopology V] (a b : E → V) :
    (∀ v : V, IsOpen (Work.RatHurewicz.spider a b v)) ∧
      (∀ e : E, IsOpen (Work.RatHurewicz.midArc a b e)) ∧
      (⋃ e : E, Work.RatHurewicz.midArc a b e) ∪ (⋃ v : V, Work.RatHurewicz.spider a b v) = Set.univ := by
  refine ⟨?_, ?_, ?_⟩
  · intro v
    exact (isOpen_iff_preimage_isOpen a b).mpr
      (by rw [preimage_spider a b v]; exact isOpen_spiderAB a b v)
  · intro e
    exact (isOpen_iff_preimage_isOpen a b).mpr
      (by rw [preimage_midArc a b e]; exact isOpen_midParam e)
  · ext z
    constructor
    · intro _
      trivial
    · intro _
      obtain ⟨p, hpz⟩ := Quotient.mk''_surjective (s₁ := Work.RatHurewicz.graphSetoid a b) z
      rw [← hpz, ← Work.RatHurewicz.gq_mk'' a b p]
      rcases p with w | ⟨e, s⟩
      · exact Or.inr (Set.mem_iUnion.mpr ⟨w, Work.RatHurewicz.mem_spider_center a b w⟩)
      · by_cases h : (s : ℝ) < 1/3
        · exact Or.inr (Set.mem_iUnion.mpr ⟨a e, Work.RatHurewicz.mem_spider_of_a a b e h⟩)
        · by_cases h2 : 2/3 < (s : ℝ)
          · exact Or.inr (Set.mem_iUnion.mpr ⟨b e, Work.RatHurewicz.mem_spider_of_b a b e h2⟩)
          · exact Or.inl (Set.mem_iUnion.mpr ⟨e, ⟨s, by linarith, by linarith, rfl⟩⟩)

end Work.RatHurewicz.GraphPi
