import Mathlib

/-!
# The finite graph quotient: definitions and elementary classification

For a finite edge set `E` with endpoint maps `a b : E → V`, the graph is the quotient of
`V ⊕ (E × I)` by the relation identifying the two ends of every edge with their endpoints.
This file provides the quotient, the canonical form of its points, the edge parametrisations,
the "legs" and "stars" (spiders) of the vertices, the middle arcs of the edges, the edge-path
inductive type, and the arc-piece / arc-chain vocabulary used to prove the edge-path theorem.
-/

namespace Work.RatHurewicz

open scoped unitInterval Topology

set_option linter.unusedSectionVars false
set_option autoImplicit false

variable {E V : Type} [Fintype E] [Fintype V] [TopologicalSpace E] [DiscreteTopology E]
  [TopologicalSpace V] [DiscreteTopology V]

noncomputable section

variable (a b : E → V)

/-- The relation whose equivalence closure defines the graph. -/
def graphRel : (V ⊕ (E × I)) → (V ⊕ (E × I)) → Prop := fun p q =>
    (∃ e : E, p = Sum.inl (a e) ∧ q = Sum.inr (e, 0))
  ∨ (∃ e : E, p = Sum.inl (b e) ∧ q = Sum.inr (e, 1))
  ∨ (∃ e : E, p = Sum.inr (e, 0) ∧ q = Sum.inl (a e))
  ∨ (∃ e : E, p = Sum.inr (e, 1) ∧ q = Sum.inl (b e))

/-- The setoid of the graph. -/
def graphSetoid : Setoid (V ⊕ (E × I)) := Relation.EqvGen.setoid (graphRel a b)

/-- The graph. -/
abbrev GraphX := Quotient (graphSetoid a b)

/-- The quotient map onto the graph. -/
def gq : V ⊕ (E × I) → GraphX a b := @Quotient.mk' _ (graphSetoid a b)

@[simp] lemma gq_mk'' (p : V ⊕ (E × I)) : gq a b p = Quotient.mk'' p := rfl

lemma rel_ae (e : E) : gq a b (Sum.inr (e, 0)) = gq a b (Sum.inl (a e)) :=
  Quotient.sound (Relation.EqvGen.rel _ _ (Or.inr (Or.inr (Or.inl ⟨e, rfl, rfl⟩))))

lemma rel_be (e : E) : gq a b (Sum.inr (e, 1)) = gq a b (Sum.inl (b e)) :=
  Quotient.sound (Relation.EqvGen.rel _ _ (Or.inr (Or.inr (Or.inr ⟨e, rfl, rfl⟩))))

/-- The canonical representative of a point of the graph. -/
def canon (p : V ⊕ (E × I)) : V ⊕ (E × I) :=
  Sum.rec (fun v => Sum.inl v)
    (fun q => if (q.2 : ℝ) = 0 then Sum.inl (a q.1)
      else if (q.2 : ℝ) = 1 then Sum.inl (b q.1) else Sum.inr q) p

lemma canon_inl (v : V) : canon a b (Sum.inl v) = Sum.inl v := rfl

lemma canon_inr (e : E) (s : I) : canon a b (Sum.inr (e, s)) =
    (if (s : ℝ) = 0 then Sum.inl (a e)
      else if (s : ℝ) = 1 then Sum.inl (b e) else Sum.inr (e, s)) := rfl

lemma canon_eq_of_rel {p q : V ⊕ (E × I)} (h : graphRel a b p q) : canon a b p = canon a b q := by
  rcases h with ⟨e, rfl, rfl⟩ | ⟨e, rfl, rfl⟩ | ⟨e, rfl, rfl⟩ | ⟨e, rfl, rfl⟩
  · rw [canon_inl, canon_inr]; simp
  · rw [canon_inl, canon_inr]; simp
  · rw [canon_inl, canon_inr]; simp
  · rw [canon_inl, canon_inr]; simp

lemma canon_eq_of_eqvGen {p q : V ⊕ (E × I)} (h : Relation.EqvGen (graphRel a b) p q) :
    canon a b p = canon a b q := by
  induction h with
  | rel x y hxy => exact canon_eq_of_rel a b hxy
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

/-- Two points of the graph that are equal have the same canonical form. -/
lemma canon_eq_of_eq {p q : V ⊕ (E × I)} (h : gq a b p = gq a b q) : canon a b p = canon a b q :=
  canon_eq_of_eqvGen a b ((Quotient.eq).mp h)

/-- Two vertices with the same image are equal. -/
lemma gq_inl_inj {v w : V} (h : gq a b (Sum.inl v) = gq a b (Sum.inl w)) : v = w := by
  have hc := canon_eq_of_eq a b h
  rw [canon_inl, canon_inl] at hc
  exact Sum.inl.inj hc

/-- A vertex equals an edge point only through one of the endpoints. -/
lemma gq_inl_inr {v : V} {e : E} {s : I}
    (h : gq a b (Sum.inl v) = gq a b (Sum.inr (e, s))) :
    (s = 0 ∧ v = a e) ∨ (s = 1 ∧ v = b e) := by
  have hc := canon_eq_of_eq a b h
  rw [canon_inl, canon_inr] at hc
  by_cases h0 : (s : ℝ) = 0
  · rw [if_pos h0] at hc
    exact Or.inl ⟨Subtype.ext h0, Sum.inl.inj hc⟩
  · by_cases h1 : (s : ℝ) = 1
    · rw [if_neg h0, if_pos h1] at hc
      exact Or.inr ⟨Subtype.ext h1, Sum.inl.inj hc⟩
    · rw [if_neg h0, if_neg h1] at hc
      exact absurd hc (by simp)

/-- Proper interior points of an edge are not vertices. -/
lemma gq_inr_ne_inl {e : E} {s : I} (h0 : 0 < (s : ℝ)) (h1 : (s : ℝ) < 1) (v : V) :
    gq a b (Sum.inr (e, s)) ≠ gq a b (Sum.inl v) := by
  intro h
  rcases gq_inl_inr a b h.symm with ⟨hs, -⟩ | ⟨hs, -⟩
  · have : (s : ℝ) = 0 := by simpa using congrArg Subtype.val hs
    linarith
  · have : (s : ℝ) = 1 := by simpa using congrArg Subtype.val hs
    linarith

/-- Two coinciding non-endpoint edge points lie on the same edge with the same parameter. -/
lemma gq_inr_inr_interior {e f : E} {s t : I} (h0 : 0 < (s : ℝ)) (h1 : (s : ℝ) < 1)
    (h : gq a b (Sum.inr (e, s)) = gq a b (Sum.inr (f, t))) : e = f ∧ s = t := by
  have hc := canon_eq_of_eq a b h
  rw [canon_inr, canon_inr] at hc
  have hs0 : (s : ℝ) ≠ 0 := by linarith
  have hs1 : (s : ℝ) ≠ 1 := by linarith
  rw [if_neg hs0, if_neg hs1] at hc
  by_cases ht0 : (t : ℝ) = 0
  · rw [if_pos ht0] at hc; exact absurd hc (by simp)
  · by_cases ht1 : (t : ℝ) = 1
    · rw [if_neg ht0, if_pos ht1] at hc; exact absurd hc (by simp)
    · rw [if_neg ht0, if_neg ht1] at hc
      have h2 : (e, s) = (f, t) := Sum.inr.inj hc
      exact ⟨congrArg Prod.fst h2, congrArg Prod.snd h2⟩

/-- If two distinct edges meet, the meeting point is a vertex end. -/
lemma gq_inr_inr_vertex {e f : E} {s t : I} (h : gq a b (Sum.inr (e, s)) = gq a b (Sum.inr (f, t)))
    (hne : e ≠ f) : s = 0 ∨ s = 1 := by
  by_contra hc
  push Not at hc
  have h0 : 0 < (s : ℝ) := lt_of_le_of_ne s.2.1 (fun hh => hc.1 (Subtype.ext hh.symm))
  have h1 : (s : ℝ) < 1 := lt_of_le_of_ne s.2.2 (fun hh => hc.2 (Subtype.ext hh))
  exact hne (gq_inr_inr_interior a b h0 h1 h).1

/-- Coinciding edge points on the same edge, one of them interior, have the same parameter. -/
lemma gq_inr_inr_same {e : E} {s t : I} (h0 : 0 < (s : ℝ)) (h1 : (s : ℝ) < 1)
    (h : gq a b (Sum.inr (e, s)) = gq a b (Sum.inr (e, t))) : s = t :=
  (gq_inr_inr_interior a b h0 h1 h).2

/-- Proper interior points on distinct edges are distinct. -/
lemma gq_inr_ne_of_ne {e f : E} (hne : e ≠ f) {s t : I} (hs0 : 0 < (s : ℝ)) (hs1 : (s : ℝ) < 1) :
    gq a b (Sum.inr (e, s)) ≠ gq a b (Sum.inr (f, t)) := by
  intro h
  exact hne (gq_inr_inr_interior a b hs0 hs1 h).1

/-! ## Edge parametrisations, legs and stars -/

/-- The parametrisation of the edge `e`, as a map into the graph. -/
def psiFunGraph (e : E) : I → GraphX a b := fun s => gq a b (Sum.inr (e, s))

lemma psi_cont (e : E) : Continuous (psiFunGraph a b e) :=
  continuous_quotient_mk'.comp (continuous_inr.comp (continuous_const.prodMk continuous_id))

/-- The image of the edge `e`. -/
def imEdge (e : E) : Set (GraphX a b) := Set.range (psiFunGraph a b e)

/-- The middle open arc of the edge `e`. -/
def midArc (e : E) : Set (GraphX a b) :=
  {z | ∃ s : I, (1 / 4 : ℝ) < (s : ℝ) ∧ (s : ℝ) < 3 / 4 ∧ z = psiFunGraph a b e s}

/-- The star (spider) of a vertex: the vertex together with a short germ of every incident
edge end.  (The germ of the `a`-end runs over parameters `≤ 1/3`, the germ of the `b`-end over
parameters `≥ 2/3`.) -/
def spider (v : V) : Set (GraphX a b) :=
  {z | z = gq a b (Sum.inl v) ∨
    (∃ e : E, a e = v ∧ ∃ s : I, (s : ℝ) < 1/3 ∧ z = psiFunGraph a b e s) ∨
    (∃ e : E, b e = v ∧ ∃ s : I, 2/3 < (s : ℝ) ∧ z = psiFunGraph a b e s)}

lemma mem_spider_center (v : V) : gq a b (Sum.inl v) ∈ spider a b v := Or.inl rfl

lemma mem_spider_of_a (e : E) {s : I} (h : (s : ℝ) < 1/3) :
    psiFunGraph a b e s ∈ spider a b (a e) :=
  Or.inr (Or.inl ⟨e, rfl, s, h, rfl⟩)

lemma mem_spider_of_b (e : E) {s : I} (h : 2/3 < (s : ℝ)) :
    psiFunGraph a b e s ∈ spider a b (b e) :=
  Or.inr (Or.inr ⟨e, rfl, s, h, rfl⟩)

/-- A loop of a space, viewed as an element of its fundamental group.
(The ascription is needed: `FundamentalGroup X x` is an `abbrev` for a category-theoretic `End`,
and the group structure is keyed on that form.) -/
def loopOf {X : Type} [TopologicalSpace X] {x : X} (p : Path x x) : FundamentalGroup X x :=
  Path.Homotopic.Quotient.mk p

/-! ## Edge paths -/

/-- The formal edge paths: words in the edges (with orientation) and trivial loops. -/
inductive EdgePath : V → V → Type
  | refl (v : V) : EdgePath v v
  | fwd (e : E) : EdgePath (a e) (b e)
  | bwd (e : E) : EdgePath (b e) (a e)
  | trans {u v w : V} : EdgePath u v → EdgePath v w → EdgePath u w

/-- The path of the graph associated with an edge. -/
def edgePath (e : E) : Path (gq a b (Sum.inl (a e))) (gq a b (Sum.inl (b e))) where
  toFun := psiFunGraph a b e
  continuous_toFun := psi_cont a b e
  source' := rel_ae a b e
  target' := rel_be a b e

/-- The path of the graph associated with a formal edge path. -/
def EdgePath.toPath {u w : V} : EdgePath a b u w → Path (gq a b (Sum.inl u)) (gq a b (Sum.inl w))
  | .refl v => Path.refl _
  | .fwd e => edgePath a b e
  | .bwd e => (edgePath a b e).symm
  | .trans p q => (EdgePath.toPath p).trans (EdgePath.toPath q)


@[simp] lemma EdgePath.toPath_refl (v : V) :
    EdgePath.toPath a b (.refl v) = Path.refl (gq a b (Sum.inl v)) := rfl

@[simp] lemma EdgePath.toPath_fwd (e : E) :
    EdgePath.toPath a b (.fwd e) = edgePath a b e := rfl

@[simp] lemma EdgePath.toPath_bwd (e : E) :
    EdgePath.toPath a b (.bwd e) = (edgePath a b e).symm := rfl

@[simp] lemma EdgePath.toPath_trans {u x w : V} (p : EdgePath a b u x) (q : EdgePath a b x w) :
    EdgePath.toPath a b (.trans p q) =
      (EdgePath.toPath a b p).trans (EdgePath.toPath a b q) := rfl

/-! ## Arc pieces and arc chains -/

/-- An *arc piece*: a path in the graph together with an edge whose parametrisation lifts it.
Such a path never wraps around an edge. -/
structure ArcPiece (x y : GraphX a b) where
  e : E
  sg : C(I, I)
  c : Path x y
  hc : ∀ t, c t = psiFunGraph a b e (sg t)

/-- The concatenation of arc pieces into a path. -/
inductive ArcChain : GraphX a b → GraphX a b → Type
  | nil (x : GraphX a b) : ArcChain x x
  | cons {x z w : GraphX a b} (p : ArcPiece a b x z) (rest : ArcChain z w) : ArcChain x w

/-- The path of the graph associated with an arc chain. -/
def ArcChain.toPath {x y : GraphX a b} : ArcChain a b x y → Path x y
  | .nil x => Path.refl x
  | .cons p rest => p.c.trans (ArcChain.toPath rest)


end

end Work.RatHurewicz
