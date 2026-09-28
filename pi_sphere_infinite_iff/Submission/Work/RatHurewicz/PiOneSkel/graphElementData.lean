import Mathlib
import Submission.Work.RatHurewicz.SkelGraph.assembly
import Submission.Work.RatHurewicz.SkelGraph.graphElementDefs
import Submission.Work.RatHurewicz.SkelGraph.goodDefs

/-!
# The graph element data of the `1`-skeleton of the cycle model

This file proves `Work.RatHurewicz.SkelGraph.GraphElementData D`, the combinatorial description of
the low dimensional points of the cycle model of `Work.RatHurewicz.cycleModelDefs`: the canonical
form `wOf D y` of a low dimensional point `y` of the model (`Work.RatHurewicz.SkelGraph.wOf`,
defined in `SkelGraph/graphElementDefs.lean`) determines the point of the `1`-skeleton, and
conversely.

The map used is `f y = gq (a D) (b D) (wOf D y)`.  The three conjuncts of `GraphElementData` are:

* `psi_wOf`: the point of the skeleton represented by `wOf D y` is the point `y` represents;
* `gq_wOf_eqvGen` (and its one-step version `gq_wOf_modelRel`): `wOf` is constant on the classes of
  the gluing relation `modelRel D`, whence `f` is well defined on the model;
* `gq_wOf_rawOf`: `f` is a section of the graph element description of `psi`, which is used to
  identify the graph element of a point of the skeleton given by an arbitrary graph element.
-/

namespace Work.RatHurewicz.PiOneSkel

open scoped Topology Simplicial unitInterval

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

variable {X : Type} [TopologicalSpace X] {x₀ : X} {n : ℕ}

/-! ## The point of the skeleton represented by `wOf` -/

/-- **The first conjunct of `GraphElementData`.**  The graph element `wOf D y` of a low dimensional
point of the model represents the same point of the `1`-skeleton as `y`. -/
theorem psi_wOf (D : MData X n x₀) (y : {y : Raw D // isLowDim D y}) :
    SkelGraph.psi D (SkelGraph.wOf D y) = SkelGraph.toSkeleton D y := by
  obtain ⟨⟨i, x⟩ | ⟨i, s⟩, hy⟩ := y
  · rcases hd : SkelGraph.decomp x with p | ⟨⟨⟨p, q⟩, hpq⟩, s'⟩
    · rw [SkelGraph.wOf_inl_inl D i x hy p hd]
      have hx : x = stdSimplex.vertex p := SkelGraph.GoodAux.eq_vertex_of_decomp_inl hd
      subst hx
      rfl
    · rw [SkelGraph.wOf_inl_inr D i x hy ⟨(p, q), hpq⟩ s' hd]
      have hcard : (SkelGraph.supp x).card ≤ 2 :=
        (SkelGraph.GoodAux.isLowDim_inl_iff i x).mp hy
      obtain ⟨hx, -, -⟩ :=
        SkelGraph.GoodAux.eq_sdPt_of_decomp_inr (pq := (p, q)) (hpq := hpq) hd hcard
      subst hx
      rfl
  · rfl

/-! ## `wOf` of the canonical points of a copy of a simplex -/

/-- Two low dimensional points of `Raw` that are equal have the same graph element. -/
theorem wOf_congr_raw {D : MData X n x₀} {a b : Raw D} (h : a = b)
    (ha : isLowDim D a) (hb : isLowDim D b) :
    SkelGraph.wOf D ⟨a, ha⟩ = SkelGraph.wOf D ⟨b, hb⟩ := by
  subst h; exact SkelGraph.GoodAux.wOf_congr ha hb

/-- The graph element of the first end point of a `1`-face. -/
theorem wOf_edgePt_zero (D : MData X n x₀) (i : D.Idx) (p q : Fin (n+2)) (hpq : p < q)
    (h : isLowDim D (SkelGraph.edgePt D (Sum.inl (⟨i, ⟨(p,q),hpq⟩⟩ :
      Σ _ : D.Idx, {pq : Fin (n+2) × Fin (n+2) // pq.1 < pq.2})) (0 : I))) :
    SkelGraph.wOf D ⟨SkelGraph.edgePt D (Sum.inl (⟨i, ⟨(p,q),hpq⟩⟩ :
      Σ _ : D.Idx, {pq : Fin (n+2) × Fin (n+2) // pq.1 < pq.2})) (0 : I), h⟩
      = Sum.inl (SkelGraph.vCl D (Sum.inl ⟨i,p⟩)) := by
  have heq : SkelGraph.edgePt D (Sum.inl (⟨i, ⟨(p,q),hpq⟩⟩ :
      Σ _ : D.Idx, {pq : Fin (n+2) × Fin (n+2) // pq.1 < pq.2})) (0 : I)
      = (Sum.inl ⟨i, stdSimplex.vertex p⟩ : Raw D) := by
    show (Sum.inl ⟨i, SkelGraph.sdPt p q (0:I)⟩ : Raw D) = _
    rw [SkelGraph.sdPt_zero]
  have h' : isLowDim D (Sum.inl ⟨i, stdSimplex.vertex p⟩ : Raw D) := by
    rw [← heq]; exact h
  rw [wOf_congr_raw heq h h']
  exact SkelGraph.GoodAux.wOf_vertex i p _

/-- The graph element of the second end point of a `1`-face. -/
theorem wOf_edgePt_one (D : MData X n x₀) (i : D.Idx) (p q : Fin (n+2)) (hpq : p < q)
    (h : isLowDim D (SkelGraph.edgePt D (Sum.inl (⟨i, ⟨(p,q),hpq⟩⟩ :
      Σ _ : D.Idx, {pq : Fin (n+2) × Fin (n+2) // pq.1 < pq.2})) (1 : I))) :
    SkelGraph.wOf D ⟨SkelGraph.edgePt D (Sum.inl (⟨i, ⟨(p,q),hpq⟩⟩ :
      Σ _ : D.Idx, {pq : Fin (n+2) × Fin (n+2) // pq.1 < pq.2})) (1 : I), h⟩
      = Sum.inl (SkelGraph.vCl D (Sum.inl ⟨i,q⟩)) := by
  have heq : SkelGraph.edgePt D (Sum.inl (⟨i, ⟨(p,q),hpq⟩⟩ :
      Σ _ : D.Idx, {pq : Fin (n+2) × Fin (n+2) // pq.1 < pq.2})) (1 : I)
      = (Sum.inl ⟨i, stdSimplex.vertex q⟩ : Raw D) := by
    show (Sum.inl ⟨i, SkelGraph.sdPt p q (1:I)⟩ : Raw D) = _
    rw [SkelGraph.sdPt_one]
  have h' : isLowDim D (Sum.inl ⟨i, stdSimplex.vertex q⟩ : Raw D) := by
    rw [← heq]; exact h
  rw [wOf_congr_raw heq h h']
  exact SkelGraph.GoodAux.wOf_vertex i q _

/-- The graph element of an interior point of a `1`-face. -/
theorem wOf_edgePt_interior (D : MData X n x₀) (i : D.Idx) (p q : Fin (n+2)) (hpq : p < q)
    (s : I) (hs0 : 0 < (s : ℝ)) (hs1 : (s : ℝ) < 1)
    (h : isLowDim D (SkelGraph.edgePt D (Sum.inl (⟨i, ⟨(p,q),hpq⟩⟩ :
      Σ _ : D.Idx, {pq : Fin (n+2) × Fin (n+2) // pq.1 < pq.2})) s)) :
    SkelGraph.wOf D ⟨SkelGraph.edgePt D (Sum.inl (⟨i, ⟨(p,q),hpq⟩⟩ :
      Σ _ : D.Idx, {pq : Fin (n+2) × Fin (n+2) // pq.1 < pq.2})) s, h⟩
      = Sum.inr (SkelGraph.eCl D (Sum.inl (⟨i, ⟨(p,q),hpq⟩⟩ :
      Σ _ : D.Idx, {pq : Fin (n+2) × Fin (n+2) // pq.1 < pq.2})), s) := by
  show SkelGraph.wOf D ⟨(Sum.inl ⟨i, SkelGraph.sdPt p q s⟩ : Raw D), h⟩ = _
  exact SkelGraph.GoodAux.wOf_sdPt hpq hs0 hs1 _

/-! ## The graph element of the raw representative of a graph element -/

/-- **The third ingredient of the proof of `GraphElementData`.**  The graph element of the raw
representative `rawOf D w` of a graph element `w` is `gq`-equivalent to `w`. -/
theorem gq_wOf_rawOf (D : MData X n x₀) (w : SkelGraph.V D ⊕ (SkelGraph.E D × I)) :
    Work.RatHurewicz.gq (SkelGraph.a D) (SkelGraph.b D) (SkelGraph.wOf D (SkelGraph.rawOf D w))
      = Work.RatHurewicz.gq (SkelGraph.a D) (SkelGraph.b D) w := by
  rcases w with v | ⟨e, s⟩
  · rcases hout : Quotient.out v with ⟨i, p⟩ | ⟨i, k⟩
    · have hv : SkelGraph.vCl D (Sum.inl ⟨i, p⟩) = v := by
        rw [← hout]; exact Quotient.out_eq v
      have hw : SkelGraph.wOf D (SkelGraph.rawOf D (Sum.inl v))
          = Sum.inl (SkelGraph.vCl D (Sum.inl ⟨i, p⟩)) := by
        have h1 : SkelGraph.rawOf D (Sum.inl v) = ⟨SkelGraph.vertPt D (Sum.inl ⟨i, p⟩),
            SkelGraph.isLowDim_vertPt D _⟩ := by
          rw [show SkelGraph.rawOf D (Sum.inl v)
              = ⟨SkelGraph.vertPt D (Quotient.out v), SkelGraph.isLowDim_vertPt D _⟩ from rfl,
            hout]
        rw [h1]
        exact SkelGraph.GoodAux.wOf_vertex i p _
      rw [hw, hv]
    · have hv : SkelGraph.vCl D (Sum.inr ⟨i, k⟩) = v := by
        rw [← hout]; exact Quotient.out_eq v
      have hw : SkelGraph.wOf D (SkelGraph.rawOf D (Sum.inl v))
          = Sum.inr (SkelGraph.eCl D (Sum.inr ⟨i, PUnit.unit⟩), SkelGraph.arcEnd k) := by
        have h1 : SkelGraph.rawOf D (Sum.inl v) = ⟨SkelGraph.vertPt D (Sum.inr ⟨i, k⟩),
            SkelGraph.isLowDim_vertPt D _⟩ := by
          rw [show SkelGraph.rawOf D (Sum.inl v)
              = ⟨SkelGraph.vertPt D (Quotient.out v), SkelGraph.isLowDim_vertPt D _⟩ from rfl,
            hout]
        rw [h1]
        rfl
      rw [hw, ← hv]
      have hk : k = 0 ∨ k = 1 := by omega
      rcases hk with hk | hk
      · subst hk
        rw [SkelGraph.arcEnd_zero, Work.RatHurewicz.rel_ae, SkelGraph.GoodAux.a_eCl_inr]
      · subst hk
        rw [SkelGraph.arcEnd_one, Work.RatHurewicz.rel_be, SkelGraph.GoodAux.b_eCl_inr]
  · rcases hout : Quotient.out e with ⟨i, ⟨⟨p,q⟩,hpq⟩⟩ | ⟨i, u⟩
    · have he : SkelGraph.eCl D (Sum.inl ⟨i, ⟨(p,q),hpq⟩⟩) = e := by
        rw [← hout]; exact Quotient.out_eq e
      have hraw : SkelGraph.rawOf D (Sum.inr (e, s))
          = ⟨SkelGraph.edgePt D (Sum.inl ⟨i, ⟨(p,q),hpq⟩⟩) s,
             SkelGraph.isLowDim_edgePt D _ _⟩ := by
        rw [show SkelGraph.rawOf D (Sum.inr (e, s))
            = ⟨SkelGraph.edgePt D (Quotient.out e) s, SkelGraph.isLowDim_edgePt D _ _⟩ from rfl,
          hout]
      rw [hraw]
      by_cases h0 : (s : ℝ) = 0
      · have hs : s = (0 : I) := Subtype.ext h0
        subst hs
        rw [wOf_edgePt_zero D i p q hpq]
        rw [← he]
        rw [Work.RatHurewicz.rel_ae, SkelGraph.GoodAux.a_eCl_inl i p q hpq]
      · by_cases h1 : (s : ℝ) = 1
        · have hs : s = (1 : I) := Subtype.ext h1
          subst hs
          rw [wOf_edgePt_one D i p q hpq]
          rw [← he]
          rw [Work.RatHurewicz.rel_be, SkelGraph.GoodAux.b_eCl_inl i p q hpq]
        · have hs0 : 0 < (s : ℝ) := lt_of_le_of_ne s.2.1 (Ne.symm h0)
          have hs1 : (s : ℝ) < 1 := lt_of_le_of_ne s.2.2 h1
          rw [wOf_edgePt_interior D i p q hpq s hs0 hs1]
          rw [← he]
    · have hu : PUnit.unit = u := Subsingleton.elim _ _
      have he : SkelGraph.eCl D (Sum.inr ⟨i, PUnit.unit⟩) = e := by
        rw [show (Sum.inr (⟨i, PUnit.unit⟩ : Σ _ : D.Idx, PUnit) : SkelGraph.EdgeRaw D)
            = Sum.inr ⟨i, u⟩ from by rw [hu]]
        rw [← hout]; exact Quotient.out_eq e
      have hraw : SkelGraph.rawOf D (Sum.inr (e, s))
          = ⟨(Sum.inr ⟨i, s⟩ : Raw D), SkelGraph.GoodAux.isLowDim_inr i s⟩ := by
        rw [show SkelGraph.rawOf D (Sum.inr (e, s))
            = ⟨SkelGraph.edgePt D (Quotient.out e) s, SkelGraph.isLowDim_edgePt D _ _⟩ from rfl,
          hout]
        rfl
      rw [hraw, SkelGraph.wOf_inr, he]

/-! ## The canonical form of a point of a copy of a simplex after a face map -/

/-- The canonical form of a face of a point of a standard simplex that is a vertex. -/
theorem decomp_facept_inl {m : ℕ} (r : Fin (m+1)) (x : stdSimplex ℝ (Fin m)) (u : Fin m)
    (h : SkelGraph.decomp x = Sum.inl u) :
    SkelGraph.decomp (facept m r x) = Sum.inl (r.succAbove u) := by
  have hx : x = stdSimplex.vertex u := SkelGraph.GoodAux.eq_vertex_of_decomp_inl h
  subst hx
  show SkelGraph.decomp (stdSimplex.map r.succAbove (stdSimplex.vertex u))
    = Sum.inl (r.succAbove u)
  rw [stdSimplex.map_vertex]
  exact SkelGraph.GoodAux.decomp_vertex _

/-- The canonical form of a face of a point of a standard simplex on a `1`-face. -/
theorem decomp_facept_inr {m : ℕ} (r : Fin (m+2)) (x : stdSimplex ℝ (Fin (m+1)))
    (u v : Fin (m+1)) (huv : u < v) (t : I)
    (h : SkelGraph.decomp x = Sum.inr (⟨(⟨(u,v),huv⟩ :
        {pq : Fin (m+1) × Fin (m+1) // pq.1 < pq.2}), t⟩))
    (hcard : (SkelGraph.supp x).card ≤ 2) :
    SkelGraph.decomp (facept (m+1) r x) =
      Sum.inr (⟨(⟨(r.succAbove u, r.succAbove v),
        Fin.strictMono_succAbove r huv⟩ :
        {pq : Fin (m+2) × Fin (m+2) // pq.1 < pq.2}), t⟩) := by
  obtain ⟨hx, ht0, ht1⟩ :=
    SkelGraph.GoodAux.eq_sdPt_of_decomp_inr (pq := (u,v)) (hpq := huv) h hcard
  subst hx
  rw [SkelGraph.facept_sdPt (m := m)]
  exact SkelGraph.GoodAux.decomp_sdPt (p := r.succAbove u) (q := r.succAbove v)
    (Fin.strictMono_succAbove r huv) ht0 ht1

/-! ## `wOf` is constant on the gluing relation of the model -/

/-- **`wOf` is constant on the relation `modelRel D`.** -/
theorem gq_wOf_modelRel (D : MData X n x₀) {p q : Raw D} (h : modelRel D p q)
    (hp : isLowDim D p) (hq : isLowDim D q) :
    Work.RatHurewicz.gq (SkelGraph.a D) (SkelGraph.b D) (SkelGraph.wOf D ⟨p, hp⟩)
      = Work.RatHurewicz.gq (SkelGraph.a D) (SkelGraph.b D) (SkelGraph.wOf D ⟨q, hq⟩) := by
  rcases h with ⟨i, j, r, r', x, rfl, rfl, hs⟩ | ⟨i, rfl, rfl⟩ | ⟨i, j, rfl, rfl⟩
  · have hcardx : (SkelGraph.supp x).card ≤ 2 := by
      have hp' : (SkelGraph.supp (facept (n+1) r x)).card ≤ 2 :=
        (SkelGraph.GoodAux.isLowDim_inl_iff i (facept (n+1) r x)).mp hp
      have h2 : (SkelGraph.supp (facept (n+1) r x)).card = (SkelGraph.supp x).card := by
        show (SkelGraph.supp (stdSimplex.map r.succAbove x)).card = (SkelGraph.supp x).card
        rw [SkelGraph.GoodAux.supp_map r.succAbove r.succAbove_right_injective,
          Finset.card_image_of_injective _ r.succAbove_right_injective]
      exact h2 ▸ hp'
    rcases hdx : SkelGraph.decomp x with u | ⟨⟨⟨u,v⟩,huv⟩, t⟩
    · have hd1 : SkelGraph.decomp (facept (n+1) r x) = Sum.inl (r.succAbove u) :=
        decomp_facept_inl (m := n+1) r x u hdx
      have hd2 : SkelGraph.decomp (facept (n+1) r' x) = Sum.inl (r'.succAbove u) :=
        decomp_facept_inl (m := n+1) r' x u hdx
      rw [SkelGraph.wOf_inl_inl D i (facept (n+1) r x) hp _ hd1,
          SkelGraph.wOf_inl_inl D j (facept (n+1) r' x) hq _ hd2]
      have hvm : SkelGraph.vertM D (Sum.inl ⟨i, r.succAbove u⟩)
          = SkelGraph.vertM D (Sum.inl ⟨j, r'.succAbove u⟩) := by
        refine Quotient.sound (Relation.EqvGen.rel _ _
          (Or.inl ⟨i, j, r, r', stdSimplex.vertex u, ?_, ?_, hs⟩))
        · show (Sum.inl ⟨i, stdSimplex.vertex (r.succAbove u)⟩ : Raw D)
              = Sum.inl ⟨i, stdSimplex.map r.succAbove (stdSimplex.vertex u)⟩
          rw [stdSimplex.map_vertex]
        · show (Sum.inl ⟨j, stdSimplex.vertex (r'.succAbove u)⟩ : Raw D)
              = Sum.inl ⟨j, stdSimplex.map r'.succAbove (stdSimplex.vertex u)⟩
          rw [stdSimplex.map_vertex]
      rw [SkelGraph.vCl_eq_of_vertM_eq D hvm]
    · have hlt_r : r.succAbove u < r.succAbove v := Fin.strictMono_succAbove r huv
      have hlt_r' : r'.succAbove u < r'.succAbove v := Fin.strictMono_succAbove r' huv
      have hd1 : SkelGraph.decomp (facept (n+1) r x) =
          Sum.inr (⟨(⟨(r.succAbove u, r.succAbove v), hlt_r⟩ :
            {pq : Fin (n+2) × Fin (n+2) // pq.1 < pq.2}), t⟩) :=
        decomp_facept_inr (m := n) r x u v huv t hdx hcardx
      have hd2 : SkelGraph.decomp (facept (n+1) r' x) =
          Sum.inr (⟨(⟨(r'.succAbove u, r'.succAbove v), hlt_r'⟩ :
            {pq : Fin (n+2) × Fin (n+2) // pq.1 < pq.2}), t⟩) :=
        decomp_facept_inr (m := n) r' x u v huv t hdx hcardx
      rw [SkelGraph.wOf_inl_inr D i (facept (n+1) r x) hp _ t hd1,
          SkelGraph.wOf_inl_inr D j (facept (n+1) r' x) hq _ t hd2]
      have hee : SkelGraph.eCl D (Sum.inl ⟨i, (⟨(r.succAbove u, r.succAbove v), hlt_r⟩ :
            {pq : Fin (n+2) × Fin (n+2) // pq.1 < pq.2})⟩)
          = SkelGraph.eCl D (Sum.inl ⟨j, (⟨(r'.succAbove u, r'.succAbove v), hlt_r'⟩ :
            {pq : Fin (n+2) × Fin (n+2) // pq.1 < pq.2})⟩) := by
        refine Quotient.sound (fun s => ?_)
        show Quotient.mk'' ((Sum.inl ⟨i, SkelGraph.sdPt (r.succAbove u) (r.succAbove v) s⟩) : Raw D)
            = Quotient.mk'' ((Sum.inl ⟨j, SkelGraph.sdPt (r'.succAbove u) (r'.succAbove v) s⟩)
              : Raw D)
        refine Quotient.sound (Relation.EqvGen.rel _ _
          (Or.inl ⟨i, j, r, r', SkelGraph.sdPt u v s, ?_, ?_, hs⟩))
        · rw [SkelGraph.facept_sdPt (m := n)]
        · rw [SkelGraph.facept_sdPt (m := n)]
      rw [hee]
  · rw [SkelGraph.GoodAux.wOf_vertex i 0 hp, SkelGraph.wOf_inr,
        Work.RatHurewicz.rel_ae, SkelGraph.GoodAux.a_eCl_inr]
    have hvm : SkelGraph.vertM D (Sum.inl ⟨i, (0:Fin (n+2))⟩)
        = SkelGraph.vertM D (Sum.inr ⟨i, (0:Fin 2)⟩) := by
      refine Quotient.sound (Relation.EqvGen.rel _ _ (Or.inr (Or.inl ⟨i, ?_, ?_⟩)))
      · rfl
      · show (Sum.inr ⟨i, SkelGraph.arcEnd (0:Fin 2)⟩ : Raw D) = Sum.inr ⟨i, (0:I)⟩
        rw [SkelGraph.arcEnd_zero]
    rw [SkelGraph.vCl_eq_of_vertM_eq D hvm]
  · rw [SkelGraph.wOf_inr, SkelGraph.wOf_inr, Work.RatHurewicz.rel_be, Work.RatHurewicz.rel_be,
        SkelGraph.GoodAux.b_eCl_inr i, SkelGraph.GoodAux.b_eCl_inr j]
    have hvm : SkelGraph.vertM D (Sum.inr ⟨i, (1:Fin 2)⟩)
        = SkelGraph.vertM D (Sum.inr ⟨j, (1:Fin 2)⟩) := by
      refine Quotient.sound (Relation.EqvGen.rel _ _ (Or.inr (Or.inr ⟨i, j, ?_, ?_⟩)))
      · show (Sum.inr ⟨i, SkelGraph.arcEnd (1:Fin 2)⟩ : Raw D) = Sum.inr ⟨i, (1:I)⟩
        rw [SkelGraph.arcEnd_one]
      · show (Sum.inr ⟨j, SkelGraph.arcEnd (1:Fin 2)⟩ : Raw D) = Sum.inr ⟨j, (1:I)⟩
        rw [SkelGraph.arcEnd_one]
    rw [SkelGraph.vCl_eq_of_vertM_eq D hvm]

/-- **`wOf` is constant on the equivalence closure of `modelRel D`.** -/
theorem gq_wOf_eqvGen (D : MData X n x₀) {p q : Raw D}
    (h : Relation.EqvGen (modelRel D) p q) (hp : isLowDim D p) (hq : isLowDim D q) :
    Work.RatHurewicz.gq (SkelGraph.a D) (SkelGraph.b D) (SkelGraph.wOf D ⟨p, hp⟩)
      = Work.RatHurewicz.gq (SkelGraph.a D) (SkelGraph.b D) (SkelGraph.wOf D ⟨q, hq⟩) := by
  revert hp hq
  induction h with
  | rel x y hxy =>
      intro hp hq
      exact gq_wOf_modelRel D hxy hp hq
  | refl x =>
      intro hp hq
      exact congrArg (Work.RatHurewicz.gq (SkelGraph.a D) (SkelGraph.b D))
        (SkelGraph.GoodAux.wOf_congr hp hq)
  | symm x y hxy ih =>
      intro hp hq
      exact (ih hq hp).symm
  | trans x y z hxy hyz ihxy ihyz =>
      intro hp hz
      have hy : isLowDim D y := (SkelGraph.GoodAux.isLowDim_eqvGen hxy).mp hp
      exact (ihxy hp hy).trans (ihyz hy hz)

/-! ## The graph element data -/

theorem graphElementData {X : Type} [TopologicalSpace X] {x₀ : X} {n : ℕ}
    (D : Work.RatHurewicz.MData X n x₀) :
    Work.RatHurewicz.SkelGraph.GraphElementData D := by
  refine ⟨fun y => Work.RatHurewicz.gq (SkelGraph.a D) (SkelGraph.b D) (SkelGraph.wOf D y),
    ?_, ?_, ?_⟩
  · intro y
    rw [SkelGraph.Phi_apply]
    exact psi_wOf D y
  · intro y w hw
    have h1 : SkelGraph.toSkeleton D (SkelGraph.rawOf D w) = SkelGraph.toSkeleton D y := by
      rw [← SkelGraph.psi_rawOf D w]; exact hw
    have hrel : Relation.EqvGen (modelRel D) (SkelGraph.rawOf D w).1 y.1 := by
      exact Quotient.eq.mp (congrArg Subtype.val h1)
    have h3 := gq_wOf_eqvGen D hrel (SkelGraph.rawOf D w).2 y.2
    rw [gq_wOf_rawOf D w] at h3
    exact h3.symm
  · intro y y' h
    exact gq_wOf_eqvGen D h y.2 y'.2

end

end Work.RatHurewicz.PiOneSkel
