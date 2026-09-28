import Mathlib
import Submission.Work.RatHurewicz.finiteGraphDefs
import Submission.Work.RatHurewicz.GraphPi.spiderDefs
import Submission.Work.RatHurewicz.GraphPi.spiderLocal

/-!
# The spider of a vertex is contractible

For a finite graph `GraphX a b = (V ⊕ (E × I)) / ~` (see `RatHurewicz/finiteGraphDefs`), the
*spider* (`Work.RatHurewicz.spider a b v`) of a vertex `v` is the vertex together with a short open
germ of every incident edge end — a finite wedge of half-open arcs glued at `v`, hence contractible.

The contraction is the "shrink toward the vertex" map, and the whole point of this file is that it
can be written with a **single continuous formula** on representatives:

`shrinkRaw : (V ⊕ (E × I)) × I → V ⊕ (E × I)`,
`Sum.inl w ↦ Sum.inl w`, `Sum.inr (e, s) ↦ Sum.inr (e, sShrink t s)`

where `sShrink t s = s + t (θ s - s)` and `θ` is `0` on `[0,1/3]`, `1` on `[2/3,1]`
(`GraphPi/spiderDefs`).  On the `a`-germ of the spider (`s < 1/3`, so `θ s = 0`) this is
`s ↦ (1 - t) s`, on the `b`-germ (`2/3 < s`, so `θ s = 1`) it is `s ↦ 1 - (1-t)(1-s)`: exactly the
two required branches, and because `θ` is continuous no gluing argument is needed at all.

Since `shrinkRaw` fixes `s = 0` and `s = 1`, it is constant on the classes of `gq a b`
(`spiderShrinkRel`), so it descends to the graph; it preserves the spider (`spiderShrinkMem`,
via the explicit computation of the preimage of the spider in `GraphPi/spiderLocal`), and the
restriction of the descended map to the spider is the required homotopy from the identity to the
constant map at the vertex.

## Main result

* `Work.RatHurewicz.GraphPi.spiderContractible`
-/

namespace Work.RatHurewicz.GraphPi

open scoped unitInterval Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false

variable {E V : Type} [Fintype E] [Fintype V] [TopologicalSpace E] [DiscreteTopology E]
  [TopologicalSpace V] [DiscreteTopology V]

noncomputable section

/-! ## The shrink map is constant on the classes of the graph -/

/-- `shrinkRaw` respects the generating relation of the graph: it fixes the two ends `0` and `1`
of every edge. -/
theorem shrinkRaw_rel (a b : E → V) (t : I) {p q : V ⊕ (E × I)} (h : graphRel a b p q) :
    gq a b (shrinkRaw (p, t)) = gq a b (shrinkRaw (q, t)) := by
  rcases h with ⟨e, rfl, rfl⟩ | ⟨e, rfl, rfl⟩ | ⟨e, rfl, rfl⟩ | ⟨e, rfl, rfl⟩
  · rw [shrinkRaw_inl, shrinkRaw_inr, sShrink_left_zero]
    exact (rel_ae a b e).symm
  · rw [shrinkRaw_inl, shrinkRaw_inr, sShrink_right_one]
    exact (rel_be a b e).symm
  · rw [shrinkRaw_inl, shrinkRaw_inr, sShrink_left_zero]
    exact rel_ae a b e
  · rw [shrinkRaw_inl, shrinkRaw_inr, sShrink_right_one]
    exact rel_be a b e

theorem shrinkRaw_rel_evg (a b : E → V) (t : I) {p q : V ⊕ (E × I)}
    (h : Relation.EqvGen (graphRel a b) p q) :
    gq a b (shrinkRaw (p, t)) = gq a b (shrinkRaw (q, t)) := by
  induction h with
  | rel x y hxy => exact shrinkRaw_rel a b t hxy
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

/-- **Well-definedness of the descent.**  Points of `V ⊕ (E × I)` with the same image in the graph
have shrunk images with the same image in the graph; equivalently, `shrinkRaw (·, t)` descends to
the graph. -/
theorem spiderShrinkRel (a b : E → V) (t : I) {p p' : V ⊕ (E × I)}
    (h : gq a b p = gq a b p') :
    gq a b (shrinkRaw (p, t)) = gq a b (shrinkRaw (p', t)) :=
  shrinkRaw_rel_evg a b t ((Quotient.eq'' (s₁ := graphSetoid a b)).mp h)

/-! ## The shrink map preserves the spider -/

/-- **The shrink map preserves the spider of `v`**: it moves the `a`-germ (`s < 1/3`) toward `0`
and the `b`-germ (`2/3 < s`) toward `1`, so nothing leaves the spider. -/
theorem spiderShrinkMem (a b : E → V) (v : V) (p : V ⊕ (E × I)) (t : I)
    (hp : gq a b p ∈ spider a b v) :
    gq a b (shrinkRaw (p, t)) ∈ spider a b v := by
  have hp' : p ∈ spiderA a v ∪ spiderB b v := by
    rw [← preimage_spider a b v]
    exact hp
  rcases p with w | ⟨e, s⟩
  · rw [shrinkRaw_inl]
    exact hp
  · rcases hp' with hA | hB
    · obtain ⟨ha, hs⟩ := (mem_spiderA_inr a v).mp hA
      rw [shrinkRaw_inr, ← ha]
      exact mem_spider_of_a a b e (lt_of_le_of_lt (sShrink_le_of_le_third (le_of_lt hs)) hs)
    · obtain ⟨hb, hs⟩ := (mem_spiderB_inr b v).mp hB
      rw [shrinkRaw_inr, ← hb]
      exact mem_spider_of_b a b e (lt_of_lt_of_le hs (le_sShrink_of_two_thirds_le (le_of_lt hs)))

/-! ## The descent of the shrink map through the quotient -/

def gqC (a b : E → V) : C(V ⊕ (E × I), GraphX a b) where
  toFun := gq a b
  continuous_toFun := continuous_quotient_mk'

def shrinkRawC : C((V ⊕ (E × I)) × I, V ⊕ (E × I)) where
  toFun := shrinkRaw
  continuous_toFun := continuous_shrinkRaw

/-- The shrink map, curried: `p ↦ (t ↦ gq (shrinkRaw (p, t)))`. -/
def shrinkCurried (a b : E → V) : C(V ⊕ (E × I), C(I, GraphX a b)) :=
  ((gqC a b).comp shrinkRawC).curry

theorem shrinkCurried_apply (a b : E → V) (p : V ⊕ (E × I)) (t : I) :
    shrinkCurried a b p t = gq a b (shrinkRaw (p, t)) := by
  show (((gqC a b).comp shrinkRawC).curry p) t = _
  rw [ContinuousMap.curry_apply]
  rfl

theorem shrinkCurried_factors (a b : E → V) :
    Function.FactorsThrough (shrinkCurried a b) (gqC a b) := by
  intro p p' h
  ext t
  rw [shrinkCurried_apply, shrinkCurried_apply]
  exact spiderShrinkRel a b t h

/-- The desc**ent** of the shrink map to the graph: a genuine homotopy
`GraphX × I → GraphX` (not only on the spider). -/
def shrinkDescended (a b : E → V) : C(GraphX a b, C(I, GraphX a b)) :=
  Topology.IsQuotientMap.lift (f := gqC a b) (isQuotientMap_quotient_mk' (s := graphSetoid a b))
    (shrinkCurried a b) (shrinkCurried_factors a b)

/-- The computation rule of the descended map, on representatives. -/
theorem shrinkDescended_apply (a b : E → V) (p : V ⊕ (E × I)) :
    shrinkDescended a b (gq a b p) = shrinkCurried a b p :=
  DFunLike.congr_fun
    (Topology.IsQuotientMap.lift_comp (f := gqC a b)
      (isQuotientMap_quotient_mk' (s := graphSetoid a b)) (shrinkCurried a b)
      (shrinkCurried_factors a b)) p

/-- The descended shrink map, uncurried. -/
def shrinkHom (a b : E → V) : C(GraphX a b × I, GraphX a b) :=
  (shrinkDescended a b).uncurry

theorem shrinkHom_gq (a b : E → V) (p : V ⊕ (E × I)) (t : I) :
    shrinkHom a b (gq a b p, t) = gq a b (shrinkRaw (p, t)) := by
  show (shrinkDescended a b (gq a b p)) t = gq a b (shrinkRaw (p, t))
  rw [shrinkDescended_apply, shrinkCurried_apply]

/-! ## Computation rules for the descended map -/

theorem shrinkHom_zero (a b : E → V) (x : GraphX a b) : shrinkHom a b (x, 0) = x := by
  induction x using Quotient.inductionOn with
  | h p =>
    change shrinkHom a b (gq a b p, (0 : I)) = gq a b p
    rw [shrinkHom_gq, shrinkRaw_zero]

/-- On representatives: at time `1` the descended shrink map sends the spider to its vertex. -/
theorem shrinkHom_one_rep (a b : E → V) (v : V) (p : V ⊕ (E × I))
    (hp : gq a b p ∈ spider a b v) : shrinkHom a b (gq a b p, 1) = gq a b (Sum.inl v) := by
  rw [shrinkHom_gq]
  have hp' : p ∈ spiderA a v ∪ spiderB b v := by
    rw [← preimage_spider a b v]
    exact hp
  rcases p with w | ⟨e, s⟩
  · have hw : w = v := (mem_spiderAB_inl a b v).mp hp'
    rw [shrinkRaw_inl, hw]
  · rcases hp' with hA | hB
    · obtain ⟨ha, hs⟩ := (mem_spiderA_inr a v).mp hA
      rw [shrinkRaw_inr]
      have hzero : sShrink 1 s = 0 := by
        apply Subtype.ext
        rw [sShrink_coe]
        unfold sShrinkVal
        rw [thetaVal_eq_zero (le_of_lt hs)]
        norm_num
      rw [hzero, ← ha]
      exact rel_ae a b e
    · obtain ⟨hb, hs⟩ := (mem_spiderB_inr b v).mp hB
      rw [shrinkRaw_inr]
      have hone : sShrink 1 s = 1 := by
        apply Subtype.ext
        rw [sShrink_coe]
        unfold sShrinkVal
        rw [thetaVal_eq_one (le_of_lt hs)]
        norm_num
      rw [hone, ← hb]
      exact rel_be a b e

/-- At time `1` the descended shrink map is constant on the spider, with value the vertex. -/
theorem shrinkHom_one (a b : E → V) (v : V) (x : ↥(spider a b v)) :
    shrinkHom a b (x.1, 1) = gq a b (Sum.inl v) := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨p, rfl⟩ := Quotient.mk''_surjective (s₁ := graphSetoid a b) x
  exact shrinkHom_one_rep a b v p hx

/-- The descended shrink map never leaves the spider. -/
theorem shrinkHom_mem (a b : E → V) (v : V) {x : GraphX a b} (hx : x ∈ spider a b v) (t : I) :
    shrinkHom a b (x, t) ∈ spider a b v := by
  obtain ⟨p, rfl⟩ := Quotient.mk''_surjective (s₁ := graphSetoid a b) x
  change shrinkHom a b (gq a b p, t) ∈ spider a b v
  rw [shrinkHom_gq]
  exact spiderShrinkMem a b v p t hx

/-! ## The homotopy and the contraction -/

def spiderShrinkHom (a b : E → V) (v : V) : C(↥(spider a b v) × I, ↥(spider a b v)) where
  toFun := fun q => ⟨shrinkHom a b (q.1.1, q.2), shrinkHom_mem a b v q.1.2 q.2⟩
  continuous_toFun := Continuous.subtype_mk
    ((shrinkHom a b).continuous.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd))
    (fun q => shrinkHom_mem a b v q.1.2 q.2)

def spiderShrinkMap (a b : E → V) (v : V) : C(I × ↥(spider a b v), ↥(spider a b v)) where
  toFun := fun q => spiderShrinkHom a b v (q.2, q.1)
  continuous_toFun := (spiderShrinkHom a b v).continuous.comp
    (continuous_snd.prodMk continuous_fst)

/-- **The contraction homotopy** of the spider: the identity is homotopic to the constant map at
the vertex. -/
def spiderHomotopy (a b : E → V) (v : V) :
    ContinuousMap.Homotopy (ContinuousMap.id ↥(spider a b v))
      (ContinuousMap.const _ ⟨gq a b (Sum.inl v), mem_spider_center a b v⟩) :=
  ContinuousMap.Homotopy.mk (spiderShrinkMap a b v)
    (by
      intro x
      apply Subtype.ext
      show shrinkHom a b (x.1, 0) = x.1
      exact shrinkHom_zero a b x.1)
    (by
      intro x
      apply Subtype.ext
      show shrinkHom a b (x.1, 1) = gq a b (Sum.inl v)
      exact shrinkHom_one a b v x)

end

/-- The star (spider) of a vertex is contractible: it is the vertex together with a short open
germ of every incident edge end, i.e. a finite wedge of half-open arcs glued at the vertex.

Suggested route: define the "shrink toward the vertex" map on the preimage
`(gq a b) ⁻¹' (spider a b v) ⊆ V ⊕ (E × I)` — there it is a plain product formula,
`(e, s) ↦ (e, (1 - t) * s)` on the `a`-side and `(e, s) ↦ (e, 1 - (1 - t) * (1 - s))` on the
`b`-side, and it is continuous — then descend it through the quotient using
`Topology.IsQuotientMap.restrictPreimage_isOpen` (the spider is open; prove it locally or import
`RatHurewicz/GraphPi/spiderLocal`) together with `Topology.IsQuotientMap.continuous_iff`, and
package the resulting homotopy as a `ContinuousMap.Homotopy (ContinuousMap.id _)
(ContinuousMap.const _ (gq a b (Sum.inl v)))` so that `contractible_iff_id_nullhomotopic`
applies. -/
theorem spiderContractible {E V : Type} [Fintype E] [Fintype V] [TopologicalSpace E] [DiscreteTopology E] [TopologicalSpace V] [DiscreteTopology V] (a b : E → V) (v : V) :
    ContractibleSpace ↥(Work.RatHurewicz.spider a b v) :=
  (contractible_iff_id_nullhomotopic _).mpr
    ⟨⟨Work.RatHurewicz.gq a b (Sum.inl v), Work.RatHurewicz.mem_spider_center a b v⟩,
      ⟨spiderHomotopy a b v⟩⟩

end Work.RatHurewicz.GraphPi
