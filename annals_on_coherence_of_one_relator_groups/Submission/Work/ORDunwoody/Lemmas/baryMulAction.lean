import Mathlib
import Submission.Work.ORDunwoody.Tracks.Level

set_option autoImplicit false
set_option warn.classDefReducibility false

namespace Work.ORDunwoody.Lemmas

open Work.ORDunwoody

universe u v

variable {G : Type u} [Group G] {V : Type v} [MulAction G V]

/-- The induced map on edges: an edge `{u,v}` of `T` is sent to `{g • u, g • v}`, which is again
an edge of `T` because the action preserves adjacency. -/
theorem baryEdgeMap_mem (T : GTree G V) (g : G) {e : Sym2 V} (he : e ∈ T.graph.edgeSet) :
    Sym2.map (fun w : V => g • w) e ∈ T.graph.edgeSet := by
  induction e using Sym2.ind with
  | h a b => exact T.smul_adj g he

/-- The action of `G` on the vertex type of the barycentric subdivision of `T`: original
vertices keep the given action and an edge is sent to the edge spanned by the images of its
endpoints. -/
def barySmul (T : GTree G V) (g : G) :
    (V ⊕ {e : Sym2 V // e ∈ T.graph.edgeSet}) → (V ⊕ {e : Sym2 V // e ∈ T.graph.edgeSet})
  | Sum.inl v => Sum.inl (g • v)
  | Sum.inr e => Sum.inr ⟨Sym2.map (fun w : V => g • w) (e : Sym2 V), baryEdgeMap_mem T g e.2⟩

/-- The `MulAction` of `G` on the barycentric subdivision of `T`. -/
noncomputable def baryMulActionInst (T : GTree G V) :
    MulAction G (V ⊕ {e : Sym2 V // e ∈ T.graph.edgeSet}) where
  toSMul := ⟨barySmul T⟩
  one_smul := by
    intro x
    cases x with
    | inl v => exact congrArg Sum.inl (one_smul G v)
    | inr e =>
      apply congrArg Sum.inr
      apply Subtype.ext
      show Sym2.map (fun w : V => (1 : G) • w) (e : Sym2 V) = (e : Sym2 V)
      simp only [one_smul, Sym2.map_id', id_eq]
  mul_smul := by
    intro g h x
    cases x with
    | inl v => exact congrArg Sum.inl (mul_smul g h v)
    | inr e =>
      apply congrArg Sum.inr
      apply Subtype.ext
      show Sym2.map (fun w : V => (g * h) • w) (e : Sym2 V) =
        Sym2.map (fun w : V => g • w) (Sym2.map (fun w : V => h • w) (e : Sym2 V))
      rw [Sym2.map_map]
      exact Sym2.map_congr (fun x _ => mul_smul g h x)

/-- **The action on the barycentric subdivision.**  If `G` acts on the tree `T` by graph
automorphisms, then it acts on the barycentric subdivision of `T` (vertex type
`V ⊕ {e : Sym2 V // e ∈ T.edgeSet}`, two vertices being adjacent in the subdivision exactly when
one is an original vertex `v`, the other an edge `e` of `T`, and `v ∈ e`): the original vertices
keep the given action and an edge `{u,v}` of `T` is sent to `{g • u, g • v}`.

Concretely, the displayed condition says that if `v` is an endpoint of the edge `e`, then the
image of `v` (which is `g • v`) is an endpoint of the image of `e`.  This is what lets the
subdivided target be used as a `G`-tree in the cellular model of Dunwoody's resolution. -/
theorem baryMulAction {G : Type*} [Group G] {V : Type*} [MulAction G V] (T : GTree G V) :
    ∃ inst : MulAction G (V ⊕ {e : Sym2 V // e ∈ T.graph.edgeSet}),
      (∀ (g : G) (v : V), inst.smul g (Sum.inl v) = Sum.inl (g • v)) ∧
      (∀ (g : G) (v : V) (e : {e : Sym2 V // e ∈ T.graph.edgeSet}), (v : V) ∈ (e : Sym2 V) →
        ∃ (v' : V) (e' : {e : Sym2 V // e ∈ T.graph.edgeSet}),
          inst.smul g (Sum.inl v) = Sum.inl v' ∧ inst.smul g (Sum.inr e) = Sum.inr e' ∧
            (v' : V) ∈ (e' : Sym2 V)) := by
  refine ⟨baryMulActionInst T, ?_, ?_⟩
  · intro g v
    change barySmul T g (Sum.inl v) = Sum.inl (g • v)
    rfl
  · intro g v e hv
    refine ⟨g • v, ⟨Sym2.map (fun w : V => g • w) (e : Sym2 V), baryEdgeMap_mem T g e.2⟩,
      ?_, ?_, ?_⟩
    · change barySmul T g (Sum.inl v) = Sum.inl (g • v); rfl
    · change barySmul T g (Sum.inr e) =
        Sum.inr ⟨Sym2.map (fun w : V => g • w) (e : Sym2 V), baryEdgeMap_mem T g e.2⟩
      rfl
    · exact Sym2.mem_map.mpr ⟨v, hv, rfl⟩

end Work.ORDunwoody.Lemmas
