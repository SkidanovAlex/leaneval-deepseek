/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# A finitely generated group acting on a tree has a cocompact invariant subtree

Let `G` act on a tree `T` (a `GTree G V`, see `Submission.Work.ORDunwoody.Basic`) and let
`H ≤ G` be finitely generated.  Then there is a cocompact `H`-tree `S` which is dominated by
`T` over the inclusion `H ↪ G`.

The construction: choose a finite generating set `S₀` of `H`, a base vertex `v₀` and, for
each `s : G`, a walk `p s : v₀ → s • v₀` (the tree is connected).  Let `A` be the finite
"seed" subtree obtained as the union of the walk subgraphs `(p s).toSubgraph` for `s ∈ S₀`
together with the vertex `v₀`, and let `D` be its `H`-orbit closure, i.e. the subgraph whose
edges are the `H`-translates of the edges of `A`
(`Submission.Work.ORDunwoody.Lemmas.OrbitSubtreeDefs`), on the vertex set
`X = ⋃_{h : H} h • A.verts`.

`D` is connected: `v₀` is joined to `h • v₀` for every `h ∈ H` by writing `h` as a word in
`S₀`, and `H` acts on `D` by graph automorphisms.  `D` is acyclic since it embeds in the
acyclic graph of `T`.  It is cocompact because the finite sets of vertices and of oriented
edges of `A` meet every vertex and every edge orbit.  Finally, since `H` is finitely
generated the orbit closure `X` is countable, so `D` may be transported to a type in any
universe by choosing an equivalent type in that universe (this is what makes the statement
below universe-polymorphic in the vertex type of the tree one constructs).

The result is `Work.ORDunwoody.CocompactSubtree` of `Submission.Work.ORDunwoody.Hypotheses`.
-/
import Mathlib
import Submission.Work.ORDunwoody.Basic
import Submission.Work.ORDunwoody.Lemmas.OrbitSubtreeDefs
import Submission.Work.ORDunwoody.Lemmas.isCocompact_iff_transversal

set_option autoImplicit false
set_option linter.unusedVariables false

universe u v w

namespace Work.ORDunwoody.Lemmas

open Work.ORDunwoody
open SimpleGraph

variable {G : Type u} [Group G] {V : Type v} [MulAction G V]

/-! ## Auxiliary facts about walks and orbit closures -/

/-- The action of `h : H` on the orbit closure of a subgraph, as a graph homomorphism. -/
def orbitActHom (T : GTree G V) (H : Subgroup G) (A : T.graph.Subgraph) (g : H) :
    (orbitSubgraph T H A).coe →g (orbitSubgraph T H A).coe where
  toFun x := ⟨g • x.1, orbitSubgraph.smul_mem_verts g x.2⟩
  map_rel' hxy := orbitSubgraph.adj_smul g hxy

/-- Reachability of two vertices of a graph given an equality between them. -/
theorem reachable_of_eq {G' : SimpleGraph V} {u v : V} (h : u = v) : G'.Reachable u v := by
  subst h
  exact Reachable.rfl

/-- Membership in `walkPairFinset w` is exactly adjacency in the graph carried by the
subgraph `w.toSubgraph` of the walk `w`. -/
theorem mem_walkPairFinset_iff {G' : SimpleGraph V} {u v : V} (w : G'.Walk u v) {a b : V} :
    (a, b) ∈ walkPairFinset w ↔ w.toSubgraph.Adj a b := by
  classical
  constructor
  · intro h
    rw [walkPairFinset, Finset.mem_union] at h
    rcases h with h | h
    · obtain ⟨i, hi, hif⟩ := Finset.mem_image.mp h
      rw [Finset.mem_range] at hi
      have h1 : w.getVert i = a := congrArg Prod.fst hif
      have h2 : w.getVert (i + 1) = b := congrArg Prod.snd hif
      rw [← h1, ← h2]
      exact w.toSubgraph_adj_getVert hi
    · obtain ⟨i, hi, hif⟩ := Finset.mem_image.mp h
      rw [Finset.mem_range] at hi
      have h1 : w.getVert (i + 1) = a := congrArg Prod.fst hif
      have h2 : w.getVert i = b := congrArg Prod.snd hif
      rw [← h1, ← h2]
      exact (w.toSubgraph_adj_getVert hi).symm
  · intro h
    obtain ⟨i, hi, hlt⟩ := (Walk.toSubgraph_adj_iff w).mp h
    rw [walkPairFinset, Finset.mem_union]
    have hi' : i ∈ Finset.range w.length := by rw [Finset.mem_range]; exact hlt
    have hmem₁ : (w.getVert i, w.getVert (i + 1)) ∈
        (Finset.range w.length).image (fun i => (w.getVert i, w.getVert (i + 1))) :=
      Finset.mem_image.mpr ⟨i, hi', rfl⟩
    have hmem₂ : (w.getVert (i + 1), w.getVert i) ∈
        (Finset.range w.length).image (fun i => (w.getVert (i + 1), w.getVert i)) :=
      Finset.mem_image.mpr ⟨i, hi', rfl⟩
    rcases Sym2.eq_iff.mp hi.symm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl hmem₁
    · exact Or.inr hmem₂

/-- Every vertex in the support of a walk is reachable, in the graph carried by the walk's
subgraph, from the start of the walk. -/
theorem walk_toSubgraph_reachable {G' : SimpleGraph V} {u v : V} (w : G'.Walk u v) :
    ∀ {a : V} (ha : a ∈ w.support),
      w.toSubgraph.coe.Reachable ⟨u, w.start_mem_verts_toSubgraph⟩
        ⟨a, w.mem_verts_toSubgraph.mpr ha⟩ := by
  induction w with
  | nil =>
      intro a ha
      rw [Walk.support_nil, List.mem_singleton] at ha
      exact reachable_of_eq (Subtype.ext ha.symm)
  | cons hxy pw ih =>
      intro a ha
      rw [Walk.support_cons, List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact Reachable.rfl
      · have hsle : G'.subgraphOfAdj hxy ≤ (Walk.cons hxy pw).toSubgraph := le_sup_left
        have hstep := (Subgraph.Adj.coe
          (hsle.2 (subgraphOfAdj_adj_self hxy))).reachable
        have hrec := Reachable.map (Subgraph.inclusion
          (le_sup_right : pw.toSubgraph ≤ (Walk.cons hxy pw).toSubgraph)) (ih ha)
        exact hstep.trans hrec

/-! ## The construction in the universe of the tree -/

/-- **The cocompact invariant subtree**, with the vertex type of the constructed tree living
in an arbitrary prescribed universe `w`.

The vertex set of the tree we build is countable (it is the orbit closure of a finite
subtree under a finitely generated group), so after constructing it inside the universe of
`T` we may transport it to any universe `w`. -/
theorem exists_cocompact_invariant_subtree_aux {G : Type u} [Group G] {V : Type v}
    [MulAction G V] (T : GTree G V) (H : Subgroup G) (hH : H.FG) :
    ∃ (W : Type w) (_ : MulAction H W) (S : GTree H W),
      S.IsCocompact ∧ DominatesOver H.subtype S T := by
  classical
  -- ## Setup: a finite generating set, a base vertex, and walks from the base vertex
  obtain ⟨S0, hS0⟩ := Subgroup.isMulFG_iff.mp hH
  have hne : Nonempty V := T.isTree.connected.nonempty
  let v0 : V := Classical.choice hne
  let p : ∀ s : G, T.graph.Walk v0 (s • v0) :=
    fun s => Classical.choice (T.isTree.connected.preconnected v0 (s • v0))
  -- ## The seed subgraph and its orbit closure
  let A : T.graph.Subgraph := seedSubgraph T S0 v0 p
  let D : T.graph.Subgraph := orbitSubgraph T H A
  let GD : SimpleGraph ↥(orbitVertSet H A.verts) := D.coe
  have hv0A : v0 ∈ A.verts := v0_mem_seedSubgraph_verts T S0 v0 p
  have hv0X : v0 ∈ orbitVertSet H A.verts := (subset_orbitVertSet (H := H) A.verts) hv0A
  -- ## The finite sets of seed vertices and seed edges
  have hAV : A.verts ⊆ ↑(seedVertsFinset T.graph S0 v0 p) := by
    intro x hx
    have hx' : x ∈ (seedSubgraph T S0 v0 p).verts := hx
    rw [seedSubgraph_verts_eq] at hx'
    rcases hx' with hx' | hx'
    · rw [Set.mem_iUnion] at hx'
      obtain ⟨s, hs⟩ := hx'
      have hsupp : x ∈ (p s.1).support := by
        rw [Walk.verts_toSubgraph] at hs
        exact hs
      exact mem_seedVertsFinset_of_mem_support T.graph S0 v0 p s.2 hsupp
    · rw [Set.mem_singleton_iff] at hx'
      rw [hx']
      exact v0_mem_seedVertsFinset T.graph S0 v0 p
  have hVA : ↑(seedVertsFinset T.graph S0 v0 p) ⊆ A.verts := by
    intro x hx
    rw [seedVertsFinset] at hx
    rcases Finset.mem_insert.mp hx with hx0 | hx
    · rw [hx0]
      exact hv0A
    · obtain ⟨⟨s, hs⟩, -, hxs⟩ := Finset.mem_biUnion.mp hx
      have hs' : x ∈ (p s).toSubgraph.verts := by
        rw [Walk.verts_toSubgraph]
        exact List.mem_toFinset.mp hxs
      have hmem : x ∈ (⋃ t : {t // t ∈ S0}, (p t.1).toSubgraph.verts) :=
        le_iSup (fun t : {t // t ∈ S0} => (p t.1).toSubgraph.verts) ⟨s, hs⟩ hs'
      have : x ∈ (seedSubgraph T S0 v0 p).verts := by
        rw [seedSubgraph_verts_eq]
        exact Or.inl hmem
      exact this
  have hVD : ∀ v ∈ seedVertsFinset T.graph S0 v0 p, v ∈ orbitVertSet H A.verts :=
    fun v hv => (subset_orbitVertSet (H := H) A.verts) (hVA hv)
  have hEseed : ∀ a b : V, A.Adj a b → (a, b) ∈ seedEdgesFinset T.graph S0 v0 p := by
    intro a b hab
    have hab' : (seedSubgraph T S0 v0 p).Adj a b := hab
    obtain ⟨s, hs⟩ := seedSubgraph_adj_iff.mp hab'
    exact Finset.mem_biUnion.mpr ⟨s, Finset.mem_univ _, (mem_walkPairFinset_iff (p s.1)).mpr hs⟩
  have hAE : ∀ e ∈ seedEdgesFinset T.graph S0 v0 p, A.Adj e.1 e.2 := by
    intro e he
    obtain ⟨s, -, hes⟩ := Finset.mem_biUnion.mp he
    exact seedSubgraph_adj_iff.mpr ⟨s, (mem_walkPairFinset_iff (p s.1)).mp hes⟩
  have hED : ∀ e ∈ seedEdgesFinset T.graph S0 v0 p,
      e.1 ∈ orbitVertSet H A.verts ∧ e.2 ∈ orbitVertSet H A.verts := by
    intro e he
    have h1 : A.Adj e.1 e.2 := hAE e he
    exact ⟨(subset_orbitVertSet (H := H) A.verts) (A.edge_vert h1),
      (subset_orbitVertSet (H := H) A.verts) (A.edge_vert h1.symm)⟩
  -- ## Step 1: the generators of `H` move the base vertex along a walk
  have hmemH : ∀ {s : G}, s ∈ S0 → s ∈ H := by
    intro s hs
    rw [← hS0]
    exact Subgroup.subset_closure hs
  have hstep : ∀ {s : G} (hs : s ∈ S0),
      GD.Reachable ⟨v0, hv0X⟩ ⟨s • v0, orbitVertSet.smul_mem ⟨s, hmemH hs⟩ hv0X⟩ := by
    intro s hs
    have hle : (p s).toSubgraph ≤ D :=
      le_trans (walkSubgraph_le_seedSubgraph T S0 v0 p hs) (le_orbitSubgraph T H A)
    exact Reachable.map (Subgraph.inclusion hle) ⟨(p s).mapToSubgraph⟩
  -- ## Step 2: `v₀` is joined to `h • v₀` for every `h : H`
  have hclosureH : Subgroup.closure {h : H | (h : G) ∈ (S0 : Set G)} = ⊤ := by
    have hmap : (Subgroup.closure {h : H | (h : G) ∈ (S0 : Set G)}).map H.subtype = H := by
      rw [MonoidHom.map_closure]
      have himg : H.subtype '' {h : H | (h : G) ∈ (S0 : Set G)} = (↑S0 : Set G) := by
        ext g
        constructor
        · rintro ⟨h, hh, rfl⟩
          exact hh
        · intro hg
          exact ⟨⟨g, by rw [← hS0]; exact Subgroup.subset_closure hg⟩, hg, rfl⟩
      rw [himg, hS0]
    rw [eq_top_iff]
    intro h _
    have hh : (h : G) ∈ (Subgroup.closure {h : H | (h : G) ∈ (S0 : Set G)}).map
        H.subtype := by
      rw [hmap]
      exact h.2
    obtain ⟨k, hk, hk_eq⟩ := hh
    have hkh : k = h := Subtype.ext hk_eq
    exact hkh ▸ hk
  have hreach : ∀ h : H, GD.Reachable ⟨v0, hv0X⟩ ⟨h • v0, orbitVertSet.smul_mem h hv0X⟩ := by
    intro h
    have hmem : h ∈ Subgroup.closure {h : H | (h : G) ∈ (S0 : Set G)} := by
      rw [hclosureH]
      exact Subgroup.mem_top h
    refine Subgroup.closure_induction
      (k := {h : H | (h : G) ∈ (S0 : Set G)})
      (p := fun g _ => GD.Reachable ⟨v0, hv0X⟩ ⟨g • v0, orbitVertSet.smul_mem g hv0X⟩)
      (fun x hx => hstep hx) (reachable_of_eq (Subtype.ext (one_smul H v0))).symm ?_ ?_ hmem
    · intro x y _ _ hxR hyR
      exact (hxR.trans (Reachable.map (orbitActHom T H A x) hyR)).trans
        (reachable_of_eq (Subtype.ext (mul_smul x y v0).symm))
    · intro x _ hxR
      have h1 : (orbitActHom T H A x⁻¹) ⟨x • v0, orbitVertSet.smul_mem x hv0X⟩ =
          (⟨v0, hv0X⟩ : ↥D.verts) := by
        refine Subtype.ext ?_
        show x⁻¹ • (x • v0) = v0
        rw [← mul_smul, inv_mul_cancel, one_smul]
      exact ((Reachable.map (orbitActHom T H A x⁻¹) hxR).trans
        (reachable_of_eq h1)).symm
  -- ## Step 3: every vertex of the seed subgraph is reachable from `v₀`
  have hseed_reach : ∀ (a : V) (ha : a ∈ A.verts),
      GD.Reachable ⟨v0, hv0X⟩ ⟨a, (subset_orbitVertSet (H := H) A.verts) ha⟩ := by
    intro a ha
    have hav : a ∈ (⋃ s : {s // s ∈ S0}, (p s.1).toSubgraph.verts) ∪ {v0} := by
      have h : a ∈ (seedSubgraph T S0 v0 p).verts := ha
      rwa [seedSubgraph_verts_eq] at h
    rw [Set.mem_union] at hav
    rcases hav with hav | hav
    · rw [Set.mem_iUnion] at hav
      obtain ⟨s, hs⟩ := hav
      have hle : (p s.1).toSubgraph ≤ D :=
        le_trans (walkSubgraph_le_seedSubgraph T S0 v0 p s.2) (le_orbitSubgraph T H A)
      have hsupp : a ∈ (p s.1).support := by
        rw [Walk.verts_toSubgraph] at hs
        exact hs
      exact Reachable.map (Subgraph.inclusion hle)
        (walk_toSubgraph_reachable (p s.1) hsupp)
    · rw [Set.mem_singleton_iff] at hav
      exact (reachable_of_eq (Subtype.ext hav)).symm
  -- ## Step 4: `GD` is connected
  have hall : ∀ x : ↥(orbitVertSet H A.verts), GD.Reachable ⟨v0, hv0X⟩ x := by
    intro x
    obtain ⟨g, a, ha, hga⟩ := x.2
    have h2 : GD.Reachable ⟨g • v0, orbitVertSet.smul_mem g hv0X⟩
        ⟨g • a, orbitVertSet.smul_mem g ((subset_orbitVertSet (H := H) A.verts) ha)⟩ :=
      Reachable.map (orbitActHom T H A g) (hseed_reach a ha)
    exact (hreach g).trans (h2.trans (reachable_of_eq (Subtype.ext hga)))
  have hconn : GD.Connected := by
    rw [connected_iff_exists_forall_reachable]
    exact ⟨⟨v0, hv0X⟩, fun x => hall x⟩
  have hac : GD.IsAcyclic := (T.isTree.isAcyclic).comap D.hom D.hom_injective
  -- ## The `H`-tree on the orbit closure
  let S : GTree H (orbitVertSet H A.verts) :=
    { graph := GD
      isTree := ⟨hconn, hac⟩
      smul_adj := fun g _ _ huv => orbitSubgraph.adj_smul g huv }
  -- ## Finite vertex and edge transversals
  have hTV : ∃ s : Finset ↥(orbitVertSet H A.verts),
      ∀ v : ↥(orbitVertSet H A.verts), ∃ g : H, g • v ∈ s := by
    refine ⟨(seedVertsFinset T.graph S0 v0 p).attach.image
      (fun a => (⟨a.1, hVD a.1 a.2⟩ : ↥(orbitVertSet H A.verts))), ?_⟩
    intro v
    obtain ⟨g, a, ha, hga⟩ := v.2
    refine ⟨g⁻¹, ?_⟩
    have hv : g⁻¹ • v = (⟨a, hVD a (hAV ha)⟩ : ↥(orbitVertSet H A.verts)) := by
      apply Subtype.ext
      rw [orbitVertSet.coe_smul, ← hga, inv_smul_smul]
    rw [hv]
    exact Finset.mem_image_of_mem _ (Finset.mem_attach _ ⟨a, hAV ha⟩)
  have hTE : ∃ s : Finset (↥(orbitVertSet H A.verts) × ↥(orbitVertSet H A.verts)),
      ∀ p : ↥(orbitVertSet H A.verts) × ↥(orbitVertSet H A.verts), S.Adj p.1 p.2 →
        ∃ g : H, (g • p.1, g • p.2) ∈ s := by
    refine ⟨(seedEdgesFinset T.graph S0 v0 p).attach.image (fun e =>
      ((⟨e.1.1, (hED e.1 e.2).1⟩ : ↥(orbitVertSet H A.verts)),
       (⟨e.1.2, (hED e.1 e.2).2⟩ : ↥(orbitVertSet H A.verts)))), ?_⟩
    rintro ⟨u, v⟩ hp
    obtain ⟨h, a, b, hab, hua, hvb⟩ := hp
    refine ⟨h⁻¹, ?_⟩
    have hpu : h⁻¹ • u = (⟨a, (hED (a, b) (hEseed a b hab)).1⟩ :
        ↥(orbitVertSet H A.verts)) := by
      apply Subtype.ext
      rw [orbitVertSet.coe_smul, ← hua, inv_smul_smul]
    have hpv : h⁻¹ • v = (⟨b, (hED (a, b) (hEseed a b hab)).2⟩ :
        ↥(orbitVertSet H A.verts)) := by
      apply Subtype.ext
      rw [orbitVertSet.coe_smul, ← hvb, inv_smul_smul]
    rw [hpu, hpv]
    exact Finset.mem_image_of_mem _ (Finset.mem_attach _ ⟨(a, b), hEseed a b hab⟩)
  have hcoc : S.IsCocompact := (isCocompact_iff_transversal S).mpr ⟨hTV, hTE⟩
  -- ## The domination map over the inclusion `H ↪ G`
  have hdom : DominatesOver H.subtype S T :=
    ⟨{ toFun := Subtype.val
       map_smul' := fun h x => rfl
       map_adj' := fun {a b} huv => Or.inl (D.adj_sub huv) }⟩
  -- ## The vertex set of `S` is countable
  have hcount : Countable ↥(orbitVertSet H A.verts) := by
    haveI hS0f : Finite ↥S0 := S0.finite_toSet.to_subtype
    haveI hFGc : Countable (FreeGroup ↥S0) := by
      show Countable (Quot FreeGroup.Red.Step)
      infer_instance
    haveI hAf : Finite ↥A.verts :=
      ((seedVertsFinset T.graph S0 v0 p).finite_toSet.subset hAV).to_subtype
    haveI hAc : Countable ↥A.verts := inferInstance
    have hrange : (FreeGroup.lift (fun s : ↥S0 => (⟨(s : G), hmemH s.2⟩ : H))).range = ⊤ := by
      rw [FreeGroup.range_lift_eq_closure]
      have himg : Set.range (fun s : ↥S0 => (⟨(s : G), hmemH s.2⟩ : H)) =
          {h : H | (h : G) ∈ (S0 : Set G)} := by
        ext h
        constructor
        · rintro ⟨s, rfl⟩
          exact s.2
        · intro hh
          exact ⟨⟨(h : G), hh⟩, Subtype.ext rfl⟩
      rw [himg, hclosureH]
    have hsurjH : ∀ h : H, ∃ z : FreeGroup ↥S0,
        FreeGroup.lift (fun s : ↥S0 => (⟨(s : G), hmemH s.2⟩ : H)) z = h := by
      intro h
      have : h ∈ (FreeGroup.lift (fun s : ↥S0 => (⟨(s : G), hmemH s.2⟩ : H))).range := by
        rw [hrange]
        exact Subgroup.mem_top h
      exact MonoidHom.mem_range.mp this
    refine Function.Surjective.countable (f := fun p : FreeGroup ↥S0 × ↥A.verts =>
      (⟨(FreeGroup.lift (fun s : ↥S0 => (⟨(s : G), hmemH s.2⟩ : H))) p.1 • (p.2 : V),
        orbitVertSet.smul_mem
          ((FreeGroup.lift (fun s : ↥S0 => (⟨(s : G), hmemH s.2⟩ : H))) p.1)
          (subset_orbitVertSet (H := H) A.verts p.2.2)⟩ :
        ↥(orbitVertSet H A.verts))) ?_
    intro x
    obtain ⟨h, a, ha, hxa⟩ := x.2
    obtain ⟨z, hz⟩ := hsurjH h
    refine ⟨(z, ⟨a, ha⟩), ?_⟩
    apply Subtype.ext
    change (FreeGroup.lift (fun s : ↥S0 => (⟨(s : G), hmemH s.2⟩ : H))) z • a = x.1
    rw [hz, hxa]
  -- ## Transport to the prescribed universe
  obtain ⟨β, hβ⟩ := (small_iff ↥(orbitVertSet H A.verts)).mp
    (Countable.toSmall ↥(orbitVertSet H A.verts) : Small.{w} ↥(orbitVertSet H A.verts))
  let e : ↥(orbitVertSet H A.verts) ≃ β := Classical.choice hβ
  let sβ : H → β → β := fun h x => e (h • e.symm x)
  letI instβ : MulAction H β :=
    { smul := sβ
      one_smul := fun x => by
        have h : sβ 1 x = x := by
          show e (1 • e.symm x) = x
          rw [one_smul, Equiv.apply_symm_apply]
        exact h
      mul_smul := fun h k x => by
        have h2 : sβ (h * k) x = sβ h (sβ k x) := by
          show e ((h * k) • e.symm x) = e (h • e.symm (e (k • e.symm x)))
          rw [Equiv.symm_apply_apply, mul_smul]
        exact h2 }
  let Gβ : SimpleGraph β := GD.comap (e.symm : β ≃ ↥(orbitVertSet H A.verts))
  let φ : Gβ ≃g GD := SimpleGraph.Iso.comap (e.symm : β ≃ ↥(orbitVertSet H A.verts)) GD
  have hφapply : ∀ x : β, φ x = e.symm x := fun x => rfl
  have hcomap : ∀ x y : β, Gβ.Adj x y ↔ GD.Adj (e.symm x) (e.symm y) :=
    fun x y => SimpleGraph.comap_adj
  have hconnβ : Gβ.Connected := by
    rw [connected_iff_exists_forall_reachable]
    refine ⟨e ⟨v0, hv0X⟩, fun y => ?_⟩
    refine (Iso.reachable_iff (φ := φ)).mp ?_
    rw [hφapply, hφapply, Equiv.symm_apply_apply]
    exact hall (e.symm y)
  have hacβ : Gβ.IsAcyclic :=
    IsAcyclic.comap (φ : Gβ →g GD) (fun x y h => φ.injective h) hac
  have hsmulβ : ∀ (h : H) ⦃x y : β⦄, Gβ.Adj x y → Gβ.Adj (h • x) (h • y) := by
    intro h x y hxy
    rw [hcomap] at hxy ⊢
    have h1 : e.symm (h • x) = h • e.symm x := by
      have hh : h • x = sβ h x := rfl
      rw [hh]
      show e.symm (e (h • e.symm x)) = h • e.symm x
      rw [Equiv.symm_apply_apply]
    have h2 : e.symm (h • y) = h • e.symm y := by
      have hh : h • y = sβ h y := rfl
      rw [hh]
      show e.symm (e (h • e.symm y)) = h • e.symm y
      rw [Equiv.symm_apply_apply]
    rw [h1, h2]
    exact S.smul_adj h hxy
  let Sβ : GTree H β :=
    { graph := Gβ
      isTree := ⟨hconnβ, hacβ⟩
      smul_adj := hsmulβ }
  have hTVβ : ∃ s : Finset β, ∀ x : β, ∃ g : H, g • x ∈ s := by
    obtain ⟨s, hs⟩ := hTV
    refine ⟨s.image e, fun x => ?_⟩
    obtain ⟨g, hg⟩ := hs (e.symm x)
    refine ⟨g, ?_⟩
    have h1 : g • x = sβ g x := rfl
    rw [h1]
    show e (g • e.symm x) ∈ s.image e
    exact Finset.mem_image_of_mem e hg
  have hTEβ : ∃ s : Finset (β × β), ∀ p : β × β, Sβ.Adj p.1 p.2 →
      ∃ g : H, (g • p.1, g • p.2) ∈ s := by
    obtain ⟨s, hs⟩ := hTE
    refine ⟨s.image (fun q => (e q.1, e q.2)), fun q hq => ?_⟩
    have hq' : S.Adj (e.symm q.1) (e.symm q.2) := by
      have hq'' : Gβ.Adj q.1 q.2 := hq
      rw [hcomap] at hq''
      exact hq
    obtain ⟨g, hg⟩ := hs (e.symm q.1, e.symm q.2) hq'
    refine ⟨g, ?_⟩
    have h1 : g • q.1 = e (g • e.symm q.1) := rfl
    have h2 : g • q.2 = e (g • e.symm q.2) := rfl
    rw [h1, h2]
    exact Finset.mem_image_of_mem _ hg
  have hcocβ : Sβ.IsCocompact := (isCocompact_iff_transversal Sβ).mpr ⟨hTVβ, hTEβ⟩
  have hdomβ : DominatesOver H.subtype Sβ T :=
    ⟨{ toFun := fun x => (e.symm x : V)
       map_smul' := fun h x => by
         have h1 : h • x = sβ h x := rfl
         rw [h1]
         show (e.symm (e (h • e.symm x)) : V) = (h : G) • (e.symm x : V)
         rw [Equiv.symm_apply_apply]
         rfl
       map_adj' := fun {a b} huv => by
         have huv' : Gβ.Adj a b := huv
         rw [hcomap] at huv'
         exact Or.inl (D.adj_sub huv') }⟩
  exact ⟨β, instβ, Sβ, hcocβ, hdomβ⟩

/-! ## The statement for an arbitrary universe of the vertex type -/

theorem exists_cocompact_invariant_subtree {G : Type*} [Group G] {V : Type*} [MulAction G V]
    (T : GTree G V) (H : Subgroup G) (hH : H.FG) :
    ∃ (W : Type*) (_ : MulAction H W) (S : GTree H W),
      S.IsCocompact ∧ DominatesOver H.subtype S T :=
  exists_cocompact_invariant_subtree_aux T H hH

end Work.ORDunwoody.Lemmas
