/-
Copyright: work of the ORDunwoody subproject.

# The barycentric subdivision of a graph: definitions and the projection

For a `SimpleGraph G` on `V`, the *barycentric subdivision* is the graph on
`V ⊕ {e : Sym2 V // e ∈ G.edgeSet}` in which each original vertex `v` is joined exactly to the
edges `e ∋ v` and in which no two vertices of the same kind are joined.

The main content of this file is a projection of walks of the subdivision to walks of `G`: a
walk of the subdivision from `Sum.inl v` to `Sum.inl w` is a "subdivision" of a walk from `v`
to `w` in `G` (each step of `G` being replaced by a two-step detour through the midpoint).
We record this as an existence statement carrying the two properties needed for the
tree-theoretic application: the projected walk is a trail whenever the given walk is, and the
edge count is halved (`p.length = 2 * q.length`).
-/
import Mathlib

set_option autoImplicit false

namespace Work.ORDunwoody.Lemmas

open SimpleGraph

variable {V : Type*}

/-- **The barycentric subdivision** of a graph `G`: the vertices are the original vertices
together with the edges of `G`, each original vertex being joined exactly to the edges
containing it, and no two vertices of the same kind being joined. -/
def barycentricGraph (G : SimpleGraph V) : SimpleGraph (V ⊕ {e : Sym2 V // e ∈ G.edgeSet}) where
  Adj x y := match x, y with
    | .inl v, .inr e => v ∈ (e : Sym2 V)
    | .inr e, .inl v => v ∈ (e : Sym2 V)
    | _, _ => False
  symm := ⟨by intro x y h; cases x <;> cases y <;> simp_all⟩
  loopless := ⟨by intro x h; cases x <;> simp_all⟩

variable {G : SimpleGraph V}

@[simp] lemma barycentricGraph_adj_inl_inl (v w : V) :
    (barycentricGraph G).Adj (Sum.inl v) (Sum.inl w) ↔ False := by simp [barycentricGraph]

@[simp] lemma barycentricGraph_adj_inr_inr (e e' : {e : Sym2 V // e ∈ G.edgeSet}) :
    (barycentricGraph G).Adj (Sum.inr e) (Sum.inr e') ↔ False := by simp [barycentricGraph]

@[simp] lemma barycentricGraph_adj_inl_inr (v : V) (e : {e : Sym2 V // e ∈ G.edgeSet}) :
    (barycentricGraph G).Adj (Sum.inl v) (Sum.inr e) ↔ v ∈ (e : Sym2 V) := by
  simp [barycentricGraph]

@[simp] lemma barycentricGraph_adj_inr_inl (v : V) (e : {e : Sym2 V // e ∈ G.edgeSet}) :
    (barycentricGraph G).Adj (Sum.inr e) (Sum.inl v) ↔ v ∈ (e : Sym2 V) := by
  simp [barycentricGraph]

/-- The `G`-edge underlying an edge of the barycentric subdivision (if there is one). -/
def edgeUnder (G : SimpleGraph V) (z : Sym2 (V ⊕ {e : Sym2 V // e ∈ G.edgeSet})) :
    Option (Sym2 V) :=
  Sym2.lift ⟨(fun a b => match a, b with
    | Sum.inl _, Sum.inr e => some (e : Sym2 V)
    | Sum.inr e, Sum.inl _ => some (e : Sym2 V)
    | _, _ => none), by intro a b; cases a <;> cases b <;> simp⟩ z

@[simp] lemma edgeUnder_inl_inr (v : V) (e : {e : Sym2 V // e ∈ G.edgeSet}) :
    edgeUnder G (s(Sum.inl v, Sum.inr e)) = some (e : Sym2 V) := rfl

@[simp] lemma edgeUnder_inr_inl (v : V) (e : {e : Sym2 V // e ∈ G.edgeSet}) :
    edgeUnder G (s(Sum.inr e, Sum.inl v)) = some (e : Sym2 V) := rfl

/-- A walk `q` in `G` *projects back* to a walk `p` of the barycentric subdivision if every
edge of `q` is the underlying `G`-edge of an edge of `p`. -/
def ProjectsTo {x y : V ⊕ {e : Sym2 V // e ∈ G.edgeSet}}
    (p : (barycentricGraph G).Walk x y) {v w : V} (q : G.Walk v w) : Prop :=
  ∀ e' : Sym2 V, e' ∈ q.edges → ∃ f ∈ p.edges, edgeUnder G f = some e'

/-- Two vertices of a `2`-element `Sym2`-set determine it. -/
lemma sym2_eq_of_mem_mem {e : Sym2 V} {a b : V} (ha : a ∈ e) (hb : b ∈ e) (hne : a ≠ b) :
    e = s(a, b) := (Sym2.mem_and_mem_iff hne).mp ⟨ha, hb⟩

/-- Vertices of a genuine edge of `G` are adjacent. -/
lemma adj_of_mem_mem {e : {e : Sym2 V // e ∈ G.edgeSet}} {a b : V} (ha : a ∈ (e : Sym2 V))
    (hb : b ∈ (e : Sym2 V)) (hne : a ≠ b) : G.Adj a b := by
  have h : (e : Sym2 V) = s(a, b) := sym2_eq_of_mem_mem ha hb hne
  exact (SimpleGraph.mem_edgeSet G).mp (h ▸ e.property)

/-- An edge of a walk of the barycentric subdivision whose underlying `G`-edge is `g` gives,
together with `g`, a "half-edge" of the walk: the incident subdivision vertex is an endpoint
of `g`. -/
lemma exists_inl_mem_of_edgeUnder {x y : V ⊕ {e : Sym2 V // e ∈ G.edgeSet}}
    (q : (barycentricGraph G).Walk x y) {f : Sym2 (V ⊕ {e : Sym2 V // e ∈ G.edgeSet})}
    (hf : f ∈ q.edges) {g : Sym2 V} (hg : edgeUnder G f = some g) :
    ∃ (a : V) (he : g ∈ G.edgeSet), a ∈ g ∧ s(Sum.inl a, Sum.inr ⟨g, he⟩) ∈ q.edges := by
  induction f using Sym2.ind with
  | _ x1 x2 =>
    cases x1 with
    | inl a =>
      cases x2 with
      | inl b => simp [edgeUnder] at hg
      | inr e =>
        simp only [edgeUnder, Sym2.lift_mk, Option.some.injEq] at hg
        have hadj : a ∈ (e : Sym2 V) := by
          have := q.edges_subset_edgeSet hf
          simpa using this
        refine ⟨a, hg.symm ▸ e.property, hg.symm ▸ hadj, ?_⟩
        rw [show (⟨g, hg.symm ▸ e.property⟩ : {e : Sym2 V // e ∈ G.edgeSet}) = e from
          Subtype.ext hg.symm]
        exact hf
    | inr e =>
      cases x2 with
      | inl a =>
        simp only [edgeUnder, Sym2.lift_mk, Option.some.injEq] at hg
        have hadj : a ∈ (e : Sym2 V) := by
          have := q.edges_subset_edgeSet hf
          simpa using this
        refine ⟨a, hg.symm ▸ e.property, hg.symm ▸ hadj, ?_⟩
        rw [Sym2.eq_swap,
          show (⟨g, hg.symm ▸ e.property⟩ : {e : Sym2 V // e ∈ G.edgeSet}) = e from
          Subtype.ext hg.symm]
        exact hf
      | inr e' => simp [edgeUnder] at hg


/-! ### The projection of walks of the subdivision to walks of `G` -/

/-- Case analysis for an adjacency of the subdivision starting at an original vertex. -/
lemma adj_inl_cases {x : V ⊕ {e : Sym2 V // e ∈ G.edgeSet}} {v : V}
    (h : (barycentricGraph G).Adj (Sum.inl v) x) :
    ∃ e : {e : Sym2 V // e ∈ G.edgeSet}, x = Sum.inr e ∧ v ∈ (e : Sym2 V) := by
  cases x with
  | inl v' => exact ((barycentricGraph_adj_inl_inl v v').mp h).elim
  | inr e => exact ⟨e, rfl, (barycentricGraph_adj_inl_inr v e).mp h⟩

/-- Case analysis for an adjacency of the subdivision starting at an edge-midpoint. -/
lemma adj_inr_cases {x : V ⊕ {e : Sym2 V // e ∈ G.edgeSet}}
    {e : {e : Sym2 V // e ∈ G.edgeSet}} (h : (barycentricGraph G).Adj (Sum.inr e) x) :
    ∃ v : V, x = Sum.inl v ∧ v ∈ (e : Sym2 V) := by
  cases x with
  | inl v => exact ⟨v, rfl, (barycentricGraph_adj_inr_inl v e).mp h⟩
  | inr e' => exact ((barycentricGraph_adj_inr_inr e e').mp h).elim

/-- **The projection lemma.**  A trail of the barycentric subdivision which runs from `Sum.inl v`
to `Sum.inl w` is a "subdivision" of a trail of `G` from `v` to `w`: there is a trail `q` with
`p.length = 2 * q.length` whose edges are the underlying `G`-edges of edges of `p`.

The second statement is the "state B" version needed for the induction: a trail running from
`Sum.inr e` to `Sum.inl w`, together with a vertex `v ∈ e` and the information that the edge
`s(inl v, inr e)` is not already used, projects to a trail from `v` to `w` with
`p.length + 1 = 2 * q.length`. -/
theorem proj_aux {x y : V ⊕ {e : Sym2 V // e ∈ G.edgeSet}}
    (p : (barycentricGraph G).Walk x y) (hp : p.IsTrail) :
    (∀ {v w : V}, x = Sum.inl v → y = Sum.inl w →
      ∃ q : G.Walk v w, q.IsTrail ∧ p.length = 2 * q.length ∧ ProjectsTo p q) ∧
    (∀ {v : V} {e : {e : Sym2 V // e ∈ G.edgeSet}} {w : V},
      x = Sum.inr e → y = Sum.inl w → v ∈ (e : Sym2 V) →
      s(Sum.inl v, Sum.inr e) ∉ p.edges →
      ∃ q : G.Walk v w, q.IsTrail ∧ p.length + 1 = 2 * q.length ∧ ProjectsTo p q) := by
  induction p with
  | nil =>
    constructor
    · intro v w hx hy
      have hvw : v = w := by simpa using hx.symm.trans hy
      subst hvw
      exact ⟨Walk.nil, Walk.IsTrail.nil, by simp, by
        intro e' he'
        exact absurd he' (by simp)⟩
    · intro v e w hx hy hv hnot
      exact absurd (hx.symm.trans hy) (by simp)
  | cons h q ih =>
    constructor
    · intro v w hx hy
      subst hx
      subst hy
      obtain ⟨e, hmid, hv⟩ := adj_inl_cases h
      subst hmid
      obtain ⟨hqt, hnot⟩ := (Walk.isTrail_cons h q).mp hp
      obtain ⟨q', hq't, hlen, hproj⟩ :=
        (ih hqt).2 (v := v) (e := e) (w := w) rfl rfl hv hnot
      refine ⟨q', hq't, ?_, ?_⟩
      · rw [Walk.length_cons]; omega
      · intro e' he'
        obtain ⟨f, hf, hfu⟩ := hproj e' he'
        exact ⟨f, by simp only [Walk.edges_cons, List.mem_cons]; exact Or.inr hf, hfu⟩
    · intro v e w hx hy hv hnot
      subst hx
      subst hy
      obtain ⟨v₁, hmid, hv₁⟩ := adj_inr_cases h
      subst hmid
      obtain ⟨hqt, hnot'⟩ := (Walk.isTrail_cons h q).mp hp
      have hne : v ≠ v₁ := by
        intro hvv
        apply hnot
        have heq : s(Sum.inl v, Sum.inr e) = s(Sum.inr e, Sum.inl v₁) := by
          rw [hvv, Sym2.eq_swap]
        rw [heq, Walk.edges_cons]
        simp
      obtain ⟨q'', hq''t, hlen, hproj⟩ := (ih hqt).1 (v := v₁) (w := w) rfl rfl
      have hadj : G.Adj v v₁ := adj_of_mem_mem hv hv₁ hne
      have hkey : s(v, v₁) ∉ q''.edges := by
        intro hmem
        have heq : (e : Sym2 V) = s(v, v₁) := sym2_eq_of_mem_mem hv hv₁ hne
        have hmem' : (e : Sym2 V) ∈ q''.edges := by rw [heq]; exact hmem
        obtain ⟨f, hf, hfu⟩ := hproj (e : Sym2 V) hmem'
        obtain ⟨a, he', ha, hfa⟩ := exists_inl_mem_of_edgeUnder q hf hfu
        rw [heq, Sym2.mem_iff] at ha
        rcases ha with rfl | rfl
        · exact hnot (by
            rw [Walk.edges_cons]
            refine List.mem_cons_of_mem _ ?_
            simpa using hfa)
        · exact hnot' (by
            rw [Sym2.eq_swap]
            simpa using hfa)
      refine ⟨Walk.cons hadj q'', ?_, ?_, ?_⟩
      · exact (Walk.isTrail_cons hadj q'').mpr ⟨hq''t, hkey⟩
      · rw [Walk.length_cons, Walk.length_cons]; omega
      · intro e' he'
        simp only [Walk.edges_cons, List.mem_cons] at he'
        rcases he' with heq' | he''
        · subst heq'
          refine ⟨s(Sum.inr e, Sum.inl v₁), ?_, ?_⟩
          · simp

          · rw [edgeUnder_inr_inl, sym2_eq_of_mem_mem hv hv₁ hne]
        · obtain ⟨f, hf, hfu⟩ := hproj e' he''
          exact ⟨f, by simp only [Walk.edges_cons, List.mem_cons]; exact Or.inr hf, hfu⟩

/-- The "state A" form of the projection lemma. -/
theorem exists_proj_inl {v w : V} (p : (barycentricGraph G).Walk (Sum.inl v) (Sum.inl w))
    (hp : p.IsTrail) :
    ∃ q : G.Walk v w, q.IsTrail ∧ p.length = 2 * q.length ∧ ProjectsTo p q :=
  (proj_aux p hp).1 (v := v) (w := w) rfl rfl

/-- The "state B" form of the projection lemma. -/
theorem exists_proj_inr {v : V} {e : {e : Sym2 V // e ∈ G.edgeSet}} {w : V}
    (p : (barycentricGraph G).Walk (Sum.inr e) (Sum.inl w)) (hp : p.IsTrail)
    (hv : v ∈ (e : Sym2 V)) (hnot : s(Sum.inl v, Sum.inr e) ∉ p.edges) :
    ∃ q : G.Walk v w, q.IsTrail ∧ p.length + 1 = 2 * q.length ∧ ProjectsTo p q :=
  (proj_aux p hp).2 (v := v) (e := e) (w := w) rfl rfl hv hnot

/-! ### Connectivity, acyclicity and the tree structure -/

/-- An endpoint of a genuine edge of `G`. -/
lemma exists_mem_of_mem_edgeSet {e : Sym2 V} (he : e ∈ G.edgeSet) : ∃ a : V, a ∈ e := by
  induction e using Sym2.ind with
  | _ a b => exact ⟨a, Sym2.mem_mk_left a b⟩

/-- Reachability in `G` lifts to reachability between the corresponding original vertices of the
barycentric subdivision. -/
lemma reachable_inl_of_reachable {v w : V} (h : G.Reachable v w) :
    (barycentricGraph G).Reachable (Sum.inl v) (Sum.inl w) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h ⊢
  have hstep : ∀ a b : V, G.Adj a b → Relation.ReflTransGen (barycentricGraph G).Adj
      (Sum.inl a : V ⊕ {e : Sym2 V // e ∈ G.edgeSet}) (Sum.inl b) := by
    intro a b hab
    have h1 : (barycentricGraph G).Adj (Sum.inl a)
        (Sum.inr (⟨s(a, b), (SimpleGraph.mem_edgeSet G).mpr hab⟩ :
          {e : Sym2 V // e ∈ G.edgeSet})) :=
      (barycentricGraph_adj_inl_inr a _).mpr (Sym2.mem_mk_left a b)
    have h2 : (barycentricGraph G).Adj
        (Sum.inr (⟨s(a, b), (SimpleGraph.mem_edgeSet G).mpr hab⟩ :
          {e : Sym2 V // e ∈ G.edgeSet})) (Sum.inl b) :=
      (barycentricGraph_adj_inr_inl b _).mpr (Sym2.mem_mk_right a b)
    exact (Relation.ReflTransGen.tail Relation.ReflTransGen.refl h1).tail h2
  exact (Relation.ReflTransGen.lift'
    (fun v : V => (Sum.inl v : V ⊕ {e : Sym2 V // e ∈ G.edgeSet})) hstep) v w h

/-- The barycentric subdivision of a connected graph is connected. -/
theorem barycentricGraph_connected (hG : G.Connected) : (barycentricGraph G).Connected := by
  rw [SimpleGraph.connected_iff]
  refine ⟨?_, ?_⟩
  · intro x y
    cases x with
    | inl v =>
      cases y with
      | inl w => exact reachable_inl_of_reachable (hG v w)
      | inr e =>
        obtain ⟨a, ha⟩ := exists_mem_of_mem_edgeSet e.property
        obtain ⟨p⟩ := reachable_inl_of_reachable (hG v a)
        exact ⟨p.concat ((barycentricGraph_adj_inl_inr a e).mpr ha)⟩
    | inr e =>
      cases y with
      | inl w =>
        obtain ⟨a, ha⟩ := exists_mem_of_mem_edgeSet e.property
        obtain ⟨p⟩ := reachable_inl_of_reachable (hG a w)
        exact ⟨Walk.cons ((barycentricGraph_adj_inr_inl a e).mpr ha) p⟩
      | inr e' =>
        obtain ⟨a, ha⟩ := exists_mem_of_mem_edgeSet e.property
        obtain ⟨b, hb⟩ := exists_mem_of_mem_edgeSet e'.property
        obtain ⟨p⟩ := reachable_inl_of_reachable (hG a b)
        have h1 : (barycentricGraph G).Adj (Sum.inr e) (Sum.inl a) :=
          (barycentricGraph_adj_inr_inl a e).mpr ha
        have h2 : (barycentricGraph G).Adj (Sum.inl b) (Sum.inr e') :=
          (barycentricGraph_adj_inl_inr b e').mpr hb
        exact ⟨Walk.cons h1 (p.concat h2)⟩
  · obtain ⟨v⟩ := hG.nonempty
    exact ⟨Sum.inl v⟩

/-- A cycle of the barycentric subdivision gives a cycle based at an original vertex. -/
lemma exists_cycle_inl {z : V ⊕ {e : Sym2 V // e ∈ G.edgeSet}}
    (c : (barycentricGraph G).Walk z z) (hc : c.IsCycle) :
    ∃ (v : V) (c' : (barycentricGraph G).Walk (Sum.inl v) (Sum.inl v)), c'.IsCycle := by
  classical
  cases z with
  | inl v => exact ⟨v, c, hc⟩
  | inr e =>
    cases c with
    | nil => exact absurd hc Walk.not_isCycle_nil
    | cons h q =>
      obtain ⟨v, hmid, hv⟩ := adj_inr_cases h
      subst hmid
      have hmem : Sum.inl v ∈ (Walk.cons h q : (barycentricGraph G).Walk (Sum.inr e)
          (Sum.inr e)).support := by
        rw [Walk.support_cons]
        exact List.mem_cons_of_mem _ (Walk.start_mem_support q)
      exact ⟨v, (Walk.cons h q).rotate (Sum.inl v) hmem, hc.rotate hmem⟩

/-- The barycentric subdivision of an acyclic graph is acyclic. -/
theorem barycentricGraph_isAcyclic (hG : G.IsAcyclic) : (barycentricGraph G).IsAcyclic := by
  classical
  intro z c hc
  obtain ⟨v, c', hc'⟩ := exists_cycle_inl c hc
  obtain ⟨q, hqt, hlen, -⟩ := exists_proj_inl c' hc'.isTrail
  have h3 : 3 ≤ c'.length := hc'.isCircuit.three_le_length
  have hpos : 0 < q.length := by omega
  have hqne : q ≠ Walk.nil := by
    intro hnil
    exact Walk.not_nil_iff_lt_length.mpr hpos (Walk.eq_nil_iff_nil.mp hnil)
  exact hG (c := q.cycleBypass) (hqt.isCycle_cycleBypass hqne)

/-- **The barycentric subdivision of a tree is a tree.** -/
theorem barycentricGraph_isTree (hG : G.IsTree) : (barycentricGraph G).IsTree :=
  ⟨barycentricGraph_connected hG.connected, barycentricGraph_isAcyclic hG.isAcyclic⟩

end Work.ORDunwoody.Lemmas
