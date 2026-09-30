import Mathlib
import Submission.Work.BMF.adi_graph_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Definitions for `Work.BMF.sum_adj_le_edges`

The combinatorial objects entering the bound
`Σ_{i,j} [GAdjQ i j] g i g j ≤ 2 Σ_{e : q ∈ edgeS e} g e.x₁ g e.x₂`:

* `adjPairs D q` : the ordered pairs of `q`-adjacent vertices;
* `goodEdges D q` : the edges of `D` whose attached prime set contains `q`;
* `adjPairsOfEdge D q e` : the ordered `q`-adjacent pairs whose two endpoints are the two
  endpoints of `e` (in either order).  For `e ∈ D.edges` this set has at most two elements.
-/

namespace Work.BMF

variable {k : ℕ} {f : ℕ → ℂ} {c C X L P₁ P₂ : ℝ}

/-- The ordered pairs of `q`-adjacent vertices. -/
noncomputable def adjPairs (D : QuadData k f c C X L P₁ P₂) (q : ℕ) :
    Finset (GVert D × GVert D) :=
  Finset.univ.filter (fun p => GAdjQ D q p.1 p.2)

/-- The edges of `D` whose attached prime set contains `q`. -/
noncomputable def goodEdges (D : QuadData k f c C X L P₁ P₂) (q : ℕ) : Finset Edge :=
  D.edges.filter (fun e => q ∈ edgeS D e)

/-- The ordered `q`-adjacent pairs whose endpoints are the two endpoints of `e`. -/
noncomputable def adjPairsOfEdge (D : QuadData k f c C X L P₁ P₂) (q : ℕ) (e : Edge) :
    Finset (GVert D × GVert D) :=
  Finset.univ.filter (fun p => GAdjQ D q p.1 p.2 ∧
    ((e.x₁ = p.1.1 ∧ e.x₂ = p.2.1) ∨ (e.x₁ = p.2.1 ∧ e.x₂ = p.1.1)))

@[simp] lemma mem_adjPairs {D : QuadData k f c C X L P₁ P₂} {q : ℕ}
    {p : GVert D × GVert D} : p ∈ adjPairs D q ↔ GAdjQ D q p.1 p.2 := by
  simp [adjPairs]

@[simp] lemma mem_goodEdges {D : QuadData k f c C X L P₁ P₂} {q : ℕ} {e : Edge} :
    e ∈ goodEdges D q ↔ e ∈ D.edges ∧ q ∈ edgeS D e := by
  simp [goodEdges]

@[simp] lemma mem_adjPairsOfEdge {D : QuadData k f c C X L P₁ P₂} {q : ℕ} {e : Edge}
    {p : GVert D × GVert D} :
    p ∈ adjPairsOfEdge D q e ↔ GAdjQ D q p.1 p.2 ∧
      ((e.x₁ = p.1.1 ∧ e.x₂ = p.2.1) ∨ (e.x₁ = p.2.1 ∧ e.x₂ = p.1.1)) := by
  simp [adjPairsOfEdge]

end Work.BMF
