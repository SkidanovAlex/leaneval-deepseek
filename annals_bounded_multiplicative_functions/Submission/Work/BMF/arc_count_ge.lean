import Mathlib
import Submission.Work.BMF.adi_all_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Finset

/-- The number of edges of `D` whose prime set contains `q` is bounded by the number of ordered
`q`-adjacent pairs of vertices.  Indeed the ordered pair of endpoints of an edge determines the
edge (`edge_ext`), and each edge of the filtered set witnesses the `q`-adjacency of its ordered
endpoint pair. -/
theorem arc_count_ge {k : ℕ} {f : ℕ → ℂ} {c C X L P₁ P₂ : ℝ}
    (D : Work.BMF.QuadData k f c C X L P₁ P₂) (q : ℕ) (hP : 0 < P₁) (hL : 0 < L)
    (hbig : 8000 * P₁ ^ 2 < X / L) :
    ((D.edges.filter (fun e => q ∈ Work.BMF.edgeS D e)).card : ℝ) ≤
      ∑ i : Work.BMF.GVert D, ∑ j : Work.BMF.GVert D,
        (if Work.BMF.GAdjQ D q i j then (1 : ℝ) else 0) := by
  classical
  set Sq : Finset Edge := D.edges.filter (fun e => q ∈ edgeS D e) with hSqdef
  have hSqmem : ∀ e : Edge, e ∈ Sq ↔ e ∈ D.edges ∧ q ∈ edgeS D e := by
    intro e
    rw [hSqdef]
    simp
  -- the ordered pair of endpoints of an edge of `Sq`, as a pair of vertices
  let φ : {e : Edge // e ∈ Sq} → GVert D × GVert D := fun e =>
    (⟨e.1.x₁, (D.geom e.1 ((hSqmem e.1).mp e.2).1).1⟩,
     ⟨e.1.x₂, (D.geom e.1 ((hSqmem e.1).mp e.2).1).2.1⟩)
  -- the set of ordered `q`-adjacent pairs of vertices
  set T : Finset (GVert D × GVert D) := Finset.univ.filter (fun p => GAdjQ D q p.1 p.2)
    with hTdef
  have hTmem : ∀ p : GVert D × GVert D, p ∈ T ↔ GAdjQ D q p.1 p.2 := by
    intro p
    rw [hTdef]
    simp
  -- `φ` maps into `T`, by definition of the adjacency
  have hmap : Set.MapsTo φ (↑(Sq.attach) : Set {e : Edge // e ∈ Sq}) (↑T : Set _) := by
    intro e _
    have he : e.1 ∈ D.edges := ((hSqmem e.1).mp e.2).1
    have hq : q ∈ edgeS D e.1 := ((hSqmem e.1).mp e.2).2
    exact (hTmem (φ e)).mpr ⟨e.1, he, hq, Or.inl ⟨rfl, rfl⟩⟩
  -- `φ` is injective: the ordered pair of endpoints determines the edge
  have hinj : Set.InjOn φ (↑(Sq.attach) : Set {e : Edge // e ∈ Sq}) := by
    intro e₁ _ e₂ _ heq
    have h1 : e₁.1.x₁ = e₂.1.x₁ := by
      have h := congrArg (fun p : GVert D × GVert D => p.1.1) heq
      simpa only [φ] using h
    have h2 : e₁.1.x₂ = e₂.1.x₂ := by
      have h := congrArg (fun p : GVert D × GVert D => p.2.1) heq
      simpa only [φ] using h
    exact Subtype.ext (edge_ext D hP hL hbig ((hSqmem e₁.1).mp e₁.2).1
      ((hSqmem e₂.1).mp e₂.2).1 h1 h2)
  have hcard : Sq.card ≤ T.card := by
    have h := Finset.card_le_card_of_injOn φ hmap hinj
    rwa [Finset.card_attach] at h
  -- the cardinality of `T` is the displayed double sum
  have hT : (T.card : ℝ) = ∑ i : GVert D, ∑ j : GVert D,
      (if GAdjQ D q i j then (1 : ℝ) else 0) := by
    have h1 : ((T.card : ℕ) : ℝ) =
        ∑ p ∈ (Finset.univ : Finset (GVert D × GVert D)),
          ((if GAdjQ D q p.1 p.2 then (1 : ℕ) else 0) : ℝ) := by
      rw [hTdef, Finset.card_filter]
      push_cast
      rfl
    rw [h1]
    rw [← Finset.univ_product_univ (α := GVert D) (β := GVert D), Finset.sum_product]
    simp
  calc (Sq.card : ℝ) ≤ (T.card : ℝ) := by exact_mod_cast hcard
    _ = ∑ i : GVert D, ∑ j : GVert D,
        (if GAdjQ D q i j then (1 : ℝ) else 0) := hT

end Work.BMF
