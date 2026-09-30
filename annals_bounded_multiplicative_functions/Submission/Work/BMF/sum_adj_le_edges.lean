import Mathlib
import Submission.Work.BMF.adi_graph_defs
import Submission.Work.BMF.sum_adj_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.BMF.sum_adj_le_edges`

The number of `q`-adjacent ordered pairs of vertices, weighted by `g i · g j`, is at most twice
the weight of the set of arcs of `D.edges` carrying `q`:

  `Σ_{i,j} [GAdjQ i j] g i g j ≤ 2 Σ_{e : q ∈ edgeS D e} g e.x₁ g e.x₂`.

The proof is a double count.  Every ordered `q`-adjacent pair `(x,y)` is witnessed by an arc of
`goodEdges D q` (this is the definition of `GAdjQ`), so `adjPairs D q` is covered by the family
`adjPairsOfEdge D q e` (`e ∈ goodEdges D q`); each of these fibres holds at most the two ordered
pairs `(e.x₁, e.x₂)` and `(e.x₂, e.x₁)` and carries the constant weight `g e.x₁ · g e.x₂`.
Hence the total weight of `adjPairs D q` is at most `2 Σ_e g e.x₁ g e.x₂`.
-/

namespace Work.BMF

variable {k : ℕ} {f : ℕ → ℂ} {c C X L P₁ P₂ : ℝ}

/-! ## A general Finset lemma -/

/-- The total weight of a union of fibres is at most the sum of the weights of the fibres,
provided all weights are nonnegative. -/
theorem sum_biUnion_le_sum_of_nonneg {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (s : Finset ι) (B : ι → Finset α) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) :
    ∑ p ∈ s.biUnion B, f p ≤ ∑ e ∈ s, ∑ p ∈ B e, f p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert ha]
      have h1 : ∑ p ∈ B a ∪ s.biUnion B, f p ≤ ∑ p ∈ B a, f p + ∑ p ∈ s.biUnion B, f p := by
        rw [← Finset.sum_sdiff (Finset.subset_union_left)]
        have hd : ∑ p ∈ (B a ∪ s.biUnion B) \ B a, f p ≤ ∑ p ∈ s.biUnion B, f p := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ => hf p)
          intro p hp
          rw [Finset.mem_sdiff] at hp
          rcases Finset.mem_union.mp hp.1 with h | h
          · exact absurd h hp.2
          · exact h
        linarith [hd]
      linarith [h1, ih]

/-! ## The covering of the adjacent pairs -/

/-- Every `q`-adjacent ordered pair is contained in the fibre of one of its witnessing arcs. -/
theorem adjPairs_subset_biUnion (D : QuadData k f c C X L P₁ P₂) (q : ℕ) :
    adjPairs D q ⊆ (goodEdges D q).biUnion (adjPairsOfEdge D q) := by
  intro p hp
  simp only [mem_adjPairs, Finset.mem_biUnion, mem_goodEdges, mem_adjPairsOfEdge] at hp ⊢
  rw [GAdjQ] at hp
  obtain ⟨e, he, hq, h⟩ := hp
  exact ⟨e, ⟨he, hq⟩, ⟨e, he, hq, h⟩, h⟩

/-- A fibre carries at most two ordered pairs: the two orientations of the edge `e`. -/
theorem adjPairsOfEdge_card_le_two (D : QuadData k f c C X L P₁ P₂) (q : ℕ) {e : Edge}
    (he : e ∈ D.edges) :
    ((adjPairsOfEdge D q e).card : ℝ) ≤ 2 := by
  classical
  have hgeom := D.geom e he
  have hx₁ : e.x₁ ∈ D.fam := hgeom.1
  have hx₂ : e.x₂ ∈ D.fam := hgeom.2.1
  have hsub : adjPairsOfEdge D q e ⊆
      ({((⟨e.x₁, hx₁⟩ : GVert D), ⟨e.x₂, hx₂⟩), (⟨e.x₂, hx₂⟩, ⟨e.x₁, hx₁⟩)}
        : Finset (GVert D × GVert D)) := by
    intro p hp
    simp only [mem_adjPairsOfEdge, Finset.mem_insert, Finset.mem_singleton] at hp ⊢
    rcases hp.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl (Prod.ext (Subtype.ext h1.symm) (Subtype.ext h2.symm))
    · exact Or.inr (Prod.ext (Subtype.ext h2.symm) (Subtype.ext h1.symm))
  have hcard : (adjPairsOfEdge D q e).card ≤
      ({((⟨e.x₁, hx₁⟩ : GVert D), ⟨e.x₂, hx₂⟩), (⟨e.x₂, hx₂⟩, ⟨e.x₁, hx₁⟩)}
        : Finset (GVert D × GVert D)).card :=
    Finset.card_le_card hsub
  have h2 : (adjPairsOfEdge D q e).card ≤ 2 := le_trans hcard Finset.card_le_two
  exact_mod_cast h2

/-! ## The main bound -/

theorem sum_adj_le_edges {k : ℕ} {f : ℕ → ℂ} {c C X L P₁ P₂ : ℝ}
    (D : QuadData k f c C X L P₁ P₂) (q : ℕ) (g : ℝ → ℝ) (hg : ∀ x, 0 ≤ g x) :
    (∑ i : GVert D, ∑ j : GVert D,
        (if GAdjQ D q i j then (1 : ℝ) else 0) * g i.1 * g j.1)
      ≤ 2 * ∑ e ∈ D.edges.filter (fun e => q ∈ edgeS D e), g e.x₁ * g e.x₂ := by
  classical
  set w : GVert D × GVert D → ℝ := fun p => g p.1.1 * g p.2.1 with hw
  have hw_nn : ∀ p : GVert D × GVert D, 0 ≤ w p := fun p => mul_nonneg (hg _) (hg _)
  have hLHS : (∑ i : GVert D, ∑ j : GVert D,
        (if GAdjQ D q i j then (1 : ℝ) else 0) * g i.1 * g j.1) = ∑ p ∈ adjPairs D q, w p := by
    rw [← Finset.sum_product (Finset.univ) (Finset.univ)
      (fun p : GVert D × GVert D => (if GAdjQ D q p.1 p.2 then (1 : ℝ) else 0) * g p.1.1 * g p.2.1)]
    rw [Finset.univ_product_univ]
    rw [adjPairs, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    by_cases h : GAdjQ D q p.1 p.2 <;> simp [h, hw]
  suffices h : ∑ p ∈ adjPairs D q, w p ≤ 2 * ∑ e ∈ goodEdges D q, g e.x₁ * g e.x₂ by
    rwa [hLHS, show (2 : ℝ) * ∑ e ∈ D.edges.filter (fun e => q ∈ edgeS D e), g e.x₁ * g e.x₂
        = 2 * ∑ e ∈ goodEdges D q, g e.x₁ * g e.x₂ from by simp only [goodEdges]]
  have hstep1 : ∑ p ∈ adjPairs D q, w p
      ≤ ∑ p ∈ (goodEdges D q).biUnion (adjPairsOfEdge D q), w p :=
    Finset.sum_le_sum_of_subset_of_nonneg (adjPairs_subset_biUnion D q)
      (fun p _ _ => hw_nn p)
  have hstep2 : ∑ p ∈ (goodEdges D q).biUnion (adjPairsOfEdge D q), w p
      ≤ ∑ e ∈ goodEdges D q, ∑ p ∈ adjPairsOfEdge D q e, w p :=
    sum_biUnion_le_sum_of_nonneg (goodEdges D q) (adjPairsOfEdge D q) w hw_nn
  have hstep3 : ∑ e ∈ goodEdges D q, ∑ p ∈ adjPairsOfEdge D q e, w p
      ≤ ∑ e ∈ goodEdges D q, 2 * (g e.x₁ * g e.x₂) := by
    refine Finset.sum_le_sum (fun e he => ?_)
    have hee : e ∈ D.edges := (mem_goodEdges.mp he).1
    have hcard : ((adjPairsOfEdge D q e).card : ℝ) ≤ 2 := adjPairsOfEdge_card_le_two D q hee
    have hconst : ∀ p ∈ adjPairsOfEdge D q e, w p = g e.x₁ * g e.x₂ := by
      intro p hp
      simp only [mem_adjPairsOfEdge] at hp
      rcases hp.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [hw]; simp only; rw [h1, h2]
      · rw [hw]; simp only; rw [h1, h2]; ring
    calc ∑ p ∈ adjPairsOfEdge D q e, w p
        = ∑ p ∈ adjPairsOfEdge D q e, g e.x₁ * g e.x₂ := Finset.sum_congr rfl hconst
      _ = ((adjPairsOfEdge D q e).card : ℝ) * (g e.x₁ * g e.x₂) := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * (g e.x₁ * g e.x₂) :=
            mul_le_mul_of_nonneg_right hcard (mul_nonneg (hg _) (hg _))
  have hstep4 : ∑ e ∈ goodEdges D q, 2 * (g e.x₁ * g e.x₂)
      = 2 * ∑ e ∈ goodEdges D q, g e.x₁ * g e.x₂ := by
    rw [Finset.mul_sum]
  linarith [hstep1, hstep2, hstep3, hstep4]

end Work.BMF
