/-
# The cardinality of the ordered pairs of non-adjacent neighbours

For a finite simple graph `G` and a vertex `v`, the number of ordered pairs `(x, y)` of distinct
non-adjacent neighbours of `v` is

`|nonAdjPairs G v| = d (d - 1) - 2 e(G[N(v)])`,

where `d = deg(v) = |N(v)|` and `nbrEdges G v = e(G[N(v)])` is the number of edges of `G` spanned
by the neighbourhood of `v`.

Indeed, `N(v) × N(v)` splits into the diagonal (`d` pairs `(x, x)`), the adjacent off-diagonal
pairs and the non-adjacent off-diagonal pairs `nonAdjPairs G v`. The adjacent off-diagonal pairs
are exactly the two orientations of the edges spanned by `N(v)`, hence number `2 · nbrEdges G v`.
-/
import Submission.Work.Deep.Sparse.Prelude
import Submission.Work.Deep.Sparse.ProbModel

namespace Work.Deep.Sparse

/-- **The cardinality of the ordered pairs of non-adjacent neighbours.**
`|nonAdjPairs G v| = d(d − 1) − 2 e(G[N(v)])`, where `d = deg v`. -/
theorem nonadj_card {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    ((Work.Deep.Sparse.nonAdjPairs G v).card : ℤ)
      = (G.degree v : ℤ) * ((G.degree v : ℤ) - 1)
        - 2 * (ErdosFaberLovaszConjecture.nbrEdges G v : ℤ) := by
  classical
  set N : Finset V := G.neighborFinset v with hN
  set S : Finset (V × V) := N ×ˢ N with hS
  set T : Finset (V × V) := S.filter (fun p : V × V => p.1 ≠ p.2) with hT
  set B : Finset (V × V) := S.filter (fun p : V × V => G.Adj p.1 p.2) with hB
  set D : Finset (V × V) := S.filter (fun p : V × V => p.1 = p.2) with hD
  have hNcard : N.card = G.degree v := SimpleGraph.card_neighborFinset_eq_degree G v
  -- `nonAdjPairs` is defined with `Finset.product`; identify it with `S.filter`.
  have hAeq : nonAdjPairs G v = S.filter (fun p : V × V => p.1 ≠ p.2 ∧ ¬ G.Adj p.1 p.2) := by
    rw [nonAdjPairs, hS, hN]
    rfl
  -- (d) `S.card = d * d`
  have hSd : S.card = G.degree v * G.degree v := by
    rw [hS, Finset.card_product, hNcard]
  -- (c) the off-diagonal pairs split into `T` and the diagonal `D`
  have hTD : T.card + D.card = S.card := by
    have hunion : T ∪ D = S := by
      ext p
      simp only [hT, hD, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (h | h)
        · exact h.1
        · exact h.1
      · intro h
        by_cases h12 : p.1 = p.2
        · exact Or.inr ⟨h, h12⟩
        · exact Or.inl ⟨h, h12⟩
    have hdisj : Disjoint T D := by
      rw [Finset.disjoint_left]
      intro p hpT hpD
      rw [hT] at hpT
      rw [hD] at hpD
      simp only [Finset.mem_filter] at hpT hpD
      exact hpT.2 hpD.2
    rw [← hunion]
    exact (Finset.card_union_of_disjoint hdisj).symm
  -- (ii) the diagonal has `d` elements
  have hDcard : D.card = G.degree v := by
    have himg : D = N.image (fun x => (x, x)) := by
      rw [hD, hS]
      ext p
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image]
      constructor
      · rintro ⟨⟨h1, h2⟩, h12⟩
        exact ⟨p.1, h1, by ext <;> simp [h12]⟩
      · rintro ⟨x, hx, hxp⟩
        rw [← hxp]
        simp [hx]
    rw [himg, Finset.card_image_of_injective _ (fun a b h => by simpa using h), hNcard]
  -- (iii) the adjacent ordered pairs are the two orientations of the edges inside `N`
  have hB2 : B.card = 2 * ErdosFaberLovaszConjecture.nbrEdges G v := by
    rw [hB]
    set E : Finset (Sym2 V) := G.edgeFinset ∩ N.sym2 with hE
    have hEcard : E.card = ErdosFaberLovaszConjecture.nbrEdges G v :=
      (ErdosFaberLovaszConjecture.nbrEdges_eq_card_sym2 G v).symm
    have hmap : Set.MapsTo (fun p : V × V => s(p.1, p.2))
        ((S.filter (fun p : V × V => G.Adj p.1 p.2)) : Set (V × V)) (E : Set (Sym2 V)) := by
      intro p hp
      rw [Finset.mem_coe] at hp
      simp only [hS, hN, Finset.mem_filter, Finset.mem_product] at hp
      obtain ⟨⟨h1, h2⟩, hadj⟩ := hp
      rw [Finset.mem_coe, hE, Finset.mem_inter]
      exact ⟨by rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]; exact hadj,
        by rw [Finset.mk_mem_sym2_iff]; exact ⟨h1, h2⟩⟩
    have hfiber : ∀ e ∈ E,
        ((S.filter (fun p : V × V => G.Adj p.1 p.2)).filter (fun p => s(p.1, p.2) = e)).card = 2 := by
      intro e
      induction e using Sym2.ind with
      | _ x y =>
        intro he
        rw [hE, Finset.mem_inter] at he
        obtain ⟨he1, he2⟩ := he
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he1
        rw [Finset.mk_mem_sym2_iff] at he2
        obtain ⟨hxN, hyN⟩ := he2
        have hadj : G.Adj x y := he1
        have hfib : (S.filter (fun p : V × V => G.Adj p.1 p.2)).filter
              (fun p => s(p.1, p.2) = s(x, y)) = ({(x, y), (y, x)} : Finset (V × V)) := by
          rw [hS, hN]
          ext p
          simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_insert, Finset.mem_singleton,
            Sym2.eq_iff]
          constructor
          · rintro ⟨_, h | h⟩
            · exact Or.inl (Prod.ext_iff.mpr ⟨h.1, h.2⟩)
            · exact Or.inr (Prod.ext_iff.mpr ⟨h.1, h.2⟩)
          · intro h
            rcases h with h | h
            · subst h
              exact ⟨⟨⟨hxN, hyN⟩, hadj⟩, Or.inl ⟨rfl, rfl⟩⟩
            · subst h
              exact ⟨⟨⟨hyN, hxN⟩, hadj.symm⟩, Or.inr ⟨rfl, rfl⟩⟩
        rw [hfib, Finset.card_pair (by simp [Prod.ext_iff, G.ne_of_adj hadj])]
    rw [← hEcard]
    rw [Finset.card_eq_sum_card_fiberwise hmap]
    rw [Finset.sum_congr rfl (fun e he => hfiber e he)]
    rw [Finset.sum_const, smul_eq_mul]
    omega
  -- (i) the off-diagonal pairs split into `nonAdjPairs` and the adjacent pairs
  have hATB : (nonAdjPairs G v).card + B.card = T.card := by
    have hunion : nonAdjPairs G v ∪ B = T := by
      ext p
      simp only [hAeq, hB, hT, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (h | h)
        · exact ⟨h.1, h.2.1⟩
        · exact ⟨h.1, G.ne_of_adj h.2⟩
      · intro h
        by_cases hadj : G.Adj p.1 p.2
        · exact Or.inr ⟨h.1, hadj⟩
        · exact Or.inl ⟨h.1, h.2, hadj⟩
    have hdisj : Disjoint (nonAdjPairs G v) B := by
      rw [Finset.disjoint_left]
      intro p hpA hpB
      rw [hAeq] at hpA
      rw [hB] at hpB
      simp only [Finset.mem_filter] at hpA hpB
      exact hpA.2.2 hpB.2
    rw [← hunion]
    exact (Finset.card_union_of_disjoint hdisj).symm
  -- Assembly: `|nonAdjPairs| + 2 e = d (d - 1)` over `ℕ`, then cast to `ℤ`.
  have hmain : (nonAdjPairs G v).card + 2 * ErdosFaberLovaszConjecture.nbrEdges G v + G.degree v
      = G.degree v * G.degree v := by
    have h1 : T.card + G.degree v = S.card := by omega
    omega
  have hZ : (((nonAdjPairs G v).card : ℕ) : ℤ) + 2 * (ErdosFaberLovaszConjecture.nbrEdges G v : ℤ)
      + (G.degree v : ℤ) = (G.degree v : ℤ) * (G.degree v : ℤ) := by
    exact_mod_cast hmain
  have hgoal : (G.degree v : ℤ) * ((G.degree v : ℤ) - 1)
      - 2 * (ErdosFaberLovaszConjecture.nbrEdges G v : ℤ)
      = (G.degree v : ℤ) * (G.degree v : ℤ) - (G.degree v : ℤ)
        - 2 * (ErdosFaberLovaszConjecture.nbrEdges G v : ℤ) := by ring
  rw [hgoal]
  linarith [hZ]

end Work.Deep.Sparse
