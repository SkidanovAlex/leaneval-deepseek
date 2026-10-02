import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.Defs

open Classical

namespace Work.Deep.GKO.OneFact

variable {n : ℕ}

/-- The number of ordered pairs `(v, u)` with `v ∈ S`, `u ∈ T` and `F.Adj v u`.  This is the
incidence count in which all the double counting below is phrased. -/
noncomputable def pc (F : SimpleGraph (Fin n)) (S T : Finset (Fin n)) : ℕ :=
  ((S ×ˢ T).filter (fun p => F.Adj p.1 p.2)).card

/-- Every edge of a graph is `s(v, w)` for a pair of adjacent vertices. -/
lemma exists_adj_of_mem_edgeSet {F : SimpleGraph (Fin n)} {e : Sym2 (Fin n)}
    (he : e ∈ F.edgeSet) : ∃ v w : Fin n, F.Adj v w ∧ s(v, w) = e := by
  revert he
  refine Sym2.ind (fun v w he => ⟨v, w, (SimpleGraph.mem_edgeSet F).mp he, rfl⟩) e

/-- `Nat.card` of a neighbour set is the cardinality of the explicit `Finset` of neighbours. -/
lemma card_neighborSet_eq (F : SimpleGraph (Fin n)) (v : Fin n) :
    Nat.card (F.neighborSet v) =
      ((Finset.univ : Finset (Fin n)).filter (fun u => F.Adj v u)).card := by
  simp [SimpleGraph.neighborSet]

/-- Incidence counting is symmetric in its two vertex sets. -/
lemma pc_swap (F : SimpleGraph (Fin n)) (S T : Finset (Fin n)) : pc F S T = pc F T S := by
  unfold pc
  refine Finset.card_nbij' (fun p => p.swap) (fun p => p.swap) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [SetLike.mem_coe, Finset.mem_filter, Finset.mem_product] at hp ⊢
    exact ⟨⟨hp.1.2, hp.1.1⟩, (F.adj_comm p.1 p.2).mp hp.2⟩
  · intro p hp
    simp only [SetLike.mem_coe, Finset.mem_filter, Finset.mem_product] at hp ⊢
    exact ⟨⟨hp.1.2, hp.1.1⟩, (F.adj_comm p.1 p.2).mp hp.2⟩
  · intro p hp
    exact Prod.swap_swap p
  · intro p hp
    exact Prod.swap_swap p

/-- The incidence count depends on the second vertex set only through the neighbours of the
first-coordinate vertices in `S`. -/
lemma pc_congr (F : SimpleGraph (Fin n)) (S T T' : Finset (Fin n))
    (h : ∀ v w, v ∈ S → F.Adj v w → (w ∈ T ↔ w ∈ T')) : pc F S T = pc F S T' := by
  unfold pc
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨h1, h2⟩, hadj⟩
    exact ⟨⟨h1, (h p.1 p.2 h1 hadj).mp h2⟩, hadj⟩
  · rintro ⟨⟨h1, h2⟩, hadj⟩
    exact ⟨⟨h1, (h p.1 p.2 h1 hadj).mpr h2⟩, hadj⟩

/-- Incidence counts are additive over edge-disjoint unions of graphs. -/
lemma pc_sup (F F' : SimpleGraph (Fin n)) (h : Disjoint F.edgeSet F'.edgeSet)
    (S T : Finset (Fin n)) : pc (F ⊔ F') S T = pc F S T + pc F' S T := by
  unfold pc
  rw [Finset.filter_congr_decidable (S ×ˢ T) (fun p => (F ⊔ F').Adj p.1 p.2)]
  have hf : (S ×ˢ T).filter (fun p => (F ⊔ F').Adj p.1 p.2)
      = (S ×ˢ T).filter (fun p => F.Adj p.1 p.2) ∪ (S ×ˢ T).filter (fun p => F'.Adj p.1 p.2) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_union, SimpleGraph.sup_adj]
    tauto
  have hdisj : Disjoint ((S ×ˢ T).filter (fun p => F.Adj p.1 p.2))
      ((S ×ˢ T).filter (fun p => F'.Adj p.1 p.2)) := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    rw [Finset.mem_filter] at hp1 hp2
    have hh := Set.disjoint_left.mp h
    exact hh ((SimpleGraph.mem_edgeSet F).mpr hp1.2) ((SimpleGraph.mem_edgeSet F').mpr hp2.2)
  rw [hf, Finset.card_union_of_disjoint hdisj]

/-- The incidence count over the whole vertex set is the sum of the degrees. -/
lemma pc_univ (F : SimpleGraph (Fin n)) (S : Finset (Fin n)) :
    pc F S Finset.univ = ∑ v ∈ S, Nat.card (F.neighborSet v) := by
  unfold pc
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl (fun v hv => ?_)
  rw [← Finset.card_filter]
  exact (card_neighborSet_eq F v).symm

/-- For a regular graph the incidence count over the whole vertex set is `|S| · k`. -/
lemma pc_reg (F : SimpleGraph (Fin n)) {k : ℕ} (hreg : IsRegularOf F k) (S : Finset (Fin n)) :
    pc F S Finset.univ = S.card * k := by
  rw [pc_univ]
  rw [Finset.sum_congr rfl (fun v hv => hreg v)]
  exact Finset.sum_const_nat (fun _ _ => rfl)

/-- Incidence counts are additive over disjoint unions of the second vertex set. -/
lemma pc_union (F : SimpleGraph (Fin n)) (S T₁ T₂ : Finset (Fin n)) (h : Disjoint T₁ T₂) :
    pc F S (T₁ ∪ T₂) = pc F S T₁ + pc F S T₂ := by
  unfold pc
  have hf : (S ×ˢ (T₁ ∪ T₂)).filter (fun p => F.Adj p.1 p.2)
      = (S ×ˢ T₁).filter (fun p => F.Adj p.1 p.2) ∪ (S ×ˢ T₂).filter (fun p => F.Adj p.1 p.2) := by
    rw [Finset.product_union, Finset.filter_union]
  have hdisj : Disjoint ((S ×ˢ T₁).filter (fun p => F.Adj p.1 p.2))
      ((S ×ˢ T₂).filter (fun p => F.Adj p.1 p.2)) := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    rw [Finset.mem_filter, Finset.mem_product] at hp1 hp2
    exact (Finset.disjoint_left.mp h) hp1.1.2 hp2.1.2
  rw [hf, Finset.card_union_of_disjoint hdisj]

/-- A `Sym2`-image of a fibre-two family: if `t` is closed under swapping and contains no
diagonal pair, then each element of `t.image Sym2.mk.uncurry` has exactly two preimages, so
the image has half the cardinality of `t`. -/
lemma two_mul_card_image_sym2 {α : Type} [DecidableEq α] (t : Finset (α × α))
    (hswap : ∀ p ∈ t, p.swap ∈ t) (hdiag : ∀ p ∈ t, p.1 ≠ p.2) :
    2 * (t.image Sym2.mk.uncurry).card = t.card := by
  have hfiber : ∀ p ∈ t, (t.filter (fun q => Sym2.mk.uncurry q = Sym2.mk.uncurry p)).card = 2 := by
    intro p hp
    have hpair : t.filter (fun q => Sym2.mk.uncurry q = Sym2.mk.uncurry p) = {p, p.swap} := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hq, heq⟩
        rcases (Sym2.mk_eq_mk_iff.mp heq) with h | h
        · exact Or.inl h
        · exact Or.inr h
      · rintro (rfl | rfl)
        · exact ⟨hp, rfl⟩
        · exact ⟨hswap p hp, Sym2.eq_swap⟩
    have hne : p ≠ p.swap := fun h => hdiag p hp (by simpa [Prod.swap] using congrArg Prod.fst h)
    rw [hpair, Finset.card_insert_of_notMem (s := {p.swap}) (by simpa using hne),
      Finset.card_singleton]
  have hcongr : (∑ e ∈ t.image (Sym2.mk.uncurry : α × α → Sym2 α),
        (t.filter (fun q => Sym2.mk.uncurry q = e)).card)
      = ∑ e ∈ t.image (Sym2.mk.uncurry : α × α → Sym2 α), 2 := by
    refine Finset.sum_congr rfl (fun e he => ?_)
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
    exact hfiber p hp
  rw [Finset.card_eq_sum_card_image (f := (Sym2.mk.uncurry : α × α → Sym2 α)) (s := t), hcongr,
    Finset.sum_const_nat (s := t.image (Sym2.mk.uncurry : α × α → Sym2 α))
      (f := fun _ => 2) (fun _ _ => rfl),
    Nat.mul_comm]

/-- Double counting: twice the number of edges of a graph lying inside `S` is the number of
ordered pairs of adjacent vertices of `S`. -/
lemma two_mul_card_edges_inside {n : ℕ} (F : SimpleGraph (Fin n)) (S : Finset (Fin n)) :
    2 * Nat.card {e : Sym2 (Fin n) | e ∈ F.edgeSet ∧ (e : Set (Fin n)) ⊆ (S : Set (Fin n))}
      = pc F S S := by
  have hbridge : Nat.card {e : Sym2 (Fin n) | e ∈ F.edgeSet ∧ (e : Set (Fin n)) ⊆ (S : Set (Fin n))}
      = ((Finset.univ : Finset (Sym2 (Fin n))).filter
          (fun e => e ∈ F.edgeSet ∧ (e : Set (Fin n)) ⊆ (S : Set (Fin n)))).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rfl
  rw [hbridge]
  unfold pc
  have himg : ((Finset.univ : Finset (Sym2 (Fin n))).filter
        (fun e => e ∈ F.edgeSet ∧ (e : Set (Fin n)) ⊆ (S : Set (Fin n))))
      = ((S ×ˢ S).filter (fun p => F.Adj p.1 p.2)).image Sym2.mk.uncurry := by
    ext e
    constructor
    · intro he
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
      obtain ⟨hee, hsub⟩ := he
      obtain ⟨v, w, hvw, rfl⟩ := exists_adj_of_mem_edgeSet hee
      refine Finset.mem_image.mpr ⟨(v, w), ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hsub (by rw [SetLike.mem_coe, Sym2.mem_iff]; exact Or.inl rfl),
        hsub (by rw [SetLike.mem_coe, Sym2.mem_iff]; exact Or.inr rfl)⟩, hvw⟩
    · intro he
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨v, w⟩ := p
      simp only [Finset.mem_filter, Finset.mem_product] at hp
      obtain ⟨⟨hp1, hp2⟩, hadj⟩ := hp
      change s(v, w) ∈ (Finset.univ.filter (fun e : Sym2 (Fin n) =>
        e ∈ F.edgeSet ∧ (e : Set (Fin n)) ⊆ (S : Set (Fin n))))
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨(SimpleGraph.mem_edgeSet F).mpr hadj, ?_⟩
      intro x hx
      rw [SetLike.mem_coe, Sym2.mem_iff] at hx
      rcases hx with rfl | rfl
      · exact hp1
      · exact hp2
  rw [himg]
  rw [two_mul_card_image_sym2 ((S ×ˢ S).filter (fun p => F.Adj p.1 p.2)) ?_ ?_]
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp ⊢
    exact ⟨⟨hp.1.2, hp.1.1⟩, (F.adj_comm p.1 p.2).mp hp.2⟩
  · intro p hp
    simp only [Finset.mem_filter] at hp
    exact F.ne_of_adj hp.2

/-- For a graph `H ⊔ H₀` that is `k`-regular, whose left part `H` is bipartite between the two equal halves `A`, `B`, the number of edges of `H₀` lying inside `A` equals the number lying inside `B`. -/
theorem insideCountEq {n : ℕ} (A B : Finset (Fin n)) (H H₀ : SimpleGraph (Fin n))
    (hAB : Disjoint A B) (hcov : A ∪ B = Finset.univ) (hdisj : Disjoint H.edgeSet H₀.edgeSet)
    (hbip : ∀ u v : Fin n, H.Adj u v → (u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A))
    (hcard : A.card = B.card) {k : ℕ} (hreg : Work.Deep.GKO.IsRegularOf (H ⊔ H₀) k) :
    Nat.card {e : Sym2 (Fin n) | e ∈ H₀.edgeSet ∧ (e : Set (Fin n)) ⊆ (A : Set (Fin n))}
      = Nat.card {e : Sym2 (Fin n) | e ∈ H₀.edgeSet ∧ (e : Set (Fin n)) ⊆ (B : Set (Fin n))} := by
  -- Every vertex contributes `k` to the incidence count of the half containing it, and the
  -- two halves have the same size.
  have hsum : pc (H ⊔ H₀) A Finset.univ = pc (H ⊔ H₀) B Finset.univ := by
    rw [pc_reg (H ⊔ H₀) hreg A, pc_reg (H ⊔ H₀) hreg B, hcard]
  have hsupA : pc (H ⊔ H₀) A Finset.univ = pc H A Finset.univ + pc H₀ A Finset.univ :=
    pc_sup H H₀ hdisj A Finset.univ
  have hsupB : pc (H ⊔ H₀) B Finset.univ = pc H B Finset.univ + pc H₀ B Finset.univ :=
    pc_sup H H₀ hdisj B Finset.univ
  -- `H` only has edges between `A` and `B`, so its incidence counts at the two halves agree.
  have hH : pc H A Finset.univ = pc H B Finset.univ := by
    have h1 : pc H A Finset.univ = pc H A B := by
      refine pc_congr H A Finset.univ B (fun v w hv hadj => ?_)
      constructor
      · intro _
        rcases hbip v w hadj with ⟨-, hwB⟩ | ⟨hvB, _⟩
        · exact hwB
        · exact absurd hvB ((Finset.disjoint_left.mp hAB) hv)
      · intro _; exact Finset.mem_univ w
    have h2 : pc H B Finset.univ = pc H B A := by
      refine pc_congr H B Finset.univ A (fun v w hv hadj => ?_)
      constructor
      · intro _
        rcases hbip v w hadj with ⟨hvA, _⟩ | ⟨-, hwA⟩
        · exact absurd hv ((Finset.disjoint_left.mp hAB) hvA)
        · exact hwA
      · intro _; exact Finset.mem_univ w
    rw [h1, h2, pc_swap H A B]
  -- Hence the incidence counts of `H₀` at the two halves agree as well.
  have hH0 : pc H₀ A Finset.univ = pc H₀ B Finset.univ := by
    have h := hsum
    rw [hsupA, hsupB, hH] at h
    exact Nat.add_left_cancel h
  -- Splitting the incidence counts of `H₀` by the half of the second endpoint, the two cross
  -- terms agree, so the inside terms agree.
  have hsplitA : pc H₀ A Finset.univ = pc H₀ A A + pc H₀ A B := by
    rw [← hcov]
    exact pc_union H₀ A A B hAB
  have hsplitB : pc H₀ B Finset.univ = pc H₀ B A + pc H₀ B B := by
    rw [← hcov]
    exact pc_union H₀ B A B hAB
  have hfin : pc H₀ A A = pc H₀ B B := by
    have h := hH0
    rw [hsplitA, hsplitB, pc_swap H₀ A B] at h
    exact Nat.add_right_cancel (h.trans (Nat.add_comm (pc H₀ B A) (pc H₀ B B)))
  -- Doubling back: each inside edge accounts for two of the ordered pairs, so the inside counts
  -- are half of the corresponding incidence counts.
  have h2A := two_mul_card_edges_inside H₀ A
  have h2B := two_mul_card_edges_inside H₀ B
  have hmul : 2 * Nat.card {e : Sym2 (Fin n) |
        e ∈ H₀.edgeSet ∧ (e : Set (Fin n)) ⊆ (A : Set (Fin n))}
      = 2 * Nat.card {e : Sym2 (Fin n) |
        e ∈ H₀.edgeSet ∧ (e : Set (Fin n)) ⊆ (B : Set (Fin n))} := by
    rw [h2A, h2B, hfin]
  exact Nat.mul_left_cancel (by norm_num) hmul

end Work.Deep.GKO.OneFact
