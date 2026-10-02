import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.Defs
import Submission.Work.Deep.GKO.exists_deficiencyMatchings
import Submission.Work.Deep.GKO.exists_matchingSplit

/-!
# Splitting the deficiency matchings into matchings of bounded size

`Work.Deep.GKO.exists_deficiencyMatchings` realises a degree sequence `d` (Hakimi's
criterion, degrees bounded by `D`) as the incidence vectors of at most `2 * D` matchings.
For the spanning-linkage step of the reduction one needs the individual matchings to be
*small*.  This file splits each of the `≤ 2 * D` matchings into blocks of at most `s`
edges: a matching with `m` edges is cut into `1 + m / s` pieces, and since a matching on
`n` vertices has at most `n / 2` edges, each of the `≤ 2 * D` matchings gives at most
`1 + n / (2 * s)` pieces.  Discarding the empty pieces (which lowers the count and leaves
the covering numbers unchanged) yields the stated decomposition.

## Main results

* `Work.Deep.GKO.matching_card_edgeSet_le` — a matching on `Fin n` has at most `n / 2` edges;
* `Work.Deep.GKO.splitCount` — a partition of the edge set of a matching covers each vertex
  at most once, and exactly once if the matching covers it;
* `Work.Deep.GKO.padFam` — the pieces of a split, padded with empty graphs to a uniform
  length;
* `Work.Deep.GKO.exists_filter_nonempty` — discarding the empty members of a finite family
  of matchings of bounded edge-set size;
* `Work.Deep.GKO.exists_deficiencyMatchings_split` — the combination.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Deep.GKO

attribute [local instance] Classical.propDecidable

/-! ## A matching has at most `n / 2` edges -/

/-- A matching on `Fin n` has at most `n / 2` edges: its `m` edges are pairwise disjoint
two-element subsets of the `n` vertices.  (Proved through the degree sum: every vertex has
degree at most `1`, so `2 * m = Σ_v deg v ≤ n`.) -/
private lemma matching_card_edgeSet_le {n : ℕ} {G : SimpleGraph (Fin n)} (hG : IsMatching' G) :
    Nat.card G.edgeSet ≤ n / 2 := by
  classical
  have hdeg : ∀ v : Fin n, G.degree v ≤ 1 := by
    intro v
    rw [← SimpleGraph.card_neighborSet_eq_degree]
    have hsub : Subsingleton ↥(G.neighborSet v) :=
      ⟨fun a b => Subtype.ext (hG v a.val b.val a.2 b.2)⟩
    calc Fintype.card ↥(G.neighborSet v) ≤ Fintype.card (Fin 1) :=
          Fintype.card_le_of_injective (fun _ => (0 : Fin 1)) (fun a b _ => hsub.1 a b)
      _ = 1 := Fintype.card_fin 1
  have hcard : Nat.card G.edgeSet = G.edgeFinset.card := by
    rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
  have h1 : 2 * Nat.card G.edgeSet ≤ n := by
    calc 2 * Nat.card G.edgeSet = 2 * G.edgeFinset.card := by rw [hcard]
      _ = ∑ v, G.degree v := (SimpleGraph.sum_degrees_eq_twice_card_edges G).symm
      _ ≤ ∑ v : Fin n, 1 := Finset.sum_le_sum (fun v _ => hdeg v)
      _ = n := by simp
  omega

/-! ## Counting the pieces that cover a vertex -/

/-- If the edge set of a matching `G` is partitioned into the edge sets of the graphs
`F j` (`j : Fin K`), then every vertex is covered by at most one of the `F j`, and by
exactly one if it is covered by `G`. -/
private lemma splitCount {n K : ℕ} {G : SimpleGraph (Fin n)} (hG : IsMatching' G)
    (F : Fin K → SimpleGraph (Fin n))
    (hle : ∀ j, F j ≤ G)
    (hdisj : ∀ j j', j ≠ j' → Disjoint (F j).edgeSet (F j').edgeSet)
    (hcov : ∀ e ∈ G.edgeSet, ∃ j, e ∈ (F j).edgeSet) (v : Fin n) :
    ((Finset.univ.filter (fun j => ∃ w, (F j).Adj v w)).card : ℕ) =
      if ∃ w, G.Adj v w then 1 else 0 := by
  classical
  by_cases hcov' : ∃ w, G.Adj v w
  · rw [if_pos hcov']
    obtain ⟨u, hu⟩ := hcov'
    obtain ⟨j, hj⟩ := hcov (s(v, u)) ((SimpleGraph.mem_edgeSet G).mpr hu)
    have hjcov : j ∈ Finset.univ.filter (fun j => ∃ w, (F j).Adj v w) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ j, ⟨u, (SimpleGraph.mem_edgeSet (F j)).mp hj⟩⟩
    have hle1 : (Finset.univ.filter (fun j => ∃ w, (F j).Adj v w)).card ≤ 1 := by
      refine Finset.card_le_one.mpr ?_
      intro x hx y hy
      obtain ⟨w, hw⟩ := (Finset.mem_filter.mp hx).2
      obtain ⟨w', hw'⟩ := (Finset.mem_filter.mp hy).2
      have hww : w = w' := hG v w w' (hle x hw) (hle y hw')
      by_cases hxy : x = y
      · exact hxy
      · exfalso
        have e1 : s(v, w) ∈ (F x).edgeSet := (SimpleGraph.mem_edgeSet (F x)).mpr hw
        have e2 : s(v, w) ∈ (F y).edgeSet := by
          rw [hww]; exact (SimpleGraph.mem_edgeSet (F y)).mpr hw'
        exact (Set.disjoint_left.mp (hdisj x y hxy)) e1 e2
    have hge1 : 1 ≤ (Finset.univ.filter (fun j => ∃ w, (F j).Adj v w)).card :=
      Finset.card_pos.mpr ⟨j, hjcov⟩
    omega
  · rw [if_neg hcov']
    have hemp : Finset.univ.filter (fun j => ∃ w, (F j).Adj v w) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr ?_
      intro j _ ⟨w, hw⟩
      exact hcov' ⟨w, hle j hw⟩
    rw [hemp]
    simp

/-! ## Padding a split to a fixed length -/

/-- The family of the `K` pieces `P j`, padded with the empty graph up to a family indexed
by `Fin L` (the pieces with index `≥ K` become empty graphs, and are discarded later). -/
private def padFam {n K : ℕ} (P : Fin K → SimpleGraph (Fin n)) (L : ℕ) :
    Fin L → SimpleGraph (Fin n) :=
  fun j => if h : (j : ℕ) < K then P ⟨(j : ℕ), h⟩ else ⊥

private lemma padFam_lt {n K L : ℕ} (P : Fin K → SimpleGraph (Fin n)) {j : Fin L}
    (h : (j : ℕ) < K) : padFam P L j = P ⟨(j : ℕ), h⟩ := dif_pos h

private lemma padFam_ge {n K L : ℕ} (P : Fin K → SimpleGraph (Fin n)) {j : Fin L}
    (h : ¬ (j : ℕ) < K) : padFam P L j = ⊥ := dif_neg h

private lemma padFam_match {n K L : ℕ} {P : Fin K → SimpleGraph (Fin n)}
    (h : ∀ j, IsMatching' (P j)) (j : Fin L) : IsMatching' (padFam P L j) := by
  by_cases hj : (j : ℕ) < K
  · rw [padFam_lt P hj]; exact h _
  · rw [padFam_ge P hj]
    intro v w w' hw _
    exact absurd hw (by simp)

private lemma padFam_le {n K L : ℕ} {G : SimpleGraph (Fin n)} {P : Fin K → SimpleGraph (Fin n)}
    (h : ∀ j, P j ≤ G) (j : Fin L) : padFam P L j ≤ G := by
  by_cases hj : (j : ℕ) < K
  · rw [padFam_lt P hj]; exact h _
  · rw [padFam_ge P hj]; exact bot_le

private lemma disjoint_edgeSet_bot {n : ℕ} (G : SimpleGraph (Fin n)) :
    Disjoint G.edgeSet ((⊥ : SimpleGraph (Fin n)).edgeSet) := by
  rw [SimpleGraph.edgeSet_bot]
  exact Set.disjoint_right.mpr fun a ha => absurd ha (Set.notMem_empty a)

private lemma disjoint_bot_edgeSet {n : ℕ} (G : SimpleGraph (Fin n)) :
    Disjoint ((⊥ : SimpleGraph (Fin n)).edgeSet) G.edgeSet := by
  rw [SimpleGraph.edgeSet_bot]
  exact Set.disjoint_left.mpr fun a ha => absurd ha (Set.notMem_empty a)

private lemma padFam_card {n K L s : ℕ} {P : Fin K → SimpleGraph (Fin n)}
    (h : ∀ j, Nat.card ((P j).edgeSet) ≤ s) (j : Fin L) :
    Nat.card ((padFam P L j).edgeSet) ≤ s := by
  by_cases hj : (j : ℕ) < K
  · rw [padFam_lt P hj]; exact h _
  · rw [padFam_ge P hj]
    have h0 : Nat.card ((⊥ : SimpleGraph (Fin n)).edgeSet) = 0 := by
      rw [SimpleGraph.edgeSet_bot]
      exact Nat.card_eq_zero.mpr (Or.inl ⟨fun x => absurd x.2 (Set.notMem_empty x.val)⟩)
    omega

private lemma padFam_disj {n K L : ℕ} {P : Fin K → SimpleGraph (Fin n)}
    (hdisj : ∀ j j', j ≠ j' → Disjoint (P j).edgeSet (P j').edgeSet)
    (j j' : Fin L) (hjj' : j ≠ j') :
    Disjoint ((padFam P L j).edgeSet) ((padFam P L j').edgeSet) := by
  by_cases h1 : (j : ℕ) < K
  · by_cases h2 : (j' : ℕ) < K
    · rw [padFam_lt P h1, padFam_lt P h2]
      exact hdisj _ _ (fun hh => hjj' (Fin.val_injective (Fin.mk.inj hh)))
    · rw [padFam_lt P h1, padFam_ge P h2]
      exact disjoint_edgeSet_bot _
  · by_cases h2 : (j' : ℕ) < K
    · rw [padFam_ge P h1, padFam_lt P h2]
      exact disjoint_bot_edgeSet _
    · rw [padFam_ge P h1, padFam_ge P h2]
      exact disjoint_bot_edgeSet _

private lemma padFam_cov {n K L : ℕ} {G : SimpleGraph (Fin n)} {P : Fin K → SimpleGraph (Fin n)}
    (hK : K ≤ L) (hcov : ∀ e ∈ G.edgeSet, ∃ j, e ∈ (P j).edgeSet)
    (e : Sym2 (Fin n)) (he : e ∈ G.edgeSet) : ∃ j : Fin L, e ∈ ((padFam P L j).edgeSet) := by
  obtain ⟨j₀, hj₀⟩ := hcov e he
  have hL : (j₀ : ℕ) < L := Nat.lt_of_lt_of_le j₀.isLt hK
  refine ⟨⟨(j₀ : ℕ), hL⟩, ?_⟩
  rw [padFam_lt P (j := (⟨(j₀ : ℕ), hL⟩ : Fin L)) j₀.isLt]
  exact hj₀

/-! ## Products of finite types -/

private lemma natCard_filter' {α : Type*} [Fintype α] [DecidableEq α] (p : α → Prop)
    [DecidablePred p] : Nat.card {i : α // p i} = (Finset.univ.filter p).card := by
  have H : ∀ i : α, i ∈ Finset.univ.filter p ↔ p i := fun i => by simp
  exact (@Nat.card_eq_fintype_card _ (Fintype.subtype (Finset.univ.filter p) H)).trans
    (Fintype.subtype_card (Finset.univ.filter p) H)

/-- Cardinality of a filtered product: counting the pairs of a product type fibre by fibre. -/
private lemma filter_card_product {k₁ k₂ : ℕ} (Q : Fin k₁ × Fin k₂ → Prop) [DecidablePred Q] :
    ((Finset.univ.filter Q).card : ℕ) =
      ∑ i : Fin k₁, ((Finset.univ.filter (fun j => Q (i, j))).card : ℕ) := by
  classical
  have hR : (∑ i : Fin k₁, ((Finset.univ.filter (fun j => Q (i, j))).card : ℕ))
      = ∑ i : Fin k₁, ∑ j : Fin k₂, (if Q (i, j) then 1 else 0 : ℕ) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [hR, Finset.card_eq_sum_ones, Finset.sum_filter, ← Finset.univ_product_univ,
    Finset.sum_product]

/-! ## Discarding the empty members of a family of matchings -/

/-- Discarding the empty members of a finite family of matchings of edge-set size at most
`s` gives a family (indexed by `Fin k`, `k ≤ card α`) of *nonempty* matchings of edge-set
size at most `s`, preserving the number of members covering each vertex. -/
private theorem exists_filter_nonempty {n s : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (F : α → SimpleGraph (Fin n)) (d : Fin n → ℕ)
    (hmatch : ∀ a, IsMatching' (F a))
    (hcard : ∀ a, Nat.card ((F a).edgeSet) ≤ s)
    (hcount : ∀ v : Fin n, Nat.card {a : α // ∃ w, (F a).Adj v w} = d v) :
    ∃ (k : ℕ) (M : Fin k → SimpleGraph (Fin n)),
      k ≤ Fintype.card α ∧
      (∀ i, IsMatching' (M i)) ∧
      (∀ i, 0 < Nat.card ((M i).edgeSet)) ∧
      (∀ i, Nat.card ((M i).edgeSet) ≤ s) ∧
      (∀ v : Fin n, Nat.card {i : Fin k // ∃ w, (M i).Adj v w} = d v) := by
  classical
  set U : Finset α := (Finset.univ : Finset α).filter (fun a => 0 < Nat.card ((F a).edgeSet))
    with hU
  set e : Fin U.card ≃ ↥U := (U.equivFinOfCardEq rfl).symm with he
  have hmem : ∀ i : Fin U.card, 0 < Nat.card ((F (e i)).edgeSet) :=
    fun i => (Finset.mem_filter.mp (e i).2).2
  refine ⟨U.card, fun i => F (e i), ?_, ?_, ?_, ?_, ?_⟩
  · calc U.card ≤ (Finset.univ : Finset α).card := Finset.card_filter_le _ _
      _ = Fintype.card α := Finset.card_univ
  · intro i; exact hmatch _
  · intro i; exact hmem i
  · intro i; exact hcard _
  · intro v
    have hp : ∀ a : α, (∃ w, (F a).Adj v w) → a ∈ U := fun a ⟨w, hw⟩ =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ a,
        Nat.card_pos_iff.mpr ⟨⟨s(v, w), (SimpleGraph.mem_edgeSet (F a)).mpr hw⟩, inferInstance⟩⟩
    show Nat.card {i : Fin U.card // ∃ w, (F (e i)).Adj v w} = d v
    calc Nat.card {i : Fin U.card // ∃ w, (F (e i)).Adj v w}
        = Nat.card {a : α // ∃ w, (F a).Adj v w} :=
          Nat.card_congr ((Equiv.subtypeEquiv e (fun i => Iff.rfl)).trans
            (Equiv.subtypeSubtypeEquivSubtype (p := fun a => a ∈ U)
              (q := fun a => ∃ w, (F a).Adj v w) (fun {a} hP => hp a hP)))
      _ = d v := hcount v

/-! ## The main theorem -/

/-- Degree sequences realizable by multigraphs decompose into matchings of bounded size: if `Σ d` is even, `d v ≤ Σ_{u ≠ v} d u` for every `v` (Hakimi's criterion) and `D` bounds the degrees, then there are `k ≤ 2D(1 + n/(2s))` matchings `M i`, each nonempty with at most `s` edges, such that every vertex `v` is covered by exactly `d v` of them.

Combine `Work.Deep.GKO.exists_deficiencyMatchings` (which produces at most `2D` matchings of unbounded size) with `Work.Deep.GKO.exists_matchingSplit`: a matching with `m` edges splits into `≤ 1 + m/s` matchings with at most `s` edges each, so the total is at most `2D(1 + n/(2s))` because a matching in `Fin n` has at most `n/2` edges.  Empty pieces have to be filtered out, which only decreases `k` and does not affect the covering counts. -/
theorem exists_deficiencyMatchings_split {n : ℕ} (d : Fin n → ℕ) {D s : ℕ}
    (heven : Even (∑ v, d v)) (hmax : ∀ v : Fin n, d v ≤ ∑ u ∈ Finset.univ.erase v, d u)
    (hD : ∀ v : Fin n, d v ≤ D) (hs : 0 < s) :
    ∃ (k : ℕ) (M : Fin k → SimpleGraph (Fin n)),
      k ≤ 2 * D * (1 + n / (2 * s)) ∧
      (∀ i, Work.Deep.GKO.IsMatching' (M i)) ∧
      (∀ i, 0 < Nat.card ((M i).edgeSet)) ∧
      (∀ i, Nat.card ((M i).edgeSet) ≤ s) ∧
      (∀ v : Fin n, Nat.card {i : Fin k // ∃ w, (M i).Adj v w} = d v) := by
  classical
  -- the deficiency step: at most `2 * D` matchings of unbounded size
  obtain ⟨k₀, M₀, hk₀, hmatch₀, hcount₀⟩ := exists_deficiencyMatchings d heven hmax hD
  -- split each of them into matchings of at most `s` edges
  have hsplit : ∀ i : Fin k₀, ∃ (K : ℕ) (P : Fin K → SimpleGraph (Fin n)),
      (∀ j, IsMatching' (P j)) ∧ (∀ j, P j ≤ M₀ i) ∧
      (∀ j, Nat.card ((P j).edgeSet) ≤ s) ∧
      (∀ j j', j ≠ j' → Disjoint (P j).edgeSet (P j').edgeSet) ∧
      (∀ e ∈ (M₀ i).edgeSet, ∃ j, e ∈ (P j).edgeSet) ∧
      (K ≤ 1 + Nat.card (M₀ i).edgeSet / s) :=
    fun i => exists_matchingSplit (M₀ i) (hmatch₀ i) hs
  choose KOf P hP1 hP2 hP3 hP4 hP5 hP6 using hsplit
  -- each matching has at most `n / 2` edges, so `KOf i ≤ 1 + n / (2 * s)`
  have hKL : ∀ i : Fin k₀, KOf i ≤ 1 + n / (2 * s) := by
    intro i
    have h1 : Nat.card (M₀ i).edgeSet / s ≤ n / (2 * s) := by
      rw [← Nat.div_div_eq_div_mul n 2 s]
      exact Nat.div_le_div_right (matching_card_edgeSet_le (hmatch₀ i))
    exact (hP6 i).trans (Nat.add_le_add_left h1 1)
  -- the count for the padded product family
  have hcountF : ∀ v : Fin n,
      Nat.card {p : Fin k₀ × Fin (1 + n / (2 * s)) //
          ∃ w, (padFam (P p.1) (1 + n / (2 * s)) p.2).Adj v w} = d v := by
    intro v
    have e2a : ((Finset.univ.filter (fun p : Fin k₀ × Fin (1 + n / (2 * s)) =>
          ∃ w, (padFam (P p.1) (1 + n / (2 * s)) p.2).Adj v w)).card : ℕ) =
        ∑ i : Fin k₀, ((Finset.univ.filter (fun j : Fin (1 + n / (2 * s)) =>
          ∃ w, (padFam (P i) (1 + n / (2 * s)) j).Adj v w)).card : ℕ) :=
      filter_card_product _
    have e2b : ∀ i : Fin k₀, ((Finset.univ.filter (fun j : Fin (1 + n / (2 * s)) =>
          ∃ w, (padFam (P i) (1 + n / (2 * s)) j).Adj v w)).card : ℕ) =
        (if ∃ w, (M₀ i).Adj v w then 1 else 0) := fun i =>
      splitCount (hmatch₀ i) (padFam (P i) (1 + n / (2 * s)))
        (padFam_le (G := M₀ i) (hP2 i)) (padFam_disj (P := P i) (hP4 i))
        (padFam_cov (hK := hKL i) (hP5 i)) v
    have e2c : ((Finset.univ.filter (fun i : Fin k₀ => ∃ w, (M₀ i).Adj v w)).card : ℕ) =
        ∑ i : Fin k₀, (if ∃ w, (M₀ i).Adj v w then 1 else 0) := by
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    calc Nat.card {p : Fin k₀ × Fin (1 + n / (2 * s)) //
            ∃ w, (padFam (P p.1) (1 + n / (2 * s)) p.2).Adj v w}
        = ((Finset.univ.filter (fun p : Fin k₀ × Fin (1 + n / (2 * s)) =>
            ∃ w, (padFam (P p.1) (1 + n / (2 * s)) p.2).Adj v w)).card : ℕ) :=
          natCard_filter' _
      _ = ∑ i : Fin k₀, ((Finset.univ.filter (fun j : Fin (1 + n / (2 * s)) =>
            ∃ w, (padFam (P i) (1 + n / (2 * s)) j).Adj v w)).card : ℕ) := e2a
      _ = ∑ i : Fin k₀, (if ∃ w, (M₀ i).Adj v w then 1 else 0) :=
          Finset.sum_congr rfl (fun i _ => e2b i)
      _ = ((Finset.univ.filter (fun i : Fin k₀ => ∃ w, (M₀ i).Adj v w)).card : ℕ) := e2c.symm
      _ = Nat.card {i : Fin k₀ // ∃ w, (M₀ i).Adj v w} := (natCard_filter' _).symm
      _ = d v := hcount₀ v
  -- discard the empty pieces
  obtain ⟨k, M, hk, hmatch, hne, hcard, hcount⟩ :=
    exists_filter_nonempty (fun p : Fin k₀ × Fin (1 + n / (2 * s)) =>
      padFam (P p.1) (1 + n / (2 * s)) p.2) d
      (fun p => padFam_match (hP1 p.1) p.2) (fun p => padFam_card (hP3 p.1) p.2) hcountF
  refine ⟨k, M, ?_, hmatch, hne, hcard, hcount⟩
  calc k ≤ Fintype.card (Fin k₀ × Fin (1 + n / (2 * s))) := hk
    _ = k₀ * (1 + n / (2 * s)) := by
        rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    _ ≤ 2 * D * (1 + n / (2 * s)) := Nat.mul_le_mul_right _ hk₀

end Work.Deep.GKO
