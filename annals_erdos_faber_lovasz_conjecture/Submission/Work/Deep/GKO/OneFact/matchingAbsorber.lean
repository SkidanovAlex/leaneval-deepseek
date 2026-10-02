import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.OneFactDefs
import Submission.Work.Deep.GKO.RegVocab
import Submission.Work.Deep.GKO.OneFact.gridRefine
import Submission.Work.Deep.GKO.OneFact.splitMatching
import Submission.Work.Deep.GKO.Abs.insideDecomp
import Submission.Work.Deep.GKO.Abs.hallBipClean
import Submission.Work.Deep.GKO.Abs.oneFactorOfMatchingFamily

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open scoped BigOperators
open Finset

namespace Work.Deep.GKO.OneFact

variable {n : ℕ}

/-! ## Elementary counting for `crossEdges` and `degIn` -/

/-- `crossEdges` is the sum over `A` of the degrees into `B`. -/
theorem crossEdges_eq_sum_degIn (G : SimpleGraph (Fin n)) (A B : Finset (Fin n)) :
    Work.Deep.GKO.crossEdges G A B = ∑ a ∈ A, Work.Deep.GKO.degIn G a B := by
  unfold Work.Deep.GKO.crossEdges Work.Deep.GKO.degIn Work.Deep.GKO.nbrFinset
  rw [Finset.product_eq_sprod, Finset.card_filter, Finset.sum_product]
  exact Finset.sum_congr rfl (fun a _ => by rw [Finset.card_filter])

/-- `∑ a ∈ A, degIn G a B = ∑ b ∈ B, degIn G b A`: both sides count the `A`-`B` edges. -/
theorem sum_degIn_comm (G : SimpleGraph (Fin n)) (A B : Finset (Fin n)) :
    (∑ a ∈ A, Work.Deep.GKO.degIn G a B) = ∑ b ∈ B, Work.Deep.GKO.degIn G b A := by
  classical
  simp only [Work.Deep.GKO.degIn, Work.Deep.GKO.nbrFinset, Finset.card_filter]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by
    rw [SimpleGraph.adj_comm]

/-- `crossEdges` is symmetric in the two vertex sets. -/
theorem crossEdges_comm (G : SimpleGraph (Fin n)) (A B : Finset (Fin n)) :
    Work.Deep.GKO.crossEdges G A B = Work.Deep.GKO.crossEdges G B A := by
  rw [crossEdges_eq_sum_degIn, crossEdges_eq_sum_degIn, sum_degIn_comm]

/-- `crossEdges` is monotone in the graph. -/
theorem crossEdges_mono {G G' : SimpleGraph (Fin n)} (h : G ≤ G') (A B : Finset (Fin n)) :
    Work.Deep.GKO.crossEdges G A B ≤ Work.Deep.GKO.crossEdges G' A B := by
  classical
  rw [crossEdges_eq_sum_degIn, crossEdges_eq_sum_degIn]
  refine Finset.sum_le_sum fun a _ => ?_
  simp only [Work.Deep.GKO.degIn, Work.Deep.GKO.nbrFinset]
  exact Finset.card_le_card fun b hb =>
    Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hb).1, h (Finset.mem_filter.mp hb).2⟩

/-- A matching has at most one edge at each vertex. -/
theorem degIn_le_one_of_matching {M : SimpleGraph (Fin n)}
    (hM : Work.Deep.GKO.IsMatching' M) (x : Fin n) (S : Finset (Fin n)) :
    Work.Deep.GKO.degIn M x S ≤ 1 := by
  classical
  rw [Work.Deep.GKO.degIn, Work.Deep.GKO.nbrFinset, Finset.card_le_one]
  intro y hy z hz
  exact hM x y z (Finset.mem_filter.mp hy).2 (Finset.mem_filter.mp hz).2

/-- A matching spans at most `min |A| |B|` edges between two vertex sets. -/
theorem crossEdges_le_min_of_matching {M : SimpleGraph (Fin n)}
    (hM : Work.Deep.GKO.IsMatching' M) (A B : Finset (Fin n)) :
    Work.Deep.GKO.crossEdges M A B ≤ min A.card B.card := by
  classical
  refine le_min ?_ ?_
  · rw [crossEdges_eq_sum_degIn]
    calc ∑ a ∈ A, Work.Deep.GKO.degIn M a B ≤ ∑ _a ∈ A, 1 :=
          Finset.sum_le_sum fun a _ => degIn_le_one_of_matching hM a B
      _ = A.card := by simp
  · rw [crossEdges_comm, crossEdges_eq_sum_degIn]
    calc ∑ b ∈ B, Work.Deep.GKO.degIn M b A ≤ ∑ _b ∈ B, 1 :=
          Finset.sum_le_sum fun b _ => degIn_le_one_of_matching hM b A
      _ = B.card := by simp

/-- The degree of `v` is the sum of the degrees into the two parts of a partition. -/
theorem degIn_univ_eq_add (G : SimpleGraph (Fin n)) (A B : Finset (Fin n))
    (hAB : Disjoint A B) (hcov : A ∪ B = Finset.univ) (v : Fin n) :
    Work.Deep.GKO.degIn G v Finset.univ
      = Work.Deep.GKO.degIn G v A + Work.Deep.GKO.degIn G v B := by
  classical
  have hmem : ∀ x : Fin n, x ∈ A ∨ x ∈ B := by
    intro x
    have h := (Finset.ext_iff.mp hcov) x
    exact (Finset.mem_union.mp (h.mpr (Finset.mem_univ x)))
  have hset : (Finset.univ.filter fun y => G.Adj v y)
      = (A.filter fun y => G.Adj v y) ∪ (B.filter fun y => G.Adj v y) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro h
      rcases hmem x with hx | hx
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
    · intro h
      exact h.elim (fun hh => hh.2) (fun hh => hh.2)
  rw [Work.Deep.GKO.degIn, Work.Deep.GKO.degIn, Work.Deep.GKO.degIn,
    Work.Deep.GKO.nbrFinset, Work.Deep.GKO.nbrFinset, Work.Deep.GKO.nbrFinset, hset,
    Finset.card_union_of_disjoint]
  rw [Finset.disjoint_left]
  intro x hx hx'
  exact Finset.disjoint_left.mp hAB (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx').1

/-- `degIn` over everything is the number of neighbours. -/
theorem degIn_univ_eq_natCard (G : SimpleGraph (Fin n)) (v : Fin n) :
    Work.Deep.GKO.degIn G v Finset.univ = Nat.card (G.neighborSet v) := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

/-! ## The vertices covered by a graph, and the cross part of a graph

`absorberHelpers.lean` in this directory contains a version of these (it does not compile:
`matching_of_le_bipRestr` there mentions undeclared variables), so they are reproduced here. -/

/-- The set of vertices incident with an edge of `M`. -/
noncomputable def vset (M : SimpleGraph (Fin n)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun v => ∃ w, M.Adj v w

theorem mem_vset {M : SimpleGraph (Fin n)} {v : Fin n} : v ∈ vset M ↔ ∃ w, M.Adj v w := by
  classical
  rw [vset, Finset.mem_filter]
  simp

theorem notMem_vset_iff {M : SimpleGraph (Fin n)} {v : Fin n} :
    v ∉ vset M ↔ ∀ w, ¬ M.Adj v w := by
  rw [mem_vset]
  exact not_exists

/-- A matching covers twice as many vertices as it has edges. -/
theorem card_vset_of_matching (M : SimpleGraph (Fin n)) (hM : Work.Deep.GKO.IsMatching' M) :
    (vset M).card = 2 * Nat.card M.edgeSet := by
  classical
  have hbU : vset M = M.edgeFinset.biUnion (fun z => z.toFinset) := by
    ext v
    rw [mem_vset, Finset.mem_biUnion]
    constructor
    · rintro ⟨w, hw⟩
      exact ⟨s(v, w), SimpleGraph.mem_edgeFinset.mpr ((SimpleGraph.mem_edgeSet M).mpr hw),
        by rw [Sym2.mem_toFinset]; exact Sym2.mem_mk_left v w⟩
    · rintro ⟨z, hz, hvz⟩
      rw [Sym2.mem_toFinset] at hvz
      obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp hvz
      exact ⟨w, (SimpleGraph.mem_edgeSet M).mp (SimpleGraph.mem_edgeFinset.mp hz)⟩
  have hdisj : (↑M.edgeFinset : Set (Sym2 (Fin n))).PairwiseDisjoint (fun z => z.toFinset) := by
    intro z hz z' hz' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro v hv hv'
    rw [Sym2.mem_toFinset] at hv hv'
    obtain ⟨w, hw⟩ := Sym2.mem_iff_exists.mp hv
    obtain ⟨w', hw'⟩ := Sym2.mem_iff_exists.mp hv'
    have hzE : z ∈ M.edgeSet := SimpleGraph.mem_edgeFinset.mp hz
    have hz'E : z' ∈ M.edgeSet := SimpleGraph.mem_edgeFinset.mp hz'
    have h1 : M.Adj v w := by rw [← (SimpleGraph.mem_edgeSet M), ← hw]; exact hzE
    have h2 : M.Adj v w' := by rw [← (SimpleGraph.mem_edgeSet M), ← hw']; exact hz'E
    have hww : w = w' := hM v w w' h1 h2
    exact hne (by rw [hw, hw', hww])
  rw [hbU, Finset.card_biUnion hdisj]
  calc ∑ z ∈ M.edgeFinset, z.toFinset.card
      = ∑ _z ∈ M.edgeFinset, 2 := by
        refine Finset.sum_congr rfl fun z hz => ?_
        rw [Sym2.card_toFinset, if_neg]
        exact SimpleGraph.not_isDiag_of_mem_edgeSet M (SimpleGraph.mem_edgeFinset.mp hz)
    _ = 2 * M.edgeFinset.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ = 2 * Nat.card M.edgeSet := by
        rw [SimpleGraph.edgeFinset_card, Nat.card_eq_fintype_card]

/-- A matching with no edge at `v` does not cover `v`. -/
theorem vset_subset_of_inside {M : SimpleGraph (Fin n)} {A : Finset (Fin n)}
    (h : ∀ u v : Fin n, M.Adj u v → u ∈ A ∧ v ∈ A) : vset M ⊆ A := by
  intro v hv
  obtain ⟨w, hw⟩ := mem_vset.mp hv
  exact (h v w hw).1

/-- If every edge of `M` joins `Aj` to `Bj` and both sides are saturated uniquely, then `M` is a
matching. -/
theorem isMatching_of_bipUnique {M : SimpleGraph (Fin n)} {A B Aj Bj : Finset (Fin n)}
    (hAB : Disjoint A B) (hAjA : Aj ⊆ A) (hBjB : Bj ⊆ B)
    (hbip : ∀ u v : Fin n, M.Adj u v → (u ∈ Aj ∧ v ∈ Bj) ∨ (u ∈ Bj ∧ v ∈ Aj))
    (hA : ∀ v : Fin n, v ∈ Aj → ∃! w : Fin n, w ∈ Bj ∧ M.Adj v w)
    (hB : ∀ v : Fin n, v ∈ Bj → ∃! w : Fin n, w ∈ Aj ∧ M.Adj v w) :
    Work.Deep.GKO.IsMatching' M := by
  have hdisj : ∀ v : Fin n, v ∈ Aj → v ∉ Bj := fun v hv hb =>
    Finset.disjoint_left.mp hAB (hAjA hv) (hBjB hb)
  intro v w w' hw hw'
  rcases hbip v w hw with ⟨hvA, hwB⟩ | ⟨hvB, hwA⟩
  · rcases hbip v w' hw' with ⟨-, hw'B⟩ | ⟨hvB', -⟩
    · exact (hA v hvA).unique ⟨hwB, hw⟩ ⟨hw'B, hw'⟩
    · exact absurd (hdisj v hvA hvB') (by simp)
  · rcases hbip v w' hw' with ⟨hvA', -⟩ | ⟨-, hw'A⟩
    · exact absurd (hdisj v hvA' hvB) (by simp)
    · exact (hB v hvB).unique ⟨hwA, hw⟩ ⟨hw'A, hw'⟩

/-- A vertex covered by a matching has a unique partner. -/
theorem existsUnique_adj_of_mem_vset {M : SimpleGraph (Fin n)} (hM : Work.Deep.GKO.IsMatching' M)
    {v : Fin n} (hv : v ∈ vset M) : ∃! w : Fin n, M.Adj v w := by
  obtain ⟨w, hw⟩ := mem_vset.mp hv
  exact ⟨w, hw, fun w' hw' => hM v w' w hw' hw⟩

/-- The subgraph of `H` consisting of the edges with one end in `A` and the other in `B`. -/
def crossRestr (H : SimpleGraph (Fin n)) (A B : Finset (Fin n)) : SimpleGraph (Fin n) :=
  H ⊓ SimpleGraph.fromEdgeSet {z : Sym2 (Fin n) | ∃ a ∈ A, ∃ b ∈ B, z = s(a, b)}

theorem crossRestr_le (H : SimpleGraph (Fin n)) (A B : Finset (Fin n)) :
    crossRestr H A B ≤ H := inf_le_left

theorem crossRestr_adj_mem {H : SimpleGraph (Fin n)} {A B : Finset (Fin n)} {u v : Fin n}
    (h : (crossRestr H A B).Adj u v) : (u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A) := by
  rw [crossRestr, SimpleGraph.inf_adj, SimpleGraph.fromEdgeSet_adj] at h
  obtain ⟨-, ⟨⟨a, ha, b, hb, hab⟩, _⟩⟩ := h
  rw [Sym2.eq_iff] at hab
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨ha, hb⟩
  · exact Or.inr ⟨hb, ha⟩

theorem crossRestr_adj_of {H : SimpleGraph (Fin n)} {A B : Finset (Fin n)} {a : Fin n}
    (ha : a ∈ A) {b : Fin n} (hb : b ∈ B) (hab : H.Adj a b) : (crossRestr H A B).Adj a b := by
  rw [crossRestr, SimpleGraph.inf_adj, SimpleGraph.fromEdgeSet_adj]
  exact ⟨hab, ⟨⟨a, ha, b, hb, rfl⟩, hab.ne⟩⟩

/-! ## Auxiliary statements

The three `..._tmp` declarations below are placeholders for the lemmas delegated to
`Work.Deep.GKO.Abs.{insideDecomp,hallBip,oneFactorOfMatchingFamily}`; they are replaced by the
imported results once those land. -/

/-- The two parts of an edge-disjoint decomposition are edge-disjoint. -/
theorem disjoint_sdiff_self (G U : SimpleGraph (Fin n)) : Disjoint (G \ U).edgeSet U.edgeSet := by
  rw [SimpleGraph.disjoint_edgeSet (G₁ := G \ U) (G₂ := U), SimpleGraph.disjoint_left]
  intro a b h hab
  exact ((SimpleGraph.sdiff_adj G U a b).mp h).2 hab

/-! ## The invariant of the absorbing induction -/

/-- The state after `m` steps of the absorbing construction: the already built matchings `P i`
(for `i.val < m`) are perfect matchings between `A \ vset (N i)` and `B \ vset (N i)`, they are
pairwise edge-disjoint and live in `Hx`, and `P` is `⊥` on the untouched indices. -/
private structure AbsSt {n : ℕ} (A B : Finset (Fin n)) (Hx : SimpleGraph (Fin n)) {t : ℕ}
    (N : Fin t → SimpleGraph (Fin n)) (m : ℕ) (P : Fin t → SimpleGraph (Fin n)) : Prop where
  le_hx : ∀ i : Fin t, i.val < m → P i ≤ Hx
  bip : ∀ i : Fin t, i.val < m → ∀ u v : Fin n, (P i).Adj u v →
    (u ∈ A \ vset (N i) ∧ v ∈ B \ vset (N i)) ∨ (u ∈ B \ vset (N i) ∧ v ∈ A \ vset (N i))
  satA : ∀ i : Fin t, i.val < m → ∀ v : Fin n, v ∈ A \ vset (N i) →
    ∃! w : Fin n, w ∈ B \ vset (N i) ∧ (P i).Adj v w
  satB : ∀ i : Fin t, i.val < m → ∀ v : Fin n, v ∈ B \ vset (N i) →
    ∃! w : Fin n, w ∈ A \ vset (N i) ∧ (P i).Adj v w
  disj : ∀ i i' : Fin t, i ≠ i' → i.val < m → i'.val < m →
    Disjoint (P i).edgeSet (P i').edgeSet
  bot : ∀ i : Fin t, m ≤ i.val → P i = ⊥

/-- The number of neighbours is monotone in the graph. -/
theorem natCard_neighborSet_mono {G G' : SimpleGraph (Fin n)} (h : G ≤ G') (v : Fin n) :
    Nat.card (G.neighborSet v) ≤ Nat.card (G'.neighborSet v) := by
  rw [← degIn_univ_eq_natCard G v, ← degIn_univ_eq_natCard G' v]
  rw [Work.Deep.GKO.degIn_eq_ncard, Work.Deep.GKO.degIn_eq_ncard]
  refine Set.ncard_le_ncard fun y hy => ?_
  simp only [Set.mem_inter_iff, SimpleGraph.mem_neighborSet] at hy ⊢
  exact ⟨h hy.1, hy.2⟩

/-! ## Degree and edge-count bounds for unions of graphs -/

/-- The degree of a vertex in a supremum of graphs is bounded by the sum of the degrees. -/
theorem degIn_iSup_le {ι : Type*} [Fintype ι] (P : ι → SimpleGraph (Fin n)) (x : Fin n)
    (S : Finset (Fin n)) :
    Work.Deep.GKO.degIn (⨆ i, P i) x S ≤ ∑ i, Work.Deep.GKO.degIn (P i) x S := by
  classical
  simp only [Work.Deep.GKO.degIn, Work.Deep.GKO.nbrFinset]
  have h1 : S.filter (fun y => (⨆ i, P i).Adj x y)
      ⊆ Finset.univ.biUnion (fun i => S.filter (fun y => (P i).Adj x y)) := by
    intro y hy
    rw [Finset.mem_filter] at hy
    obtain ⟨hys, hy2⟩ := hy
    rw [SimpleGraph.iSup_adj] at hy2
    obtain ⟨i, hi⟩ := hy2
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, Finset.mem_filter.mpr ⟨hys, hi⟩⟩
  calc (S.filter (fun y => (⨆ i, P i).Adj x y)).card
      ≤ (Finset.univ.biUnion (fun i => S.filter (fun y => (P i).Adj x y))).card :=
        Finset.card_le_card h1
    _ ≤ ∑ i, (S.filter (fun y => (P i).Adj x y)).card := Finset.card_biUnion_le

/-- The edge count between two sets in a supremum of graphs is bounded by the sum. -/
theorem crossEdges_iSup_le {ι : Type*} [Fintype ι] (P : ι → SimpleGraph (Fin n))
    (A B : Finset (Fin n)) :
    Work.Deep.GKO.crossEdges (⨆ i, P i) A B ≤ ∑ i, Work.Deep.GKO.crossEdges (P i) A B := by
  classical
  unfold Work.Deep.GKO.crossEdges
  have h1 : (A.product B).filter (fun p => (⨆ i, P i).Adj p.1 p.2)
      ⊆ Finset.univ.biUnion (fun i => (A.product B).filter (fun p => (P i).Adj p.1 p.2)) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨hp1, hp2⟩ := hp
    rw [SimpleGraph.iSup_adj] at hp2
    obtain ⟨i, hi⟩ := hp2
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, Finset.mem_filter.mpr ⟨hp1, hi⟩⟩
  calc ((A.product B).filter (fun p => (⨆ i, P i).Adj p.1 p.2)).card
      ≤ (Finset.univ.biUnion (fun i => (A.product B).filter
          (fun p => (P i).Adj p.1 p.2))).card := Finset.card_le_card h1
    _ ≤ ∑ i, ((A.product B).filter (fun p => (P i).Adj p.1 p.2)).card :=
        Finset.card_biUnion_le

/-- The degree into a superset is bounded by the degree into `S` plus the difference. -/
theorem degIn_le_degIn_subset_add_card_sdiff (G : SimpleGraph (Fin n)) (x : Fin n)
    {S T : Finset (Fin n)} (h : S ⊆ T) :
    Work.Deep.GKO.degIn G x T ≤ Work.Deep.GKO.degIn G x S + (T \ S).card := by
  classical
  have h3 : T.filter (fun y => G.Adj x y) ⊆ S.filter (fun y => G.Adj x y) ∪ (T \ S) := by
    intro y hy
    rw [Finset.mem_filter] at hy
    by_cases hyS : y ∈ S
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hyS, hy.2⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hy.1, hyS⟩)
  simp only [Work.Deep.GKO.degIn, Work.Deep.GKO.nbrFinset]
  exact le_trans (Finset.card_le_card h3) (Finset.card_union_le _ _)

/-- The degree into `S` is bounded by the degree into a superset plus the difference. -/
theorem degIn_le_degIn_add_card_sdiff (G : SimpleGraph (Fin n)) (x : Fin n) {S T : Finset (Fin n)}
    (h : S ⊆ T) : Work.Deep.GKO.degIn G x S ≤ Work.Deep.GKO.degIn G x T + (T \ S).card := by
  classical
  have h3 : T.filter (fun y => G.Adj x y) ⊆ S.filter (fun y => G.Adj x y) ∪ (T \ S) := by
    intro y hy
    rw [Finset.mem_filter] at hy
    by_cases hyS : y ∈ S
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hyS, hy.2⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hy.1, hyS⟩)
  have h5 : S.filter (fun y => G.Adj x y) ⊆ T.filter (fun y => G.Adj x y) ∪ (T \ S) := by
    intro y hy
    rw [Finset.mem_filter] at hy
    exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨h hy.1, hy.2⟩)
  simp only [Work.Deep.GKO.degIn, Work.Deep.GKO.nbrFinset]
  calc (S.filter (fun y => G.Adj x y)).card
      ≤ (T.filter (fun y => G.Adj x y) ∪ (T \ S)).card := Finset.card_le_card h5
    _ ≤ (T.filter (fun y => G.Adj x y)).card + (T \ S).card := Finset.card_union_le _ _

/-- The degree in a graph is at most the sum of the degrees in an edge-disjoint decomposition
`G = (G \ U) ⊔ U`. -/
theorem degIn_le_sdiff_add (G U : SimpleGraph (Fin n)) (hU : U ≤ G) (x : Fin n)
    (S : Finset (Fin n)) :
    Work.Deep.GKO.degIn G x S
      ≤ Work.Deep.GKO.degIn (G \ U) x S + Work.Deep.GKO.degIn U x S := by
  rw [Work.Deep.GKO.degIn_eq_ncard, Work.Deep.GKO.degIn_eq_ncard, Work.Deep.GKO.degIn_eq_ncard]
  refine le_trans (Set.ncard_le_ncard ?_) (Set.ncard_union_le _ _)
  intro y hy
  simp only [Set.mem_inter_iff, SimpleGraph.mem_neighborSet, SimpleGraph.sdiff_adj,
    Set.mem_union] at hy ⊢
  tauto

/-- The edge count of a graph is at most the sum of the edge counts of an edge-disjoint
decomposition `G = (G \ U) ⊔ U`. -/
theorem crossEdges_le_sdiff_add (G U : SimpleGraph (Fin n)) (hU : U ≤ G) (A B : Finset (Fin n)) :
    Work.Deep.GKO.crossEdges G A B
      ≤ Work.Deep.GKO.crossEdges (G \ U) A B + Work.Deep.GKO.crossEdges U A B := by
  rw [crossEdges_eq_sum_degIn, crossEdges_eq_sum_degIn, crossEdges_eq_sum_degIn,
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun a _ => degIn_le_sdiff_add G U hU a B

/-- **The absorbing family.**  From the classes `N j` (matchings inside `A` or inside `B`, of size
`≤ 2 s` and balanced between the two sides) we build, one at a time, matchings `P j` in `Hx`
joining `A \ vset (N j)` to `B \ vset (N j)` perfectly; Hall's condition at step `j` is the
delegated `hallBip`. -/
private theorem absorbFamily {n : ℕ} {A B : Finset (Fin n)} (hAB : Disjoint A B)
    (hcov : A ∪ B = Finset.univ) (hcard : A.card = B.card)
    {Hx : SimpleGraph (Fin n)}
    (hHxbip : ∀ u v : Fin n, Hx.Adj u v → (u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A))
    {q ε : ℝ} (hε : 0 < ε)
    (hlr : ∀ S : Finset (Fin n), S ⊆ A → ∀ T : Finset (Fin n), T ⊆ B →
      ε * (n : ℝ) ≤ (S.card : ℝ) → ε * (n : ℝ) ≤ (T.card : ℝ) →
      q * (S.card : ℝ) * (T.card : ℝ) ≤ (Work.Deep.GKO.crossEdges Hx S T : ℝ))
    {t s : ℕ} (hts : t ≤ s) (hroomq : (s : ℝ) < q * ε * (n : ℝ))
    (hdegHx : ∀ v : Fin n, ε * (n : ℝ) + 3 * (s : ℝ) ≤ (Nat.card (Hx.neighborSet v) : ℝ))
    (N : Fin t → SimpleGraph (Fin n))
    (hNm : ∀ j, Work.Deep.GKO.IsMatching' (N j))
    (hNin : ∀ j, ∀ u v : Fin n, (N j).Adj u v → (u ∈ A ∧ v ∈ A) ∨ (u ∈ B ∧ v ∈ B))
    (hNbal : ∀ j, (A ∩ vset (N j)).card = (B ∩ vset (N j)).card)
    (hNsmall : ∀ j, (A ∩ vset (N j)).card ≤ 2 * s) :
    ∃ P : Fin t → SimpleGraph (Fin n),
      (∀ j, P j ≤ Hx) ∧
      (∀ j, ∀ u v : Fin n, (P j).Adj u v →
        (u ∈ A \ vset (N j) ∧ v ∈ B \ vset (N j)) ∨ (u ∈ B \ vset (N j) ∧ v ∈ A \ vset (N j))) ∧
      (∀ j, ∀ v : Fin n, v ∈ A \ vset (N j) →
        ∃! w : Fin n, w ∈ B \ vset (N j) ∧ (P j).Adj v w) ∧
      (∀ j, ∀ v : Fin n, v ∈ B \ vset (N j) →
        ∃! w : Fin n, w ∈ A \ vset (N j) ∧ (P j).Adj v w) ∧
      (∀ i j : Fin t, i ≠ j → Disjoint (P i).edgeSet (P j).edgeSet) := by
  classical
  have hmain : ∀ m ≤ t, ∃ P : Fin t → SimpleGraph (Fin n), AbsSt A B Hx N m P := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨fun _ => ⊥, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i hi; exact absurd hi (Nat.not_lt_zero i.val)
      · intro i hi; exact absurd hi (Nat.not_lt_zero i.val)
      · intro i hi; exact absurd hi (Nat.not_lt_zero i.val)
      · intro i hi; exact absurd hi (Nat.not_lt_zero i.val)
      · intro i i' _ hi; exact absurd hi (Nat.not_lt_zero i.val)
      · intro i _; rfl
    | succ m ih =>
      intro hm
      obtain ⟨P, hP⟩ := ih (Nat.le_of_succ_le hm)
      have hmt : m < t := hm
      have hmt_le : m ≤ t := le_of_lt hmt
      set j : Fin t := ⟨m, hmt⟩ with hj
      have hjval : j.val = m := rfl
      -- the matchings built so far are matchings
      have hpM : ∀ i : Fin t, i.val < m → Work.Deep.GKO.IsMatching' (P i) := fun i hi =>
        isMatching_of_bipUnique hAB Finset.sdiff_subset Finset.sdiff_subset
          (hP.bip i hi) (hP.satA i hi) (hP.satB i hi)
      -- the graph of the already used edges
      set U : SimpleGraph (Fin n) := ⨆ i : Fin m, P (Fin.castLE hmt_le i) with hU
      have hP_le_U : ∀ i : Fin t, i.val < m → P i ≤ U := by
        intro i hi
        have h2 := le_iSup (fun i' : Fin m => P (Fin.castLE hmt_le i')) ⟨i.val, hi⟩
        have h3 : Fin.castLE hmt_le ⟨i.val, hi⟩ = i := Fin.ext rfl
        rw [h3] at h2
        rwa [hU]
      have hU_le_Hx : U ≤ Hx := by
        rw [hU]
        refine iSup_le fun i' => ?_
        exact hP.le_hx (Fin.castLE hmt_le i') (by simpa using i'.isLt)
      have hpM' : ∀ i' : Fin m, Work.Deep.GKO.IsMatching' (P (Fin.castLE hmt_le i')) :=
        fun i' => hpM _ (by simpa using i'.isLt)
      have hdegU : ∀ x : Fin n, Work.Deep.GKO.degIn U x Finset.univ ≤ m := by
        intro x
        have h1 : Work.Deep.GKO.degIn (⨆ i : Fin m, P (Fin.castLE hmt_le i)) x Finset.univ
            ≤ ∑ i : Fin m, Work.Deep.GKO.degIn (P (Fin.castLE hmt_le i)) x Finset.univ :=
          degIn_iSup_le _ x _
        rw [hU]
        calc Work.Deep.GKO.degIn (⨆ i : Fin m, P (Fin.castLE hmt_le i)) x Finset.univ
            ≤ ∑ i : Fin m, Work.Deep.GKO.degIn (P (Fin.castLE hmt_le i)) x Finset.univ := h1
          _ ≤ ∑ _i : Fin m, 1 := Finset.sum_le_sum fun i _ => degIn_le_one_of_matching (hpM' i) x _
          _ = m := by simp
      have hcrossU : ∀ S T : Finset (Fin n),
          Work.Deep.GKO.crossEdges U S T ≤ m * min S.card T.card := by
        intro S T
        have h1 : Work.Deep.GKO.crossEdges (⨆ i : Fin m, P (Fin.castLE hmt_le i)) S T
            ≤ ∑ i : Fin m, Work.Deep.GKO.crossEdges (P (Fin.castLE hmt_le i)) S T :=
          crossEdges_iSup_le _ S T
        rw [hU]
        calc Work.Deep.GKO.crossEdges (⨆ i : Fin m, P (Fin.castLE hmt_le i)) S T
            ≤ ∑ i : Fin m, Work.Deep.GKO.crossEdges (P (Fin.castLE hmt_le i)) S T := h1
          _ ≤ ∑ _i : Fin m, min S.card T.card :=
              Finset.sum_le_sum fun i _ => crossEdges_le_min_of_matching (hpM' i) S T
          _ = m * min S.card T.card := by simp
      have hKle : Hx \ U ≤ Hx := sdiff_le
      -- the Hall input
      have hrem : ∀ S : Finset (Fin n), S ⊆ A \ vset (N j) → ∀ T : Finset (Fin n),
          T ⊆ B \ vset (N j) →
          (Work.Deep.GKO.crossEdges Hx S T : ℝ) ≤ (Work.Deep.GKO.crossEdges (Hx \ U) S T : ℝ)
            + (m : ℝ) * min (S.card : ℝ) (T.card : ℝ) := by
        intro S _ T _
        have h1 : Work.Deep.GKO.crossEdges Hx S T
            ≤ Work.Deep.GKO.crossEdges (Hx \ U) S T + Work.Deep.GKO.crossEdges U S T :=
          crossEdges_le_sdiff_add Hx U hU_le_Hx S T
        have h2 : Work.Deep.GKO.crossEdges U S T ≤ m * min S.card T.card := hcrossU S T
        have h3 : (Work.Deep.GKO.crossEdges Hx S T : ℝ)
            ≤ (Work.Deep.GKO.crossEdges (Hx \ U) S T : ℝ)
              + ((m * min S.card T.card : ℕ) : ℝ) := by
          exact_mod_cast le_trans h1 (Nat.add_le_add_left h2 _)
        calc (Work.Deep.GKO.crossEdges Hx S T : ℝ)
            ≤ (Work.Deep.GKO.crossEdges (Hx \ U) S T : ℝ)
              + ((m * min S.card T.card : ℕ) : ℝ) := h3
          _ = (Work.Deep.GKO.crossEdges (Hx \ U) S T : ℝ)
              + (m : ℝ) * min (S.card : ℝ) (T.card : ℝ) := by
              push_cast [Nat.cast_min]; ring
      have hcardj : (A \ vset (N j)).card = (B \ vset (N j)).card := by
        have h1 : (vset (N j) ∩ A).card = (A ∩ vset (N j)).card := by rw [Finset.inter_comm]
        have h2 : (vset (N j) ∩ B).card = (B ∩ vset (N j)).card := by rw [Finset.inter_comm]
        rw [Finset.card_sdiff, Finset.card_sdiff, h1, h2, hcard, hNbal j]
      have hroomq' : (m : ℝ) < q * ε * (n : ℝ) := by
        have h1 : (m : ℝ) < (s : ℝ) := by
          have : m < s := by omega
          exact_mod_cast this
        linarith [hroomq]
      -- the degree hypotheses
      have hdegA' : ∀ v : Fin n, v ∈ A \ vset (N j) →
          ε * (n : ℝ) ≤ (Work.Deep.GKO.degIn (Hx \ U) v (B \ vset (N j)) : ℝ) := by
        intro v hv
        have hvA : v ∈ A := (Finset.mem_sdiff.mp hv).1
        have h1 : Work.Deep.GKO.degIn Hx v Finset.univ
            ≤ Work.Deep.GKO.degIn (Hx \ U) v Finset.univ
              + Work.Deep.GKO.degIn U v Finset.univ :=
          degIn_le_sdiff_add Hx U hU_le_Hx v Finset.univ
        have h2 : Work.Deep.GKO.degIn Hx v Finset.univ = Nat.card (Hx.neighborSet v) :=
          degIn_univ_eq_natCard Hx v
        have h4 : Work.Deep.GKO.degIn (Hx \ U) v Finset.univ
            ≤ Work.Deep.GKO.degIn (Hx \ U) v B := by
          rw [Work.Deep.GKO.degIn_eq_ncard, Work.Deep.GKO.degIn_eq_ncard]
          refine Set.ncard_le_ncard fun y hy => ?_
          simp only [Set.mem_inter_iff, SimpleGraph.mem_neighborSet] at hy ⊢
          obtain ⟨hyadj, -⟩ := hy
          have hxy : Hx.Adj v y := ((SimpleGraph.sdiff_adj Hx U v y).mp hyadj).1
          rcases hHxbip v y hxy with ⟨-, hyB⟩ | ⟨hvB, -⟩
          · exact ⟨hyadj, hyB⟩
          · exact absurd hvB (Finset.disjoint_left.mp hAB hvA)
        have h5 : Work.Deep.GKO.degIn (Hx \ U) v B
            ≤ Work.Deep.GKO.degIn (Hx \ U) v (B \ vset (N j))
              + (B \ (B \ vset (N j))).card :=
          degIn_le_degIn_subset_add_card_sdiff (Hx \ U) v Finset.sdiff_subset
        have h6 : B \ (B \ vset (N j)) = B ∩ vset (N j) := sdiff_sdiff_right_self
        have h7 : (B ∩ vset (N j)).card = (A ∩ vset (N j)).card := (hNbal j).symm
        have h8 : (A ∩ vset (N j)).card ≤ 2 * s := hNsmall j
        have hm1 : m + 1 ≤ s := by omega
        -- assemble in ℝ
        have h10 : (Nat.card (Hx.neighborSet v) : ℝ) ≤
            (Work.Deep.GKO.degIn (Hx \ U) v (B \ vset (N j)) : ℝ)
              + ((B \ (B \ vset (N j))).card : ℝ)
              + (Work.Deep.GKO.degIn U v Finset.univ : ℝ) := by
          have h11 : (Work.Deep.GKO.degIn (Hx \ U) v Finset.univ : ℝ)
              ≤ (Work.Deep.GKO.degIn (Hx \ U) v (B \ vset (N j)) : ℝ)
                + ((B \ (B \ vset (N j))).card : ℝ) := by
            exact_mod_cast le_trans h4 h5
          have h12 : (Work.Deep.GKO.degIn Hx v Finset.univ : ℝ)
              ≤ (Work.Deep.GKO.degIn (Hx \ U) v Finset.univ : ℝ)
                + (Work.Deep.GKO.degIn U v Finset.univ : ℝ) := by
            exact_mod_cast h1
          have h13 : (Nat.card (Hx.neighborSet v) : ℝ)
              = (Work.Deep.GKO.degIn Hx v Finset.univ : ℝ) := by rw [h2]
          rw [h13]
          linarith
        have h14 : ((B \ (B \ vset (N j))).card : ℝ) ≤ 2 * (s : ℝ) := by
          rw [h6, h7]; exact_mod_cast h8
        have h15 : (Work.Deep.GKO.degIn U v Finset.univ : ℝ) ≤ (m : ℝ) := by
          exact_mod_cast hdegU v
        have h16 : ε * (n : ℝ) + 3 * (s : ℝ) ≤ (Nat.card (Hx.neighborSet v) : ℝ) := hdegHx v
        have h17 : (m : ℝ) + ((B \ (B \ vset (N j))).card : ℝ) ≤ 3 * (s : ℝ) - 1 := by
          have h18 : (m : ℝ) + 1 ≤ (s : ℝ) := by exact_mod_cast hm1
          linarith
        linarith [h10, h14, h15, h16, h17]
      have hdegB' : ∀ v : Fin n, v ∈ B \ vset (N j) →
          ε * (n : ℝ) ≤ (Work.Deep.GKO.degIn (Hx \ U) v (A \ vset (N j)) : ℝ) := by
        intro v hv
        have hvB : v ∈ B := (Finset.mem_sdiff.mp hv).1
        have h1 : Work.Deep.GKO.degIn Hx v Finset.univ
            ≤ Work.Deep.GKO.degIn (Hx \ U) v Finset.univ
              + Work.Deep.GKO.degIn U v Finset.univ :=
          degIn_le_sdiff_add Hx U hU_le_Hx v Finset.univ
        have h2 : Work.Deep.GKO.degIn Hx v Finset.univ = Nat.card (Hx.neighborSet v) :=
          degIn_univ_eq_natCard Hx v
        have h4 : Work.Deep.GKO.degIn (Hx \ U) v Finset.univ
            ≤ Work.Deep.GKO.degIn (Hx \ U) v A := by
          rw [Work.Deep.GKO.degIn_eq_ncard, Work.Deep.GKO.degIn_eq_ncard]
          refine Set.ncard_le_ncard fun y hy => ?_
          simp only [Set.mem_inter_iff, SimpleGraph.mem_neighborSet] at hy ⊢
          obtain ⟨hyadj, -⟩ := hy
          have hxy : Hx.Adj v y := ((SimpleGraph.sdiff_adj Hx U v y).mp hyadj).1
          rcases hHxbip v y hxy with ⟨hvA, -⟩ | ⟨-, hyA⟩
          · exact absurd hvB (Finset.disjoint_left.mp hAB hvA)
          · exact ⟨hyadj, hyA⟩
        have h5 : Work.Deep.GKO.degIn (Hx \ U) v A
            ≤ Work.Deep.GKO.degIn (Hx \ U) v (A \ vset (N j))
              + (A \ (A \ vset (N j))).card :=
          degIn_le_degIn_subset_add_card_sdiff (Hx \ U) v Finset.sdiff_subset
        have h6 : A \ (A \ vset (N j)) = A ∩ vset (N j) := sdiff_sdiff_right_self
        have h8 : (A ∩ vset (N j)).card ≤ 2 * s := hNsmall j
        have hm1 : m + 1 ≤ s := by omega
        have h10 : (Nat.card (Hx.neighborSet v) : ℝ) ≤
            (Work.Deep.GKO.degIn (Hx \ U) v (A \ vset (N j)) : ℝ)
              + ((A \ (A \ vset (N j))).card : ℝ)
              + (Work.Deep.GKO.degIn U v Finset.univ : ℝ) := by
          have h11 : (Work.Deep.GKO.degIn (Hx \ U) v Finset.univ : ℝ)
              ≤ (Work.Deep.GKO.degIn (Hx \ U) v (A \ vset (N j)) : ℝ)
                + ((A \ (A \ vset (N j))).card : ℝ) := by
            exact_mod_cast le_trans h4 h5
          have h12 : (Work.Deep.GKO.degIn Hx v Finset.univ : ℝ)
              ≤ (Work.Deep.GKO.degIn (Hx \ U) v Finset.univ : ℝ)
                + (Work.Deep.GKO.degIn U v Finset.univ : ℝ) := by
            exact_mod_cast h1
          have h13 : (Nat.card (Hx.neighborSet v) : ℝ)
              = (Work.Deep.GKO.degIn Hx v Finset.univ : ℝ) := by rw [h2]
          rw [h13]
          linarith
        have h14 : ((A \ (A \ vset (N j))).card : ℝ) ≤ 2 * (s : ℝ) := by
          rw [h6]; exact_mod_cast h8
        have h15 : (Work.Deep.GKO.degIn U v Finset.univ : ℝ) ≤ (m : ℝ) := by
          exact_mod_cast hdegU v
        have h16 : ε * (n : ℝ) + 3 * (s : ℝ) ≤ (Nat.card (Hx.neighborSet v) : ℝ) := hdegHx v
        have h17 : (m : ℝ) + ((A \ (A \ vset (N j))).card : ℝ) ≤ 3 * (s : ℝ) - 1 := by
          have h18 : (m : ℝ) + 1 ≤ (s : ℝ) := by exact_mod_cast hm1
          linarith
        linarith [h10, h14, h15, h16, h17]
      -- Hall's condition
      obtain ⟨Pnew, hPnewle, hPnewbip, hPnewA, hPnewB⟩ :=
        Work.Deep.GKO.Abs.hallBipClean (A := A) (B := B) (Aj := A \ vset (N j)) (Bj := B \ vset (N j))
          hAB Finset.sdiff_subset Finset.sdiff_subset hcardj hlr hKle hrem hdegA' hdegB'
          hε hroomq'
      -- the extended family
      refine ⟨Function.update P j Pnew, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- `le_hx`
        intro i hi
        rcases eq_or_ne i j with rfl | hne
        · rw [Function.update_self]
          exact le_trans hPnewle hKle
        · rw [Function.update_of_ne hne]
          exact hP.le_hx i (by omega)
      · -- bipartite
        intro i hi u v huv
        rcases eq_or_ne i j with rfl | hne
        · rw [Function.update_self] at huv
          exact hPnewbip u v huv
        · rw [Function.update_of_ne hne] at huv
          exact hP.bip i (by omega) u v huv
      · -- saturation of the `A`-side
        intro i hi v hv
        rcases eq_or_ne i j with rfl | hne
        · rw [Function.update_self]
          exact hPnewA v hv
        · rw [Function.update_of_ne hne]
          exact hP.satA i (by omega) v hv
      · -- saturation of the `B`-side
        intro i hi v hv
        rcases eq_or_ne i j with rfl | hne
        · rw [Function.update_self]
          exact hPnewB v hv
        · rw [Function.update_of_ne hne]
          exact hP.satB i (by omega) v hv
      · -- pairwise disjointness
        intro i i' hne hi hi'
        rcases eq_or_ne i j with rfl | hi_ne
        · -- `i` is the new index
          rcases eq_or_ne i' j with rfl | hi'_ne
          · exact False.elim (absurd rfl hne)
          · have hi'_m : i'.val < m := by omega
            rw [Function.update_self, Function.update_of_ne hi'_ne]
            exact Disjoint.mono (SimpleGraph.edgeSet_mono hPnewle)
              (SimpleGraph.edgeSet_mono (hP_le_U i' hi'_m)) (disjoint_sdiff_self Hx U)
        · have hi_m : i.val < m := by omega
          rcases eq_or_ne i' j with rfl | hi'_ne
          · rw [Function.update_of_ne hi_ne, Function.update_self]
            exact Disjoint.mono (SimpleGraph.edgeSet_mono (hP_le_U i hi_m))
              (SimpleGraph.edgeSet_mono hPnewle) (Disjoint.symm (disjoint_sdiff_self Hx U))
          · have hi'_m : i'.val < m := by omega
            rw [Function.update_of_ne hi_ne, Function.update_of_ne hi'_ne]
            exact hP.disj i i' hne hi_m hi'_m
      · -- the untouched indices
        intro i hi
        have hne : i ≠ j := by
          intro h
          rw [h] at hi
          exact absurd hi (by simp [hjval])
        rw [Function.update_of_ne hne]
        exact hP.bot i (by omega)
  obtain ⟨P, hP⟩ := hmain t le_rfl
  exact ⟨P, fun i => hP.le_hx i i.isLt, fun i => hP.bip i i.isLt, fun i => hP.satA i i.isLt,
    fun i => hP.satB i i.isLt, fun i j hij => hP.disj i j hij i.isLt j.isLt⟩

/-- `2 ⌊s/4⌋ ≤ ⌊s/2⌋`. -/
private lemma two_mul_div4_le_div2 (s : ℕ) : 2 * (s / 4) ≤ s / 2 := by
  rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
  have h5 : 4 * (s / 4) ≤ s := by
    have h6 := Nat.div_mul_le_self s 4
    omega
  omega

/-- `s/2 + s/2 ≤ s`. -/
private lemma half_add_half_le (s : ℕ) : s / 2 + s / 2 ≤ s := by omega

/-- `2 ⌊s/4⌋ + ⌊X/2⌋ + 2 ≤ s` when `s = X + 3`. -/
private lemma num_arith (X s : ℕ) (hs : s = X + 3) : 2 * (s / 4) + X / 2 + 2 ≤ s := by
  rw [hs]
  omega

theorem matchingAbsorber {n : ℕ} (hn : Even n) (A B : Finset (Fin n)) (hAB : Disjoint A B)
    (hcov : A ∪ B = Finset.univ) (hcard : A.card = B.card)
    (H H₀ : SimpleGraph (Fin n)) (hdisj : Disjoint H.edgeSet H₀.edgeSet)
    (hbip : ∀ u v : Fin n, H.Adj u v → (u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A))
    {D d₀ k : ℕ} {q ε : ℝ}
    (hq : 0 < q) (hε : 0 < ε)
    (hmin : ∀ v : Fin n, D ≤ Nat.card (H.neighborSet v))
    (hlr : Work.Deep.GKO.BipLowerReg H A B q ε)
    (hΔ0 : ∀ v : Fin n, Nat.card (H₀.neighborSet v) ≤ d₀)
    (hreg : Work.Deep.GKO.IsRegularOf (H ⊔ H₀) k)
    (hroom1 : 8 * (Nat.sqrt (d₀ * n) + 3) ≤ D)
    (hroom2 : 2 * ε * (n : ℝ) ≤ (D : ℝ))
    (hroom3 : ((Nat.sqrt (d₀ * n) + 3 : ℕ) : ℝ) < q * ε * (n : ℝ)) :
    Work.Deep.GKO.HasOneFactorization (H ⊔ H₀) k := by
  classical
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    refine ⟨fun _ => ⊥, fun i => ⟨bot_le, fun v => Fin.elim0 v⟩, fun i j _ => ?_,
      fun e he => ?_⟩
    · rw [SimpleGraph.edgeSet_bot]
      simp
    · induction e using Sym2.ind with
      | h u v => exact Fin.elim0 u
  -- basic cardinalities
  have h2A : 2 * A.card = n := by
    have h := Finset.card_union_of_disjoint hAB
    rw [hcov, Finset.card_univ, Fintype.card_fin] at h
    omega
  have h2B : 2 * B.card = n := by omega
  have hApos : 0 < A.card := by omega
  have hmemAB : ∀ x : Fin n, x ∈ A ∨ x ∈ B := by
    intro x
    have h := (Finset.ext_iff.mp hcov) x
    exact Finset.mem_union.mp (h.mpr (Finset.mem_univ x))
  -- the cross part of `H₀`, and the graph `Hx` of all cross edges
  set Hx : SimpleGraph (Fin n) := H ⊔ crossRestr H₀ A B with hHx
  have hH_le_Hx : H ≤ Hx := le_sup_left
  have hHxbip : ∀ u v : Fin n, Hx.Adj u v → (u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A) := by
    intro u v huv
    rw [hHx, SimpleGraph.sup_adj] at huv
    rcases huv with h | h
    · exact hbip u v h
    · exact crossRestr_adj_mem h
  have hlrHx : ∀ S : Finset (Fin n), S ⊆ A → ∀ T : Finset (Fin n), T ⊆ B →
      ε * (n : ℝ) ≤ (S.card : ℝ) → ε * (n : ℝ) ≤ (T.card : ℝ) →
      q * (S.card : ℝ) * (T.card : ℝ) ≤ (Work.Deep.GKO.crossEdges Hx S T : ℝ) := by
    intro S hS T hT h1 h2
    refine le_trans (hlr S hS T hT h1 h2) ?_
    exact_mod_cast crossEdges_mono hH_le_Hx S T
  -- numerical parameters
  set X : ℕ := Nat.sqrt (d₀ * n) with hX
  set s : ℕ := X + 3 with hs
  have hs3 : 3 ≤ s := by omega
  have hD_half : D ≤ n / 2 := by
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hApos
    have h1 : D ≤ Nat.card (H.neighborSet v) := hmin v
    have h2 : Nat.card (H.neighborSet v) ≤ Work.Deep.GKO.degIn H v B := by
      rw [← degIn_univ_eq_natCard H v, Work.Deep.GKO.degIn_eq_ncard, Work.Deep.GKO.degIn_eq_ncard]
      refine Set.ncard_le_ncard fun y hy => ?_
      simp only [Set.mem_inter_iff, SimpleGraph.mem_neighborSet] at hy ⊢
      obtain ⟨hyadj, -⟩ := hy
      rcases hbip v y hyadj with ⟨-, hyB⟩ | ⟨hvB, -⟩
      · exact ⟨hyadj, hyB⟩
      · exact absurd hvB (Finset.disjoint_left.mp hAB hv)
    have h3 : Work.Deep.GKO.degIn H v B ≤ B.card := Work.Deep.GKO.degIn_le_card H v B
    omega
  have hX16 : X + 3 ≤ n / 16 := by
    have h1 : 8 * (X + 3) ≤ D := hroom1
    have h2 : 16 * (X + 3) ≤ n := by omega
    omega
  have hsq : d₀ * n < (X + 1) * (X + 1) := by
    rw [hX]
    simpa [Nat.succ_eq_add_one, pow_two] using Nat.lt_succ_sqrt' (d₀ * n)
  have h16d0 : 16 * d₀ ≤ n := by
    have h1 : X + 1 ≤ n / 16 := by omega
    have h2 : (X + 1) * (X + 1) ≤ (n / 16) * (n / 16) := Nat.mul_le_mul h1 h1
    have h3 : d₀ * n < (n / 16) * (n / 16) := lt_of_lt_of_le hsq h2
    have h4 : (n / 16) * (n / 16) * 256 ≤ n * n := by
      have h5 : 16 * (n / 16) ≤ n := by omega
      nlinarith [h5, Nat.zero_le (n / 16), Nat.zero_le n]
    have h6 : d₀ * n * 256 < n * n := by nlinarith [h3, h4]
    have h7 : (d₀ * 256) * n < n * n := by nlinarith [h6]
    have h8 : d₀ * 256 < n := by
      by_contra hcon
      have h9 : n * n ≤ (d₀ * 256) * n := Nat.mul_le_mul_right n (by omega)
      omega
    omega
  have hd0 : 4 * d₀ ≤ X := by
    rw [hX]
    refine Nat.le_sqrt'.mpr ?_
    nlinarith [h16d0]
  -- the inside edge counts agree
  have hinsideA : (∑ v ∈ A, Work.Deep.GKO.degIn (H ⊔ H₀) v A)
      = ∑ v ∈ A, Work.Deep.GKO.degIn H₀ v A := by
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [Work.Deep.GKO.degIn_eq_ncard, Work.Deep.GKO.degIn_eq_ncard]
    congr 1
    ext y
    simp only [Set.mem_inter_iff, SimpleGraph.mem_neighborSet, SimpleGraph.sup_adj]
    constructor
    · rintro ⟨h | h, hy⟩
      · exfalso
        rcases hbip v y h with ⟨-, hyB⟩ | ⟨hvB, -⟩
        · exact Finset.disjoint_left.mp hAB hy hyB
        · exact Finset.disjoint_left.mp hAB hv hvB
      · exact ⟨h, hy⟩
    · rintro ⟨h, hy⟩
      exact ⟨Or.inr h, hy⟩
  have hinsideB : (∑ v ∈ B, Work.Deep.GKO.degIn (H ⊔ H₀) v B)
      = ∑ v ∈ B, Work.Deep.GKO.degIn H₀ v B := by
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [Work.Deep.GKO.degIn_eq_ncard, Work.Deep.GKO.degIn_eq_ncard]
    congr 1
    ext y
    simp only [Set.mem_inter_iff, SimpleGraph.mem_neighborSet, SimpleGraph.sup_adj]
    constructor
    · rintro ⟨h | h, hy⟩
      · exfalso
        rcases hbip v y h with ⟨hvA, -⟩ | ⟨-, hyA⟩
        · exact Finset.disjoint_left.mp hAB hvA hv
        · exact Finset.disjoint_left.mp hAB hyA hy
      · exact ⟨h, hy⟩
    · rintro ⟨h, hy⟩
      exact ⟨Or.inr h, hy⟩
  have hsumA : (∑ v ∈ A, Work.Deep.GKO.degIn (H ⊔ H₀) v A)
      + (∑ v ∈ A, Work.Deep.GKO.degIn (H ⊔ H₀) v B)
      = k * A.card := by
    rw [← Finset.sum_add_distrib]
    calc ∑ v ∈ A, (Work.Deep.GKO.degIn (H ⊔ H₀) v A
            + Work.Deep.GKO.degIn (H ⊔ H₀) v B)
        = ∑ v ∈ A, Work.Deep.GKO.degIn (H ⊔ H₀) v Finset.univ :=
          Finset.sum_congr rfl fun v _ => (degIn_univ_eq_add (H ⊔ H₀) A B hAB hcov v).symm
      _ = ∑ v ∈ A, Nat.card ((H ⊔ H₀).neighborSet v) :=
          Finset.sum_congr rfl fun v _ => degIn_univ_eq_natCard (H ⊔ H₀) v
      _ = ∑ _v ∈ A, k := Finset.sum_congr rfl fun v _ => hreg v
      _ = k * A.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hsumB : (∑ v ∈ B, Work.Deep.GKO.degIn (H ⊔ H₀) v B)
      + (∑ v ∈ B, Work.Deep.GKO.degIn (H ⊔ H₀) v A)
      = k * B.card := by
    rw [← Finset.sum_add_distrib]
    calc ∑ v ∈ B, (Work.Deep.GKO.degIn (H ⊔ H₀) v B
            + Work.Deep.GKO.degIn (H ⊔ H₀) v A)
        = ∑ v ∈ B, Work.Deep.GKO.degIn (H ⊔ H₀) v Finset.univ :=
          Finset.sum_congr rfl fun v _ => by
            rw [add_comm]
            exact (degIn_univ_eq_add (H ⊔ H₀) A B hAB hcov v).symm
      _ = ∑ v ∈ B, Nat.card ((H ⊔ H₀).neighborSet v) :=
          Finset.sum_congr rfl fun v _ => degIn_univ_eq_natCard (H ⊔ H₀) v
      _ = ∑ _v ∈ B, k := Finset.sum_congr rfl fun v _ => hreg v
      _ = k * B.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hinside : (∑ v ∈ A, Work.Deep.GKO.degIn H₀ v A)
      = ∑ v ∈ B, Work.Deep.GKO.degIn H₀ v B := by
    have h1 : (∑ v ∈ A, Work.Deep.GKO.degIn H₀ v A)
        + (∑ v ∈ A, Work.Deep.GKO.degIn (H ⊔ H₀) v B) = k * A.card := by
      rw [← hinsideA]; exact hsumA
    have h2 : (∑ v ∈ B, Work.Deep.GKO.degIn H₀ v B)
        + (∑ v ∈ B, Work.Deep.GKO.degIn (H ⊔ H₀) v A) = k * B.card := by
      rw [← hinsideB]; exact hsumB
    have h3 : (∑ v ∈ A, Work.Deep.GKO.degIn (H ⊔ H₀) v B)
        = (∑ v ∈ B, Work.Deep.GKO.degIn (H ⊔ H₀) v A) :=
      sum_degIn_comm (H ⊔ H₀) A B
    rw [h3, hcard] at h1
    exact Nat.add_right_cancel (h1.trans h2.symm)
  -- the numerical hypothesis of the inside decomposition
  have hM_le : (∑ v ∈ A, Work.Deep.GKO.degIn H₀ v A) ≤ d₀ * A.card := by
    calc (∑ v ∈ A, Work.Deep.GKO.degIn H₀ v A)
        ≤ ∑ _v ∈ A, d₀ := Finset.sum_le_sum fun v _ => ?_
      _ = d₀ * A.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    exact le_trans (Work.Deep.GKO.degIn_mono H₀ v (Finset.subset_univ A))
      (le_trans (by rw [degIn_univ_eq_natCard H₀ v]) (hΔ0 v))
  have h2M : 2 * (∑ v ∈ A, Work.Deep.GKO.degIn H₀ v A) ≤ d₀ * n := by
    have h := Nat.mul_le_mul_left 2 hM_le
    have h2 := congrArg (fun x => d₀ * x) h2A
    have h3 : 2 * (d₀ * A.card) = d₀ * (2 * A.card) := by ring
    omega
  have h4div : s - 3 ≤ 4 * (s / 4) := by
    have h4 : s % 4 < 4 := Nat.mod_lt s (by norm_num)
    have h5 : s / 4 * 4 + s % 4 = s := Nat.div_add_mod' s 4
    omega
  have hsq_le : 1 ≤ X → (X + 1) * (X + 1) ≤ s * (s - 3) := by
    intro hX1
    have h5 : s - 3 = X := by omega
    rw [h5, hs]
    nlinarith
  have h2Ms : 2 * (∑ v ∈ A, Work.Deep.GKO.degIn H₀ v A) ≤ s * (s - 3) := by
    rcases Nat.eq_zero_or_pos X with hX0 | hXpos
    · have h1 : d₀ * n < 1 := by rw [hX0] at hsq; simpa using hsq
      have h2 : d₀ = 0 := by
        by_contra hcon
        have h3 : 1 ≤ d₀ := Nat.one_le_iff_ne_zero.mpr hcon
        have h4 : 1 ≤ d₀ * n := by
          rcases Nat.eq_zero_or_pos n with h6 | h6
          · omega
          · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
        omega
      rw [h2] at h2M
      have h6 : (∑ v ∈ A, Work.Deep.GKO.degIn H₀ v A) = 0 := by omega
      rw [h6]
      simp
    · have h1 : (X + 1) * (X + 1) ≤ s * (s - 3) := hsq_le hXpos
      have h2 : 2 * (∑ v ∈ A, Work.Deep.GKO.degIn H₀ v A) < (X + 1) * (X + 1) := by
        have h3 : 2 * (∑ v ∈ A, Work.Deep.GKO.degIn H₀ v A) ≤ d₀ * n := h2M
        omega
      exact le_of_lt (lt_of_lt_of_le h2 h1)
  have hMlt : (∑ v ∈ A, Work.Deep.GKO.degIn H₀ v A) < (s / 4 + 1) * (2 * s) := by
    have h10 : s * (s - 3) ≤ s * (4 * (s / 4)) := Nat.mul_le_mul_left s h4div
    have h11 : s * (4 * (s / 4)) = 4 * (s / 4) * s := by ring
    have h12 : s * (s - 3) < 4 * (s / 4) * s + 4 * s := by
      have h13 : 0 < 4 * s := by omega
      omega
    have h14 : 4 * (s / 4) * s + 4 * s = 2 * ((s / 4 + 1) * (2 * s)) := by ring
    have h15 : 2 * (∑ v ∈ A, Work.Deep.GKO.degIn H₀ v A)
        < 2 * ((s / 4 + 1) * (2 * s)) := by
      calc 2 * (∑ v ∈ A, Work.Deep.GKO.degIn H₀ v A) ≤ s * (s - 3) := h2Ms
        _ < 4 * (s / 4) * s + 4 * s := h12
        _ = 2 * ((s / 4 + 1) * (2 * s)) := h14
    exact (Nat.mul_lt_mul_left (by norm_num : 0 < 2)).mp h15
  have hMdiv : (∑ v ∈ A, Work.Deep.GKO.degIn H₀ v A) / (2 * s) ≤ s / 4 := by
    have hb : 0 < 2 * s := by omega
    exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hb).mpr hMlt)
  have hnum : 2 * ((∑ v ∈ A, Work.Deep.GKO.degIn H₀ v A) / (2 * s) + (d₀ + 1)) ≤ s := by
    have h1 : (∑ v ∈ A, Work.Deep.GKO.degIn H₀ v A) / (2 * s) ≤ s / 4 := hMdiv
    have h2 : 2 * d₀ ≤ X / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
      omega
    have h3 : 2 * (s / 4) + X / 2 + 2 ≤ s := num_arith X s hs
    have ha : 2 * ((∑ v ∈ A, Work.Deep.GKO.degIn H₀ v A) / (2 * s)) ≤ 2 * (s / 4) :=
      Nat.mul_le_mul_left 2 h1
    have hd : 2 * ((∑ v ∈ A, Work.Deep.GKO.degIn H₀ v A) / (2 * s) + (d₀ + 1))
        = 2 * ((∑ v ∈ A, Work.Deep.GKO.degIn H₀ v A) / (2 * s)) + (2 * d₀ + 2) := by ring
    rw [hd]
    omega
  -- the inside decomposition
  obtain ⟨t, ν, NA, NB, hts, hNAm, hNAle, hNAin, hNBm, hNBle, hNBin, hNAcard, hNBcard,
      hν_le, hNAdisj, hNBdisj, hNAcov, hNBcov⟩ :=
    Work.Deep.GKO.Abs.insideDecomp hAB hΔ0 (by omega : 0 < s) hinside hnum
  -- the classes `N j = NA j ⊔ NB j`
  let N : Fin t → SimpleGraph (Fin n) := fun j => NA j ⊔ NB j
  have hN : ∀ j : Fin t, N j = NA j ⊔ NB j := fun j => rfl
  have hNin : ∀ j, ∀ u v : Fin n, (N j).Adj u v → (u ∈ A ∧ v ∈ A) ∨ (u ∈ B ∧ v ∈ B) := by
    intro j u v huv
    rw [hN j, SimpleGraph.sup_adj] at huv
    rcases huv with h | h
    · exact Or.inl (hNAin j u v h)
    · exact Or.inr (hNBin j u v h)
  have hNm : ∀ j, Work.Deep.GKO.IsMatching' (N j) := by
    intro j u v v' huv huv'
    rw [hN j, SimpleGraph.sup_adj] at huv huv'
    rcases huv with h | h
    · have h1 : u ∈ A := (hNAin j u v h).1
      rcases huv' with h' | h'
      · exact hNAm j u v v' h h'
      · exact absurd (hNBin j u v' h').1 (Finset.disjoint_left.mp hAB h1)
    · have h1 : u ∈ B := (hNBin j u v h).1
      rcases huv' with h' | h'
      · exact absurd h1 (Finset.disjoint_left.mp hAB (hNAin j u v' h').1)
      · exact hNBm j u v v' h h'
  have hNdisj : ∀ i j : Fin t, i ≠ j → Disjoint (N i).edgeSet (N j).edgeSet := by
    intro i j hij
    rw [hN i, hN j, SimpleGraph.disjoint_edgeSet, SimpleGraph.disjoint_left]
    intro u v huv huv'
    rw [SimpleGraph.sup_adj] at huv huv'
    rcases huv with h | h
    · rcases huv' with h' | h'
      · exact absurd h' (SimpleGraph.disjoint_left.mp (SimpleGraph.disjoint_edgeSet.mp
          (hNAdisj i j hij)) u v h)
      · exact absurd (hNBin j u v h').1 (Finset.disjoint_left.mp hAB (hNAin i u v h).1)
    · rcases huv' with h' | h'
      · exact absurd (hNBin i u v h).1 (Finset.disjoint_left.mp hAB (hNAin j u v h').1)
      · exact absurd h' (SimpleGraph.disjoint_left.mp (SimpleGraph.disjoint_edgeSet.mp
          (hNBdisj i j hij)) u v h)
  have hNAvset : ∀ j, vset (NA j) ⊆ A := fun j => vset_subset_of_inside (hNAin j)
  have hNBvset : ∀ j, vset (NB j) ⊆ B := fun j => vset_subset_of_inside (hNBin j)
  have hNAvcard : ∀ j, (vset (NA j)).card = 2 * ν j := fun j => by
    rw [card_vset_of_matching (NA j) (hNAm j), hNAcard j]
  have hNBvcard : ∀ j, (vset (NB j)).card = 2 * ν j := fun j => by
    rw [card_vset_of_matching (NB j) (hNBm j), hNBcard j]
  have hAinterN : ∀ j, A ∩ vset (N j) = vset (NA j) := by
    intro j
    refine Finset.ext fun u => ?_
    rw [Finset.mem_inter]
    constructor
    · intro hu
      obtain ⟨w, hw⟩ := mem_vset.mp hu.2
      rcases (show (NA j).Adj u w ∨ (NB j).Adj u w from by
        rw [← SimpleGraph.sup_adj, ← hN j]; exact hw) with h | h
      · exact mem_vset.mpr ⟨w, h⟩
      · exact absurd (hNBin j u w h).1 (Finset.disjoint_left.mp hAB hu.1)
    · intro hu
      obtain ⟨w, hw⟩ := mem_vset.mp hu
      exact ⟨hNAvset j hu,
        mem_vset.mpr ⟨w, by rw [hN j, SimpleGraph.sup_adj]; exact Or.inl hw⟩⟩
  have hBinterN : ∀ j, B ∩ vset (N j) = vset (NB j) := by
    intro j
    refine Finset.ext fun u => ?_
    rw [Finset.mem_inter]
    constructor
    · intro hu
      obtain ⟨w, hw⟩ := mem_vset.mp hu.2
      rcases (show (NA j).Adj u w ∨ (NB j).Adj u w from by
        rw [← SimpleGraph.sup_adj, ← hN j]; exact hw) with h | h
      · exact absurd hu.1 (Finset.disjoint_left.mp hAB (hNAin j u w h).1)
      · exact mem_vset.mpr ⟨w, h⟩
    · intro hu
      obtain ⟨w, hw⟩ := mem_vset.mp hu
      exact ⟨hNBvset j hu,
        mem_vset.mpr ⟨w, by rw [hN j, SimpleGraph.sup_adj]; exact Or.inr hw⟩⟩
  have hNbal : ∀ j, (A ∩ vset (N j)).card = (B ∩ vset (N j)).card := fun j => by
    rw [hAinterN j, hBinterN j, hNAvcard j, hNBvcard j]
  have hNsmall : ∀ j, (A ∩ vset (N j)).card ≤ 2 * s := fun j => by
    rw [hAinterN j, hNAvcard j]
    exact Nat.mul_le_mul_left 2 (hν_le j)
  -- the degree bound for `Hx`
  have hdegHx : ∀ v : Fin n, ε * (n : ℝ) + 3 * (s : ℝ) ≤ (Nat.card (Hx.neighborSet v) : ℝ) := by
    intro v
    have h1 : ε * (n : ℝ) ≤ (D : ℝ) / 2 := by linarith [hroom2]
    have h6 : (8 * (X + 3) : ℝ) ≤ (D : ℝ) := by exact_mod_cast hroom1
    have h7 : (s : ℝ) = (X : ℝ) + 3 := by rw [hs]; push_cast; ring
    have h9 : 3 * (s : ℝ) ≤ (D : ℝ) / 2 := by rw [h7]; linarith
    have h10 : (D : ℝ) ≤ (Nat.card (Hx.neighborSet v) : ℝ) := by
      have h11 : D ≤ Nat.card (H.neighborSet v) := hmin v
      have h12 : Nat.card (H.neighborSet v) ≤ Nat.card (Hx.neighborSet v) :=
        natCard_neighborSet_mono hH_le_Hx v
      exact_mod_cast le_trans h11 h12
    linarith
  -- the absorbing family
  have hroomq : (s : ℝ) < q * ε * (n : ℝ) := by rw [hs]; exact hroom3
  obtain ⟨P, hPle, hPbip, hPA, hPB, hPdisj⟩ :=
    absorbFamily hAB hcov hcard hHxbip hε hlrHx hts hroomq hdegHx N hNm hNin hNbal hNsmall
  -- the matchings
  let M : Fin t → SimpleGraph (Fin n) := fun j => N j ⊔ P j
  have hM : ∀ j : Fin t, M j = N j ⊔ P j := fun j => rfl
  have hPm : ∀ j, Work.Deep.GKO.IsMatching' (P j) := fun j =>
    isMatching_of_bipUnique hAB Finset.sdiff_subset Finset.sdiff_subset (hPbip j) (hPA j) (hPB j)
  have hNP : ∀ a b : Fin t, Disjoint (N a).edgeSet (P b).edgeSet := by
    intro a b
    rw [SimpleGraph.disjoint_edgeSet, SimpleGraph.disjoint_left]
    intro u v huv huv'
    have h1 := hNin a u v huv
    have h2 : (u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A) := by
      rcases hPbip b u v huv' with ⟨hu, hv⟩ | ⟨hu, hv⟩
      · exact Or.inl ⟨(Finset.mem_sdiff.mp hu).1, (Finset.mem_sdiff.mp hv).1⟩
      · exact Or.inr ⟨(Finset.mem_sdiff.mp hu).1, (Finset.mem_sdiff.mp hv).1⟩
    rcases h1 with ⟨huA, hvA⟩ | ⟨huB, hvB⟩
    · rcases h2 with ⟨-, hvB⟩ | ⟨huB, -⟩
      · exact Finset.disjoint_left.mp hAB hvA hvB
      · exact Finset.disjoint_left.mp hAB huA huB
    · rcases h2 with ⟨huA, -⟩ | ⟨-, hvA⟩
      · exact Finset.disjoint_left.mp hAB huA huB
      · exact Finset.disjoint_left.mp hAB hvA hvB
  have hMperf : ∀ j, Work.Deep.GKO.IsPerfectMatching' (H ⊔ H₀) (M j) := by
    intro j
    refine ⟨?_, ?_⟩
    · rw [hM j]
      refine sup_le ?_ ?_
      · rw [hN j]
        exact sup_le (le_trans (hNAle j) le_sup_right) (le_trans (hNBle j) le_sup_right)
      · exact le_trans (hPle j) (sup_le le_sup_left (le_trans (crossRestr_le H₀ A B) le_sup_right))
    · intro v
      by_cases hv : v ∈ vset (N j)
      · obtain ⟨w, hw, huniq⟩ := existsUnique_adj_of_mem_vset (hNm j) hv
        refine ⟨w, ?_, ?_⟩
        · show (N j ⊔ P j).Adj v w
          rw [SimpleGraph.sup_adj]; exact Or.inl hw
        · intro w' hw'
          change (N j ⊔ P j).Adj v w' at hw'
          rw [SimpleGraph.sup_adj] at hw'
          rcases hw' with h' | h'
          · exact huniq w' h'
          · exfalso
            rcases hPbip j v w' h' with ⟨hvA, -⟩ | ⟨hvB, -⟩
            · exact (Finset.mem_sdiff.mp hvA).2 hv
            · exact (Finset.mem_sdiff.mp hvB).2 hv
      · rcases hmemAB v with hvA | hvB
        · obtain ⟨w, hw, huniq⟩ := hPA j v (Finset.mem_sdiff.mpr ⟨hvA, hv⟩)
          refine ⟨w, ?_, ?_⟩
          · show (N j ⊔ P j).Adj v w
            rw [SimpleGraph.sup_adj]; exact Or.inr hw.2
          · intro w' hw'
            change (N j ⊔ P j).Adj v w' at hw'
            rw [SimpleGraph.sup_adj] at hw'
            rcases hw' with h' | h'
            · exact False.elim (hv (mem_vset.mpr ⟨w', h'⟩))
            · have hw'B : w' ∈ B \ vset (N j) := by
                rcases hPbip j v w' h' with ⟨-, h2⟩ | ⟨hvB, -⟩
                · exact h2
                · exfalso
                  exact absurd (Finset.mem_sdiff.mp hvB).1 (Finset.disjoint_left.mp hAB hvA)
              exact huniq w' ⟨hw'B, h'⟩
        · obtain ⟨w, hw, huniq⟩ := hPB j v (Finset.mem_sdiff.mpr ⟨hvB, hv⟩)
          refine ⟨w, ?_, ?_⟩
          · show (N j ⊔ P j).Adj v w
            rw [SimpleGraph.sup_adj]; exact Or.inr hw.2
          · intro w' hw'
            change (N j ⊔ P j).Adj v w' at hw'
            rw [SimpleGraph.sup_adj] at hw'
            rcases hw' with h' | h'
            · exact False.elim (hv (mem_vset.mpr ⟨w', h'⟩))
            · have hw'A : w' ∈ A \ vset (N j) := by
                rcases hPbip j v w' h' with ⟨h2, -⟩ | ⟨-, hvA⟩
                · exfalso
                  exact absurd hvB (Finset.disjoint_left.mp hAB (Finset.mem_sdiff.mp h2).1)
                · exact hvA
              exact huniq w' ⟨hw'A, h'⟩
  have hMdisj : ∀ i j : Fin t, i ≠ j → Disjoint (M i).edgeSet (M j).edgeSet := by
    intro i j hij
    refine (SimpleGraph.disjoint_edgeSet).mpr ?_
    rw [SimpleGraph.disjoint_left]
    intro u v huv huv'
    change (N i ⊔ P i).Adj u v at huv
    change (N j ⊔ P j).Adj u v at huv'
    rw [SimpleGraph.sup_adj] at huv huv'
    rcases huv with h | h
    · rcases huv' with h' | h'
      · exact absurd ((SimpleGraph.mem_edgeSet (N j)).mpr h')
          (Set.disjoint_left.mp (hNdisj i j hij) ((SimpleGraph.mem_edgeSet (N i)).mpr h))
      · exact absurd ((SimpleGraph.mem_edgeSet (P j)).mpr h')
          (Set.disjoint_left.mp (hNP i j) ((SimpleGraph.mem_edgeSet (N i)).mpr h))
    · rcases huv' with h' | h'
      · exact absurd ((SimpleGraph.mem_edgeSet (N j)).mpr h')
          (Set.disjoint_left.mp (hNP j i).symm ((SimpleGraph.mem_edgeSet (P i)).mpr h))
      · exact absurd ((SimpleGraph.mem_edgeSet (P j)).mpr h')
          (Set.disjoint_left.mp (hPdisj i j hij) ((SimpleGraph.mem_edgeSet (P i)).mpr h))
  -- the remainder
  set R : SimpleGraph (Fin n) := (H ⊔ H₀) \ (⨆ j : Fin t, M j) with hR
  have hRchar : ∀ e : Sym2 (Fin n), e ∈ R.edgeSet ↔
      e ∈ (H ⊔ H₀).edgeSet ∧ ∀ j : Fin t, e ∉ (M j).edgeSet := by
    intro e
    rw [hR, SimpleGraph.edgeSet_sdiff, SimpleGraph.edgeSet_iSup, Set.mem_sdiff, Set.mem_iUnion]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun j hj => h2 ⟨j, hj⟩⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun hh => hh.elim fun j hj => h2 j hj⟩
  have hRbip : ∀ u v : Fin n, R.Adj u v → (u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A) := by
    intro u v huv
    have he : s(u, v) ∈ R.edgeSet := (SimpleGraph.mem_edgeSet R).mpr huv
    have h1 := (hRchar _).mp he
    have hG : (H ⊔ H₀).Adj u v := (SimpleGraph.mem_edgeSet _).mp h1.1
    rw [SimpleGraph.sup_adj] at hG
    rcases hG with hH | hH₀
    · exact hbip u v hH
    · rcases hmemAB u with huA | huB
      · rcases hmemAB v with hvA | hvB
        · obtain ⟨j, hj⟩ := hNAcov u v huA hvA hH₀
          have hmem : s(u, v) ∈ (M j).edgeSet := by
            have h1' : (NA j).edgeSet ⊆ (N j).edgeSet :=
              SimpleGraph.edgeSet_mono (by rw [hN j]; exact le_sup_left)
            have h2' : (N j).edgeSet ⊆ (M j).edgeSet :=
              SimpleGraph.edgeSet_mono (by rw [hM j]; exact le_sup_left)
            exact h2' (h1' ((SimpleGraph.mem_edgeSet (NA j)).mpr hj))
          exact absurd hmem (h1.2 j)
        · exact Or.inl ⟨huA, hvB⟩
      · rcases hmemAB v with hvA | hvB
        · exact Or.inr ⟨huB, hvA⟩
        · obtain ⟨j, hj⟩ := hNBcov u v huB hvB hH₀
          have hmem : s(u, v) ∈ (M j).edgeSet := by
            have h1' : (NB j).edgeSet ⊆ (N j).edgeSet :=
              SimpleGraph.edgeSet_mono (by rw [hN j]; exact le_sup_right)
            have h2' : (N j).edgeSet ⊆ (M j).edgeSet :=
              SimpleGraph.edgeSet_mono (by rw [hM j]; exact le_sup_left)
            exact h2' (h1' ((SimpleGraph.mem_edgeSet (NB j)).mpr hj))
          exact absurd hmem (h1.2 j)
  have hUnionNbr : ∀ v : Fin n, ((⨆ j : Fin t, M j).neighborSet v).ncard = t := by
    intro v
    refine le_antisymm ?_ ?_
    · have h1 : Work.Deep.GKO.degIn (⨆ j : Fin t, M j) v Finset.univ
          ≤ ∑ j : Fin t, Work.Deep.GKO.degIn (M j) v Finset.univ := degIn_iSup_le _ v _
      have h2 : ∀ j : Fin t, Work.Deep.GKO.degIn (M j) v Finset.univ = 1 := by
        intro j
        rw [degIn_univ_eq_natCard, Nat.card_eq_one_iff_exists]
        obtain ⟨w, hw, huniq⟩ := (hMperf j).2 v
        refine ⟨⟨w, (SimpleGraph.mem_neighborSet (M j) v w).mpr hw⟩, fun y => Subtype.ext ?_⟩
        exact huniq ↑y ((SimpleGraph.mem_neighborSet (M j) v ↑y).mp y.2)
      calc ((⨆ j : Fin t, M j).neighborSet v).ncard
          = Work.Deep.GKO.degIn (⨆ j : Fin t, M j) v Finset.univ :=
            (degIn_univ_eq_natCard _ v).symm
        _ ≤ ∑ j : Fin t, Work.Deep.GKO.degIn (M j) v Finset.univ := h1
        _ = ∑ _j : Fin t, 1 := Finset.sum_congr rfl fun j _ => h2 j
        _ = t := by simp
    · have hpart : ∀ j : Fin t, ∃ w : Fin n, (M j).Adj v w := fun j => ((hMperf j).2 v).exists
      set part : Fin t → Fin n := fun j => Classical.choose (hpart j) with hpartdef
      have hpart_mem : ∀ j, (M j).Adj v (part j) := fun j => Classical.choose_spec (hpart j)
      have hpart_inj : Function.Injective part := by
        intro i j hij
        by_contra hne
        have h1 : s(v, part j) ∈ (M i).edgeSet :=
          (SimpleGraph.mem_edgeSet _).mpr (hij ▸ hpart_mem i)
        have h2 : s(v, part j) ∈ (M j).edgeSet := (SimpleGraph.mem_edgeSet _).mpr (hpart_mem j)
        exact Set.disjoint_left.mp (hMdisj i j hne) h1 h2
      have hsub : Set.range part ⊆ (⨆ j : Fin t, M j).neighborSet v := by
        rintro w ⟨j, rfl⟩
        rw [SimpleGraph.mem_neighborSet, SimpleGraph.iSup_adj]
        exact ⟨j, hpart_mem j⟩
      calc t = (Set.range part).ncard := by
            rw [Set.ncard_range_of_injective hpart_inj]
            simp
        _ ≤ ((⨆ j : Fin t, M j).neighborSet v).ncard := Set.ncard_le_ncard hsub
  have hRreg : ∀ v : Fin n, Nat.card (R.neighborSet v) = k - t := by
    intro v
    have hdisj : Disjoint (R.neighborSet v) ((⨆ j : Fin t, M j).neighborSet v) := by
      rw [Set.disjoint_left]
      intro w h1 h2
      rw [SimpleGraph.mem_neighborSet] at h1 h2
      have h3 := (hRchar _).mp ((SimpleGraph.mem_edgeSet R).mpr h1)
      rw [SimpleGraph.iSup_adj] at h2
      obtain ⟨j, hj⟩ := h2
      exact h3.2 j ((SimpleGraph.mem_edgeSet _).mpr hj)
    have hunion : (R.neighborSet v ∪ (⨆ j : Fin t, M j).neighborSet v)
        = (H ⊔ H₀).neighborSet v := by
      ext w
      rw [Set.mem_union, SimpleGraph.mem_neighborSet, SimpleGraph.mem_neighborSet,
        SimpleGraph.iSup_adj]
      constructor
      · rintro (h | ⟨j, hj⟩)
        · exact (SimpleGraph.mem_edgeSet _).mp ((hRchar _).mp ((SimpleGraph.mem_edgeSet R).mpr h)).1
        · exact (hMperf j).1 hj
      · intro h
        by_cases hR' : R.Adj v w
        · exact Or.inl hR'
        · refine Or.inr ?_
          have h1 : s(v, w) ∈ (H ⊔ H₀).edgeSet := (SimpleGraph.mem_edgeSet _).mpr h
          by_contra hcon
          have h2 : s(v, w) ∈ R.edgeSet :=
            (hRchar _).mpr ⟨h1, fun j hj => hcon ⟨j, (SimpleGraph.mem_edgeSet (M j)).mp hj⟩⟩
          exact hR' ((SimpleGraph.mem_edgeSet R).mp h2)
    have hsum : Nat.card ((H ⊔ H₀).neighborSet v)
        = Nat.card (R.neighborSet v) + Nat.card ((⨆ j : Fin t, M j).neighborSet v) := by
      rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq, ← hunion,
        Set.ncard_union_eq hdisj (Set.toFinite _)]
    have hsum' : ((R.neighborSet v)).ncard + t = k := by
      have h1 := hsum
      rw [hreg v, Nat.card_coe_set_eq, Nat.card_coe_set_eq] at h1
      rw [show ((⨆ j : Fin t, M j).neighborSet v).ncard = t from hUnionNbr v] at h1
      omega
    have h3 : ((R.neighborSet v)).ncard = k - t := by omega
    exact (Nat.card_coe_set_eq (R.neighborSet v)).trans h3
  have hck : t ≤ k := by
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hApos
    have h1 : D ≤ Nat.card ((H ⊔ H₀).neighborSet v) :=
      le_trans (hmin v) (natCard_neighborSet_mono le_sup_left v)
    have h2 : Nat.card ((H ⊔ H₀).neighborSet v) = k := hreg v
    have h4 : s ≤ D := by
      have h5 : 8 * (X + 3) ≤ D := hroom1
      omega
    omega
  exact Work.Deep.GKO.Abs.oneFactorOfMatchingFamily (H ⊔ H₀) A B hAB hcov hcard M R hMperf hMdisj
    (fun e => hRchar e) hRbip hRreg hck
end Work.Deep.GKO.OneFact
