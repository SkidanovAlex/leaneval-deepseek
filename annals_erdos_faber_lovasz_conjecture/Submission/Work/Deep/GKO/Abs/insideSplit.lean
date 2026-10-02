import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.Defs
import Submission.Work.Deep.GKO.exists_matchingSplit
import Submission.Work.Deep.GKO.Abs.insideColouring
import Submission.Work.Deep.GKO.Abs.sum_natCard_edgeSet_of_decomp

/-!
# `Work.Deep.GKO.Abs.insideSplit`

The edges of a graph `H` of maximum degree at most `d` that lie inside a vertex set `A` split
into at most `d + 1 + m / s` matchings of size at most `s`, where `m` is the number of inside
edges.

The two inputs are

* `Work.Deep.GKO.Abs.insideColouring` — Vizing's `Δ+1` edge colouring restricted to the inside
  edges, giving `d + 1` colour classes, each of which is a matching;
* `Work.Deep.GKO.exists_matchingSplit` — cutting each colour class into blocks of at most `s`
  edges.

The blocks are indexed by the disjoint union `Σ i, Fin (q i)` of the `q i` blocks of the `i`-th
colour class, which `finSigmaFinEquiv` identifies with `Fin (∑ i, q i)`; the total number of
blocks is at most `∑ i (1 + |C i| / s) ≤ (d + 1) + m / s`.
-/

set_option maxHeartbeats 1000000

namespace Work.Deep.GKO.Abs

open scoped Sym2

theorem insideSplit {n : ℕ} (A : Finset (Fin n)) (H : SimpleGraph (Fin n)) {d s : ℕ}
    (hd : ∀ v : Fin n, Nat.card (H.neighborSet v) ≤ d) (hs : 0 < s) :
    ∃ (k : ℕ) (PA : Fin k → SimpleGraph (Fin n)) (lam : Fin k → ℕ),
      k ≤ d + 1 + Nat.card {e : Sym2 (Fin n) | e ∈ H.edgeSet ∧ (e : Set (Fin n)) ⊆ (A : Set (Fin n))} / s ∧
      (∀ i, Work.Deep.GKO.IsMatching' (PA i)) ∧
      (∀ i, PA i ≤ H) ∧
      (∀ i, ∀ u v : Fin n, (PA i).Adj u v → u ∈ A ∧ v ∈ A) ∧
      (∀ i, Nat.card (PA i).edgeSet = lam i) ∧
      (∀ i, lam i ≤ s) ∧
      (∀ i j : Fin k, i ≠ j → Disjoint (PA i).edgeSet (PA j).edgeSet) ∧
      (∀ e ∈ H.edgeSet, (e : Set (Fin n)) ⊆ (A : Set (Fin n)) → ∃ i, e ∈ (PA i).edgeSet) ∧
      (∑ i, lam i = Nat.card {e : Sym2 (Fin n) | e ∈ H.edgeSet ∧ (e : Set (Fin n)) ⊆ (A : Set (Fin n))}) := by
  classical
  -- ## The inside edge set
  set EA : Finset (Sym2 (Fin n)) :=
    Finset.univ.filter (fun e => e ∈ H.edgeSet ∧ (e : Set (Fin n)) ⊆ (A : Set (Fin n))) with hEA
  have hEA_mem : ∀ e, e ∈ EA ↔ e ∈ H.edgeSet ∧ (e : Set (Fin n)) ⊆ (A : Set (Fin n)) := by
    intro e; rw [hEA]; simp
  have hEA_sub : (↑EA : Set (Sym2 (Fin n))) ⊆ H.edgeSet := fun e he => (hEA_mem e).mp he |>.1
  have hm_card : Nat.card {e : Sym2 (Fin n) | e ∈ H.edgeSet ∧ (e : Set (Fin n)) ⊆ (A : Set (Fin n))}
      = EA.card := by
    rw [Nat.card_coe_set_eq]
    have h : ({e : Sym2 (Fin n) | e ∈ H.edgeSet ∧ (e : Set (Fin n)) ⊆ (A : Set (Fin n))} :
        Set (Sym2 (Fin n))) = (↑EA : Set (Sym2 (Fin n))) := by
      ext e; exact (hEA_mem e).symm
    rw [h, Set.ncard_coe_finset]
  -- ## Vizing's colouring of the inside edges, and its colour classes
  obtain ⟨col, hcol⟩ := Work.Deep.GKO.Abs.insideColouring A H hd
  let Ci : Fin (d + 1) → Finset (Sym2 (Fin n)) := fun i => EA.filter (fun e => col e = i)
  have hCi_eq : ∀ i, Ci i = EA.filter (fun e => col e = i) := fun _ => rfl
  have hCi_mem : ∀ i e, e ∈ Ci i ↔ e ∈ EA ∧ col e = i := by
    intro i e; rw [hCi_eq i, Finset.mem_filter]
  have hCi_le : ∀ i, Ci i ⊆ EA := fun i e he => ((hCi_mem i e).mp he).1
  have hCi_disj : ∀ i j : Fin (d + 1), i ≠ j → Disjoint (Ci i) (Ci j) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact hij (((hCi_mem i x).mp hx).2.symm.trans ((hCi_mem j x).mp hx').2)
  have hCi_cov : ∀ x ∈ EA, x ∈ Ci (col x) := fun x hx => (hCi_mem (col x) x).mpr ⟨hx, rfl⟩
  have hCi_match : ∀ i, Work.Deep.GKO.IsMatching'
      (SimpleGraph.fromEdgeSet ((Ci i : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))) := by
    intro i v w w' hvw hvw'
    rw [SimpleGraph.fromEdgeSet_adj] at hvw hvw'
    obtain ⟨hm, hne⟩ := hvw
    obtain ⟨hm', hne'⟩ := hvw'
    have h1 : s(v, w) ∈ EA := (Finset.mem_filter.mp hm).1
    have h2 : s(v, w') ∈ EA := (Finset.mem_filter.mp hm').1
    have hcol_eq : col s(v, w) = col s(v, w') := by
      rw [(Finset.mem_filter.mp hm).2, (Finset.mem_filter.mp hm').2]
    by_contra hww
    have hne_edge : s(v, w) ≠ s(v, w') := by
      intro h
      rcases Sym2.eq_iff.mp h with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact hww h2
      · exact hne' h1
    exact hcol s(v, w) s(v, w') ((hEA_mem _).mp h1).1 ((hEA_mem _).mp h1).2
      ((hEA_mem _).mp h2).1 ((hEA_mem _).mp h2).2 hne_edge
      ⟨v, Sym2.mem_mk_left v w, Sym2.mem_mk_left v w'⟩ hcol_eq
  have hCi_edgeSet : ∀ i, (SimpleGraph.fromEdgeSet ((Ci i : Finset (Sym2 (Fin n))) :
      Set (Sym2 (Fin n)))).edgeSet = ((Ci i : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n))) := by
    intro i
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    exact Set.eq_of_subset_of_subset Set.sdiff_subset fun z hz => ⟨hz, by
      rw [Sym2.mem_diagSet]
      exact SimpleGraph.not_isDiag_of_mem_edgeSet H (hEA_sub (hCi_le i hz))⟩
  -- ## Cutting each colour class into blocks of at most `s` edges
  have hsplit : ∀ i : Fin (d + 1), ∃ (q : ℕ) (P : Fin q → SimpleGraph (Fin n)),
      (∀ j, Work.Deep.GKO.IsMatching' (P j)) ∧
      (∀ j, P j ≤ SimpleGraph.fromEdgeSet
        ((Ci i : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))) ∧
      (∀ j, Nat.card (P j).edgeSet ≤ s) ∧
      (∀ j j', j ≠ j' → Disjoint (P j).edgeSet (P j').edgeSet) ∧
      (∀ e ∈ (SimpleGraph.fromEdgeSet
        ((Ci i : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))).edgeSet,
        ∃ j, e ∈ (P j).edgeSet) ∧
      q ≤ 1 + (Ci i).card / s := by
    intro i
    obtain ⟨q, P, h1, h2, h3, h4, h5, h6⟩ := Work.Deep.GKO.exists_matchingSplit
      (SimpleGraph.fromEdgeSet ((Ci i : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n))))
      (hCi_match i) hs
    exact ⟨q, P, h1, h2, h3, h4, h5, by
      rwa [hCi_edgeSet i, Nat.card_coe_set_eq, Set.ncard_coe_finset] at h6⟩
  choose q P hP using hsplit
  have hPm : ∀ i j, Work.Deep.GKO.IsMatching' (P i j) := fun i j => (hP i).1 j
  have hPle : ∀ i j, P i j ≤ SimpleGraph.fromEdgeSet
      ((Ci i : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n))) := fun i j => (hP i).2.1 j
  have hPcard : ∀ i j, Nat.card (P i j).edgeSet ≤ s := fun i j => (hP i).2.2.1 j
  have hPdisj : ∀ i (j j' : Fin (q i)), j ≠ j' →
      Disjoint (P i j).edgeSet (P i j').edgeSet := fun i => (hP i).2.2.2.1
  have hPcov : ∀ i (e : Sym2 (Fin n)), e ∈ (SimpleGraph.fromEdgeSet
      ((Ci i : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))).edgeSet →
      ∃ j, e ∈ (P i j).edgeSet := fun i => (hP i).2.2.2.2.1
  have hPq : ∀ i, q i ≤ 1 + (Ci i).card / s := fun i => (hP i).2.2.2.2.2
  -- every edge of a block lies in the corresponding colour class
  have hP_edge : ∀ (i : Fin (d + 1)) (j : Fin (q i)) (x : Sym2 (Fin n)),
      x ∈ (P i j).edgeSet → x ∈ Ci i := by
    intro i j x hx
    have h1 : x ∈ (SimpleGraph.fromEdgeSet
        ((Ci i : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))).edgeSet :=
      SimpleGraph.edgeSet_mono (hPle i j) hx
    rwa [hCi_edgeSet i] at h1
  -- ## Assembling the family, indexed by the disjoint union of the blocks
  let k : ℕ := ∑ i : Fin (d + 1), q i
  let E : (Sigma fun i : Fin (d + 1) => Fin (q i)) ≃ Fin k := finSigmaFinEquiv
  let PA : Fin k → SimpleGraph (Fin n) := fun y => P (E.symm y).1 (E.symm y).2
  let lam : Fin k → ℕ := fun y => Nat.card (PA y).edgeSet
  have PA_apply : ∀ y : Fin k, PA y = P (E.symm y).1 (E.symm y).2 := fun _ => rfl
  -- the total number of edges of a colour class is the sum over its blocks
  have hEAcard : (∑ i : Fin (d + 1), (Ci i).card) = EA.card := by
    have h5 : (∑ i : Fin (d + 1), (Ci i).card)
        = ∑ i : Fin (d + 1), (EA.filter (fun e => col e = i)).card :=
      Finset.sum_congr rfl (fun i _ => by rw [hCi_eq i])
    rw [h5, ← Finset.card_eq_sum_card_fiberwise (s := EA) (t := Finset.univ) (f := col)
      (fun x _ => Finset.mem_univ (col x))]
  refine ⟨k, PA, lam, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the number of blocks
    have h1 : k ≤ ∑ i : Fin (d + 1), (1 + (Ci i).card / s) := by
      show (∑ i : Fin (d + 1), q i) ≤ _
      exact Finset.sum_le_sum (fun i _ => hPq i)
    have h2 : (∑ i : Fin (d + 1), (1 + (Ci i).card / s))
        = (d + 1) + ∑ i : Fin (d + 1), (Ci i).card / s := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp
    have h3 : (∑ i : Fin (d + 1), (Ci i).card / s)
        ≤ (∑ i : Fin (d + 1), (Ci i).card) / s := by
      rw [Nat.le_div_iff_mul_le hs, Finset.sum_mul]
      exact Finset.sum_le_sum (fun i _ => Nat.div_mul_le_self (Ci i).card s)
    rw [hm_card]
    calc k ≤ ∑ i : Fin (d + 1), (1 + (Ci i).card / s) := h1
      _ = (d + 1) + ∑ i : Fin (d + 1), (Ci i).card / s := h2
      _ ≤ (d + 1) + (∑ i : Fin (d + 1), (Ci i).card) / s := Nat.add_le_add_left h3 (d + 1)
      _ = d + 1 + EA.card / s := by rw [hEAcard]
  · -- each part is a matching
    intro y
    rw [PA_apply y]
    exact hPm (E.symm y).1 (E.symm y).2
  · -- each part is a subgraph of `H`
    intro y
    rw [PA_apply y]
    refine le_trans (hPle (E.symm y).1 (E.symm y).2) ?_
    rw [SimpleGraph.fromEdgeSet_le]
    exact Set.Subset.trans Set.sdiff_subset (fun z hz => hEA_sub (hCi_le _ hz))
  · -- the endpoints of every edge of a part lie in `A`
    intro y u v huv
    rw [PA_apply y] at huv
    have h1 : (SimpleGraph.fromEdgeSet ((Ci (E.symm y).1 : Finset (Sym2 (Fin n))) :
        Set (Sym2 (Fin n)))).Adj u v := hPle (E.symm y).1 (E.symm y).2 huv
    obtain ⟨hmem, -⟩ := (SimpleGraph.fromEdgeSet_adj _).mp h1
    have h2 : (s(u, v) : Set (Fin n)) ⊆ (A : Set (Fin n)) :=
      ((hEA_mem s(u, v)).mp ((hCi_mem _ s(u, v)).mp hmem).1).2
    rw [Sym2.coe_mk] at h2
    exact ⟨h2 (by simp), h2 (by simp)⟩
  · -- the edge counts
    intro y
    rfl
  · -- the parts are small
    intro y
    show Nat.card (PA y).edgeSet ≤ s
    rw [PA_apply y]
    exact hPcard (E.symm y).1 (E.symm y).2
  · -- distinct parts are edge-disjoint
    intro y y' hyy
    have hne : E.symm y ≠ E.symm y' := by
      intro h
      exact hyy (by
        have h2 := congrArg E h
        rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h2)
    rw [PA_apply y, PA_apply y']
    by_cases hi : (E.symm y).1 = (E.symm y').1
    · -- blocks of the same colour class
      have htransport : ∀ {i i' : Fin (d + 1)} (hi : i = i') (j : Fin (q i')),
          P i' j = P i (Fin.cast (congrArg q hi.symm) j) := by
        intro i i' hi j
        cases hi
        simp
      rw [htransport hi (E.symm y').2]
      refine hPdisj (E.symm y).1 (E.symm y).2 _ (fun hjj => hne (Sigma.ext hi ?_))
      exact (Fin.heq_ext_iff (congrArg q hi)).mpr (by rw [hjj, Fin.val_cast])
    · -- blocks of different colour classes
      refine Set.disjoint_left.mpr (fun x hx hx' => ?_)
      have hx1 : x ∈ Ci (E.symm y).1 := hP_edge _ _ x hx
      have hx2 : x ∈ Ci (E.symm y').1 := hP_edge _ _ x hx'
      exact (Finset.disjoint_left.mp (hCi_disj _ _ hi) hx1) hx2
  · -- the parts cover all inside edges
    intro x hx hxA
    have hxEA : x ∈ EA := (hEA_mem x).mpr ⟨hx, hxA⟩
    have hxCi : x ∈ Ci (col x) := hCi_cov x hxEA
    have hxEdge : x ∈ (SimpleGraph.fromEdgeSet ((Ci (col x) : Finset (Sym2 (Fin n))) :
        Set (Sym2 (Fin n)))).edgeSet := by
      rw [hCi_edgeSet (col x)]; exact hxCi
    obtain ⟨j, hj⟩ := hPcov (col x) x hxEdge
    refine ⟨E ⟨col x, j⟩, ?_⟩
    rw [PA_apply, Equiv.symm_apply_apply]
    exact hj
  · -- the total number of edges
    have hsum1 : (∑ y : Fin k, lam y)
        = ∑ i : Fin (d + 1), ∑ j : Fin (q i), Nat.card (P i j).edgeSet := by
      show (∑ y : Fin k, Nat.card (P (E.symm y).1 (E.symm y).2).edgeSet) = _
      rw [Equiv.sum_comp E.symm (fun x : Sigma fun i : Fin (d + 1) => Fin (q i) =>
        Nat.card (P x.1 x.2).edgeSet)]
      rw [Fintype.sum_sigma]
    have hsum2 : ∀ i : Fin (d + 1), (∑ j : Fin (q i), Nat.card (P i j).edgeSet)
        = (Ci i).card := by
      intro i
      have h := Work.Deep.GKO.Abs.sum_natCard_edgeSet_of_decomp
        (G := SimpleGraph.fromEdgeSet ((Ci i : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n))))
        (P := fun j => P i j) (fun j => hPle i j) (fun j j' hjj => hPdisj i j j' hjj)
        (fun e he => hPcov i e he)
      rw [h, hCi_edgeSet i, Nat.card_coe_set_eq, Set.ncard_coe_finset]
    calc (∑ y : Fin k, lam y)
        = ∑ i : Fin (d + 1), ∑ j : Fin (q i), Nat.card (P i j).edgeSet := hsum1
      _ = ∑ i : Fin (d + 1), (Ci i).card := Finset.sum_congr rfl (fun i _ => hsum2 i)
      _ = EA.card := hEAcard
      _ = Nat.card {e : Sym2 (Fin n) | e ∈ H.edgeSet ∧ (e : Set (Fin n)) ⊆ (A : Set (Fin n))} :=
          hm_card.symm

end Work.Deep.GKO.Abs
