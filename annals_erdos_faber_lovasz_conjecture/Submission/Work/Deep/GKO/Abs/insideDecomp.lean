import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.Defs
import Submission.Work.Deep.GKO.RegVocab
import Submission.Work.Deep.GKO.OneFact.gridRefine
import Submission.Work.Deep.GKO.OneFact.splitMatching
import Submission.Work.Deep.GKO.OneFact.insideCountEq
import Submission.Work.Deep.GKO.Abs.insideSplit
import Submission.Work.Deep.GKO.Abs.splitAlong

namespace Work.Deep.GKO.Abs

set_option linter.unusedVariables false

open scoped Sym2

/-- Double counting: twice the number of `H`-edges lying inside the vertex set `A` is the sum of
the `A`-inside degrees of the vertices of `A`.  This is the bridge between the formulation of the
inside-edge decomposition in terms of degree sums and its formulation in terms of edge counts. -/
theorem two_mul_insideEdges_eq_sum_degIn {n : ℕ} (H : SimpleGraph (Fin n)) (A : Finset (Fin n)) :
    2 * Nat.card {e : Sym2 (Fin n) | e ∈ H.edgeSet ∧ (e : Set (Fin n)) ⊆ (A : Set (Fin n))}
      = ∑ v ∈ A, Work.Deep.GKO.degIn H v A := by
  rw [Work.Deep.GKO.OneFact.two_mul_card_edges_inside]
  unfold Work.Deep.GKO.OneFact.pc Work.Deep.GKO.degIn Work.Deep.GKO.nbrFinset
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [Finset.card_filter]

/-- Splitting the inside edges of a graph into equally sized matchings on both sides of a
partition of the vertex set.  If every degree of `H` is at most `d`, the numbers of `A`-inside and
`B`-inside `H`-edges are equal, and `2 * (m / s + (d + 1)) ≤ s` where `2 * m` is the number of
`A`-inside edges, then the `A`-inside edges and the `B`-inside edges both decompose into equally
sized matchings, at most `s` of them, each of size at most `s`.

Available ingredients: `Work.Deep.GKO.OneFact.gridRefine` (common refinement of two compositions
of an integer), `Work.Deep.GKO.OneFact.splitMatching` (a matching splits into sub-matchings with
prescribed sizes), and the Vizing tool `Submission.Commons.Combinatorics.SimpleGraph.vizing`. -/
theorem insideDecomp {n : ℕ} {A B : Finset (Fin n)} {H : SimpleGraph (Fin n)} {d s : ℕ}
    (hAB : Disjoint A B)
    (hΔ : ∀ v : Fin n, Nat.card (H.neighborSet v) ≤ d)
    (hs : 0 < s)
    (heq : (∑ v ∈ A, Work.Deep.GKO.degIn H v A)
        = (∑ v ∈ B, Work.Deep.GKO.degIn H v B))
    (hnum : 2 * ((∑ v ∈ A, Work.Deep.GKO.degIn H v A) / (2 * s) + (d + 1)) ≤ s) :
    ∃ (t : ℕ) (ν : Fin t → ℕ) (NA NB : Fin t → SimpleGraph (Fin n)),
      t ≤ s ∧
      (∀ j, Work.Deep.GKO.IsMatching' (NA j)) ∧
      (∀ j, NA j ≤ H) ∧
      (∀ j, ∀ u v : Fin n, (NA j).Adj u v → u ∈ A ∧ v ∈ A) ∧
      (∀ j, Work.Deep.GKO.IsMatching' (NB j)) ∧
      (∀ j, NB j ≤ H) ∧
      (∀ j, ∀ u v : Fin n, (NB j).Adj u v → u ∈ B ∧ v ∈ B) ∧
      (∀ j, Nat.card (NA j).edgeSet = ν j) ∧
      (∀ j, Nat.card (NB j).edgeSet = ν j) ∧
      (∀ j, ν j ≤ s) ∧
      (∀ i j : Fin t, i ≠ j → Disjoint (NA i).edgeSet (NA j).edgeSet) ∧
      (∀ i j : Fin t, i ≠ j → Disjoint (NB i).edgeSet (NB j).edgeSet) ∧
      (∀ u v : Fin n, u ∈ A → v ∈ A → H.Adj u v → ∃ j, (NA j).Adj u v) ∧
      (∀ u v : Fin n, u ∈ B → v ∈ B → H.Adj u v → ∃ j, (NB j).Adj u v) := by
  classical
  -- The number of `A`-inside edges is half the sum of the `A`-inside degrees, and likewise
  -- for `B`; this turns the two hypotheses into equations between edge counts.
  have hA2 := two_mul_insideEdges_eq_sum_degIn H A
  have hB2 := two_mul_insideEdges_eq_sum_degIn H B
  have hcard_eq : Nat.card {e : Sym2 (Fin n) | e ∈ H.edgeSet ∧ (e : Set (Fin n)) ⊆ (A : Set (Fin n))}
      = Nat.card {e : Sym2 (Fin n) | e ∈ H.edgeSet ∧ (e : Set (Fin n)) ⊆ (B : Set (Fin n))} := by
    omega
  have hdiv_eq : Nat.card {e : Sym2 (Fin n) | e ∈ H.edgeSet ∧ (e : Set (Fin n)) ⊆ (A : Set (Fin n))} / s
      = Nat.card {e : Sym2 (Fin n) | e ∈ H.edgeSet ∧ (e : Set (Fin n)) ⊆ (B : Set (Fin n))} / s := by
    rw [hcard_eq]
  -- The numerical hypothesis, in terms of the number of `A`-inside edges.
  have hnumA : 2 * (Nat.card {e : Sym2 (Fin n) | e ∈ H.edgeSet ∧ (e : Set (Fin n)) ⊆ (A : Set (Fin n))} / s + (d + 1)) ≤ s := by
    have hdiv : (∑ v ∈ A, Work.Deep.GKO.degIn H v A) / (2 * s)
        = Nat.card {e : Sym2 (Fin n) | e ∈ H.edgeSet ∧ (e : Set (Fin n)) ⊆ (A : Set (Fin n))} / s := by
      rw [← hA2]
      exact Nat.mul_div_mul_left _ _ (by norm_num)
    rwa [hdiv] at hnum
  -- Vizing splits the inside-`A` edges (respectively the inside-`B` edges) into matchings of
  -- size at most `s`, of which there are at most `d + 1 + m / s`.
  obtain ⟨a, PA, lam, ha, hPAmatch, hPAle, hPAin, hPAlam, hlamle, hPAdisj, hPAcov, hPAsum⟩ :=
    insideSplit A H hΔ hs
  obtain ⟨b, PB, mu, hb, hPBmatch, hPBle, hPBin, hPBmu, hmule, hPBdisj, hPBcov, hPBsum⟩ :=
    insideSplit B H hΔ hs
  -- The two size compositions of the same integer have a common refinement.
  have hsum_eq : ∑ i, lam i = ∑ j, mu j := by rw [hPAsum, hPBsum, hcard_eq]
  obtain ⟨t, ν, idxA, idxB, hνpos, hfibA, hfibB, hνA, hνB, hgrid⟩ :=
    Work.Deep.GKO.OneFact.gridRefine lam mu hsum_eq
  -- Re-split each decomposition along the refinement, so that both sides get the same sizes.
  obtain ⟨NA, hNAmatch, hNAle, hNAcard, hNAdisj, hNAcov⟩ :=
    splitAlong PA hPAmatch hPAdisj idxA ν (fun i => by rw [hfibA i, hPAlam i])
  obtain ⟨NB, hNBmatch, hNBle, hNBcard, hNBdisj, hNBcov⟩ :=
    splitAlong PB hPBmatch hPBdisj idxB ν (fun j => by rw [hfibB j, hPBmu j])
  -- The number of parts is at most `a + b ≤ 2 * (m / s + d + 1) ≤ s`.
  have ht_le : t ≤ s := by
    have hgrid' : t ≤ a + b := by simpa using hgrid
    have hab : a + b ≤ s := by
      have h2 : b ≤ d + 1 + Nat.card {e : Sym2 (Fin n) | e ∈ H.edgeSet ∧ (e : Set (Fin n)) ⊆ (B : Set (Fin n))} / s := hb
      rw [← hdiv_eq] at h2
      omega
    omega
  refine ⟨t, ν, NA, NB, ht_le, hNAmatch, ?_, ?_, hNBmatch, ?_, ?_, hNAcard, hNBcard, ?_,
    hNAdisj, hNBdisj, ?_, ?_⟩
  · intro j; exact le_trans (hNAle j) (hPAle (idxA j))
  · intro j u v huv; exact hPAin (idxA j) u v ((SimpleGraph.le_iff_adj.mp (hNAle j)) u v huv)
  · intro j; exact le_trans (hNBle j) (hPBle (idxB j))
  · intro j u v huv; exact hPBin (idxB j) u v ((SimpleGraph.le_iff_adj.mp (hNBle j)) u v huv)
  · intro j; exact le_trans (hνA j) (hlamle (idxA j))
  · -- every `A`-inside edge of `H` is an unordered pair `s(u, v)` with `u, v ∈ A`
    intro u v hu hv huv
    have hmem : s(u, v) ∈ H.edgeSet := huv
    have hsub : (s(u, v) : Set (Fin n)) ⊆ (A : Set (Fin n)) := by
      rw [Sym2.coe_mk]
      intro x hx
      rcases hx with rfl | rfl
      · exact hu
      · exact hv
    obtain ⟨i, hi⟩ := hPAcov (s(u, v)) hmem hsub
    obtain ⟨k, hk⟩ := hNAcov (s(u, v)) ⟨i, hi⟩
    exact ⟨k, hk⟩
  · intro u v hu hv huv
    have hmem : s(u, v) ∈ H.edgeSet := huv
    have hsub : (s(u, v) : Set (Fin n)) ⊆ (B : Set (Fin n)) := by
      rw [Sym2.coe_mk]
      intro x hx
      rcases hx with rfl | rfl
      · exact hu
      · exact hv
    obtain ⟨i, hi⟩ := hPBcov (s(u, v)) hmem hsub
    obtain ⟨k, hk⟩ := hNBcov (s(u, v)) ⟨i, hi⟩
    exact ⟨k, hk⟩

end Work.Deep.GKO.Abs
