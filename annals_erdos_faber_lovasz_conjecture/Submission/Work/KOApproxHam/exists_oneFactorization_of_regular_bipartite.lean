import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.KOApproxHam.BlowUp
import Submission.Work.KOApproxHam.degIn_sdiff
import Submission.Work.KOApproxHam.exists_unit_bipartite_factor_of_regular

/-!
# König's one-factorization of a regular bipartite graph

If `A` and `B` are disjoint finite sets in a graph `G` and the bipartite graph spanned by the
edges between `A` and `B` is `r`-regular (every `v ∈ A` has exactly `r` neighbours in `B`, every
`v ∈ B` exactly `r` neighbours in `A`), with `r ≥ 1`, then the `A`–`B` edges of `G` split into
`r` pairwise edge-disjoint perfect matchings between `A` and `B`.

This is the classical theorem of König.  The proof is the standard induction: by Hall's theorem
(`Work.KOApproxHam.exists_unit_bipartite_factor_of_regular`) the edges between `A` and `B`
contain a perfect matching; deleting it leaves an `(r-1)`-regular bipartite pair, to which the
induction hypothesis applies.  The resulting family `M : Fin r → SimpleGraph (Fin n)` is built by
`Fin.cases` (the peeled matching as index `0`, the recursive family shifted by one).
-/

namespace Work.KOApproxHam

open Work.Deep.GKO

/-- **The induction behind the one-factorization.**  For every `r ≥ 1` and every `r`-regular
bipartite pair `(A, B)` in an ambient graph `G`, the `A`–`B` edges of `G` split into `r` pairwise
edge-disjoint perfect matchings between `A` and `B`.

The statement is quantified over the ambient graph (rather than just over the initially given
one) because the induction step replaces `G` by `G` minus a peeled perfect matching; all the
clauses of the conclusion are properties of the individual subgraphs `M i` together with the
degree conditions, and these pass to subgraphs. -/
private theorem oneFac_aux {n : ℕ} (A B : Finset (Fin n)) (hAB : Disjoint A B) :
    ∀ r : ℕ, 1 ≤ r → ∀ G : SimpleGraph (Fin n),
      (∀ v ∈ A, degIn G v B = r) → (∀ v ∈ B, degIn G v A = r) →
      ∃ M : Fin r → SimpleGraph (Fin n),
        (∀ i, M i ≤ G) ∧
        (∀ i, ∀ v ∈ A, degIn (M i) v B = 1) ∧
        (∀ i, ∀ v ∈ B, degIn (M i) v A = 1) ∧
        (∀ i j, i ≠ j → Disjoint (M i).edgeSet (M j).edgeSet) ∧
        (∀ i, ∀ v, v ∉ A ∪ B → ∀ w, ¬ (M i).Adj v w) ∧
        (∀ i, ∀ v ∈ A, ∀ w ∈ A, ¬ (M i).Adj v w) ∧
        (∀ i, ∀ v ∈ B, ∀ w ∈ B, ¬ (M i).Adj v w) ∧
        (∀ v ∈ A, ∀ w ∈ B, G.Adj v w → ∃ i, (M i).Adj v w) := by
  intro r
  induction r with
  | zero => intro h; exact absurd h (by omega)
  | succ s ih =>
    rcases Nat.eq_zero_or_pos s with hs0 | hspos
    · -- `r = 1`: a single perfect matching, which necessarily covers every `A`–`B` edge of `G`.
      subst hs0
      intro _ G hregA hregB
      obtain ⟨M, hMG, hMout, hMA, hMB, hMdegA, hMdegB⟩ :=
        exists_unit_bipartite_factor_of_regular G A B hAB le_rfl hregA hregB
      refine ⟨fun _ => M, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i; exact hMG
      · intro i v hv; exact hMdegA v hv
      · intro i v hv; exact hMdegB v hv
      · intro i j hij
        exact absurd (Fin.ext (by
          have hi : i.val = 0 := Nat.lt_one_iff.mp i.isLt
          have hj : j.val = 0 := Nat.lt_one_iff.mp j.isLt
          omega)) hij
      · intro i v hv w; exact hMout v hv w
      · intro i v hv w hw; exact hMA v hv w hw
      · intro i v hv w hw; exact hMB v hv w hw
      · -- the covering clause: `v` has exactly one `G`-neighbour `w` in `B`, and the matching
        -- saturates `v`, so its matching partner must be that neighbour.
        intro v hv w hw hadj
        refine ⟨0, ?_⟩
        have hGnb : nbrFinset G v B = {w} := by
          obtain ⟨a, ha⟩ := Finset.card_eq_one.mp
            (show (nbrFinset G v B).card = 1 from hregA v hv)
          have hmem : w ∈ nbrFinset G v B := mem_nbrFinset.mpr ⟨hw, hadj⟩
          rw [ha] at hmem
          rw [ha, Finset.mem_singleton.mp hmem]
        have hsub : nbrFinset M v B ⊆ {w} := by
          rw [← hGnb]
          intro y hy
          rw [mem_nbrFinset] at hy ⊢
          exact ⟨hy.1, hMG hy.2⟩
        have heq : nbrFinset M v B = {w} := by
          refine Finset.eq_of_subset_of_card_le hsub ?_
          rw [Finset.card_singleton]
          exact (hMdegA v hv).ge
        have hwin : w ∈ nbrFinset M v B := by rw [heq]; exact Finset.mem_singleton_self w
        exact (mem_nbrFinset.mp hwin).2
    · -- `r = s + 1 ≥ 2`: peel a perfect matching `M₀` and recurse on `G \ M₀`.
      intro hs G hregA hregB
      obtain ⟨M₀, hM₀G, hM₀out, hM₀A, hM₀B, hM₀degA, hM₀degB⟩ :=
        exists_unit_bipartite_factor_of_regular G A B hAB hs hregA hregB
      have hG'le : G \ M₀ ≤ G := sdiff_le
      have hregA' : ∀ v ∈ A, degIn (G \ M₀) v B = s := by
        intro v hv
        rw [degIn_sdiff hM₀G, hregA v hv, hM₀degA v hv]
        omega
      have hregB' : ∀ v ∈ B, degIn (G \ M₀) v A = s := by
        intro v hv
        rw [degIn_sdiff hM₀G, hregB v hv, hM₀degB v hv]
        omega
      obtain ⟨M', hM'le, hM'degA, hM'degB, hM'disj, hM'out, hM'A, hM'B, hM'cov⟩ :=
        ih hspos (G \ M₀) hregA' hregB'
      let M : Fin (s + 1) → SimpleGraph (Fin n) := Fin.cases M₀ M'
      refine ⟨M, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i
        induction i using Fin.cases with
        | zero => exact hM₀G
        | succ j => exact le_trans (hM'le j) hG'le
      · intro i v hv
        induction i using Fin.cases with
        | zero => exact hM₀degA v hv
        | succ j => exact hM'degA j v hv
      · intro i v hv
        induction i using Fin.cases with
        | zero => exact hM₀degB v hv
        | succ j => exact hM'degB j v hv
      · intro i j hij
        induction i using Fin.cases with
        | zero =>
          induction j using Fin.cases with
          | zero => exact absurd rfl hij
          | succ k =>
            refine Set.disjoint_left.mpr fun x hx0 hx1 => ?_
            have hsub : (M' k).edgeSet ⊆ (G \ M₀).edgeSet := SimpleGraph.edgeSet_mono (hM'le k)
            have hx' : x ∈ (G \ M₀).edgeSet := hsub hx1
            rw [SimpleGraph.edgeSet_sdiff] at hx'
            exact hx'.2 hx0
        | succ k =>
          induction j using Fin.cases with
          | zero =>
            refine Set.disjoint_left.mpr fun x hx0 hx1 => ?_
            have hsub : (M' k).edgeSet ⊆ (G \ M₀).edgeSet := SimpleGraph.edgeSet_mono (hM'le k)
            have hx' : x ∈ (G \ M₀).edgeSet := hsub hx0
            rw [SimpleGraph.edgeSet_sdiff] at hx'
            exact hx'.2 hx1
          | succ l =>
            exact hM'disj k l (fun h => hij (by rw [h]))
      · intro i v hv w
        induction i using Fin.cases with
        | zero => exact hM₀out v hv w
        | succ j => exact hM'out j v hv w
      · intro i v hv w hw
        induction i using Fin.cases with
        | zero => exact hM₀A v hv w hw
        | succ j => exact hM'A j v hv w hw
      · intro i v hv w hw
        induction i using Fin.cases with
        | zero => exact hM₀B v hv w hw
        | succ j => exact hM'B j v hv w hw
      · -- the covering clause: `G`-edges not used by `M₀` survive in `G \ M₀`.
        intro v hv w hw hadj
        by_cases h0 : M₀.Adj v w
        · exact ⟨0, h0⟩
        · have h' : (G \ M₀).Adj v w := (SimpleGraph.sdiff_adj G M₀ v w).mpr ⟨hadj, h0⟩
          obtain ⟨j, hj⟩ := hM'cov v hv w hw h'
          exact ⟨j.succ, hj⟩

theorem exists_oneFactorization_of_regular_bipartite {n : ℕ} (G : SimpleGraph (Fin n))
    (A B : Finset (Fin n)) (hAB : Disjoint A B) {r : ℕ} (hpos : 1 ≤ r)
    (hregA : ∀ v ∈ A, Work.Deep.GKO.degIn G v B = r)
    (hregB : ∀ v ∈ B, Work.Deep.GKO.degIn G v A = r) :
    ∃ M : Fin r → SimpleGraph (Fin n),
      (∀ i, M i ≤ G) ∧
      (∀ i, ∀ v ∈ A, Work.Deep.GKO.degIn (M i) v B = 1) ∧
      (∀ i, ∀ v ∈ B, Work.Deep.GKO.degIn (M i) v A = 1) ∧
      (∀ i j, i ≠ j → Disjoint (M i).edgeSet (M j).edgeSet) ∧
      (∀ i, ∀ v, v ∉ A ∪ B → ∀ w, ¬ (M i).Adj v w) ∧
      (∀ i, ∀ v ∈ A, ∀ w ∈ A, ¬ (M i).Adj v w) ∧
      (∀ i, ∀ v ∈ B, ∀ w ∈ B, ¬ (M i).Adj v w) ∧
      (∀ v ∈ A, ∀ w ∈ B, G.Adj v w → ∃ i, (M i).Adj v w) :=
  oneFac_aux A B hAB r hpos G hregA hregB

end Work.KOApproxHam
