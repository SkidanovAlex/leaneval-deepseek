import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.OneFact.N5.Defs
import Submission.Work.Deep.GKO.OneFact.N5.Basic
import Submission.Work.Deep.GKO.OneFact.N5.completeInsideMatching
import Submission.Work.Deep.GKO.OneFact.N5.bipLowerRegRemaining
import Submission.Work.Deep.GKO.OneFact.N5.degInRemainingNeighbors
import Submission.Work.Deep.GKO.OneFact.N5.roomRemaining
import Submission.Work.Deep.GKO.OneFact.N5.cardHeavyLe
import Submission.Work.Deep.GKO.OneFact.N5.lastClassIndicator

/-!
# N5c: completing *all* the classes (`EFL_N5_LEAD.md` §2, §3)

`completeInsideMatching` (N5b) completes one near-perfect inside matching `N` to a perfect matching
of `N ⊔ K` using one application of `BipLowerReg`; it re-matches at most `5 |uncov N|` covered
vertices and re-matches no covered vertex of a prescribed set `F`.

`completeAllClasses` (N5c) iterates this over the whole family `N : Fin c → SimpleGraph (Fin n)`:
the classes are processed one after another, each time with the cross graph `K₀` *minus the cross
edges already consumed* and with `F` the vertices that have already been re-matched `L` times.  The
outcome is a family of pairwise edge-disjoint perfect matchings of `N j ⊔ K₀` in which every vertex
is re-matched at most `L` times.

The iteration carries five registers, which are the clauses of the auxiliary statement
`completeAllClassesAux` below:

1. every `P j` is a perfect matching of `N j ⊔ K₀`;
2. the `P j` are pairwise edge-disjoint;
3. `cntOf N P v ≤ L` at every vertex (the goal of the node);
4. `(usedNbrs K₀ P v).card ≤ missOf N v + cntOf N P v` — the cross edges of `K₀` at `v` consumed so
   far are charged to the miss count and the re-match count, whence at most `m + L`;
5. `∑_v cntOf N P v ≤ 5 ∑_j |uncov (N j)|` — the global re-match budget, from which the size
   `5nm/L` of the forbidden set `F` of the next step follows (`cardHeavyLe`).

The numerical inputs of one step (survival of `BipLowerReg` under the deletion, the degree loss, the
room computation, the size of `F` and the per-class cross-edge budget) are the delegated modules
imported above.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators
open Classical

namespace Work.Deep.GKO.OneFact.N5

noncomputable section

variable {n : ℕ}

/-! ## Auxiliaries -/

/-- Monotonicity of `⊔` in its right argument. -/
private theorem sup_le_sup_right_aux {G H H' : SimpleGraph (Fin n)} (h : H ≤ H') :
    G ⊔ H ≤ G ⊔ H' := by
  intro x y hxy
  rcases (SimpleGraph.sup_adj G H x y).mp hxy with h1 | h1
  · exact (SimpleGraph.sup_adj G H' x y).mpr (Or.inl h1)
  · exact (SimpleGraph.sup_adj G H' x y).mpr (Or.inr (h h1))

/-- A cross edge used by an earlier class cannot also be used by the last class: the last class
runs on the cross graph with all earlier used edges deleted.  (This is the edge-disjointness of the
two classes, contrapositively.) -/
private theorem not_adj_of_used {A B : Finset (Fin n)} (hAB : Disjoint A B)
    (hcov : A ∪ B = Finset.univ) {N Nl K₀ Kl Pl Pol : SimpleGraph (Fin n)}
    (hNin : ∀ u v, N.Adj u v → IsInsidePair A B u v)
    (hNinl : ∀ u v, Nl.Adj u v → IsInsidePair A B u v)
    (hKbip : ∀ u v, K₀.Adj u v → IsCrossPair A B u v)
    (hKl : ∀ u v, Kl.Adj u v → K₀.Adj u v)
    (hused : ∀ u v, Kl.Adj u v → ¬ Pol.Adj u v)
    (hPol : Pol ≤ N ⊔ K₀) (hPl : Pl ≤ Nl ⊔ Kl)
    (hNNl : ∀ u v, N.Adj u v → ¬ Nl.Adj u v)
    {x y : Fin n} (hu : Pol.Adj x y) (hv : Pl.Adj x y) : False := by
  have hPol' := (SimpleGraph.sup_adj N K₀ x y).mp (hPol hu)
  have hPl' := (SimpleGraph.sup_adj Nl Kl x y).mp (hPl hv)
  rcases cross_or_inside hcov (u := x) (v := y) with hc | hi
  · rcases hPol' with h | h
    · exact not_inside_of_cross hAB hc (hNin x y h)
    · rcases hPl' with h2 | h2
      · exact not_inside_of_cross hAB hc (hNinl x y h2)
      · exact hused x y h2 hu
  · rcases hPol' with h | h
    · rcases hPl' with h2 | h2
      · exact hNNl x y h h2
      · exact not_cross_of_inside hAB hi (hKbip x y (hKl x y h2))
    · exact not_cross_of_inside hAB hi (hKbip x y h)

/-! ## The iteration -/

/-- **The N5c iteration with its registers.**  `completeAllClasses` is the `∀ v, cntOf N P v ≤ L`
clause of the conclusion below; the remaining clauses are the invariant that the iteration has to
carry. -/
private theorem completeAllClassesAux {n : ℕ} (A B : Finset (Fin n)) (hAB : Disjoint A B)
    (hcov : A ∪ B = Finset.univ) (hcard : A.card = B.card)
    (K₀ : SimpleGraph (Fin n))
    (hKbip : ∀ u v, K₀.Adj u v → (u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A))
    {q ε : ℝ} {s m L D₀ : ℕ} (hq : 0 < q) (hε : 0 < ε) (hL : 0 < L)
    (hlr : Work.Deep.GKO.BipLowerReg K₀ A B q ε)
    (hdeg0 : ∀ v, D₀ ≤ Nat.card (K₀.neighborSet v))
    (hroomq : ((m + L : ℕ) : ℝ) ≤ q * ε * (n : ℝ) / 2)
    (hroomD : ε * (n : ℝ) + ((3 * (5 * n * m / L) + 14 * s + m + L + 1 : ℕ) : ℝ) < (D₀ : ℝ)) :
    ∀ (c : ℕ) (N : Fin c → SimpleGraph (Fin n)),
      (∀ j, IsMatching' (N j)) →
      (∀ j u v, (N j).Adj u v → (u ∈ A ∧ v ∈ A) ∨ (u ∈ B ∧ v ∈ B)) →
      (∀ i j, i ≠ j → Disjoint (N i).edgeSet (N j).edgeSet) →
      (∀ j, (uncov (N j)).card ≤ s) →
      (∀ v, missOf N v ≤ m) →
      ∃ P : Fin c → SimpleGraph (Fin n),
        (∀ j, IsPerfectMatching' (N j ⊔ K₀) (P j)) ∧
        (∀ i j, i ≠ j → Disjoint (P i).edgeSet (P j).edgeSet) ∧
        (∀ v, cntOf N P v ≤ L) ∧
        (∀ v, (usedNbrs K₀ P v).card ≤ missOf N v + cntOf N P v) ∧
        (∑ v, cntOf N P v) ≤ 5 * ∑ j, (uncov (N j)).card := by
  intro c
  induction c with
  | zero =>
    intro N hN hNin hNdisj hU hmiss
    refine ⟨Fin.elim0, ?_, ?_, ?_, ?_, ?_⟩
    · intro j; exact j.elim0
    · intro i; exact i.elim0
    · intro v; simp [cntOf]
    · intro v; simp [usedNbrs, cntOf, missOf]
    · simp [cntOf]
  | succ c ih =>
    intro N hN hNin hNdisj hU hmiss
    -- the family restricted to its first `c` classes, and the last class
    let N' : Fin c → SimpleGraph (Fin n) := fun j => N j.castSucc
    let Nl : SimpleGraph (Fin n) := N (Fin.last c)
    have hNsnoc : Fin.snoc N' Nl = N := snoc_castSucc_last N
    -- the induction hypothesis completes the first `c` classes
    obtain ⟨P', hP'perf, hP'disj, hP'cnt, hP'used, hP'sum⟩ :=
      ih N'
        (fun j => hN j.castSucc)
        (fun j u v h => hNin j.castSucc u v h)
        (fun i j hij => hNdisj i.castSucc j.castSucc
          (fun h => hij (Fin.castSucc_injective c h)))
        (fun j => hU j.castSucc)
        (fun v => le_trans (missOf_castSucc_le N v) (hmiss v))
    have hmiss' : ∀ v, missOf N' v ≤ m := fun v => le_trans (missOf_castSucc_le N v) (hmiss v)
    -- the cross graph still available, and the forbidden set
    let Kl : SimpleGraph (Fin n) := remaining K₀ P'
    let Fz : Finset (Fin n) := Finset.univ.filter fun v => L ≤ cntOf N' P' v
    -- the numerical inputs of the step
    have hFzcard : Fz.card ≤ 5 * n * m / L := cardHeavyLe N' P' hL hmiss' hP'sum
    have hused' : ∀ v, (usedNbrs K₀ P' v).card ≤ m + L := by
      intro v
      have h1 := hP'used v
      have h2 := hP'cnt v
      have h3 := hmiss' v
      omega
    have hlr' : Work.Deep.GKO.BipLowerReg Kl A B (q / 2) ε :=
      bipLowerRegRemaining A B K₀ P' hq hlr hroomq hused'
    have hdeg' : ∀ v, D₀ - (m + L) - Fz.card ≤ Work.Deep.GKO.degIn Kl v (Finset.univ \ Fz) :=
      degInRemainingNeighbors K₀ P' Fz hdeg0 hused'
    have hroom' : ε * (n : ℝ) + ((2 * Fz.card + 14 * s : ℕ) : ℝ)
        < ((D₀ - (m + L) - Fz.card : ℕ) : ℝ) :=
      roomRemaining hFzcard hroomD
    have hKbip' : ∀ u v, Kl.Adj u v → (u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A) := by
      intro u v huv
      exact hKbip u v (remaining_le K₀ P' huv)
    -- N5b completes the last class
    obtain ⟨Pl, hPlperf, hPlforb, hPlcard⟩ :=
      completeInsideMatching A B hAB hcov hcard Nl Kl (hN (Fin.last c)) (hNin (Fin.last c))
        hKbip' Fz (by linarith : (0 : ℝ) < q / 2) hε hlr' (hU (Fin.last c)) hdeg' hroom'
    -- the registers of the extended family
    have hcnt_last : ∀ v, cntOf N (Fin.snoc P' Pl) v ≤ L := by
      intro v
      rw [← hNsnoc, cntOf_snoc_ind]
      by_cases hv : L ≤ cntOf N' P' v
      · have hnot : ¬ (v ∉ uncov Nl ∧ Rematched Nl Pl v) := by
          rintro ⟨hvu, hrem⟩
          exact hPlforb v (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩) hvu hrem
        rw [rematchInd_eq_zero hnot]
        simpa using hP'cnt v
      · have hlt : cntOf N' P' v < L := lt_of_not_ge hv
        have h1 := rematchInd_le_one Nl Pl v
        omega
    have hused_last : ∀ v, (usedNbrs K₀ (Fin.snoc P' Pl) v).card
        ≤ missOf N v + cntOf N (Fin.snoc P' Pl) v := by
      intro v
      rw [← hNsnoc, missOf_add_cntOf_snoc_ind]
      have hmatch : Work.Deep.GKO.IsMatching' Pl := IsPerfectMatching'.isMatching' hPlperf
      have h2 : useCount K₀ Pl v ≤ crossUseInd Nl Pl v :=
        lastClassIndicator A B hAB (fun u v h => hNin (Fin.last c) u v h)
          (fun u v h => hKbip u v h) hmatch v
      calc (usedNbrs K₀ (Fin.snoc P' Pl) v).card
          ≤ (usedNbrs K₀ P' v).card + useCount K₀ Pl v := usedNbrs_snoc_card_le K₀ P' Pl v
        _ ≤ (missOf N' v + cntOf N' P' v) + crossUseInd Nl Pl v := by
              have h1 := hP'used v
              omega
    have hlast_sum : (∑ v, rematchInd Nl Pl v) ≤ 5 * (uncov Nl).card := by
      rw [sum_rematchInd_eq_ncard]
      exact hPlcard
    have hsum_last : (∑ v, cntOf N (Fin.snoc P' Pl) v) ≤ 5 * ∑ j, (uncov (N j)).card := by
      have hUnivSplit : (∑ j : Fin (c + 1), (uncov (N j)).card)
          = (∑ j : Fin c, (uncov (N' j)).card) + (uncov Nl).card := by
        rw [Fin.sum_univ_castSucc]
      rw [hUnivSplit]
      have hsplit : (∑ v, cntOf N (Fin.snoc P' Pl) v)
          = (∑ v, cntOf N' P' v) + ∑ v, rematchInd Nl Pl v := by
        rw [← hNsnoc]
        rw [Finset.sum_congr rfl (fun v _ => cntOf_snoc_ind N' Nl P' Pl v)]
        exact Finset.sum_add_distrib
      rw [hsplit]
      calc (∑ v, cntOf N' P' v) + (∑ v, rematchInd Nl Pl v)
          ≤ 5 * (∑ j, (uncov (N' j)).card) + 5 * (uncov Nl).card :=
            add_le_add hP'sum hlast_sum
        _ = 5 * ((∑ j, (uncov (N' j)).card) + (uncov Nl).card) := by ring
    refine ⟨Fin.snoc P' Pl, ?_, ?_, hcnt_last, hused_last, hsum_last⟩
    · -- clause 1: perfect matchings
      intro j
      rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
      · simp only [Fin.snoc_castSucc]; exact hP'perf j'
      · simp only [Fin.snoc_last]
        exact ⟨le_trans hPlperf.1 (sup_le_sup_right_aux (remaining_le K₀ P')), hPlperf.2⟩
    · -- clause 2: pairwise edge-disjointness
      intro i j hij
      rw [disjoint_edgeSet_iff]
      intro u v hiu hjv
      rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
      · rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
        · simp only [Fin.snoc_castSucc, Fin.snoc_castSucc] at hiu hjv
          exact (disjoint_edgeSet_iff.mp (hP'disj i' j' (fun h => hij (by rw [h])))) u v hiu hjv
        · simp only [Fin.snoc_castSucc] at hiu
          simp only [Fin.snoc_last] at hjv
          have hKl_used : ∀ x y, Kl.Adj x y → ¬ (P' i').Adj x y := by
            intro x y hxy hxy'
            exact ((remaining_adj K₀ P' x y).mp hxy).2 (mem_usedEdges.mpr ⟨i', hxy'⟩)
          have hNNl : ∀ x y, (N' i').Adj x y → ¬ Nl.Adj x y :=
            (disjoint_edgeSet_iff.mp (hNdisj i'.castSucc (Fin.last c)
              (Fin.castSucc_ne_last i')))
          exact not_adj_of_used hAB hcov (fun x y h => hNin i'.castSucc x y h)
            (fun x y h => hNin (Fin.last c) x y h) (fun x y h => hKbip x y h)
            (fun x y h => remaining_le K₀ P' h) hKl_used (hP'perf i').1 hPlperf.1 hNNl hiu hjv
      · simp only [Fin.snoc_last] at hiu
        rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
        · simp only [Fin.snoc_castSucc] at hjv
          have hKl_used : ∀ x y, Kl.Adj x y → ¬ (P' j').Adj x y := by
            intro x y hxy hxy'
            exact ((remaining_adj K₀ P' x y).mp hxy).2 (mem_usedEdges.mpr ⟨j', hxy'⟩)
          have hNNl : ∀ x y, (N' j').Adj x y → ¬ Nl.Adj x y :=
            (disjoint_edgeSet_iff.mp (hNdisj j'.castSucc (Fin.last c)
              (Fin.castSucc_ne_last j')))
          exact not_adj_of_used hAB hcov (fun x y h => hNin j'.castSucc x y h)
            (fun x y h => hNin (Fin.last c) x y h) (fun x y h => hKbip x y h)
            (fun x y h => remaining_le K₀ P' h) hKl_used (hP'perf j').1 hPlperf.1 hNNl hjv hiu
        · exact absurd rfl hij

end

theorem completeAllClasses {n : ℕ} (A B : Finset (Fin n)) (hAB : Disjoint A B)
    (hcov : A ∪ B = Finset.univ) (hcard : A.card = B.card)
    {c : ℕ} (N : Fin c → SimpleGraph (Fin n)) (hN : ∀ j, Work.Deep.GKO.IsMatching' (N j))
    (hNin : ∀ j u v, (N j).Adj u v → (u ∈ A ∧ v ∈ A) ∨ (u ∈ B ∧ v ∈ B))
    (hNdisj : ∀ i j, i ≠ j → Disjoint (N i).edgeSet (N j).edgeSet)
    (K₀ : SimpleGraph (Fin n))
    (hKbip : ∀ u v, K₀.Adj u v → (u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A))
    {q ε : ℝ} {s m L D₀ : ℕ} (hq : 0 < q) (hε : 0 < ε) (hL : 0 < L)
    (hlr : Work.Deep.GKO.BipLowerReg K₀ A B q ε)
    (hU : ∀ j, (Work.Deep.GKO.OneFact.N5.uncov (N j)).card ≤ s)
    (hmiss : ∀ v, (Finset.univ.filter fun j => v ∈ Work.Deep.GKO.OneFact.N5.uncov (N j)).card ≤ m)
    (hdeg : ∀ v, D₀ ≤ Nat.card (K₀.neighborSet v))
    (hroomq : ((m + L : ℕ) : ℝ) ≤ q * ε * (n : ℝ) / 2)
    (hroomD : ε * (n : ℝ) + ((3 * (5 * n * m / L) + 14 * s + m + L + 1 : ℕ) : ℝ) < (D₀ : ℝ)) :
    ∃ P : Fin c → SimpleGraph (Fin n),
      (∀ j, Work.Deep.GKO.IsPerfectMatching' (N j ⊔ K₀) (P j)) ∧
      (∀ i j, i ≠ j → Disjoint (P i).edgeSet (P j).edgeSet) ∧
      (∀ v, ({j : Fin c | v ∉ Work.Deep.GKO.OneFact.N5.uncov (N j) ∧
        Work.Deep.GKO.OneFact.N5.Rematched (N j) (P j) v} : Set (Fin c)).ncard ≤ L)
:= by
  obtain ⟨P, h1, h2, h3, -, -⟩ :=
    completeAllClassesAux A B hAB hcov hcard K₀ hKbip hq hε hL hlr hdeg hroomq hroomD
      c N hN hNin hNdisj hU hmiss
  exact ⟨P, h1, h2, fun v => by rw [ncard_cntOf]; exact h3 v⟩

end Work.Deep.GKO.OneFact.N5
