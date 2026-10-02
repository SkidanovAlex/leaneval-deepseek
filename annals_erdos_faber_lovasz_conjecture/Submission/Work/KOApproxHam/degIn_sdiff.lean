import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.RegVocab

namespace Work.KOApproxHam

/-- Deleting a subgraph subtracts the degree: for `M ≤ G`, the number of neighbours of `v` in `B`
inside `G \ M` is the number of those in `G` minus the number of those in `M`. -/
theorem degIn_sdiff {n : ℕ} {G M : SimpleGraph (Fin n)} (hMG : M ≤ G) (v : Fin n)
    (B : Finset (Fin n)) :
    Work.Deep.GKO.degIn (G \ M) v B
      = Work.Deep.GKO.degIn G v B - Work.Deep.GKO.degIn M v B := by
  classical
  -- It suffices to prove the *additive* identity `deg_G = deg_M + deg_{G \ M}`: the subtraction
  -- on `ℕ` is then exact (`omega`), the truncation never being active because `M ≤ G` makes the
  -- neighbours of `v` in `M` a subset of those in `G`.
  have key : Work.Deep.GKO.degIn G v B
      = Work.Deep.GKO.degIn M v B + Work.Deep.GKO.degIn (G \ M) v B := by
    simp only [Work.Deep.GKO.degIn, Work.Deep.GKO.nbrFinset, Finset.card_filter]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases hG : G.Adj v y
    · by_cases hM : M.Adj v y <;> simp_all [SimpleGraph.sdiff_adj]
    · have hM : ¬ M.Adj v y := fun h => hG (hMG h)
      simp [hG, hM, SimpleGraph.sdiff_adj]
  omega

end Work.KOApproxHam
