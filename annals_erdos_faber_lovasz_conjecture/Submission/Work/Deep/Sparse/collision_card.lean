import Submission.Work.Deep.Sparse.Prelude
import Submission.Work.Deep.Sparse.ProbModel

open scoped BigOperators

namespace Work.Deep.Sparse

/-- The elementary identity `2 * C(n,2) = n * (n - 1)`. -/
private theorem two_mul_choose_two (n : ℕ) : 2 * n.choose 2 = n * (n - 1) := by
  rcases n with _ | m
  · decide
  · have h : (m + 1) * m = (m + 1).choose 2 * 2 := by
      simpa using Nat.add_one_mul_choose_eq m 1
    rw [Nat.add_sub_cancel]
    exact (Nat.mul_comm 2 ((m + 1).choose 2)).trans h.symm

/-- `n * n - n = 2 * C(n,2)`: the number of ordered pairs of distinct elements of an `n`-element
set, read as `(offDiag_card)` on the left and as twice a binomial coefficient on the right. -/
private theorem mul_self_sub_self (n : ℕ) : n * n - n = 2 * n.choose 2 := by
  rw [two_mul_choose_two, Nat.mul_sub, Nat.mul_one]

theorem collision_card {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {k : ℕ} (f : V → Fin k) (v : V) :
    (Work.Deep.Sparse.collisionPairs G f v).card
      = 2 * (Work.Deep.Sparse.ofColoring G f).pairTerm v := by
  classical
  -- The ordered pairs of distinct retained neighbours of `v` carrying a common colour split,
  -- over the colours `c`, into the off-diagonals of the colour classes
  -- `{x ∈ N(v) | Retained G f x ∧ f x = c}`.
  have hbridge : ∀ c : Fin k, colourClassCount G f v c
      = ((G.neighborFinset v).filter (fun x => Retained G f x ∧ f x = c)).card :=
    fun c => rfl
  have hdisj : ((Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint
      (fun c => ((G.neighborFinset v).filter (fun x => Retained G f x ∧ f x = c)).offDiag) := by
    intro c _ c' _ hcc'
    rw [Function.onFun, Finset.disjoint_left]
    intro p hp hp'
    have hf : f p.1 = c := (Finset.mem_filter.mp (Finset.mem_offDiag.mp hp).1).2.2
    have hf' : f p.1 = c' := (Finset.mem_filter.mp (Finset.mem_offDiag.mp hp').1).2.2
    exact hcc' (hf.symm.trans hf')
  have hunion : collisionPairs G f v =
      Finset.univ.disjiUnion
        (fun c => ((G.neighborFinset v).filter (fun x => Retained G f x ∧ f x = c)).offDiag)
        hdisj := by
    ext p
    rw [mem_collisionPairs, Finset.mem_disjiUnion]
    constructor
    · rintro ⟨h1, h2, h3, h4, h5, h6⟩
      refine ⟨f p.1, Finset.mem_univ _, Finset.mem_offDiag.mpr ⟨?_, ?_, h3⟩⟩
      · exact Finset.mem_filter.mpr ⟨h1, h4, rfl⟩
      · exact Finset.mem_filter.mpr ⟨h2, h5, h6.symm⟩
    · rintro ⟨c, -, hp⟩
      rw [Finset.mem_offDiag] at hp
      have hp1 := Finset.mem_filter.mp hp.1
      have hp2 := Finset.mem_filter.mp hp.2.1
      exact ⟨hp1.1, hp2.1, hp.2.2, hp1.2.1, hp2.2.1, hp1.2.2.trans hp2.2.2.symm⟩
  rw [hunion, Finset.card_disjiUnion, pairTerm_ofColoring G f v, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.offDiag_card, ← hbridge c]
  exact mul_self_sub_self _

end Work.Deep.Sparse
