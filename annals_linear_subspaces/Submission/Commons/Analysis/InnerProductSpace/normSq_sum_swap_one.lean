import Mathlib
import Submission.Commons.Analysis.InnerProductSpace.wedge_replace_inner
import Submission.Commons.Analysis.InnerProductSpace.normSq_sum_of_pairwise_orthogonal

namespace Commons.Analysis.InnerProductSpace

lemma normSq_sum_swap_one {k : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (e c : Fin k → E) (he : Orthonormal ℝ e)
    (hc : ∀ i j : Fin k, inner ℝ (e i) (c j) = 0) :
    ‖(Finset.univ : Finset (Fin k)).sum (fun j : Fin k =>
        exteriorPower.ιMulti ℝ k (fun r : Fin k => if r = j then c j else e r))‖ ^ 2 =
      (Finset.univ : Finset (Fin k)).sum (fun j : Fin k => ‖c j‖ ^ 2) := by
  classical
  -- `w j` is the decomposable element obtained from the orthonormal family `e` by
  -- replacing the `j`-th entry with `c j`.
  let w : Fin k → ⋀[ℝ]^k E := fun j =>
    exteriorPower.ιMulti ℝ k (fun r : Fin k => if r = j then c j else e r)
  -- The vectors `w i` are pairwise orthogonal: for `i ≠ j`, the wedge products have
  -- disjoint orthonormal structure, so their inner product vanishes.
  have horth : Pairwise (fun i j : Fin k => inner ℝ (w i) (w j) = 0) := by
    intro i j hij
    dsimp [w]
    rw [wedge_replace_inner e he (i := i) (i' := j) (g := c i) (h := c j)]
    · rw [if_neg hij]
    · intro r
      rw [real_inner_comm]
      exact hc r i
    · intro r
      rw [real_inner_comm]
      exact hc r j
  calc
    ‖(Finset.univ : Finset (Fin k)).sum (fun j : Fin k =>
        exteriorPower.ιMulti ℝ k (fun r : Fin k => if r = j then c j else e r))‖ ^ 2
        = ‖(Finset.univ : Finset (Fin k)).sum w‖ ^ 2 := by simp [w]
    _ = (Finset.univ : Finset (Fin k)).sum (fun j : Fin k => ‖w j‖ ^ 2) := by
          exact normSq_sum_of_pairwise_orthogonal w horth
    _ = (Finset.univ : Finset (Fin k)).sum (fun j : Fin k => ‖c j‖ ^ 2) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          -- the norm of the `j`-th wedge product is the norm of `c j`, because all
          -- `e r` are orthonormal unit vectors orthogonal to `c j`
          dsimp [w]
          rw [← real_inner_self_eq_norm_sq]
          rw [wedge_replace_inner e he (i := j) (i' := j) (g := c j) (h := c j)]
          · rw [if_pos rfl, real_inner_self_eq_norm_sq]
          · intro r
            rw [real_inner_comm]
            exact hc r j
          · intro r
            rw [real_inner_comm]
            exact hc r j

end Commons.Analysis.InnerProductSpace
