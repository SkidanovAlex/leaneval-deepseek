/-
# Applying the Lovász Local Lemma to coordinate-local events of the random colouring

This module packages the Lovász Local Lemma (`Submission.Work.Deep.Sparse.lll_main`) together
with the independence of events on disjoint coordinates
(`Submission.Work.Deep.Sparse.prob_indep`) into the form used by the naive colouring
procedure: a finite family of "bad" events on the uniform colouring space `V → Fin k`, each
determined by the colours of a bounded set `Ball i` of vertices, with a uniform bound `p` on
their probabilities and a bound `X` on the number of events whose balls meet `Ball i`, is
avoided by some colouring as soon as `4p(X+1) ≤ 1`.
-/
import Submission.Work.Deep.Sparse.Prelude
import Submission.Work.Deep.Sparse.ProbBasic
import Submission.Work.Deep.Sparse.prob_indep
import Submission.Work.Deep.Sparse.lll_main

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.Deep.Sparse

/-- **The Lovász Local Lemma for coordinate-local events.**  If every bad event `A i` is
determined by the colours on `Ball i`, at most `X` balls meet the ball of `i` (for every `i`),
every `A i` has probability at most `p`, and `4p(X+1) ≤ 1`, then some colouring avoids all of
them. -/
theorem lll_apply {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ} [Nonempty (V → Fin k)]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A : ι → Set (V → Fin k)) (Ball : ι → Finset V)
    (X : ℕ) (p : ℝ)
    (hdet : ∀ i (f g : V → Fin k), (∀ v ∈ Ball i, f v = g v) → (f ∈ A i ↔ g ∈ A i))
    (hcard : ∀ i, (Finset.univ.filter (fun j : ι => (Ball i ∩ Ball j).Nonempty)).card ≤ X)
    (hprob : ∀ i, (colSpace (V := V) k).prob (A i) ≤ p)
    (hsmall : 4 * p * ((X : ℝ) + 1) ≤ 1) :
    ∃ f : V → Fin k, ∀ i, f ∉ A i := by
  classical
  by_cases hι : Nonempty ι
  · obtain ⟨i₀⟩ := hι
    have hp0 : 0 ≤ p := le_trans (FinSpace.prob_nonneg _ _) (hprob i₀)
    set Dep : ι → Finset ι :=
      fun i => insert i (Finset.univ.filter (fun j : ι => (Ball i ∩ Ball j).Nonempty)) with hDep
    have hpos : 0 < (colSpace (V := V) k).prob (⋂ i, (A i)ᶜ) := by
      refine lll_main (colSpace (V := V) k) A Dep p (fun i => ?_) hp0 hprob ?_ ?_
      · exact Finset.mem_insert_self i _
      · -- independence of `A i` from the complements of far events
        intro i T hdisj
        have hfar : ∀ j ∈ T, Disjoint (Ball i) (Ball j) := by
          intro j hj
          have hj' : j ∉ Dep i := Finset.disjoint_left.mp hdisj hj
          rw [hDep, Finset.mem_insert, not_or] at hj'
          rw [Finset.disjoint_iff_inter_eq_empty]
          by_contra hne
          exact hj'.2 (by
            rw [Finset.mem_filter]
            exact ⟨Finset.mem_univ j, Finset.nonempty_iff_ne_empty.mpr hne⟩)
        have hST : Disjoint (Ball i) (T.biUnion Ball) := by
          rw [Finset.disjoint_biUnion_right]
          exact hfar
        have hE : ∀ f g : V → Fin k, (∀ v ∈ Ball i, f v = g v) → (f ∈ A i ↔ g ∈ A i) :=
          hdet i
        have hE' : ∀ f g : V → Fin k, (∀ v ∈ T.biUnion Ball, f v = g v) →
            (f ∈ ⋂ j ∈ T, (A j)ᶜ ↔ g ∈ ⋂ j ∈ T, (A j)ᶜ) := by
          intro f g hagree
          simp only [Set.mem_iInter, Set.mem_compl_iff]
          constructor
          · intro h j hj
            rw [← hdet j f g (fun v hv => hagree v (Finset.mem_biUnion.mpr ⟨j, hj, hv⟩))]
            exact h j hj
          · intro h j hj
            rw [hdet j f g (fun v hv => hagree v (Finset.mem_biUnion.mpr ⟨j, hj, hv⟩))]
            exact h j hj
        exact prob_indep hST hE hE'
      · -- the smallness condition for `lll_main`
        intro i
        have h1 : ((Dep i).card : ℝ) ≤ (X : ℝ) + 1 := by
          have hle : (Dep i).card ≤ X + 1 := by
            rw [hDep]
            refine le_trans (Finset.card_insert_le _ _) ?_
            have := hcard i
            omega
          exact_mod_cast hle
        have h2 : (0 : ℝ) ≤ 4 * p := by linarith
        calc 4 * p * ((Dep i).card : ℝ) ≤ 4 * p * ((X : ℝ) + 1) :=
              mul_le_mul_of_nonneg_left h1 h2
          _ ≤ 1 := hsmall
    obtain ⟨f, hf⟩ := FinSpace.exists_of_prob_pos _ hpos
    exact ⟨f, fun i => Set.mem_iInter.mp hf i⟩
  · refine ⟨Classical.arbitrary (V → Fin k), fun i => ?_⟩
    exact absurd ⟨i⟩ hι

end Work.Deep.Sparse
