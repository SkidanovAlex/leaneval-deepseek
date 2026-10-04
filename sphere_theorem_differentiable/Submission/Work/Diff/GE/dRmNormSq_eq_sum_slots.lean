import Mathlib
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.GE.NablaRm

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `|∇Rm|²` as a sum over the slots of `∇Rm`

`dRmNormSq g x` is defined (`Submission/Diff/Grad.lean`) as the sum of the squares of the
components of `∇Rm` in the chosen orthonormal frame `onFrame g x`:

`dRmNormSq g x = ∑ m, ∑ i, ∑ j, ∑ k, ∑ l, (covRm g x (e m) (e i) (e j) (e k) (e l)) ^ 2`.

The `(0,5)`-tensor `∇Rm` is symmetric in nothing, but the *sum over all slots* only depends on the
set of the five arguments, not on the order in which they are listed: every slot ranges over the
full frame `e` independently.  This file records the elementary combinatorial fact that the
five-fold iterated sum is invariant under the cyclic rotation of the argument slots
`(a,b,c,d,e) ↦ (b,c,d,a,e)` (`sum5_slot_perm`), and applies it to rewrite `dRmNormSq` in the
argument order used by the gradient-estimate development.
-/

namespace Work.Diff.GE

open Finset
open scoped BigOperators

/-- Commutativity of a two-fold sum over a common finite index type. -/
private lemma sum_rot2 {ι : Type*} [Fintype ι] {β : Type*} [AddCommMonoid β]
    (X : ι → ι → β) : (∑ a, ∑ b, X a b) = ∑ b, ∑ a, X a b :=
  Finset.sum_comm

/-- The first index of a three-fold sum may be moved to the innermost position. -/
private lemma sum_rot3 {ι : Type*} [Fintype ι] {β : Type*} [AddCommMonoid β]
    (X : ι → ι → ι → β) : (∑ a, ∑ b, ∑ c, X a b c) = ∑ b, ∑ c, ∑ a, X a b c := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun b _ => sum_rot2 (fun a c => X a b c))

/-- The first index of a four-fold sum may be moved to the innermost position. -/
private lemma sum_rot4 {ι : Type*} [Fintype ι] {β : Type*} [AddCommMonoid β]
    (X : ι → ι → ι → ι → β) :
    (∑ a, ∑ b, ∑ c, ∑ d, X a b c d) = ∑ b, ∑ c, ∑ d, ∑ a, X a b c d := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun b _ => sum_rot3 (fun a c d => X a b c d))

/-- The first index of a five-fold sum may be moved to the innermost position. -/
private lemma sum_rot5 {ι : Type*} [Fintype ι] {β : Type*} [AddCommMonoid β]
    (X : ι → ι → ι → ι → ι → β) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, X a b c d e) = ∑ b, ∑ c, ∑ d, ∑ e, ∑ a, X a b c d e := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun b _ => sum_rot4 (fun a c d e => X a b c d e))

/-- **Slot reindexing of a five-fold sum.**  The five-fold iterated sum over a common index type
of a `(0,5)`-tensor is invariant under the cyclic rotation of its argument slots
`(a,b,c,d,e) ↦ (b,c,d,a,e)`: each slot ranges independently over the whole index set, so only the
*set* of arguments matters, not the position each occupies in the argument list.  The statement is
the change of variables `(k,i,j,l,m) ↦ (i,j,l,k,m)` in the summation indices. -/
theorem sum5_slot_perm {n : ℕ} (h : Fin n → Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ k, ∑ i, ∑ j, ∑ l, ∑ m, h i j l k m)
      = ∑ m, ∑ i, ∑ j, ∑ k, ∑ l, h m i j k l := by
  -- Both sides are the same five-fold sum, read with the argument slots `(b,c,d,a,e)` resp.
  -- `(a,b,c,d,e)`; these two bound-variable patterns are `rfl`-equal.
  have hA : (∑ k, ∑ i, ∑ j, ∑ l, ∑ m, h i j l k m)
      = ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, h b c d a e := rfl
  have hB : (∑ m, ∑ i, ∑ j, ∑ k, ∑ l, h m i j k l)
      = ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, h a b c d e := rfl
  rw [hA, hB]
  -- Move the outermost summation index to the position of the fourth slot and swap the last two.
  trans ∑ b, ∑ c, ∑ d, ∑ a, ∑ e, h b c d a e
  · rw [sum_rot5 (fun a b c d e => h b c d a e)]
    refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ =>
      Finset.sum_congr rfl (fun d _ => ?_)))
    exact sum_rot2 (fun e a => h b c d a e)
  · rfl

/-- The squared norm `dRmNormSq g x = |∇Rm|²` may be computed with the argument slots of `covRm`
listed in the order `(i, j, l, k, m)` and with any nesting of the five sums: since every slot of
`∇Rm` ranges over the whole frame `onFrame g x` independently, the order in which the slots are
enumerated is immaterial. -/
theorem dRmNormSq_eq_sum_slots
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M]
    (g : Submission.Diff.SMet I M) (x : M) :
    (∑ k, ∑ i, ∑ j, ∑ l, ∑ m,
        (Submission.Diff.covRm g x (Submission.Diff.onFrame g x i)
          (Submission.Diff.onFrame g x j) (Submission.Diff.onFrame g x l)
          (Submission.Diff.onFrame g x k) (Submission.Diff.onFrame g x m)) ^ 2)
      = Submission.Diff.dRmNormSq g x := by
  exact sum5_slot_perm (n := Module.finrank ℝ E)
      (fun a b c d e => (Submission.Diff.covRm g x (Submission.Diff.onFrame g x a)
        (Submission.Diff.onFrame g x b) (Submission.Diff.onFrame g x c)
        (Submission.Diff.onFrame g x d) (Submission.Diff.onFrame g x e)) ^ 2)

end Work.Diff.GE
