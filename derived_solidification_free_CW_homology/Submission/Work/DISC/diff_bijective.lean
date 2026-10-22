import Mathlib
import Submission.Work.DISC.Defs

namespace Work.DISC

namespace NullSeq

variable {S : LightProfinite.{0}} {M : ModuleCat.{0} ℤ}

/-- Telescoping identity for the difference of consecutive terms: the sum of the differences
`b_{n+k} - b_{n+k+1}` collapses to `b_n - b_{n+N}`. -/
lemma sum_range_diff_apply (b : NullSeq S M) (n N : ℕ) :
    ∑ k ∈ Finset.range N, (b.1 (n + k) - b.1 (n + (k + 1))) =
      b.1 (n + 0) - b.1 (n + N) :=
  Finset.sum_range_sub' (fun k => b.1 (n + k)) N

/-- If a null sequence `a` satisfies `a_m = a_{m+1}` for all `m ≥ N`, then `a` already vanishes
for all `m ≥ N`: the values of `a` above `N` are eventually constant, and they are eventually
`0`. -/
lemma eq_zero_of_forall_ge (a : NullSeq S M) (N : ℕ)
    (h : ∀ m ≥ N, a.1 m = a.1 (m + 1)) : ∀ n ≥ N, a.1 n = 0 := by
  intro n hn
  rcases Nat.lt_or_ge n a.bound with hnM | hnM
  · have hchain : ∀ k, a.1 n = a.1 (n + k) := by
      intro k
      induction k with
      | zero => rw [Nat.add_zero]
      | succ k ih => rw [ih, h (n + k) (by omega), show n + k + 1 = n + (k + 1) by omega]
    rw [hchain (a.bound - n), show n + (a.bound - n) = a.bound by omega]
    exact a.bound_spec a.bound le_rfl
  · exact a.bound_spec n hnM

/-- `tailSum` is a left inverse of the difference map on null sequences. -/
lemma tailSum_diff (a : NullSeq S M) : tailSum (diff a) = a := by
  apply Subtype.ext
  funext n
  show (∑ k ∈ Finset.range (diff a).bound, (a.1 (n + k) - a.1 (n + (k + 1)))) = a.1 n
  have hN : ∀ m ≥ (diff a).bound, a.1 m = a.1 (m + 1) := by
    intro m hm
    exact sub_eq_zero.mp ((diff a).bound_spec m hm)
  have hz : a.1 (n + (diff a).bound) = 0 :=
    eq_zero_of_forall_ge a (diff a).bound hN (n + (diff a).bound) (by omega)
  rw [Finset.sum_range_sub']
  rw [Nat.add_zero, hz, sub_zero]

/-- `tailSum` is a right inverse of the difference map on null sequences. -/
lemma diff_tailSum (b : NullSeq S M) : diff (tailSum b) = b := by
  apply Subtype.ext
  funext n
  show (∑ k ∈ Finset.range b.bound, b.1 (n + k)) -
      (∑ k ∈ Finset.range b.bound, b.1 (n + 1 + k)) = b.1 n
  have hsecond : (∑ k ∈ Finset.range b.bound, b.1 (n + 1 + k)) =
      ∑ k ∈ Finset.range b.bound, b.1 (n + (k + 1)) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show n + 1 + k = n + (k + 1) by omega]
  rw [hsecond, ← Finset.sum_sub_distrib]
  rw [Finset.sum_range_sub']
  rw [Nat.add_zero, b.bound_spec (n + b.bound) (by omega), sub_zero]

end NullSeq

theorem diff_bijective (S : LightProfinite.{0}) (M : ModuleCat.{0} ℤ) :
    Function.Bijective (Work.DISC.NullSeq.diff (S := S) (M := M)) :=
  ⟨fun a b hab => by
    have h := congrArg (NullSeq.tailSum (S := S) (M := M)) hab
    rwa [NullSeq.tailSum_diff, NullSeq.tailSum_diff] at h,
   fun b => ⟨NullSeq.tailSum b, NullSeq.diff_tailSum b⟩⟩

end Work.DISC
