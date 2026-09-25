import Mathlib
import Submission.NK.Chebotarev.Basic
import Submission.Commons.NumberTheory.NumberField.Set.summable_primeIdealZetaSum
import Submission.Commons.NumberTheory.NumberField.Set.primeIdealZetaSum_union_of_disjoint

/-!
# Sets of primes differing finitely have comparable prime-ideal zeta sums

If two sets `S`, `T` of finite places of a number field `K` differ in only finitely many
primes, then the difference of their prime-ideal zeta sums stays bounded as `s → 1⁺`:

`∑_{𝔭 ∈ S} N𝔭^{-s} - ∑_{𝔭 ∈ T} N𝔭^{-s} = O(1)`.

Indeed, for `s > 1` both series converge, and splitting `S = (S ∩ T) ⊔ (S \ T)` and
`T = (S ∩ T) ⊔ (T \ S)` shows that the difference equals
`∑_{𝔭 ∈ S \ T} N𝔭^{-s} - ∑_{𝔭 ∈ T \ S} N𝔭^{-s}`, a difference of two sums over the finite set
`(S \ T) ∪ (T \ S)`, hence bounded in absolute value by twice its cardinality.
-/

namespace NK.Chebotarev

open Filter Asymptotics

theorem isBigO_primeIdealZetaSum_sub_of_finite_diff {K : Type*} [Field K] [NumberField K]
    {S T : Set (NK.Chebotarev.PrimeIdeal K)} (h : (S \ T ∪ T \ S).Finite) :
    (fun s : ℝ => NumberField.Set.primeIdealZetaSum S s -
      NumberField.Set.primeIdealZetaSum T s)
      =O[nhdsWithin (1 : ℝ) (Set.Ioi 1)] (fun _ : ℝ => (1 : ℝ)) := by
  classical
  have hSTfin : (S \ T).Finite := h.subset Set.subset_union_left
  have hTSfin : (T \ S).Finite := h.subset Set.subset_union_right
  -- For `s > 1` the two series converge, and the common part `S ∩ T` cancels.
  have hsplit : ∀ s : ℝ, 1 < s →
      NumberField.Set.primeIdealZetaSum S s - NumberField.Set.primeIdealZetaSum T s
        = NumberField.Set.primeIdealZetaSum (S \ T) s
          - NumberField.Set.primeIdealZetaSum (T \ S) s := by
    intro s hs
    have hsum : Summable (fun 𝔭 : PrimeIdeal K =>
        (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) :=
      Commons.NumberTheory.NumberField.Set.summable_primeIdealZetaSum hs
    have hdisjS : Disjoint (S ∩ T) (S \ T) := by
      rw [Set.disjoint_left]
      intro x hx hx'
      exact hx'.2 hx.2
    have hdisjT : Disjoint (S ∩ T) (T \ S) := by
      rw [Set.disjoint_left]
      intro x hx hx'
      exact hx'.2 hx.1
    have hS : NumberField.Set.primeIdealZetaSum S s
        = NumberField.Set.primeIdealZetaSum (S ∩ T) s
          + NumberField.Set.primeIdealZetaSum (S \ T) s := by
      conv_lhs => rw [← Set.inter_union_sdiff (s := S) (t := T)]
      exact Commons.NumberTheory.NumberField.Set.primeIdealZetaSum_union_of_disjoint hdisjS s
        (hsum.subtype (· ∈ S ∩ T)) (hsum.subtype (· ∈ S \ T))
    have hT : NumberField.Set.primeIdealZetaSum T s
        = NumberField.Set.primeIdealZetaSum (S ∩ T) s
          + NumberField.Set.primeIdealZetaSum (T \ S) s := by
      conv_lhs => rw [← Set.inter_union_sdiff (s := T) (t := S), Set.inter_comm T S]
      exact Commons.NumberTheory.NumberField.Set.primeIdealZetaSum_union_of_disjoint hdisjT s
        (hsum.subtype (· ∈ S ∩ T)) (hsum.subtype (· ∈ T \ S))
    rw [hS, hT]
    ring
  refine IsBigO.of_bound (2 * ((S \ T ∪ T \ S).ncard : ℝ)) ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs1 : (1 : ℝ) < s := hs
  rw [hsplit s hs1, norm_one, mul_one]
  have hx : ‖NumberField.Set.primeIdealZetaSum (S \ T) s‖ ≤ ((S \ T ∪ T \ S).ncard : ℝ) := by
    rw [Real.norm_of_nonneg (NumberField.Set.primeIdealZetaSum_nonneg (S \ T) s)]
    calc NumberField.Set.primeIdealZetaSum (S \ T) s ≤ ((S \ T).ncard : ℝ) :=
          NumberField.Set.primeIdealZetaSum_le_card_of_finite hSTfin (by linarith)
      _ ≤ ((S \ T ∪ T \ S).ncard : ℝ) := by
          exact_mod_cast Set.ncard_le_ncard Set.subset_union_left h
  have hy : ‖NumberField.Set.primeIdealZetaSum (T \ S) s‖ ≤ ((S \ T ∪ T \ S).ncard : ℝ) := by
    rw [Real.norm_of_nonneg (NumberField.Set.primeIdealZetaSum_nonneg (T \ S) s)]
    calc NumberField.Set.primeIdealZetaSum (T \ S) s ≤ ((T \ S).ncard : ℝ) :=
          NumberField.Set.primeIdealZetaSum_le_card_of_finite hTSfin (by linarith)
      _ ≤ ((S \ T ∪ T \ S).ncard : ℝ) := by
          exact_mod_cast Set.ncard_le_ncard Set.subset_union_right h
  calc ‖NumberField.Set.primeIdealZetaSum (S \ T) s
        - NumberField.Set.primeIdealZetaSum (T \ S) s‖
      ≤ ‖NumberField.Set.primeIdealZetaSum (S \ T) s‖
        + ‖NumberField.Set.primeIdealZetaSum (T \ S) s‖ := norm_sub_le _ _
    _ ≤ ((S \ T ∪ T \ S).ncard : ℝ) + ((S \ T ∪ T \ S).ncard : ℝ) := add_le_add hx hy
    _ = 2 * ((S \ T ∪ T \ S).ncard : ℝ) := by ring

end NK.Chebotarev
