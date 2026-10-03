import Mathlib
import Submission.Work.FIArea4.Vflip.Vfd.farPre

/-!
# The dyadic regrouping of the flipped far sum (FI §12)

This module proves `far_sum_eq_dyadic`: the double sum

`Σ_{p,q ∈ boxF R S} GG a b α p q · BB D R S p q`

of the flipped far part, whose modulus sum `BB` runs over the fixed range `0 ≤ q' ≤ 4RS`
(intersected with the divisor conditions), is regrouped into the dyadic pieces
`InnerRangeI D R S a b α m (2^j) (2^(j+1))` of the flipped modulus `q'`, `0 ≤ j < 4RS`,
together with the single piece `InnerRangeI D R S a b α m 0 1` for `q' = 1`.

The combinatorial content is that the summand `farH D R S a b α m q'` (the `q'`-th slice of the
flipped sum, before summation over `q'`) vanishes for `q' = 0` and for `q' > 4RS`: the divisor
condition `m q' ∣ pairAbs p q` together with `0 < pairAbs p q ≤ 4RS` forces `1 ≤ q' ≤ 4RS`. Hence
the range `{0, …, 4RS}` may be replaced by the disjoint dyadic shells
`{1} ∪ ⋃_{j<4RS} (2^j, 2^(j+1)]`, which is the content of `dyadic_range_split`.
-/

namespace Work.FIArea4.Vflip.Vfd

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The `q'`-slice of the flipped far sum: the coefficient of the flipped modulus `q'` in
`reindex_far`, i.e. the sum over the pair `(p,q)` of the box of `GG · flipWeight` restricted by
the divisor conditions `0 < pairAbs`, `m ∣ pairC`, `m q' ∣ pairAbs`. -/
def farH (D R S : ℕ) (a b : ℝ) (α : ℕ → ℕ → ℂ) (m q' : ℕ) : ℂ :=
  ∑ p ∈ boxF R S, ∑ q ∈ boxF R S,
    (if 0 < pairAbs p.1 q.1 p.2 q.2 ∧ m ∣ pairC p.1 q.1 ∧ m * q' ∣ pairAbs p.1 q.1 p.2 q.2
     then GG a b α p q * flipWeight D q' p.1 p.2 q.1 q.2 else 0)

/-- **`InnerRangeI` is the sum of the `q'`-slices over the interval `Q₁ < q' ≤ Q₂`.** -/
lemma InnerRangeI_eq_sum_farH (D R S : ℕ) (a b : ℝ) (α : ℕ → ℕ → ℂ) (m Q1 Q2 : ℕ) :
    InnerRangeI D R S a b α m Q1 Q2 = ∑ q' ∈ Finset.Ioc Q1 Q2, farH D R S a b α m q' := by
  unfold InnerRangeI FarIdxI farH
  rw [Finset.sum_filter]
  simp only [Finset.sum_product]

/-- The `q'`-slice vanishes beyond `4RS`: `m q' ∣ pairAbs p q` and `0 < pairAbs p q ≤ 4RS` force
`q' ≤ 4RS`. -/
lemma farH_zero_of_gt (D R S : ℕ) (a b : ℝ) (α : ℕ → ℕ → ℂ) (m q' : ℕ)
    (hq' : 4 * R * S < q') : farH D R S a b α m q' = 0 := by
  unfold farH
  refine Finset.sum_eq_zero (fun p hp => Finset.sum_eq_zero (fun q hq => ?_))
  rw [if_neg]
  rintro ⟨hpa, hmc, hdvd⟩
  have hle : m * q' ≤ pairAbs p.1 q.1 p.2 q.2 := Nat.le_of_dvd hpa hdvd
  have hne : m * q' ≠ 0 := fun h => by
    rw [h] at hdvd
    exact absurd (Nat.eq_zero_of_zero_dvd hdvd) hpa.ne'
  have hmpos : 0 < m := Nat.pos_of_ne_zero (fun h => hne (by rw [h, zero_mul]))
  have h1 : q' ≤ m * q' := Nat.le_mul_of_pos_left q' hmpos
  have h2 := pairAbs_le_fourRS hp hq
  omega

/-- The `q' = 0` slice vanishes, since `0 ∣ pairAbs` is incompatible with `0 < pairAbs`. -/
lemma farH_zero_zero (D R S : ℕ) (a b : ℝ) (α : ℕ → ℕ → ℂ) (m : ℕ) :
    farH D R S a b α m 0 = 0 := by
  unfold farH
  refine Finset.sum_eq_zero (fun p hp => Finset.sum_eq_zero (fun q hq => ?_))
  rw [if_neg]
  rintro ⟨hpa, hmc, hdvd⟩
  rw [mul_zero] at hdvd
  exact absurd (Nat.eq_zero_of_zero_dvd hdvd) hpa.ne'

/-- **The dyadic shells tile the interval `1 < q' ≤ 2^N`**: the disjoint union of
`(2^j, 2^(j+1)]` for `0 ≤ j < N` is `(1, 2^N]`. -/
lemma dyadic_sum_Ioc (N : ℕ) (f : ℕ → ℂ) :
    ∑ j ∈ Finset.range N, ∑ q' ∈ Finset.Ioc (2^j) (2^(j+1)), f q'
      = ∑ q' ∈ Finset.Ioc 1 (2^N), f q' := by
  induction N with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have h2 : (2:ℕ)^(n+1) = (2:ℕ)^n + (2:ℕ)^n := by rw [pow_succ]; ring
      have hunion : Finset.Ioc 1 ((2:ℕ)^n) ∪ Finset.Ioc ((2:ℕ)^n) ((2:ℕ)^n + (2:ℕ)^n)
          = Finset.Ioc 1 ((2:ℕ)^n + (2:ℕ)^n) :=
        Finset.Ioc_union_Ioc_eq_Ioc (a := 1) (b := (2:ℕ)^n) (c := (2:ℕ)^n + (2:ℕ)^n)
          Nat.one_le_two_pow (Nat.le_add_right _ _)
      have hdisj : Disjoint (Finset.Ioc 1 ((2:ℕ)^n))
          (Finset.Ioc ((2:ℕ)^n) ((2:ℕ)^n + (2:ℕ)^n)) := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        rw [Finset.mem_Ioc] at hx1 hx2
        omega
      rw [h2, ← hunion, Finset.sum_union hdisj]

/-- **The dyadic regrouping of a range sum.** If `f 0 = 0` and `f` vanishes beyond `N`, then the
sum over `{0, …, N}` splits into the shells `(2^j, 2^(j+1)]`, `j < N`, of the `q' ≥ 2` part, plus
the single term `q' = 1`. -/
lemma dyadic_range_split (N : ℕ) (f : ℕ → ℂ) (h0 : f 0 = 0)
    (hN : ∀ q', N < q' → f q' = 0) :
    ∑ q' ∈ Finset.range (N+1), f q'
      = (∑ j ∈ Finset.range N, ∑ q' ∈ Finset.Ioc (2^j) (2^(j+1)), f q')
        + ∑ q' ∈ Finset.Ioc 0 1, f q' := by
  have hIoc01 : ∑ q' ∈ Finset.Ioc 0 1, f q' = f 1 := by
    have hset : Finset.Ioc 0 1 = ({1} : Finset ℕ) := by
      ext q; simp only [Finset.mem_Ioc, Finset.mem_singleton]; omega
    rw [hset, Finset.sum_singleton]
  have hrange : ∑ q' ∈ Finset.range (N+1), f q' = ∑ q' ∈ Finset.Ioc 0 N, f q' := by
    have hset : Finset.range (N+1) = insert 0 (Finset.Ioc 0 N) := by
      ext q; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioc]; omega
    rw [hset, Finset.sum_insert (by simp only [Finset.mem_Ioc]; omega), h0, zero_add]
  rw [hIoc01, hrange, dyadic_sum_Ioc N f]
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0
    simp only [pow_zero, Finset.Ioc_self, Finset.sum_empty, zero_add]
    exact (hN 1 (by norm_num)).symm
  · have hle1 : 1 ≤ N := hNpos
    have hNle : N ≤ 2^N := le_of_lt Nat.lt_two_pow_self
    have hsplit : Finset.Ioc 1 (2^N) = Finset.Ioc 1 N ∪ Finset.Ioc N (2^N) :=
      (Finset.Ioc_union_Ioc_eq_Ioc (a := 1) (b := N) (c := 2^N) hle1 hNle).symm
    have hdisj : Disjoint (Finset.Ioc 1 N) (Finset.Ioc N (2^N)) := by
      rw [Finset.disjoint_left]; intro x hx1 hx2; rw [Finset.mem_Ioc] at hx1 hx2; omega
    have hzero : ∑ q' ∈ Finset.Ioc N (2^N), f q' = 0 := by
      refine Finset.sum_eq_zero (fun q' hq' => ?_)
      rw [Finset.mem_Ioc] at hq'
      exact hN q' hq'.1
    rw [hsplit, Finset.sum_union hdisj, hzero, add_zero]
    have hset2 : Finset.Ioc 0 N = insert 1 (Finset.Ioc 1 N) := by
      ext q; simp only [Finset.mem_insert, Finset.mem_Ioc]; omega
    rw [hset2, Finset.sum_insert (by simp only [Finset.mem_Ioc]; omega), add_comm]

/-- **The reindexed far sum, in the `q'`-slice notation**: `reindex_far` with the inner pair sum
written as `farH`. -/
lemma far_sum_eq_reindex_farH (D R S : ℕ) (a b : ℝ) (α : ℕ → ℕ → ℂ) :
    (∑ p ∈ boxF R S, ∑ q ∈ boxF R S, GG a b α p q * BB D R S p q)
      = ∑ m ∈ Finset.range (2*R+1), (ArithmeticFunction.moebius m : ℂ) *
          ∑ q' ∈ Finset.range (4*R*S+1), farH D R S a b α m q' := by
  rw [reindex_far D R S a b α]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun q' hq' => rfl)

/-- **The dyadic split of the `q'`-sum for a fixed Möbius variable `m`.** -/
lemma far_dyadic_bracket (D R S : ℕ) (a b : ℝ) (α : ℕ → ℕ → ℂ) (m : ℕ) :
    (∑ q' ∈ Finset.range (4*R*S+1), farH D R S a b α m q')
      = (∑ j ∈ Finset.range (4*R*S), InnerRangeI D R S a b α m (2^j) (2^(j+1)))
        + InnerRangeI D R S a b α m 0 1 := by
  rw [dyadic_range_split (4*R*S) (farH D R S a b α m) (farH_zero_zero D R S a b α m)
      (fun q' hq' => farH_zero_of_gt D R S a b α m q' hq')]
  congr 1
  · exact Finset.sum_congr rfl
      (fun j _ => (InnerRangeI_eq_sum_farH D R S a b α m (2^j) (2^(j+1))).symm)
  · exact (InnerRangeI_eq_sum_farH D R S a b α m 0 1).symm

theorem far_sum_eq_dyadic (D R S : ℕ) (a b : ℝ) (α : ℕ → ℕ → ℂ) :
    (∑ p ∈ boxF R S, ∑ q ∈ boxF R S, GG a b α p q * BB D R S p q)
      = ∑ m ∈ Finset.range (2*R+1), (ArithmeticFunction.moebius m : ℂ) *
          (∑ j ∈ Finset.range (4*R*S), InnerRangeI D R S a b α m (2^j) (2^(j+1))
            + InnerRangeI D R S a b α m 0 1) := by
  rw [far_sum_eq_reindex_farH]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rw [far_dyadic_bracket D R S a b α m]

end

end Work.FIArea4.Vflip.Vfd
