import Mathlib
import Submission.Work.Diff.STE.Torus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE

/-- Power-mean (Jensen) inequality for a finite family of nonnegative reals, in the shape used
below: the `k`-th power of the sum is at most `m ^ (k - 1)` times the sum of the `k`-th powers,
where `m` is the number of terms.  (Special case of `pow_sum_le_card_mul_sum_pow`.) -/
lemma sum_pow_le_card_pow_mul_sum_pow {ι : Type*} [Fintype ι] (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i)
    {k : ℕ} (hk : 1 ≤ k) :
    (∑ i, x i) ^ k ≤ (((Fintype.card ι : ℕ) : ℝ)) ^ (k - 1) * ∑ i, x i ^ k := by
  have h := pow_sum_le_card_mul_sum_pow (s := Finset.univ) (f := x) (fun i _ => hx i) (k - 1)
  simpa only [Finset.card_univ, Nat.sub_add_cancel hk] using h

/-- For `x i ≥ 0`, the `k`-th power of `1 + ∑ x i` is at most `(card ι + 1) ^ k (1 + ∑ (x i) ^ k)`.

This is the power-mean inequality applied to the `card ι + 1` nonnegative numbers
`1, x i` (`i : ι`): the arithmetic mean of these numbers is `(1 + ∑ x i) / (card ι + 1)`, and
their power mean of order `k` is at least it, giving
`(1 + ∑ x i) ^ k ≤ (card ι + 1) ^ (k - 1) (1 + ∑ (x i) ^ k) ≤ (card ι + 1) ^ k (1 + ∑ (x i) ^ k)`. -/
theorem one_add_sum_pow_le {ι : Type*} [Fintype ι] (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (k : ℕ) :
    (1 + ∑ i, x i) ^ k ≤ (((Fintype.card ι : ℕ) : ℝ) + 1) ^ k * (1 + ∑ i, x i ^ k) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · -- `k = 0`: both sides are positive constants, and `1 ≤ 1 + card ι`.
    subst hk
    simp only [pow_zero, one_mul]
    have h : (0 : ℝ) ≤ ∑ _i : ι, (1 : ℝ) := Finset.sum_nonneg (fun i _ => zero_le_one)
    linarith
  · -- `k ≥ 1`: add the extra term `1` as a term of the family, over `Unit ⊕ ι`.
    let F : Unit ⊕ ι → ℝ := fun o => match o with | Sum.inl _ => 1 | Sum.inr i => x i
    have hF0 : ∀ o, 0 ≤ F o := by
      intro o; cases o with
      | inl u => simp [F]
      | inr i => simpa [F] using hx i
    have hsum : ∑ o, F o = 1 + ∑ i, x i := by
      rw [Fintype.sum_sum_type]; simp [F]
    have hsumk : ∑ o, F o ^ k = 1 + ∑ i, x i ^ k := by
      rw [Fintype.sum_sum_type]; simp [F]
    have hcard : ((Fintype.card (Unit ⊕ ι) : ℕ) : ℝ) = ((Fintype.card ι : ℕ) : ℝ) + 1 := by
      rw [Fintype.card_sum, Fintype.card_unit]; push_cast; ring
    have hpm := sum_pow_le_card_pow_mul_sum_pow F hF0 hk
    rw [hcard, hsum, hsumk] at hpm
    have hpow :
        ((((Fintype.card ι : ℕ) : ℝ)) + 1) ^ (k - 1) ≤ ((((Fintype.card ι : ℕ) : ℝ)) + 1) ^ k :=
      pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card ι)]) (Nat.sub_le k 1)
    have hZ : (0 : ℝ) ≤ 1 + ∑ i, x i ^ k :=
      add_nonneg zero_le_one (Finset.sum_nonneg (fun i _ => pow_nonneg (hx i) k))
    exact hpm.trans (mul_le_mul_of_nonneg_right hpow hZ)

end Work.Diff.STE
