import Mathlib
import Submission.Work.WilE3.Taylor.Grad.order_le_of_pow_lt

namespace Work.Taylor.Grad

/-- **Order bookkeeping for a sum-of-squares power inequality.**

If `F : Fin k → ℝ → ℝ` and `G` are analytic at `0`, `F i` has order `n`, `G` has order `m` and is
positive on a right neighbourhood of `0`, and

`(∑ j, (F j t) ^ 2) ^ q < (G t) ^ (2 * p)`  for all small `t > 0`,

then `p * m ≤ q * n`.

The point is that the sum of squares dominates the single term `(F i t) ^ 2`, so
`(F i t) ^ (2 * q) = ((F i t) ^ 2) ^ q < (G t) ^ (2 * p)`; the function `t ↦ (F i t) ^ 2` is
analytic at `0` with order `2 * n` and positive on a right neighbourhood of `0`, so the general
order bookkeeping lemma applies and yields `2 * p * m ≤ q * (2 * n)`. -/
theorem order_le_of_sumsq_pow_lt {k : ℕ} {F : Fin k → ℝ → ℝ} {G : ℝ → ℝ} {p q m n : ℕ} {i : Fin k}
    (hF : AnalyticAt ℝ (F i) 0) (hG : AnalyticAt ℝ G 0)
    (hFord : analyticOrderAt (F i) 0 = n) (hGord : analyticOrderAt G 0 = m)
    (hGpos : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < G t)
    (hineq : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (∑ j, (F j t) ^ 2) ^ q < (G t) ^ (2 * p)) :
    p * m ≤ q * n := by
  -- The function `t ↦ (F i t) ^ 2` is analytic at `0` ...
  have hsq : AnalyticAt ℝ (fun t : ℝ => (F i t) ^ 2) 0 := by fun_prop
  -- ... with order `2 * n` ...
  have hsqord : analyticOrderAt (fun t : ℝ => (F i t) ^ 2) 0 = 2 * n := by
    have h1 : (fun t : ℝ => (F i t) ^ 2) = (F i) ^ 2 := rfl
    rw [h1, analyticOrderAt_pow hF 2, hFord]
    norm_num
  -- ... and is positive on a right neighbourhood of `0` (the order `n` of `F i` is finite, so
  -- `F i` does not vanish identically near `0`, and by the principle of isolated zeros it is
  -- nonzero in a punctured neighbourhood, in particular on a right neighbourhood).
  have hpos_sq : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < (F i t) ^ 2 := by
    rcases hF.eventually_eq_zero_or_eventually_ne_zero with hzero | hne
    · exfalso
      have htop : analyticOrderAt (F i) 0 = ⊤ := analyticOrderAt_eq_top.mpr hzero
      rw [hFord] at htop
      exact ENat.natCast_ne_top n htop
    · have hsub : Set.Ioi (0 : ℝ) ⊆ ({0}ᶜ : Set ℝ) := fun x hx => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact ne_of_gt hx
      filter_upwards [hne.filter_mono (nhdsWithin_mono 0 hsub)] with t ht
      exact sq_pos_of_ne_zero ht
  -- The sum dominates its `i`-th summand, hence the inequality transfers to `(F i ·) ^ 2`.
  have hineq' : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (fun t : ℝ => (F i t) ^ 2) t ^ q < (G t) ^ (2 * p) := by
    filter_upwards [hineq] with t ht
    refine lt_of_le_of_lt ?_ ht
    exact pow_le_pow_left₀ (sq_nonneg _)
      (Finset.single_le_sum (fun j _ => sq_nonneg (F j t)) (Finset.mem_univ i)) q
  -- Apply the general order bookkeeping: `2 * p * m ≤ q * (2 * n)`.
  have key := Work.WilE3.Taylor.Grad.order_le_of_pow_lt (G := fun t : ℝ => (F i t) ^ 2) (F := G)
    (p := p) (q := q) (n := 2 * n) (k := m) hsq hG hsqord hGord hpos_sq hGpos hineq'
  -- Cancel the common factor `2`.
  have h2 : 2 * (p * m) ≤ 2 * (q * n) := by
    calc 2 * (p * m) = 2 * p * m := by ring
      _ ≤ q * (2 * n) := key
      _ = 2 * (q * n) := by ring
  exact Nat.le_of_mul_le_mul_left h2 (by norm_num)

end Work.Taylor.Grad
