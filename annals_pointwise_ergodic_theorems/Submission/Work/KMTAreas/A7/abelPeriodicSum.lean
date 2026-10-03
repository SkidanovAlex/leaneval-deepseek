import Mathlib

namespace Work.KMTAreas.A7

/-- Local helper: triangle inequality for a difference of complex numbers. -/
private lemma norm_sub_le_cplx (x y : ℂ) : ‖x - y‖ ≤ ‖x‖ + ‖y‖ := by
  have h : x - y = x + (-y) := by ring
  rw [h]
  exact (norm_add_le x (-y)).trans_eq (by rw [norm_neg])

/-- Local helper: multiplicativity of the norm on `ℂ`. -/
private lemma norm_mul_cplx (x y : ℂ) : ‖x * y‖ = ‖x‖ * ‖y‖ := Complex.norm_mul x y

/-- **Summation by parts** (Abel transformation) for series indexed by `ℕ`. -/
private lemma sum_range_by_parts_cplx (d h : ℕ → ℂ) (N : ℕ) :
    ∑ r ∈ Finset.range (N + 1), d r * h r
      = (∑ r ∈ Finset.range (N + 1), d r) * h N
        - ∑ r ∈ Finset.range N, (∑ j ∈ Finset.range (r + 1), d j) * (h (r + 1) - h r) := by
  induction N with
  | zero =>
      rw [Finset.sum_range_succ (fun r => d r * h r) 0,
          Finset.sum_range_succ (fun r => d r) 0,
          Finset.sum_range_zero, Finset.sum_range_zero]
      ring
  | succ N ih =>
      show ∑ r ∈ Finset.range (N + 1 + 1), d r * h r
          = (∑ r ∈ Finset.range (N + 1 + 1), d r) * h (N + 1)
            - ∑ r ∈ Finset.range (N + 1),
                (∑ j ∈ Finset.range (r + 1), d j) * (h (r + 1) - h r)
      have h1 : ∑ r ∈ Finset.range (N + 1 + 1), d r * h r
          = (∑ r ∈ Finset.range (N + 1), d r * h r) + d (N + 1) * h (N + 1) :=
        Finset.sum_range_succ (fun r => d r * h r) (N + 1)
      have h2 : (∑ r ∈ Finset.range (N + 1 + 1), d r)
          = (∑ r ∈ Finset.range (N + 1), d r) + d (N + 1) :=
        Finset.sum_range_succ (fun r => d r) (N + 1)
      have h3 : (∑ r ∈ Finset.range (N + 1),
            (∑ j ∈ Finset.range (r + 1), d j) * (h (r + 1) - h r))
          = (∑ r ∈ Finset.range N,
              (∑ j ∈ Finset.range (r + 1), d j) * (h (r + 1) - h r))
            + (∑ j ∈ Finset.range (N + 1), d j) * (h (N + 1) - h N) :=
        Finset.sum_range_succ
          (fun r => (∑ j ∈ Finset.range (r + 1), d j) * (h (r + 1) - h r)) N
      rw [h1, h2, h3, ih]
      ring

/-- Partial sums of a `q`-periodic sequence with vanishing period are bounded by `q`. -/
private lemma partialSum_bound (q : ℕ) (hq : 0 < q) (c : ℤ → ℂ)
    (hzero : ∀ n : ℤ, ∑ r ∈ Finset.range q, c (n + (r : ℤ)) = 0)
    (hc : ∀ n : ℤ, ‖c n‖ ≤ 1) (m : ℤ) (k : ℕ) :
    ‖∑ i ∈ Finset.range k, c (m + (i : ℤ))‖ ≤ (q : ℝ) := by
  have hshift : ∀ (m : ℤ) (k : ℕ),
      ∑ i ∈ Finset.range (k + q), c (m + (i : ℤ)) = ∑ i ∈ Finset.range k, c (m + (i : ℤ)) := by
    intro m k
    rw [Finset.sum_range_add (fun i => c (m + (i : ℤ))) k q]
    have h2 : (∑ i ∈ Finset.range q, c (m + ((k + i : ℕ) : ℤ))) = 0 := by
      rw [← hzero (m + (k : ℤ))]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      exact congrArg c (by push_cast; ring)
    rw [h2, add_zero]
  refine Nat.strong_induction_on k ?_
  intro n ih
  rcases lt_or_ge n q with hn | hn
  · calc ‖∑ i ∈ Finset.range n, c (m + (i : ℤ))‖
        ≤ ∑ i ∈ Finset.range n, ‖c (m + (i : ℤ))‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range n, (1 : ℝ) := Finset.sum_le_sum (fun i _ => hc _)
      _ = (n : ℝ) := by simp
      _ ≤ (q : ℝ) := by exact_mod_cast hn.le
  · have h1 : ∑ i ∈ Finset.range n, c (m + (i : ℤ))
        = ∑ i ∈ Finset.range (n - q), c (m + (i : ℤ)) := by
      conv_lhs => rw [← Nat.sub_add_cancel hn]
      exact hshift m (n - q)
    rw [h1]
    exact ih (n - q) (by omega)

/-- Partial sums of the truncation of `c` at level `a` are bounded by `q`. -/
private lemma cutoff_sum_bound (q : ℕ) (hq : 0 < q) (c : ℤ → ℂ) (a : ℕ)
    (hzero : ∀ n : ℤ, ∑ r ∈ Finset.range q, c (n + (r : ℤ)) = 0)
    (hc : ∀ n : ℤ, ‖c n‖ ≤ 1) (k : ℕ) :
    ‖∑ i ∈ Finset.range k, (if a < i then c (i : ℤ) else 0)‖ ≤ (q : ℝ) := by
  by_cases hk : a + 1 ≤ k
  · have hsub : Finset.Ico (a + 1) k ⊆ Finset.range k := by
      intro i hi
      simp only [Finset.mem_Ico, Finset.mem_range] at hi ⊢
      omega
    have hoff : ∀ i ∈ Finset.range k, i ∉ Finset.Ico (a + 1) k →
        (if a < i then c (i : ℤ) else 0) = 0 := by
      intro i hi hin
      have hlt : ¬ (a < i) := by
        simp only [Finset.mem_range] at hi
        simp only [Finset.mem_Ico] at hin
        omega
      rw [if_neg hlt]
    have heq : (∑ i ∈ Finset.range k, (if a < i then c (i : ℤ) else 0))
        = ∑ i ∈ Finset.Ico (a + 1) k, c (i : ℤ) := by
      rw [← Finset.sum_subset (f := fun i => (if a < i then c (i : ℤ) else 0)) hsub hoff]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have hai : a < i := by
        simp only [Finset.mem_Ico] at hi
        omega
      rw [if_pos hai]
    rw [heq, Finset.sum_Ico_eq_sum_range]
    have hsum : (∑ j ∈ Finset.range (k - (a + 1)), c (((a + 1) + j : ℕ) : ℤ))
        = (∑ j ∈ Finset.range (k - (a + 1)), c (((a : ℤ) + 1) + (j : ℤ))) := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      exact congrArg c (by push_cast; ring)
    rw [hsum]
    exact partialSum_bound q hq c hzero hc ((a : ℤ) + 1) (k - (a + 1))
  · have heq : (∑ i ∈ Finset.range k, (if a < i then c (i : ℤ) else 0)) = 0 := by
      refine Finset.sum_eq_zero (fun i hi => ?_)
      have hlt : ¬ (a < i) := by
        simp only [Finset.mem_range] at hi
        omega
      rw [if_neg hlt]
    rw [heq, norm_zero]
    exact Nat.cast_nonneg q

theorem abelPeriodicSum (q : ℕ) (hq : 0 < q) (c : ℤ → ℂ) (f : ℕ → ℂ)
    (hzero : ∀ n : ℤ, ∑ r ∈ Finset.range q, c (n + (r : ℤ)) = 0)
    (hc : ∀ n : ℤ, ‖c n‖ ≤ 1) {a b : ℕ} (hab : a ≤ b) :
    ‖∑ n ∈ Finset.Ioc a b, c (n : ℤ) * f n‖
      ≤ (q : ℝ) * (‖f b‖ + ∑ n ∈ Finset.Ico (a + 1) b, ‖f (n + 1) - f n‖) := by
  have hGbound : ∀ k : ℕ, ‖∑ j ∈ Finset.range k, (if a < j then c (j : ℤ) else 0)‖ ≤ (q : ℝ) :=
    fun k => cutoff_sum_bound q hq c a hzero hc k
  have hbp : (∑ r ∈ Finset.range (b + 1), (if a < r then c (r : ℤ) else 0) * f r)
      = (∑ r ∈ Finset.range (b + 1), (if a < r then c (r : ℤ) else 0)) * f b
        - ∑ r ∈ Finset.range b,
            (∑ j ∈ Finset.range (r + 1), (if a < j then c (j : ℤ) else 0)) * (f (r + 1) - f r) :=
    sum_range_by_parts_cplx (fun i => if a < i then c (i : ℤ) else 0) f b
  have hLHS : (∑ i ∈ Finset.range (b + 1), (if a < i then c (i : ℤ) else 0) * f i)
      = ∑ i ∈ Finset.Ioc a b, c (i : ℤ) * f i := by
    have hsub : Finset.Ioc a b ⊆ Finset.range (b + 1) := by
      intro i hi
      simp only [Finset.mem_Ioc, Finset.mem_range] at hi ⊢
      omega
    have hoff : ∀ i ∈ Finset.range (b + 1), i ∉ Finset.Ioc a b →
        (if a < i then c (i : ℤ) else 0) * f i = 0 := by
      intro i hi hin
      have hlt : ¬ (a < i) := by
        simp only [Finset.mem_range] at hi
        simp only [Finset.mem_Ioc] at hin
        omega
      rw [if_neg hlt, zero_mul]
    rw [← Finset.sum_subset (f := fun i => (if a < i then c (i : ℤ) else 0) * f i) hsub hoff]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [if_pos ((Finset.mem_Ioc.mp hi).1)]
  have hDIFF : (∑ i ∈ Finset.range b,
        (∑ j ∈ Finset.range (i + 1), (if a < j then c (j : ℤ) else 0)) * (f (i + 1) - f i))
      = ∑ i ∈ Finset.Ico (a + 1) b,
        (∑ j ∈ Finset.range (i + 1), (if a < j then c (j : ℤ) else 0)) * (f (i + 1) - f i) := by
    have hsub : Finset.Ico (a + 1) b ⊆ Finset.range b := by
      intro i hi
      simp only [Finset.mem_Ico, Finset.mem_range] at hi ⊢
      omega
    have hoff : ∀ i ∈ Finset.range b, i ∉ Finset.Ico (a + 1) b →
        (∑ j ∈ Finset.range (i + 1), (if a < j then c (j : ℤ) else 0)) * (f (i + 1) - f i) = 0 := by
      intro i hi hin
      have hs : (∑ j ∈ Finset.range (i + 1), (if a < j then c (j : ℤ) else 0)) = 0 := by
        refine Finset.sum_eq_zero (fun j hj => ?_)
        have hlt : ¬ (a < j) := by
          simp only [Finset.mem_range] at hi hj
          simp only [Finset.mem_Ico] at hin
          omega
        rw [if_neg hlt]
      rw [hs, zero_mul]
    rw [← Finset.sum_subset
      (f := fun i => (∑ j ∈ Finset.range (i + 1), (if a < j then c (j : ℤ) else 0)) *
        (f (i + 1) - f i)) hsub hoff]
  rw [← hLHS, hbp, hDIFF]
  calc ‖(∑ r ∈ Finset.range (b + 1), (if a < r then c (r : ℤ) else 0)) * f b
        - ∑ r ∈ Finset.Ico (a + 1) b,
            (∑ j ∈ Finset.range (r + 1), (if a < j then c (j : ℤ) else 0)) * (f (r + 1) - f r)‖
      ≤ ‖(∑ r ∈ Finset.range (b + 1), (if a < r then c (r : ℤ) else 0)) * f b‖
        + ‖∑ r ∈ Finset.Ico (a + 1) b,
            (∑ j ∈ Finset.range (r + 1), (if a < j then c (j : ℤ) else 0)) * (f (r + 1) - f r)‖ :=
        norm_sub_le_cplx _ _
    _ ≤ ‖∑ r ∈ Finset.range (b + 1), (if a < r then c (r : ℤ) else 0)‖ * ‖f b‖
        + ∑ r ∈ Finset.Ico (a + 1) b,
            ‖∑ j ∈ Finset.range (r + 1), (if a < j then c (j : ℤ) else 0)‖ * ‖f (r + 1) - f r‖ := by
        refine add_le_add (le_of_eq (norm_mul_cplx _ _)) ?_
        calc ‖∑ r ∈ Finset.Ico (a + 1) b,
                (∑ j ∈ Finset.range (r + 1), (if a < j then c (j : ℤ) else 0)) * (f (r + 1) - f r)‖
            ≤ ∑ r ∈ Finset.Ico (a + 1) b,
                ‖(∑ j ∈ Finset.range (r + 1), (if a < j then c (j : ℤ) else 0)) *
                  (f (r + 1) - f r)‖ := norm_sum_le _ _
          _ = ∑ r ∈ Finset.Ico (a + 1) b,
                ‖∑ j ∈ Finset.range (r + 1), (if a < j then c (j : ℤ) else 0)‖ *
                ‖f (r + 1) - f r‖ :=
              Finset.sum_congr rfl (fun r _ => norm_mul_cplx _ _)
    _ ≤ (q : ℝ) * ‖f b‖ + ∑ r ∈ Finset.Ico (a + 1) b, (q : ℝ) * ‖f (r + 1) - f r‖ := by
        refine add_le_add ?_ (Finset.sum_le_sum (fun r _ => ?_))
        · exact mul_le_mul_of_nonneg_right (hGbound (b + 1)) (norm_nonneg _)
        · exact mul_le_mul_of_nonneg_right (hGbound (r + 1)) (norm_nonneg _)
    _ = (q : ℝ) * (‖f b‖ + ∑ r ∈ Finset.Ico (a + 1) b, ‖f (r + 1) - f r‖) := by
        rw [← Finset.mul_sum]
        ring

end Work.KMTAreas.A7
