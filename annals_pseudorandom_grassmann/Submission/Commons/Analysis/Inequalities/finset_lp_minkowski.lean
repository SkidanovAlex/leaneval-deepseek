import Mathlib.Analysis.MeanInequalities

namespace Commons.Analysis.Inequalities

/-- `L^p` scaling by a nonnegative constant: `‖c • f‖_p = c ‖f‖_p`. -/
private lemma Lp_scaling {ι : Type*} [Fintype ι] (p : ℝ) (hpne : p ≠ 0) (c : ℝ) (hc : 0 ≤ c)
    (f : ι → ℝ) :
    (∑ i, |c * f i| ^ p) ^ (1 / p) = c * (∑ i, |f i| ^ p) ^ (1 / p) := by
  have hT : 0 ≤ ∑ i, |f i| ^ p :=
    Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (abs_nonneg (f i)) p)
  calc
    (∑ i, |c * f i| ^ p) ^ (1 / p)
        = (∑ i, c ^ p * |f i| ^ p) ^ (1 / p) := by
            congr 1
            apply Finset.sum_congr rfl
            intro i _
            rw [abs_mul, abs_of_nonneg hc, Real.mul_rpow hc (abs_nonneg (f i))]
    _ = (c ^ p * ∑ i, |f i| ^ p) ^ (1 / p) := by rw [Finset.mul_sum]
    _ = (c ^ p) ^ (1 / p) * (∑ i, |f i| ^ p) ^ (1 / p) := by
            rw [Real.mul_rpow (Real.rpow_nonneg hc p) hT]
    _ = c * (∑ i, |f i| ^ p) ^ (1 / p) := by
            congr 1
            rw [← Real.rpow_mul hc p (1 / p), mul_one_div, div_self hpne, Real.rpow_one]

/-- Weighted Minkowski inequality over an arbitrary finite index set. -/
private lemma weighted_Lp_sum_le {ι κ : Type*} [Fintype ι] (p : ℝ) (hp : 1 ≤ p)
    (w : κ → ℝ) (hw : ∀ j, 0 ≤ w j) (f : κ → ι → ℝ) (s : Finset κ) :
    (∑ i, |∑ j ∈ s, w j * f j i| ^ p) ^ (1 / p) ≤
      ∑ j ∈ s, w j * (∑ i, |f j i| ^ p) ^ (1 / p) := by
  classical
  have hpne : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty, abs_zero]
      rw [Finset.sum_const, nsmul_eq_mul, Real.zero_rpow hpne, mul_zero,
        Real.zero_rpow (one_div_ne_zero hpne)]
  | insert k s hk ih =>
      simp only [Finset.sum_insert hk]
      have step : (∑ i, |w k * f k i + ∑ j ∈ s, w j * f j i| ^ p) ^ (1 / p)
          ≤ (∑ i, |w k * f k i| ^ p) ^ (1 / p)
            + (∑ i, |∑ j ∈ s, w j * f j i| ^ p) ^ (1 / p) := by
        have h := Real.Lp_add_le (s := Finset.univ) (f := fun i => w k * f k i)
          (g := fun i => ∑ j ∈ s, w j * f j i) (p := p) hp
        simpa using h
      have hscale := Lp_scaling (ι := ι) p hpne (w k) (hw k) (f k)
      calc
        (∑ i, |w k * f k i + ∑ j ∈ s, w j * f j i| ^ p) ^ (1 / p)
            ≤ (∑ i, |w k * f k i| ^ p) ^ (1 / p)
              + (∑ i, |∑ j ∈ s, w j * f j i| ^ p) ^ (1 / p) := step
        _ = w k * (∑ i, |f k i| ^ p) ^ (1 / p)
              + (∑ i, |∑ j ∈ s, w j * f j i| ^ p) ^ (1 / p) := by rw [hscale]
        _ ≤ w k * (∑ i, |f k i| ^ p) ^ (1 / p)
              + ∑ j ∈ s, w j * (∑ i, |f j i| ^ p) ^ (1 / p) := by
              exact add_le_add le_rfl ih

theorem finset_lp_minkowski {ι κ : Type*} [Fintype ι] [Fintype κ] (p : ℝ) (hp : 1 ≤ p)
    (w : κ → ℝ) (hw : ∀ j, 0 ≤ w j) (f : κ → ι → ℝ) :
    (∑ i, |∑ j, w j * f j i| ^ p) ^ (1 / p) ≤
      ∑ j, w j * (∑ i, |f j i| ^ p) ^ (1 / p) := by
  simpa using weighted_Lp_sum_le (κ := κ) p hp w hw f Finset.univ

end Commons.Analysis.Inequalities