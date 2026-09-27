import Mathlib
import Submission.Work.EQ.geom_sum_sq
import Submission.Work.EQ.geom_sum_kw_sharp
import Submission.Work.EQ.kpow_mul_pred

namespace Work.EQ

/-- Numeric and geometric-series bounds used in the dynamics of `LocalModel`.

With `μ = (1 + lam)/2` (so `1 - μ = (1 - lam)/2`) and the hypotheses `0 < ε`, `0 < C`,
`0 < lam < 1`, `C ε ≤ (1 - lam)/4` **and** `ε ≤ (1 - lam)/4`: `0 < μ < 1`, `2 C ε ≤ 1 - μ`, and
the explicit finite-sum bounds below hold.  (Note `∑ k ∈ Finset.range n` is the partial sum of a
nonnegative series; ℕ-truncated exponents at `k = 0` are killed by the factor `k`.) -/
theorem dyn_geom_bounds {lam C ε : ℝ} (hε0 : 0 < ε) (hC0 : 0 < C) (hlam0 : 0 < lam)
    (hlam1 : lam < 1) (hCε : C * ε ≤ (1 - lam) / 4) (hε : ε ≤ (1 - lam) / 4) :
    0 < (1 + lam) / 2 ∧
      (1 + lam) / 2 < 1 ∧
      2 * C * ε ≤ 1 - (1 + lam) / 2 ∧
      (∀ n : ℕ, ∑ k ∈ Finset.range n, C * ε ^ 2 * ((1 + lam) / 2) ^ (2 * k) ≤ 1 / 8) ∧
      (∀ n : ℕ, ∑ k ∈ Finset.range n,
        8 * C ^ 2 * ε ^ 2 * ((k : ℝ) * ((1 + lam) / 2) ^ (2 * k - 1)) ≤ 1 / 2) ∧
      (∀ k : ℕ, 2 * C * ε * ((k : ℝ) * ((1 + lam) / 2) ^ (k - 1)) ≤ 1) ∧
      (∀ n : ℕ, ((1 + lam) / 2) ^ n ≤ 1) ∧
      (∀ n : ℕ, ((1 + lam) / 2) ^ n * ε ≤ ε) := by
  set μ : ℝ := (1 + lam) / 2 with hμ
  have hμpos : 0 < μ := by rw [hμ]; linarith
  have hμlt1 : μ < 1 := by rw [hμ]; linarith
  have hμhalf : (1 : ℝ) / 2 < μ := by rw [hμ]; linarith
  have hμnonneg : 0 ≤ μ := le_of_lt hμpos
  have hsub : 1 - μ = (1 - lam) / 2 := by rw [hμ]; ring
  have hhalf : (1 - lam) / 4 = (1 - μ) / 2 := by rw [hsub]; ring
  have hCε' : C * ε ≤ (1 - μ) / 2 := by rw [← hhalf]; exact hCε
  have hε' : ε ≤ (1 - μ) / 2 := by rw [← hhalf]; exact hε
  have hA : 2 * C * ε ≤ 1 - μ := by nlinarith [hCε']
  have hμsq_lt1 : μ ^ 2 < 1 := by nlinarith [hμpos, hμlt1]
  have h1mμ2pos : 0 < 1 - μ ^ 2 := by linarith
  have h1mμpos : 0 < 1 - μ := by linarith
  -- Conjunct 4
  have c4 : ∀ n : ℕ, ∑ k ∈ Finset.range n, C * ε ^ 2 * μ ^ (2 * k) ≤ 1 / 8 := by
    intro n
    have hg := geom_sum_sq (le_of_lt hμpos) hμlt1 n
    have hfactor : ∑ k ∈ Finset.range n, C * ε ^ 2 * μ ^ (2 * k)
        = C * ε ^ 2 * ∑ k ∈ Finset.range n, (μ ^ 2) ^ k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [pow_mul]
    rw [hfactor]
    have hCe2 : C * ε ^ 2 ≤ (1 - μ) ^ 2 / 4 := by
      have h1 : C * ε ^ 2 = (C * ε) * ε := by ring
      rw [h1]
      have hb : 0 ≤ (1 - μ) / 2 := by linarith
      calc (C * ε) * ε ≤ ((1 - μ) / 2) * ((1 - μ) / 2) :=
            mul_le_mul hCε' hε' hε0.le hb
        _ = (1 - μ) ^ 2 / 4 := by ring
    have hle : (1 - μ) ^ 2 / 4 ≤ (1 / 8) * (1 - μ ^ 2) := by
      have hfac : 1 - μ ^ 2 = (1 - μ) * (1 + μ) := by ring
      have h3 : 1 ≤ 3 * μ := by linarith [hμhalf]
      rw [hfac]
      nlinarith [h3, h1mμpos, hμpos, hμlt1, sq_nonneg (1 - μ)]
    have hmid : C * ε ^ 2 * (1 / (1 - μ ^ 2)) ≤ 1 / 8 := by
      rw [mul_one_div, div_le_iff₀ h1mμ2pos]
      linarith [hCe2, hle]
    exact le_trans (mul_le_mul_of_nonneg_left hg (by positivity)) hmid
  -- Conjunct 5
  have c5 : ∀ n : ℕ, ∑ k ∈ Finset.range n,
      8 * C ^ 2 * ε ^ 2 * ((k : ℝ) * μ ^ (2 * k - 1)) ≤ 1 / 2 := by
    intro n
    have hg := geom_sum_kw_sharp (le_of_lt hμpos) hμlt1 n
    have hfactor : ∑ k ∈ Finset.range n, 8 * C ^ 2 * ε ^ 2 * ((k : ℝ) * μ ^ (2 * k - 1))
        = 8 * C ^ 2 * ε ^ 2 * ∑ k ∈ Finset.range n, ((k : ℝ) * μ ^ (2 * k - 1)) := by
      rw [Finset.mul_sum]
    rw [hfactor]
    have hA2 : 8 * C ^ 2 * ε ^ 2 ≤ 2 * (1 - μ) ^ 2 := by
      have hsq : (2 * C * ε) ^ 2 ≤ (1 - μ) ^ 2 := pow_le_pow_left₀ (by positivity) hA 2
      nlinarith [hsq]
    have hbound : 8 * C ^ 2 * ε ^ 2 * (μ / (1 - μ ^ 2) ^ 2) ≤ 1 / 2 := by
      have hXnn : 0 ≤ μ / (1 - μ ^ 2) ^ 2 :=
        div_nonneg hμnonneg (pow_nonneg (le_of_lt h1mμ2pos) 2)
      have hstep : 8 * C ^ 2 * ε ^ 2 * (μ / (1 - μ ^ 2) ^ 2)
          ≤ 2 * (1 - μ) ^ 2 * (μ / (1 - μ ^ 2) ^ 2) :=
        mul_le_mul_of_nonneg_right hA2 hXnn
      refine le_trans hstep ?_
      have hfac : (1 : ℝ) - μ ^ 2 = (1 - μ) * (1 + μ) := by ring
      have heq : 2 * (1 - μ) ^ 2 * (μ / (1 - μ ^ 2) ^ 2) = 2 * μ / (1 + μ) ^ 2 := by
        rw [hfac]
        have h1 : (1 - μ) ≠ 0 := by linarith
        have h2 : (1 + μ) ≠ 0 := by linarith
        field_simp
      rw [heq]
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (1 + μ) ^ 2)]
      nlinarith [sq_nonneg (1 - μ)]
    exact le_trans (mul_le_mul_of_nonneg_left hg (by positivity)) hbound
  -- Conjunct 6
  have c6 : ∀ k : ℕ, 2 * C * ε * ((k : ℝ) * μ ^ (k - 1)) ≤ 1 := by
    intro k
    have hk := kpow_mul_pred hμpos hμlt1 k
    have h2 : 0 ≤ 2 * C * ε := by positivity
    refine le_trans (mul_le_mul_of_nonneg_left hk h2) ?_
    rw [mul_one_div, div_le_iff₀ h1mμpos]
    nlinarith [hA]
  -- Conjunct 7
  have c7 : ∀ n : ℕ, μ ^ n ≤ 1 := fun n => pow_le_one₀ (n := n) hμnonneg (le_of_lt hμlt1)
  -- Conjunct 8
  have c8 : ∀ n : ℕ, μ ^ n * ε ≤ ε := by
    intro n
    have := mul_le_mul_of_nonneg_right (c7 n) hε0.le
    simpa using this
  exact ⟨hμpos, hμlt1, hA, c4, c5, c6, c7, c8⟩

end Work.EQ
