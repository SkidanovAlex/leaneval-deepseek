import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder

namespace Commons.Analysis.Real

open MeasureTheory
open scoped ENNReal

/-- **Dyadic sum versus integral for a non-increasing function.**  For a function `f : ℝ → ℝ≥0∞`
which is non-increasing on the positive half-line, the dyadic weighted sum `∑_{ℓ<L} 2^{-ℓ} f(2^{-ℓ})`
is bounded by twice the integral of `f` over `(0,1]`. -/
theorem sum_range_mul_le_lintegral_of_antitone (f : ℝ → ℝ≥0∞)
    (hf : ∀ x y : ℝ, 0 < x → x ≤ y → f y ≤ f x) (L : ℕ) :
    ∑ ℓ ∈ Finset.range L, (1 / 2 : ℝ≥0∞) ^ ℓ * f ((1 / 2 : ℝ) ^ ℓ)
      ≤ 2 * ∫⁻ r in Set.Ioc (0 : ℝ) 1, f r := by
  -- The dyadic interval `(2^{-(ℓ+1)}, 2^{-ℓ}]` supporting the `ℓ`-th term.
  let A : ℕ → Set ℝ := fun ℓ => Set.Ioc ((1/2:ℝ)^(ℓ+1)) ((1/2:ℝ)^ℓ)
  have hA : ∀ ℓ, A ℓ = Set.Ioc ((1/2:ℝ)^(ℓ+1)) ((1/2:ℝ)^ℓ) := fun ℓ => rfl
  -- `2^{-ℓ}` as an element of `ℝ≥0∞` is `ofReal` of the real `2^{-ℓ}`.
  have hpow : ∀ ℓ : ℕ, (1/2:ℝ≥0∞)^ℓ = ENNReal.ofReal ((1/2:ℝ)^ℓ) := by
    intro ℓ
    have h : (1/2 : ℝ≥0∞) = ENNReal.ofReal (1/2:ℝ) := by simp
    rw [h, ← ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 1/2)]
  -- Termwise bound: `2^{-ℓ} f(2^{-ℓ}) ≤ 2 ∫_{A ℓ} f`.
  have hterm : ∀ ℓ, (1/2:ℝ≥0∞)^ℓ * f ((1/2:ℝ)^ℓ) ≤ 2 * ∫⁻ r in A ℓ, f r := by
    intro ℓ
    -- On `A ℓ` the function dominates its value at the right endpoint `2^{-ℓ}`.
    have hmono : ∫⁻ r in A ℓ, f ((1/2:ℝ)^ℓ) ≤ ∫⁻ r in A ℓ, f r := by
      apply setLIntegral_mono' (s := A ℓ)
      · rw [hA ℓ]; exact measurableSet_Ioc
      · intro r hr
        rw [hA ℓ] at hr
        simp only [Set.mem_Ioc] at hr
        exact hf r ((1/2:ℝ)^ℓ) (lt_trans (pow_pos (by norm_num) _) hr.1) hr.2
    have hconst : ∫⁻ r in A ℓ, f ((1/2:ℝ)^ℓ) = f ((1/2:ℝ)^ℓ) * volume (A ℓ) :=
      setLIntegral_const (A ℓ) (f ((1/2:ℝ)^ℓ))
    -- The measure of `A ℓ` is `2^{-(ℓ+1)}`.
    have hvol : volume (A ℓ) = ENNReal.ofReal ((1/2:ℝ)^(ℓ+1)) := by
      rw [hA ℓ, Real.volume_Ioc]
      congr 1
      have hh : (1/2:ℝ)^ℓ = 2 * (1/2:ℝ)^(ℓ+1) := by rw [pow_succ]; ring
      linarith
    have h2 : (2:ℝ≥0∞) * volume (A ℓ) = ENNReal.ofReal ((1/2:ℝ)^ℓ) := by
      rw [hvol, show (2:ℝ≥0∞) = ENNReal.ofReal 2 by simp,
          ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
      congr 1
      rw [pow_succ]; ring
    calc (1/2:ℝ≥0∞)^ℓ * f ((1/2:ℝ)^ℓ)
        = ENNReal.ofReal ((1/2:ℝ)^ℓ) * f ((1/2:ℝ)^ℓ) := by rw [hpow ℓ]
      _ = (2 * volume (A ℓ)) * f ((1/2:ℝ)^ℓ) := by rw [h2]
      _ = 2 * (f ((1/2:ℝ)^ℓ) * volume (A ℓ)) := by ring
      _ ≤ 2 * ∫⁻ r in A ℓ, f r := by
            exact mul_le_mul_right (by rw [← hconst]; exact hmono) 2
  -- The dyadic intervals are pairwise disjoint.
  have hdisj : (Finset.range L : Set ℕ).PairwiseDisjoint A := by
    intro i hi j hj hij
    change Disjoint (A i) (A j)
    rw [Set.disjoint_left]
    intro r hri hrj
    rw [hA i] at hri
    rw [hA j] at hrj
    simp only [Set.mem_Ioc] at hri hrj
    rcases lt_or_gt_of_ne hij with h | h
    · have hle : (1/2:ℝ)^j ≤ (1/2:ℝ)^(i+1) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      linarith [hri.1, hrj.2, hle]
    · have hle : (1/2:ℝ)^i ≤ (1/2:ℝ)^(j+1) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      linarith [hrj.1, hri.2, hle]
  have hmeas : ∀ b ∈ Finset.range L, MeasurableSet (A b) := by
    intro b hb
    rw [hA b]; exact measurableSet_Ioc
  -- Each dyadic interval lies inside `(0,1]`.
  have hAsub : ∀ ℓ, A ℓ ⊆ Set.Ioc (0:ℝ) 1 := by
    intro ℓ r hr
    rw [hA ℓ] at hr
    simp only [Set.mem_Ioc] at hr ⊢
    exact ⟨lt_trans (pow_pos (by norm_num) _) hr.1,
           le_trans hr.2 (pow_le_one₀ (by norm_num) (by norm_num))⟩
  have hsubset : (⋃ ℓ ∈ Finset.range L, A ℓ) ⊆ Set.Ioc (0:ℝ) 1 := by
    intro r hr
    simp only [Set.mem_iUnion] at hr
    obtain ⟨ℓ, -, hrℓ⟩ := hr
    exact hAsub ℓ hrℓ
  calc ∑ ℓ ∈ Finset.range L, (1/2:ℝ≥0∞)^ℓ * f ((1/2:ℝ)^ℓ)
      ≤ ∑ ℓ ∈ Finset.range L, 2 * ∫⁻ r in A ℓ, f r := by
          apply Finset.sum_le_sum
          intro ℓ hℓ
          exact hterm ℓ
    _ = 2 * ∑ ℓ ∈ Finset.range L, ∫⁻ r in A ℓ, f r := by rw [Finset.mul_sum]
    _ = 2 * ∫⁻ r in (⋃ ℓ ∈ Finset.range L, A ℓ), f r := by
          rw [lintegral_biUnion_finset hdisj hmeas f]
    _ ≤ 2 * ∫⁻ r in Set.Ioc (0:ℝ) 1, f r := by
          exact mul_le_mul_right (lintegral_mono_set hsubset) 2

end Commons.Analysis.Real