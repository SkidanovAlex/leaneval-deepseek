import Mathlib
import Submission.Work.BourgainPlan.Maximal.dyCZ
import Submission.Work.BourgainPlan.Maximal.ell2Maximal

/-!
# Auxiliary definitions for the weak-`(1,1)` bound of the `ℓ²`-valued dyadic maximal function

* `ell2Sigma g x = (Σ_t ‖g t x‖ₑ²) ^ (1/2)`, the `ℓ²`-norm of the family `g` at `x`;
* `ell2F g x = (Σ_t (dyMax ‖g t ·‖ₑ x)²) ^ (1/2)`, the `ℓ²`-valued maximal function;
* `linOp g m e x = Σ_t e t x · (average of ‖g t ·‖ₑ over the dyadic cell of level `m t x`
  containing `x`)`, the *linearised* maximal operator.

`linOp g m e x ≤ ell2F g x` whenever `0 ≤ e` and `Σ_t e t x² ≤ 1` (`linOp_le_ell2F`), so the
weak-`(1,1)` bound for `linOp` (uniformly in the selections `m`, `e` and in the number of
components, proved in `linearizedWeakType`) implies the target `ell2MaxWeakOne`.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Work.BourgainPlan.Maximal

/-- The `ℓ²`-norm `(Σ_t ‖g t x‖ₑ²)^(1/2)` of a finite family of functions. -/
noncomputable def ell2Sigma {n : ℕ} (g : Fin n → ℝ → ℝ) (x : ℝ) : ℝ≥0∞ :=
  (ell2Sq g x) ^ ((1 : ℝ) / 2)

/-- The `ℓ²`-valued dyadic maximal function. -/
noncomputable def ell2F {n : ℕ} (g : Fin n → ℝ → ℝ) (x : ℝ) : ℝ≥0∞ :=
  (ell2Max g x) ^ ((1 : ℝ) / 2)

/-- The linearised maximal operator, for a selection `m` of dyadic levels and weights `e`. -/
noncomputable def linOp {n : ℕ} (g : Fin n → ℝ → ℝ) (m : Fin n → ℝ → ℤ)
    (e : Fin n → ℝ → ℝ) (x : ℝ) : ℝ≥0∞ :=
  ∑ t, ENNReal.ofReal (e t x) * dyAvg (fun y => ‖g t y‖ₑ) (m t x) x

lemma ell2Sigma_measurable {n : ℕ} {g : Fin n → ℝ → ℝ} (hg : ∀ t, Measurable (g t)) :
    Measurable (ell2Sigma g) := by
  unfold ell2Sigma ell2Sq
  exact (ENNReal.continuous_rpow_const (y := (1:ℝ)/2)).measurable.comp
    (Finset.measurable_sum _ fun t _ => (hg t).enorm.pow_const 2)

lemma ell2F_measurable {n : ℕ} {g : Fin n → ℝ → ℝ} : Measurable (ell2F g) :=
  (ENNReal.continuous_rpow_const (y := (1:ℝ)/2)).measurable.comp (ell2Max_measurable g)

/-- If a finite sum of `ℝ≥0∞`-terms vanishes then so does every term. -/
lemma eq_zero_of_sum_eq_zero {ι : Type*} [Fintype ι] {c : ι → ℝ≥0∞}
    (h : ∑ i, c i = 0) (i : ι) : c i = 0 := by
  have h1 : c i ≤ ∑ j, c j :=
    Finset.single_le_sum (f := c) (fun j _ => bot_le) (Finset.mem_univ i)
  exact le_antisymm (h ▸ h1) bot_le

/-- `x = (x^2)^(1/2)` in `ℝ≥0∞`. -/
lemma eq_rpow_half_sq (x : ℝ≥0∞) : x = (x ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := by
  rw [← ENNReal.rpow_mul, show (2 : ℝ) * ((1 : ℝ) / 2) = 1 by norm_num, ENNReal.rpow_one]

/-- **Cauchy--Schwarz for finite sums in `ℝ≥0∞`**:
`Σ_i a_i b_i ≤ (Σ_i a_i²)^{1/2} (Σ_i b_i²)^{1/2}`. -/
lemma ENNReal_sum_mul_le_sqrt_mul_sqrt {ι : Type*} [Fintype ι] (a b : ι → ℝ≥0∞) :
    ∑ i, a i * b i
      ≤ (∑ i, a i ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) * (∑ i, b i ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := by
  have h12 : (0 : ℝ) < (1 : ℝ) / 2 := by norm_num
  have hA2 : (0 : ℝ) < (2 : ℝ) := by norm_num
  have hA1 : (0 : ℝ) ≤ (1 : ℝ) / 2 := h12.le
  have hiA : ∀ i, a i ≤ (∑ j, a j ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := fun i =>
    (eq_rpow_half_sq (a i)).le.trans (ENNReal.rpow_le_rpow
      (Finset.single_le_sum (f := fun j => a j ^ (2 : ℝ)) (fun j _ => bot_le)
        (Finset.mem_univ i)) hA1)
  have hiB : ∀ i, b i ≤ (∑ j, b j ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := fun i =>
    (eq_rpow_half_sq (b i)).le.trans (ENNReal.rpow_le_rpow
      (Finset.single_le_sum (f := fun j => b j ^ (2 : ℝ)) (fun j _ => bot_le)
        (Finset.mem_univ i)) hA1)
  by_cases hA : (∑ i, a i ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) = ⊤
  · by_cases hB : (∑ i, b i ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) = 0
    · have hb : ∀ i, b i = 0 := fun i => le_antisymm ((hiB i).trans (le_of_eq hB)) bot_le
      rw [hA, hB, mul_zero]
      simp only [hb, mul_zero, Finset.sum_const_zero]
      exact bot_le
    · rw [hA, ENNReal.top_mul hB]
      exact le_top
  · by_cases hB : (∑ i, b i ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) = ⊤
    · by_cases hA0 : (∑ i, a i ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) = 0
      · have ha : ∀ i, a i = 0 := fun i => le_antisymm ((hiA i).trans (le_of_eq hA0)) bot_le
        rw [hA0, hB, zero_mul]
        simp only [ha, zero_mul, Finset.sum_const_zero]
        exact bot_le
      · rw [hB, ENNReal.mul_top hA0]
        exact le_top
    · have hAlt : (∑ i, a i ^ (2 : ℝ)) < ⊤ :=
        (ENNReal.rpow_lt_top_iff_of_pos h12).mp (lt_top_iff_ne_top.mpr hA)
      have hBlt : (∑ i, b i ^ (2 : ℝ)) < ⊤ :=
        (ENNReal.rpow_lt_top_iff_of_pos h12).mp (lt_top_iff_ne_top.mpr hB)
      have hai : ∀ i, a i < ⊤ := fun i => lt_of_le_of_lt (hiA i) (lt_top_iff_ne_top.mpr hA)
      have hbi : ∀ i, b i < ⊤ := fun i => lt_of_le_of_lt (hiB i) (lt_top_iff_ne_top.mpr hB)
      have hLtoReal : (∑ i, a i * b i).toReal = ∑ i, (a i).toReal * (b i).toReal := by
        rw [ENNReal.toReal_sum]
        · exact Finset.sum_congr rfl fun i _ => ENNReal.toReal_mul
        · intro i _
          exact ne_of_lt (ENNReal.mul_lt_top (hai i) (hbi i))
      have hAtoReal : (∑ i, a i ^ (2 : ℝ)).toReal = ∑ i, (a i).toReal ^ (2 : ℝ) := by
        rw [ENNReal.toReal_sum]
        · exact Finset.sum_congr rfl fun i _ => by rw [← ENNReal.toReal_rpow]
        · intro i _
          exact ne_of_lt (ENNReal.rpow_lt_top_of_nonneg hA2.le (ne_of_lt (hai i)))
      have hBtoReal : (∑ i, b i ^ (2 : ℝ)).toReal = ∑ i, (b i).toReal ^ (2 : ℝ) := by
        rw [ENNReal.toReal_sum]
        · exact Finset.sum_congr rfl fun i _ => by rw [← ENNReal.toReal_rpow]
        · intro i _
          exact ne_of_lt (ENNReal.rpow_lt_top_of_nonneg hA2.le (ne_of_lt (hbi i)))
      have hLHSlt : (∑ i, a i * b i) < ⊤ :=
        ENNReal.sum_lt_top.mpr fun i _ => ENNReal.mul_lt_top (hai i) (hbi i)
      have hRHSlt : (∑ i, a i ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) * (∑ i, b i ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
          < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hA) (lt_top_iff_ne_top.mpr hB)
      refine (ENNReal.toReal_le_toReal (ne_of_lt hLHSlt) (ne_of_lt hRHSlt)).mp ?_
      rw [hLtoReal, ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow,
        hAtoReal, hBtoReal]
      have hmain := Real.inner_le_Lp_mul_Lq Finset.univ (fun i => (a i).toReal) (fun i => (b i).toReal)
        (p := 2) (q := 2) (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩)
      simpa only [abs_of_nonneg (ENNReal.toReal_nonneg)] using hmain

/-- The linearised operator is dominated by the `ℓ²`-valued maximal function. -/
lemma linOp_le_ell2F {n : ℕ} (g : Fin n → ℝ → ℝ) (m : Fin n → ℝ → ℤ) (e : Fin n → ℝ → ℝ)
    (he0 : ∀ t x, 0 ≤ e t x) (he1 : ∀ x, ∑ t, (e t x)^2 ≤ 1) (x : ℝ) :
    linOp g m e x ≤ ell2F g x := by
  unfold linOp
  have h1 : ∑ t, ENNReal.ofReal (e t x) * dyAvg (fun y => ‖g t y‖ₑ) (m t x) x
      ≤ ∑ t, ENNReal.ofReal (e t x) * (dyMax (fun y => ‖g t y‖ₑ) x) := by
    refine Finset.sum_le_sum fun t _ => mul_le_mul_right ?_ _
    exact dyAvg_le_dyMax _ _ _
  refine h1.trans ?_
  refine (ENNReal_sum_mul_le_sqrt_mul_sqrt (fun t => ENNReal.ofReal (e t x))
    (fun t => dyMax (fun y => ‖g t y‖ₑ) x)).trans ?_
  have hsum : (∑ t, ENNReal.ofReal (e t x) ^ (2 : ℝ))
      = ENNReal.ofReal (∑ t, (e t x) ^ 2) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun t _ => sq_nonneg _)]
    exact Finset.sum_congr rfl fun t _ => by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast,
        ← ENNReal.ofReal_pow (he0 t x) 2]
  have hrpow : (ENNReal.ofReal (∑ t, (e t x) ^ 2)) ^ ((1 : ℝ) / 2)
      = ENNReal.ofReal ((∑ t, (e t x) ^ 2) ^ ((1 : ℝ) / 2)) :=
    ENNReal.ofReal_rpow_of_nonneg (Finset.sum_nonneg fun t _ => sq_nonneg _)
      (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2)
  have hle1 : (∑ t, (e t x) ^ 2) ^ ((1 : ℝ) / 2) ≤ 1 := by
    calc (∑ t, (e t x) ^ 2) ^ ((1 : ℝ) / 2) ≤ (1 : ℝ) ^ ((1 : ℝ) / 2) :=
          Real.rpow_le_rpow (Finset.sum_nonneg fun t _ => sq_nonneg _) (he1 x) (by norm_num)
      _ = 1 := Real.one_rpow _
  have hfin : ENNReal.ofReal ((∑ t, (e t x) ^ 2) ^ ((1 : ℝ) / 2)) ≤ 1 := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal (1 : ℝ) by norm_num]
    exact ENNReal.ofReal_le_ofReal hle1
  calc (∑ t, ENNReal.ofReal (e t x) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
        * (∑ t, (dyMax (fun y => ‖g t y‖ₑ) x) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
      = ENNReal.ofReal ((∑ t, (e t x) ^ 2) ^ ((1 : ℝ) / 2))
        * (∑ t, (dyMax (fun y => ‖g t y‖ₑ) x) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := by
        rw [hsum, hrpow]
    _ ≤ 1 * (∑ t, (dyMax (fun y => ‖g t y‖ₑ) x) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) :=
        mul_le_mul_of_nonneg_right hfin bot_le
    _ = ell2F g x := by rw [one_mul]; rfl

end Work.BourgainPlan.Maximal
