import Mathlib
import Submission.Commons.MeasureTheory.Integral.simplex_monomial_integral

open MeasureTheory Set
open scoped BigOperators Pointwise

namespace Commons.MeasureTheory.Integral

noncomputable section

/-- Dilation of the unit simplex by a positive scalar `c`. -/
private lemma smul_simplexSet_builder {n : ℕ} {c : ℝ} (hc : 0 < c) :
    c • {v : Fin n → ℝ | (∀ i, 0 ≤ v i) ∧ ∑ i, v i ≤ 1}
      = {u : Fin n → ℝ | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ c} := by
  ext u
  constructor
  · intro hu
    rcases hu with ⟨v, hv, rfl⟩
    refine ⟨fun i => mul_nonneg hc.le (hv.1 i), ?_⟩
    have : (∑ i, (c • v) i) = c * ∑ i, v i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => rfl)
    rw [this]
    calc c * ∑ i, v i ≤ c * 1 := mul_le_mul_of_nonneg_left hv.2 hc.le
      _ = c := mul_one c
  · intro hu
    refine ⟨c⁻¹ • u, ⟨fun i => mul_nonneg (inv_nonneg.2 hc.le) (hu.1 i), ?_⟩, ?_⟩
    · have : (∑ i, (c⁻¹ • u) i) = c⁻¹ * ∑ i, u i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => rfl)
      rw [this]
      calc c⁻¹ * ∑ i, u i ≤ c⁻¹ * c := mul_le_mul_of_nonneg_left hu.2 (inv_nonneg.2 hc.le)
        _ = 1 := inv_mul_cancel₀ hc.ne'
    · ext i
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]

/-- Change of variables `u = c • v` on the simplex: the `c`-simplex integral equals
`c ^ n` times the unit-simplex integral of the dilated integrand. -/
private lemma setIntegral_simplex_scaling {n : ℕ} {c : ℝ} (hc : 0 < c)
    (f : (Fin n → ℝ) → ℝ) :
    ∫ u in {u : Fin n → ℝ | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ c}, f u
      = c ^ n * ∫ v in {v : Fin n → ℝ | (∀ i, 0 ≤ v i) ∧ ∑ i, v i ≤ 1}, f (c • v) := by
  have h := Measure.setIntegral_comp_smul_of_pos (μ := (volume : Measure (Fin n → ℝ))) f
      {v : Fin n → ℝ | (∀ i, 0 ≤ v i) ∧ ∑ i, v i ≤ 1} hc
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, smul_simplexSet_builder hc,
    smul_eq_mul] at h
  have hc' : (c : ℝ) ^ n ≠ 0 := by positivity
  rw [h, ← mul_assoc, mul_inv_cancel₀ hc', one_mul]

theorem simplex_integral_scaled {k : ℕ} (c : ℝ) (hc : 0 < c) (a : ℕ) (b : Fin k → ℕ) :
    ∫ t : Fin k → ℝ in {t | (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ c},
        (c - ∑ i, t i) ^ a * ∏ i, (t i) ^ (b i) =
      c ^ (k + a + ∑ i, b i) *
        (((a.factorial * ∏ i, (b i).factorial : ℕ)) : ℝ) /
          (((a + ∑ i, b i + k).factorial : ℕ) : ℝ) := by
  set F : (Fin k → ℝ) → ℝ := fun u => (c - ∑ i, u i) ^ a * ∏ i, (u i) ^ (b i) with hF
  have hpoint : ∀ v : Fin k → ℝ,
      F (c • v) = c ^ (a + ∑ i, b i) * ((1 - ∑ i, v i) ^ a * ∏ i, (v i) ^ (b i)) := by
    intro v
    simp only [hF]
    have hsum : ∑ i, (c • v) i = c * ∑ i, v i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => rfl)
    have hprod : ∏ i, ((c • v) i) ^ (b i) = c ^ (∑ i, b i) * ∏ i, (v i) ^ (b i) := by
      have hp : ∀ i, ((c • v) i) ^ (b i) = c ^ (b i) * (v i) ^ (b i) := by
        intro i; rw [Pi.smul_apply, smul_eq_mul, mul_pow]
      rw [Finset.prod_congr rfl (fun i _ => hp i), Finset.prod_mul_distrib,
        Finset.prod_pow_eq_pow_sum]
    rw [hsum, hprod]
    have h1 : c - c * ∑ i, v i = c * (1 - ∑ i, v i) := by ring
    rw [h1, mul_pow, pow_add]
    ring
  have hstep : ∫ t in {t : Fin k → ℝ | (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ c}, F t
      = c ^ k * ∫ v in {v : Fin k → ℝ | (∀ i, 0 ≤ v i) ∧ ∑ i, v i ≤ 1}, F (c • v) :=
    setIntegral_simplex_scaling hc F
  rw [hstep, funext hpoint, MeasureTheory.integral_const_mul]
  have hbase : ∫ v in {v : Fin k → ℝ | (∀ i, 0 ≤ v i) ∧ ∑ i, v i ≤ 1},
        (1 - ∑ i, v i) ^ a * ∏ i, (v i) ^ (b i) =
      (((a.factorial * ∏ i, (b i).factorial : ℕ)) : ℝ) /
        (((a + ∑ i, b i + k).factorial : ℕ) : ℝ) :=
    simplex_monomial_integral a b
  rw [hbase, ← mul_assoc, ← pow_add, mul_div_assoc]
  congr 1
  congr 1
  ring

end

end Commons.MeasureTheory.Integral
