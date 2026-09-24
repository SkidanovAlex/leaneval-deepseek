import Mathlib
import Submission.Work.GM.Affine.WinMass_fejer_defs
import Submission.Work.GM.Affine.region_II_vocab
import Submission.Work.GM.Affine.far_mass_le
import Submission.Work.GM.Affine.nearcorr_fejerK_nonneg

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

namespace Work.GM.Affine

noncomputable section

theorem far_tail_integral_le_decay {δ T M₂ M₃ A : ℝ} {f : ℝ → ℝ} {j : ℕ}
    (hT : 1 ≤ T) (hδ : 0 < δ) (hM₂ : 0 < M₂) (hM₃ : 0 ≤ M₃) (hj : 1 ≤ j) (hA : 0 ≤ A)
    (hfejer : ∀ x : ℝ, fejerK M₃ x ≤ M₃)
    (hbound : ∀ x ∈ {x : ℝ | T ^ (δ / 2) * T / M₂ < |x|},
        ‖Bsum f M₂ x‖ ≤ A * (T / (M₂ * |x|)) ^ j) :
    (∫ x in {x : ℝ | T ^ (δ / 2) * T / M₂ < |x|}, ‖Bsum f M₂ x‖ ^ 2 * fejerK M₃ x)
      ≤ A ^ 2 * M₃ * (2 * T ^ (1 - (δ / 2) * (2 * (j : ℝ) - 1)) / (2 * (j : ℝ) - 1)) / M₂ := by
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le zero_lt_one hT
  have h2j : 1 < 2 * j := by omega
  set Y : ℝ := T ^ (δ / 2) * T / M₂ with hYdef
  have hYfac : Y = T ^ (δ / 2) * (T / M₂) := by rw [hYdef, mul_div_assoc]
  have hYpos : 0 < Y := by rw [hYfac]; positivity
  have hTM : (T / M₂) ≠ 0 := ne_of_gt (div_pos hT0 hM₂)
  -- integrability of the majorant on the closed tail
  have hIntc : IntegrableOn (fun x : ℝ => (T / (M₂ * |x|)) ^ (2 * j)) {x : ℝ | Y ≤ |x|} := by
    have hc : 0 < T / M₂ := div_pos hT0 hM₂
    have h1 : IntegrableOn (fun y : ℝ => ((T / M₂) / |y|) ^ (2 * j)) {y : ℝ | Y ≤ |y|} :=
      integrableOn_abs_div_pow hc hYpos h2j
    have hdiv : ∀ x ∈ {y : ℝ | Y ≤ |y|},
        ((T / M₂) / |x|) ^ (2 * j) = (T / (M₂ * |x|)) ^ (2 * j) :=
      fun x _ => by rw [div_div]
    exact h1.congr_fun hdiv (by measurability)
  have hInts : IntegrableOn (fun x : ℝ => (T / (M₂ * |x|)) ^ (2 * j)) {x : ℝ | Y < |x|} :=
    hIntc.mono_set (fun x hx => show Y ≤ |x| from le_of_lt (show Y < |x| from hx))
  have hIntgc : IntegrableOn (fun x : ℝ => A ^ 2 * M₃ * (T / (M₂ * |x|)) ^ (2 * j))
      {x : ℝ | Y ≤ |x|} :=
    MeasureTheory.Integrable.const_mul hIntc (A ^ 2 * M₃)
  have hIntgs : IntegrableOn (fun x : ℝ => A ^ 2 * M₃ * (T / (M₂ * |x|)) ^ (2 * j))
      {x : ℝ | Y < |x|} :=
    hIntgc.mono_set (fun x hx => show Y ≤ |x| from le_of_lt (show Y < |x| from hx))
  -- pointwise bound on the strict tail
  have hpt : ∀ x ∈ {x : ℝ | Y < |x|}, ‖Bsum f M₂ x‖ ^ 2 * fejerK M₃ x
      ≤ A ^ 2 * M₃ * (T / (M₂ * |x|)) ^ (2 * j) := by
    intro x hx
    have hb := hbound x hx
    have hbase : 0 ≤ T / (M₂ * |x|) := div_nonneg hT0.le (mul_nonneg hM₂.le (abs_nonneg x))
    have hbnn : 0 ≤ A * (T / (M₂ * |x|)) ^ j := mul_nonneg hA (pow_nonneg hbase j)
    have hsq : ‖Bsum f M₂ x‖ ^ 2 ≤ (A * (T / (M₂ * |x|)) ^ j) ^ 2 := by
      nlinarith [norm_nonneg (Bsum f M₂ x), hb, hbnn]
    calc ‖Bsum f M₂ x‖ ^ 2 * fejerK M₃ x
        ≤ ‖Bsum f M₂ x‖ ^ 2 * M₃ := mul_le_mul_of_nonneg_left (hfejer x) (sq_nonneg _)
      _ ≤ (A * (T / (M₂ * |x|)) ^ j) ^ 2 * M₃ := mul_le_mul_of_nonneg_right hsq hM₃
      _ = A ^ 2 * M₃ * (T / (M₂ * |x|)) ^ (2 * j) := by
          have h1 : ((T / (M₂ * |x|)) ^ j) ^ 2 = (T / (M₂ * |x|)) ^ (2 * j) := by
            rw [← pow_mul, Nat.mul_comm]
          rw [mul_pow, h1]
          ring
  -- value of the majorant on the closed tail
  have hval : ∫ y in {y : ℝ | Y ≤ |y|}, (T / (M₂ * |y|)) ^ (2 * j)
      = 2 * (T / M₂) * ((T / M₂) / Y) ^ (2 * j - 1) / (((2 * j : ℕ) : ℝ) - 1) := by
    have hcongr : ∫ y in {y : ℝ | Y ≤ |y|}, (T / (M₂ * |y|)) ^ (2 * j)
        = ∫ y in {y : ℝ | Y ≤ |y|}, ((T / M₂) / |y|) ^ (2 * j) :=
      setIntegral_congr_fun (by measurability) (fun y _ => by rw [div_div])
    rw [hcongr]
    exact integral_abs_div_pow (div_pos hT0 hM₂) hYpos h2j
  have hsplit : ∫ x in {x : ℝ | Y ≤ |x|}, A ^ 2 * M₃ * (T / (M₂ * |x|)) ^ (2 * j)
      = A ^ 2 * M₃ * ∫ x in {x : ℝ | Y ≤ |x|}, (T / (M₂ * |x|)) ^ (2 * j) :=
    integral_const_mul (A ^ 2 * M₃) _
  -- exponent bookkeeping
  have hcast : (((2 * j : ℕ) : ℝ)) - 1 = 2 * (j : ℝ) - 1 := by push_cast; ring
  have hratio : (T / M₂) / Y = (T ^ (δ / 2))⁻¹ := by
    rw [hYfac, mul_comm (T ^ (δ / 2)) (T / M₂), div_mul_eq_div_div, div_self hTM, one_div]
  have hpow : ((T / M₂) / Y) ^ (2 * j - 1) = T ^ (-((δ / 2) * (2 * (j : ℝ) - 1))) := by
    rw [hratio, inv_pow, ← Real.rpow_natCast (T ^ (δ / 2)) (2 * j - 1), ← Real.rpow_mul hT0.le]
    rw [Real.rpow_neg hT0.le]
    congr 1
    congr 1
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * j)]
    push_cast
    ring
  have hTE : 2 * (T / M₂) * T ^ (-((δ / 2) * (2 * (j : ℝ) - 1)))
      = 2 * T ^ (1 - (δ / 2) * (2 * (j : ℝ) - 1)) / M₂ := by
    rw [show (1 : ℝ) - (δ / 2) * (2 * (j : ℝ) - 1)
        = 1 + (-((δ / 2) * (2 * (j : ℝ) - 1))) from by ring]
    rw [Real.rpow_add hT0, Real.rpow_one]
    ring
  have hmono : ({x : ℝ | Y < |x|} : Set ℝ) ≤ᵐ[volume] {x : ℝ | Y ≤ |x|} :=
    Filter.Eventually.of_forall (fun x hx => show Y ≤ |x| from le_of_lt (show Y < |x| from hx))
  calc ∫ x in {x : ℝ | Y < |x|}, ‖Bsum f M₂ x‖ ^ 2 * fejerK M₃ x
      ≤ ∫ x in {x : ℝ | Y < |x|}, A ^ 2 * M₃ * (T / (M₂ * |x|)) ^ (2 * j) :=
        setIntegral_mono_of_nonneg
          (fun x _ => mul_nonneg (sq_nonneg (‖Bsum f M₂ x‖)) (nearcorr_fejerK_nonneg M₃ x))
          hpt hIntgs
    _ ≤ ∫ x in {x : ℝ | Y ≤ |x|}, A ^ 2 * M₃ * (T / (M₂ * |x|)) ^ (2 * j) :=
        setIntegral_mono_set hIntgc
          (Filter.Eventually.of_forall (fun x => mul_nonneg (mul_nonneg (sq_nonneg A) hM₃)
            (pow_nonneg (div_nonneg hT0.le (mul_nonneg hM₂.le (abs_nonneg x))) (2 * j)))) hmono
    _ = A ^ 2 * M₃ * (2 * (T / M₂) * ((T / M₂) / Y) ^ (2 * j - 1) / (((2 * j : ℕ) : ℝ) - 1)) := by
        rw [hsplit, hval]
    _ = A ^ 2 * M₃ * (2 * T ^ (1 - (δ / 2) * (2 * (j : ℝ) - 1)) / (2 * (j : ℝ) - 1)) / M₂ := by
        rw [hpow, hcast, hTE]
        ring

end

end Work.GM.Affine
