import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Measure ENNReal

namespace Work.EllipticEst.InteriorRegularity

/-- `(x ^ (1/2)) ^ 2 = x` for `x : ℝ≥0∞`. -/
private lemma rpow_half_sq (x : ℝ≥0∞) : (x ^ (1/2:ℝ)) ^ (2:ℝ) = x := by
  rw [← ENNReal.rpow_mul]
  norm_num

/-- `x * x = x ^ 2` for `x : ℝ≥0∞`, with the real (= rpow) exponent. -/
private lemma mul_self_rpow_two (x : ℝ≥0∞) : x * x = x ^ (2:ℝ) := by
  rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast, pow_two]

/-- `x ^ (1/2) * x ^ (1/2) = x` for `x : ℝ≥0∞`. -/
private lemma rpow_half_mul_half (x : ℝ≥0∞) : x ^ (1/2:ℝ) * x ^ (1/2:ℝ) = x := by
  rw [← ENNReal.mul_rpow_of_nonneg x x (by norm_num : (0:ℝ) ≤ 1/2), mul_self_rpow_two,
    ← ENNReal.rpow_mul]
  norm_num

/-- `ofReal (A * B ^ 2) = ofReal A * (ofReal B) ^ 2` for `A, B ≥ 0`. -/
private lemma ofReal_mul_sq (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ENNReal.ofReal (A * B ^ 2) = ENNReal.ofReal A * ENNReal.ofReal B ^ (2:ℝ) := by
  rw [pow_two B, ENNReal.ofReal_mul hA, ENNReal.ofReal_mul hB, mul_self_rpow_two]

/-- Weighted Cauchy–Schwarz for `ℝ≥0∞`-valued functions:
`(∫ f g) ^ 2 ≤ (∫ f) * (∫ f g ^ 2)`.
It is Hölder's inequality with conjugate exponents `p = q = 2` applied to `f ^ (1/2)` and
`f ^ (1/2) * g`. -/
private theorem lintegral_weighted_cs {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    (∫⁻ a, f a * g a ∂μ) ^ (2:ℝ) ≤ (∫⁻ a, f a ∂μ) * (∫⁻ a, f a * g a ^ (2:ℝ) ∂μ) := by
  have hpq : (2:ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hF : AEMeasurable (fun a => f a ^ (1/2:ℝ)) μ := hf.pow_const _
  have hG : AEMeasurable (fun a => f a ^ (1/2:ℝ) * g a) μ := (hf.pow_const _).mul hg
  have hold := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hF hG
  have h1 : (∫⁻ a, ((fun a => f a ^ (1/2:ℝ)) * (fun a => f a ^ (1/2:ℝ) * g a)) a ∂μ)
      = ∫⁻ a, f a * g a ∂μ := by
    refine lintegral_congr fun a => ?_
    rw [Pi.mul_apply, ← mul_assoc, rpow_half_mul_half]
  have h2 : (∫⁻ a, (fun a => f a ^ (1/2:ℝ)) a ^ (2:ℝ) ∂μ) = ∫⁻ a, f a ∂μ := by
    refine lintegral_congr fun a => ?_
    exact rpow_half_sq (f a)
  have h3 : (∫⁻ a, (fun a => f a ^ (1/2:ℝ) * g a) a ^ (2:ℝ) ∂μ)
      = ∫⁻ a, f a * g a ^ (2:ℝ) ∂μ := by
    refine lintegral_congr fun a => ?_
    change (f a ^ (1/2:ℝ) * g a) ^ (2:ℝ) = f a * g a ^ (2:ℝ)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2), rpow_half_sq]
  rw [h1, h2, h3] at hold
  calc (∫⁻ a, f a * g a ∂μ) ^ (2:ℝ)
      ≤ ((∫⁻ a, f a ∂μ) ^ (1/2:ℝ) * (∫⁻ a, f a * g a ^ (2:ℝ) ∂μ) ^ (1/2:ℝ)) ^ (2:ℝ) :=
        ENNReal.rpow_le_rpow hold (by norm_num)
    _ = (∫⁻ a, f a ∂μ) * (∫⁻ a, f a * g a ^ (2:ℝ) ∂μ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2), rpow_half_sq,
          rpow_half_sq]

theorem lintegral_mul_sq_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {F u : E → ℝ} (hF : ∀ x, 0 ≤ F x) (hu : ∀ x, 0 ≤ u x)
    (hFm : AEMeasurable F MeasureTheory.volume)
    (hum : AEMeasurable u MeasureTheory.volume) (x : E) :
    (∫⁻ y, ENNReal.ofReal (F (x - y) * u y)) ^ (2:ℝ)
      ≤ (∫⁻ y, ENNReal.ofReal (F (x - y))) * (∫⁻ y, ENNReal.ofReal (F (x - y) * u y ^ 2)) := by
  have hfa : AEMeasurable (fun y : E => ENNReal.ofReal (F (x - y))) MeasureTheory.volume :=
    (hFm.comp_quasiMeasurePreserving
      (MeasureTheory.quasiMeasurePreserving_sub_left_of_right_invariant
        MeasureTheory.volume x)).ennreal_ofReal
  have hua : AEMeasurable (fun y : E => ENNReal.ofReal (u y)) MeasureTheory.volume :=
    hum.ennreal_ofReal
  have key : (∫⁻ a : E, ENNReal.ofReal (F (x - a)) * ENNReal.ofReal (u a)) ^ (2:ℝ)
      ≤ (∫⁻ a : E, ENNReal.ofReal (F (x - a)))
        * (∫⁻ a : E, ENNReal.ofReal (F (x - a)) * ENNReal.ofReal (u a) ^ (2:ℝ)) :=
    lintegral_weighted_cs hfa hua
  have hL : (∫⁻ y, ENNReal.ofReal (F (x - y) * u y))
      = ∫⁻ y, ENNReal.ofReal (F (x - y)) * ENNReal.ofReal (u y) :=
    lintegral_congr fun y => ENNReal.ofReal_mul (hF (x - y))
  have hR : (∫⁻ y, ENNReal.ofReal (F (x - y) * u y ^ 2))
      = ∫⁻ y, ENNReal.ofReal (F (x - y)) * ENNReal.ofReal (u y) ^ (2:ℝ) :=
    lintegral_congr fun y => ofReal_mul_sq (F (x - y)) (u y) (hF (x - y)) (hu y)
  rw [hL, hR]
  exact key

end Work.EllipticEst.InteriorRegularity
