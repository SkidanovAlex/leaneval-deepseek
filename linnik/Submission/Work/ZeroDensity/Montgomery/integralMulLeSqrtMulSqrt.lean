import Mathlib

namespace Work.ZeroDensity.Montgomery

open MeasureTheory intervalIntegral

/-- Cauchy–Schwarz (Hölder with conjugate exponents `2` and `2`) for interval integrals of
nonnegative continuous functions: the integral of `f * k` is bounded by the product of the
square roots of the integrals of `f ^ 2` and `k ^ 2`. -/
lemma integralMulLeSqrtMulSqrt {f k : ℝ → ℝ} (hf : Continuous f) (hk : Continuous k)
    (hf0 : ∀ x, 0 ≤ f x) (hk0 : ∀ x, 0 ≤ k x) {A B : ℝ} (hAB : A ≤ B) :
    ∫ x in A..B, f x * k x ≤ Real.sqrt (∫ x in A..B, f x ^ 2) * Real.sqrt (∫ x in A..B, k x ^ 2) := by
  obtain ⟨Cf, hCf⟩ := isCompact_Icc.exists_bound_of_continuousOn hf.continuousOn
  obtain ⟨Ck, hCk⟩ := isCompact_Icc.exists_bound_of_continuousOn hk.continuousOn
  have hmemf : MemLp f (ENNReal.ofReal 2) (volume.restrict (Set.Ioc A B)) :=
    MemLp.of_bound hf.aestronglyMeasurable Cf <| by
      rw [ae_restrict_iff' measurableSet_Ioc]
      exact Filter.Eventually.of_forall fun x hx => hCf x (Set.Ioc_subset_Icc_self hx)
  have hmemk : MemLp k (ENNReal.ofReal 2) (volume.restrict (Set.Ioc A B)) :=
    MemLp.of_bound hk.aestronglyMeasurable Ck <| by
      rw [ae_restrict_iff' measurableSet_Ioc]
      exact Filter.Eventually.of_forall fun x hx => hCk x (Set.Ioc_subset_Icc_self hx)
  have hnf : 0 ≤ᵐ[volume.restrict (Set.Ioc A B)] f :=
    Filter.Eventually.of_forall fun x => hf0 x
  have hnk : 0 ≤ᵐ[volume.restrict (Set.Ioc A B)] k :=
    Filter.Eventually.of_forall fun x => hk0 x
  have hholder := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
      (μ := volume.restrict (Set.Ioc A B)) (f := f) (g := k)
      Real.HolderConjugate.two_two hnf hnk hmemf hmemk
  have hL : ∫ x in A..B, f x * k x
      = ∫ a, f a * k a ∂(volume.restrict (Set.Ioc A B)) := by
    rw [intervalIntegral.integral_of_le hAB]
  have hRf : ∫ x in A..B, f x ^ 2
      = ∫ a, f a ^ (2:ℝ) ∂(volume.restrict (Set.Ioc A B)) := by
    rw [intervalIntegral.integral_of_le hAB]
    exact integral_congr_ae (Filter.Eventually.of_forall fun a => (Real.rpow_two (f a)).symm)
  have hRk : ∫ x in A..B, k x ^ 2
      = ∫ a, k a ^ (2:ℝ) ∂(volume.restrict (Set.Ioc A B)) := by
    rw [intervalIntegral.integral_of_le hAB]
    exact integral_congr_ae (Filter.Eventually.of_forall fun a => (Real.rpow_two (k a)).symm)
  rw [hL, hRf, hRk]
  calc ∫ a, f a * k a ∂(volume.restrict (Set.Ioc A B))
      ≤ (∫ a, f a ^ (2:ℝ) ∂(volume.restrict (Set.Ioc A B))) ^ (1/2:ℝ)
          * (∫ a, k a ^ (2:ℝ) ∂(volume.restrict (Set.Ioc A B))) ^ (1/2:ℝ) := hholder
    _ = Real.sqrt (∫ a, f a ^ (2:ℝ) ∂(volume.restrict (Set.Ioc A B)))
          * Real.sqrt (∫ a, k a ^ (2:ℝ) ∂(volume.restrict (Set.Ioc A B))) := by
        simp only [Real.sqrt_eq_rpow]

end Work.ZeroDensity.Montgomery
