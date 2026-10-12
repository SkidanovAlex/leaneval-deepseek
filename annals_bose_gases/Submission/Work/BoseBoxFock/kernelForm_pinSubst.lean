import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.MB.SlotWeakBase
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

/-- **Pinning away from the diagonal.**  If the weight functions `w₁, v₁, w₂, v₂`
agree (pointwise, for every pair of indices) with the functions `W₁, V₁, W₂, V₂`
almost everywhere on the one-particle space, then the kernel form may be computed
with `W₁, V₁, W₂, V₂` in place of the `η`'s.

The content is the transfer of the a.e. hypotheses on the one-particle variable
`z` to the a.e. statement in the many-particle variable `x`, through the
coordinate projection `x ↦ xᵢ` (which pulls null sets back to null sets), and
then `integral_congr_ae` in each of the three integration variables. -/
theorem kernelForm_pinSubst {m n : ℕ} {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    {ι κ : Type} [DecidableEq ι] [DecidableEq κ] (Idx : Finset ι) (Jdx : Finset κ)
    (a : ι → κ → ℂ) (w₁ v₁ w₂ v₂ : ι → κ → Fin m → ℝ)
    (W₁ V₁ W₂ V₂ : ι → κ → EuclideanSpace ℝ (Fin 3) → ℂ)
    (hW₁ : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))),
      ∀ p ∈ Idx, ∀ q ∈ Jdx, Work.BoseDict.etaOf e (w₁ p q) z = W₁ p q z)
    (hV₁ : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))),
      ∀ p ∈ Idx, ∀ q ∈ Jdx, Work.BoseDict.etaOf e (v₁ p q) z = V₁ p q z)
    (hW₂ : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))),
      ∀ p ∈ Idx, ∀ q ∈ Jdx, Work.BoseDict.etaOf e (w₂ p q) z = W₂ p q z)
    (hV₂ : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))),
      ∀ p ∈ Idx, ∀ q ∈ Jdx, Work.BoseDict.etaOf e (v₂ p q) z = V₂ p q z)
    (Θ : (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ) (i j : Fin n) :
    (∫ x : Fin n → EuclideanSpace ℝ (Fin 3), ∫ y : EuclideanSpace ℝ (Fin 3),
        ∫ u : EuclideanSpace ℝ (Fin 3), (starRingEnd ℂ) (Θ x) *
        (∑ p ∈ Idx, ∑ q ∈ Jdx, a p q *
          (Work.BoseDict.etaOf e (w₁ p q) (x i) * (starRingEnd ℂ) (Work.BoseDict.etaOf e (v₁ p q) y)
            * Work.BoseDict.etaOf e (w₂ p q) (x j) * (starRingEnd ℂ) (Work.BoseDict.etaOf e (v₂ p q) u)))
        * Θ (Function.update (Function.update x i y) j u))
      = (∫ x : Fin n → EuclideanSpace ℝ (Fin 3), ∫ y : EuclideanSpace ℝ (Fin 3),
        ∫ u : EuclideanSpace ℝ (Fin 3), (starRingEnd ℂ) (Θ x) *
        (∑ p ∈ Idx, ∑ q ∈ Jdx, a p q *
          (W₁ p q (x i) * (starRingEnd ℂ) (V₁ p q y)
            * W₂ p q (x j) * (starRingEnd ℂ) (V₂ p q u)))
        * Θ (Function.update (Function.update x i y) j u)) := by
  -- The a.e. hypothesis on the one-particle space, transferred to the `i`-th coordinate.
  have hx₁ : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin n → EuclideanSpace ℝ (Fin 3))),
      ∀ p ∈ Idx, ∀ q ∈ Jdx, Work.BoseDict.etaOf e (w₁ p q) (x i) = W₁ p q (x i) := by
    rw [MeasureTheory.ae_iff]
    have h0 : (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))
        {z | ¬ (∀ p ∈ Idx, ∀ q ∈ Jdx, Work.BoseDict.etaOf e (w₁ p q) z = W₁ p q z)} = 0 :=
      MeasureTheory.ae_iff.mp hW₁
    have heq : {x : Fin n → EuclideanSpace ℝ (Fin 3) |
        ¬ (∀ p ∈ Idx, ∀ q ∈ Jdx, Work.BoseDict.etaOf e (w₁ p q) (x i) = W₁ p q (x i))}
        = (fun x : Fin n → EuclideanSpace ℝ (Fin 3) => x i) ⁻¹'
          {z | ¬ (∀ p ∈ Idx, ∀ q ∈ Jdx, Work.BoseDict.etaOf e (w₁ p q) z = W₁ p q z)} := by
      ext x; rfl
    rw [heq]
    exact MeasureTheory.Measure.pi_eval_preimage_null
      (μ := fun _ : Fin n => (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))) h0
  -- Same for the `j`-th coordinate.
  have hx₂ : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin n → EuclideanSpace ℝ (Fin 3))),
      ∀ p ∈ Idx, ∀ q ∈ Jdx, Work.BoseDict.etaOf e (w₂ p q) (x j) = W₂ p q (x j) := by
    rw [MeasureTheory.ae_iff]
    have h0 : (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))
        {z | ¬ (∀ p ∈ Idx, ∀ q ∈ Jdx, Work.BoseDict.etaOf e (w₂ p q) z = W₂ p q z)} = 0 :=
      MeasureTheory.ae_iff.mp hW₂
    have heq : {x : Fin n → EuclideanSpace ℝ (Fin 3) |
        ¬ (∀ p ∈ Idx, ∀ q ∈ Jdx, Work.BoseDict.etaOf e (w₂ p q) (x j) = W₂ p q (x j))}
        = (fun x : Fin n → EuclideanSpace ℝ (Fin 3) => x j) ⁻¹'
          {z | ¬ (∀ p ∈ Idx, ∀ q ∈ Jdx, Work.BoseDict.etaOf e (w₂ p q) z = W₂ p q z)} := by
      ext x; rfl
    rw [heq]
    exact MeasureTheory.Measure.pi_eval_preimage_null
      (μ := fun _ : Fin n => (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))) h0
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [hx₁, hx₂] with x hx1 hx2
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [hV₁] with y hy
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [hV₂] with u hu
  have hsum : (∑ p ∈ Idx, ∑ q ∈ Jdx, a p q *
      (Work.BoseDict.etaOf e (w₁ p q) (x i) * (starRingEnd ℂ) (Work.BoseDict.etaOf e (v₁ p q) y)
        * Work.BoseDict.etaOf e (w₂ p q) (x j) * (starRingEnd ℂ) (Work.BoseDict.etaOf e (v₂ p q) u)))
      = (∑ p ∈ Idx, ∑ q ∈ Jdx, a p q *
      (W₁ p q (x i) * (starRingEnd ℂ) (V₁ p q y)
        * W₂ p q (x j) * (starRingEnd ℂ) (V₂ p q u))) := by
    refine Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => ?_
    rw [hx1 p hp q hq, hy p hp q hq, hx2 p hp q hq, hu p hp q hq]
  rw [hsum]

end Work.BoseBoxFock
