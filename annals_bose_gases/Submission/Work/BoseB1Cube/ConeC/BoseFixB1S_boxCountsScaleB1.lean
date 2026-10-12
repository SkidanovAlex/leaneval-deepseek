import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.BoxQWords
import Submission.Work.hlocWire.boxPInd_smul
import Submission.Work.hlocWire.boxQInd_smul
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseFixB1S

open Submission.BoseGases

/-! ## 1. The box projections are linear in the state

The corpus's `Work.hlocWire.boxPInd_smul`/`boxQInd_smul` record the `•`-form; the rescaled
states in the a-priori closure are written pointwise, `fun x => t * Φ x`, so we record the
same one scaling step in that form. -/

/-- `P_{B,i}` is linear in the state, in pointwise form. -/
lemma boxPInd_const_mul_coneC {N : ℕ} (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3))) (i : Fin N)
    (Φ : X N → ℝ) (t : ℝ) :
    Work.UBBInputs8.boxPInd volA A i (fun x => t * Φ x)
      = fun x => t * Work.UBBInputs8.boxPInd volA A i Φ x := by
  ext x
  simp only [Work.UBBInputs8.boxPInd]
  rw [MeasureTheory.integral_const_mul]
  ring

/-- `Q_{B,i} = 1_{B,i} − P_{B,i}` is linear in the state, in pointwise form. -/
lemma boxQInd_const_mul {N : ℕ} (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3))) (i : Fin N)
    (Φ : X N → ℝ) (t : ℝ) :
    Work.UBBInputs8.boxQInd volA A i (fun x => t * Φ x)
      = fun x => t * Work.UBBInputs8.boxQInd volA A i Φ x := by
  ext x
  simp only [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd]
  rw [MeasureTheory.integral_const_mul]
  ring

/-! ## 2. One integral identity -/

/-- `∫ (t·f)² = t² ∫ f²` over the ambient box: the one unconditional integral identity used for
each summand of each count. -/
lemma integral_sq_const_mul {N : ℕ} (ℓ t : ℝ) (f : X N → ℝ) :
    (∫ x in abox N ℓ, (t * f x) ^ 2) = t ^ 2 * ∫ x in abox N ℓ, (f x) ^ 2 := by
  rw [← MeasureTheory.integral_const_mul]
  congr 1
  funext x
  ring

/-! ## 3. The four counts -/

/-- Quadratic homogeneity of the localised flat count `S = Σᵢ∫(PᵢΦ)²`. -/
lemma boxFlatCount_scale {N : ℕ} (volA ℓ : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (Φ : X N → ℝ) (t : ℝ) :
    boxFlatCount volA ℓ A (fun x => t * Φ x) = t ^ 2 * boxFlatCount volA ℓ A Φ := by
  unfold boxFlatCount
  simp only [boxPInd_const_mul_coneC]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ =>
    integral_sq_const_mul ℓ t (Work.UBBInputs8.boxPInd volA A i Φ))

/-- Quadratic homogeneity of the localised pair-condensate count `cS₂ = Σ_{i<j}∫(PᵢPⱼΦ)²`. -/
lemma boxPairCount_scale {N : ℕ} (volA ℓ : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (Φ : X N → ℝ) (t : ℝ) :
    boxPairCount volA ℓ A (fun x => t * Φ x) = t ^ 2 * boxPairCount volA ℓ A Φ := by
  unfold boxPairCount
  simp only [boxPInd_const_mul_coneC]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun p _ =>
    integral_sq_const_mul ℓ t
      (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ)))

/-- Quadratic homogeneity of the localised excited count `n₊ = Σᵢ∫(QᵢΦ)²`. -/
lemma boxQCount_scale {N : ℕ} (volA ℓ : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (Φ : X N → ℝ) (t : ℝ) :
    boxQCount volA ℓ A (fun x => t * Φ x) = t ^ 2 * boxQCount volA ℓ A Φ := by
  unfold boxQCount
  simp only [boxQInd_const_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ =>
    integral_sq_const_mul ℓ t (Work.UBBInputs8.boxQInd volA A i Φ))

/-- Quadratic homogeneity of FS's excited count `n₊(B) = Σᵢ‖Q_{B,i}Φ‖²`, which is
definitionally `boxQCount`. -/
lemma cnPlusBoxInd_scale {N : ℕ} (volA ℓ : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (Φ : X N → ℝ) (t : ℝ) :
    Work.UBBInputs8.cnPlusBoxInd ℓ A volA (fun x => t * Φ x)
      = t ^ 2 * Work.UBBInputs8.cnPlusBoxInd ℓ A volA Φ := by
  simpa only [boxQCount, Work.UBBInputs8.cnPlusBoxInd] using boxQCount_scale volA ℓ A Φ t

/-! ## 4. The target -/

theorem boxCountsScaleB1 {N : ℕ} (volA ℓ : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (Φ : Submission.BoseGases.X N → ℝ) (t : ℝ) :
    Work.BoseFixB1S.boxFlatCount volA ℓ A (fun x => t * Φ x)
        = t ^ 2 * Work.BoseFixB1S.boxFlatCount volA ℓ A Φ
      ∧ Work.BoseFixB1S.boxPairCount volA ℓ A (fun x => t * Φ x)
        = t ^ 2 * Work.BoseFixB1S.boxPairCount volA ℓ A Φ
      ∧ Work.BoseFixB1S.boxQCount volA ℓ A (fun x => t * Φ x)
        = t ^ 2 * Work.BoseFixB1S.boxQCount volA ℓ A Φ
      ∧ Work.UBBInputs8.cnPlusBoxInd ℓ A volA (fun x => t * Φ x)
        = t ^ 2 * Work.UBBInputs8.cnPlusBoxInd ℓ A volA Φ :=
  ⟨boxFlatCount_scale volA ℓ A Φ t, boxPairCount_scale volA ℓ A Φ t,
    boxQCount_scale volA ℓ A Φ t, cnPlusBoxInd_scale volA ℓ A Φ t⟩

end Work.BoseFixB1S
