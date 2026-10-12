import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.boxQInd_sq_aesm
import Submission.Work.BoseFixB1S.fibreMean_sq_integrableOn
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Work.BoseFixB1S

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **Pointwise unfolding of the projection.**  The mean-free box projection is the box indicator
in the slot `i` times the deviation of `Ψ` from its (un-normalised) `A`-fibre mean in that slot. -/
private lemma boxQInd_eq_indicator_mul_sub_fibreMean {volA : ℝ} {A : Set ℝ³} {N : ℕ}
    (i : Fin N) (Ψ : X N → ℝ) (x : X N) :
    UBBInputs8.boxQInd volA A i Ψ x
      = A.indicator (fun _ => (1 : ℝ)) (x i)
        * (Ψ x - (1 / volA) * ∫ z in A, Ψ (Function.update x i z)) := by
  simp only [UBBInputs8.boxQInd, UBBInputs8.boxPInd]
  ring

/-- **Elementary pointwise bound** for the projection: the box indicator costs nothing
(`1_A(xᵢ) ∈ {0,1}`) and `(a − b)² ≤ 2a² + 2b²`. -/
private lemma boxQInd_sq_le {volA : ℝ} {A : Set ℝ³} {N : ℕ} (i : Fin N) (Ψ : X N → ℝ)
    (x : X N) :
    (UBBInputs8.boxQInd volA A i Ψ x) ^ 2
      ≤ 2 * (Ψ x) ^ 2 + 2 * ((1 / volA) * ∫ z in A, Ψ (Function.update x i z)) ^ 2 := by
  rw [boxQInd_eq_indicator_mul_sub_fibreMean i Ψ x]
  have hind1 : A.indicator (fun _ => (1 : ℝ)) (x i) = 0
      ∨ A.indicator (fun _ => (1 : ℝ)) (x i) = 1 := by
    by_cases h : x i ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
  have hstep : (A.indicator (fun _ => (1 : ℝ)) (x i)
      * (Ψ x - (1 / volA) * ∫ z in A, Ψ (Function.update x i z))) ^ 2
      ≤ (Ψ x - (1 / volA) * ∫ z in A, Ψ (Function.update x i z)) ^ 2 := by
    rcases hind1 with h | h
    · rw [h]
      nlinarith [sq_nonneg (Ψ x - (1 / volA) * ∫ z in A, Ψ (Function.update x i z))]
    · rw [h]
      nlinarith [sq_nonneg (Ψ x - (1 / volA) * ∫ z in A, Ψ (Function.update x i z))]
  have hamgm : (Ψ x - (1 / volA) * ∫ z in A, Ψ (Function.update x i z)) ^ 2
      ≤ 2 * (Ψ x) ^ 2 + 2 * ((1 / volA) * ∫ z in A, Ψ (Function.update x i z)) ^ 2 := by
    nlinarith [sq_nonneg (Ψ x + (1 / volA) * ∫ z in A, Ψ (Function.update x i z))]
  linarith [hstep, hamgm]

/-! ## The target -/

theorem integrableOn_boxQInd_sq {a volA : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hvolApos : 0 < volA)
    (hA : MeasurableSet A) (hsub : A ⊆ Submission.BoseGases.acube a) {N : ℕ} (i : Fin N)
    (Ψ : Submission.BoseGases.X N → ℝ)
    (hΨm : MeasureTheory.AEStronglyMeasurable Ψ
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox N a)))
    (hΨ2 : MeasureTheory.Integrable (fun x : Submission.BoseGases.X N => (Ψ x) ^ 2)
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox N a))) :
    MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N => (Work.UBBInputs8.boxQInd volA A i Ψ x) ^ 2)
      (Submission.BoseGases.abox N a) MeasureTheory.volume := by
  -- the two delegated pieces, stated at the ambient box measure
  have hM2 := fibreMean_sq_integrableOn hvolA hvolApos hA hsub i Ψ hΨm hΨ2
  have hBsm := boxQInd_sq_aesm hvolA hvolApos hA hsub i Ψ hΨm
  -- `N` is a successor (`Fin N` is inhabited)
  have hN : N ≠ 0 := fun h => by subst h; exact i.elim0
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN
  show Integrable (fun x : X (k + 1) => (UBBInputs8.boxQInd volA A i Ψ x) ^ 2)
    ((volume : Measure (X (k + 1))).restrict (abox (k + 1) a))
  -- the box measure is the product measure, where the fibre analysis lives
  rw [restrict_abox_eq_pi (k + 1) a] at hΨm hΨ2 hM2 hBsm ⊢
  -- the dominating function `2Ψ² + 2M²`
  have hD : Integrable (fun x : X (k + 1) =>
      2 * (Ψ x) ^ 2 + 2 * ((1 / volA) * ∫ z in A, Ψ (Function.update x i z)) ^ 2)
      (Measure.pi (fun _ : Fin (k + 1) => (volume : Measure ℝ³).restrict (acube a))) :=
    (hΨ2.const_mul 2).add (hM2.const_mul 2)
  refine Integrable.mono' hD hBsm ?_
  filter_upwards with x
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact boxQInd_sq_le i Ψ x

end Work.BoseFixB1S
