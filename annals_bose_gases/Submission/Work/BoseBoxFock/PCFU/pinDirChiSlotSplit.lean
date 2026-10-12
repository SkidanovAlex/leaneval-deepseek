import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.pinDirChi_le_kinFormB
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.pinDirChiSlotSplit`

The **one-slot bookkeeping of the `χ_ℓ`-weighted Dirichlet content, with the two constants split**:
given the one-body bound

    `∫_{Λ} χ_ℓ(z)² Σ_j (∂_j ψ(z))² ≤ A · fsT ψ + B · ∫_{Λ} ψ²`

(the corpus's `chiSqDirichletFsT` with the two constants kept separate) and the corpus slice
identities (`pinDirChi_slot_slice`, `kinFormB_slot_fsT`, `mass_slice`), the slot-`i` contribution

    `Σ_j ∫_{abox} χ_ℓ(xᵢ)² ‖∂_{i,j}Φ_ℂ‖²`

is dominated by `A` times the slot-`i` contribution `ℓ⁻³ ∫ 1_Λ(xᵢ)·fsT(fibreᵢ)` of the box kinetic
word plus `B` times the state mass — i.e. exactly the statement of
`Work.BoseBoxFock.pinDirChi_slot_le` with the two constants decoupled.

The proof is the one of `pinDirChi_slot_le` (`Submission/Work/BoseBoxFock/pinDirChi_le_kinFormB.lean`)
carried out with `A` and `B` in place of `C₁`; nothing else changes.
-/

namespace Work.BoseBoxFock.PCFU

noncomputable section

open MeasureTheory
open scoped BigOperators

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn
local notation "boxL" => Work.BoseK15.corpusBox.boxL

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

theorem pinDirChiSlotSplit {n : ℕ} {ℓ d s εT b A B : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (i : Fin n)
    (h₁ : ∀ ψ : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      (∫ z in Work.BoseK15.corpusBox.boxL ℓ, (Submission.BoseGases.chiScale ℓ z) ^ 2 *
          (∑ j : Fin 3, (fderiv ℝ ψ z (Submission.BoseGases.kcStdBasis j)) ^ 2))
        ≤ A * Work.BoseKinLoc.fsT ℓ d s εT b 0 ψ
          + B * (∫ z in Work.BoseK15.corpusBox.boxL ℓ, ψ z ^ 2)) :
    (∑ j : Fin 3, ∫ x in Submission.BoseGases.abox n ℓ,
        (Submission.BoseGases.chiScale ℓ (x i)) ^ 2 *
          ‖fderiv ℝ (fun y : Submission.BoseGases.X n => ((Φ y : ℝ) : ℂ)) x
            (Work.BoseBoxFock.slotDirVec i j)‖ ^ 2)
      ≤ A * (ℓ ^ (-3 : ℤ) * (∫ x in Submission.BoseGases.abox n ℓ,
            Work.BoseKinLoc.indU ℓ 0 (x i) *
              Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre n i Φ x)))
          + B * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) := by
  classical
  -- the three corpus slice identities
  have hslice := pinDirChi_slot_slice (ℓ := ℓ) hℓ hΦ i
  obtain ⟨hkinint, hkin⟩ :=
    kinFormB_slot_fsT (ℓ := ℓ) (d := d) (s := s) (εT := εT) (b := b) hℓ hΦ i
  have hmass := mass_slice (ℓ := ℓ) hℓ hΦ.continuous i
  -- joint continuity of the slot integrands
  have hdcont (j : Fin 3) : Continuous
      (Function.uncurry (fun (w : E3) (x' : {k : Fin n // k ≠ i} → E3) =>
        fderiv ℝ (fun z : E3 => Φ (insertCoord i z x')) w
          (Submission.BoseGases.kcStdBasis j))) :=
    continuous_fibre_deriv hΦ i j
  have hFcont (j : Fin 3) : Continuous
      (Function.uncurry (fun (w : E3) (x' : {k : Fin n // k ≠ i} → E3) =>
        (Submission.BoseGases.chiScale ℓ w) ^ 2 *
          (fderiv ℝ (fun z : E3 => Φ (insertCoord i z x')) w
            (Submission.BoseGases.kcStdBasis j)) ^ 2)) :=
    (((Submission.BoseGases.chiScale_continuous ℓ).pow 2).comp continuous_fst).mul
      ((hdcont j).pow 2)
  have hGcont : Continuous
      (Function.uncurry (fun (w : E3) (x' : {k : Fin n // k ≠ i} → E3) =>
        (Submission.BoseGases.chiScale ℓ w) ^ 2 *
          (∑ j : Fin 3, (fderiv ℝ (fun z : E3 => Φ (insertCoord i z x')) w
            (Submission.BoseGases.kcStdBasis j)) ^ 2))) :=
    (((Submission.BoseGases.chiScale_continuous ℓ).pow 2).comp continuous_fst).mul
      (continuous_finsetSum _ (fun j _ => (hdcont j).pow 2))
  have hins : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : E3 × ({k : Fin n // k ≠ i} → E3) => insertCoord i q.1 q.2) :=
    contDiff_insertCoord_comp (P := E3 × ({k : Fin n // k ≠ i} → E3)) (j := i)
      (w := fun q => q.1) (x' := fun q => q.2) contDiff_fst contDiff_snd
  have hmcont : Continuous
      (Function.uncurry (fun (w : E3) (x' : {k : Fin n // k ≠ i} → E3) =>
        (Φ (insertCoord i w x')) ^ 2)) :=
    (hΦ.comp hins).continuous.pow 2
  -- integrability of the uncurried slot integrands on the product of the two compact boxes
  have hFint (j : Fin 3) : Integrable
      (Function.uncurry (fun (w : E3) (x' : {k : Fin n // k ≠ i} → E3) =>
        (Submission.BoseGases.chiScale ℓ w) ^ 2 *
          (fderiv ℝ (fun z : E3 => Φ (insertCoord i z x')) w
            (Submission.BoseGases.kcStdBasis j)) ^ 2))
      ((volume.restrict (boxL ℓ)).prod (volume.restrict (boxPiSet ({k : Fin n // k ≠ i}) ℓ))) :=
    integrable_uncurry_of_continuous hℓ (hFcont j)
  have hGint : Integrable
      (Function.uncurry (fun (w : E3) (x' : {k : Fin n // k ≠ i} → E3) =>
        (Submission.BoseGases.chiScale ℓ w) ^ 2 *
          (∑ j : Fin 3, (fderiv ℝ (fun z : E3 => Φ (insertCoord i z x')) w
            (Submission.BoseGases.kcStdBasis j)) ^ 2)))
      ((volume.restrict (boxL ℓ)).prod (volume.restrict (boxPiSet ({k : Fin n // k ≠ i}) ℓ))) :=
    integrable_uncurry_of_continuous hℓ hGcont
  have hmint : Integrable
      (Function.uncurry (fun (w : E3) (x' : {k : Fin n // k ≠ i} → E3) =>
        (Φ (insertCoord i w x')) ^ 2))
      ((volume.restrict (boxL ℓ)).prod (volume.restrict (boxPiSet ({k : Fin n // k ≠ i}) ℓ))) :=
    integrable_uncurry_of_continuous hℓ hmcont
  have hmint2 : Integrable (fun x' : {k : Fin n // k ≠ i} → E3 =>
      ∫ w in boxL ℓ, (Φ (insertCoord i w x')) ^ 2)
      (volume.restrict (boxPiSet ({k : Fin n // k ≠ i}) ℓ)) :=
    (Integrable.integral_prod_right hmint).congr
      (Filter.Eventually.of_forall fun x' =>
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun w => rfl))
  -- the smoothness of the slot fibres
  have hfib (x' : {k : Fin n // k ≠ i} → E3) :
      ContDiff ℝ (⊤ : ℕ∞) (fun z : E3 => Φ (insertCoord i z x')) :=
    hΦ.comp (contDiff_insertCoord_comp (P := E3) (j := i) (w := fun z : E3 => z)
      (x' := fun _ : E3 => x') contDiff_id contDiff_const)
  -- Step A: the slices
  have hA : (∑ j : Fin 3, ∫ x in Submission.BoseGases.abox n ℓ,
        (Submission.BoseGases.chiScale ℓ (x i)) ^ 2 *
          ‖fderiv ℝ (fun y : Submission.BoseGases.X n => ((Φ y : ℝ) : ℂ)) x
            (Work.BoseBoxFock.slotDirVec i j)‖ ^ 2)
      = ∑ j : Fin 3, ∫ w in boxL ℓ, ∫ x' in boxPiSet ({k : Fin n // k ≠ i}) ℓ,
          (Submission.BoseGases.chiScale ℓ w) ^ 2 *
            (fderiv ℝ (fun z : E3 => Φ (insertCoord i z x')) w
              (Submission.BoseGases.kcStdBasis j)) ^ 2 :=
    Finset.sum_congr rfl (fun j _ => hslice j)
  -- Step B: swap the two integrations in each summand
  have hB : (∑ j : Fin 3, ∫ w in boxL ℓ, ∫ x' in boxPiSet ({k : Fin n // k ≠ i}) ℓ,
          (Submission.BoseGases.chiScale ℓ w) ^ 2 *
            (fderiv ℝ (fun z : E3 => Φ (insertCoord i z x')) w
              (Submission.BoseGases.kcStdBasis j)) ^ 2)
      = ∑ j : Fin 3, ∫ x' in boxPiSet ({k : Fin n // k ≠ i}) ℓ, ∫ w in boxL ℓ,
          (Submission.BoseGases.chiScale ℓ w) ^ 2 *
            (fderiv ℝ (fun z : E3 => Φ (insertCoord i z x')) w
              (Submission.BoseGases.kcStdBasis j)) ^ 2 := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [MeasureTheory.integral_integral_swap]
    exact hFint j
  -- Step C: pull the `j`-sum out of the `x'`-integral
  have hC : (∑ j : Fin 3, ∫ x' in boxPiSet ({k : Fin n // k ≠ i}) ℓ, ∫ w in boxL ℓ,
          (Submission.BoseGases.chiScale ℓ w) ^ 2 *
            (fderiv ℝ (fun z : E3 => Φ (insertCoord i z x')) w
              (Submission.BoseGases.kcStdBasis j)) ^ 2)
      = ∫ x' in boxPiSet ({k : Fin n // k ≠ i}) ℓ,
          ∑ j : Fin 3, ∫ w in boxL ℓ,
            (Submission.BoseGases.chiScale ℓ w) ^ 2 *
              (fderiv ℝ (fun z : E3 => Φ (insertCoord i z x')) w
                (Submission.BoseGases.kcStdBasis j)) ^ 2 :=
    (MeasureTheory.integral_finsetSum (μ := volume.restrict (boxPiSet ({k : Fin n // k ≠ i}) ℓ))
      (s := Finset.univ)
      (f := fun j x' => ∫ w in boxL ℓ, (Submission.BoseGases.chiScale ℓ w) ^ 2 *
        (fderiv ℝ (fun z : E3 => Φ (insertCoord i z x')) w (Submission.BoseGases.kcStdBasis j)) ^ 2)
      (fun j _ => Integrable.integral_prod_right (hFint j))).symm
  -- Step D: the pointwise identification of the summed integrand
  have hDpoint (x' : {k : Fin n // k ≠ i} → E3) :
      (∫ w in boxL ℓ, (Submission.BoseGases.chiScale ℓ w) ^ 2 *
          (∑ j : Fin 3, (fderiv ℝ (fun z : E3 => Φ (insertCoord i z x')) w
            (Submission.BoseGases.kcStdBasis j)) ^ 2))
        = ∑ j : Fin 3, ∫ w in boxL ℓ, (Submission.BoseGases.chiScale ℓ w) ^ 2 *
            (fderiv ℝ (fun z : E3 => Φ (insertCoord i z x')) w
              (Submission.BoseGases.kcStdBasis j)) ^ 2 := by
    have hsplit : (∫ w in boxL ℓ, (Submission.BoseGases.chiScale ℓ w) ^ 2 *
          (∑ j : Fin 3, (fderiv ℝ (fun z : E3 => Φ (insertCoord i z x')) w
            (Submission.BoseGases.kcStdBasis j)) ^ 2))
        = ∫ w in boxL ℓ, ∑ j : Fin 3,
            (Submission.BoseGases.chiScale ℓ w) ^ 2 *
              (fderiv ℝ (fun z : E3 => Φ (insertCoord i z x')) w
                (Submission.BoseGases.kcStdBasis j)) ^ 2 := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun w => ?_))
      dsimp only
      rw [Finset.mul_sum]
    rw [hsplit, MeasureTheory.integral_finsetSum]
    intro j _
    exact integrableOn_boxL_of_continuous hℓ (continuous_slot_integrand hΦ i j x')
  have hD : (∫ x' in boxPiSet ({k : Fin n // k ≠ i}) ℓ,
          ∑ j : Fin 3, ∫ w in boxL ℓ,
            (Submission.BoseGases.chiScale ℓ w) ^ 2 *
              (fderiv ℝ (fun z : E3 => Φ (insertCoord i z x')) w
                (Submission.BoseGases.kcStdBasis j)) ^ 2)
      = ∫ x' in boxPiSet ({k : Fin n // k ≠ i}) ℓ, ∫ w in boxL ℓ,
          (Submission.BoseGases.chiScale ℓ w) ^ 2 *
            (∑ j : Fin 3, (fderiv ℝ (fun z : E3 => Φ (insertCoord i z x')) w
              (Submission.BoseGases.kcStdBasis j)) ^ 2) :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x' =>
      (hDpoint x').symm))
  -- Step E: the one-body bound, fibrewise
  have hE : (∫ x' in boxPiSet ({k : Fin n // k ≠ i}) ℓ, ∫ w in boxL ℓ,
          (Submission.BoseGases.chiScale ℓ w) ^ 2 *
            (∑ j : Fin 3, (fderiv ℝ (fun z : E3 => Φ (insertCoord i z x')) w
              (Submission.BoseGases.kcStdBasis j)) ^ 2))
      ≤ ∫ x' in boxPiSet ({k : Fin n // k ≠ i}) ℓ,
          (A * Work.BoseKinLoc.fsT ℓ d s εT b 0
              (fun z : E3 => Φ (insertCoord i z x'))
            + B * (∫ w in boxL ℓ, (Φ (insertCoord i w x')) ^ 2)) := by
    refine MeasureTheory.integral_mono_ae (Integrable.integral_prod_right hGint)
      (Integrable.add (hkinint.const_mul A) (hmint2.const_mul B))
      (Filter.Eventually.of_forall (fun x' => h₁ _ (hfib x')))
  -- Step F: split the sum of the two integrals
  have hF : (∫ x' in boxPiSet ({k : Fin n // k ≠ i}) ℓ,
          (A * Work.BoseKinLoc.fsT ℓ d s εT b 0
              (fun z : E3 => Φ (insertCoord i z x'))
            + B * (∫ w in boxL ℓ, (Φ (insertCoord i w x')) ^ 2)))
      = A * (∫ x' in boxPiSet ({k : Fin n // k ≠ i}) ℓ,
            Work.BoseKinLoc.fsT ℓ d s εT b 0 (fun z : E3 => Φ (insertCoord i z x')))
          + B * (∫ x' in boxPiSet ({k : Fin n // k ≠ i}) ℓ,
              ∫ w in boxL ℓ, (Φ (insertCoord i w x')) ^ 2) := by
    rw [MeasureTheory.integral_add (hkinint.const_mul A) (hmint2.const_mul B),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  -- Step G: the two slice identities
  have hG : A * (∫ x' in boxPiSet ({k : Fin n // k ≠ i}) ℓ,
          Work.BoseKinLoc.fsT ℓ d s εT b 0 (fun z : E3 => Φ (insertCoord i z x')))
        + B * (∫ x' in boxPiSet ({k : Fin n // k ≠ i}) ℓ,
            ∫ w in boxL ℓ, (Φ (insertCoord i w x')) ^ 2)
      = A * (ℓ ^ (-3 : ℤ) * (∫ x in Submission.BoseGases.abox n ℓ,
            Work.BoseKinLoc.indU ℓ 0 (x i) *
              Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre n i Φ x)))
          + B * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) := by
    rw [← hkin, ← hmass]
  calc (∑ j : Fin 3, ∫ x in Submission.BoseGases.abox n ℓ,
        (Submission.BoseGases.chiScale ℓ (x i)) ^ 2 *
          ‖fderiv ℝ (fun y : Submission.BoseGases.X n => ((Φ y : ℝ) : ℂ)) x
            (Work.BoseBoxFock.slotDirVec i j)‖ ^ 2)
      = ∑ j : Fin 3, ∫ w in boxL ℓ, ∫ x' in boxPiSet ({k : Fin n // k ≠ i}) ℓ,
          (Submission.BoseGases.chiScale ℓ w) ^ 2 *
            (fderiv ℝ (fun z : E3 => Φ (insertCoord i z x')) w
              (Submission.BoseGases.kcStdBasis j)) ^ 2 := hA
    _ = ∑ j : Fin 3, ∫ x' in boxPiSet ({k : Fin n // k ≠ i}) ℓ, ∫ w in boxL ℓ,
          (Submission.BoseGases.chiScale ℓ w) ^ 2 *
            (fderiv ℝ (fun z : E3 => Φ (insertCoord i z x')) w
              (Submission.BoseGases.kcStdBasis j)) ^ 2 := hB
    _ = ∫ x' in boxPiSet ({k : Fin n // k ≠ i}) ℓ,
          ∑ j : Fin 3, ∫ w in boxL ℓ,
            (Submission.BoseGases.chiScale ℓ w) ^ 2 *
              (fderiv ℝ (fun z : E3 => Φ (insertCoord i z x')) w
                (Submission.BoseGases.kcStdBasis j)) ^ 2 := hC
    _ = ∫ x' in boxPiSet ({k : Fin n // k ≠ i}) ℓ, ∫ w in boxL ℓ,
          (Submission.BoseGases.chiScale ℓ w) ^ 2 *
            (∑ j : Fin 3, (fderiv ℝ (fun z : E3 => Φ (insertCoord i z x')) w
              (Submission.BoseGases.kcStdBasis j)) ^ 2) := hD
    _ ≤ ∫ x' in boxPiSet ({k : Fin n // k ≠ i}) ℓ,
          (A * Work.BoseKinLoc.fsT ℓ d s εT b 0
              (fun z : E3 => Φ (insertCoord i z x'))
            + B * (∫ w in boxL ℓ, (Φ (insertCoord i w x')) ^ 2)) := hE
    _ = A * (∫ x' in boxPiSet ({k : Fin n // k ≠ i}) ℓ,
            Work.BoseKinLoc.fsT ℓ d s εT b 0 (fun z : E3 => Φ (insertCoord i z x')))
          + B * (∫ x' in boxPiSet ({k : Fin n // k ≠ i}) ℓ,
              ∫ w in boxL ℓ, (Φ (insertCoord i w x')) ^ 2) := hF
    _ = A * (ℓ ^ (-3 : ℤ) * (∫ x in Submission.BoseGases.abox n ℓ,
            Work.BoseKinLoc.indU ℓ 0 (x i) *
              Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre n i Φ x)))
          + B * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) := hG

end

end Work.BoseBoxFock.PCFU
