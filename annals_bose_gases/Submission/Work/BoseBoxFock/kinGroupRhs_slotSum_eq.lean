import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.gapRowSum
import Submission.Work.BoseBoxFock.momRowSum
import Submission.Work.BoseFixB2.DvApriori.KinOffdiag.pieces_integrableOn_fibre
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.kinGroupRhs_slotSum_eq`

The box-restricted kinetic group `kinFormB` is the slot sum of the localised kinetic word `fsT`
(FS `eq:DefT`), and the right-hand side of the frozen pair-form target subtracts the two box gaps
`(b/4)·ℓ⁻²·n₊` (gap), `(b/100)·ε_T(dℓ)⁻²·n₊^H` (large momenta).  This module proves that the
slot sum of the *full* difference (kinetic word minus the two gaps, read on the slot fibres) is
exactly that right-hand side — i.e. the three rows are consistent slot by slot.

The proof has three ingredients, all of them already in the corpus:

* **per slot**, the box integral of the difference is the difference of the box integrals
  (`slot_integral_split`): the constants `b/4`, `b/100·ε_T` come out, and the two bare forms
  `gapBare`, `momForm` are recognised as the gap/momentum words at unit parameters
  (`gapWord ℓ b 0 ψ = bℓ⁻²·gapBare ℓ 0 ψ`, `momWord ℓ d ε_T b 0 ψ = bε_T(dℓ)⁻²·momForm ℓ d 0 ψ`);
  the integral splitting needs `IntegrableOn` of the three slot integrands
  (`Work.BoseFixB2.Sector.integrableOn_fsT_fibre_smooth` for the word,
  `Work.BoseFixB2.DvApriori.KinOffdiag.pieces_integrableOn_fibre` for the two words) and the
  (unconditional) Bochner linearity `integral_sub`, `integral_const_mul`;
* **gap row**: `Σ_j ∫ 1_Λ(x_j)·gapWord ℓ 1 0 (fibre_j Φ) = ℓ·n₊` (`gapRowSum`, i.e. the peel
  `Work.BoseFixB1.slotSum_gapWord_eq_b_cnPlus` at `b = 1`), so that
  `Σ_j ℓ⁻³∫ … = ℓ⁻²·n₊`;
* **momentum row**: `Σ_j ∫ 1_Λ(x_j)·momWord ℓ d 1 1 0 (fibre_j Φ) = (dℓ)⁻²·(ℓ³·n₊^H)`
  (`momRowSum`), so that `Σ_j ℓ⁻³∫ … = (dℓ)⁻²·n₊^H`;
* the kinetic row is `kinFormB` by definition, and `ℓ⁻³ℓ³ = 1` for `ℓ > 0`.
-/

namespace Work.BoseBoxFock

open MeasureTheory
open scoped BigOperators

/-- **Per-slot splitting of the box kinetic integrand.**  For every slot `j`, the box integral of
`1_Λ(x_j)·(fsT − (b/4)(ℓ²)⁻¹gapBare − (b/100)ε_T(dℓ)⁻²momForm)` on the fibre of `j` is the
corresponding difference of the three box integrals, the two bare forms being the gap and momentum
words at unit parameters.  The two `IntegrableOn` inputs make the Bochner integral split. -/
private lemma slot_integral_split {n : ℕ} {ℓ s d eT b : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (j : Fin n) :
    (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x j) *
        (Work.BoseKinLoc.fsT ℓ d s eT b 0 (Work.BoseKinLoc.fibre n j Φ x)
          - b / 4 * ((ℓ ^ 2)⁻¹ * Work.BoseKinLoc.gapBare ℓ 0 (Work.BoseKinLoc.fibre n j Φ x))
          - b / 100 * (eT * (d * ℓ) ^ (-2 : ℤ) * Work.BoseKinLoc.momForm ℓ d 0 (Work.BoseKinLoc.fibre n j Φ x))))
      = (∫ x in Submission.BoseGases.abox n ℓ,
            Work.BoseKinLoc.indU ℓ 0 (x j) * Work.BoseKinLoc.fsT ℓ d s eT b 0 (Work.BoseKinLoc.fibre n j Φ x))
        - b / 4 * (∫ x in Submission.BoseGases.abox n ℓ,
            Work.BoseKinLoc.indU ℓ 0 (x j) * Work.BoseKinLoc.gapWord ℓ 1 0 (Work.BoseKinLoc.fibre n j Φ x))
        - b / 100 * eT * (∫ x in Submission.BoseGases.abox n ℓ,
            Work.BoseKinLoc.indU ℓ 0 (x j) * Work.BoseKinLoc.momWord ℓ d 1 1 0 (Work.BoseKinLoc.fibre n j Φ x)) := by
  -- the two bare forms are the words at unit parameters
  have hGW : ∀ ψ : EuclideanSpace ℝ (Fin 3) → ℝ,
      (ℓ ^ 2)⁻¹ * Work.BoseKinLoc.gapBare ℓ 0 ψ = Work.BoseKinLoc.gapWord ℓ 1 0 ψ := by
    intro ψ
    simp only [Work.BoseKinLoc.gapWord, one_mul]
    rw [show (-2 : ℤ) = -(2 : ℤ) by norm_num, zpow_neg, zpow_ofNat]
  have hMW : ∀ ψ : EuclideanSpace ℝ (Fin 3) → ℝ,
      eT * (d * ℓ) ^ (-2 : ℤ) * Work.BoseKinLoc.momForm ℓ d 0 ψ
        = eT * Work.BoseKinLoc.momWord ℓ d 1 1 0 ψ := by
    intro ψ
    simp only [Work.BoseKinLoc.momWord, one_mul]
    ring
  -- integrability of the three pieces on the box
  have hI1 : Integrable (fun x : Submission.BoseGases.X n =>
      Work.BoseKinLoc.indU ℓ 0 (x j) * Work.BoseKinLoc.fsT ℓ d s eT b 0 (Work.BoseKinLoc.fibre n j Φ x))
      (volume.restrict (Submission.BoseGases.abox n ℓ)) :=
    Work.BoseFixB2.Sector.integrableOn_fsT_fibre_smooth hℓ j hΦ
  have hI2 : Integrable (fun x : Submission.BoseGases.X n =>
      (b / 4) * (Work.BoseKinLoc.indU ℓ 0 (x j) * Work.BoseKinLoc.gapWord ℓ 1 0 (Work.BoseKinLoc.fibre n j Φ x)))
      (volume.restrict (Submission.BoseGases.abox n ℓ)) :=
    (Work.BoseFixB2.DvApriori.KinOffdiag.pieces_integrableOn_fibre
      (ℓ := ℓ) (d := d) (s := s) (εT := eT) (b := 1) hℓ j hΦ).1.const_mul (b / 4)
  have hI3 : Integrable (fun x : Submission.BoseGases.X n =>
      ((b / 100) * eT) * (Work.BoseKinLoc.indU ℓ 0 (x j) * Work.BoseKinLoc.momWord ℓ d 1 1 0 (Work.BoseKinLoc.fibre n j Φ x)))
      (volume.restrict (Submission.BoseGases.abox n ℓ)) :=
    (Work.BoseFixB2.DvApriori.KinOffdiag.pieces_integrableOn_fibre
      (ℓ := ℓ) (d := d) (s := s) (εT := 1) (b := 1) hℓ j hΦ).2.1.const_mul ((b / 100) * eT)
  -- the pointwise rewriting of the integrand
  have hpt : ∀ x : Submission.BoseGases.X n,
      Work.BoseKinLoc.indU ℓ 0 (x j) *
        (Work.BoseKinLoc.fsT ℓ d s eT b 0 (Work.BoseKinLoc.fibre n j Φ x)
          - b / 4 * ((ℓ ^ 2)⁻¹ * Work.BoseKinLoc.gapBare ℓ 0 (Work.BoseKinLoc.fibre n j Φ x))
          - b / 100 * (eT * (d * ℓ) ^ (-2 : ℤ) * Work.BoseKinLoc.momForm ℓ d 0 (Work.BoseKinLoc.fibre n j Φ x)))
        = ((Work.BoseKinLoc.indU ℓ 0 (x j) * Work.BoseKinLoc.fsT ℓ d s eT b 0 (Work.BoseKinLoc.fibre n j Φ x))
            - (b / 4) * (Work.BoseKinLoc.indU ℓ 0 (x j) * Work.BoseKinLoc.gapWord ℓ 1 0 (Work.BoseKinLoc.fibre n j Φ x)))
          - ((b / 100) * eT) * (Work.BoseKinLoc.indU ℓ 0 (x j) * Work.BoseKinLoc.momWord ℓ d 1 1 0 (Work.BoseKinLoc.fibre n j Φ x)) := by
    intro x
    rw [hGW (Work.BoseKinLoc.fibre n j Φ x), hMW (Work.BoseKinLoc.fibre n j Φ x)]
    ring
  calc (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x j) *
        (Work.BoseKinLoc.fsT ℓ d s eT b 0 (Work.BoseKinLoc.fibre n j Φ x)
          - b / 4 * ((ℓ ^ 2)⁻¹ * Work.BoseKinLoc.gapBare ℓ 0 (Work.BoseKinLoc.fibre n j Φ x))
          - b / 100 * (eT * (d * ℓ) ^ (-2 : ℤ) * Work.BoseKinLoc.momForm ℓ d 0 (Work.BoseKinLoc.fibre n j Φ x))))
      = ∫ x in Submission.BoseGases.abox n ℓ,
          ((Work.BoseKinLoc.indU ℓ 0 (x j) * Work.BoseKinLoc.fsT ℓ d s eT b 0 (Work.BoseKinLoc.fibre n j Φ x)
              - (b / 4) * (Work.BoseKinLoc.indU ℓ 0 (x j) * Work.BoseKinLoc.gapWord ℓ 1 0 (Work.BoseKinLoc.fibre n j Φ x)))
            - ((b / 100) * eT) * (Work.BoseKinLoc.indU ℓ 0 (x j) * Work.BoseKinLoc.momWord ℓ d 1 1 0 (Work.BoseKinLoc.fibre n j Φ x))) := by
        exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = (∫ x in Submission.BoseGases.abox n ℓ,
          (Work.BoseKinLoc.indU ℓ 0 (x j) * Work.BoseKinLoc.fsT ℓ d s eT b 0 (Work.BoseKinLoc.fibre n j Φ x)
              - (b / 4) * (Work.BoseKinLoc.indU ℓ 0 (x j) * Work.BoseKinLoc.gapWord ℓ 1 0 (Work.BoseKinLoc.fibre n j Φ x))))
        - (∫ x in Submission.BoseGases.abox n ℓ,
            ((b / 100) * eT) * (Work.BoseKinLoc.indU ℓ 0 (x j) * Work.BoseKinLoc.momWord ℓ d 1 1 0 (Work.BoseKinLoc.fibre n j Φ x))) :=
        MeasureTheory.integral_sub (hI1.sub hI2) hI3
    _ = ((∫ x in Submission.BoseGases.abox n ℓ,
            Work.BoseKinLoc.indU ℓ 0 (x j) * Work.BoseKinLoc.fsT ℓ d s eT b 0 (Work.BoseKinLoc.fibre n j Φ x))
          - (∫ x in Submission.BoseGases.abox n ℓ,
              (b / 4) * (Work.BoseKinLoc.indU ℓ 0 (x j) * Work.BoseKinLoc.gapWord ℓ 1 0 (Work.BoseKinLoc.fibre n j Φ x))))
        - (∫ x in Submission.BoseGases.abox n ℓ,
            ((b / 100) * eT) * (Work.BoseKinLoc.indU ℓ 0 (x j) * Work.BoseKinLoc.momWord ℓ d 1 1 0 (Work.BoseKinLoc.fibre n j Φ x))) := by
        rw [MeasureTheory.integral_sub hI1 hI2]
    _ = (∫ x in Submission.BoseGases.abox n ℓ,
            Work.BoseKinLoc.indU ℓ 0 (x j) * Work.BoseKinLoc.fsT ℓ d s eT b 0 (Work.BoseKinLoc.fibre n j Φ x))
        - b / 4 * (∫ x in Submission.BoseGases.abox n ℓ,
            Work.BoseKinLoc.indU ℓ 0 (x j) * Work.BoseKinLoc.gapWord ℓ 1 0 (Work.BoseKinLoc.fibre n j Φ x))
        - b / 100 * eT * (∫ x in Submission.BoseGases.abox n ℓ,
            Work.BoseKinLoc.indU ℓ 0 (x j) * Work.BoseKinLoc.momWord ℓ d 1 1 0 (Work.BoseKinLoc.fibre n j Φ x)) := by
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]

theorem kinGroupRhs_slotSum_eq {n : ℕ} {ℓ s d eT b : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    (∑ j : Fin n, (ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseKinLoc.indU ℓ 0 (x j) *
          (Work.BoseKinLoc.fsT ℓ d s eT b 0 (Work.BoseKinLoc.fibre n j Φ x)
            - b / 4 * ((ℓ ^ 2)⁻¹ * Work.BoseKinLoc.gapBare ℓ 0 (Work.BoseKinLoc.fibre n j Φ x))
            - b / 100 * (eT * (d * ℓ) ^ (-2 : ℤ) *
                Work.BoseKinLoc.momForm ℓ d 0 (Work.BoseKinLoc.fibre n j Φ x))))
      = Work.BoseKinLoc.kinFormB n ℓ d s eT b Φ
        - b / 4 * (ℓ ^ (-2 : ℤ) * Submission.BoseGases.cnPlus ℓ Φ)
        - b / 100 * (eT * (d * ℓ) ^ (-2 : ℤ) * Work.BoseBoxFix.nPlusHB ℓ d Φ) := by
  -- the two power conversions and the volume cancellation `ℓ⁻³ℓ³ = 1`
  have h3 : (ℓ ^ 3)⁻¹ = ℓ ^ (-3 : ℤ) := by
    rw [show (-3 : ℤ) = -(3 : ℤ) by norm_num, zpow_neg, zpow_ofNat]
  have h3' : ℓ ^ (-3 : ℤ) * ℓ ^ 3 = 1 := by
    rw [← zpow_natCast ℓ 3, ← zpow_add₀ (ne_of_gt hℓ)]
    norm_num
  -- ## the kinetic row: `kinFormB` is the slot sum by definition
  have hFrow : (∑ j : Fin n, (ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseKinLoc.indU ℓ 0 (x j) * Work.BoseKinLoc.fsT ℓ d s eT b 0 (Work.BoseKinLoc.fibre n j Φ x))
      = Work.BoseKinLoc.kinFormB n ℓ d s eT b Φ := by
    rw [← Finset.mul_sum, h3]
    simp only [Work.BoseKinLoc.kinFormB]
  -- ## the gap row (`gapRowSum` at `b = 1`)
  have hGrow : (∑ j : Fin n, (ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseKinLoc.indU ℓ 0 (x j) * Work.BoseKinLoc.gapWord ℓ 1 0 (Work.BoseKinLoc.fibre n j Φ x))
      = ℓ ^ (-2 : ℤ) * Submission.BoseGases.cnPlus ℓ Φ := by
    rw [← Finset.mul_sum, gapRowSum (ℓ := ℓ) (b := 1) hℓ hΦ, h3]
    rw [show ℓ ^ (-3 : ℤ) * (1 * ℓ ^ (-2 : ℤ) * (ℓ ^ 3 * Submission.BoseGases.cnPlus ℓ Φ))
        = (ℓ ^ (-3 : ℤ) * ℓ ^ 3) * (ℓ ^ (-2 : ℤ) * Submission.BoseGases.cnPlus ℓ Φ) by ring,
      h3', one_mul]
  -- ## the momentum row (`momRowSum` at `ε_T = b = 1`)
  have hHrow : (∑ j : Fin n, (ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseKinLoc.indU ℓ 0 (x j) * Work.BoseKinLoc.momWord ℓ d 1 1 0 (Work.BoseKinLoc.fibre n j Φ x))
      = (d * ℓ) ^ (-2 : ℤ) * Work.BoseBoxFix.nPlusHB ℓ d Φ := by
    rw [← Finset.mul_sum, momRowSum (ℓ := ℓ) (d := d) (eT := 1) (b := 1) hℓ, h3]
    rw [show ℓ ^ (-3 : ℤ) * (1 * 1 * (d * ℓ) ^ (-2 : ℤ) * (ℓ ^ 3 * Work.BoseBoxFix.nPlusHB ℓ d Φ))
        = (ℓ ^ (-3 : ℤ) * ℓ ^ 3) * ((d * ℓ) ^ (-2 : ℤ) * Work.BoseBoxFix.nPlusHB ℓ d Φ) by ring,
      h3', one_mul]
  -- ## per slot, the box integral of the difference is the difference of the box integrals
  have hsum : (∑ j : Fin n, (ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseKinLoc.indU ℓ 0 (x j) *
          (Work.BoseKinLoc.fsT ℓ d s eT b 0 (Work.BoseKinLoc.fibre n j Φ x)
            - b / 4 * ((ℓ ^ 2)⁻¹ * Work.BoseKinLoc.gapBare ℓ 0 (Work.BoseKinLoc.fibre n j Φ x))
            - b / 100 * (eT * (d * ℓ) ^ (-2 : ℤ) *
                Work.BoseKinLoc.momForm ℓ d 0 (Work.BoseKinLoc.fibre n j Φ x))))
      = ∑ j : Fin n, ((ℓ ^ 3)⁻¹ * (∫ x in Submission.BoseGases.abox n ℓ,
                Work.BoseKinLoc.indU ℓ 0 (x j) * Work.BoseKinLoc.fsT ℓ d s eT b 0 (Work.BoseKinLoc.fibre n j Φ x))
            - b / 4 * ((ℓ ^ 3)⁻¹ * (∫ x in Submission.BoseGases.abox n ℓ,
                Work.BoseKinLoc.indU ℓ 0 (x j) * Work.BoseKinLoc.gapWord ℓ 1 0 (Work.BoseKinLoc.fibre n j Φ x)))
            - b / 100 * eT * ((ℓ ^ 3)⁻¹ * (∫ x in Submission.BoseGases.abox n ℓ,
                Work.BoseKinLoc.indU ℓ 0 (x j) * Work.BoseKinLoc.momWord ℓ d 1 1 0 (Work.BoseKinLoc.fibre n j Φ x)))) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [slot_integral_split (ℓ := ℓ) (s := s) (d := d) (eT := eT) (b := b) hℓ hΦ j]
    ring
  -- ## assembly: distribute the sums and apply the three row identities
  rw [hsum, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  rw [(Finset.mul_sum Finset.univ (fun j : Fin n => (ℓ ^ 3)⁻¹ *
          (∫ x in Submission.BoseGases.abox n ℓ,
            Work.BoseKinLoc.indU ℓ 0 (x j) * Work.BoseKinLoc.gapWord ℓ 1 0 (Work.BoseKinLoc.fibre n j Φ x)))
        (b / 4)).symm,
      (Finset.mul_sum Finset.univ (fun j : Fin n => (ℓ ^ 3)⁻¹ *
          (∫ x in Submission.BoseGases.abox n ℓ,
            Work.BoseKinLoc.indU ℓ 0 (x j) * Work.BoseKinLoc.momWord ℓ d 1 1 0 (Work.BoseKinLoc.fibre n j Φ x)))
        ((b / 100) * eT)).symm]
  rw [hFrow, hGrow, hHrow]
  ring

end Work.BoseBoxFock
