import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Kinetic.kinetic_localisation_of_thresholds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixKin.Kinetic

noncomputable section

open MeasureTheory
open scoped ContDiff Topology Real BigOperators ENNReal

set_option maxHeartbeats 3200000

/-- **The momentum-space bookkeeping with the `K`-coefficient** (the public, `K`-form of the
private helper `budget_le_dSpace` of `BoseKinLoc.Kinetic.kinetic_localisation_of_thresholds`,
as used by `Work.BoseFixKin.Kinetic.kinetic_localisation_core`).

Given the pointwise momentum budget
`(1+K)/2 ε_T(dℓ)⁻² raSym + bβ⁻¹(p²/(ℓ²p²+β)) + ((1−ε_T)tpr(2s) + ε_T tpr(2ds)) ≤ p²`
and the `p`-integrability of the two `tprSym`-weighted densities, the combination
`½ε_T(dℓ)⁻² raFrac + bℓ⁻² gapFrac + (K/2)ε_T(dℓ)⁻² raFrac + ((1−ε_T)A₁ + ε_T A₂)`
is dominated by `dSpace ψ`.

The only change with respect to the private `budget_le_dSpace` is that the two `raFrac`
summands are `(1/2)` and `(K/2)` (summing to `(1+K)/2`, which is the coefficient carried by the
hypothesis `hbud`), so the auxiliary symbol `Bd` below carries the coefficient `(1+K)/2`. -/
lemma budget_le_dSpace_K {β C K ℓ d s εT b : ℝ} (hβ : 0 < β) (hC : 0 < C) (hK : 0 ≤ K)
    (hℓ : 0 < ℓ) (hd : 0 < d) (hs : 0 < s) (hεT : 0 ≤ εT) (hεT1 : εT ≤ 1) (hb : 0 ≤ b)
    {ψ : EuclideanSpace ℝ (Fin 3) → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    (hcs : HasCompactSupport ψ)
    (hbud : ∀ p : EuclideanSpace ℝ (Fin 3),
      (1 + K) / 2 * εT * (d * ℓ) ^ (-2 : ℤ) * Work.BoseKinLoc.raSym ℓ d p
      + b * β⁻¹ * (‖p‖ ^ 2 / (ℓ ^ 2 * ‖p‖ ^ 2 + β))
      + ((1 - εT) * Work.BoseKinLoc.tprSym ℓ (2 * s) C p
          + εT * Work.BoseKinLoc.tprSym ℓ (2 * (d * s)) C p) ≤ ‖p‖ ^ 2)
    (hT1 : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseKinLoc.tprSym ℓ (2 * s) C p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2))
    (hT2 : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseKinLoc.tprSym ℓ (2 * (d * s)) C p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2)) :
    (1 / 2) * (εT * (d * ℓ) ^ (-2 : ℤ)) * Work.BoseKinLoc.raFrac ℓ d ψ
      + b * ℓ ^ (-2 : ℤ) * Work.BoseKinLoc.gapFrac ℓ β ψ
      + (K / 2) * (εT * (d * ℓ) ^ (-2 : ℤ)) * Work.BoseKinLoc.raFrac ℓ d ψ
      + ((1 - εT) * (((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
            Work.BoseKinLoc.tprSym ℓ (2 * s) C p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2)
          + εT * (((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
            Work.BoseKinLoc.tprSym ℓ (2 * (d * s)) C p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2))
      ≤ Work.BSKinetic.dSpace ψ := by
  have hf2 : Integrable (fun p : EuclideanSpace ℝ (Fin 3) => ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2) :=
    Work.BSKinetic.integrable_kinFT_sq ψ hψ hcs
  have hIE : Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      ‖p‖ ^ 2 * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2) :=
    Work.SmallBoxTBWord.integrable_kinFT_energy_cspt ψ hψ hcs
  have hra_cont : Continuous (fun p : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseKinLoc.raSym ℓ d p) := by
    unfold Work.BoseKinLoc.raSym
    exact Continuous.div (by fun_prop) (by fun_prop) (fun p => by positivity)
  have hga_cont : Continuous (fun p : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseKinLoc.gapSym ℓ β p) := by
    unfold Work.BoseKinLoc.gapSym
    exact continuous_const.mul (Continuous.div (by fun_prop) (by fun_prop) (fun p => by positivity))
  have hra_le : ∀ p : EuclideanSpace ℝ (Fin 3), ‖Work.BoseKinLoc.raSym ℓ d p‖ ≤ 1 := by
    intro p
    have hden : (0:ℝ) < ‖p‖ ^ 2 + (d * ℓ) ^ (-2 : ℤ) := by positivity
    have hpos : 0 ≤ Work.BoseKinLoc.raSym ℓ d p := by unfold Work.BoseKinLoc.raSym; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hpos, Work.BoseKinLoc.raSym, div_le_one hden]
    linarith [sq_nonneg ‖p‖, show (0:ℝ) ≤ (d * ℓ) ^ (-2 : ℤ) from by positivity]
  have hga_le : ∀ p : EuclideanSpace ℝ (Fin 3), ‖Work.BoseKinLoc.gapSym ℓ β p‖ ≤ β⁻¹ := by
    intro p
    have hden : (0:ℝ) < ℓ ^ 2 * ‖p‖ ^ 2 + β := by positivity
    have hpos : 0 ≤ Work.BoseKinLoc.gapSym ℓ β p := by unfold Work.BoseKinLoc.gapSym; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hpos, Work.BoseKinLoc.gapSym]
    have hle : (ℓ ^ 2 * ‖p‖ ^ 2) / (ℓ ^ 2 * ‖p‖ ^ 2 + β) ≤ 1 := by
      rw [div_le_one hden]; linarith [sq_nonneg ‖p‖, sq_nonneg ℓ]
    calc β⁻¹ * ((ℓ ^ 2 * ‖p‖ ^ 2) / (ℓ ^ 2 * ‖p‖ ^ 2 + β))
        ≤ β⁻¹ * 1 := mul_le_mul_of_nonneg_left hle (by positivity)
      _ = β⁻¹ := mul_one _
  have hIra : Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseKinLoc.raSym ℓ d p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2) :=
    hf2.bdd_mul hra_cont.aestronglyMeasurable (ae_of_all _ hra_le)
  have hIgap : Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseKinLoc.gapSym ℓ β p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2) :=
    hf2.bdd_mul hga_cont.aestronglyMeasurable (ae_of_all _ hga_le)
  set Bd : EuclideanSpace ℝ (Fin 3) → ℝ := fun p =>
      (1 + K) / 2 * εT * (d * ℓ) ^ (-2 : ℤ) * Work.BoseKinLoc.raSym ℓ d p
      + b * ℓ ^ (-2 : ℤ) * Work.BoseKinLoc.gapSym ℓ β p
      + ((1 - εT) * Work.BoseKinLoc.tprSym ℓ (2 * s) C p
          + εT * Work.BoseKinLoc.tprSym ℓ (2 * (d * s)) C p) with hBd_def
  have hptgap : ∀ p : EuclideanSpace ℝ (Fin 3), b * ℓ ^ (-2 : ℤ) * Work.BoseKinLoc.gapSym ℓ β p
      = b * β⁻¹ * (‖p‖ ^ 2 / (ℓ ^ 2 * ‖p‖ ^ 2 + β)) := by
    intro p
    rw [Work.BoseKinLoc.gapSym]
    field_simp
  have hbud' : ∀ p : EuclideanSpace ℝ (Fin 3), Bd p ≤ ‖p‖ ^ 2 := by
    intro p
    rw [hBd_def]
    beta_reduce
    rw [hptgap p]
    exact hbud p
  have hBdnn : ∀ p : EuclideanSpace ℝ (Fin 3), 0 ≤ Bd p := by
    intro p
    rw [hBd_def]
    have hK2 : (0:ℝ) ≤ (1 + K) / 2 := by linarith
    have h1 : 0 ≤ Work.BoseKinLoc.raSym ℓ d p := by unfold Work.BoseKinLoc.raSym; positivity
    have h2 : 0 ≤ Work.BoseKinLoc.gapSym ℓ β p := by unfold Work.BoseKinLoc.gapSym; positivity
    have ht1 : 0 ≤ Work.BoseKinLoc.tprSym ℓ (2 * s) C p := by
      rw [Work.BoseKinLoc.tprSym]; split
      · exact Submission.BoseGases.fsKinCoeff_nonneg _ _
      · positivity
    have ht2 : 0 ≤ Work.BoseKinLoc.tprSym ℓ (2 * (d * s)) C p := by
      rw [Work.BoseKinLoc.tprSym]; split
      · exact Submission.BoseGases.fsKinCoeff_nonneg _ _
      · positivity
    have h3 : 0 ≤ (1 - εT) * Work.BoseKinLoc.tprSym ℓ (2 * s) C p := mul_nonneg (by linarith) ht1
    have h4 : 0 ≤ εT * Work.BoseKinLoc.tprSym ℓ (2 * (d * s)) C p := mul_nonneg hεT ht2
    have h5 : 0 ≤ (1 + K) / 2 * εT * (d * ℓ) ^ (-2 : ℤ) * Work.BoseKinLoc.raSym ℓ d p := by
      have h : (0:ℝ) ≤ (d * ℓ) ^ (-2 : ℤ) := by positivity
      exact mul_nonneg (mul_nonneg (mul_nonneg hK2 hεT) h) h1
    have h6 : 0 ≤ b * ℓ ^ (-2 : ℤ) * Work.BoseKinLoc.gapSym ℓ β p := by
      have : (0:ℝ) ≤ ℓ ^ (-2 : ℤ) := by positivity
      positivity
    linarith
  have hLE : (∫ p : EuclideanSpace ℝ (Fin 3), Bd p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2)
      ≤ ∫ p : EuclideanSpace ℝ (Fin 3), ‖p‖ ^ 2 * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2 :=
    integral_mono_of_nonneg (ae_of_all _ (fun p => mul_nonneg (hBdnn p) (sq_nonneg _))) hIE
      (ae_of_all _ (fun p => mul_le_mul_of_nonneg_right (hbud' p) (sq_nonneg _)))
  have hExp : (∫ p : EuclideanSpace ℝ (Fin 3), Bd p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2)
      = (1 + K) / 2 * εT * (d * ℓ) ^ (-2 : ℤ) * (∫ p : EuclideanSpace ℝ (Fin 3),
            Work.BoseKinLoc.raSym ℓ d p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2)
        + b * ℓ ^ (-2 : ℤ) * (∫ p : EuclideanSpace ℝ (Fin 3),
            Work.BoseKinLoc.gapSym ℓ β p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2)
        + ((1 - εT) * (∫ p : EuclideanSpace ℝ (Fin 3),
              Work.BoseKinLoc.tprSym ℓ (2 * s) C p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2)
            + εT * (∫ p : EuclideanSpace ℝ (Fin 3),
              Work.BoseKinLoc.tprSym ℓ (2 * (d * s)) C p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2)) := by
    have h1 : Integrable (fun p : EuclideanSpace ℝ (Fin 3) => (1 + K) / 2 * εT *
        (d * ℓ) ^ (-2 : ℤ) *
        (Work.BoseKinLoc.raSym ℓ d p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2)) := hIra.const_mul _
    have h2 : Integrable (fun p : EuclideanSpace ℝ (Fin 3) => b * ℓ ^ (-2 : ℤ) *
        (Work.BoseKinLoc.gapSym ℓ β p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2)) := hIgap.const_mul _
    have h3 : Integrable (fun p : EuclideanSpace ℝ (Fin 3) => (1 - εT) *
        (Work.BoseKinLoc.tprSym ℓ (2 * s) C p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2)) :=
      hT1.const_mul _
    have h4 : Integrable (fun p : EuclideanSpace ℝ (Fin 3) => εT *
        (Work.BoseKinLoc.tprSym ℓ (2 * (d * s)) C p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2)) :=
      hT2.const_mul _
    have h12 : Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
        (1 + K) / 2 * εT * (d * ℓ) ^ (-2 : ℤ) *
          (Work.BoseKinLoc.raSym ℓ d p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2)
        + b * ℓ ^ (-2 : ℤ) * (Work.BoseKinLoc.gapSym ℓ β p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2)) :=
      (h1.add h2).congr (ae_of_all _ (fun p => rfl))
    have h34 : Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
        (1 - εT) * (Work.BoseKinLoc.tprSym ℓ (2 * s) C p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2)
        + εT * (Work.BoseKinLoc.tprSym ℓ (2 * (d * s)) C p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2)) :=
      (h3.add h4).congr (ae_of_all _ (fun p => rfl))
    rw [show (∫ p : EuclideanSpace ℝ (Fin 3), Bd p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2)
        = ∫ p : EuclideanSpace ℝ (Fin 3), ((1 + K) / 2 * εT * (d * ℓ) ^ (-2 : ℤ) *
              (Work.BoseKinLoc.raSym ℓ d p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2)
            + b * ℓ ^ (-2 : ℤ) *
              (Work.BoseKinLoc.gapSym ℓ β p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2)
            + ((1 - εT) * (Work.BoseKinLoc.tprSym ℓ (2 * s) C p
                  * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2)
              + εT * (Work.BoseKinLoc.tprSym ℓ (2 * (d * s)) C p
                  * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2))) from by
      refine integral_congr_ae (ae_of_all _ (fun p => ?_))
      rw [hBd_def]; ring]
    rw [integral_add h12 h34, integral_add h1 h2, integral_add h3 h4,
      integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]
  have hStep1 : (1 / 2) * (εT * (d * ℓ) ^ (-2 : ℤ)) * Work.BoseKinLoc.raFrac ℓ d ψ
        + b * ℓ ^ (-2 : ℤ) * Work.BoseKinLoc.gapFrac ℓ β ψ
        + (K / 2) * (εT * (d * ℓ) ^ (-2 : ℤ)) * Work.BoseKinLoc.raFrac ℓ d ψ
        + ((1 - εT) * (((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
              Work.BoseKinLoc.tprSym ℓ (2 * s) C p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2)
            + εT * (((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
              Work.BoseKinLoc.tprSym ℓ (2 * (d * s)) C p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2))
      = ((2 * Real.pi) ^ 3)⁻¹ * ((1 + K) / 2 * εT * (d * ℓ) ^ (-2 : ℤ) *
              (∫ p : EuclideanSpace ℝ (Fin 3),
                Work.BoseKinLoc.raSym ℓ d p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2)
          + b * ℓ ^ (-2 : ℤ) * (∫ p : EuclideanSpace ℝ (Fin 3),
              Work.BoseKinLoc.gapSym ℓ β p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2)
          + ((1 - εT) * (∫ p : EuclideanSpace ℝ (Fin 3),
                Work.BoseKinLoc.tprSym ℓ (2 * s) C p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2)
              + εT * (∫ p : EuclideanSpace ℝ (Fin 3),
                Work.BoseKinLoc.tprSym ℓ (2 * (d * s)) C p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2))) := by
    rw [Work.BoseKinLoc.raFrac, Work.BoseKinLoc.gapFrac]
    ring
  calc (1 / 2) * (εT * (d * ℓ) ^ (-2 : ℤ)) * Work.BoseKinLoc.raFrac ℓ d ψ
        + b * ℓ ^ (-2 : ℤ) * Work.BoseKinLoc.gapFrac ℓ β ψ
        + (K / 2) * (εT * (d * ℓ) ^ (-2 : ℤ)) * Work.BoseKinLoc.raFrac ℓ d ψ
        + ((1 - εT) * (((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
              Work.BoseKinLoc.tprSym ℓ (2 * s) C p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2)
            + εT * (((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
              Work.BoseKinLoc.tprSym ℓ (2 * (d * s)) C p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2))
      = ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : EuclideanSpace ℝ (Fin 3),
          Bd p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2) := by
        rw [hStep1, hExp]
    _ ≤ ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : EuclideanSpace ℝ (Fin 3),
          ‖p‖ ^ 2 * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hLE (by positivity)
    _ = Work.BSKinetic.dSpace ψ := (Work.OneBodyKin.dSpace_eq_fourier ψ hψ hcs).symm

end
end Work.BoseFixKin.Kinetic
