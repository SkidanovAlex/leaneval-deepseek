import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixKin.Kinetic.budget_le_dSpace_K
import Submission.Work.BoseFixKin.Kinetic.fsT_split_all
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

/-- **The per-parameter core of FS `lem:LocKinEn` on the coupled regime** (node N3a of
`BOSE_BCLASH_LEAD.md`).

This is `Work.BoseKinLoc.Kinetic.kinetic_localisation_of_thresholds` with (a) the regime
bookkeeping replaced by its unpacked hypotheses, (b) the momentum bound `hmom` carrying the
explicit factor `(1/2) K` on `raFrac` (instead of `(1/2)`), and (c) the pointwise momentum budget
`hbud` carrying the coefficient `(1+K)/2` in its first term.  The proof is a *copy* of that
file's proof: copy the private helper `budget_le_dSpace` (its lines 81–249) under a public name,
with the two summands `(1/2)*(εT*(dℓ)⁻²)*raFrac` replaced by `(1/2)*(εT*(dℓ)⁻²)*raFrac` and
`(K/2)*(εT*(dℓ)⁻²)*raFrac` (which is exactly what `hbud`'s `(1+K)/2` coefficient consumes), then
copy the proof body from line 285 on, using `hmom` in place of the `mom_word_le` step and
`htpr (2*s) (Or.inl rfl)` / `htpr (2*(d*s)) (Or.inr rfl)` in place of the `σ ≤ s₀` bookkeeping. -/
theorem kinetic_localisation_core {β C K ℓ d s εT b : ℝ} (hβ : 0 < β)
    (hC : 0 < C) (hK : 0 ≤ K) (hℓ : 0 < ℓ) (hd : 0 < d) (hd1 : d ≤ 1) (hs : 0 < s)
    (hεT : 0 < εT) (hεT1 : εT ≤ 1) (hb : 0 < b)
    (hgap : Work.BoseKinLoc.GapBound β) (hneu : Work.BoseKinLoc.NeumannBound)
    (hmom : ∀ ψ : ℝ³ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      Integrable (fun u : ℝ³ => Work.BoseKinLoc.momForm ℓ d u ψ) →
        b * (∫ u : ℝ³, Work.BoseKinLoc.momForm ℓ d u ψ) ≤ (1 / 2) * K * Work.BoseKinLoc.raFrac ℓ d ψ)
    (htpr : ∀ σ : ℝ, (σ = 2 * s ∨ σ = 2 * (d * s)) → ∀ ψ : ℝ³ → ℝ, ContDiff ℝ ∞ ψ →
      HasCompactSupport ψ →
        Integrable (fun u : ℝ³ =>
          Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff ((σ * ℓ)⁻¹)) u ψ) →
          ∫ u : ℝ³, Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff ((σ * ℓ)⁻¹)) u ψ
            ≤ ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³,
                Work.BoseKinLoc.tprSym ℓ σ C p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2)
    (hbud : ∀ p : ℝ³,
      (1 + K) / 2 * εT * (d * ℓ) ^ (-2 : ℤ) * Work.BoseKinLoc.raSym ℓ d p
        + b * β⁻¹ * (‖p‖ ^ 2 / (ℓ ^ 2 * ‖p‖ ^ 2 + β))
        + ((1 - εT) * Work.BoseKinLoc.tprSym ℓ (2 * s) C p
            + εT * Work.BoseKinLoc.tprSym ℓ (2 * (d * s)) C p)
      ≤ ‖p‖ ^ 2) :
    ∀ ψ : ℝ³ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      Integrable (fun u : ℝ³ => Work.BoseKinLoc.fsT ℓ d s εT b u ψ) →
        ∫ u : ℝ³, Work.BoseKinLoc.fsT ℓ d s εT b u ψ ≤ Work.BSKinetic.dSpace ψ := by
  intro ψ hψ hcs hint
  -- integrability of the two `tprSym` weights
  have hT1 : Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseKinLoc.tprSym ℓ (2 * s) C p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2) :=
    Work.BoseKinLoc.Kinetic.tprSym_integrable hℓ (by linarith) hC hψ hcs
  have hT2 : Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseKinLoc.tprSym ℓ (2 * (d * s)) C p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2) :=
    Work.BoseKinLoc.Kinetic.tprSym_integrable hℓ (by positivity) hC hψ hcs
  -- the splitting of `∫ fsT` into the four words, together with their integrability
  obtain ⟨hAint, hGint, hMint, hPint, hsplit⟩ :=
    fsT_split_all hℓ hd hs hεT.le hεT1 hb.le hψ hcs hint
  -- the four termwise bounds
  have hA_bound : (∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.neuWord ℓ d εT u ψ)
      ≤ (1 / 2) * (εT * (d * ℓ) ^ (-2 : ℤ)) * Work.BoseKinLoc.raFrac ℓ d ψ := by
    have hdℓ : 0 < d * ℓ := mul_pos hd hℓ
    have ha2pos : 0 < (d * ℓ) ^ (-2 : ℤ) := zpow_pos hdℓ _
    have h1 : (∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.neuWord ℓ d εT u ψ)
        = ((1/2) * εT * (d * ℓ) ^ (-2 : ℤ)) * (∫ u : EuclideanSpace ℝ (Fin 3),
            Work.BoseKinLoc.neuFrac ℓ ((d * ℓ) ^ (-2 : ℤ)) u (Work.BoseKinLoc.Qfree ℓ u ψ)) := by
      rw [show (fun u : EuclideanSpace ℝ (Fin 3) => Work.BoseKinLoc.neuWord ℓ d εT u ψ)
          = fun u : EuclideanSpace ℝ (Fin 3) =>
              ((1/2) * εT * (d * ℓ) ^ (-2 : ℤ)) *
                Work.BoseKinLoc.neuFrac ℓ ((d * ℓ) ^ (-2 : ℤ)) u (Work.BoseKinLoc.Qfree ℓ u ψ)
          from rfl]
      exact integral_const_mul _ _
    have hψ2 : Integrable (fun z : EuclideanSpace ℝ (Fin 3) => (ψ z) ^ 2) :=
      Continuous.integrable_of_hasCompactSupport (hψ.continuous.pow 2)
        (hcs.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num))
    have hQ : ∀ u : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.neuFrac ℓ ((d * ℓ) ^ (-2 : ℤ)) u
        (Work.BoseKinLoc.Qfree ℓ u ψ) = Work.BoseKinLoc.neuFrac ℓ ((d * ℓ) ^ (-2 : ℤ)) u ψ := by
      intro u
      have hQfun : Work.BoseKinLoc.Qfree ℓ u ψ = fun z : EuclideanSpace ℝ (Fin 3) =>
          ψ z + (-(Work.BSKinetic.bsMean ℓ u ψ)) := by
        funext z; simp only [Work.BoseKinLoc.Qfree, Work.BSKinetic.bsQ]; ring
      rw [hQfun, Work.BoseKinLoc.NeuFrac.neuFrac_add_const_of_integrableSq (ℓ := ℓ)
        (a2 := (d * ℓ) ^ (-2 : ℤ)) ha2pos u ψ (-(Work.BSKinetic.bsMean ℓ u ψ))
        hψ.continuous.measurable hψ2]
    have hcne : ((1/2) * εT * (d * ℓ) ^ (-2 : ℤ)) ≠ 0 := by positivity
    have hIntQ : Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
        Work.BoseKinLoc.neuFrac ℓ ((d * ℓ) ^ (-2 : ℤ)) u (Work.BoseKinLoc.Qfree ℓ u ψ)) := by
      have h0 := hAint.const_mul (((1/2) * εT * (d * ℓ) ^ (-2 : ℤ))⁻¹)
      refine h0.congr (ae_of_all _ (fun u => ?_))
      show (((1/2) * εT * (d * ℓ) ^ (-2 : ℤ))⁻¹ * Work.BoseKinLoc.neuWord ℓ d εT u ψ)
        = Work.BoseKinLoc.neuFrac ℓ ((d * ℓ) ^ (-2 : ℤ)) u (Work.BoseKinLoc.Qfree ℓ u ψ)
      simp only [Work.BoseKinLoc.neuWord]
      rw [← mul_assoc, inv_mul_cancel₀ hcne, one_mul]
    have hIntψ : Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
        Work.BoseKinLoc.neuFrac ℓ ((d * ℓ) ^ (-2 : ℤ)) u ψ) :=
      hIntQ.congr (ae_of_all _ (fun u => hQ u))
    have h3 : (∫ u : EuclideanSpace ℝ (Fin 3),
        Work.BoseKinLoc.neuFrac ℓ ((d * ℓ) ^ (-2 : ℤ)) u ψ) ≤ Work.BoseKinLoc.raFrac ℓ d ψ :=
      hneu ψ hψ hcs ℓ d hℓ hd hIntψ
    have h2eq : (∫ u : EuclideanSpace ℝ (Fin 3),
          Work.BoseKinLoc.neuFrac ℓ ((d * ℓ) ^ (-2 : ℤ)) u (Work.BoseKinLoc.Qfree ℓ u ψ))
        = ∫ u : EuclideanSpace ℝ (Fin 3),
            Work.BoseKinLoc.neuFrac ℓ ((d * ℓ) ^ (-2 : ℤ)) u ψ :=
      integral_congr_ae (ae_of_all _ hQ)
    rw [h1, h2eq]
    have hc : ((1/2) * εT * (d * ℓ) ^ (-2 : ℤ)) = (1/2) * (εT * (d * ℓ) ^ (-2 : ℤ)) := by ring
    rw [hc]
    exact mul_le_mul_of_nonneg_left h3 (by positivity)
  have hG_bound : (∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.gapWord ℓ b u ψ)
      ≤ b * ℓ ^ (-2 : ℤ) * Work.BoseKinLoc.gapFrac ℓ β ψ := by
    have h1 : (∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.gapWord ℓ b u ψ)
        = (b * ℓ ^ (-2 : ℤ)) * (∫ u : EuclideanSpace ℝ (Fin 3),
            Work.BoseKinLoc.gapBare ℓ u ψ) := by
      rw [show (fun u : EuclideanSpace ℝ (Fin 3) => Work.BoseKinLoc.gapWord ℓ b u ψ)
          = fun u : EuclideanSpace ℝ (Fin 3) =>
              (b * ℓ ^ (-2 : ℤ)) * Work.BoseKinLoc.gapBare ℓ u ψ from rfl]
      exact integral_const_mul _ _
    have hbb : b * ℓ ^ (-2 : ℤ) ≠ 0 := by
      have h : (0:ℝ) < ℓ ^ (-2 : ℤ) := by positivity
      exact mul_ne_zero (ne_of_gt hb) (ne_of_gt h)
    have hIntBare : Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
        Work.BoseKinLoc.gapBare ℓ u ψ) := by
      have h0 := hGint.const_mul ((b * ℓ ^ (-2 : ℤ))⁻¹)
      refine h0.congr (ae_of_all _ (fun u => ?_))
      show (b * ℓ ^ (-2 : ℤ))⁻¹ * Work.BoseKinLoc.gapWord ℓ b u ψ
        = Work.BoseKinLoc.gapBare ℓ u ψ
      simp only [Work.BoseKinLoc.gapWord]
      rw [← mul_assoc, inv_mul_cancel₀ hbb, one_mul]
    have h2 := hgap ψ hψ hcs ℓ hℓ hIntBare
    rw [h1]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have hM_bound : (∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.momWord ℓ d εT b u ψ)
      ≤ (K / 2) * (εT * (d * ℓ) ^ (-2 : ℤ)) * Work.BoseKinLoc.raFrac ℓ d ψ := by
    have hco : b * εT * (d * ℓ) ^ (-2 : ℤ) ≠ 0 := by
      have h : (0:ℝ) < (d * ℓ) ^ (-2 : ℤ) := by positivity
      exact mul_ne_zero (mul_ne_zero (ne_of_gt hb) (ne_of_gt hεT)) (ne_of_gt h)
    have hIntForm : Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
        Work.BoseKinLoc.momForm ℓ d u ψ) := by
      have h0 := hMint.const_mul ((b * εT * (d * ℓ) ^ (-2 : ℤ))⁻¹)
      refine h0.congr (ae_of_all _ (fun u => ?_))
      show (b * εT * (d * ℓ) ^ (-2 : ℤ))⁻¹ * Work.BoseKinLoc.momWord ℓ d εT b u ψ
        = Work.BoseKinLoc.momForm ℓ d u ψ
      simp only [Work.BoseKinLoc.momWord]
      rw [← mul_assoc, inv_mul_cancel₀ hco, one_mul]
    have h2 : b * (∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.momForm ℓ d u ψ)
        ≤ (1 / 2) * K * Work.BoseKinLoc.raFrac ℓ d ψ := hmom ψ hψ hcs hIntForm
    have h1 : (∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.momWord ℓ d εT b u ψ)
        = (b * εT * (d * ℓ) ^ (-2 : ℤ)) * (∫ u : EuclideanSpace ℝ (Fin 3),
            Work.BoseKinLoc.momForm ℓ d u ψ) := by
      rw [show (fun u : EuclideanSpace ℝ (Fin 3) => Work.BoseKinLoc.momWord ℓ d εT b u ψ)
          = fun u : EuclideanSpace ℝ (Fin 3) =>
              (b * εT * (d * ℓ) ^ (-2 : ℤ)) * Work.BoseKinLoc.momForm ℓ d u ψ from rfl]
      exact integral_const_mul _ _
    rw [h1]
    have h3 : b * εT * (d * ℓ) ^ (-2 : ℤ) * (∫ u : EuclideanSpace ℝ (Fin 3),
          Work.BoseKinLoc.momForm ℓ d u ψ)
        = εT * (d * ℓ) ^ (-2 : ℤ) * (b * (∫ u : EuclideanSpace ℝ (Fin 3),
            Work.BoseKinLoc.momForm ℓ d u ψ)) := by ring
    rw [h3]
    have h4 := mul_le_mul_of_nonneg_left h2
      (show (0:ℝ) ≤ εT * (d * ℓ) ^ (-2 : ℤ) by positivity)
    have h5 : εT * (d * ℓ) ^ (-2 : ℤ) * ((1 / 2) * K * Work.BoseKinLoc.raFrac ℓ d ψ)
        = (K / 2) * (εT * (d * ℓ) ^ (-2 : ℤ)) * Work.BoseKinLoc.raFrac ℓ d ψ := by ring
    linarith [h4, h5]
  have hP_bound : (∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.mainWord ℓ d s εT u ψ)
      ≤ (1 - εT) * (((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
            Work.BoseKinLoc.tprSym ℓ (2 * s) C p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2)
          + εT * (((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
            Work.BoseKinLoc.tprSym ℓ (2 * (d * s)) C p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2) := by
    have hcoef1 : (2 * (s * ℓ))⁻¹ = ((2 * s) * ℓ)⁻¹ := by congr 1; ring
    have hcoef2 : (2 * (d * s * ℓ))⁻¹ = ((2 * (d * s)) * ℓ)⁻¹ := by congr 1; ring
    have hB0 : Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
        Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff 0) u ψ) :=
      Work.BSKinetic.integrable_bsOneBody_fsKinCoeff_zero (ne_of_gt hℓ) hψ hcs
    have hmono1 : ∀ u : EuclideanSpace ℝ (Fin 3), Work.BSKinetic.bsOneBody ℓ
        (Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹)) u ψ
        ≤ Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff 0) u ψ := by
      intro u
      exact Work.BSKinetic.bsOneBody_mono_coeff
        (fun r => Submission.BoseGases.fsKinCoeff_nonneg _ r)
        (fun r => Work.BSKinetic.fsKinCoeff_zero_le (by positivity) r)
        (Work.BSKinetic.integrable_bsKinWeight_zero u hψ hcs)
    have hB1int : Integrable (fun u : EuclideanSpace ℝ (Fin 3) => Work.BSKinetic.bsOneBody ℓ
        (Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹)) u ψ) :=
      hB0.mono' ((Work.BSKinetic.Decomp.continuous_bsOneBody hℓ _ ψ hψ hcs).aestronglyMeasurable)
        (ae_of_all _ (fun u => by
          rw [Real.norm_of_nonneg (Work.BSKinetic.bsOneBody_nonneg
            (fun r => Submission.BoseGases.fsKinCoeff_nonneg _ r) u ψ)]
          exact hmono1 u))
    have hmono2 : ∀ u : EuclideanSpace ℝ (Fin 3), Work.BSKinetic.bsOneBody ℓ
        (Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹)) u ψ
        ≤ Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff 0) u ψ := by
      intro u
      exact Work.BSKinetic.bsOneBody_mono_coeff
        (fun r => Submission.BoseGases.fsKinCoeff_nonneg _ r)
        (fun r => Work.BSKinetic.fsKinCoeff_zero_le (by positivity) r)
        (Work.BSKinetic.integrable_bsKinWeight_zero u hψ hcs)
    have hB2int : Integrable (fun u : EuclideanSpace ℝ (Fin 3) => Work.BSKinetic.bsOneBody ℓ
        (Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹)) u ψ) :=
      hB0.mono' ((Work.BSKinetic.Decomp.continuous_bsOneBody hℓ _ ψ hψ hcs).aestronglyMeasurable)
        (ae_of_all _ (fun u => by
          rw [Real.norm_of_nonneg (Work.BSKinetic.bsOneBody_nonneg
            (fun r => Submission.BoseGases.fsKinCoeff_nonneg _ r) u ψ)]
          exact hmono2 u))
    have hmainEq : (fun u : EuclideanSpace ℝ (Fin 3) => Work.BoseKinLoc.mainWord ℓ d s εT u ψ)
        = fun u : EuclideanSpace ℝ (Fin 3) =>
            (1 - εT) * Work.BSKinetic.bsOneBody ℓ
                (Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹)) u ψ
              + εT * Work.BSKinetic.bsOneBody ℓ
                (Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹)) u ψ := rfl
    have hs1 : Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
        (1 - εT) * Work.BSKinetic.bsOneBody ℓ
          (Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹)) u ψ) := hB1int.const_mul _
    have hs2 : Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
        εT * Work.BSKinetic.bsOneBody ℓ
          (Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹)) u ψ) := hB2int.const_mul _
    have hsplitmain : (∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.mainWord ℓ d s εT u ψ)
        = (1 - εT) * (∫ u : EuclideanSpace ℝ (Fin 3), Work.BSKinetic.bsOneBody ℓ
              (Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹)) u ψ)
          + εT * (∫ u : EuclideanSpace ℝ (Fin 3), Work.BSKinetic.bsOneBody ℓ
              (Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹)) u ψ) := by
      rw [hmainEq, integral_add hs1 hs2, integral_const_mul, integral_const_mul]
    have hB1'int : Integrable (fun u : EuclideanSpace ℝ (Fin 3) => Work.BSKinetic.bsOneBody ℓ
        (Submission.BoseGases.fsKinCoeff (((2 * s) * ℓ)⁻¹)) u ψ) :=
      hB1int.congr (ae_of_all _ (fun u => by rw [hcoef1]))
    have hB2'int : Integrable (fun u : EuclideanSpace ℝ (Fin 3) => Work.BSKinetic.bsOneBody ℓ
        (Submission.BoseGases.fsKinCoeff (((2 * (d * s)) * ℓ)⁻¹)) u ψ) :=
      hB2int.congr (ae_of_all _ (fun u => by rw [hcoef2]))
    have ht1 := htpr (2 * s) (Or.inl rfl) ψ hψ hcs hB1'int
    have ht2 := htpr (2 * (d * s)) (Or.inr rfl) ψ hψ hcs hB2'int
    have ht1' : (∫ u : EuclideanSpace ℝ (Fin 3), Work.BSKinetic.bsOneBody ℓ
          (Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹)) u ψ)
        ≤ ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
            Work.BoseKinLoc.tprSym ℓ (2 * s) C p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2 := by
      rw [← hcoef1] at ht1; exact ht1
    have ht2' : (∫ u : EuclideanSpace ℝ (Fin 3), Work.BSKinetic.bsOneBody ℓ
          (Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹)) u ψ)
        ≤ ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
            Work.BoseKinLoc.tprSym ℓ (2 * (d * s)) C p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2 := by
      rw [← hcoef2] at ht2; exact ht2
    rw [hsplitmain]
    exact add_le_add (mul_le_mul_of_nonneg_left ht1' (by linarith))
      (mul_le_mul_of_nonneg_left ht2' (by linarith))
  -- assemble
  have hsum : (∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.fsT ℓ d s εT b u ψ)
      ≤ (1 / 2) * (εT * (d * ℓ) ^ (-2 : ℤ)) * Work.BoseKinLoc.raFrac ℓ d ψ
        + b * ℓ ^ (-2 : ℤ) * Work.BoseKinLoc.gapFrac ℓ β ψ
        + (K / 2) * (εT * (d * ℓ) ^ (-2 : ℤ)) * Work.BoseKinLoc.raFrac ℓ d ψ
        + ((1 - εT) * (((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
              Work.BoseKinLoc.tprSym ℓ (2 * s) C p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2)
            + εT * (((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
              Work.BoseKinLoc.tprSym ℓ (2 * (d * s)) C p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2)) := by
    rw [hsplit]
    linarith [hA_bound, hG_bound, hM_bound, hP_bound]
  exact le_trans hsum (budget_le_dSpace_K hβ hC hK hℓ hd hs hεT.le hεT1 hb.le hψ hcs hbud hT1 hT2)

end

end Work.BoseFixKin.Kinetic
