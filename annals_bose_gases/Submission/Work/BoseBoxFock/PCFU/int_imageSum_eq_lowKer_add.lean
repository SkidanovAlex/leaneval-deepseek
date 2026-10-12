import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PCFU.latTailAux
import Submission.Work.BoseBoxFock.PCFU.lowKer_imageSum_bound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.int_imageSum_eq_lowKer_add`

The image sum `u ↦ Σ'_{d : ℤ³} Κ(u - x j + ℓ • latVec d)` of the position-space kernel
`Κ = lowKer fc κ` of FS's low-momentum multiplier (`PCFU/dictBricks.lean`) splits off its `d = 0`
term, which is the same kernel with the *reversed* argument (`Κ` is even, `lowKer_neg`):

    Σ'_d Κ(u - x_j + ℓ•latVec d)
      = Κ(x_j - u) + Σ'_d (if d = 0 then 0 else Κ(u - x_j + ℓ•latVec d)) .

Integrating against a bounded measurable test function `ψ(x[j ↦ ·])` and using the additivity of
the Bochner integral gives the target identity.  The only analytic input is that the image sum is
bounded on the box `acube ℓ` (the kernel decays faster than any polynomial, `lowKer_decay`, so its
periodisation along the lattice is bounded on bounded sets); everything else is bookkeeping.

The bound is isolated as the hypothesis `hC` of `int_imageSum_eq_lowKer_add_of_bound`; the
reference lemma is `Work.BoseBoxFock.PCFU.lowKer_imageSum_bound`.
-/

noncomputable section

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

namespace Work.BoseBoxFock.PCFU

/-- `‖↑r‖ = |r|` for a real `r` seen in `ℂ`. -/
private lemma complexNorm_ofReal_iis (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| := by
  rw [Complex.norm_def, Complex.normSq_ofReal, ← sq, Real.sqrt_sq_eq_abs]

/-- `latVec 0 = 0`. -/
private lemma latVec_zero_iis : Work.BoseBoxFock.latVec (0 : Fin 3 → ℤ) = (0 : E3) := by
  ext i
  simp [Work.BoseBoxFock.latVec]

/-- **Summability of the image sum.**  The kernel decays faster than any polynomial
(`lowKer_decay`), so its translates along the lattice `ℓℤ³` are summable in `ℤ³`
(`Work.BoseBoxFock.summable_shift_latVec`). -/
private lemma summable_image_c (fc : Work.BoseBoxFix.LowCut) {κ ℓ : ℝ} (hκ : 0 < κ)
    (hℓ : 0 < ℓ) (z : E3) :
    Summable (fun d : Fin 3 → ℤ =>
      ((lowKer fc κ (z + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ)) := by
  obtain ⟨C, hC0, hC⟩ := lowKer_decay fc hκ 2
  have h4 : ∀ q : E3, (0 : ℝ) < (1 + ‖q‖) ^ 4 := fun q => by positivity
  refine Work.BoseBoxFock.summable_shift_latVec (Φ := fun q : E3 => ((lowKer fc κ q : ℝ) : ℂ))
    (C := C) hC0 (fun q => ?_) hℓ z
  rw [complexNorm_ofReal_iis, ← Real.norm_eq_abs]
  calc ‖lowKer fc κ q‖
      = ((1 + ‖q‖) ^ 4)⁻¹ * ((1 + ‖q‖) ^ 4 * ‖lowKer fc κ q‖) := by
        rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt (h4 q)), one_mul]
    _ ≤ ((1 + ‖q‖) ^ 4)⁻¹ * C := mul_le_mul_of_nonneg_left (hC q) (inv_nonneg.mpr (h4 q).le)
    _ = C * (1 + ‖q‖) ^ (-((4 : ℕ) : ℤ)) := by rw [zpow_neg, zpow_natCast]; ring

/-- **The image sum splits off its `d = 0` term**, which is the kernel with the reversed argument
(`lowKer_neg`). -/
private lemma imageSum_split (fc : Work.BoseBoxFix.LowCut) {κ ℓ : ℝ} (hκ : 0 < κ) (hℓ : 0 < ℓ)
    {n : ℕ} (j : Fin n) (x : Submission.BoseGases.X n) (u : E3) :
    (∑' d : Fin 3 → ℤ, ((lowKer fc κ (u - x j + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
      = ((lowKer fc κ (x j - u) : ℝ) : ℂ)
        + ∑' d : Fin 3 → ℤ, if d = 0 then (0 : ℂ)
            else ((lowKer fc κ (u - x j + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ) := by
  have hsumm := summable_image_c fc hκ hℓ (u - x j)
  rw [hsumm.tsum_eq_add_tsum_ite (0 : Fin 3 → ℤ)]
  congr 1
  rw [latVec_zero_iis, smul_zero, add_zero, show u - x j = -(x j - u) by abel, lowKer_neg]

/-- The non-`d = 0` part of the image sum is bounded on the box, given the bound `hC` on the
norm-image sum. -/
private lemma imageSum_offZero_bound (fc : Work.BoseBoxFix.LowCut) {κ ℓ : ℝ} (hκ : 0 < κ)
    (hℓ : 0 < ℓ) {n : ℕ} (j : Fin n) (x : Submission.BoseGases.X n) {C : ℝ}
    (hC : ∀ u ∈ Submission.BoseGases.acube ℓ,
      ∑' d : Fin 3 → ℤ, ‖lowKer fc κ (u - x j + ℓ • Work.BoseBoxFock.latVec d)‖ ≤ C) :
    ∀ u ∈ Submission.BoseGases.acube ℓ,
      ‖(∑' d : Fin 3 → ℤ, if d = 0 then (0 : ℂ)
          else ((lowKer fc κ (u - x j + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))‖ ≤ C := by
  intro u hu
  have hsummC := summable_image_c fc hκ hℓ (u - x j)
  have hsummN : Summable (fun d : Fin 3 → ℤ =>
      ‖((lowKer fc κ (u - x j + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ)‖) := hsummC.norm
  have hsummI : Summable (fun d : Fin 3 → ℤ => ‖if d = 0 then (0 : ℂ)
      else ((lowKer fc κ (u - x j + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ)‖) :=
    Summable.of_nonneg_of_le (fun d => norm_nonneg _)
      (fun d => by by_cases hd : d = 0 <;> simp [hd]) hsummN
  refine le_trans (norm_tsum_le_tsum_norm hsummI) ?_
  refine le_trans (Summable.tsum_le_tsum (fun d => ?_) hsummI hsummN) ?_
  · by_cases hd : d = 0 <;> simp [hd]
  · have hnorm : (∑' d : Fin 3 → ℤ,
        ‖((lowKer fc κ (u - x j + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ)‖)
        = ∑' d : Fin 3 → ℤ, ‖lowKer fc κ (u - x j + ℓ • Work.BoseBoxFock.latVec d)‖ :=
      tsum_congr (fun d => by rw [complexNorm_ofReal_iis, Real.norm_eq_abs])
    rw [hnorm]
    exact hC u hu

/-- **The target identity, with the boundedness of the image sum on the box as an explicit
hypothesis.**  The reference instance of `hC` is `Work.BoseBoxFock.PCFU.lowKer_imageSum_bound`. -/
theorem int_imageSum_eq_lowKer_add_of_bound (fc : Work.BoseBoxFix.LowCut) {κ ℓ : ℝ} (hκ : 0 < κ)
    (hℓ : 0 < ℓ) {n : ℕ} (j : Fin n) (ψ : Submission.BoseGases.X n → ℝ)
    (hψm : Measurable ψ) (hψb : ∃ C : ℝ, ∀ y, ‖ψ y‖ ≤ C) (x : Submission.BoseGases.X n)
    (hC : ∃ C : ℝ, ∀ u ∈ Submission.BoseGases.acube ℓ,
      ∑' d : Fin 3 → ℤ, ‖Work.BoseBoxFock.PCFU.lowKer fc κ
        (u - x j + ℓ • Work.BoseBoxFock.latVec d)‖ ≤ C) :
    ∫ u in Submission.BoseGases.acube ℓ,
        (∑' d : Fin 3 → ℤ, ((Work.BoseBoxFock.PCFU.lowKer fc κ
            (u - x j + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
          * ((ψ (Function.update x j u) : ℝ) : ℂ)
      = (∫ u in Submission.BoseGases.acube ℓ,
            ((Work.BoseBoxFock.PCFU.lowKer fc κ (x j - u) : ℝ) : ℂ)
              * ((ψ (Function.update x j u) : ℝ) : ℂ))
        + ∫ u in Submission.BoseGases.acube ℓ,
            (∑' d : Fin 3 → ℤ, if d = 0 then (0 : ℂ)
                else ((Work.BoseBoxFock.PCFU.lowKer fc κ
                  (u - x j + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
              * ((ψ (Function.update x j u) : ℝ) : ℂ) := by
  obtain ⟨Cimg, hCimg⟩ := hC
  obtain ⟨Cψ, hCψ⟩ := hψb
  obtain ⟨-, Cnlk, hCnlk0, hCnlk⟩ := lowKer_regular fc hκ
  have hCψ0 : 0 ≤ Cψ := le_trans (norm_nonneg (ψ x)) (hCψ x)
  -- the test function in the slot `j`
  have hψum : Measurable (fun u : E3 => ((ψ (Function.update x j u) : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp
      (hψm.comp (by fun_prop : Measurable (fun u : E3 => Function.update x j u)))
  have hψub : ∀ u : E3, ‖((ψ (Function.update x j u) : ℝ) : ℂ)‖ ≤ Cψ := fun u => by
    rw [complexNorm_ofReal_iis, ← Real.norm_eq_abs]
    exact hCψ _
  -- integrability of the `d = 0` (reversed kernel) part
  have hKint : IntegrableOn (fun u : E3 => ((Work.BoseBoxFock.PCFU.lowKer fc κ (x j - u) : ℝ) : ℂ)
      * ((ψ (Function.update x j u) : ℝ) : ℂ)) (Submission.BoseGases.acube ℓ) volume := by
    refine IntegrableOn.of_bound (Submission.BoseGases.acube_lt_top ℓ hℓ.le)
      ((Complex.measurable_ofReal.comp ((lowKer_regular fc hκ).1.measurable.comp
        (by fun_prop : Measurable (fun u : E3 => x j - u)))).mul hψum).aestronglyMeasurable
      (Cnlk * Cψ) (Filter.Eventually.of_forall (fun u => ?_))
    rw [norm_mul, complexNorm_ofReal_iis, complexNorm_ofReal_iis]
    exact mul_le_mul (hCnlk (x j - u)) (by rw [← Real.norm_eq_abs]; exact hCψ _)
      (abs_nonneg _) hCnlk0
  -- integrability of the `d ≠ 0` part
  have hoff : ∀ u ∈ Submission.BoseGases.acube ℓ,
      ‖(∑' d : Fin 3 → ℤ, if d = 0 then (0 : ℂ)
          else ((Work.BoseBoxFock.PCFU.lowKer fc κ
            (u - x j + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))‖ ≤ Cimg :=
    imageSum_offZero_bound fc hκ hℓ j x hCimg
  have hTint : IntegrableOn (fun u : E3 => (∑' d : Fin 3 → ℤ, if d = 0 then (0 : ℂ)
      else ((Work.BoseBoxFock.PCFU.lowKer fc κ
        (u - x j + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
      * ((ψ (Function.update x j u) : ℝ) : ℂ)) (Submission.BoseGases.acube ℓ) volume := by
    have hTmeas : AEStronglyMeasurable (fun u : E3 => (∑' d : Fin 3 → ℤ, if d = 0 then (0 : ℂ)
        else ((Work.BoseBoxFock.PCFU.lowKer fc κ
          (u - x j + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ)))
        (volume.restrict (Submission.BoseGases.acube ℓ)) := by
      refine AEStronglyMeasurable.tsum (fun d => ?_)
      by_cases hd : d = 0
      · simp only [hd, ↓reduceIte]
        exact aestronglyMeasurable_const
      · simp only [hd, ↓reduceIte]
        exact (Complex.measurable_ofReal.comp ((lowKer_regular fc hκ).1.measurable.comp
          (by fun_prop : Measurable (fun u : E3 =>
            u - x j + ℓ • Work.BoseBoxFock.latVec d)))).aestronglyMeasurable
    refine IntegrableOn.of_bound (Submission.BoseGases.acube_lt_top ℓ hℓ.le)
      (hTmeas.mul hψum.aestronglyMeasurable) (Cimg * Cψ) ?_
    refine (MeasureTheory.ae_restrict_iff' (Submission.BoseGases.acube_measurable ℓ)).mpr
      (Filter.Eventually.of_forall (fun u hu => ?_))
    rw [norm_mul]
    exact mul_le_mul (hoff u hu) (hψub u) (norm_nonneg _)
      (le_trans (norm_nonneg _) (hoff u hu))
  -- the pointwise split, then additivity of the integral
  have hmain : (∫ u in Submission.BoseGases.acube ℓ,
        (∑' d : Fin 3 → ℤ, ((Work.BoseBoxFock.PCFU.lowKer fc κ
            (u - x j + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
          * ((ψ (Function.update x j u) : ℝ) : ℂ))
      = ∫ u in Submission.BoseGases.acube ℓ,
          ((((Work.BoseBoxFock.PCFU.lowKer fc κ (x j - u) : ℝ) : ℂ)
              * ((ψ (Function.update x j u) : ℝ) : ℂ))
            + ((∑' d : Fin 3 → ℤ, if d = 0 then (0 : ℂ)
                else ((Work.BoseBoxFock.PCFU.lowKer fc κ
                  (u - x j + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
              * ((ψ (Function.update x j u) : ℝ) : ℂ))) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
    dsimp only
    rw [imageSum_split fc hκ hℓ j x u]
    ring
  rw [hmain, integral_add hKint hTint]

theorem int_imageSum_eq_lowKer_add (fc : Work.BoseBoxFix.LowCut) {κ ℓ : ℝ} (hκ : 0 < κ)
    (hℓ : 0 < ℓ) {n : ℕ} (j : Fin n) (ψ : Submission.BoseGases.X n → ℝ)
    (hψm : Measurable ψ) (hψb : ∃ C : ℝ, ∀ y, ‖ψ y‖ ≤ C) (x : Submission.BoseGases.X n) :
    ∫ u in Submission.BoseGases.acube ℓ,
        (∑' d : Fin 3 → ℤ, ((Work.BoseBoxFock.PCFU.lowKer fc κ
            (u - x j + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
          * ((ψ (Function.update x j u) : ℝ) : ℂ)
      = (∫ u in Submission.BoseGases.acube ℓ,
            ((Work.BoseBoxFock.PCFU.lowKer fc κ (x j - u) : ℝ) : ℂ)
              * ((ψ (Function.update x j u) : ℝ) : ℂ))
        + ∫ u in Submission.BoseGases.acube ℓ,
            (∑' d : Fin 3 → ℤ, if d = 0 then (0 : ℂ)
                else ((Work.BoseBoxFock.PCFU.lowKer fc κ
                  (u - x j + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
              * ((ψ (Function.update x j u) : ℝ) : ℂ) := by
  obtain ⟨C, _hC0, hC⟩ := lowKer_imageSum_bound fc hκ hℓ j x
  exact int_imageSum_eq_lowKer_add_of_bound fc hκ hℓ j ψ hψm hψb x ⟨C, hC⟩

end Work.BoseBoxFock.PCFU
