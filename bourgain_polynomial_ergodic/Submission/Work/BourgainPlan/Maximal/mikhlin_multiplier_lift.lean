import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.rescaled_mikhlin_multiplier_lp
import Submission.Work.BourgainPlan.Thm52.CircleLiftDefs
import Submission.Work.Analysis.Fourier.band_projection_schwartz_lp
import Submission.Work.BourgainPlan.Maximal.mikhlinConvolutionLp
import Submission.Work.BourgainPlan.Maximal.integrable_fourierInv_of_contDiff_two_hasCompactSupport

namespace Work.BourgainPlan.Maximal

open MeasureTheory
open scoped ENNReal FourierTransform

noncomputable section

set_option maxHeartbeats 2000000

/-- The fundamental-domain lift of a circle symbol vanishes off `Icc (-1/2) (1/2)`, hence has
compact support. -/
lemma hasCompactSupport_circleLift (ψ : Work.BourgainPlan.IonescuWainger.Circle → ℂ) :
    HasCompactSupport (Work.BourgainPlan.Thm52.circleLift ψ) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -(1 / 2 : ℝ)) (b := 1 / 2)) ?_
  intro x hx
  refine Work.BourgainPlan.Thm52.circleLift_of_notMem ?_
  intro hx'
  exact hx ⟨le_of_lt hx'.1, hx'.2⟩

/-- The inverse Fourier transform of the zero function is zero. -/
lemma fourierInv_fun_zero :
    FourierTransformInv.fourierInv (fun _ : ℝ => (0 : ℂ)) = fun _ : ℝ => 0 := by
  funext x
  rw [Real.fourierInv_eq']
  simp

/-- The convolution form of the multiplier identity, with the factors in the order in which the
Mikhlin bound (in convolution form) is stated. -/
lemma fourierInv_mul_eq_conv_swap {m f : ℝ → ℂ} (hm : MeasureTheory.Integrable m)
    (hf : MeasureTheory.Integrable f) (x : ℝ) :
    FourierTransformInv.fourierInv (fun ξ : ℝ => m ξ * FourierTransform.fourier f ξ) x
      = ∫ y : ℝ, FourierTransformInv.fourierInv m (x - y) * f y := by
  rw [Commons.Analysis.Fourier.fourierInv_mul_fourier_eq_convolution hm hf x]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun y => mul_comm _ _))

/-- **Mikhlin's multiplier bound in the shape consumed by Tao's `main`**: a circle symbol whose compactly supported lift `circleLift ψ` is `C²` and satisfies the Mikhlin bounds `‖ψ‖ ≤ A`, `|x|‖ψ'‖ ≤ A`, `|x|²‖ψ''‖ ≤ A` on `ℝ` gives an `L^q(ℝ, ℂ)`-bound at most `C A` for every `1 < q`, in the shape of the hypothesis of `hstep3_msw` (integrable inputs, the compactly supported lift). -/
theorem mikhlin_multiplier_lift (q : ℝ) (hq : 1 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ψ : Work.BourgainPlan.IonescuWainger.Circle → ℂ) (A : ℝ), 0 ≤ A →
      ContDiff ℝ 2 (Work.BourgainPlan.Thm52.circleLift ψ) →
      (∀ x : ℝ, ‖Work.BourgainPlan.Thm52.circleLift ψ x‖ ≤ A) →
      (∀ x : ℝ, |x| * ‖deriv (Work.BourgainPlan.Thm52.circleLift ψ) x‖ ≤ A) →
      (∀ x : ℝ, |x| ^ 2 * ‖iteratedDeriv 2 (Work.BourgainPlan.Thm52.circleLift ψ) x‖ ≤ A) →
      ∀ g : ℝ → ℂ, MeasureTheory.Integrable g →
        ∫⁻ x : ℝ, ‖FourierTransformInv.fourierInv
            (fun ξ : ℝ => Work.BourgainPlan.Thm52.circleLift ψ ξ
              * FourierTransform.fourier g ξ) x‖ₑ ^ q ∂MeasureTheory.volume
          ≤ ENNReal.ofReal ((C * A) ^ q) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ q ∂MeasureTheory.volume := by
  obtain ⟨C, hCpos, hC⟩ := mikhlinConvolutionLp q hq
  refine ⟨C, hCpos, ?_⟩
  intro ψ A hA hCD h0 h1 h2 g hg
  have hqpos : 0 < q := lt_trans zero_lt_one hq
  set m : ℝ → ℂ := Work.BourgainPlan.Thm52.circleLift ψ with hm
  have hsupp : HasCompactSupport m := by rw [hm]; exact hasCompactSupport_circleLift ψ
  have hmint : Integrable m := hCD.continuous.integrable_of_hasCompactSupport hsupp
  have hmIk : Integrable (FourierTransformInv.fourierInv m) :=
    integrable_fourierInv_of_contDiff_two_hasCompactSupport hCD hsupp
  rcases eq_or_lt_of_le hA with hA0 | hApos
  · -- `A = 0`: the symbol vanishes identically
    have hA0' : A = 0 := hA0.symm
    have hmzero : m = 0 := by
      funext x
      refine norm_le_zero_iff.mp ?_
      calc ‖m x‖ ≤ A := h0 x
        _ = 0 := hA0'
    have hL : (fun ξ : ℝ => m ξ * FourierTransform.fourier g ξ) = fun _ => (0 : ℂ) := by
      funext ξ; rw [hmzero]; simp
    rw [hA0', hL, fourierInv_fun_zero]
    simp [Real.zero_rpow (ne_of_gt hqpos), ENNReal.zero_rpow_of_pos hqpos]
  · by_cases hfin : ∫⁻ x : ℝ, ‖g x‖ₑ ^ q = ⊤
    · -- the right-hand side is infinite
      have hRHS : ENNReal.ofReal ((C * A) ^ q) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ q = ⊤ := by
        rw [hfin, ENNReal.mul_top]
        exact ENNReal.ofReal_ne_zero_iff.mpr (Real.rpow_pos_of_pos (mul_pos hCpos hApos) q)
      rw [hRHS]
      exact le_top
    · -- `g ∈ L^q`: apply the convolution form of Mikhlin's theorem
      have hmem : MemLp g (ENNReal.ofReal q) := by
        show eLpNorm g (ENNReal.ofReal q) < ⊤
        rw [lt_top_iff_ne_top]
        intro htop
        have h := Work.BourgainPlan.IonescuWainger.eLpNorm_rpow_eq_lintegral hqpos g hg.aestronglyMeasurable
        rw [htop] at h
        have htopq : (⊤ : ℝ≥0∞) ^ q = ⊤ := by
          rw [ENNReal.rpow_eq_top_iff]
          exact Or.inr ⟨rfl, hqpos⟩
        rw [htopq] at h
        exact hfin h.symm
      let F : ℝ → ℂ := fun x : ℝ => ∫ y : ℝ, FourierTransformInv.fourierInv m (x - y) * g y
      have hFm : AEStronglyMeasurable F volume := by
        have hJ : AEStronglyMeasurable
            (fun z : ℝ × ℝ => FourierTransformInv.fourierInv m (z.1 - z.2) * g z.2)
            ((volume : Measure ℝ).prod volume) :=
          (hmIk.aestronglyMeasurable.comp_quasiMeasurePreserving
            (quasiMeasurePreserving_sub_of_right_invariant volume volume)).mul
            hg.aestronglyMeasurable.comp_snd
        exact hJ.integral_prod_right'
      have hkey := hC m A hA hmint hCD h0 h1 h2 hmIk g hmem
      have hstep : ∫⁻ x : ℝ, ‖FourierTransformInv.fourierInv
              (fun ξ : ℝ => m ξ * FourierTransform.fourier g ξ) x‖ₑ ^ q
          = ∫⁻ x : ℝ, ‖F x‖ₑ ^ q := by
        refine lintegral_congr (fun x => ?_)
        rw [fourierInv_mul_eq_conv_swap hmint hg x]
      have hE : (MeasureTheory.eLpNorm F (ENNReal.ofReal q)
            (MeasureTheory.volume : MeasureTheory.Measure ℝ)) ^ q = ∫⁻ x : ℝ, ‖F x‖ₑ ^ q :=
        Work.BourgainPlan.IonescuWainger.eLpNorm_rpow_eq_lintegral hqpos F hFm
      have hLHS : ∫⁻ x : ℝ, ‖FourierTransformInv.fourierInv
              (fun ξ : ℝ => m ξ * FourierTransform.fourier g ξ) x‖ₑ ^ q
          = (MeasureTheory.eLpNorm F (ENNReal.ofReal q)
              (MeasureTheory.volume : MeasureTheory.Measure ℝ)) ^ q := by
        rw [hstep, hE]
      have hRHS : (MeasureTheory.eLpNorm F (ENNReal.ofReal q)
              (MeasureTheory.volume : MeasureTheory.Measure ℝ)) ^ q
          ≤ ENNReal.ofReal ((C * A) ^ q) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ q := by
        calc (MeasureTheory.eLpNorm F (ENNReal.ofReal q)
                (MeasureTheory.volume : MeasureTheory.Measure ℝ)) ^ q
            ≤ (ENNReal.ofReal (C * A) * MeasureTheory.eLpNorm g (ENNReal.ofReal q)
                (MeasureTheory.volume : MeasureTheory.Measure ℝ)) ^ q :=
              ENNReal.rpow_le_rpow hkey hqpos.le
          _ = ENNReal.ofReal ((C * A) ^ q) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ q := by
              rw [ENNReal.mul_rpow_of_nonneg _ _ hqpos.le,
                ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hCpos.le hApos.le) hqpos.le,
                Work.BourgainPlan.IonescuWainger.eLpNorm_rpow_eq_lintegral hqpos g
                  hg.aestronglyMeasurable]
      exact hLHS.trans_le hRHS

end

end Work.BourgainPlan.Maximal
