import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PCFU.taper_pairing_aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PCFU

open MeasureTheory

theorem slotTrunc {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ}
    {fu : Work.BoseBoxFix.LowCut} {N : ℕ}
    {y : EuclideanSpace ℝ (Fin 3)} {g : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgs : tsupport g ⊆ Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ)) :
    MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin 3) =>
        ((g (y - z) : ℝ) : ℂ) * Work.BoseBoxFock.PCFU.KfrU v h μ fu N z)
      ∧ (∫ z, ((g (y - z) : ℝ) : ℂ) * Work.BoseBoxFock.PCFU.KfrU v h μ fu N z
        = ∑ m : Work.BoseBoxFock.Lab N,
            ((Work.BoseBoxFock.W1h v h μ fu N m : ℝ) : ℂ)
              * Submission.BoseGases.kinFT (fun z => ((g (y - z) : ℝ) : ℂ))
                  (-(Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N m))) := by
  classical
  -- The `k`-frame `KfrU` is a *finite* trigonometric sum (`k` runs over the label cube
  -- `Lab N`), so the `univ`-truncation is an identity, not a limit: expand the frame and
  -- interchange the finite sum with the integral.
  have hboximg : IsCompact ((fun w : EuclideanSpace ℝ (Fin 3) => y - w) ''
      Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ)) :=
    (Work.BoseBoxFock.L1Tails.latPair_boxL_isCompact _).image (continuous_const.sub continuous_id)
  -- the support of `z ↦ g (y - z)` is the reflected translate of `tsupport g` (compact)
  have hsF : Function.support (fun z : EuclideanSpace ℝ (Fin 3) => ((g (y - z) : ℝ) : ℂ)) ⊆
      (fun w : EuclideanSpace ℝ (Fin 3) => y - w) ''
        Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ) := by
    intro z hz
    rw [Function.mem_support] at hz
    refine ⟨y - z, ?_, by abel_nf⟩
    exact hgs (subset_tsupport g (by intro hh; exact hz (by rw [hh]; simp)))
  have hFc : Continuous (fun z : EuclideanSpace ℝ (Fin 3) => ((g (y - z) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (hg.continuous.comp (continuous_const.sub continuous_id))
  -- integrability of the whole integrand: continuous with compact support
  have hcont : Continuous (fun z : EuclideanSpace ℝ (Fin 3) =>
      ((g (y - z) : ℝ) : ℂ) * Work.BoseBoxFock.PCFU.KfrU v h μ fu N z) :=
    hFc.mul (Work.BoseBoxFock.PCFU.taper_continuous_KfrU v h μ fu N)
  have hInt : Integrable (fun z : EuclideanSpace ℝ (Fin 3) =>
      ((g (y - z) : ℝ) : ℂ) * Work.BoseBoxFock.PCFU.KfrU v h μ fu N z) :=
    hcont.integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact hboximg
        (fun z hz => hsF (Function.support_mul_subset_left _ _ hz)))
  -- the individual summands of the expanded frame
  have hsummand : ∀ m : Work.BoseBoxFock.Lab N, Integrable (fun z : EuclideanSpace ℝ (Fin 3) =>
      ((g (y - z) : ℝ) : ℂ) *
        (((Work.BoseBoxFock.W1h v h μ fu N m : ℝ) : ℂ) *
          Complex.exp (Complex.I * (inner ℝ
            (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N m) z : ℂ)))) := by
    intro m
    exact Continuous.integrable_of_hasCompactSupport (by fun_prop)
      (HasCompactSupport.of_support_subset_isCompact hboximg
        (fun z hz => hsF (Function.support_mul_subset_left _ _ hz)))
  -- expansion of the frame (`KfrU` is a definitional finite sum)
  have hexpand : (fun z : EuclideanSpace ℝ (Fin 3) =>
        ((g (y - z) : ℝ) : ℂ) * Work.BoseBoxFock.PCFU.KfrU v h μ fu N z)
      = (fun z : EuclideanSpace ℝ (Fin 3) => ∑ m : Work.BoseBoxFock.Lab N,
          ((g (y - z) : ℝ) : ℂ) * (((Work.BoseBoxFock.W1h v h μ fu N m : ℝ) : ℂ) *
            Complex.exp (Complex.I * (inner ℝ
              (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N m) z : ℂ)))) := by
    funext z
    rw [Work.BoseBoxFock.PCFU.KfrU, Finset.mul_sum]
  -- termwise integration
  have hLHS : (∫ z : EuclideanSpace ℝ (Fin 3),
        ((g (y - z) : ℝ) : ℂ) * Work.BoseBoxFock.PCFU.KfrU v h μ fu N z)
      = ∑ m : Work.BoseBoxFock.Lab N, (((Work.BoseBoxFock.W1h v h μ fu N m : ℝ) : ℂ) *
          ∫ z : EuclideanSpace ℝ (Fin 3), ((g (y - z) : ℝ) : ℂ) *
            Complex.exp (Complex.I * (inner ℝ
              (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N m) z : ℂ))) := by
    rw [hexpand]
    rw [MeasureTheory.integral_finsetSum (Finset.univ : Finset (Work.BoseBoxFock.Lab N))
      (f := fun (m : Work.BoseBoxFock.Lab N) (z : EuclideanSpace ℝ (Fin 3)) =>
        ((g (y - z) : ℝ) : ℂ) * (((Work.BoseBoxFock.W1h v h μ fu N m : ℝ) : ℂ) *
          Complex.exp (Complex.I * (inner ℝ
            (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N m) z : ℂ))))
      (fun m _ => hsummand m)]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    beta_reduce
    ring
  -- the per-mode Fourier transform: `∫ z, g(y−z)·e^{i⟪κ_m,z⟫} = kinFT (g(y−·)) (−κ_m)`
  have hkin : ∀ m : Work.BoseBoxFock.Lab N,
      (∫ z : EuclideanSpace ℝ (Fin 3), ((g (y - z) : ℝ) : ℂ) *
        Complex.exp (Complex.I * (inner ℝ
          (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N m) z : ℂ)))
      = Submission.BoseGases.kinFT (fun z => ((g (y - z) : ℝ) : ℂ))
          (-(Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N m)) := by
    intro m
    simp only [Submission.BoseGases.kinFT]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    beta_reduce
    have harg : -(Complex.I * ((inner ℝ
          (-(Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N m)) z : ℝ) : ℂ))
        = Complex.I * ((inner ℝ
            (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N m) z : ℝ) : ℂ) := by
      rw [inner_neg_left]
      push_cast
      ring
    rw [harg, mul_comm]
  refine ⟨hInt, ?_⟩
  rw [hLHS]
  exact Finset.sum_congr rfl (fun m _ => by rw [hkin m])

end Work.BoseBoxFock.PCFU
