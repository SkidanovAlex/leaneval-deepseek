import Mathlib.Analysis.Convolution
import Mathlib.Tactic.Have
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseBoxFock.PCFU.ChDKernelDefs
import Submission.Work.BoseBoxFock.chat_eq_kinFT_of_even
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.PCFU

noncomputable section

open MeasureTheory
open scoped BigOperators Convolution

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem chDconv_kinFT {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fu : Work.BoseBoxFix.LowCut} {ℓ Λ : ℝ} (hℓ : 0 < ℓ) (hΛ : 0 < Λ)
    (hI : MeasureTheory.Integrable (Work.BoseFixR.W1fun v h ℓ))
    (hev : ∀ x : EuclideanSpace ℝ (Fin 3), Work.BoseFixR.W1fun v h ℓ (-x) = Work.BoseFixR.W1fun v h ℓ x)
    (p : EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.kinFT (fun y : EuclideanSpace ℝ (Fin 3) => ((∫ w : EuclideanSpace ℝ (Fin 3),
        Work.BoseK15.corpusBox.chiLam ℓ w
          * Work.BoseBoxFock.uvSmear fu Λ (Work.BoseFixR.W1fun v h ℓ) (y - w) : ℝ) : ℂ)) p
      = ((ℓ ^ 3 : ℝ) : ℂ)
        * ((Work.BoseK15.corpusBox.hatChi (ℓ • p) : ℝ) : ℂ)
        * ((Work.BoseBoxFock.uvCut fu Λ p
              * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p : ℝ) : ℂ) := by
  -- ### 1. Integrability of the two factors of the convolution
  -- The localisation window `χ_Λ` is continuous with compact support.
  have hchiInt : MeasureTheory.Integrable (Work.BoseK15.corpusBox.chiLam ℓ) :=
    (Work.BoseB4.BoxData.chiLam_cont Work.BoseK15.corpusBox ℓ).integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact
        (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ)
        (fun x hx => Work.BoseB4.BoxData.chiLam_supp Work.BoseK15.corpusBox hℓ hx))
  -- The smoothing kernel `ψ_Λ = uvKernel fu Λ` is (the real part of) a Schwartz function.
  have hKint : MeasureTheory.Integrable (Work.BoseBoxFock.uvKernel fu Λ) :=
    Work.BoseBoxFock.integrable_uvKernel fu hΛ
  -- The smeared weight is the convolution `ψ_Λ ⋆ W₁`.
  have hconvS : Work.BoseBoxFock.uvSmear fu Λ (Work.BoseFixR.W1fun v h ℓ)
      = Work.BoseBoxFock.uvKernel fu Λ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E3)]
          (Work.BoseFixR.W1fun v h ℓ) := by
    funext x
    rw [Work.BoseBoxFock.uvSmear, convolution_lsmul]
    simp only [smul_eq_mul]
    have hh := integral_sub_left_eq_self
      (fun t : E3 => Work.BoseBoxFock.uvKernel fu Λ t * Work.BoseFixR.W1fun v h ℓ (x - t))
      volume x
    simpa only [sub_sub_cancel] using hh
  have hSInt : MeasureTheory.Integrable
      (Work.BoseBoxFock.uvSmear fu Λ (Work.BoseFixR.W1fun v h ℓ)) := by
    rw [hconvS]
    exact MeasureTheory.Integrable.integrable_convolution
      (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := (volume : Measure E3)) hKint hI
  -- ### 2. The Fourier transform of a convolution is the product of the transforms
  rw [Work.BoseRowsL.Row2.kinFT_ofReal_convolution hchiInt hSInt p]
  -- ### 3. The two factors
  -- (a) `kinFT χ_Λ = ℓ³ χ̂(ℓp)`.
  have hchiFT : Submission.BoseGases.kinFT
      (fun x : E3 => ((Work.BoseK15.corpusBox.chiLam ℓ x : ℝ) : ℂ)) p
      = ((ℓ ^ 3 * Work.BoseK15.corpusBox.hatChi (ℓ • p) : ℝ) : ℂ) :=
    Work.BoseBoxFock.integral_chiLam_exp hℓ p
  -- (b) `kinFT (ψ_Λ ⋆ W₁) = ζ_Λ · ĉhat W₁`.
  have hSFT : Submission.BoseGases.kinFT
      (fun x : E3 => ((Work.BoseBoxFock.uvSmear fu Λ (Work.BoseFixR.W1fun v h ℓ) x : ℝ) : ℂ)) p
      = ((Work.BoseBoxFock.uvCut fu Λ p
            * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p : ℝ) : ℂ) := by
    have hrewrite : (fun x : E3 =>
          ((Work.BoseBoxFock.uvSmear fu Λ (Work.BoseFixR.W1fun v h ℓ) x : ℝ) : ℂ))
        = fun x : E3 => ((∫ y : E3,
            Work.BoseBoxFock.uvKernel fu Λ y * Work.BoseFixR.W1fun v h ℓ (x - y) : ℝ) : ℂ) := by
      funext x
      rw [hconvS]
      simp only [convolution_lsmul, smul_eq_mul]
    rw [hrewrite, Work.BoseRowsL.Row2.kinFT_ofReal_convolution hKint hI p,
      ← Work.BoseBoxFock.chat_eq_kinFT_of_even (W := Work.BoseBoxFock.uvKernel fu Λ)
        (fun z => Work.BoseBoxFock.uvKernel_even fu Λ z) p,
      Work.BoseBoxFock.chat_uvKernel fu hΛ p,
      ← Work.BoseBoxFock.chat_eq_kinFT_of_even (W := Work.BoseFixR.W1fun v h ℓ) hev p,
      ← Complex.ofReal_mul]
  rw [hchiFT, hSFT, Complex.ofReal_mul]

end

end Work.PCFU
