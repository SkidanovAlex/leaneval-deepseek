import Mathlib.Tactic.Have
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Submission.Work.SmallBoxBridge.Resolve.kinFT_eq_fourier
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory
open scoped Real FourierTransform ComplexConjugate

namespace Work.BoseKinLoc.NeuFrac

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- A complex number with vanishing imaginary part is the coercion of its real part. -/
lemma eq_ofReal_re_of_im_eq_zero {z : ℂ} (h : z.im = 0) : z = ((z.re : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [h]

/-- Conjugation of a complex number with vanishing imaginary part. -/
lemma conj_eq_ofReal_re_of_im_eq_zero {z : ℂ} (h : z.im = 0) :
    conj z = ((z.re : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [h]

/-- The pointwise identity `conj (a * conj b) = b * conj a` which flips the order of the two
arguments of the (conjugate-linear) pairing. -/
lemma conj_mul_conj (a b : ℂ) : conj (a * conj b) = b * conj a := by
  simp [map_mul, mul_comm]

/-- The real part of a real multiple of a complex number. -/
lemma re_smul_ofReal (r : ℝ) (z : ℂ) : (r • z).re = r * z.re := by
  rw [RCLike.real_smul_eq_coe_mul]
  exact Complex.re_ofReal_mul r z

theorem parseval_pconv_re (F G : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ)
    (hF : ∀ x, (F x).im = 0) (hG : ∀ x, (G x).im = 0) :
    (∫ x : EuclideanSpace ℝ (Fin 3), (F x).re * (G x).re)
      = ((2 * Real.pi) ^ 3)⁻¹ *
          ∫ p : EuclideanSpace ℝ (Fin 3),
            (Submission.BoseGases.kinFT (F : EuclideanSpace ℝ (Fin 3) → ℂ) p *
              (starRingEnd ℂ) (Submission.BoseGases.kinFT (G : EuclideanSpace ℝ (Fin 3) → ℂ) p)).re := by
  classical
  have hκpos : (0 : ℝ) < 2 * Real.pi := by positivity
  have hκne : (2 * Real.pi : ℝ) ≠ 0 := hκpos.ne'
  -- ### integrability of the position-space pairing
  have hInt1 : Integrable (fun x : ℝ³ => F x * conj (G x)) := by
    refine (SchwartzMap.integrable F).mul_bdd (c := SchwartzMap.seminorm ℝ 0 0 G)
      (Complex.continuous_conj.comp G.continuous).aestronglyMeasurable ?_
    filter_upwards with x
    rw [Complex.norm_conj]
    exact SchwartzMap.norm_le_seminorm ℝ G x
  -- ### integrability of the momentum-space pairing
  have hInt2 : Integrable (fun p : ℝ³ =>
      Submission.BoseGases.kinFT (F : ℝ³ → ℂ) p *
        conj (Submission.BoseGases.kinFT (G : ℝ³ → ℂ) p)) := by
    have hbase : Integrable (fun ξ : ℝ³ =>
        (𝓕 F) ξ * conj ((𝓕 G) ξ)) := by
      refine (SchwartzMap.integrable (𝓕 F)).mul_bdd
        (c := SchwartzMap.seminorm ℝ 0 0 (𝓕 G))
        (Complex.continuous_conj.comp (SchwartzMap.continuous (𝓕 G))).aestronglyMeasurable ?_
      filter_upwards with ξ
      rw [Complex.norm_conj]
      exact SchwartzMap.norm_le_seminorm ℝ (𝓕 G) ξ
    refine (hbase.comp_smul (R := (2 * Real.pi)⁻¹) (inv_ne_zero hκne)).congr ?_
    filter_upwards with p
    beta_reduce
    rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe,
      ← _root_.Work.SmallBoxBridge.Resolve.kinFT_eq_fourier (F : ℝ³ → ℂ) p,
      ← _root_.Work.SmallBoxBridge.Resolve.kinFT_eq_fourier (G : ℝ³ → ℂ) p]
  -- ### the complex Plancherel/Parseval identity
  have hPlanch : (∫ x : ℝ³, F x * conj (G x))
      = ∫ ξ : ℝ³, (𝓕 F) ξ * conj ((𝓕 G) ξ) := by
    have hP := SchwartzMap.integral_inner_fourier_fourier F G
    simp only [RCLike.inner_apply] at hP
    have h1 : conj (∫ x : ℝ³, F x * conj (G x))
        = ∫ x : ℝ³, G x * conj (F x) := by
      rw [← integral_conj]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => conj_mul_conj (F x) (G x))
    have h2 : conj (∫ ξ : ℝ³, (𝓕 F) ξ * conj ((𝓕 G) ξ))
        = ∫ ξ : ℝ³, (𝓕 G) ξ * conj ((𝓕 F) ξ) := by
      rw [← integral_conj]
      exact integral_congr_ae
        (Filter.Eventually.of_forall fun ξ => conj_mul_conj ((𝓕 F) ξ) ((𝓕 G) ξ))
    have hboth : conj (∫ x : ℝ³, F x * conj (G x))
        = conj (∫ ξ : ℝ³, (𝓕 F) ξ * conj ((𝓕 G) ξ)) := by
      rw [h1, h2]
      simpa only [SchwartzMap.fourier_coe] using hP.symm
    simpa only [Complex.conj_conj] using congrArg conj hboth
  -- ### the scaling `p = 2π ξ`
  have hscale : (∫ p : ℝ³, Submission.BoseGases.kinFT (F : ℝ³ → ℂ) p *
        conj (Submission.BoseGases.kinFT (G : ℝ³ → ℂ) p))
      = (2 * Real.pi) ^ 3 •
          (∫ ξ : ℝ³, (𝓕 F) ξ * conj ((𝓕 G) ξ)) := by
    have hcomp := MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg (volume : Measure ℝ³)
      (fun ξ : ℝ³ => (𝓕 F) ξ * conj ((𝓕 G) ξ)) hκpos.le
    rw [show Module.finrank ℝ ℝ³ = 3 from by simp [EuclideanSpace]] at hcomp
    rw [← hcomp]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    beta_reduce
    rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe,
      ← _root_.Work.SmallBoxBridge.Resolve.kinFT_eq_fourier (F : ℝ³ → ℂ) p,
      ← _root_.Work.SmallBoxBridge.Resolve.kinFT_eq_fourier (G : ℝ³ → ℂ) p]
  -- ### real parts
  have hA : (∫ x : ℝ³, (F x).re * (G x).re) = (∫ x : ℝ³, F x * conj (G x)).re := by
    have hre : (∫ x : ℝ³, F x * conj (G x)).re
        = ∫ x : ℝ³, (F x * conj (G x)).re := (integral_re hInt1).symm
    rw [hre]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    beta_reduce
    rw [eq_ofReal_re_of_im_eq_zero (hF x), conj_eq_ofReal_re_of_im_eq_zero (hG x)]
    simp [Complex.ofReal_re]
  have hB : (∫ p : ℝ³, (Submission.BoseGases.kinFT (F : ℝ³ → ℂ) p *
        (starRingEnd ℂ) (Submission.BoseGases.kinFT (G : ℝ³ → ℂ) p)).re)
      = (∫ p : ℝ³, Submission.BoseGases.kinFT (F : ℝ³ → ℂ) p *
          conj (Submission.BoseGases.kinFT (G : ℝ³ → ℂ) p)).re := by
    have hre : (∫ p : ℝ³, Submission.BoseGases.kinFT (F : ℝ³ → ℂ) p *
          conj (Submission.BoseGases.kinFT (G : ℝ³ → ℂ) p)).re
        = ∫ p : ℝ³, (Submission.BoseGases.kinFT (F : ℝ³ → ℂ) p *
            conj (Submission.BoseGases.kinFT (G : ℝ³ → ℂ) p)).re :=
      (integral_re hInt2).symm
    rw [hre]
  have hVp : (∫ p : ℝ³, Submission.BoseGases.kinFT (F : ℝ³ → ℂ) p *
        conj (Submission.BoseGases.kinFT (G : ℝ³ → ℂ) p))
      = ((2 * Real.pi) ^ 3 : ℝ) • (∫ x : ℝ³, F x * conj (G x)) := by
    rw [hscale, hPlanch]
  have hsmul : ((((2 * Real.pi) ^ 3 : ℝ)) • (∫ x : ℝ³, F x * conj (G x))).re
      = (2 * Real.pi) ^ 3 * (∫ x : ℝ³, F x * conj (G x)).re := by
    exact re_smul_ofReal ((2 * Real.pi) ^ 3) (∫ x : ℝ³, F x * conj (G x))
  rw [hA, hB, hVp, hsmul]
  rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 3 hκne), one_mul]

end Work.BoseKinLoc.NeuFrac
