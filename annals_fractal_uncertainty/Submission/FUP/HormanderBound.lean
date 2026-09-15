import Submission.FUP.HermHessBridge
import Mathlib.Analysis.InnerProductSpace.Basic

open MeasureTheory
open scoped BigOperators ContDiff

set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {d : ℕ}

/-!
# The Hörmander "pointwise Cauchy--Schwarz + Kohn--Morrey" bound

This module assembles the *only* estimate that the abstract existence theorem (Demailly,
*Complex Analytic and Differential Geometry*, Chapter VIII, Theorems 1.2 and 4.5) needs as input
in the concrete `∂̄`-setting:

`‖⟨η, u⟩_{L²(e^{-φ})}‖² ≤ (∫ |η|² e^{-φ}/κ) · (‖∂̄u‖²_{L²(e^{-φ})} + ‖ϑu‖²_{L²(e^{-φ})})`

for every smooth compactly supported `(0,1)`-form `u`.  It is the combination of the pointwise
Cauchy--Schwarz inequality (with the weight `1/κ`) and the Kohn--Morrey estimate
`∫ κ|u|²e^{-φ} ≤ ‖∂̄u‖² + ‖ϑu‖²` of `Submission.FUP.HermHessBridge`.
-/

namespace Submission.FUP

/-- The Hermitian pairing `∑_j η_j conj(u_j)` of two `(0,1)`-forms. -/
noncomputable def formDot (η u : (Fin d → ℂ) → (Fin d → ℂ)) (z : Fin d → ℂ) : ℂ :=
  ∑ j, η z j * star (u z j)

/-- The weighted `L²` pairing `⟨η, u⟩_{e^{-φ}} = ∫ ∑_j η_j conj(u_j) e^{-φ}`. -/
noncomputable def formPair (η u : (Fin d → ℂ) → (Fin d → ℂ)) (φ : (Fin d → ℂ) → ℝ) : ℂ :=
  ∫ z, formDot η u z * ((Real.exp (-(φ z)) : ℝ) : ℂ)

/-- `∫ κ|u|²e^{-φ}`. -/
noncomputable def kapNormSq (u : (Fin d → ℂ) → (Fin d → ℂ)) (φ : (Fin d → ℂ) → ℝ)
    (κ : (Fin d → ℂ) → ℝ) : ℝ :=
  ∫ z, κ z * (∑ j, ‖u z j‖ ^ 2) * Real.exp (-(φ z))

/-- `∫ |∂̄u|²e^{-φ}` (the `(0,2)`-norm of `∂̄u`). -/
noncomputable def dbarNormSq (u : (Fin d → ℂ) → (Fin d → ℂ)) (φ : (Fin d → ℂ) → ℝ) : ℝ :=
  ∫ z, ((1 / 2 : ℝ) * ∑ j, ∑ k, ‖dbComp u k j z - dbComp u j k z‖ ^ 2) * Real.exp (-(φ z))

/-- `∫ |ϑu|²e^{-φ}` (the norm of the formal adjoint). -/
noncomputable def adjNormSq (u : (Fin d → ℂ) → (Fin d → ℂ)) (φ : (Fin d → ℂ) → ℝ) : ℝ :=
  ∫ z, (‖∑ j, covComp u φ j z‖ ^ 2) * Real.exp (-(φ z))

/-- `∫ |η|²e^{-φ}/κ`. -/
noncomputable def etaKapNorm (η : (Fin d → ℂ) → (Fin d → ℂ)) (φ : (Fin d → ℂ) → ℝ)
    (κ : (Fin d → ℂ) → ℝ) : ℝ :=
  ∫ z, formNormSq η z * Real.exp (-(φ z)) / κ z



lemma formDot_norm_le {η u : (Fin d → ℂ) → (Fin d → ℂ)} (z : Fin d → ℂ) :
    ‖formDot η u z‖ ≤ ∑ j, ‖η z j‖ * ‖u z j‖ := by
  have h : formDot η u z = ∑ j, η z j * star (u z j) := rfl
  rw [h]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  simp only [norm_mul, norm_star]
  exact le_rfl

lemma formDot_norm_sq_le {η u : (Fin d → ℂ) → (Fin d → ℂ)} {κ : (Fin d → ℂ) → ℝ}
    (z : Fin d → ℂ) (hκ : 0 < κ z) :
    ‖formDot η u z‖ ^ 2 ≤ (∑ j, ‖η z j‖ ^ 2 / κ z) * (κ z * ∑ j, ‖u z j‖ ^ 2) := by
  have h1 : ‖formDot η u z‖ ^ 2 ≤ (∑ j, ‖η z j‖ * ‖u z j‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (formDot_norm_le z) 2
  have h2 : (∑ j, ‖η z j‖ * ‖u z j‖) ^ 2
      ≤ (∑ j, ‖η z j‖ ^ 2) * (∑ j, ‖u z j‖ ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖η z j‖) (fun j => ‖u z j‖)
  have h3 : (∑ j, ‖η z j‖ ^ 2 / κ z) * (κ z * ∑ j, ‖u z j‖ ^ 2)
      = (∑ j, ‖η z j‖ ^ 2) * (∑ j, ‖u z j‖ ^ 2) := by
    rw [← Finset.sum_div]
    field_simp
  rw [h3]
  exact h1.trans h2

lemma exp_neg_half_sq (t : ℝ) : Real.exp (-t / 2) ^ 2 = Real.exp (-t) := by
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

lemma sqrt_mul_sqrt (a b : ℝ) (ha : 0 ≤ a) :
    Real.sqrt a * Real.sqrt b = Real.sqrt (a * b) := (Real.sqrt_mul ha b).symm

/-- **The pointwise Cauchy--Schwarz inequality with the weight `1/κ`.** -/
lemma formDot_norm_mul_exp_le (z : Fin d → ℂ) {η u : (Fin d → ℂ) → (Fin d → ℂ)}
    {φ : (Fin d → ℂ) → ℝ} {κ : (Fin d → ℂ) → ℝ} (hκ : 0 < κ z) :
    ‖formDot η u z‖ * Real.exp (-(φ z))
      ≤ (Real.sqrt (∑ j, ‖η z j‖ ^ 2 / κ z) * Real.exp (-(φ z) / 2))
        * (Real.sqrt (κ z * ∑ j, ‖u z j‖ ^ 2) * Real.exp (-(φ z) / 2)) := by
  set A : ℝ := ∑ j, ‖η z j‖ ^ 2 / κ z with hA
  set B : ℝ := κ z * ∑ j, ‖u z j‖ ^ 2 with hB
  have hA0 : 0 ≤ A := by
    rw [hA]; exact Finset.sum_nonneg fun j _ => div_nonneg (by positivity) hκ.le
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hcs : ‖formDot η u z‖ ^ 2 ≤ A * B := by
    rw [hA, hB]; exact formDot_norm_sq_le z hκ
  have h1 : ‖formDot η u z‖ ≤ Real.sqrt (A * B) :=
    Real.le_sqrt (norm_nonneg _) (mul_nonneg hA0 hB0) |>.mpr hcs
  have h2 : Real.sqrt A * Real.sqrt B = Real.sqrt (A * B) := (Real.sqrt_mul hA0 B).symm
  have he : Real.exp (-(φ z) / 2) * Real.exp (-(φ z) / 2) = Real.exp (-(φ z)) := by
    rw [← Real.exp_add]; congr 1; ring
  calc ‖formDot η u z‖ * Real.exp (-(φ z))
      ≤ Real.sqrt (A * B) * Real.exp (-(φ z)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
    _ = (Real.sqrt A * Real.exp (-(φ z) / 2)) * (Real.sqrt B * Real.exp (-(φ z) / 2)) := by
        rw [← h2, ← he]; ring
    _ = _ := by rw [hA, hB]

/-- A finite sum of compactly supported real functions has compact support. -/
private lemma hcs_finset_sum {ι : Type*} [Fintype ι] {F : ι → (Fin d → ℂ) → ℝ}
    (hF : ∀ i, HasCompactSupport (F i)) : HasCompactSupport (fun z => ∑ i, F i z) := by
  have h := HasCompactSupport.finset_sum (s := (Finset.univ : Finset ι)) (f := F)
    (fun i _ => hF i)
  have heq : (∑ i : ι, F i) = fun z => ∑ i : ι, F i z := by
    funext z; exact Finset.sum_apply z Finset.univ F
  rwa [heq] at h

/-- A nonnegative a.e.-strongly-measurable function with finite `ofReal`-lintegral is integrable. -/
lemma integrable_of_lintegral_ofReal_lt_top {f : (Fin d → ℂ) → ℝ}
    (hf : AEStronglyMeasurable f (volume : Measure (Fin d → ℂ)))
    (hnn : ∀ z, 0 ≤ f z) (h : ∫⁻ z, ENNReal.ofReal (f z) < ⊤) :
    Integrable f (volume : Measure (Fin d → ℂ)) :=
  ⟨hf, (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hnn)).mpr h⟩

/-- **The abstract Cauchy--Schwarz + Kohn--Morrey estimate.**

`‖⟨η,u⟩_{e^{-φ}}‖² ≤ (∫|η|²e^{-φ}/κ)·(‖∂̄u‖²_{e^{-φ}} + ‖ϑu‖²_{e^{-φ}})`, the estimate that
Demailly's abstract existence theorem (Chapter VIII, Theorem 1.2) needs as its input in the
concrete `∂̄`-setting.  This is the combination of the pointwise Cauchy--Schwarz inequality for the
weight `1/κ` (`formDot_norm_mul_exp_le`) with the Kohn--Morrey estimate
`kohn_morrey_estimate_of_hessian`. -/
theorem norm_formPair_sq_le {η u : (Fin d → ℂ) → (Fin d → ℂ)} {φ : (Fin d → ℂ) → ℝ}
    {κ : (Fin d → ℂ) → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hκc : Continuous κ) (hκpos : ∀ z, 0 < κ z)
    (hηc : ∀ j, Continuous (fun z => η z j))
    (hηint : ∫⁻ z, ENNReal.ofReal (formNormSq η z * Real.exp (-(φ z)) / κ z) < ⊤)
    (hu : ∀ j, ContDiff ℝ 2 (fComp u j)) (hsu : ∀ j, HasCompactSupport (fComp u j))
    (hhess : ∀ z (w : Fin d → ℂ), 4 * (κ z * ∑ j, ‖w j‖ ^ 2)
      ≤ (iteratedFDeriv ℝ 2 φ z) ![w, w]
        + (iteratedFDeriv ℝ 2 φ z) ![Complex.I • w, Complex.I • w]) :
    ‖formPair η u φ‖ ^ 2 ≤ etaKapNorm η φ κ * (dbarNormSq u φ + adjNormSq u φ) := by
  have hφc : Continuous φ := hφ.continuous
  have hFNScont : Continuous (formNormSq η) := by
    have h : Continuous (fun z => ∑ j, ‖η z j‖ ^ 2) :=
      continuous_finsetSum _ (fun j _ => (hηc j).norm.pow 2)
    exact h
  have hUcont : Continuous (fun z => ∑ j, ‖u z j‖ ^ 2) :=
    continuous_finsetSum _ (fun j _ => ((hu j).continuous.norm).pow 2)
  have hUcs : HasCompactSupport (fun z => ∑ j, ‖u z j‖ ^ 2) :=
    hcs_finset_sum fun j =>
      (hsu j).comp_left (g := fun w : ℂ => ‖w‖ ^ 2) (by simp)
  have hFNSnn : ∀ z, 0 ≤ formNormSq η z := fun z => by
    rw [formNormSq]; exact Finset.sum_nonneg fun j _ => by positivity
  have hUnn : ∀ z, 0 ≤ ∑ j, ‖u z j‖ ^ 2 := fun z =>
    Finset.sum_nonneg fun j _ => by positivity
  -- integrability of the first squared majorant, from the finiteness hypothesis
  have hIntA : Integrable (fun z => formNormSq η z * ((κ z)⁻¹ * Real.exp (-(φ z)))) := by
    refine integrable_of_lintegral_ofReal_lt_top ?_ (fun z => ?_) ?_
    · exact (hFNScont.mul ((hκc.inv₀ fun z => (hκpos z).ne').mul
        (Real.continuous_exp.comp hφc.neg))).aestronglyMeasurable
    · exact mul_nonneg (hFNSnn z)
        (mul_nonneg (inv_nonneg.mpr (hκpos z).le) (Real.exp_nonneg _))
    · rw [lintegral_congr fun z => by
        rw [show formNormSq η z * ((κ z)⁻¹ * Real.exp (-(φ z)))
            = formNormSq η z * Real.exp (-(φ z)) / κ z by ring]]
      exact hηint
  have hIntB : Integrable (fun z => (∑ j, ‖u z j‖ ^ 2) * (κ z * Real.exp (-(φ z)))) :=
    (hUcont.mul (hκc.mul (Real.continuous_exp.comp hφc.neg))).integrable_of_hasCompactSupport
      (hUcs.mul_right (f' := fun z => κ z * Real.exp (-(φ z))))
  -- the two `L²` majorants
  let F : (Fin d → ℂ) → ℝ := fun z => Real.sqrt (formNormSq η z / κ z) * Real.exp (-(φ z) / 2)
  let G : (Fin d → ℂ) → ℝ := fun z => Real.sqrt (κ z * (∑ j, ‖u z j‖ ^ 2)) * Real.exp (-(φ z) / 2)
  have hFcont : Continuous F := by
    change Continuous (fun z => Real.sqrt (formNormSq η z / κ z) * Real.exp (-(φ z) / 2))
    exact (Real.continuous_sqrt.comp (hFNScont.div hκc fun z => (hκpos z).ne')).mul
      (Real.continuous_exp.comp (hφc.neg.div_const 2))
  have hGcont : Continuous G := by
    change Continuous (fun z => Real.sqrt (κ z * (∑ j, ‖u z j‖ ^ 2)) * Real.exp (-(φ z) / 2))
    exact (Real.continuous_sqrt.comp (hκc.mul hUcont)).mul
      (Real.continuous_exp.comp (hφc.neg.div_const 2))
  have hFmem : MemLp F 2 (volume : Measure (Fin d → ℂ)) := by
    rw [memLp_two_iff_integrable_sq hFcont.aestronglyMeasurable]
    change Integrable (fun z => (Real.sqrt (formNormSq η z / κ z) * Real.exp (-(φ z) / 2)) ^ 2)
    refine hIntA.congr (Filter.Eventually.of_forall fun z => ?_)
    show formNormSq η z * ((κ z)⁻¹ * Real.exp (-(φ z)))
      = (Real.sqrt (formNormSq η z / κ z) * Real.exp (-(φ z) / 2)) ^ 2
    rw [mul_pow, Real.sq_sqrt (div_nonneg (hFNSnn z) (hκpos z).le), exp_neg_half_sq]
    ring
  have hGmem : MemLp G 2 (volume : Measure (Fin d → ℂ)) := by
    rw [memLp_two_iff_integrable_sq hGcont.aestronglyMeasurable]
    change Integrable (fun z => (Real.sqrt (κ z * (∑ j, ‖u z j‖ ^ 2))
      * Real.exp (-(φ z) / 2)) ^ 2)
    refine hIntB.congr (Filter.Eventually.of_forall fun z => ?_)
    show (∑ j, ‖u z j‖ ^ 2) * (κ z * Real.exp (-(φ z)))
      = (Real.sqrt (κ z * (∑ j, ‖u z j‖ ^ 2)) * Real.exp (-(φ z) / 2)) ^ 2
    rw [mul_pow, Real.sq_sqrt (mul_nonneg (hκpos z).le (hUnn z)), exp_neg_half_sq]
    ring
  have hFGint : Integrable (fun z => F z * G z) := hFmem.integrable_mul hGmem
  -- Hölder
  have hHolder : ∫ z, F z * G z
      ≤ Real.sqrt (∫ z, F z ^ 2) * Real.sqrt (∫ z, G z ^ 2) := by
    have hFnn : 0 ≤ᵐ[volume] F := Filter.Eventually.of_forall fun z =>
      mul_nonneg (Real.sqrt_nonneg _) (Real.exp_nonneg _)
    have hGnn : 0 ≤ᵐ[volume] G := Filter.Eventually.of_forall fun z =>
      mul_nonneg (Real.sqrt_nonneg _) (Real.exp_nonneg _)
    have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume) (p := 2) (q := 2)
      (Real.HolderConjugate.two_two) hFnn hGnn
      (by simpa only [ENNReal.ofReal_ofNat] using hFmem)
      (by simpa only [ENNReal.ofReal_ofNat] using hGmem)
    simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow] using h
  -- the two squared integrals
  have hF2 : ∫ z, F z ^ 2 = etaKapNorm η φ κ := by
    rw [etaKapNorm]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show (Real.sqrt (formNormSq η z / κ z) * Real.exp (-(φ z) / 2)) ^ 2
      = formNormSq η z * Real.exp (-(φ z)) / κ z
    rw [mul_pow, Real.sq_sqrt (div_nonneg (hFNSnn z) (hκpos z).le), exp_neg_half_sq]
    ring
  have hG2 : ∫ z, G z ^ 2 = kapNormSq u φ κ := by
    rw [kapNormSq]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show (Real.sqrt (κ z * (∑ j, ‖u z j‖ ^ 2)) * Real.exp (-(φ z) / 2)) ^ 2
      = κ z * (∑ j, ‖u z j‖ ^ 2) * Real.exp (-(φ z))
    rw [mul_pow, Real.sq_sqrt (mul_nonneg (hκpos z).le (hUnn z)), exp_neg_half_sq]
  have hKM : kapNormSq u φ κ ≤ dbarNormSq u φ + adjNormSq u φ := by
    rw [kapNormSq, dbarNormSq, adjNormSq]
    exact kohn_morrey_estimate_of_hessian hu hφ hsu hκc hhess
  have hEtaNonneg : 0 ≤ etaKapNorm η φ κ := by
    rw [etaKapNorm]
    refine integral_nonneg fun z => ?_
    have h1 : 0 ≤ formNormSq η z := by
      rw [formNormSq]; exact Finset.sum_nonneg fun j _ => by positivity
    exact div_nonneg (mul_nonneg h1 (Real.exp_nonneg _)) (hκpos z).le
  -- the pointwise majorant
  have hpoint : (fun z => ‖formDot η u z‖ * Real.exp (-(φ z))) ≤ fun z => F z * G z := by
    intro z
    have h := formDot_norm_mul_exp_le z (κ := κ) (η := η) (u := u) (φ := φ) (hκpos z)
    have hsumdiv : (∑ j, ‖η z j‖ ^ 2 / κ z) = formNormSq η z / κ z := by
      rw [show formNormSq η z = ∑ j, ‖η z j‖ ^ 2 from rfl, Finset.sum_div]
    rwa [hsumdiv] at h
  have hstep1 : ‖formPair η u φ‖ ≤ ∫ z, F z * G z := by
    have h1 : ‖formPair η u φ‖ ≤ ∫ z, ‖formDot η u z‖ * Real.exp (-(φ z)) := by
      refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      show ‖formDot η u z * ((Real.exp (-(φ z)) : ℝ) : ℂ)‖
        = ‖formDot η u z‖ * Real.exp (-(φ z))
      have hnorm : ‖(((Real.exp (-(φ z)) : ℝ)) : ℂ)‖ = Real.exp (-(φ z)) := by
        rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self (Real.exp_nonneg _)]
      rw [norm_mul, hnorm]
    refine h1.trans ?_
    exact integral_mono_of_nonneg (Filter.Eventually.of_forall fun z =>
      mul_nonneg (norm_nonneg _) (Real.exp_nonneg _)) hFGint
      (Filter.Eventually.of_forall hpoint)
  have hF2nn : 0 ≤ ∫ z, F z ^ 2 := integral_nonneg fun z => by positivity
  have hG2nn : 0 ≤ ∫ z, G z ^ 2 := integral_nonneg fun z => by positivity
  calc ‖formPair η u φ‖ ^ 2
      ≤ (∫ z, F z * G z) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hstep1 2
    _ ≤ (Real.sqrt (∫ z, F z ^ 2) * Real.sqrt (∫ z, G z ^ 2)) ^ 2 := by
        refine pow_le_pow_left₀ ?_ hHolder 2
        positivity
    _ = (∫ z, F z ^ 2) * (∫ z, G z ^ 2) := by
        rw [mul_pow, Real.sq_sqrt hF2nn, Real.sq_sqrt hG2nn]
    _ = etaKapNorm η φ κ * kapNormSq u φ κ := by rw [hF2, hG2]
    _ ≤ etaKapNorm η φ κ * (dbarNormSq u φ + adjNormSq u φ) :=
        mul_le_mul_of_nonneg_left hKM hEtaNonneg

end Submission.FUP
