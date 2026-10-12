import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Submission.Work.BoseBoxFock.kinFT_plancherel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Derivative Plancherel for the `p`-convention Fourier transform

We prove the second-moment (derivative Plancherel) identity for `Submission.BoseGases.kinFT`
(`kinFT u p = ∫_y e^{−i⟪p,y⟫}u(y)dy`):

`∫_p Σᵢ ‖∂ᵢ(kinFT g)(p)‖² dp = (2π)³ ∫_x ‖x‖²‖g x‖² dx`   (`g` smooth, compactly supported),

the momentum-derivative counterpart of the corpus's momentum-moment identities (which read the
`⟨p,e_i⟩²`-weighted second moment of `kinFT g` against the transform of `∂_{e_i}g`).

The two ingredients:

* the **derivative identity** `∂_{p_i}(kinFT g)(p) = kinFT (fun z ↦ −i⟪e_i,z⟫ g z) p`.  It is
  Mathlib's `Real.hasFDerivAt_fourier` (`∂_ξ 𝓕g = 𝓕(fun v ↦ −2πi⟪v,·⟫ g v)`) transported to the
  `p`-convention through the chain rule with the dilation `p ↦ (2π)⁻¹ • p`
  (`Work.SmallBoxBridge.Resolve.kinFT_eq_fourier`), and read off in a direction
  (`Real.fourier_continuousLinearMap_apply` for the evaluation of the `→L`-valued Fourier
  transform);
* the corpus Plancherel for `L¹ ∩ L²` states (`Work.BoseKinLoc.Kinetic.kinFT_sq_of_memLp`),
  applied to each of the three scalar functions `z ↦ z_i g z` (smooth, compactly supported),
  which also supplies the integrability that lets the finite `Fin 3`-sum out of the integral.
-/

noncomputable section

open MeasureTheory
open scoped Real FourierTransform

set_option maxHeartbeats 800000

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The momentum-multiplication function `kinFTMomFun g i` -/

/-- The `i`-th momentum-multiplication function `z ↦ −i · z_i · g z`, the function whose
`kinFT` is the `i`-th partial derivative of `kinFT g`. -/
def kinFTMomFun (g : E3 → ℂ) (i : Fin 3) : E3 → ℂ :=
  fun z => -Complex.I * ((inner ℝ (EuclideanSpace.single i (1 : ℝ)) z : ℝ) : ℂ) * g z

lemma kinFTMomFun_apply (g : E3 → ℂ) (i : Fin 3) (z : E3) :
    kinFTMomFun g i z = -Complex.I * ((inner ℝ (EuclideanSpace.single i (1 : ℝ)) z : ℝ) : ℂ) * g z :=
  rfl

lemma continuous_kinFTMomFun {g : E3 → ℂ} (hg : Continuous g) (i : Fin 3) :
    Continuous (kinFTMomFun g i) := by
  rw [show kinFTMomFun g i = fun z : E3 =>
      (-Complex.I * ((inner ℝ (EuclideanSpace.single i (1 : ℝ)) z : ℝ) : ℂ)) * g z from rfl]
  exact (continuous_const.mul
    (Complex.continuous_ofReal.comp
      (innerSL ℝ (EuclideanSpace.single i (1 : ℝ))).continuous)).mul hg

lemma hasCompactSupport_kinFTMomFun {g : E3 → ℂ} (hgc : HasCompactSupport g) (i : Fin 3) :
    HasCompactSupport (kinFTMomFun g i) :=
  HasCompactSupport.mul_left (f := fun z : E3 =>
    -Complex.I * ((inner ℝ (EuclideanSpace.single i (1 : ℝ)) z : ℝ) : ℂ)) hgc

/-! ## 2. The `Fin 3`-sums at a point -/

/-- The squared modulus of `kinFTMomFun g i x` is `x_i² ‖g x‖²`. -/
lemma norm_kinFTMomFun_sq (g : E3 → ℂ) (i : Fin 3) (x : E3) :
    ‖kinFTMomFun g i x‖ ^ 2 = (inner ℝ (EuclideanSpace.single i (1 : ℝ)) x) ^ 2 * ‖g x‖ ^ 2 := by
  have h1 : ‖(-Complex.I * ((inner ℝ (EuclideanSpace.single i (1 : ℝ)) x : ℝ) : ℂ)) * g x‖
      = |inner ℝ (EuclideanSpace.single i (1 : ℝ)) x| * ‖g x‖ := by
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul]
    congr 1
    simp
  rw [kinFTMomFun, h1, mul_pow, sq_abs]

/-- `Σᵢ x_i² = ‖x‖²` for the standard basis `EuclideanSpace.single i 1`. -/
lemma sum_inner_single_sq (x : E3) :
    (∑ i : Fin 3, (inner ℝ (EuclideanSpace.single i (1 : ℝ)) x) ^ 2) = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [EuclideanSpace.inner_single_left]
  simp only [map_one, one_mul, Real.norm_eq_abs, sq_abs]

/-- The pointwise second-moment identity `Σᵢ ‖kinFTMomFun g i x‖² = ‖x‖²‖g x‖²`. -/
lemma sum_norm_kinFTMomFun_sq (g : E3 → ℂ) (x : E3) :
    (∑ i : Fin 3, ‖kinFTMomFun g i x‖ ^ 2) = ‖x‖ ^ 2 * ‖g x‖ ^ 2 := by
  rw [Finset.sum_congr rfl (fun i _ => norm_kinFTMomFun_sq g i x), ← Finset.sum_mul,
    sum_inner_single_sq]

/-! ## 3. The Fourier transform of the CLM-valued multiplier, evaluated in a direction -/

/-- The `→L`-valued Fourier transform of `fourierSMulRight (innerSL ℝ) g`, evaluated in a
direction `a` and at a frequency `y`, written as an explicit scalar integral.  This is
`Real.fourier_continuousLinearMap_apply` (moving `a` through the Bochner integral of continuous
linear maps) followed by the definitional unfolding `Real.fourier_eq` and the pointwise
computation `fourierSMulRight L f v a = −2πi ⟪v,a⟫ g v`. -/
private lemma fourier_fourierSMulRight_apply {g : E3 → ℂ}
    (hInt : Integrable (fun v : E3 => VectorFourier.fourierSMulRight (innerSL ℝ) g v))
    (y a : E3) :
    (𝓕 (fun v : E3 => VectorFourier.fourierSMulRight (innerSL ℝ) g v) y) a
      = ∫ v : E3, Complex.exp ((↑(-2 * Real.pi * inner ℝ v y) : ℂ) * Complex.I)
          * (-(2 * Real.pi * Complex.I) * ((inner ℝ v a : ℝ) : ℂ) * g v) := by
  rw [Real.fourier_continuousLinearMap_apply hInt, Real.fourier_eq]
  apply integral_congr_ae
  filter_upwards with v
  simp only [VectorFourier.fourierSMulRight_apply, Circle.smul_def, Real.fourierChar_apply,
    Complex.real_smul, smul_eq_mul]
  rw [innerSL_apply_apply]
  ring_nf

/-- The pointwise comparison of integrands after the substitution `y = (2π)⁻¹ • p`,
`a = (2π)⁻¹ • w`. -/
private lemma kinFT_deriv_integrand (g : E3 → ℂ) (p w v : E3) :
    Complex.exp ((↑(-2 * Real.pi * inner ℝ v ((2 * Real.pi)⁻¹ • p)) : ℂ) * Complex.I)
        * (-(2 * Real.pi * Complex.I) * ((inner ℝ v ((2 * Real.pi)⁻¹ • w) : ℝ) : ℂ) * g v)
      = Complex.exp (-(Complex.I * (inner ℝ p v : ℂ)))
        * (-Complex.I * ((inner ℝ w v : ℝ) : ℂ) * g v) := by
  rw [real_inner_smul_right v p, real_inner_smul_right v w]
  have harg : (↑(-2 * Real.pi * ((2 * Real.pi)⁻¹ * inner ℝ v p)) : ℂ) * Complex.I
      = -(Complex.I * (inner ℝ p v : ℂ)) := by
    rw [real_inner_comm v p]
    push_cast
    field_simp
  rw [harg]
  congr 2
  rw [real_inner_comm v w]
  push_cast
  field_simp

/-! ## 4. The derivative identity -/

/-- **Derivative identity for `kinFT`.**  For `g` smooth with compact support,
`∂_w (kinFT g)(p) = kinFT (fun z ↦ −i⟪w,z⟫ g z) p` for every direction `w`. -/
lemma kinFT_fderiv_dir {g : E3 → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g) (hgc : HasCompactSupport g)
    (p w : E3) :
    fderiv ℝ (fun q : E3 => Submission.BoseGases.kinFT g q) p w
      = Submission.BoseGases.kinFT
          (fun z : E3 => -Complex.I * ((inner ℝ w z : ℝ) : ℂ) * g z) p := by
  have hInt : Integrable g := hg.continuous.integrable_of_hasCompactSupport hgc
  -- integrability of `v ↦ ‖v‖ ‖g v‖`
  have hcs_norm : HasCompactSupport (fun v : E3 => ‖v‖ * ‖g v‖) :=
    (hgc.comp_left (g := fun z : ℂ => ‖z‖) (by simp)).mul_left
  have hIntW : Integrable (fun v : E3 => ‖v‖ * ‖g v‖) :=
    (continuous_norm.mul hg.continuous.norm).integrable_of_hasCompactSupport hcs_norm
  -- integrability of the `→L`-valued multiplier
  have hIntF : Integrable (fun v : E3 => VectorFourier.fourierSMulRight (innerSL ℝ) g v) := by
    refine Integrable.mono'
      (hIntW.const_mul (2 * Real.pi * ‖(innerSL ℝ : E3 →L[ℝ] E3 →L[ℝ] ℝ)‖))
      hInt.aestronglyMeasurable.fourierSMulRight (Filter.Eventually.of_forall (fun v => ?_))
    refine (VectorFourier.norm_fourierSMulRight_le (innerSL ℝ) g v).trans (le_of_eq ?_)
    ring
  -- the chain rule with the dilation `p ↦ (2π)⁻¹ • p`
  set s : E3 →L[ℝ] E3 := (2 * Real.pi)⁻¹ • (1 : E3 →L[ℝ] E3) with hs
  have hF : HasFDerivAt (𝓕 g)
      (𝓕 (fun v : E3 => VectorFourier.fourierSMulRight (innerSL ℝ) g v) (s p)) (s p) :=
    Real.hasFDerivAt_fourier hInt hIntW (s p)
  have hcomp : HasFDerivAt (fun q : E3 => 𝓕 g (s q))
      ((𝓕 (fun v : E3 => VectorFourier.fourierSMulRight (innerSL ℝ) g v) (s p)) ∘SL s) p :=
    hF.comp p s.hasFDerivAt
  have hfun : (fun q : E3 => 𝓕 g (s q)) = fun q : E3 => Submission.BoseGases.kinFT g q := by
    funext q
    rw [Work.SmallBoxBridge.Resolve.kinFT_eq_fourier]
    rfl
  have hkin : HasFDerivAt (fun q : E3 => Submission.BoseGases.kinFT g q)
      ((𝓕 (fun v : E3 => VectorFourier.fourierSMulRight (innerSL ℝ) g v) (s p)) ∘SL s) p :=
    hfun ▸ hcomp
  rw [hkin.fderiv]
  rw [ContinuousLinearMap.comp_apply]
  rw [show s p = (2 * Real.pi)⁻¹ • p from rfl, show s w = (2 * Real.pi)⁻¹ • w from rfl]
  rw [fourier_fourierSMulRight_apply hIntF]
  rw [Submission.BoseGases.kinFT]
  apply integral_congr_ae
  filter_upwards with v
  exact kinFT_deriv_integrand g p w v

/-! ## 5. The derivative Plancherel identity -/

/-- **Derivative Plancherel / second-moment identity for `kinFT`.**
For `g` smooth with compact support,
`∫ Σᵢ ‖∂ᵢ(kinFT g)(p)‖² dp = (2π)³ ∫ ‖x‖²‖g x‖² dx`.
Route: (i) the derivative identity `∂_{p_i}(kinFT g)(p) = kinFT (fun z => -Complex.I * (z i : ℂ) * g z) p`
(differentiation under the integral sign, justified by compact support); (ii) the corpus Plancherel
`Work.BoseBoxFock.kinFT_plancherel` applied to each scalar function `x ↦ x i * g x` (smooth, compactly
supported), plus `‖kinFT(-i x_i g)‖ = ‖kinFT(x_i g)‖`. -/
theorem kinFTDerivPlancherel {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g) :
    (∫ p : EuclideanSpace ℝ (Fin 3), ∑ i : Fin 3,
        ‖fderiv ℝ (fun q : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.kinFT g q) p
          (EuclideanSpace.single i (1 : ℝ))‖ ^ 2)
      = (2 * Real.pi) ^ 3 * ∫ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ^ 2 * ‖g x‖ ^ 2 := by
  have hcont : ∀ i : Fin 3, Continuous (kinFTMomFun g i) := fun i => continuous_kinFTMomFun hg.continuous i
  have hcs : ∀ i : Fin 3, HasCompactSupport (kinFTMomFun g i) := fun i => hasCompactSupport_kinFTMomFun hgc i
  have hmem1 : ∀ i : Fin 3, MemLp (kinFTMomFun g i) 1 :=
    fun i => (hcont i).memLp_of_hasCompactSupport (hcs i) (p := 1)
  have hmem2 : ∀ i : Fin 3, MemLp (kinFTMomFun g i) 2 :=
    fun i => (hcont i).memLp_of_hasCompactSupport (hcs i) (p := 2)
  -- the derivative identity, per coordinate
  have hderiv : ∀ (p : E3) (i : Fin 3),
      fderiv ℝ (fun q : E3 => Submission.BoseGases.kinFT g q) p
          (EuclideanSpace.single i (1 : ℝ))
        = Submission.BoseGases.kinFT (kinFTMomFun g i) p :=
    fun p i => kinFT_fderiv_dir hg hgc p _
  -- integrability of the momentum-side integrands
  have hIntKin : ∀ i : Fin 3,
      Integrable (fun p : E3 => ‖Submission.BoseGases.kinFT (kinFTMomFun g i) p‖ ^ 2) :=
    fun i => (Work.BoseKinLoc.Kinetic.kinFT_sq_of_memLp (hmem1 i) (hmem2 i)).1
  -- Plancherel, solved for the unnormalised momentum integral
  have hplanch : ∀ i : Fin 3,
      (∫ p : E3, ‖Submission.BoseGases.kinFT (kinFTMomFun g i) p‖ ^ 2)
        = (2 * Real.pi) ^ 3 * ∫ x : E3, ‖kinFTMomFun g i x‖ ^ 2 := by
    intro i
    have hne : ((2 * Real.pi) ^ 3 : ℝ) ≠ 0 := by positivity
    have h := (Work.BoseKinLoc.Kinetic.kinFT_sq_of_memLp (hmem1 i) (hmem2 i)).2
    calc (∫ p : E3, ‖Submission.BoseGases.kinFT (kinFTMomFun g i) p‖ ^ 2)
        = (2 * Real.pi) ^ 3 *
            (((2 * Real.pi) ^ 3)⁻¹ *
              ∫ p : E3, ‖Submission.BoseGases.kinFT (kinFTMomFun g i) p‖ ^ 2) := by
          rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
      _ = (2 * Real.pi) ^ 3 * ∫ x : E3, ‖kinFTMomFun g i x‖ ^ 2 := by rw [h]
  -- integrability of the position-side integrands
  have hIntNorm : ∀ i : Fin 3, Integrable (fun x : E3 => ‖kinFTMomFun g i x‖ ^ 2) := by
    intro i
    have hcs2 : HasCompactSupport (fun x : E3 => ‖kinFTMomFun g i x‖ ^ 2) :=
      (hcs i).comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp)
    exact ((hcont i).norm.pow 2).integrable_of_hasCompactSupport hcs2
  -- the four bookkeeping steps
  have step1 : (∫ p : E3, ∑ i : Fin 3,
        ‖fderiv ℝ (fun q : E3 => Submission.BoseGases.kinFT g q) p
          (EuclideanSpace.single i (1 : ℝ))‖ ^ 2)
      = ∫ p : E3, ∑ i : Fin 3, ‖Submission.BoseGases.kinFT (kinFTMomFun g i) p‖ ^ 2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
    exact Finset.sum_congr rfl (fun i _ => by rw [hderiv p i])
  have step2 : (∫ p : E3, ∑ i : Fin 3, ‖Submission.BoseGases.kinFT (kinFTMomFun g i) p‖ ^ 2)
      = ∑ i : Fin 3, ∫ p : E3, ‖Submission.BoseGases.kinFT (kinFTMomFun g i) p‖ ^ 2 := by
    simpa using integral_finsetSum (Finset.univ : Finset (Fin 3))
      (f := fun i (p : E3) => ‖Submission.BoseGases.kinFT (kinFTMomFun g i) p‖ ^ 2)
      (fun i _ => hIntKin i)
  have step3 : (∫ x : E3, ∑ i : Fin 3, ‖kinFTMomFun g i x‖ ^ 2)
      = ∑ i : Fin 3, ∫ x : E3, ‖kinFTMomFun g i x‖ ^ 2 := by
    simpa using integral_finsetSum (Finset.univ : Finset (Fin 3))
      (f := fun i (x : E3) => ‖kinFTMomFun g i x‖ ^ 2) (fun i _ => hIntNorm i)
  have step4 : (∫ x : E3, ∑ i : Fin 3, ‖kinFTMomFun g i x‖ ^ 2)
      = ∫ x : E3, ‖x‖ ^ 2 * ‖g x‖ ^ 2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    exact sum_norm_kinFTMomFun_sq g x
  calc (∫ p : E3, ∑ i : Fin 3,
        ‖fderiv ℝ (fun q : E3 => Submission.BoseGases.kinFT g q) p
          (EuclideanSpace.single i (1 : ℝ))‖ ^ 2)
      = ∫ p : E3, ∑ i : Fin 3, ‖Submission.BoseGases.kinFT (kinFTMomFun g i) p‖ ^ 2 := step1
    _ = ∑ i : Fin 3, ∫ p : E3, ‖Submission.BoseGases.kinFT (kinFTMomFun g i) p‖ ^ 2 := step2
    _ = ∑ i : Fin 3, (2 * Real.pi) ^ 3 * ∫ x : E3, ‖kinFTMomFun g i x‖ ^ 2 :=
          Finset.sum_congr rfl (fun i _ => hplanch i)
    _ = (2 * Real.pi) ^ 3 * ∑ i : Fin 3, ∫ x : E3, ‖kinFTMomFun g i x‖ ^ 2 := by
          rw [Finset.mul_sum]
    _ = (2 * Real.pi) ^ 3 * ∫ x : E3, ∑ i : Fin 3, ‖kinFTMomFun g i x‖ ^ 2 := by rw [step3]
    _ = (2 * Real.pi) ^ 3 * ∫ x : E3, ‖x‖ ^ 2 * ‖g x‖ ^ 2 := by rw [step4]

end Work.BoseBoxFock
