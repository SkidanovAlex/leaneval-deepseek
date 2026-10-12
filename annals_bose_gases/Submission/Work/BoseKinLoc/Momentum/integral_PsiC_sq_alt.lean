import Mathlib.Tactic.Have
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.BoseKinLoc.Momentum.boxFTfun_kinFT
import Submission.Work.BoseKinLoc.Momentum.integrable_PsiC
import Submission.Work.BoseKinLoc.Momentum.integrable_norm_sq_PsiC
import Submission.Work.BoseKinLoc.Momentum.kinFT_l1l2_plancherel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Momentum.integral_PsiC_sq_alt` — FS `eq:Q1Qslide`, the `L²` mass of `PsiC`

Plancherel identity for the mean-free localised state

  `PsiC ℓ p ψ = boxFTfun ℓ p ψ − boxMeanR ℓ ψ · boxHat ℓ p`  (`momDefs`):

  `∫_x ‖PsiC ℓ p ψ x‖² dx = (2π)⁻³ ∫_q ‖fhat ψ q‖² Bh(ℓ,q,p)² dq`

where `Bh ℓ q p = boxHat ℓ (q−p) − ℓ⁻³ boxHat ℓ p · boxHat ℓ q`.

The proof is the two-step computation announced in the port note below: the pointwise
transform identity `kinFT (PsiC ℓ p ψ) q = fhat ψ q · Bh ℓ q p` (splitting off the box
mean, `boxFTfun_kinFT` + `boxMeanR_eq`), then `kinFT_l1l2_plancherel` applied to
`integrable_PsiC` and `MemLp`-`2` of `PsiC` (from `integrable_norm_sq_PsiC` via
`memLp_two_iff_integrable_sq_norm`).

The local helpers are `private` so that this file can be imported freely alongside the
other `*_alt` ports of `MomForM_u_integral`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.Momentum

open Submission.BoseGases

set_option linter.unusedVariables false

/-- `boxMeanR ℓ ψ` is the `p = 0` `boxFTfun` rescaled: `boxMeanR = ℓ⁻³ boxFTfun ℓ 0 ψ`. -/
private lemma boxMeanR_eq_alt (ℓ : ℝ) (ψ : ℝ³ → ℝ) (x : ℝ³) :
    (boxMeanR ℓ ψ x : ℂ) = (ℓ ^ 3)⁻¹ * boxFTfun ℓ 0 ψ x := by
  have hJ : (∫ z in acube ℓ, (ψ (x + z) : ℂ)) = ((∫ z in acube ℓ, ψ (x + z) : ℝ) : ℂ) :=
    integral_ofReal
  unfold boxMeanR boxFTfun
  rw [show (fun z : ℝ³ => Complex.exp (-(Complex.I * (inner ℝ (0:ℝ³) z : ℂ))) * (ψ (x + z) : ℂ))
      = fun z : ℝ³ => (ψ (x + z) : ℂ) from by
    funext z; simp]
  rw [hJ]
  push_cast
  ring

/-- The `q`-mode integrand `e^{-i⟪q,·⟫} boxFTfun ℓ p ψ` is integrable: it is dominated by
`‖boxFTfun ℓ p ψ‖`, which is integrable (`integrable_boxFTfun`). -/
private lemma integrable_exp_mul_boxFTfun_alt (ℓ : ℝ) (hℓ : 0 < ℓ) (k p : ℝ³) (ψ : ℝ³ → ℝ)
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    Integrable (fun x : ℝ³ => Complex.exp (-(Complex.I * (inner ℝ k x : ℂ))) * boxFTfun ℓ p ψ x) := by
  refine Integrable.mono' (g := fun x : ℝ³ => ‖boxFTfun ℓ p ψ x‖)
    ((integrable_boxFTfun hℓ p ψ hψ hcs).norm) ?_ ?_
  · exact ((Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable).mul
      (integrable_boxFTfun hℓ p ψ hψ hcs).aestronglyMeasurable
  · filter_upwards with x
    rw [norm_mul,
      show (-(Complex.I * (inner ℝ k x : ℂ))) = ((-(inner ℝ k x) : ℝ) : ℂ) * Complex.I from by
        push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, one_mul]

/-- **The `q`-Fourier transform of `PsiC`**: `kinFT (PsiC ℓ p ψ) q = fhat ψ q · Bh(ℓ,q,p)`.

This is `kinFT` of `boxFTfun ℓ p ψ − ℓ⁻³ boxHat ℓ p · boxFTfun ℓ 0 ψ` (the definition of
`PsiC` combined with `boxMeanR_eq_alt`), evaluated with `boxFTfun_kinFT`. -/
private theorem kinFT_PsiC_alt_local (ℓ : ℝ) (hℓ : 0 < ℓ) (p : ℝ³) (ψ : ℝ³ → ℝ)
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) (q : ℝ³) :
    kinFT (PsiC ℓ p ψ) q = fhat ψ q * (Bh ℓ q p : ℂ) := by
  have hsplit : PsiC ℓ p ψ
      = boxFTfun ℓ p ψ - ((ℓ ^ 3)⁻¹ * (Work.OneBodyKin.boxHat ℓ p : ℂ)) • boxFTfun ℓ 0 ψ := by
    funext x
    rw [show PsiC ℓ p ψ x = boxFTfun ℓ p ψ x
        - (boxMeanR ℓ ψ x : ℂ) * (Work.OneBodyKin.boxHat ℓ p : ℂ) from rfl, boxMeanR_eq_alt ℓ ψ x]
    rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hI1 := integrable_exp_mul_boxFTfun_alt ℓ hℓ q p ψ hψ hcs
  have hI2 := (integrable_exp_mul_boxFTfun_alt ℓ hℓ q 0 ψ hψ hcs).const_mul
    ((ℓ ^ 3)⁻¹ * (Work.OneBodyKin.boxHat ℓ p : ℂ))
  have hfun : (fun y : ℝ³ => Complex.exp (-(Complex.I * (inner ℝ q y : ℂ))) *
        (boxFTfun ℓ p ψ - ((ℓ ^ 3)⁻¹ * (Work.OneBodyKin.boxHat ℓ p : ℂ)) • boxFTfun ℓ 0 ψ) y)
      = fun y => Complex.exp (-(Complex.I * (inner ℝ q y : ℂ))) * boxFTfun ℓ p ψ y
          - ((ℓ ^ 3)⁻¹ * (Work.OneBodyKin.boxHat ℓ p : ℂ))
            * (Complex.exp (-(Complex.I * (inner ℝ q y : ℂ))) * boxFTfun ℓ 0 ψ y) := by
    funext y
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hsplit, kinFT, hfun]
  rw [MeasureTheory.integral_sub hI1 hI2, MeasureTheory.integral_const_mul]
  rw [show (∫ x : ℝ³, Complex.exp (-(Complex.I * (inner ℝ q x : ℂ))) * boxFTfun ℓ p ψ x)
      = kinFT (boxFTfun ℓ p ψ) q from rfl]
  rw [show (∫ x : ℝ³, Complex.exp (-(Complex.I * (inner ℝ q x : ℂ))) * boxFTfun ℓ 0 ψ x)
      = kinFT (boxFTfun ℓ 0 ψ) q from rfl]
  rw [boxFTfun_kinFT ℓ p ψ hψ hcs, boxFTfun_kinFT ℓ 0 ψ hψ hcs]
  simp only [sub_zero]
  unfold Bh
  push_cast
  ring

/-- `PsiC ℓ p ψ ∈ L²`: it is `L¹` (`integrable_PsiC`) and its square modulus is integrable
(`integrable_norm_sq_PsiC`). -/
private lemma memLp_PsiC_local (ℓ : ℝ) (p : ℝ³) (ψ : ℝ³ → ℝ)
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    MemLp (PsiC ℓ p ψ) 2 (volume : Measure ℝ³) :=
  (memLp_two_iff_integrable_sq_norm (integrable_PsiC ℓ p ψ hψ hcs).aestronglyMeasurable).2
    (integrable_norm_sq_PsiC ℓ p ψ hψ hcs)

-- Port of `integral_PsiC_sq` (FS eq:Q1Qslide).  A complete proof (same statement, name
-- `integral_PsiC_sq`) is in `Submission/Work/BoseKinLoc/Momentum/_scratch.lean`; do NOT import
-- that scratch file, copy the proof here.  It goes through the pointwise identity
-- `kinFT (PsiC ℓ p ψ) q = fhat ψ q · Bh ℓ q p` (proved by splitting off the box mean, using
-- `boxFTfun_kinFT`, `boxMeanR_eq` and `integral_exp_acube`) and then `kinFT_l1l2_plancherel`
-- with `integrable_PsiC` and `integrable_norm_sq_PsiC` (`memLp` from
-- `memLp_two_iff_integrable_sq_norm`).
theorem integral_PsiC_sq_alt (ℓ : ℝ) (hℓ : 0 < ℓ) (p : EuclideanSpace ℝ (Fin 3)) (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    ∫ x : EuclideanSpace ℝ (Fin 3), ‖Work.BoseKinLoc.Momentum.PsiC ℓ p ψ x‖ ^ 2 =
      ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : EuclideanSpace ℝ (Fin 3), ‖Work.BoseKinLoc.fhat ψ q‖ ^ 2 * (Work.BoseKinLoc.Momentum.Bh ℓ q p) ^ 2 := by
  have hpl := kinFT_l1l2_plancherel (integrable_PsiC ℓ p ψ hψ hcs)
    (memLp_PsiC_local ℓ p ψ hψ hcs)
  have hcongr : (∫ q : ℝ³, ‖fhat ψ q‖ ^ 2 * (Bh ℓ q p) ^ 2)
      = ∫ q : ℝ³, ‖kinFT (PsiC ℓ p ψ) q‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards with q
    rw [kinFT_PsiC_alt_local ℓ hℓ p ψ hψ hcs q, norm_mul, mul_pow,
      show ‖(((Bh ℓ q p : ℝ)) : ℂ)‖ ^ 2 = (Bh ℓ q p) ^ 2 from by
        rw [Complex.sq_norm, Complex.normSq_ofReal, pow_two]]
  rw [hcongr, hpl]
  have h2pi : (2 * Real.pi : ℝ) ^ 3 ≠ 0 := pow_ne_zero 3 (by positivity)
  rw [← mul_assoc, inv_mul_cancel₀ h2pi, one_mul]

end Work.BoseKinLoc.Momentum
