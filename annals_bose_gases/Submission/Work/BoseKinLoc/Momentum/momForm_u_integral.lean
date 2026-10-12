import Mathlib.Tactic.Have
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Fourier.Notation
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Submission.Work.BoseKinLoc.Momentum.aestronglyMeasurable_momForm
import Submission.Work.BoseKinLoc.Momentum.aestronglyMeasurable_momForm_joint
import Submission.Work.BoseKinLoc.Momentum.boxFTfun_kinFT
import Submission.Work.BoseKinLoc.Momentum.integrable_PsiC
import Submission.Work.BoseKinLoc.Momentum.integrable_fhat_Bh
import Submission.Work.BoseKinLoc.Momentum.integrable_momProj_Bh
import Submission.Work.BoseKinLoc.Momentum.integrable_norm_sq_PsiC
import Submission.Work.BoseKinLoc.Momentum.integral_momProj_Bh
import Submission.Work.BoseKinLoc.Momentum.kinFT_l1l2_plancherel
import Submission.Work.BoseKinLoc.Momentum.memLp_kinFT
import Submission.Work.BoseKinLoc.Momentum.setIntegral_bsBox
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Momentum.momForm_u_integral` — FS `eq:Q1Qslide`, the exact `u`-average

The precise `u`-average of the sliding mean-free box family

  `momForm ℓ d u ψ = (2π)⁻³ ∫_p momProj ℓ d p · ‖kinFT (1_{Λ(u)}(ψ − m_u)) p‖²`

(supported in the box `Λ(u) = ℓu + acube ℓ`, `m_u` the box mean) is the Fourier-diagonal form

  `∫_u momForm ℓ d u ψ
     = (2π)⁻³ ∫_s ‖fhat ψ s‖² · ((2π)⁻³ ∫_{‖w‖ > (d²)⁻¹}
          (cubFT (w − ℓ•s) − cubFT (ℓ•s) cubFT w)² dw) ds`.

## Proof

Write `Ψ(p, x) = boxFTfun ℓ p ψ x − boxMeanR ℓ ψ x · boxHat ℓ p` (`momDefs`), so that
`kinFT (statU ℓ u ψ) p = e^{−iℓ⟪p,u⟫} Ψ(p, ℓu)` (`kinFT_statU`), and `kinFT (Ψ(p,·)) q =
fhat ψ q · Bh ℓ q p` (`kinFT_PsiC`).  Plancherel (`kinFT_l1l2_plancherel`) for `Ψ(p,·)` gives the
`u`-average (`integral_u_statU_sq`, `integral_PsiC_sq`), and the `p`-average of `Bh²` is computed
by the dilation `boxHat ℓ x = ℓ³ cubFT (ℓx)` (`integral_momProj_Bh`).  The two changes of order
of integration are Tonelli for the nonnegative integrands, with the joint measurabilities
`aestronglyMeasurable_momForm_joint` and `aestronglyMeasurable_pq_joint`.

Everything is done at the level of `ℝ≥0∞`-valued integrals (`lintegral`) and converted back at the
end, so no joint integrability hypothesis is needed.
-/

noncomputable section
open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal FourierTransform Pointwise

namespace Work.BoseKinLoc.Momentum
open Submission.BoseGases

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

lemma measurableSet_bsBox (ℓ : ℝ) (u : ℝ³) : MeasurableSet (Work.BSKinetic.bsBox ℓ u) := by
  have h : Work.BSKinetic.bsBox ℓ u = (fun x : ℝ³ => x - ℓ • u) ⁻¹' acube ℓ := rfl
  rw [h]
  exact (acube_measurable ℓ).preimage (by fun_prop)

lemma setIntegral_eq_indicator {s : Set ℝ³} (hs : MeasurableSet s) (f : ℝ³ → ℂ) :
    (∫ x in s, f x) = ∫ x, s.indicator f x := (MeasureTheory.integral_indicator hs).symm

lemma setIntegral_sub' {s : Set ℝ³} (hs : MeasurableSet s) {f g : ℝ³ → ℂ}
    (hf : IntegrableOn f s) (hg : IntegrableOn g s) :
    (∫ x in s, (f x - g x)) = (∫ x in s, f x) - ∫ x in s, g x := by
  rw [setIntegral_eq_indicator hs f, setIntegral_eq_indicator hs g,
    setIntegral_eq_indicator hs (fun x => f x - g x)]
  rw [← MeasureTheory.integral_sub ((MeasureTheory.integrable_indicator_iff hs).mpr hf)
    ((MeasureTheory.integrable_indicator_iff hs).mpr hg)]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ s
  · simp only [Set.indicator_of_mem hx]
  · simp only [Set.indicator_of_notMem hx, sub_self]

lemma setIntegral_const_mul' (s : Set ℝ³) (c : ℂ) (f : ℝ³ → ℂ) :
    (∫ x in s, c * f x) = c * ∫ x in s, f x :=
  MeasureTheory.integral_const_mul c f

lemma setIntegral_mul_const' (s : Set ℝ³) (c : ℂ) (f : ℝ³ → ℂ) :
    (∫ x in s, f x * c) = (∫ x in s, f x) * c :=
  MeasureTheory.integral_mul_const c f

lemma continuous_cubFT : Continuous cubFT := by
  have hcont : Continuous
      (fun q : ℝ³ => (kinFT (fun z : ℝ³ => (Work.OneBodyKin.bsMeanBoxInd 1 z : ℂ)) q).re) :=
    Complex.continuous_re.comp
      (continuous_kinFT_of_integrable
        (Complex.ofRealCLM.integrable_comp (Work.OneBodyKin.integrable_bsMeanBoxInd 1)))
  have hfun : (fun q : ℝ³ => (kinFT (fun z : ℝ³ => (Work.OneBodyKin.bsMeanBoxInd 1 z : ℂ)) q).re)
      = cubFT := by
    funext q
    rw [Work.OneBodyKin.kinFT_bsMeanBoxInd]
    simp [cubFT, Work.OneBodyKin.boxHat]
  rwa [hfun] at hcont

lemma boxMeanR_eq (ℓ : ℝ) (ψ : ℝ³ → ℝ) (x : ℝ³) :
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

lemma hphase (ℓ : ℝ) (u p : ℝ³) (z : ℝ³) :
    Complex.exp (-(Complex.I * (inner ℝ p (ℓ • u + z) : ℂ)))
      = Complex.exp (-(Complex.I * ((ℓ * inner ℝ p u : ℝ) : ℂ)))
          * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) := by
  rw [← Complex.exp_add]
  congr 1
  rw [inner_add_right, inner_smul_right]
  push_cast
  ring

lemma kinFT_indU (ℓ : ℝ) (u : ℝ³) (p : ℝ³) :
    kinFT (fun x => (indU ℓ u x : ℂ)) p
      = Complex.exp (-(Complex.I * ((ℓ * inner ℝ p u : ℝ) : ℂ)))
          * (Work.OneBodyKin.boxHat ℓ p : ℂ) := by
  have hs : MeasurableSet (Work.BSKinetic.bsBox ℓ u) := measurableSet_bsBox ℓ u
  have hred : kinFT (fun x => (indU ℓ u x : ℂ)) p
      = ∫ x in Work.BSKinetic.bsBox ℓ u, Complex.exp (-(Complex.I * (inner ℝ p x : ℂ))) := by
    rw [kinFT]
    rw [show (fun x : ℝ³ => Complex.exp (-(Complex.I * (inner ℝ p x : ℂ))) * (indU ℓ u x : ℂ))
        = (Work.BSKinetic.bsBox ℓ u).indicator
            (fun x => Complex.exp (-(Complex.I * (inner ℝ p x : ℂ)))) from by
      funext x
      simp only [Work.BoseKinLoc.indU, Work.BoseKinLoc.lamBox]
      by_cases hx : x ∈ Work.BSKinetic.bsBox ℓ u
      · simp only [Set.indicator_of_mem hx]; simp
      · simp only [Set.indicator_of_notMem hx]; simp]
    rw [MeasureTheory.integral_indicator hs]
  rw [hred, setIntegral_bsBox]
  rw [show (∫ z in acube ℓ, Complex.exp (-(Complex.I * (inner ℝ p (ℓ • u + z) : ℂ))))
      = ∫ z in acube ℓ, Complex.exp (-(Complex.I * ((ℓ * inner ℝ p u : ℝ) : ℂ)))
          * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) from by
    apply MeasureTheory.setIntegral_congr_fun (acube_measurable ℓ)
    intro z _
    exact hphase ℓ u p z]
  rw [setIntegral_const_mul']
  rw [integral_exp_acube]

lemma kinFT_indU_mul (ℓ : ℝ) (u : ℝ³) (ψ : ℝ³ → ℝ) (p : ℝ³) :
    kinFT (fun x => (indU ℓ u x : ℂ) * (ψ x : ℂ)) p
      = Complex.exp (-(Complex.I * ((ℓ * inner ℝ p u : ℝ) : ℂ))) * boxFTfun ℓ p ψ (ℓ • u) := by
  have hs : MeasurableSet (Work.BSKinetic.bsBox ℓ u) := measurableSet_bsBox ℓ u
  have hred : kinFT (fun x => (indU ℓ u x : ℂ) * (ψ x : ℂ)) p
      = ∫ x in Work.BSKinetic.bsBox ℓ u,
          Complex.exp (-(Complex.I * (inner ℝ p x : ℂ))) * (ψ x : ℂ) := by
    rw [kinFT]
    rw [show (fun x : ℝ³ => Complex.exp (-(Complex.I * (inner ℝ p x : ℂ))) * ((indU ℓ u x : ℂ) * (ψ x : ℂ)))
        = (Work.BSKinetic.bsBox ℓ u).indicator
            (fun x => Complex.exp (-(Complex.I * (inner ℝ p x : ℂ))) * (ψ x : ℂ)) from by
      funext x
      simp only [Work.BoseKinLoc.indU, Work.BoseKinLoc.lamBox]
      by_cases hx : x ∈ Work.BSKinetic.bsBox ℓ u
      · simp only [Set.indicator_of_mem hx]; simp
      · simp only [Set.indicator_of_notMem hx]; simp]
    rw [MeasureTheory.integral_indicator hs]
  rw [hred, setIntegral_bsBox]
  rw [show (∫ z in acube ℓ, Complex.exp (-(Complex.I * (inner ℝ p (ℓ • u + z) : ℂ))) * (ψ (ℓ • u + z) : ℂ))
      = ∫ z in acube ℓ, Complex.exp (-(Complex.I * ((ℓ * inner ℝ p u : ℝ) : ℂ)))
          * (Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * (ψ (ℓ • u + z) : ℂ)) from by
    apply MeasureTheory.setIntegral_congr_fun (acube_measurable ℓ)
    intro z _
    dsimp only
    rw [hphase ℓ u p z]; ring]
  rw [setIntegral_const_mul']
  rfl

lemma boxFTfun_eq_integral (ℓ : ℝ) (p : ℝ³) (ψ : ℝ³ → ℝ) (u : ℝ³) :
    boxFTfun ℓ p ψ (ℓ • u)
      = ∫ z in acube ℓ, Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * (ψ (ℓ • u + z) : ℂ) := rfl

lemma kinFT_statU (ℓ : ℝ) (hℓ : 0 < ℓ) (u : ℝ³) (ψ : ℝ³ → ℝ)
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (p : ℝ³) :
    kinFT (statU ℓ u ψ) p
      = Complex.exp (-(Complex.I * ((ℓ * inner ℝ p u : ℝ) : ℂ))) * PsiC ℓ p ψ (ℓ • u) := by
  set m : ℝ := Work.BSKinetic.bsMean ℓ u ψ with hm
  have hψc : Continuous ψ := hψ.continuous
  have hcont1 : Continuous (fun z : ℝ³ =>
      Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * (ψ (ℓ • u + z) : ℂ)) := by fun_prop
  have hcont2 : Continuous (fun z : ℝ³ =>
      Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * (m : ℂ)) := by fun_prop
  have hs : MeasurableSet (Work.BSKinetic.bsBox ℓ u) := measurableSet_bsBox ℓ u
  have hred : kinFT (statU ℓ u ψ) p
      = ∫ x in Work.BSKinetic.bsBox ℓ u,
          Complex.exp (-(Complex.I * (inner ℝ p x : ℂ))) * ((ψ x - m : ℝ) : ℂ) := by
    rw [kinFT]
    rw [show (fun x : ℝ³ => Complex.exp (-(Complex.I * (inner ℝ p x : ℂ))) * statU ℓ u ψ x)
        = (Work.BSKinetic.bsBox ℓ u).indicator
            (fun x => Complex.exp (-(Complex.I * (inner ℝ p x : ℂ))) * ((ψ x - m : ℝ) : ℂ)) from by
      funext x
      simp only [statU, Work.BoseKinLoc.indU, Work.BoseKinLoc.lamBox, Work.BoseKinLoc.Qfree,
        Work.BSKinetic.bsQ]
      by_cases hx : x ∈ Work.BSKinetic.bsBox ℓ u
      · simp only [Set.indicator_of_mem hx]; push_cast; ring
      · simp only [Set.indicator_of_notMem hx]; simp]
    rw [MeasureTheory.integral_indicator hs]
  rw [hred, setIntegral_bsBox]
  rw [show (∫ z in acube ℓ, Complex.exp (-(Complex.I * (inner ℝ p (ℓ • u + z) : ℂ))) * ((ψ (ℓ • u + z) - m : ℝ) : ℂ))
      = ∫ z in acube ℓ, Complex.exp (-(Complex.I * ((ℓ * inner ℝ p u : ℝ) : ℂ)))
          * (Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * ((ψ (ℓ • u + z) - m : ℝ) : ℂ)) from by
    apply MeasureTheory.setIntegral_congr_fun (acube_measurable ℓ)
    intro z _
    dsimp only
    rw [hphase ℓ u p z]; ring]
  rw [setIntegral_const_mul']
  rw [show (fun z : ℝ³ => Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * ((ψ (ℓ • u + z) - m : ℝ) : ℂ))
      = fun z => Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * (ψ (ℓ • u + z) : ℂ)
          - Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * (m : ℂ) from by
    funext z; push_cast; ring]
  rw [setIntegral_sub' (acube_measurable ℓ)
    (ContinuousOn.integrableOn_compact (acube_compact hℓ) hcont1.continuousOn)
    (ContinuousOn.integrableOn_compact (acube_compact hℓ) hcont2.continuousOn)]
  rw [setIntegral_mul_const', integral_exp_acube]
  rw [show (m : ℂ) = (boxMeanR ℓ ψ (ℓ • u) : ℂ) from by rw [hm]; rfl]
  rw [PsiC, boxFTfun_eq_integral]
  ring

lemma integral_u_statU_sq (ℓ : ℝ) (hℓ : 0 < ℓ) (p : ℝ³) (ψ : ℝ³ → ℝ)
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) :
    ∫ u : ℝ³, ‖kinFT (statU ℓ u ψ) p‖ ^ 2
      = (ℓ ^ 3)⁻¹ * ∫ x : ℝ³, ‖PsiC ℓ p ψ x‖ ^ 2 := by
  have hpt : ∀ u : ℝ³, ‖kinFT (statU ℓ u ψ) p‖ ^ 2 = ‖PsiC ℓ p ψ (ℓ • u)‖ ^ 2 := by
    intro u
    rw [kinFT_statU ℓ hℓ u ψ hψ p, norm_mul,
      show Complex.exp (-(Complex.I * ((ℓ * inner ℝ p u : ℝ) : ℂ)))
          = Complex.exp (((-(ℓ * inner ℝ p u) : ℝ) : ℂ) * Complex.I) from by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, one_mul]
  rw [show (∫ u : ℝ³, ‖kinFT (statU ℓ u ψ) p‖ ^ 2)
      = ∫ u : ℝ³, (fun x : ℝ³ => ‖PsiC ℓ p ψ x‖ ^ 2) (ℓ • u) from by
    apply integral_congr_ae; filter_upwards with u; exact hpt u]
  rw [MeasureTheory.Measure.integral_comp_smul_of_nonneg volume
    (fun x : ℝ³ => ‖PsiC ℓ p ψ x‖ ^ 2) ℓ (hR := hℓ.le)]
  rw [show Module.finrank ℝ ℝ³ = 3 from by simp [EuclideanSpace], smul_eq_mul]


lemma acube_subset_acube_abs (ℓ : ℝ) : acube ℓ ⊆ acube (2 * |ℓ| + 2) := by
  intro z hz m
  have hm := hz m
  rw [Set.mem_Icc] at hm ⊢
  constructor <;> linarith [abs_nonneg ℓ, neg_abs_le ℓ, le_abs_self ℓ, hm.1, hm.2]

lemma hasCompactSupport_boxFTfun (ℓ : ℝ) (p : ℝ³) (ψ : ℝ³ → ℝ) (hcs : HasCompactSupport ψ) :
    HasCompactSupport (boxFTfun ℓ p ψ) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (K := tsupport ψ + acube (2 * |ℓ| + 2))
    (hcs.isCompact.add (acube_compact (by positivity : (0:ℝ) < 2 * |ℓ| + 2))) ?_
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hcon
  apply hx
  have hzero : ∀ z ∈ acube ℓ, ψ (x + z) = 0 := by
    intro z hz
    by_contra hψ
    exact hcon (Set.mem_add.mpr ⟨x + z, subset_tsupport ψ (Function.mem_support.mpr hψ), -z,
      (Work.OneBodyKin.neg_mem_acube_iff (2 * |ℓ| + 2) z).mpr (acube_subset_acube_abs ℓ hz),
      by abel⟩)
  unfold boxFTfun
  rw [show (∫ z in acube ℓ, Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * (ψ (x + z) : ℂ))
      = ∫ z in acube ℓ, (0 : ℂ) from by
    apply MeasureTheory.setIntegral_congr_fun (acube_measurable ℓ)
    intro z hz
    dsimp only
    rw [hzero z hz]; simp]
  simp

lemma hasCompactSupport_boxMeanR (ℓ : ℝ) (ψ : ℝ³ → ℝ) (hcs : HasCompactSupport ψ) :
    HasCompactSupport (boxMeanR ℓ ψ) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (K := tsupport ψ + acube (2 * |ℓ| + 2))
    (hcs.isCompact.add (acube_compact (by positivity : (0:ℝ) < 2 * |ℓ| + 2))) ?_
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hcon
  apply hx
  have hzero : ∀ z ∈ acube ℓ, ψ (x + z) = 0 := by
    intro z hz
    by_contra hψ
    exact hcon (Set.mem_add.mpr ⟨x + z, subset_tsupport ψ (Function.mem_support.mpr hψ), -z,
      (Work.OneBodyKin.neg_mem_acube_iff (2 * |ℓ| + 2) z).mpr (acube_subset_acube_abs ℓ hz),
      by abel⟩)
  unfold boxMeanR
  rw [show (∫ z in acube ℓ, ψ (x + z)) = ∫ z in acube ℓ, (0 : ℝ) from by
    apply MeasureTheory.setIntegral_congr_fun (acube_measurable ℓ)
    intro z hz
    dsimp only
    rw [hzero z hz]]
  simp

lemma continuous_boxFTfun {ℓ : ℝ} (hℓ : 0 < ℓ) (p : ℝ³) (ψ : ℝ³ → ℝ)
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    Continuous (boxFTfun ℓ p ψ) := by
  obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hψ.continuous
  have hmain : Continuous (fun x : ℝ³ => ∫ z : ℝ³, (acube ℓ).indicator
      (fun z => Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * (ψ (x + z) : ℂ)) z) := by
    apply continuous_of_dominated (bound := fun z : ℝ³ => (acube ℓ).indicator (fun _ => C) z)
    · intro x
      exact (((Complex.continuous_exp.comp (by fun_prop)).mul (Complex.continuous_ofReal.comp
        (hψ.continuous.comp (continuous_const.add continuous_id)))).aestronglyMeasurable).indicator
        (acube_measurable ℓ)
    · intro x
      filter_upwards with z
      by_cases hz : z ∈ acube ℓ
      · simp only [Set.indicator_of_mem hz]
        rw [norm_mul,
          show (-(Complex.I * (inner ℝ p z : ℂ))) = ((-(inner ℝ p z) : ℝ) : ℂ) * Complex.I from by
            push_cast; ring,
          Complex.norm_exp_ofReal_mul_I, one_mul]
        simpa using hC (x + z)
      · simp only [Set.indicator_of_notMem hz]; simp
    · rw [MeasureTheory.integrable_indicator_iff (acube_measurable ℓ)]
      exact integrableOn_const (acube_compact hℓ).measure_lt_top.ne (by simp)
    · filter_upwards with z
      by_cases hz : z ∈ acube ℓ
      · simp only [Set.indicator_of_mem hz]
        fun_prop
      · simp only [Set.indicator_of_notMem hz]
        exact continuous_const
  rw [show boxFTfun ℓ p ψ = fun x : ℝ³ => ∫ z : ℝ³, (acube ℓ).indicator
      (fun z => Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * (ψ (x + z) : ℂ)) z from by
    funext x
    rw [boxFTfun, setIntegral_eq_indicator (acube_measurable ℓ)]]
  exact hmain

lemma continuous_boxMeanR {ℓ : ℝ} (hℓ : 0 < ℓ) (ψ : ℝ³ → ℝ)
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    Continuous (boxMeanR ℓ ψ) := by
  obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hψ.continuous
  have hmain : Continuous (fun x : ℝ³ => ∫ z : ℝ³,
      (acube ℓ).indicator (fun z => ψ (x + z)) z) := by
    apply continuous_of_dominated (bound := fun z : ℝ³ => (acube ℓ).indicator (fun _ => C) z)
    · intro x
      exact ((hψ.continuous.comp (continuous_const.add continuous_id)).aestronglyMeasurable).indicator
        (acube_measurable ℓ)
    · intro x
      filter_upwards with z
      by_cases hz : z ∈ acube ℓ
      · simp only [Set.indicator_of_mem hz]
        rw [Real.norm_eq_abs]
        exact hC (x + z)
      · simp only [Set.indicator_of_notMem hz]; simp
    · rw [MeasureTheory.integrable_indicator_iff (acube_measurable ℓ)]
      exact integrableOn_const (acube_compact hℓ).measure_lt_top.ne (by simp)
    · filter_upwards with z
      by_cases hz : z ∈ acube ℓ
      · simp only [Set.indicator_of_mem hz]; fun_prop
      · simp only [Set.indicator_of_notMem hz]; exact continuous_const
  have hfun : boxMeanR ℓ ψ = fun x : ℝ³ => (ℓ ^ 3)⁻¹ * ∫ z : ℝ³,
      (acube ℓ).indicator (fun z => ψ (x + z)) z := by
    funext x
    rw [boxMeanR]
    rw [show (∫ z in acube ℓ, ψ (x + z)) = ∫ z, (acube ℓ).indicator (fun z => ψ (x + z)) z from
      (MeasureTheory.integral_indicator (acube_measurable ℓ)).symm]
  rw [hfun]
  exact continuous_const.mul hmain

lemma continuous_PsiC {ℓ : ℝ} (hℓ : 0 < ℓ) (p : ℝ³) (ψ : ℝ³ → ℝ)
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    Continuous (PsiC ℓ p ψ) := by
  have h1 := continuous_boxFTfun hℓ p ψ hψ hcs
  have h2 := continuous_boxMeanR hℓ ψ hψ hcs
  unfold PsiC
  exact h1.sub ((Complex.continuous_ofReal.comp h2).mul continuous_const)

lemma hasCompactSupport_PsiC (ℓ : ℝ) (p : ℝ³) (ψ : ℝ³ → ℝ) (hcs : HasCompactSupport ψ) :
    HasCompactSupport (PsiC ℓ p ψ) := by
  unfold PsiC
  refine (hasCompactSupport_boxFTfun ℓ p ψ hcs).sub ?_
  exact ((hasCompactSupport_boxMeanR ℓ ψ hcs).comp_left (g := fun r : ℝ => (r : ℂ))
    (by simp)).mul_right

lemma memLp_PsiC_self (ℓ : ℝ) (hℓ : 0 < ℓ) (p : ℝ³) (ψ : ℝ³ → ℝ)
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    MemLp (PsiC ℓ p ψ) 2 (volume : Measure ℝ³) :=
  (memLp_two_iff_integrable_sq_norm (continuous_PsiC hℓ p ψ hψ hcs).aestronglyMeasurable).2
    (integrable_norm_sq_PsiC ℓ p ψ hψ hcs)

lemma integrable_statU_sq (ℓ : ℝ) (hℓ : 0 < ℓ) (p : ℝ³) (ψ : ℝ³ → ℝ)
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    Integrable (fun u : ℝ³ => ‖kinFT (statU ℓ u ψ) p‖ ^ 2) := by
  have hpt : (fun u : ℝ³ => ‖kinFT (statU ℓ u ψ) p‖ ^ 2)
      = fun u : ℝ³ => ‖PsiC ℓ p ψ (ℓ • u)‖ ^ 2 := by
    funext u
    rw [kinFT_statU ℓ hℓ u ψ hψ p, norm_mul,
      show Complex.exp (-(Complex.I * ((ℓ * inner ℝ p u : ℝ) : ℂ)))
          = Complex.exp (((-(ℓ * inner ℝ p u) : ℝ) : ℂ) * Complex.I) from by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, one_mul]
  rw [hpt]
  exact (integrable_norm_sq_PsiC ℓ p ψ hψ hcs).comp_smul (ne_of_gt hℓ)

lemma integrable_exp_mul_boxFTfun (ℓ : ℝ) (hℓ : 0 < ℓ) (k p : ℝ³) (ψ : ℝ³ → ℝ)
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    Integrable (fun x : ℝ³ => Complex.exp (-(Complex.I * (inner ℝ k x : ℂ))) * boxFTfun ℓ p ψ x) := by
  refine Integrable.mono' ((integrable_boxFTfun hℓ p ψ hψ hcs).norm) ?_ ?_
  · exact ((Complex.continuous_exp.comp (by fun_prop)).mul
      (continuous_boxFTfun hℓ p ψ hψ hcs)).aestronglyMeasurable
  · filter_upwards with x
    rw [norm_mul,
      show (-(Complex.I * (inner ℝ k x : ℂ))) = ((-(inner ℝ k x) : ℝ) : ℂ) * Complex.I from by
        push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, one_mul]

lemma kinFT_PsiC (ℓ : ℝ) (hℓ : 0 < ℓ) (p : ℝ³) (ψ : ℝ³ → ℝ)
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) (q : ℝ³) :
    kinFT (PsiC ℓ p ψ) q = fhat ψ q * (Bh ℓ q p : ℂ) := by
  have hsplit : PsiC ℓ p ψ
      = boxFTfun ℓ p ψ - ((ℓ ^ 3)⁻¹ * (Work.OneBodyKin.boxHat ℓ p : ℂ)) • boxFTfun ℓ 0 ψ := by
    funext x
    rw [show PsiC ℓ p ψ x = boxFTfun ℓ p ψ x
        - (boxMeanR ℓ ψ x : ℂ) * (Work.OneBodyKin.boxHat ℓ p : ℂ) from rfl, boxMeanR_eq]
    rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hI1 := integrable_exp_mul_boxFTfun ℓ hℓ q p ψ hψ hcs
  have hI2 := (integrable_exp_mul_boxFTfun ℓ hℓ q 0 ψ hψ hcs).const_mul
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

lemma integral_PsiC_sq (ℓ : ℝ) (hℓ : 0 < ℓ) (p : ℝ³) (ψ : ℝ³ → ℝ)
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    ∫ x : ℝ³, ‖PsiC ℓ p ψ x‖ ^ 2
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : ℝ³, ‖fhat ψ q‖ ^ 2 * (Bh ℓ q p) ^ 2 := by
  have hpl := kinFT_l1l2_plancherel (integrable_PsiC ℓ p ψ hψ hcs)
    (memLp_PsiC_self ℓ hℓ p ψ hψ hcs)
  have hcongr : (∫ q : ℝ³, ‖fhat ψ q‖ ^ 2 * (Bh ℓ q p) ^ 2)
      = ∫ q : ℝ³, ‖kinFT (PsiC ℓ p ψ) q‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards with q
    rw [kinFT_PsiC ℓ hℓ p ψ hψ hcs q, norm_mul, mul_pow,
      show ‖(((Bh ℓ q p : ℝ)) : ℂ)‖ ^ 2 = (Bh ℓ q p) ^ 2 from by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal, pow_two]]
  rw [hcongr, hpl]
  have h2pi : (2 * Real.pi : ℝ) ^ 3 ≠ 0 := pow_ne_zero 3 (by positivity)
  field_simp

lemma momProj_nonneg (ℓ d : ℝ) (p : ℝ³) : 0 ≤ momProj ℓ d p := by
  unfold momProj; split <;> norm_num

lemma momProj_le_one (ℓ d : ℝ) (p : ℝ³) : momProj ℓ d p ≤ 1 := by
  unfold momProj; split <;> norm_num

lemma momForm_eq (ℓ d : ℝ) (u : ℝ³) (ψ : ℝ³ → ℝ) :
    momForm ℓ d u ψ
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, momProj ℓ d p * ‖kinFT (statU ℓ u ψ) p‖ ^ 2 := rfl

lemma isCompact_bsBox {ℓ : ℝ} (hℓ : 0 < ℓ) (u : ℝ³) : IsCompact (Work.BSKinetic.bsBox ℓ u) := by
  have h : Work.BSKinetic.bsBox ℓ u = (fun z : ℝ³ => ℓ • u + z) '' acube ℓ := by
    ext x
    simp only [Set.mem_image, Work.BSKinetic.bsBox, Set.mem_setOf_eq]
    constructor
    · intro hx; exact ⟨x - ℓ • u, hx, by abel⟩
    · rintro ⟨z, hz, rfl⟩; simpa using hz
  rw [h]
  exact (acube_compact hℓ).image (continuous_const.add continuous_id)

lemma statU_eq_indicator (ℓ : ℝ) (u : ℝ³) (ψ : ℝ³ → ℝ) :
    statU ℓ u ψ = (Work.BSKinetic.bsBox ℓ u).indicator
      (fun x => ((ψ x - Work.BSKinetic.bsMean ℓ u ψ : ℝ) : ℂ)) := by
  funext x
  simp only [statU, Work.BoseKinLoc.indU, Work.BoseKinLoc.lamBox, Work.BoseKinLoc.Qfree,
    Work.BSKinetic.bsQ, Set.indicator_apply]
  by_cases hx : x ∈ Work.BSKinetic.bsBox ℓ u
  · simp only [Set.indicator_of_mem hx]; push_cast; ring
  · simp only [Set.indicator_of_notMem hx]; simp

lemma integrable_statU (ℓ : ℝ) (hℓ : 0 < ℓ) (u : ℝ³) (ψ : ℝ³ → ℝ)
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) : Integrable (statU ℓ u ψ) := by
  rw [statU_eq_indicator]
  rw [MeasureTheory.integrable_indicator_iff (measurableSet_bsBox ℓ u)]
  have hcont : Continuous (fun x : ℝ³ => ((ψ x - Work.BSKinetic.bsMean ℓ u ψ : ℝ) : ℂ)) := by
    have h1 : Continuous ψ := hψ.continuous
    fun_prop
  exact ContinuousOn.integrableOn_compact (isCompact_bsBox hℓ u) hcont.continuousOn

lemma memLp_statU (ℓ : ℝ) (hℓ : 0 < ℓ) (u : ℝ³) (ψ : ℝ³ → ℝ)
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    MemLp (statU ℓ u ψ) 2 (volume : Measure ℝ³) := by
  refine (memLp_two_iff_integrable_sq_norm ?_).2 ?_
  · rw [statU_eq_indicator]
    have hcont : Continuous (fun x : ℝ³ => ((ψ x - Work.BSKinetic.bsMean ℓ u ψ : ℝ) : ℂ)) := by
      have h1 : Continuous ψ := hψ.continuous
      fun_prop
    exact hcont.aestronglyMeasurable.indicator (measurableSet_bsBox ℓ u)
  · rw [show (fun x : ℝ³ => ‖statU ℓ u ψ x‖ ^ 2)
        = (Work.BSKinetic.bsBox ℓ u).indicator
            (fun x => ‖((ψ x - Work.BSKinetic.bsMean ℓ u ψ : ℝ) : ℂ)‖ ^ 2) from by
      funext x
      rw [statU_eq_indicator]
      by_cases hx : x ∈ Work.BSKinetic.bsBox ℓ u
      · simp only [Set.indicator_of_mem hx]
      · simp only [Set.indicator_of_notMem hx]; simp]
    rw [MeasureTheory.integrable_indicator_iff (measurableSet_bsBox ℓ u)]
    have hcont : Continuous (fun x : ℝ³ => ‖((ψ x - Work.BSKinetic.bsMean ℓ u ψ : ℝ) : ℂ)‖ ^ 2) := by
      have h1 : Continuous ψ := hψ.continuous
      fun_prop
    exact ContinuousOn.integrableOn_compact (isCompact_bsBox hℓ u) hcont.continuousOn

lemma integrable_momProj_kinFT_sq (ℓ d : ℝ) (hℓ : 0 < ℓ) (u : ℝ³) (ψ : ℝ³ → ℝ)
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    Integrable (fun p : ℝ³ => momProj ℓ d p * ‖kinFT (statU ℓ u ψ) p‖ ^ 2) := by
  have hbase : Integrable (fun p : ℝ³ => ‖kinFT (statU ℓ u ψ) p‖ ^ 2) := by
    have h := (memLp_kinFT (integrable_statU ℓ hℓ u ψ hψ hcs) (memLp_statU ℓ hℓ u ψ hψ hcs)
      ).integrable_norm_rpow (by norm_num) (by norm_num)
    simpa [Real.rpow_two] using h
  refine Integrable.mono' hbase ?_ ?_
  · have ha : AEMeasurable (fun p : ℝ³ => momProj ℓ d p) volume := by
      refine Measurable.aemeasurable ?_
      unfold momProj
      exact Measurable.ite (measurableSet_lt measurable_const continuous_norm.measurable)
        measurable_const measurable_const
    have hb : AEMeasurable (fun p : ℝ³ => ‖kinFT (statU ℓ u ψ) p‖ ^ 2) volume :=
      ((continuous_kinFT_of_integrable (integrable_statU ℓ hℓ u ψ hψ hcs)).norm.pow 2).aemeasurable
    exact (ha.mul hb).aestronglyMeasurable
  · filter_upwards with p
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (momProj_nonneg ℓ d p) (sq_nonneg _))]
    exact mul_le_of_le_one_left (sq_nonneg _) (momProj_le_one ℓ d p)

lemma lintegral_const_mul_real (c : ℝ) (f : ℝ³ → ℝ≥0∞) :
    ∫⁻ a : ℝ³, ENNReal.ofReal c * f a = ENNReal.ofReal c * ∫⁻ a : ℝ³, f a :=
  lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

lemma continuous_boxHat (ℓ : ℝ) : Continuous (Work.OneBodyKin.boxHat ℓ) := by
  have hcont : Continuous (fun q : ℝ³ =>
      (kinFT (fun z : ℝ³ => (Work.OneBodyKin.bsMeanBoxInd ℓ z : ℂ)) q).re) :=
    Complex.continuous_re.comp
      (continuous_kinFT_of_integrable
        (Complex.ofRealCLM.integrable_comp (Work.OneBodyKin.integrable_bsMeanBoxInd ℓ)))
  have hfun : (fun q : ℝ³ => (kinFT (fun z : ℝ³ => (Work.OneBodyKin.bsMeanBoxInd ℓ z : ℂ)) q).re)
      = Work.OneBodyKin.boxHat ℓ := by
    funext q
    rw [Work.OneBodyKin.kinFT_bsMeanBoxInd]
    simp
  rwa [hfun] at hcont

lemma continuous_Bh (ℓ : ℝ) : Continuous (fun z : ℝ³ × ℝ³ => Bh ℓ z.1 z.2) := by
  have h1 : Continuous (fun z : ℝ³ × ℝ³ => Work.OneBodyKin.boxHat ℓ (z.1 - z.2)) :=
    (continuous_boxHat ℓ).comp (continuous_fst.sub continuous_snd)
  have h2 : Continuous (fun z : ℝ³ × ℝ³ =>
      (ℓ^3)⁻¹ * Work.OneBodyKin.boxHat ℓ z.2 * Work.OneBodyKin.boxHat ℓ z.1) :=
    ((continuous_const.mul ((continuous_boxHat ℓ).comp continuous_snd)).mul
      ((continuous_boxHat ℓ).comp continuous_fst))
  have h3 := h1.sub h2
  rw [show (fun z : ℝ³ × ℝ³ => Bh ℓ z.1 z.2) = fun z : ℝ³ × ℝ³ =>
      Work.OneBodyKin.boxHat ℓ (z.1 - z.2) - (ℓ^3)⁻¹ * Work.OneBodyKin.boxHat ℓ z.2 * Work.OneBodyKin.boxHat ℓ z.1 from rfl]
  exact h3

lemma msym_nonneg (ℓ d : ℝ) (s : ℝ³) : 0 ≤ msym ℓ d s := by
  unfold msym
  refine mul_nonneg (by positivity) (setIntegral_nonneg ?_ (fun w _ => sq_nonneg _))
  exact measurableSet_lt measurable_const continuous_norm.measurable

lemma aestronglyMeasurable_msym (ℓ d : ℝ) :
    AEStronglyMeasurable (msym ℓ d) (volume : Measure ℝ³) := by
  have h1 : Continuous (fun z : ℝ³ × ℝ³ => cubFT (z.2 - ℓ • z.1)) :=
    continuous_cubFT.comp (by fun_prop : Continuous fun z : ℝ³ × ℝ³ => z.2 - ℓ • z.1)
  have h2 : Continuous (fun z : ℝ³ × ℝ³ => cubFT (ℓ • z.1)) :=
    continuous_cubFT.comp (by fun_prop : Continuous fun z : ℝ³ × ℝ³ => ℓ • z.1)
  have h3 : Continuous (fun z : ℝ³ × ℝ³ => cubFT z.2) := continuous_cubFT.comp continuous_snd
  have hg2 : StronglyMeasurable (fun z : ℝ³ × ℝ³ =>
      (cubFT (z.2 - ℓ • z.1) - cubFT (ℓ • z.1) * cubFT z.2)^2) :=
    ((h1.sub (h2.mul h3)).pow 2).stronglyMeasurable
  have hmeas : StronglyMeasurable (fun s : ℝ³ =>
      ∫ w in {q : ℝ³ | (d^2)⁻¹ < ‖q‖},
        (cubFT (w - ℓ • s) - cubFT (ℓ • s) * cubFT w)^2) :=
    StronglyMeasurable.integral_prod_right'
      (ν := volume.restrict {q : ℝ³ | (d^2)⁻¹ < ‖q‖}) hg2
  rw [show msym ℓ d = fun s : ℝ³ => ((2*Real.pi)^3)⁻¹ *
      ∫ w in {q : ℝ³ | (d^2)⁻¹ < ‖q‖},
        (cubFT (w - ℓ • s) - cubFT (ℓ • s) * cubFT w)^2 from by
    funext s; rw [msym]]
  exact (hmeas.const_mul _).aestronglyMeasurable

lemma int_momProj_Bh_eq_msym (ℓ d : ℝ) (hℓ : 0 < ℓ) (hd : 0 < d) (q : ℝ³) :
    (∫ w in {q' : ℝ³ | (d^2)⁻¹ < ‖q'‖},
        (cubFT (w - ℓ • q) - cubFT (ℓ • q) * cubFT w)^2) = (2*Real.pi)^3 * msym ℓ d q := by
  rw [msym]
  have h : (2*Real.pi)^3 ≠ 0 := pow_ne_zero 3 (by positivity)
  field_simp

lemma aestronglyMeasurable_pq_joint (ℓ d : ℝ) (ψ : ℝ³ → ℝ) (hψ : ContDiff ℝ (⊤:ENat) ψ)
    (hcs : HasCompactSupport ψ) :
    AEMeasurable (fun z : ℝ³ × ℝ³ => ENNReal.ofReal
      (momProj ℓ d z.1 * (‖fhat ψ z.2‖^2 * (Bh ℓ z.2 z.1)^2))) (volume.prod volume) := by
  have hfhat : Continuous (fhat ψ) := continuous_kinFT_of_integrable (integrable_psiCe ψ hψ hcs)
  have hg : Continuous (fun z : ℝ³ × ℝ³ => ‖fhat ψ z.2‖^2 * (Bh ℓ z.2 z.1)^2) :=
    ((continuous_norm.comp (hfhat.comp continuous_snd)).pow 2).mul
      (((continuous_Bh ℓ).comp (continuous_snd.prodMk continuous_fst)).pow 2)
  have hmom : Measurable (fun z : ℝ³ × ℝ³ => momProj ℓ d z.1) := by
    unfold momProj
    exact (Measurable.ite (measurableSet_lt measurable_const continuous_norm.measurable)
      measurable_const measurable_const).comp measurable_fst
  exact ((hmom.mul hg.measurable).aemeasurable).ennreal_ofReal

theorem momForm_u_integral (ψ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ)
    (ℓ d : ℝ) (hℓ : 0 < ℓ) (hd : 0 < d) :
    ∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.momForm ℓ d u ψ =
      ((2 * Real.pi) ^ 3)⁻¹ * ∫ s : EuclideanSpace ℝ (Fin 3), ‖Work.BoseKinLoc.fhat ψ s‖ ^ 2 *
        (((2 * Real.pi) ^ 3)⁻¹ * ∫ w in {q : EuclideanSpace ℝ (Fin 3) | (d ^ 2)⁻¹ < ‖q‖},
          (Work.BoseKinLoc.Momentum.cubFT (w - ℓ • s) -
            Work.BoseKinLoc.Momentum.cubFT (ℓ • s) * Work.BoseKinLoc.Momentum.cubFT w) ^ 2) := by
  show ∫ u : ℝ³, momForm ℓ d u ψ = ((2 * Real.pi) ^ 3)⁻¹ * ∫ s : ℝ³, ‖fhat ψ s‖ ^ 2 * msym ℓ d s
  have hjoint := aestronglyMeasurable_momForm_joint ℓ d ψ hℓ hψ
  have hjointE : AEMeasurable (fun w : ℝ³ × ℝ³ => ENNReal.ofReal
      (momProj ℓ d w.2 * ‖kinFT (statU ℓ w.1 ψ) w.2‖ ^ 2)) (volume.prod volume) :=
    hjoint.aemeasurable.ennreal_ofReal
  have hψint : Integrable (fun z : ℝ³ => (ψ z : ℂ)) := integrable_psiCe ψ hψ hcs
  have hpu : ∀ u : ℝ³, ENNReal.ofReal (momForm ℓ d u ψ)
      = ENNReal.ofReal (((2*Real.pi)^3)⁻¹) * ∫⁻ p : ℝ³,
          ENNReal.ofReal (momProj ℓ d p * ‖kinFT (statU ℓ u ψ) p‖ ^ 2) := by
    intro u
    rw [momForm_eq, ENNReal.ofReal_mul (by positivity)]
    congr 1
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (integrable_momProj_kinFT_sq ℓ d hℓ u ψ hψ hcs)
      (Eventually.of_forall (fun p => mul_nonneg (momProj_nonneg ℓ d p) (sq_nonneg _)))
  have hJu : ∀ p : ℝ³, ∫⁻ u : ℝ³, ENNReal.ofReal (momProj ℓ d p * ‖kinFT (statU ℓ u ψ) p‖ ^ 2)
      = ENNReal.ofReal (momProj ℓ d p * ((ℓ^3)⁻¹ * ((2*Real.pi)^3)⁻¹))
        * ∫⁻ q : ℝ³, ENNReal.ofReal (‖fhat ψ q‖ ^ 2 * (Bh ℓ q p) ^ 2) := by
    intro p
    rw [show (fun u : ℝ³ => ENNReal.ofReal (momProj ℓ d p * ‖kinFT (statU ℓ u ψ) p‖ ^ 2))
        = fun u : ℝ³ => ENNReal.ofReal (momProj ℓ d p)
            * ENNReal.ofReal (‖kinFT (statU ℓ u ψ) p‖ ^ 2) from by
      funext u; rw [ENNReal.ofReal_mul (momProj_nonneg ℓ d p)]]
    rw [lintegral_const_mul_real (momProj ℓ d p)]
    have hstep : ∫⁻ u : ℝ³, ENNReal.ofReal (‖kinFT (statU ℓ u ψ) p‖ ^ 2)
        = ENNReal.ofReal ((ℓ^3)⁻¹ * ((2*Real.pi)^3)⁻¹)
          * ∫⁻ q : ℝ³, ENNReal.ofReal (‖fhat ψ q‖ ^ 2 * (Bh ℓ q p) ^ 2) := by
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
          (integrable_statU_sq ℓ hℓ p ψ hψ hcs) (Eventually.of_forall fun u => sq_nonneg _),
        integral_u_statU_sq ℓ hℓ p ψ hψ, ENNReal.ofReal_mul (by positivity)]
      rw [show ENNReal.ofReal ((ℓ^3)⁻¹ * ((2*Real.pi)^3)⁻¹)
          = ENNReal.ofReal ((ℓ^3)⁻¹) * ENNReal.ofReal (((2*Real.pi)^3)⁻¹) from
        ENNReal.ofReal_mul (by positivity), mul_assoc]
      congr 1
      rw [integral_PsiC_sq ℓ hℓ p ψ hψ hcs, ENNReal.ofReal_mul (by positivity)]
      congr 1
      exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal (integrable_fhat_Bh ℓ p ψ hψ hcs)
        (Eventually.of_forall fun q => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    rw [hstep, ← mul_assoc, ← ENNReal.ofReal_mul (momProj_nonneg ℓ d p)]
  have hq : ∀ q : ℝ³, ∫⁻ p : ℝ³,
        ENNReal.ofReal (momProj ℓ d p * (‖fhat ψ q‖ ^ 2 * (Bh ℓ q p) ^ 2))
      = ENNReal.ofReal (ℓ^3 * (2*Real.pi)^3)
        * ENNReal.ofReal (‖fhat ψ q‖ ^ 2 * msym ℓ d q) := by
    intro q
    rw [show (fun p : ℝ³ => ENNReal.ofReal (momProj ℓ d p * (‖fhat ψ q‖ ^ 2 * (Bh ℓ q p) ^ 2)))
        = fun p : ℝ³ => ENNReal.ofReal (‖fhat ψ q‖ ^ 2)
            * ENNReal.ofReal (momProj ℓ d p * (Bh ℓ q p) ^ 2) from by
      funext p
      rw [show momProj ℓ d p * (‖fhat ψ q‖ ^ 2 * (Bh ℓ q p) ^ 2)
          = ‖fhat ψ q‖ ^ 2 * (momProj ℓ d p * (Bh ℓ q p) ^ 2) from by ring,
        ENNReal.ofReal_mul (sq_nonneg _)]]
    rw [lintegral_const_mul_real (‖fhat ψ q‖ ^ 2)]
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (integrable_momProj_Bh ℓ d hℓ q)
      (Eventually.of_forall fun p => mul_nonneg (momProj_nonneg ℓ d p) (sq_nonneg _)),
      integral_momProj_Bh ℓ d hℓ hd q, int_momProj_Bh_eq_msym ℓ d hℓ hd q]
    rw [← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  have hmain : ∫⁻ u : ℝ³, ENNReal.ofReal (momForm ℓ d u ψ)
      = ENNReal.ofReal (((2*Real.pi)^3)⁻¹)
        * ∫⁻ s : ℝ³, ENNReal.ofReal (‖fhat ψ s‖ ^ 2 * msym ℓ d s) := by
    rw [lintegral_congr hpu, lintegral_const_mul_real (((2*Real.pi)^3)⁻¹)]
    congr 1
    rw [lintegral_lintegral_swap hjointE, lintegral_congr hJu]
    -- group the p-independent constants and pull them out
    rw [show (fun p : ℝ³ => ENNReal.ofReal (momProj ℓ d p * ((ℓ^3)⁻¹ * ((2*Real.pi)^3)⁻¹))
          * ∫⁻ q : ℝ³, ENNReal.ofReal (‖fhat ψ q‖ ^ 2 * (Bh ℓ q p) ^ 2))
        = fun p : ℝ³ => ENNReal.ofReal ((ℓ^3)⁻¹ * ((2*Real.pi)^3)⁻¹)
          * (ENNReal.ofReal (momProj ℓ d p)
            * ∫⁻ q : ℝ³, ENNReal.ofReal (‖fhat ψ q‖ ^ 2 * (Bh ℓ q p) ^ 2)) from by
      funext p
      rw [show ENNReal.ofReal (momProj ℓ d p * ((ℓ^3)⁻¹ * ((2*Real.pi)^3)⁻¹))
          = ENNReal.ofReal (momProj ℓ d p) * ENNReal.ofReal ((ℓ^3)⁻¹ * ((2*Real.pi)^3)⁻¹) from
        ENNReal.ofReal_mul (momProj_nonneg ℓ d p)]
      ring]
    rw [lintegral_const_mul_real ((ℓ^3)⁻¹ * ((2*Real.pi)^3)⁻¹)]
    rw [show (fun p : ℝ³ => ENNReal.ofReal (momProj ℓ d p)
          * ∫⁻ q : ℝ³, ENNReal.ofReal (‖fhat ψ q‖ ^ 2 * (Bh ℓ q p) ^ 2))
        = fun p : ℝ³ => ∫⁻ q : ℝ³,
            ENNReal.ofReal (momProj ℓ d p * (‖fhat ψ q‖ ^ 2 * (Bh ℓ q p) ^ 2)) from by
      funext p
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr; intro q
      rw [ENNReal.ofReal_mul (momProj_nonneg ℓ d p)]]
    rw [lintegral_lintegral_swap (aestronglyMeasurable_pq_joint ℓ d ψ hψ hcs),
      lintegral_congr hq, lintegral_const_mul_real (ℓ^3 * (2*Real.pi)^3)]
    rw [show ENNReal.ofReal ((ℓ^3)⁻¹ * ((2*Real.pi)^3)⁻¹)
          * (ENNReal.ofReal (ℓ^3 * (2*Real.pi)^3)
            * ∫⁻ s : ℝ³, ENNReal.ofReal (‖fhat ψ s‖ ^ 2 * msym ℓ d s))
        = ∫⁻ s : ℝ³, ENNReal.ofReal (‖fhat ψ s‖ ^ 2 * msym ℓ d s) from by
      rw [← mul_assoc, show ENNReal.ofReal ((ℓ^3)⁻¹ * ((2*Real.pi)^3)⁻¹)
            * ENNReal.ofReal (ℓ^3 * (2*Real.pi)^3) = 1 from by
        rw [← ENNReal.ofReal_mul (by positivity),
          show (ℓ^3)⁻¹ * ((2*Real.pi)^3)⁻¹ * (ℓ^3 * (2*Real.pi)^3) = 1 from by field_simp]
        simp,
        one_mul]]
  rw [show (∫ u : ℝ³, momForm ℓ d u ψ) = (∫⁻ u : ℝ³, ENNReal.ofReal (momForm ℓ d u ψ)).toReal from
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun u => momForm_nonneg u ψ)
      (aestronglyMeasurable_momForm ℓ d ψ),
    show ((2*Real.pi)^3)⁻¹ * ∫ s : ℝ³, ‖fhat ψ s‖^2 * msym ℓ d s
      = (ENNReal.ofReal (((2*Real.pi)^3)⁻¹) * ∫⁻ s : ℝ³,
          ENNReal.ofReal (‖fhat ψ s‖^2 * msym ℓ d s)).toReal from by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
      congr 1
      exact integral_eq_lintegral_of_nonneg_ae
        (Eventually.of_forall fun s => mul_nonneg (sq_nonneg _) (msym_nonneg ℓ d s))
        (((continuous_kinFT_of_integrable hψint).norm.pow 2).aestronglyMeasurable.mul
          (aestronglyMeasurable_msym ℓ d)),
    hmain]

end Work.BoseKinLoc.Momentum
