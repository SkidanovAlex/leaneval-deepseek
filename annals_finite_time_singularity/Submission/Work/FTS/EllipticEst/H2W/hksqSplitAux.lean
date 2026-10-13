import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.H2W.mixedA
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.FTS.EllipticEst.AgmonSlice.zsq_pzIter2_mixed_open
import Submission.Work.Coercivity.EzDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-!
# Bookkeeping layer for `hksqSplitMixed`

The self-contained auxiliary layer of `Work.FTS.EllipticEst.H2W.hksqSplitMixed`: the generic
splitting of an iterated integral over `Iz × Iθ` into a finite sum, the honesty of the
individual summands inherited from `HkMem` by domination with the `ℋ^k`-integrand, and the
congruence of weighted `L²`-squares on the open quadrant.
-/

/-! ## Small pointwise and measure-theoretic bookkeeping -/

/-- Multiplication of a function which is `C^∞` on the open quadrant by the radial factor
`z ^ 2` keeps it `C^∞` there. -/
theorem smoothOpen_zsq_mul {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * f z θ) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => z ^ 2 * f z θ)) Work.FTS.EllipticEst.Q0
  rw [show Function.uncurry (fun z θ => z ^ 2 * f z θ)
      = fun p : ℝ × ℝ => p.1 ^ 2 * f p.1 p.2 from rfl]
  have hf' : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => f p.1 p.2)
      Work.FTS.EllipticEst.Q0 := hf
  exact ((contDiffOn_fst (𝕜 := ℝ) (s := Work.FTS.EllipticEst.Q0)).pow 2).mul hf'

/-- The product weight `Wt α` is continuous on the open quadrant. -/
theorem continuousOn_Wt_Q0 (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) Work.FTS.EllipticEst.Q0 := by
  have hmem : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < p.1 ∧ 0 < p.2 ∧ p.2 < Real.pi / 2 :=
    fun p hp => Work.FTS.EllipticEst.mem_Q0.mp hp
  have hsinpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < Real.sin (2 * p.2) := fun p hp => by
    obtain ⟨-, h0, h1⟩ := hmem p hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Work.FTS.EllipticEst.Q0 := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by funext p; rfl
    rw [hfun]
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => ?_)
    exact pow_ne_zero 2 (ne_of_gt (hmem p hp).1)
  have hWt : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = fun p : ℝ × ℝ => Work.Spaces.w p.1
          * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by funext p; rfl
  rw [hWt]
  refine hw.mul ?_
  exact (((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn)).rpow_const
    (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))

/-- The `ℋ^k`-integrand vanishes identically at `z = 0`. -/
theorem HkIntegrand_at_zero (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α k f 0 θ = 0 := by
  simp only [Work.Spaces.HkIntegrand, Work.Spaces.Wt, Work.Spaces.wTheta, Work.Spaces.w]
  norm_num

/-- **Congruence of a weighted `L²`-square on the closed radial half-line.** -/
theorem L2Sq_congr_Q0 {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ, 0 ≤ z → θ ∈ Set.Ioo 0 (Real.pi / 2) → f z θ = g z θ) :
    Work.Spaces.L2Sq f = Work.Spaces.L2Sq g := by
  have hIoo : (Set.Ioo (0 : ℝ) (Real.pi / 2)) =ᵐ[MeasureTheory.volume] Work.Spaces.Iθ :=
    MeasureTheory.Ioo_ae_eq_Icc
  rw [Work.Spaces.L2Sq, Work.Spaces.L2Sq]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z hz => ?_)
  have e1 : (∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2)
      = ∫ θ in Set.Ioo 0 (Real.pi / 2), (f z θ) ^ 2 :=
    MeasureTheory.setIntegral_congr_set hIoo.symm
  have e2 : (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2)
      = ∫ θ in Set.Ioo 0 (Real.pi / 2), (g z θ) ^ 2 :=
    MeasureTheory.setIntegral_congr_set hIoo.symm
  rw [e1, e2]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
    (fun θ hθ => by rw [h z θ hz hθ])

/-! ## Splitting an iterated integral into a finite sum -/

/-- **Honesty of the iterated integral of a finite sum.** -/
theorem i2Mem_finsetSum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ → ℝ)
    (h : ∀ i ∈ s, Work.Coercivity.I2Mem (f i)) :
    Work.Coercivity.I2Mem (fun z θ => ∑ i ∈ s, f i z θ) := by
  constructor
  · intro z hz
    exact MeasureTheory.integrable_finsetSum s (fun i hi => (h i hi).1 z hz)
  · have hint : MeasureTheory.Integrable
        (fun z : ℝ => ∑ i ∈ s, ∫ θ in Work.Spaces.Iθ, f i z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      MeasureTheory.integrable_finsetSum s (fun i hi => (h i hi).2)
    refine hint.congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    exact (MeasureTheory.integral_finsetSum s (fun i hi => (h i hi).1 z hz)).symm

/-- **The iterated integral of a finite sum is the sum of the iterated integrals.** -/
theorem iterated_integral_finsetSum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ → ℝ)
    (h : ∀ i ∈ s, Work.Coercivity.I2Mem (f i)) :
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ∑ i ∈ s, f i z θ)
      = ∑ i ∈ s, (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, f i z θ) := by
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, ∑ i ∈ s, f i z θ)
        = ∑ i ∈ s, ∫ θ in Work.Spaces.Iθ, f i z θ :=
    fun z hz => MeasureTheory.integral_finsetSum s (fun i hi => (h i hi).1 z hz)
  have hcongr : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ∑ i ∈ s, f i z θ)
      = ∫ z in Work.Spaces.Iz, ∑ i ∈ s, (∫ θ in Work.Spaces.Iθ, f i z θ) :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ici hinner
  have hcongr2 : (∫ z in Work.Spaces.Iz, ∑ i ∈ s, (∫ θ in Work.Spaces.Iθ, f i z θ))
      = ∑ i ∈ s, (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, f i z θ) :=
    MeasureTheory.integral_finsetSum s (fun i hi => (h i hi).2)
  rw [hcongr, hcongr2]

/-- **Additivity of the iterated integral in two terms.** -/
theorem iterated_integral_add {A B : ℝ → ℝ → ℝ} (hA : Work.Coercivity.I2Mem A)
    (hB : Work.Coercivity.I2Mem B) :
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, (A z θ + B z θ))
      = (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, A z θ)
        + (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, B z θ) := by
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, (A z θ + B z θ))
        = (∫ θ in Work.Spaces.Iθ, A z θ) + (∫ θ in Work.Spaces.Iθ, B z θ) :=
    fun z hz => MeasureTheory.integral_add (hA.1 z hz) (hB.1 z hz)
  have hcongr : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, (A z θ + B z θ))
      = ∫ z in Work.Spaces.Iz,
          ((∫ θ in Work.Spaces.Iθ, A z θ) + (∫ θ in Work.Spaces.Iθ, B z θ)) :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ici hinner
  have hcongr2 : (∫ z in Work.Spaces.Iz,
        ((∫ θ in Work.Spaces.Iθ, A z θ) + (∫ θ in Work.Spaces.Iθ, B z θ)))
      = (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, A z θ)
        + (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, B z θ) :=
    MeasureTheory.integral_add hA.2 hB.2
  rw [hcongr, hcongr2]

/-- **Honesty of the iterated integral of a square dominated by the `ℋ^k`-integrand.**
This is the `HkMem`-version of the integrability of a single summand of the
`ℋ^k`-integrand: a nonnegative square bounded pointwise by the (integrable) full integrand
is honest.  The a.e. strong measurability comes from continuity on the open quadrant. -/
theorem i2Mem_sq_of_le {α : ℝ} {k : ℕ} {f A : ℝ → ℝ → ℝ} (hm : Work.Spaces.HkMem α k f)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => (A p.1 p.2) ^ 2) Work.FTS.EllipticEst.Q0)
    (hle : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      (A z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α k f z θ) :
    Work.Coercivity.I2Mem (fun z θ => (A z θ) ^ 2) := by
  constructor
  · intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · subst h0
      refine MeasureTheory.IntegrableOn.congr_fun MeasureTheory.integrableOn_zero
        (fun θ hθ => ?_) measurableSet_Icc
      have h1 := hle 0 (le_refl (0 : ℝ)) θ hθ
      rw [HkIntegrand_at_zero] at h1
      exact (le_antisymm h1 (sq_nonneg _)).symm
    · have hsl : ContinuousOn (fun θ : ℝ => (A z θ) ^ 2) (Set.Ioo 0 (Real.pi / 2)) :=
        hcont.comp (continuous_const.prodMk continuous_id).continuousOn
          (fun θ hθ => ⟨hz0, hθ⟩)
      have haesm : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => (A z θ) ^ 2)
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
        have h1 : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => (A z θ) ^ 2)
            (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
          hsl.aestronglyMeasurable measurableSet_Ioo
        have hset : MeasureTheory.volume.restrict Work.Spaces.Iθ
            = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
          (MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc).symm
        rwa [hset]
      refine MeasureTheory.Integrable.mono' (hm.1 z hz) haesm ?_
      filter_upwards [MeasureTheory.ae_restrict_mem
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with θ hθ
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hle z hz θ hθ
  · have hjoint : MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ => (A p.1 p.2) ^ 2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      Work.Spaces.aesm_of_continuousOn_Qd _ hcont
    refine MeasureTheory.Integrable.mono' hm.2 hjoint.integral_prod_right' ?_
    filter_upwards [MeasureTheory.ae_restrict_mem
      (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)] with z hz
    rw [Real.norm_of_nonneg (integral_nonneg fun θ => sq_nonneg _)]
    exact integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => sq_nonneg _)
      (hm.1 z hz)
      (MeasureTheory.ae_restrict_of_forall_mem
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
        fun θ hθ => hle z hz θ hθ)

/-- The iterated integral of an `if`-guarded function is the `if` of the iterated
integrals. -/
theorem iterated_integral_ite {p : Prop} [Decidable p] {f : ℝ → ℝ → ℝ} :
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, (if p then f z θ else 0))
      = if p then (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, f z θ) else 0 := by
  by_cases h : p
  · rw [if_pos h]
    have e1 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, (if p then f z θ else 0))
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, f z θ := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z hz => ?_)
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
      exact if_pos h
    rw [e1]
  · rw [if_neg h]
    have e1 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, (if p then f z θ else 0))
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, (0 : ℝ) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z hz => ?_)
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
      exact if_neg h
    rw [e1]
    simp

end Work.FTS.EllipticEst.H2W
