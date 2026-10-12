import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseKinLoc.Kinetic.momForm_le_box
import Submission.Work.BoseKinLoc.Momentum.aestronglyMeasurable_momForm_joint
import Submission.Work.BoseKinLoc.Momentum.integrable_fhat_Bh
import Submission.Work.BoseKinLoc.Momentum.integrable_momProj_Bh
import Submission.Work.BoseKinLoc.Momentum.integrable_statU_sq_alt
import Submission.Work.BoseKinLoc.Momentum.integral_PsiC_sq_alt
import Submission.Work.BoseKinLoc.Momentum.integral_momProj_Bh
import Submission.Work.BoseKinLoc.Momentum.integral_u_statU_sq_alt
import Submission.Work.BoseKinLoc.Momentum.memLp_kinFT
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Momentum.momForm_u_integral_alt` — FS `eq:Q1Qslide`, the exact `u`-average

The precise `u`-average of the sliding mean-free box family

  `momForm ℓ d u ψ = (2π)⁻³ ∫_p momProj ℓ d p · ‖kinFT (1_{Λ(u)}(ψ − m_u)) p‖²`

is the Fourier-diagonal form

  `∫_u momForm ℓ d u ψ
     = (2π)⁻³ ∫_s ‖fhat ψ s‖² · ((2π)⁻³ ∫_{‖w‖ > (d²)⁻¹}
          (cubFT (w − ℓ•s) − cubFT (ℓ•s) cubFT w)² dw) ds`.

## Proof strategy (all in `ℝ≥0∞`; no Bochner-integrability side conditions)

Every function in sight is nonnegative, so the argument runs in the extended nonnegative
reals, where Tonelli's theorem needs only a.e. measurability:

* `momForm ℓ d u ψ = (2π)⁻³ ∫_p momProj ℓ d p · ‖kinFT (statU ℓ u ψ) p‖²` is definitional
  (`statU ℓ u ψ` is literally the function transformed inside `momForm`), hence
  `⟦momForm ℓ d u ψ⟧ = ⟦(2π)⁻³⟧ · ∫⁻_p ⟦momProj ℓ d p · ‖kinFT (statU ℓ u ψ) p‖²⟧`
  (`ofReal_integral_eq_lintegral_ofReal`, the `p`-integrand being integrable by
  `kinFT_sq_of_memLp` applied to the bounded, compactly supported box state);
* Tonelli (`lintegral_lintegral_swap`) for the `(u,p)`-integrand — measurability is
  `aestronglyMeasurable_momForm_joint`;
* the `u`-integral of `‖kinFT (statU ℓ u ψ) p‖²` is computed by the dilation change of
  variables `u ↦ x = ℓu` after the pointwise identity
  `kinFT (statU ℓ u ψ) p = e^{−iℓ⟪p,u⟫} PsiC ℓ p ψ (ℓu)` (`integral_u_statU_sq_alt`);
* the `x`-integral of `‖PsiC ℓ p ψ‖²` is Plancherel for the boxed state,
  `∫_x ‖PsiC ℓ p ψ x‖² = (2π)⁻³ ∫_q ‖fhat ψ q‖² Bh ℓ q p²` (`integral_PsiC_sq_alt`);
* Tonelli again for the `(p,q)`-integrand, then
  `∫_p momProj ℓ d p · Bh ℓ q p² = ℓ³ ∫_{‖w‖>(d²)⁻¹} (cubFT (w − ℓ•q) − cubFT (ℓ•q) cubFT w)²`
  (`integral_momProj_Bh`);
* the constants collapse and both sides become `(2π)⁻⁶` times
  `∫_q ‖fhat ψ q‖² ∫_{‖w‖>(d²)⁻¹} (cubFT (w − ℓ•q) − cubFT (ℓ•q) cubFT w)²`.

The passage back to Bochner integrals is `integral_eq_lintegral_of_nonneg_ae`
(`momForm_nonneg` on the left, and a.e. strong measurability of
`s ↦ ‖fhat ψ s‖² msym ℓ d s` on the right).

The four analytic inputs are stated as the explicit hypotheses of `momForm_u_integral_core`
and then supplied by the sibling modules `Momentum.integrable_statU_sq_alt`,
`Momentum.integral_u_statU_sq_alt`, `Momentum.integral_PsiC_sq_alt` and
`Momentum.aestronglyMeasurable_msym_alt`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.Momentum

open Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## Elementary facts about the objects in the statement -/

/-- `statU` is the `Kinetic` chapter's `boxState` (the same function, under two names). -/
lemma statU_eq_boxState (ℓ : ℝ) (u : E3) (ψ : E3 → ℝ) :
    statU ℓ u ψ = Work.BoseKinLoc.Kinetic.boxState ℓ u ψ := rfl

/-- `momForm` unfolded through the complexified box state `statU`. -/
lemma momForm_eq_statU (ℓ d : ℝ) (u : E3) (ψ : E3 → ℝ) :
    Work.BoseKinLoc.momForm ℓ d u ψ
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, momProj ℓ d p * ‖kinFT (statU ℓ u ψ) p‖ ^ 2 :=
  rfl

/-- The `p`-integrand of `momForm` is integrable, for every `u`: Plancherel in `L¹ ∩ L²`
applied to the bounded compactly supported box state. -/
lemma integrable_momProj_kinFT_statU_sq (ℓ d : ℝ) (hℓ : 0 < ℓ) (u : E3) (ψ : E3 → ℝ)
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    Integrable (fun p : E3 => momProj ℓ d p * ‖kinFT (statU ℓ u ψ) p‖ ^ 2) := by
  have hbase : Integrable (fun p : E3 => ‖kinFT (statU ℓ u ψ) p‖ ^ 2) := by
    have hb := Work.BoseKinLoc.Kinetic.boxState_memLp hℓ u hψ
    have h := Work.BoseKinLoc.Kinetic.kinFT_sq_of_memLp
      (F := Work.BoseKinLoc.Kinetic.boxState ℓ u ψ) hb.1 hb.2
    rw [statU_eq_boxState]
    exact h.1
  refine Integrable.mono' hbase ?_ ?_
  · have ha : AEMeasurable (fun p : E3 => momProj ℓ d p) volume := by
      refine Measurable.aemeasurable ?_
      unfold momProj
      exact Measurable.ite (measurableSet_lt measurable_const continuous_norm.measurable)
        measurable_const measurable_const
    exact (ha.mul hbase.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
  · filter_upwards with p
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (Work.BoseKinLoc.Kinetic.momProj_nonneg ℓ d p) (sq_nonneg _))]
    exact mul_le_of_le_one_left (sq_nonneg _) (Work.BoseKinLoc.Kinetic.momProj_le_one ℓ d p)

/-- `u ↦ momForm ℓ d u ψ` is a.e. strongly measurable, from the joint measurability of the
`(u,p)`-integrand. -/
lemma aestronglyMeasurable_momForm_alt (ℓ d : ℝ) (ψ : E3 → ℝ) (hℓ : 0 < ℓ)
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) :
    AEStronglyMeasurable (fun u : E3 => Work.BoseKinLoc.momForm ℓ d u ψ) volume := by
  have hjoint := aestronglyMeasurable_momForm_joint ℓ d ψ hℓ hψ
  have hmeas : AEStronglyMeasurable
      (fun u : E3 => ∫ p : E3, momProj ℓ d p * ‖kinFT (statU ℓ u ψ) p‖ ^ 2) volume :=
    hjoint.integral_prod_right'
  refine (hmeas.const_mul (((2 * Real.pi) ^ 3)⁻¹)).congr ?_
  filter_upwards with u
  exact (momForm_eq_statU ℓ d u ψ).symm

/-- `msym ℓ d` is nonnegative. -/
lemma msym_nonneg_alt (ℓ d : ℝ) (s : E3) : 0 ≤ msym ℓ d s := by
  unfold msym
  refine mul_nonneg (by positivity) (setIntegral_nonneg ?_ (fun w _ => sq_nonneg _))
  exact measurableSet_lt measurable_const continuous_norm.measurable

/-- The raw exterior `w`-integral is `(2π)³` times `msym`. -/
lemma int_raw_eq_msym (ℓ d : ℝ) (q : E3) :
    (∫ w in {q' : E3 | (d ^ 2)⁻¹ < ‖q'‖},
        (cubFT (w - ℓ • q) - cubFT (ℓ • q) * cubFT w) ^ 2) = (2 * Real.pi) ^ 3 * msym ℓ d q := by
  unfold msym
  field_simp

/-- `(p,q) ↦ Bh ℓ q p` is continuous (for `ℓ > 0`). -/
lemma continuous_Bh_pair {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Continuous (fun z : E3 × E3 => Bh ℓ z.2 z.1) := by
  have hbox : Continuous (Work.OneBodyKin.boxHat ℓ) := continuous_boxHat_of_pos hℓ
  unfold Bh
  fun_prop

/-- The `(p,q)`-integrand of the second Tonelli step is a.e. measurable. -/
lemma aestronglyMeasurable_momProj_fhat_Bh (ℓ d : ℝ) (ψ : E3 → ℝ)
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) (hℓ : 0 < ℓ) :
    AEMeasurable (fun z : E3 × E3 => ENNReal.ofReal
      (momProj ℓ d z.1 * (‖fhat ψ z.2‖ ^ 2 * (Bh ℓ z.2 z.1) ^ 2)))
      (volume.prod volume) := by
  have hψint : Integrable (fun z : E3 => (ψ z : ℂ)) := integrable_psiCe ψ hψ hcs
  have hfhat : Continuous (fhat ψ) := continuous_kinFT_of_integrable hψint
  have hBh : Continuous (fun z : E3 × E3 => Bh ℓ z.2 z.1) := continuous_Bh_pair hℓ
  have hmom : Measurable (fun z : E3 × E3 => momProj ℓ d z.1) := by
    unfold momProj
    exact (Measurable.ite (measurableSet_lt measurable_const continuous_norm.measurable)
      measurable_const measurable_const).comp measurable_fst
  have hg : Measurable (fun z : E3 × E3 => ‖fhat ψ z.2‖ ^ 2 * (Bh ℓ z.2 z.1) ^ 2) :=
    (((hfhat.measurable.comp measurable_snd).norm.pow_const 2)).mul (hBh.measurable.pow_const 2)
  exact ((hmom.mul hg).aemeasurable).ennreal_ofReal

/-- `msym ℓ d` is a.e. strongly measurable (the `s`-dependence sits inside a parametric integral
over a fixed measurable set of a jointly continuous integrand). -/
lemma msym_aesm (ℓ d : ℝ) :
    AEStronglyMeasurable (msym ℓ d) (volume : Measure E3) := by
  have hset : MeasurableSet {q : E3 | (d ^ 2)⁻¹ < ‖q‖} :=
    measurableSet_lt measurable_const continuous_norm.measurable
  -- the squared sliding difference is continuous in `(s,w)`
  have hg : StronglyMeasurable (fun z : E3 × E3 =>
      (cubFT (z.2 - ℓ • z.1) - cubFT (ℓ • z.1) * cubFT z.2) ^ 2) :=
    (((cubFT_continuous.comp (continuous_snd.sub (continuous_fst.const_smul ℓ))).sub
      ((cubFT_continuous.comp (continuous_fst.const_smul ℓ)).mul
        (cubFT_continuous.comp continuous_snd))).pow 2).stronglyMeasurable
  have hind : StronglyMeasurable (fun z : E3 × E3 =>
      Set.indicator {q : E3 | (d ^ 2)⁻¹ < ‖q‖} (fun _ : E3 => (1 : ℝ)) z.2) :=
    ((stronglyMeasurable_const : StronglyMeasurable (fun _ : E3 => (1 : ℝ))).indicator
      hset).comp_measurable measurable_snd
  have hprod : StronglyMeasurable (fun z : E3 × E3 =>
      Set.indicator {q : E3 | (d ^ 2)⁻¹ < ‖q‖} (fun _ : E3 => (1 : ℝ)) z.2
        * (cubFT (z.2 - ℓ • z.1) - cubFT (ℓ • z.1) * cubFT z.2) ^ 2) := hind.mul hg
  have hEq : (fun z : E3 × E3 => Set.indicator {q : E3 | (d ^ 2)⁻¹ < ‖q‖}
        (fun w => (cubFT (w - ℓ • z.1) - cubFT (ℓ • z.1) * cubFT w) ^ 2) z.2)
      = fun z : E3 × E3 => Set.indicator {q : E3 | (d ^ 2)⁻¹ < ‖q‖} (fun _ : E3 => (1 : ℝ)) z.2
        * (cubFT (z.2 - ℓ • z.1) - cubFT (ℓ • z.1) * cubFT z.2) ^ 2 := by
    funext z
    by_cases hz : z.2 ∈ {q : E3 | (d ^ 2)⁻¹ < ‖q‖}
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, one_mul]
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, zero_mul]
  have hjoint : StronglyMeasurable (fun z : E3 × E3 => Set.indicator {q : E3 | (d ^ 2)⁻¹ < ‖q‖}
      (fun w => (cubFT (w - ℓ • z.1) - cubFT (ℓ • z.1) * cubFT w) ^ 2) z.2) := by
    rw [hEq]
    exact hprod
  have hmeas : StronglyMeasurable (fun s : E3 =>
      ∫ w in {q : E3 | (d ^ 2)⁻¹ < ‖q‖},
        (cubFT (w - ℓ • s) - cubFT (ℓ • s) * cubFT w) ^ 2) := by
    rw [show (fun s : E3 => ∫ w in {q : E3 | (d ^ 2)⁻¹ < ‖q‖},
          (cubFT (w - ℓ • s) - cubFT (ℓ • s) * cubFT w) ^ 2)
        = fun s : E3 => ∫ w : E3, Set.indicator {q : E3 | (d ^ 2)⁻¹ < ‖q‖}
            (fun w => (cubFT (w - ℓ • s) - cubFT (ℓ • s) * cubFT w) ^ 2) w from by
      funext s
      exact (integral_indicator hset).symm]
    exact StronglyMeasurable.integral_prod_right hjoint
  have hfun : msym ℓ d = fun s : E3 => ((2 * Real.pi) ^ 3)⁻¹ * ∫ w in {q : E3 | (d ^ 2)⁻¹ < ‖q‖},
      (cubFT (w - ℓ • s) - cubFT (ℓ • s) * cubFT w) ^ 2 := rfl
  rw [hfun]
  exact (hmeas.const_mul _).aestronglyMeasurable

/-! ## The main computation -/

/-- **FS `eq:Q1Qslide`** with the four analytic inputs as explicit hypotheses. -/
lemma momForm_u_integral_core
    (h_statU_int : ∀ (ℓ : ℝ), 0 < ℓ → ∀ (p : E3) (ψ : E3 → ℝ), ContDiff ℝ (⊤ : ENat) ψ →
      HasCompactSupport ψ → Integrable (fun u : E3 => ‖kinFT (statU ℓ u ψ) p‖ ^ 2))
    (h_u_int : ∀ (ℓ : ℝ), 0 < ℓ → ∀ (p : E3) (ψ : E3 → ℝ), ContDiff ℝ (⊤ : ENat) ψ →
      ∫ u : E3, ‖kinFT (statU ℓ u ψ) p‖ ^ 2 = (ℓ ^ 3)⁻¹ * ∫ x : E3, ‖PsiC ℓ p ψ x‖ ^ 2)
    (h_PsiC_int : ∀ (ℓ : ℝ), 0 < ℓ → ∀ (p : E3) (ψ : E3 → ℝ),
      ContDiff ℝ (⊤ : ENat) ψ → HasCompactSupport ψ →
      ∫ x : E3, ‖PsiC ℓ p ψ x‖ ^ 2
        = ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : E3, ‖fhat ψ q‖ ^ 2 * (Bh ℓ q p) ^ 2)
    (h_msym_aesm : ∀ (ℓ d : ℝ), AEStronglyMeasurable (msym ℓ d) (volume : Measure E3))
    (ψ : E3 → ℝ) (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ)
    (ℓ d : ℝ) (hℓ : 0 < ℓ) (hd : 0 < d) :
    ∫ u : E3, Work.BoseKinLoc.momForm ℓ d u ψ =
      ((2 * Real.pi) ^ 3)⁻¹ * ∫ s : E3, ‖fhat ψ s‖ ^ 2 *
        (((2 * Real.pi) ^ 3)⁻¹ * ∫ w in {q : E3 | (d ^ 2)⁻¹ < ‖q‖},
          (cubFT (w - ℓ • s) - cubFT (ℓ • s) * cubFT w) ^ 2) := by
  have hψint : Integrable (fun z : E3 => (ψ z : ℂ)) := integrable_psiCe ψ hψ hcs
  have h2pi : (0 : ℝ) < (2 * Real.pi) ^ 3 := by positivity
  have h2pi_inv : (0 : ℝ) ≤ ((2 * Real.pi) ^ 3)⁻¹ := by positivity
  have hl3 : (0 : ℝ) ≤ ℓ ^ 3 := by positivity
  -- a.e. measurability of the `(u,p)`-integrand, lifted to `ℝ≥0∞`
  have hjointE : AEMeasurable (fun w : E3 × E3 => ENNReal.ofReal
      (momProj ℓ d w.2 * ‖kinFT (statU ℓ w.1 ψ) w.2‖ ^ 2)) (volume.prod volume) :=
    (aestronglyMeasurable_momForm_joint ℓ d ψ hℓ hψ).aemeasurable.ennreal_ofReal
  -- ### Step 1: unfold `momForm` and pass to the Lebesgue integral
  have hpu : ∀ u : E3, ENNReal.ofReal (Work.BoseKinLoc.momForm ℓ d u ψ)
      = ENNReal.ofReal (((2 * Real.pi) ^ 3)⁻¹) * ∫⁻ p : E3,
          ENNReal.ofReal (momProj ℓ d p * ‖kinFT (statU ℓ u ψ) p‖ ^ 2) := by
    intro u
    rw [momForm_eq_statU ℓ d u ψ, ENNReal.ofReal_mul h2pi_inv]
    congr 1
    exact ofReal_integral_eq_lintegral_ofReal
      (integrable_momProj_kinFT_statU_sq ℓ d hℓ u ψ hψ hcs)
      (Eventually.of_forall fun p =>
        mul_nonneg (Work.BoseKinLoc.Kinetic.momProj_nonneg ℓ d p) (sq_nonneg _))
  -- ### Step 2: the `u`-integral for fixed `p`
  have hJu : ∀ p : E3, ∫⁻ u : E3, ENNReal.ofReal (momProj ℓ d p * ‖kinFT (statU ℓ u ψ) p‖ ^ 2)
      = ENNReal.ofReal (momProj ℓ d p) * (ENNReal.ofReal ((ℓ ^ 3)⁻¹) *
          (ENNReal.ofReal (((2 * Real.pi) ^ 3)⁻¹) *
            ∫⁻ q : E3, ENNReal.ofReal (‖fhat ψ q‖ ^ 2 * (Bh ℓ q p) ^ 2))) := by
    intro p
    have hstep : ∫⁻ u : E3, ENNReal.ofReal (‖kinFT (statU ℓ u ψ) p‖ ^ 2)
        = ENNReal.ofReal ((ℓ ^ 3)⁻¹) * (ENNReal.ofReal (((2 * Real.pi) ^ 3)⁻¹) *
            ∫⁻ q : E3, ENNReal.ofReal (‖fhat ψ q‖ ^ 2 * (Bh ℓ q p) ^ 2)) := by
      have hb : ∫⁻ u : E3, ENNReal.ofReal (‖kinFT (statU ℓ u ψ) p‖ ^ 2)
          = ENNReal.ofReal (∫ u : E3, ‖kinFT (statU ℓ u ψ) p‖ ^ 2) :=
        (ofReal_integral_eq_lintegral_ofReal (h_statU_int ℓ hℓ p ψ hψ hcs)
          (Eventually.of_forall fun u => sq_nonneg _)).symm
      have hsplit : ENNReal.ofReal ((ℓ ^ 3)⁻¹ * (((2 * Real.pi) ^ 3)⁻¹ *
            (∫ q : E3, ‖fhat ψ q‖ ^ 2 * (Bh ℓ q p) ^ 2)))
          = ENNReal.ofReal ((ℓ ^ 3)⁻¹) * (ENNReal.ofReal (((2 * Real.pi) ^ 3)⁻¹) *
              ENNReal.ofReal (∫ q : E3, ‖fhat ψ q‖ ^ 2 * (Bh ℓ q p) ^ 2)) := by
        rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (ℓ ^ 3)⁻¹),
          ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ((2 * Real.pi) ^ 3)⁻¹)]
      rw [hb, h_u_int ℓ hℓ p ψ hψ, h_PsiC_int ℓ hℓ p ψ hψ hcs, hsplit,
        ofReal_integral_eq_lintegral_ofReal (integrable_fhat_Bh ℓ p ψ hψ hcs)
          (Eventually.of_forall fun q => mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    rw [show (fun u : E3 => ENNReal.ofReal (momProj ℓ d p * ‖kinFT (statU ℓ u ψ) p‖ ^ 2))
        = fun u : E3 => ENNReal.ofReal (momProj ℓ d p)
            * ENNReal.ofReal (‖kinFT (statU ℓ u ψ) p‖ ^ 2) from by
      funext u; rw [ENNReal.ofReal_mul (Work.BoseKinLoc.Kinetic.momProj_nonneg ℓ d p)]]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hstep]
  -- ### Step 3: the `p`-integral for fixed `q`
  have hq : ∀ q : E3, ∫⁻ p : E3,
        ENNReal.ofReal (momProj ℓ d p * (‖fhat ψ q‖ ^ 2 * (Bh ℓ q p) ^ 2))
      = ENNReal.ofReal (ℓ ^ 3 * (2 * Real.pi) ^ 3)
        * ENNReal.ofReal (‖fhat ψ q‖ ^ 2 * msym ℓ d q) := by
    intro q
    have hreal : ∫ p : E3, momProj ℓ d p * (‖fhat ψ q‖ ^ 2 * (Bh ℓ q p) ^ 2)
        = ℓ ^ 3 * (2 * Real.pi) ^ 3 * (‖fhat ψ q‖ ^ 2 * msym ℓ d q) := by
      rw [show (fun p : E3 => momProj ℓ d p * (‖fhat ψ q‖ ^ 2 * (Bh ℓ q p) ^ 2))
          = fun p : E3 => ‖fhat ψ q‖ ^ 2 * (momProj ℓ d p * (Bh ℓ q p) ^ 2) from by
        funext p; ring]
      rw [integral_const_mul, integral_momProj_Bh ℓ d hℓ hd q, int_raw_eq_msym ℓ d q]
      ring
    have hI : Integrable (fun p : E3 =>
        momProj ℓ d p * (‖fhat ψ q‖ ^ 2 * (Bh ℓ q p) ^ 2)) := by
      refine ((integrable_momProj_Bh ℓ d hℓ q).const_mul (‖fhat ψ q‖ ^ 2)).congr ?_
      filter_upwards with p
      ring
    have hbridge : ∫⁻ p : E3,
          ENNReal.ofReal (momProj ℓ d p * (‖fhat ψ q‖ ^ 2 * (Bh ℓ q p) ^ 2))
        = ENNReal.ofReal (ℓ ^ 3 * (2 * Real.pi) ^ 3)
          * ENNReal.ofReal (‖fhat ψ q‖ ^ 2 * msym ℓ d q) := by
      rw [← ofReal_integral_eq_lintegral_ofReal hI
          (Eventually.of_forall fun p => mul_nonneg
            (Work.BoseKinLoc.Kinetic.momProj_nonneg ℓ d p)
            (mul_nonneg (sq_nonneg _) (sq_nonneg _))),
        hreal, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ℓ ^ 3 * (2 * Real.pi) ^ 3),
        ENNReal.ofReal_mul (sq_nonneg (‖fhat ψ q‖))]
    exact hbridge
  -- ### Step 4: assembly
  have hmain : ∫⁻ u : E3, ENNReal.ofReal (Work.BoseKinLoc.momForm ℓ d u ψ)
      = ENNReal.ofReal (((2 * Real.pi) ^ 3)⁻¹)
        * ∫⁻ s : E3, ENNReal.ofReal (‖fhat ψ s‖ ^ 2 * msym ℓ d s) := by
    rw [lintegral_congr hpu, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    rw [lintegral_lintegral_swap hjointE, lintegral_congr hJu]
    -- pull the constants `(ℓ³)⁻¹(2π)⁻³` out of the `p`-integral
    rw [show (fun p : E3 => ENNReal.ofReal (momProj ℓ d p) *
            (ENNReal.ofReal ((ℓ ^ 3)⁻¹) * (ENNReal.ofReal (((2 * Real.pi) ^ 3)⁻¹) *
              ∫⁻ q : E3, ENNReal.ofReal (‖fhat ψ q‖ ^ 2 * (Bh ℓ q p) ^ 2))))
        = fun p : E3 => (ENNReal.ofReal ((ℓ ^ 3)⁻¹) * ENNReal.ofReal (((2 * Real.pi) ^ 3)⁻¹)) *
            (ENNReal.ofReal (momProj ℓ d p) *
              ∫⁻ q : E3, ENNReal.ofReal (‖fhat ψ q‖ ^ 2 * (Bh ℓ q p) ^ 2)) from by
      funext p; ring]
    rw [lintegral_const_mul' _ _
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
    -- move `⟦momProj p⟧` inside the `q`-integral
    rw [show (fun p : E3 => ENNReal.ofReal (momProj ℓ d p) *
            ∫⁻ q : E3, ENNReal.ofReal (‖fhat ψ q‖ ^ 2 * (Bh ℓ q p) ^ 2))
        = fun p : E3 => ∫⁻ q : E3, ENNReal.ofReal
            (momProj ℓ d p * (‖fhat ψ q‖ ^ 2 * (Bh ℓ q p) ^ 2)) from by
      funext p
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr; intro q
      rw [ENNReal.ofReal_mul (Work.BoseKinLoc.Kinetic.momProj_nonneg ℓ d p)]]
    rw [lintegral_lintegral_swap (aestronglyMeasurable_momProj_fhat_Bh ℓ d ψ hψ hcs hℓ),
      lintegral_congr hq, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    -- the constants collapse
    have hconst : ENNReal.ofReal ((ℓ ^ 3)⁻¹) * ENNReal.ofReal (((2 * Real.pi) ^ 3)⁻¹) *
        ENNReal.ofReal (ℓ ^ 3 * (2 * Real.pi) ^ 3) = 1 := by
      rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (ℓ ^ 3)⁻¹),
        ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (ℓ ^ 3)⁻¹ * ((2 * Real.pi) ^ 3)⁻¹)]
      rw [show (ℓ ^ 3)⁻¹ * ((2 * Real.pi) ^ 3)⁻¹ * (ℓ ^ 3 * (2 * Real.pi) ^ 3) = 1 by
        field_simp]
      simp
    rw [← mul_assoc, hconst, one_mul]
  -- ### Step 5: return to Bochner integrals
  rw [show (∫ u : E3, Work.BoseKinLoc.momForm ℓ d u ψ)
        = (∫⁻ u : E3, ENNReal.ofReal (Work.BoseKinLoc.momForm ℓ d u ψ)).toReal from
      integral_eq_lintegral_of_nonneg_ae
        (Eventually.of_forall fun u => Work.BoseKinLoc.momForm_nonneg u ψ)
        (aestronglyMeasurable_momForm_alt ℓ d ψ hℓ hψ),
    show ((2 * Real.pi) ^ 3)⁻¹ * ∫ s : E3, ‖fhat ψ s‖ ^ 2 *
        (((2 * Real.pi) ^ 3)⁻¹ * ∫ w in {q : E3 | (d ^ 2)⁻¹ < ‖q‖},
          (cubFT (w - ℓ • s) - cubFT (ℓ • s) * cubFT w) ^ 2)
      = (ENNReal.ofReal (((2 * Real.pi) ^ 3)⁻¹) *
          ∫⁻ s : E3, ENNReal.ofReal (‖fhat ψ s‖ ^ 2 * msym ℓ d s)).toReal from by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal h2pi_inv]
      congr 1
      exact integral_eq_lintegral_of_nonneg_ae
        (Eventually.of_forall fun s => mul_nonneg (sq_nonneg _) (msym_nonneg_alt ℓ d s))
        (((continuous_kinFT_of_integrable hψint).norm.pow 2).aestronglyMeasurable.mul
          (h_msym_aesm ℓ d)),
    hmain]

theorem momForm_u_integral_alt (ψ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ)
    (ℓ d : ℝ) (hℓ : 0 < ℓ) (hd : 0 < d) :
    ∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.momForm ℓ d u ψ =
      ((2 * Real.pi) ^ 3)⁻¹ * ∫ s : EuclideanSpace ℝ (Fin 3), ‖Work.BoseKinLoc.fhat ψ s‖ ^ 2 *
        (((2 * Real.pi) ^ 3)⁻¹ * ∫ w in {q : EuclideanSpace ℝ (Fin 3) | (d ^ 2)⁻¹ < ‖q‖},
          (Work.BoseKinLoc.Momentum.cubFT (w - ℓ • s) -
            Work.BoseKinLoc.Momentum.cubFT (ℓ • s) * Work.BoseKinLoc.Momentum.cubFT w) ^ 2) := by
  exact momForm_u_integral_core
    (fun ℓ hℓ p ψ hψ hcs => integrable_statU_sq_alt ℓ hℓ p ψ hψ hcs)
    (fun ℓ hℓ p ψ hψ => integral_u_statU_sq_alt ℓ hℓ p ψ hψ)
    (fun ℓ hℓ p ψ hψ hcs => integral_PsiC_sq_alt ℓ hℓ p ψ hψ hcs)
    (fun ℓ d => msym_aesm ℓ d)
    ψ hψ hcs ℓ d hℓ hd
end Work.BoseKinLoc.Momentum
