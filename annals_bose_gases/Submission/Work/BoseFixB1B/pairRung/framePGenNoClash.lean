import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1.boxTauGen_mode_bound_meas
import Submission.Work.BoseFixB1B.pairMass_pos
import Submission.Work.BoseFixB1B.pairRung.framePerXBound
import Submission.Work.BoseFixB1B.pairRung.frameXIntegral
import Submission.Work.BoseFixB1S.D1InputsB1
import Submission.Work.BoseFixB1S.boxPairIdSlidingB1
import Submission.Work.BoseFixB1S.chainIntegralQdep
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B.pairRung

open _root_.BoseGases Submission.BoseGases
open Work.BoseFixB1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 0. Elementary support lemmas -/

/-- Inserting a point of a subset of the cube into a slot keeps a box configuration in the box. -/
lemma fpc_update_mem_abox {n : ℕ} {a : ℝ} {A : Set E3} (hA : A ⊆ acube a)
    {x : X n} (hx : x ∈ abox n a) (i : Fin n) {z : E3} (hz : z ∈ A) :
    Function.update x i z ∈ abox n a := by
  rw [mem_abox_iff] at hx ⊢
  intro k
  rw [Function.update_apply]
  by_cases hk : k = i
  · rw [if_pos hk]; exact hA hz
  · rw [if_neg hk]; exact hx k

/-- The restricted box measure is finite. -/
lemma fpc_isFiniteMeasure_restrict_Ac {a : ℝ} (ha : 0 < a) {Ac : Set E3}
    (hAc : Ac ⊆ acube a) :
    IsFiniteMeasure ((volume : Measure E3).restrict Ac) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ]
  exact lt_of_le_of_lt (measure_mono hAc) (acube_lt_top a ha.le)

/-- The frame integrand is nonnegative. -/
lemma fpc_frameIntegrand_nonneg (volA : ℝ) (Ac : Set E3) (χ : E3 → ℝ) {N : ℕ}
    (Ψ : X N → ℝ) (q : E3) (x : X N) : 0 ≤ frameIntegrand volA Ac χ Ψ q x := by
  have h : frameIntegrand volA Ac χ Ψ q x
      = (boxTauAnnGen volA Ac (boxWinModeReGen volA Ac χ q) Ψ x) ^ 2
        + (boxTauAnnGen volA Ac (boxWinModeImGen volA Ac χ q) Ψ x) ^ 2 := rfl
  rw [h]
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

/-! ## 1. Measurability -/

lemma fpc_measurable_boxWinModeReGen {volA : ℝ} {Ac : Set E3}
    (hAcm : MeasurableSet Ac) {χ : E3 → ℝ} (hχ : Measurable χ) (q : E3) :
    Measurable (boxWinModeReGen volA Ac χ q) := by
  have h1 : Measurable (fun z : E3 => Ac.indicator (fun _ => (1 : ℝ)) z
      * (χ z * Real.cos (inner ℝ q z) - volA⁻¹ * ∫ w in Ac, χ w * Real.cos (inner ℝ q w))) :=
    Measurable.mul (measurable_const.indicator hAcm)
      (((hχ.mul (Real.continuous_cos.measurable.comp
        (continuous_const.inner continuous_id).measurable)).sub measurable_const))
  exact h1

lemma fpc_measurable_boxWinModeImGen {volA : ℝ} {Ac : Set E3}
    (hAcm : MeasurableSet Ac) {χ : E3 → ℝ} (hχ : Measurable χ) (q : E3) :
    Measurable (boxWinModeImGen volA Ac χ q) := by
  have h1 : Measurable (fun z : E3 => -(Ac.indicator (fun _ => (1 : ℝ)) z
      * (χ z * Real.sin (inner ℝ q z) - volA⁻¹ * ∫ w in Ac, χ w * Real.sin (inner ℝ q w)))) :=
    Measurable.neg (Measurable.mul (measurable_const.indicator hAcm)
      (((hχ.mul (Real.continuous_sin.measurable.comp
        (continuous_const.inner continuous_id).measurable)).sub measurable_const)))
  exact h1

/-- `boxTauAnnGen` is measurable in the configuration. -/
lemma fpc_measurable_boxTauAnnGen {N : ℕ} (volA : ℝ) {Ac : Set E3} (hAcm : MeasurableSet Ac)
    {g : E3 → ℝ} (hg : Measurable g) {Ψ : X N → ℝ} (hΨ : Measurable Ψ) :
    Measurable (boxTauAnnGen volA Ac g Ψ) := by
  unfold boxTauAnnGen
  refine Measurable.const_mul ?_ _
  refine Finset.measurable_sum _ (fun i _ => ?_)
  refine Measurable.mul ((measurable_const.indicator hAcm).comp (measurable_pi_apply i)) ?_
  have hsm : StronglyMeasurable (Function.uncurry (fun (x : X N) (z : E3) =>
      g z * Ψ (Function.update x i z))) :=
    ((hg.comp measurable_snd).mul (hΨ.comp measurable_update')).stronglyMeasurable
  have h := hsm.integral_prod_right (ν := (volume : Measure E3).restrict Ac)
  simpa only [Function.uncurry_apply_pair] using h.measurable

/-! ## 2. The windowed mode is bounded by `2κ` -/

/-- **The mode bound**, for a signed window `χ` with `|χ| ≤ κ`. -/
lemma fpc_abs_modeGen_le {a volA κ : ℝ} (ha : 0 < a) (hvolpos : 0 < volA)
    {Ac : Set E3} (hAcm : MeasurableSet Ac) (hAc : Ac ⊆ acube a)
    (hvol : volA = (MeasureTheory.volume Ac).toReal)
    {χ f : E3 → ℝ} (hχc : Continuous χ) (hfc : Continuous f) (hf1 : ∀ z, |f z| ≤ 1)
    (hκ : ∀ z, |χ z| ≤ κ) (z : E3) :
    |Ac.indicator (fun _ => (1 : ℝ)) z * (χ z * f z - volA⁻¹ * ∫ w in Ac, χ w * f w)|
      ≤ 2 * κ := by
  haveI : IsFiniteMeasure ((volume : Measure E3).restrict Ac) :=
    fpc_isFiniteMeasure_restrict_Ac ha hAc
  have hκ0 : 0 ≤ κ := le_trans (abs_nonneg (χ 0)) (hκ 0)
  have hc : |∫ w in Ac, χ w * f w| ≤ κ * volA := by
    have hb : ∀ w ∈ Ac, |χ w * f w| ≤ κ := by
      intro w _
      rw [abs_mul]
      calc |χ w| * |f w| ≤ κ * 1 := mul_le_mul (hκ w) (hf1 w) (abs_nonneg _) hκ0
        _ = κ := mul_one κ
    have hInt : IntegrableOn (fun w : E3 => χ w * f w) Ac volume :=
      ((hχc.mul hfc).continuousOn.integrableOn_compact
        (acube_compact ha)).mono_set hAc
    calc |∫ w in Ac, χ w * f w| ≤ ∫ w in Ac, |χ w * f w| := abs_integral_le_integral_abs
      _ ≤ ∫ _w in Ac, (κ : ℝ) := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun w => abs_nonneg _)
            (integrable_const κ) (ae_restrict_iff' hAcm |>.mpr (ae_of_all _ hb))
      _ = κ * volA := by
          rw [MeasureTheory.setIntegral_const, Measure.real_def, ← hvol]
          rw [smul_eq_mul, mul_comm]
  by_cases hz : z ∈ Ac
  · rw [Set.indicator_of_mem hz, one_mul]
    have h1 : |χ z * f z| ≤ κ := by
      rw [abs_mul]
      calc |χ z| * |f z| ≤ κ * 1 := mul_le_mul (hκ z) (hf1 z) (abs_nonneg _) hκ0
        _ = κ := mul_one κ
    have h2 : |volA⁻¹ * ∫ w in Ac, χ w * f w| ≤ κ := by
      rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hvolpos.le)]
      calc volA⁻¹ * |∫ w in Ac, χ w * f w| ≤ volA⁻¹ * (κ * volA) :=
            mul_le_mul_of_nonneg_left hc (inv_nonneg.mpr hvolpos.le)
        _ = κ := by
            rw [inv_mul_eq_iff_eq_mul₀ (ne_of_gt hvolpos)]
            ring
    calc |χ z * f z - volA⁻¹ * ∫ w in Ac, χ w * f w|
        ≤ |χ z * f z| + |volA⁻¹ * ∫ w in Ac, χ w * f w| := abs_sub _ _
      _ ≤ κ + κ := add_le_add h1 h2
      _ = 2 * κ := by ring
  · rw [Set.indicator_of_notMem hz, zero_mul, abs_zero]
    linarith

/-- A mode bounded by `κ` has bounded windowed real part. -/
lemma fpc_abs_boxWinModeReGen_le {a volA κ : ℝ} (ha : 0 < a) (hvolpos : 0 < volA)
    {Ac : Set E3} (hAcm : MeasurableSet Ac) (hAc : Ac ⊆ acube a)
    (hvol : volA = (MeasureTheory.volume Ac).toReal)
    {χ : E3 → ℝ} (hχc : Continuous χ)
    (hκ : ∀ z, |χ z| ≤ κ) (q z : E3) :
    |boxWinModeReGen volA Ac χ q z| ≤ 2 * κ :=
  fpc_abs_modeGen_le ha hvolpos hAcm hAc hvol hχc
    (Real.continuous_cos.comp (continuous_const.inner continuous_id))
    (fun w => Real.abs_cos_le_one _) hκ z

/-- A mode bounded by `κ` has bounded windowed imaginary part. -/
lemma fpc_abs_boxWinModeImGen_le {a volA κ : ℝ} (ha : 0 < a) (hvolpos : 0 < volA)
    {Ac : Set E3} (hAcm : MeasurableSet Ac) (hAc : Ac ⊆ acube a)
    (hvol : volA = (MeasureTheory.volume Ac).toReal)
    {χ : E3 → ℝ} (hχc : Continuous χ)
    (hκ : ∀ z, |χ z| ≤ κ) (q z : E3) :
    |boxWinModeImGen volA Ac χ q z| ≤ 2 * κ := by
  rw [boxWinModeImGen, abs_neg]
  exact fpc_abs_modeGen_le ha hvolpos hAcm hAc hvol hχc
    (Real.continuous_sin.comp (continuous_const.inner continuous_id))
    (fun w => Real.abs_sin_le_one _) hκ z

/-! ## 3. The amplitude bound and integrability of its square -/

/-- **The amplitude bound.** -/
lemma fpc_abs_boxTauAnnGen_le {N : ℕ} {a volA κ CΨ : ℝ} (ha : 0 < a) (hvolpos : 0 < volA)
    (hκ0 : 0 ≤ κ) {Ac : Set E3} (hAcm : MeasurableSet Ac) (hAc : Ac ⊆ acube a)
    (hvol : volA = (MeasureTheory.volume Ac).toReal)
    {g : E3 → ℝ} (hgm : Measurable g) (hg : ∀ z, |g z| ≤ κ)
    {Ψ : X N → ℝ} (hΨ : Continuous Ψ) (hCΨ : ∀ x ∈ abox N a, |Ψ x| ≤ CΨ)
    {x : X N} (hx : x ∈ abox N a) :
    |boxTauAnnGen volA Ac g Ψ x| ≤ (Real.sqrt volA)⁻¹ * (N : ℝ) * (κ * CΨ * volA) := by
  haveI : IsFiniteMeasure ((volume : Measure E3).restrict Ac) :=
    fpc_isFiniteMeasure_restrict_Ac ha hAc
  have hterm : ∀ i : Fin N, |∫ z in Ac, g z * Ψ (Function.update x i z)| ≤ κ * CΨ * volA := by
    intro i
    have hb : ∀ z ∈ Ac, |g z * Ψ (Function.update x i z)| ≤ κ * CΨ := by
      intro z hz
      rw [abs_mul]
      exact mul_le_mul (hg z) (hCΨ _ (fpc_update_mem_abox hAc hx i hz))
        (abs_nonneg _) hκ0
    have haesm : AEStronglyMeasurable (fun z : E3 => g z * Ψ (Function.update x i z))
        ((volume : Measure E3).restrict Ac) :=
      (hgm.mul (hΨ.measurable.comp (measurable_update (f := x) (a := i)))).aestronglyMeasurable
    have hInt : IntegrableOn (fun z : E3 => g z * Ψ (Function.update x i z)) Ac volume :=
      IntegrableOn.of_bound
        (lt_of_le_of_lt (measure_mono hAc) (acube_lt_top a ha.le))
        haesm (κ * CΨ) (ae_restrict_iff' hAcm |>.mpr (ae_of_all _ hb))
    refine (abs_integral_le_integral_abs).trans ?_
    have hmono := integral_mono_of_nonneg
      (μ := (volume : Measure E3).restrict Ac)
      (f := fun z => |g z * Ψ (Function.update x i z)|)
      (g := fun _ : E3 => κ * CΨ)
      (Eventually.of_forall fun z => abs_nonneg _) (integrable_const (κ * CΨ))
      (ae_restrict_iff' hAcm |>.mpr (ae_of_all _ hb))
    refine hmono.trans (le_of_eq ?_)
    rw [MeasureTheory.setIntegral_const, Measure.real_def, ← hvol]
    rw [smul_eq_mul]
    ring
  have hle : |∑ i : Fin N, Ac.indicator (fun _ => (1 : ℝ)) (x i)
      * ∫ z in Ac, g z * Ψ (Function.update x i z)| ≤ ∑ _i : Fin N, (κ * CΨ * volA) := by
    calc |∑ i : Fin N, Ac.indicator (fun _ => (1 : ℝ)) (x i)
            * ∫ z in Ac, g z * Ψ (Function.update x i z)|
        ≤ ∑ i : Fin N, |Ac.indicator (fun _ => (1 : ℝ)) (x i)
            * ∫ z in Ac, g z * Ψ (Function.update x i z)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin N, (1 : ℝ) * (κ * CΨ * volA) := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          rw [abs_mul]
          have hind : |Ac.indicator (fun _ => (1 : ℝ)) (x i)| ≤ (1 : ℝ) := by
            by_cases h : x i ∈ Ac
            · rw [Set.indicator_of_mem h, abs_one]
            · rw [Set.indicator_of_notMem h, abs_zero]; norm_num
          exact mul_le_mul hind (hterm i) (abs_nonneg _) (by norm_num)
      _ = ∑ _i : Fin N, (κ * CΨ * volA) :=
          Finset.sum_congr rfl (fun i _ => by ring)
  have hsqrt : |boxTauAnnGen volA Ac g Ψ x|
      = (Real.sqrt volA)⁻¹ * |∑ i : Fin N, Ac.indicator (fun _ => (1 : ℝ)) (x i)
          * ∫ z in Ac, g z * Ψ (Function.update x i z)| := by
    rw [boxTauAnnGen, abs_mul, abs_inv, abs_of_nonneg (Real.sqrt_nonneg volA)]
  rw [hsqrt]
  calc (Real.sqrt volA)⁻¹ * |∑ i : Fin N, Ac.indicator (fun _ => (1 : ℝ)) (x i)
        * ∫ z in Ac, g z * Ψ (Function.update x i z)|
      ≤ (Real.sqrt volA)⁻¹ * ∑ _i : Fin N, (κ * CΨ * volA) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = (Real.sqrt volA)⁻¹ * (N : ℝ) * (κ * CΨ * volA) := by
        rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
        ring

/-- The square of a genuine box amplitude is integrable on the box. -/
lemma fpc_integrableOn_boxTauAnnGen_sq {N : ℕ} {a volA κ CΨ : ℝ} (ha : 0 < a)
    (hvolpos : 0 < volA) (hκ0 : 0 ≤ κ) {Ac : Set E3} (hAcm : MeasurableSet Ac)
    (hAc : Ac ⊆ acube a) (hvol : volA = (MeasureTheory.volume Ac).toReal)
    {g : E3 → ℝ} (hgm : Measurable g) (hg : ∀ z, |g z| ≤ κ)
    {Ψ : X N → ℝ} (hΨ : Continuous Ψ) (hCΨ : ∀ x ∈ abox N a, |Ψ x| ≤ CΨ) :
    IntegrableOn (fun x => (boxTauAnnGen volA Ac g Ψ x) ^ 2) (abox N a) volume := by
  refine IntegrableOn.of_bound (abox_lt_top N a ha.le)
    ((fpc_measurable_boxTauAnnGen volA hAcm hgm hΨ.measurable).pow_const 2
      |>.aestronglyMeasurable)
    (((Real.sqrt volA)⁻¹ * (N : ℝ) * (κ * CΨ * volA)) ^ 2) ?_
  rw [ae_restrict_iff' (abox_measurable N a)]
  refine ae_of_all _ (fun x hx => ?_)
  rw [Real.norm_eq_abs, abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _)
    (fpc_abs_boxTauAnnGen_le ha hvolpos hκ0 hAcm hAc hvol hgm hg hΨ hCΨ hx) 2

/-- Integrability of the frame integrand in `x`, for fixed `q`. -/
lemma fpc_integrableOn_frameIntegrand {N : ℕ} {a volA κ CΨ : ℝ} (ha : 0 < a)
    (hvolpos : 0 < volA) (hκ0 : 0 ≤ κ) {Ac : Set E3} (hAcm : MeasurableSet Ac)
    (hAc : Ac ⊆ acube a) (hvol : volA = (MeasureTheory.volume Ac).toReal)
    {χ : E3 → ℝ} (hχc : Continuous χ) (hκ : ∀ z, |χ z| ≤ κ)
    {Ψ : X N → ℝ} (hΨ : Continuous Ψ) (hCΨ : ∀ x ∈ abox N a, |Ψ x| ≤ CΨ) (q : E3) :
    IntegrableOn (fun x => frameIntegrand volA Ac χ Ψ q x) (abox N a) volume := by
  have hRe := fpc_integrableOn_boxTauAnnGen_sq (N := N) (κ := 2 * κ) ha hvolpos (by linarith)
    hAcm hAc hvol (fpc_measurable_boxWinModeReGen hAcm hχc.measurable q)
    (fun z => fpc_abs_boxWinModeReGen_le ha hvolpos hAcm hAc hvol hχc hκ q z) hΨ hCΨ
  have hIm := fpc_integrableOn_boxTauAnnGen_sq (N := N) (κ := 2 * κ) ha hvolpos (by linarith)
    hAcm hAc hvol (fpc_measurable_boxWinModeImGen hAcm hχc.measurable q)
    (fun z => fpc_abs_boxWinModeImGen_le ha hvolpos hAcm hAc hvol hχc hκ q z) hΨ hCΨ
  exact hRe.add hIm

/-! ## 4. `boxWinModePGen` is the `x`-integral of the frame integrand -/

lemma fpc_boxWinModePGen_eq_integral_frameIntegrand {N : ℕ} {a volA κ CΨ : ℝ} (ha : 0 < a)
    (hvolpos : 0 < volA) (hκ0 : 0 ≤ κ) {Ac : Set E3} (hAcm : MeasurableSet Ac)
    (hAc : Ac ⊆ acube a) (hvol : volA = (MeasureTheory.volume Ac).toReal)
    {χ : E3 → ℝ} (hχc : Continuous χ) (hκ : ∀ z, |χ z| ≤ κ)
    {Ψ : X N → ℝ} (hΨ : Continuous Ψ) (hCΨ : ∀ x ∈ abox N a, |Ψ x| ≤ CΨ) (q : E3) :
    boxWinModePGen a volA Ac χ Ψ q
      = ∫ x in abox N a, frameIntegrand volA Ac χ Ψ q x := by
  have hRe : IntegrableOn (fun x : X N =>
      (boxTauAnnGen volA Ac (boxWinModeReGen volA Ac χ q) Ψ x) ^ 2) (abox N a) volume :=
    fpc_integrableOn_boxTauAnnGen_sq (N := N) (κ := 2 * κ) ha hvolpos (by linarith) hAcm hAc hvol
      (fpc_measurable_boxWinModeReGen hAcm hχc.measurable q)
      (fun z => fpc_abs_boxWinModeReGen_le ha hvolpos hAcm hAc hvol hχc hκ q z) hΨ hCΨ
  have hIm : IntegrableOn (fun x : X N =>
      (boxTauAnnGen volA Ac (boxWinModeImGen volA Ac χ q) Ψ x) ^ 2) (abox N a) volume :=
    fpc_integrableOn_boxTauAnnGen_sq (N := N) (κ := 2 * κ) ha hvolpos (by linarith) hAcm hAc hvol
      (fpc_measurable_boxWinModeImGen hAcm hχc.measurable q)
      (fun z => fpc_abs_boxWinModeImGen_le ha hvolpos hAcm hAc hvol hχc hκ q z) hΨ hCΨ
  rw [boxWinModePGen, boxModePGen, boxModePGen, ← integral_add hRe hIm]
  exact integral_congr_ae (Eventually.of_forall fun x => rfl)

/-! ## 5. The two delegated pieces -/

/-
The per-configuration frame bound for a signed, merely continuous window, at an arbitrary particle
number `n` — `Work.BoseFixB1B.pairRung.framePerXBound` — is imported from
`Submission/Work/BoseFixB1B/pairRung/framePerXBound.lean`, and its `x`-integral companion (the slot
swap) — `Work.BoseFixB1B.pairRung.frameXIntegral` — from
`Submission/Work/BoseFixB1B/pairRung/frameXIntegral.lean`.  Both are used in the assembly below (in
`hper` and in `hIntB`/`hval` respectively), where the imported expression of `frameXIntegral` is
matched against the local abbreviation `fpc_frameBound`.
-/

/-! ## 6. The per-configuration frame bound, named -/

/-- The per-configuration frame bound of `framePerXBound` (the same expression, our own name). -/
noncomputable def fpc_frameBound (volA κ : ℝ) (Ac : Set E3) {N : ℕ} (Ψ : X N → ℝ)
    (x : X N) : ℝ :=
  volA⁻¹ * (N : ℝ) * κ ^ 2 * (2 * Real.pi) ^ 3 *
    ∑ i : Fin N, Ac.indicator (fun _ => (1 : ℝ)) (x i)
      * ∫ z in Ac, (slotFibre volA Ac i Ψ x z) ^ 2

lemma fpc_frameBound_eq (volA κ : ℝ) (Ac : Set E3) {N : ℕ} (Ψ : X N → ℝ) (x : X N) :
    fpc_frameBound volA κ Ac Ψ x
      = volA⁻¹ * (N : ℝ) * κ ^ 2 * (2 * Real.pi) ^ 3 *
          ∑ i : Fin N, Ac.indicator (fun _ => (1 : ℝ)) (x i)
            * ∫ z in Ac, (slotFibre volA Ac i Ψ x z) ^ 2 := rfl

/-! ## 7. The frame bound -/

theorem framePGenNoClash {N : ℕ} {a volA : ℝ} (ha : 0 < a)
    {Ac : Set (EuclideanSpace ℝ (Fin 3))} (hAcm : MeasurableSet Ac)
    (hAcsub : Ac ⊆ Submission.BoseGases.acube a)
    (hvol : volA = (MeasureTheory.volume Ac).toReal) (hvolpos : 0 < volA)
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχc : Continuous χ) (hχs : HasCompactSupport χ)
    (hχsupp : ∀ z, z ∉ Ac → χ z = 0) {κ : ℝ} (hκ : ∀ z, |χ z| ≤ κ)
    {Ψ : Submission.BoseGases.X N → ℝ} (hΨ : Continuous Ψ) :
    ((2 * Real.pi) ^ 3)⁻¹ * (∫ q : EuclideanSpace ℝ (Fin 3),
        Work.BoseFixB1.boxWinModePGen a volA Ac χ Ψ q)
      ≤ 2 * κ ^ 2 * (N : ℝ) * Work.UBBInputs8.cnPlusBoxInd a Ac volA Ψ := by
  have hκ0 : 0 ≤ κ := le_trans (abs_nonneg (χ 0)) (hκ 0)
  have hcn : 0 ≤ Work.UBBInputs8.cnPlusBoxInd a Ac volA Ψ := by
    rw [Work.UBBInputs8.cnPlusBoxInd]
    exact Finset.sum_nonneg (fun i _ => integral_nonneg fun x => sq_nonneg _)
  rcases N with _ | M
  · -- ### `N = 0`: everything vanishes
    have hzero : ∀ q : E3, boxWinModePGen a volA Ac χ Ψ q = 0 := by
      intro q
      simp [boxWinModePGen, boxModePGen, boxTauAnnGen]
    have hint : (∫ q : E3, boxWinModePGen a volA Ac χ Ψ q) = 0 := by
      simp only [hzero]
      simp
    rw [hint]
    simp [Work.UBBInputs8.cnPlusBoxInd]
  · -- ### `N = M + 1`
    obtain ⟨CΨ, hCΨ0, hCΨnorm⟩ :=
      Work.BoseFixB1.exists_bound_abox (N := M + 1) (ℓ := a) ha hΨ
    have hCΨ : ∀ x ∈ abox (M + 1) a, |Ψ x| ≤ CΨ := fun x hx => by
      rw [← Real.norm_eq_abs]; exact hCΨnorm x hx
    -- ### 1. `boxWinModePGen` is the `x`-integral of the frame integrand
    have hstep1 : ∀ q : E3, boxWinModePGen a volA Ac χ Ψ q
        = ∫ x in abox (M + 1) a, frameIntegrand volA Ac χ Ψ q x :=
      fun q => fpc_boxWinModePGen_eq_integral_frameIntegrand ha hvolpos hκ0 hAcm hAcsub hvol
        hχc hκ hΨ hCΨ q
    -- ### 2. measurability and nonnegativity of `q ↦ boxWinModePGen q`
    have hsmU : StronglyMeasurable
        (fun p : E3 × X (M + 1) => frameIntegrand volA Ac χ Ψ p.1 p.2) :=
      stronglyMeasurable_frameIntegrand ha hvolpos hAcm hAcsub hχc hΨ
    have haesmP : AEStronglyMeasurable (fun q : E3 => boxWinModePGen a volA Ac χ Ψ q)
        (volume : Measure E3) := by
      have h2 : StronglyMeasurable (fun q : E3 =>
          ∫ x, frameIntegrand volA Ac χ Ψ q x
            ∂((volume : Measure (X (M + 1))).restrict (abox (M + 1) a))) :=
        hsmU.integral_prod_right'
      refine h2.aestronglyMeasurable.congr ?_
      exact Eventually.of_forall fun q => (hstep1 q).symm
    have hPnn : ∀ q : E3, 0 ≤ boxWinModePGen a volA Ac χ Ψ q := by
      intro q
      rw [hstep1 q]
      exact integral_nonneg fun x => fpc_frameIntegrand_nonneg volA Ac χ Ψ q x
    -- ### 3. the `lintegral` chain
    have hIntx : ∀ q : E3, Integrable (fun x => frameIntegrand volA Ac χ Ψ q x)
        ((volume : Measure (X (M + 1))).restrict (abox (M + 1) a)) :=
      fun q => fpc_integrableOn_frameIntegrand ha hvolpos hκ0 hAcm hAcsub hvol hχc hκ hΨ hCΨ q
    have hstep2 : ∀ q : E3, ENNReal.ofReal (boxWinModePGen a volA Ac χ Ψ q)
        = ∫⁻ x, ENNReal.ofReal (frameIntegrand volA Ac χ Ψ q x)
            ∂((volume : Measure (X (M + 1))).restrict (abox (M + 1) a)) := by
      intro q
      rw [hstep1 q]
      exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hIntx q)
        (Eventually.of_forall fun x => fpc_frameIntegrand_nonneg volA Ac χ Ψ q x)
    have hjoint : AEMeasurable (Function.uncurry (fun (q : E3) (x : X (M + 1)) =>
        ENNReal.ofReal (frameIntegrand volA Ac χ Ψ q x)))
        ((volume : Measure E3).prod
          ((volume : Measure (X (M + 1))).restrict (abox (M + 1) a))) :=
      AEMeasurable.ennreal_ofReal hsmU.aemeasurable
    have hton : (∫⁻ q, ∫⁻ x, ENNReal.ofReal (frameIntegrand volA Ac χ Ψ q x)
          ∂((volume : Measure (X (M + 1))).restrict (abox (M + 1) a)) ∂(volume : Measure E3))
        = ∫⁻ x, ∫⁻ q, ENNReal.ofReal (frameIntegrand volA Ac χ Ψ q x)
          ∂(volume : Measure E3)
          ∂((volume : Measure (X (M + 1))).restrict (abox (M + 1) a)) :=
      MeasureTheory.lintegral_lintegral_swap hjoint
    have hper : ∀ x : X (M + 1),
        (∫⁻ q : E3, ENNReal.ofReal (frameIntegrand volA Ac χ Ψ q x))
          ≤ ENNReal.ofReal (fpc_frameBound volA κ Ac Ψ x) := by
      intro x
      obtain ⟨hIntq, hbnd⟩ :=
        framePerXBound ha hAcm hAcsub hvol hvolpos hχc hχs hχsupp hκ hΨ x
      have hbnd' : (∫ q : E3, frameIntegrand volA Ac χ Ψ q x)
          ≤ fpc_frameBound volA κ Ac Ψ x := by
        rw [fpc_frameBound_eq]
        exact hbnd
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIntq
        (Eventually.of_forall fun q => fpc_frameIntegrand_nonneg volA Ac χ Ψ q x)]
      exact ENNReal.ofReal_mono hbnd'
    obtain ⟨hIntB0, hval0⟩ :=
      frameXIntegral (n := M + 1) (a := a) (volA := volA) (κ := κ) (CΨ := CΨ)
        ha hAcm hAcsub hvol hvolpos hΨ hCΨ hCΨ0
    have hIntB : Integrable (fun x => fpc_frameBound volA κ Ac Ψ x)
        ((volume : Measure (X (M + 1))).restrict (abox (M + 1) a)) := by
      rw [show (fun x : X (M + 1) => fpc_frameBound volA κ Ac Ψ x)
          = fun x : X (M + 1) => volA⁻¹ * (((M + 1 : ℕ)) : ℝ) * κ ^ 2 * (2 * Real.pi) ^ 3 *
              ∑ i : Fin (M + 1), Ac.indicator (fun _ => (1 : ℝ)) (x i)
                * ∫ z in Ac, (slotFibre volA Ac i Ψ x z) ^ 2 from
        funext fun x => fpc_frameBound_eq volA κ Ac Ψ x]
      exact hIntB0
    have hval : (∫ x in abox (M + 1) a, fpc_frameBound volA κ Ac Ψ x)
        = (2 * Real.pi) ^ 3 * volA⁻¹ * (((M + 1 : ℕ)) : ℝ) * κ ^ 2 * volA
          * Work.UBBInputs8.cnPlusBoxInd a Ac volA Ψ := by
      rw [show (∫ x in abox (M + 1) a, fpc_frameBound volA κ Ac Ψ x)
          = ∫ x in abox (M + 1) a,
              volA⁻¹ * (((M + 1 : ℕ)) : ℝ) * κ ^ 2 * (2 * Real.pi) ^ 3 *
                ∑ i : Fin (M + 1), Ac.indicator (fun _ => (1 : ℝ)) (x i)
                  * ∫ z in Ac, (slotFibre volA Ac i Ψ x z) ^ 2 from
        integral_congr_ae (Eventually.of_forall fun x => fpc_frameBound_eq volA κ Ac Ψ x)]
      exact hval0
    have hBnn : ∀ x : X (M + 1), 0 ≤ fpc_frameBound volA κ Ac Ψ x := by
      intro x
      rw [fpc_frameBound_eq]
      refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) (sq_nonneg κ))
        (by positivity)) ?_
      · exact inv_nonneg.mpr hvolpos.le
      · exact Nat.cast_nonneg (M + 1)
      · refine Finset.sum_nonneg (fun i _ => mul_nonneg ?_ (integral_nonneg fun z => sq_nonneg _))
        by_cases h : x i ∈ Ac
        · simp [Set.indicator_of_mem h]
        · simp [Set.indicator_of_notMem h]
    have hstep5 : (∫⁻ x, ENNReal.ofReal (fpc_frameBound volA κ Ac Ψ x)
          ∂((volume : Measure (X (M + 1))).restrict (abox (M + 1) a)))
        = ENNReal.ofReal (∫ x in abox (M + 1) a, fpc_frameBound volA κ Ac Ψ x) :=
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIntB
        (Eventually.of_forall hBnn)).symm
    have hchain : (∫⁻ q, ENNReal.ofReal (boxWinModePGen a volA Ac χ Ψ q))
        ≤ ENNReal.ofReal ((2 * Real.pi) ^ 3 * volA⁻¹ * (((M + 1 : ℕ)) : ℝ) * κ ^ 2 * volA
            * Work.UBBInputs8.cnPlusBoxInd a Ac volA Ψ) := by
      calc (∫⁻ q, ENNReal.ofReal (boxWinModePGen a volA Ac χ Ψ q))
          = ∫⁻ q, ∫⁻ x, ENNReal.ofReal (frameIntegrand volA Ac χ Ψ q x)
              ∂((volume : Measure (X (M + 1))).restrict (abox (M + 1) a))
              ∂(volume : Measure E3) :=
            lintegral_congr_ae (Eventually.of_forall fun q => hstep2 q)
        _ = ∫⁻ x, ∫⁻ q, ENNReal.ofReal (frameIntegrand volA Ac χ Ψ q x)
              ∂(volume : Measure E3)
              ∂((volume : Measure (X (M + 1))).restrict (abox (M + 1) a)) := hton
        _ ≤ ∫⁻ x, ENNReal.ofReal (fpc_frameBound volA κ Ac Ψ x)
              ∂((volume : Measure (X (M + 1))).restrict (abox (M + 1) a)) :=
            lintegral_mono hper
        _ = ENNReal.ofReal (∫ x in abox (M + 1) a, fpc_frameBound volA κ Ac Ψ x) := hstep5
        _ = ENNReal.ofReal ((2 * Real.pi) ^ 3 * volA⁻¹ * (((M + 1 : ℕ)) : ℝ) * κ ^ 2 * volA
              * Work.UBBInputs8.cnPlusBoxInd a Ac volA Ψ) := by rw [hval]
    -- ### 4. back to real integrals
    have hfin : (∫⁻ q, ENNReal.ofReal (boxWinModePGen a volA Ac χ Ψ q)) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hchain
    have hreal : (∫ q : E3, boxWinModePGen a volA Ac χ Ψ q)
        ≤ (2 * Real.pi) ^ 3 * volA⁻¹ * (((M + 1 : ℕ)) : ℝ) * κ ^ 2 * volA
          * Work.UBBInputs8.cnPlusBoxInd a Ac volA Ψ := by
      have h1 := (ENNReal.toReal_le_toReal hfin ENNReal.ofReal_ne_top).mpr hchain
      rw [← MeasureTheory.integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hPnn)
        haesmP] at h1
      rwa [ENNReal.toReal_ofReal (by
        have h2 : (0 : ℝ) ≤ (2 * Real.pi) ^ 3 * volA⁻¹ * (((M + 1 : ℕ)) : ℝ) * κ ^ 2 * volA := by
          positivity
        exact mul_nonneg h2 hcn)] at h1
    -- ### 5. arithmetic
    calc ((2 * Real.pi) ^ 3)⁻¹ * (∫ q : E3, boxWinModePGen a volA Ac χ Ψ q)
        ≤ ((2 * Real.pi) ^ 3)⁻¹ * ((2 * Real.pi) ^ 3 * volA⁻¹ * (((M + 1 : ℕ)) : ℝ) * κ ^ 2
            * volA * Work.UBBInputs8.cnPlusBoxInd a Ac volA Ψ) :=
          mul_le_mul_of_nonneg_left hreal (by positivity)
      _ = (((M + 1 : ℕ)) : ℝ) * κ ^ 2 * Work.UBBInputs8.cnPlusBoxInd a Ac volA Ψ := by
          field_simp
      _ ≤ 2 * κ ^ 2 * (((M + 1 : ℕ)) : ℝ) * Work.UBBInputs8.cnPlusBoxInd a Ac volA Ψ := by
          have h1 : 0 ≤ κ ^ 2 * (((M + 1 : ℕ)) : ℝ) * Work.UBBInputs8.cnPlusBoxInd a Ac volA Ψ :=
            mul_nonneg (mul_nonneg (sq_nonneg κ) (by positivity)) hcn
          linarith

end Work.BoseFixB1B.pairRung
