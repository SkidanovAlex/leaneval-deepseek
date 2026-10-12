import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BSKinetic.SlotSwap.bigBoxWord1_slot_aemeas
import Submission.Work.BSKinetic.SlotSwap.joint_measurable_smallBoxWord1
import Submission.Work.BSKinetic.cnPlus_slotState1_eq
import Submission.Work.BSKinetic.slotWord_bounds
import Submission.Work.BSKinetic.tBwordBInd_eq_slotSum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! **The `u`-integral of the `(n+1)`-body sliding word as a slot sum, plus the integrability of the
three `r`-functions the assembly integrates.**

The first conjunct is the Fubini step: `Work.BSKinetic.tBwordBInd_eq_slotSum` (module
`Submission.Work.BSKinetic.tBwordBInd_eq_slotSum`) gives, *pointwise in `u`*,

    `tBwordBInd (n+1) ℓ d ε c u Φ = Σ_i ∫_r∈abox n ℓ smallBoxWord1 ℓ d ε c u (slotState1 i Φ r)`,

so `∫_u` of the left side equals `Σ_i ∫_u ∫_r ...` (`MeasureTheory.integral_finset_sum`, each term
integrable) which Fubini (`MeasureTheory.integral_integral_swap`) turns into
`Σ_i ∫_r ∫_u ...`.  Joint integrability of `(u,r) ↦ smallBoxWord1 ℓ d ε c u (slotState1 i Φ r)` on
`volume.prod (Work.BSKinetic.boxMu n ℓ)` follows from the compact `u`-support and the uniform bound
of `Work.BSKinetic.slotWord_bounds` (`Submission/Work/BSKinetic/slotWord_bounds.lean`) together
with the joint measurability supplied by
`Submission.Work.BSKinetic.SlotSwap.joint_measurable_smallBoxWord1`, through
`Commons.Measure.Integral.integrable_uncurry_of_lintegral_le_sfinite` (the domination by
`K * 1_{‖u‖ ≤ R}`).

The three integrability conjuncts are then `MeasureTheory.AEStronglyMeasurable` (in `r`) plus an
a.e. bound, via `MeasureTheory.Integrable.of_bound` on the finite measure
`Work.BSKinetic.boxMu n ℓ` (`Submission.BoseGases.abox_lt_top`): the bound for the first function
is `|Φ| ≤ 2 * sup |Φ|` on the compact box `abox (n+1) ℓ` and `cnPlus` is an integral of a square;
the bounds for the second and third are `Work.BSKinetic.slotWord_bounds`
(`Work.BSKinetic.smallBoxWord1_bound`, `Work.BSKinetic.bigBoxWord1_bound`). -/

noncomputable section

open MeasureTheory Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BSKinetic

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-! ## 1. Elementary bookkeeping -/

/-- The restricted measure `boxMu n ℓ` is finite. -/
lemma isFiniteMeasure_boxMu (n : ℕ) (ℓ : ℝ) (hℓ : 0 ≤ ℓ) : IsFiniteMeasure (boxMu n ℓ) :=
  ⟨by rw [boxMu, Measure.restrict_apply_univ]; exact abox_lt_top n ℓ hℓ⟩

/-- The slot-`i` fibre of a smooth `(n+1)`-particle state is a smooth one-particle state. -/
lemma contDiff_slotState1 {n : ℕ} {Φ : X (n + 1) → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ)
    (i : Fin (n + 1)) (r : X n) : ContDiff ℝ (⊤ : ENat) (slotState1 i Φ r) := by
  have hfib : ContDiff ℝ (⊤ : ENat) (fun z : ℝ³ => Φ (kcInsN n i (z, r))) :=
    hΦ.comp (Work.SmallBoxBridge.Fourier.contDiff_kcInsN_right i r)
  have h : slotState1 i Φ r
      = (fun z : ℝ³ => Φ (kcInsN n i (z, r))) ∘ (fun x : X 1 => x 0) := rfl
  rw [h]
  exact hfib.comp (by fun_prop)

/-- A uniform bound for a smooth state on the compact box `abox N ℓ`. -/
lemma exists_abs_bound_abox {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : X N → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ENat) Φ) : ∃ S : ℝ, 0 ≤ S ∧ ∀ x ∈ abox N ℓ, |Φ x| ≤ S := by
  obtain ⟨C, hC⟩ := (abox_compact N hℓ).exists_bound_of_continuousOn hΦ.continuous.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
  have h := hC x hx
  rw [Real.norm_eq_abs] at h
  exact le_trans h (le_max_left _ _)

/-- `∫ z in acube ℓ, c = ℓ^3 * c`. -/
lemma setIntegral_acube_const (ℓ : ℝ) (hℓ : 0 ≤ ℓ) (c : ℝ) :
    ∫ z in acube ℓ, c = ℓ ^ 3 * c := by
  rw [MeasureTheory.setIntegral_const, Measure.real_def, acube_volume ℓ hℓ,
    ENNReal.toReal_ofReal (by positivity), smul_eq_mul]

/-! ## 2. The excited count of a slot fibre -/

/-- Continuity of the excited count of the slot fibre in the configuration `r`. -/
lemma continuous_cnPlus_slotState1 {ℓ : ℝ} (hℓ : 0 < ℓ) (n : ℕ)
    (Φ : X (n + 1) → ℝ) (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (i : Fin (n + 1)) :
    Continuous (fun r : X n => cnPlus ℓ (slotState1 i Φ r)) := by
  rw [show (fun r : X n => cnPlus ℓ (slotState1 i Φ r))
      = fun r : X n => ∫ z in acube ℓ, (Φ (kcInsN n i (z, r))
            - (ℓ ^ 3)⁻¹ * ∫ w in acube ℓ, Φ (kcInsN n i (w, r))) ^ 2 from
    funext fun r => cnPlus_slotState1_eq hℓ n Φ i r]
  refine Commons.Analysis.Calculus.continuous_setIntegral_isCompact (acube_compact hℓ) ?_
  have h1 : Continuous (fun q : X n × ℝ³ => Φ (kcInsN n i (q.2, q.1))) :=
    hΦ.continuous.comp ((kcInsN_cont i).comp (continuous_snd.prodMk continuous_fst))
  have hmean : Continuous (fun r : X n => (ℓ ^ 3)⁻¹ *
      ∫ w in acube ℓ, Φ (kcInsN n i (w, r))) :=
    (Commons.Analysis.Calculus.continuous_setIntegral_isCompact (acube_compact hℓ) h1).const_mul _
  exact (h1.sub (hmean.comp continuous_fst)).pow 2

/-- The absolute bound for the excited count of a slot fibre on the box. -/
lemma abs_cnPlus_slotState1_le {ℓ : ℝ} (hℓ : 0 < ℓ) (n : ℕ) (Φ : X (n + 1) → ℝ)
    (hΦ : ContDiff ℝ (⊤ : ENat) Φ) {S : ℝ} (hS : ∀ x ∈ abox (n + 1) ℓ, |Φ x| ≤ S) (hS0 : 0 ≤ S)
    (i : Fin (n + 1)) {r : X n} (hr : r ∈ abox n ℓ) :
    |cnPlus ℓ (slotState1 i Φ r)| ≤ ℓ ^ 3 * (2 * S) ^ 2 := by
  rw [cnPlus_slotState1_eq hℓ n Φ i r]
  set M : ℝ := (ℓ ^ 3)⁻¹ * ∫ w in acube ℓ, Φ (kcInsN n i (w, r)) with hM
  have hfibcont : Continuous (fun w : ℝ³ => Φ (kcInsN n i (w, r))) :=
    hΦ.continuous.comp ((kcInsN_cont i).comp (continuous_id.prodMk continuous_const))
  -- the box mean is bounded by `S`
  have hIntAbs : IntegrableOn (fun w : ℝ³ => |Φ (kcInsN n i (w, r))|) (acube ℓ) volume :=
    ContinuousOn.integrableOn_compact (acube_compact hℓ) hfibcont.abs.continuousOn
  have hIntConst : IntegrableOn (fun _ : ℝ³ => S) (acube ℓ) volume :=
    MeasureTheory.integrableOn_const (C := S)
      (by rw [acube_volume ℓ hℓ.le]; exact ENNReal.ofReal_ne_top)
      (by rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_ne_top)
  have hIntBound : (∫ w in acube ℓ, |Φ (kcInsN n i (w, r))|) ≤ ∫ w in acube ℓ, S :=
    setIntegral_mono_on hIntAbs hIntConst (acube_measurable ℓ)
      (fun w hw => hS _ (kcInsN_mem_abox i hr hw))
  have hMabs : |M| ≤ S := by
    rw [hM, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (ℓ ^ 3)⁻¹)]
    calc (ℓ ^ 3)⁻¹ * |∫ w in acube ℓ, Φ (kcInsN n i (w, r))|
        ≤ (ℓ ^ 3)⁻¹ * ∫ w in acube ℓ, |Φ (kcInsN n i (w, r))| :=
          mul_le_mul_of_nonneg_left MeasureTheory.abs_integral_le_integral_abs (by positivity)
      _ ≤ (ℓ ^ 3)⁻¹ * ∫ w in acube ℓ, S := mul_le_mul_of_nonneg_left hIntBound (by positivity)
      _ = (ℓ ^ 3)⁻¹ * (ℓ ^ 3 * S) := by rw [setIntegral_acube_const ℓ hℓ.le S]
      _ = S := by field_simp
  -- the pointwise bound of the integrand
  have hpt : ∀ z ∈ acube ℓ, (Φ (kcInsN n i (z, r)) - M) ^ 2 ≤ (2 * S) ^ 2 := by
    intro z hz
    have h1 : |Φ (kcInsN n i (z, r))| ≤ S := hS _ (kcInsN_mem_abox i hr hz)
    calc (Φ (kcInsN n i (z, r)) - M) ^ 2 = |Φ (kcInsN n i (z, r)) - M| ^ 2 := (sq_abs _).symm
      _ ≤ (|Φ (kcInsN n i (z, r))| + |M|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (abs_sub _ _) 2
      _ ≤ (S + S) ^ 2 := pow_le_pow_left₀ (add_nonneg (abs_nonneg _) (abs_nonneg _))
            (add_le_add h1 hMabs) 2
      _ = (2 * S) ^ 2 := by ring
  have hIntSq : IntegrableOn (fun z : ℝ³ => (Φ (kcInsN n i (z, r)) - M) ^ 2) (acube ℓ) volume :=
    ContinuousOn.integrableOn_compact (acube_compact hℓ)
      ((hfibcont.sub continuous_const).pow 2).continuousOn
  have hIntConst2 : IntegrableOn (fun _ : ℝ³ => (2 * S) ^ 2) (acube ℓ) volume :=
    MeasureTheory.integrableOn_const (C := (2 * S) ^ 2)
      (by rw [acube_volume ℓ hℓ.le]; exact ENNReal.ofReal_ne_top)
      (by rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_ne_top)
  calc |∫ z in acube ℓ, (Φ (kcInsN n i (z, r)) - M) ^ 2|
      ≤ ∫ z in acube ℓ, |(Φ (kcInsN n i (z, r)) - M) ^ 2| :=
        MeasureTheory.abs_integral_le_integral_abs
    _ = ∫ z in acube ℓ, (Φ (kcInsN n i (z, r)) - M) ^ 2 :=
        setIntegral_congr_fun (acube_measurable ℓ) (fun z _ => abs_of_nonneg (sq_nonneg _))
    _ ≤ ∫ z in acube ℓ, (2 * S) ^ 2 :=
        setIntegral_mono_on hIntSq hIntConst2 (acube_measurable ℓ) hpt
    _ = ℓ ^ 3 * (2 * S) ^ 2 := setIntegral_acube_const ℓ hℓ.le ((2 * S) ^ 2)

/-- **Conjunct 2**: the excited count of a slot fibre is integrable against `boxMu`. -/
lemma integrable_cnPlus_slotState1 {ℓ : ℝ} (hℓ : 0 < ℓ) (n : ℕ)
    (Φ : X (n + 1) → ℝ) (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (i : Fin (n + 1)) :
    Integrable (fun r : X n => cnPlus ℓ (slotState1 i Φ r)) (boxMu n ℓ) := by
  haveI hfin : IsFiniteMeasure (boxMu n ℓ) := isFiniteMeasure_boxMu n ℓ hℓ.le
  obtain ⟨S, hS0, hS⟩ := exists_abs_bound_abox hℓ hΦ
  refine MeasureTheory.Integrable.of_bound
    (continuous_cnPlus_slotState1 hℓ n Φ hΦ i).aestronglyMeasurable (ℓ ^ 3 * (2 * S) ^ 2) ?_
  rw [boxMu, MeasureTheory.ae_restrict_iff' (abox_measurable n ℓ)]
  filter_upwards with r hr
  exact abs_cnPlus_slotState1_le hℓ n Φ hΦ hS hS0 i hr

/-! ## 3. The big-box word of a slot fibre -/

/-- **Conjunct 4**: the anchored big-box word of a slot fibre is integrable against `boxMu`. -/
lemma integrable_bigBoxWord1_slotState1 {ℓ c : ℝ} (hℓ : 0 < ℓ) (n : ℕ)
    (Φ : X (n + 1) → ℝ) (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (i : Fin (n + 1)) :
    Integrable (fun r : X n => bigBoxWord1 ℓ c (slotState1 i Φ r)) (boxMu n ℓ) := by
  haveI hfin : IsFiniteMeasure (boxMu n ℓ) := isFiniteMeasure_boxMu n ℓ hℓ.le
  obtain ⟨Kb, hKb0, hKb⟩ := bigBoxWord1_bound (ℓ := ℓ) (c := c) hℓ n hΦ
  refine MeasureTheory.Integrable.of_bound (SlotSwap.bigBoxWord1_slot_aemeas hℓ n Φ hΦ i) Kb ?_
  rw [boxMu, MeasureTheory.ae_restrict_iff' (abox_measurable n ℓ)]
  filter_upwards with r hr
  rw [Real.norm_eq_abs]
  exact hKb i r hr

/-! ## 4. The main theorem -/

theorem tBwordBInd_slotSwap_and_integrable {ℓ d b ε c : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (n : ℕ)
    (Φ : Submission.BoseGases.X (n + 1) → ℝ) (hΦ : ContDiff ℝ (⊤ : ENat) Φ)
    (hsupp : Work.BSKinetic.SuppInBox (n + 1) ℓ Φ) :
    (∫ u : EuclideanSpace ℝ (Fin 3), Work.UBBInputs8.tBwordBInd (n + 1) ℓ d ε c u Φ)
        = ∑ i : Fin (n + 1), ∫ r in Submission.BoseGases.abox n ℓ,
            ∫ u : EuclideanSpace ℝ (Fin 3),
              Work.BSKinetic.smallBoxWord1 ℓ d ε c u (Work.BSKinetic.slotState1 i Φ r)
    ∧ (∀ i : Fin (n + 1),
        MeasureTheory.Integrable (fun r : Submission.BoseGases.X n =>
            (b / (2 * ℓ ^ 2)) * Submission.BoseGases.cnPlus ℓ (Work.BSKinetic.slotState1 i Φ r))
          (Work.BSKinetic.boxMu n ℓ))
    ∧ (∀ i : Fin (n + 1),
        MeasureTheory.Integrable (fun r : Submission.BoseGases.X n =>
            ∫ u : EuclideanSpace ℝ (Fin 3),
              Work.BSKinetic.smallBoxWord1 ℓ d ε c u (Work.BSKinetic.slotState1 i Φ r))
          (Work.BSKinetic.boxMu n ℓ))
    ∧ (∀ i : Fin (n + 1),
        MeasureTheory.Integrable (fun r : Submission.BoseGases.X n =>
            Work.BSKinetic.bigBoxWord1 ℓ c (Work.BSKinetic.slotState1 i Φ r))
          (Work.BSKinetic.boxMu n ℓ)) := by
  classical
  haveI hfin : IsFiniteMeasure (boxMu n ℓ) := isFiniteMeasure_boxMu n ℓ hℓ.le
  obtain ⟨K, R, hK0, hR0, hfar, hsmall, hbig⟩ :=
    slotWord_bounds (ℓ := ℓ) (d := d) (ε := ε) (c := c) hℓ hd n Φ hΦ
  -- joint integrability of the slot word
  have hin : ∀ i : Fin (n + 1), Integrable (Function.uncurry (fun (u : ℝ³) (r : X n) =>
      smallBoxWord1 ℓ d ε c u (slotState1 i Φ r))) (volume.prod (boxMu n ℓ)) := by
    intro i
    refine Commons.Measure.Integral.integrable_uncurry_of_lintegral_le_sfinite
      (μ := volume) (ν := boxMu n ℓ)
      (f := fun (u : ℝ³) (r : X n) => smallBoxWord1 ℓ d ε c u (slotState1 i Φ r))
      (g := fun _ : X n => ENNReal.ofReal K * volume (Metric.closedBall (0 : ℝ³) R))
      (SlotSwap.joint_measurable_smallBoxWord1 hℓ hd n Φ hΦ i) ?_ ?_
    · rw [MeasureTheory.lintegral_const, boxMu, Measure.restrict_apply_univ]
      exact ENNReal.mul_ne_top
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (MeasureTheory.measure_closedBall_lt_top (x := (0 : ℝ³)) (r := R)).ne)
        (abox_lt_top n ℓ hℓ.le).ne
    · rw [boxMu, MeasureTheory.ae_restrict_iff' (abox_measurable n ℓ)]
      filter_upwards with r hr
      calc ∫⁻ u, ENNReal.ofReal ‖smallBoxWord1 ℓ d ε c u (slotState1 i Φ r)‖
          ≤ ∫⁻ u, ENNReal.ofReal K *
              (Metric.closedBall (0 : ℝ³) R).indicator (fun _ => (1 : ENNReal)) u := by
            apply lintegral_mono; intro u
            show ENNReal.ofReal ‖smallBoxWord1 ℓ d ε c u (slotState1 i Φ r)‖
                ≤ ENNReal.ofReal K *
                  (Metric.closedBall (0 : ℝ³) R).indicator (fun _ => (1 : ENNReal)) u
            by_cases hu : u ∈ Metric.closedBall (0 : ℝ³) R
            · rw [Set.indicator_of_mem hu, mul_one]
              exact ENNReal.ofReal_le_ofReal (by rw [Real.norm_eq_abs]; exact hsmall i r hr u)
            · rw [Set.indicator_of_notMem hu, mul_zero]
              have hu' : R < ‖u‖ := by
                have h := hu
                rw [Metric.mem_closedBall, dist_zero_right] at h
                exact not_le.mp h
              rw [hfar u hu' i r]
              simp
        _ = ENNReal.ofReal K * volume (Metric.closedBall (0 : ℝ³) R) := by
            rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            congr 1
            rw [MeasureTheory.lintegral_indicator (Metric.isClosed_closedBall.measurableSet),
              MeasureTheory.setLIntegral_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- conjunct 1: the Fubini exchange
    rw [show (∫ u : ℝ³, UBBInputs8.tBwordBInd (n + 1) ℓ d ε c u Φ)
        = ∫ u : ℝ³, ∑ i : Fin (n + 1), ∫ r in abox n ℓ,
            smallBoxWord1 ℓ d ε c u (slotState1 i Φ r) from by
      apply integral_congr_ae
      filter_upwards with u
      exact tBwordBInd_eq_slotSum hℓ hd n u Φ hΦ]
    rw [MeasureTheory.integral_finsetSum (s := Finset.univ)
      (f := fun (i : Fin (n + 1)) (u : ℝ³) => ∫ r in abox n ℓ,
        smallBoxWord1 ℓ d ε c u (slotState1 i Φ r))
      (fun i _ => ((hin i).integral_prod_left))]
    refine Finset.sum_congr rfl fun i _ => ?_
    show ∫ a : ℝ³, ∫ r, smallBoxWord1 ℓ d ε c a (slotState1 i Φ r) ∂(boxMu n ℓ)
        = ∫ r, ∫ u : ℝ³, smallBoxWord1 ℓ d ε c u (slotState1 i Φ r) ∂volume ∂(boxMu n ℓ)
    rw [MeasureTheory.integral_integral_swap (μ := volume) (ν := boxMu n ℓ) (hin i)]
  · -- conjunct 2
    intro i
    exact (integrable_cnPlus_slotState1 hℓ n Φ hΦ i).const_mul (b / (2 * ℓ ^ 2))
  · -- conjunct 3
    intro i
    exact (hin i).integral_prod_right
  · -- conjunct 4
    intro i
    exact integrable_bigBoxWord1_slotState1 hℓ n Φ hΦ i

end Work.BSKinetic
