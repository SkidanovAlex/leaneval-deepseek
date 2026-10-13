/-
# `SlotsZeroModeKey` - the key identity `∫ Φ·(bslOp (ρ ⊗ e_m))·wgt = 0` and its Fubini form

Part of `Work.FTS.StrongEps.EComparison.SlotsZeroModeODE`; see `SlotsZeroModeMain` for the
overview.  Contents:

* `integrableOn_absPhi_box` - product-measure integrability of `|Φ|` against the indicator of a
  box in the radial variable (from the per-slice integrability of `|Φ|` and its integral);
* `integrableOn_modeIntegrand` - product-measure integrability of the *un-cut* mode integrand
  `Φ·(bslOp (ρ ⊗ e_m))·z^((5-α)/α)cos θ`;
* `layer_integral_eq` - Fubini: the product-measure integral of the layer density equals the
  iterated one;
* `key_set` - the vanishing of `∫_{Q0} Φ·(bslOp (ρ ⊗ e_m))·wgt`, obtained by comparing it with
  the cut-off identities `perN_zero` (both correction terms live in the two boundary layers);
* `key_eq_target` - the identification of that integral with the iterated integral of the
  statement.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Construction.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_Lzero
import Submission.Work.FTS.PhiStar.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.EllipticEst.ModalSolution.bslOp_ibp
import Submission.Work.FTS.ClassC.psiTrunc_uncurry_smooth
import Submission.Work.FTS.H2.ModalSolR.PerModeBasic
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroModeDefs
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroModeMain
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroModeIbp

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EComparison

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## The two measures on the quadrant -/

/-- `(0, π/2)` and `Iθ` carry the same restricted Lebesgue measure. -/
theorem restrict_Ioo_eq_Iθ :
    (volume.restrict (Set.Ioo 0 (π / 2)) : Measure ℝ) = volume.restrict Work.Spaces.Iθ := by
  refine MeasureTheory.Measure.restrict_congr_set ?_
  rw [Work.Spaces.Iθ, ae_eq_set]
  refine ⟨?_, ?_⟩
  · rw [Set.sdiff_eq_empty.mpr Set.Ioo_subset_Icc_self, measure_empty]
  · rw [Set.Icc_sdiff_Ioo_same (by linarith [Real.pi_pos] : (0 : ℝ) ≤ π / 2)]
    rw [Set.insert_eq]
    exact measure_union_null (measure_singleton 0) (measure_singleton _)

/-- The restricted measure of the quadrant is the product of the two restricted one-dimensional
measures. -/
theorem restrict_Q0_eq_prod :
    (volume.restrict Work.FTS.EllipticEst.Q0 : Measure (ℝ × ℝ))
      = ((volume : Measure ℝ).restrict (Set.Ioi 0)).prod
          ((volume : Measure ℝ).restrict (Set.Ioo 0 (π / 2))) := by
  rw [Work.FTS.EllipticEst.Q0, MeasureTheory.Measure.volume_eq_prod ℝ ℝ,
    MeasureTheory.Measure.prod_restrict]

/-! ## Integrability against the box indicator -/

theorem continuousOn_absPhi_mode {Φ : ℝ → ℝ → ℝ}
    (hsm : ∀ k : ℕ, ContDiffOn ℝ k (Function.uncurry Φ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    ContinuousOn (fun p : ℝ × ℝ => |Φ p.1 p.2|) Work.FTS.EllipticEst.Q0 :=
  ((Work.FTS.EllipticEst.smoothOpen_iff_forall Φ).mpr hsm).continuousOn.abs

/-- **Product-measure integrability of `|Φ|` against a box indicator in `z`.** -/
theorem integrableOn_absPhi_box {Φ : ℝ → ℝ → ℝ} {a b : ℝ}
    (hsm : ∀ k : ℕ, ContDiffOn ℝ k (Function.uncurry Φ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hΦint : ∀ z ∈ Set.Ioi (0 : ℝ), MeasureTheory.IntegrableOn (fun θ => |Φ z θ|) Work.Spaces.Iθ)
    (hEint : MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, |Φ z θ|)
      (Set.Icc a b)) :
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => |Φ p.1 p.2|
      * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1) Work.FTS.EllipticEst.Q0 := by
  rw [MeasureTheory.IntegrableOn, restrict_Q0_eq_prod]
  refine (MeasureTheory.integrable_prod_iff ?_).mpr ⟨?_, ?_⟩
  · -- a.e. strong measurability
    have hcont := (continuousOn_absPhi_mode hsm).aestronglyMeasurable
      (μ := volume) Work.FTS.EllipticEst.isOpen_Q0.measurableSet
    rw [← restrict_Q0_eq_prod]
    exact hcont.mul (Measurable.aestronglyMeasurable
      (measurable_const.indicator measurableSet_Icc |>.comp measurable_fst))
  · -- the per-slice integrability
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun z hz => ?_
    have h1 := (hΦint z hz).integrable
    rw [← restrict_Ioo_eq_Iθ] at h1
    have h2 := h1.const_mul ((Set.Icc a b).indicator (fun _ => (1 : ℝ)) z)
    refine h2.congr (Eventually.of_forall fun y => ?_)
    show (Set.Icc a b).indicator (fun _ => (1 : ℝ)) z * |Φ z y|
      = |Φ z y| * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) z
    ring
  · -- the outer integrability
    have hEq : (fun z : ℝ => ∫ θ, ‖|Φ z θ| * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) z‖
          ∂((volume : Measure ℝ).restrict (Set.Ioo 0 (π / 2))))
        = fun z => (Set.Icc a b).indicator (fun _ => (1 : ℝ)) z
            * ∫ θ in Work.Spaces.Iθ, |Φ z θ| := by
      funext z
      rw [show (fun θ => ‖|Φ z θ| * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) z‖)
          = fun θ => (Set.Icc a b).indicator (fun _ => (1 : ℝ)) z * |Φ z θ| from by
        funext θ
        rw [Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (indicator_one_nonneg z), abs_abs, mul_comm]]
      rw [MeasureTheory.integral_const_mul, ← restrict_Ioo_eq_Iθ]
    rw [hEq]
    have h3 : MeasureTheory.Integrable ((Set.Icc a b).indicator
        (fun z => ∫ θ in Work.Spaces.Iθ, |Φ z θ|)) volume :=
      hEint.integrable_indicator measurableSet_Icc
    have h4 : MeasureTheory.Integrable ((Set.Icc a b).indicator
        (fun z => ∫ θ in Work.Spaces.Iθ, |Φ z θ|)) (volume.restrict (Set.Ioi 0)) :=
      h3.mono_measure MeasureTheory.Measure.restrict_le_self
    refine h4.congr (Eventually.of_forall fun z => ?_)
    show (Set.Icc a b).indicator (fun z => ∫ θ in Work.Spaces.Iθ, |Φ z θ|) z
      = (Set.Icc a b).indicator (fun _ => (1 : ℝ)) z
        * ∫ θ in Work.Spaces.Iθ, |Φ z θ|
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases hz : z ∈ Set.Icc a b <;> simp [hz]

/-! ## Derivatives of a function vanishing near a point -/

/-- If `f` vanishes in a neighbourhood of `z`, then so do its first two derivatives at `z`. -/
theorem deriv_deriv_eq_zero_of_eventuallyEq_zero {f : ℝ → ℝ} {z : ℝ} (h : f =ᶠ[𝓝 z] 0) :
    deriv f z = 0 ∧ deriv (deriv f) z = 0 := by
  obtain ⟨V, hVf, hVopen, hzV⟩ := mem_nhds_iff.mp h
  have hVeq : f =ᶠ[𝓝 z] (fun _ => 0) := Filter.mem_of_superset (hVopen.mem_nhds hzV) hVf
  have h1 : deriv f z = 0 := by
    rw [Filter.EventuallyEq.deriv_eq hVeq]
    simp
  have hd : deriv f =ᶠ[𝓝 z] (fun _ : ℝ => 0) := by
    filter_upwards [hVopen.mem_nhds hzV] with y hy
    have hyeq : f =ᶠ[𝓝 y] (fun _ => 0) := Filter.mem_of_superset (hVopen.mem_nhds hy) hVf
    rw [Filter.EventuallyEq.deriv_eq hyeq]
    simp
  have h2 : deriv (deriv f) z = 0 := by
    rw [Filter.EventuallyEq.deriv_eq hd]
    simp
  exact ⟨h1, h2⟩

/-! ## The pointwise bounds on the two factors of the mode integrand -/

/-- A bound on the Dirichlet eigenfunction on `Iθ`. -/
theorem exists_bound_eFam (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Work.Spaces.Iθ,
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((Work.FTS.ClassC.contDiff_eFam_nat m 0).continuous.continuousOn)
  refine ⟨max C 0, le_max_right _ _, fun θ hθ => ?_⟩
  have h2 := hC θ hθ
  rw [Real.norm_eq_abs] at h2
  exact h2.trans (le_max_left _ _)

/-- The mode coefficient of `ρ` is bounded by a constant times the box indicator (it vanishes off
the support of `ρ`). -/
theorem exists_bound_modeCoef {α : ℝ} {ρ : ℝ → ℝ} {m : ℕ} (hρ : ∀ k : ℕ, ContDiff ℝ k ρ)
    {a b : ℝ} (hsub : tsupport ρ ⊆ Set.Icc a b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ,
      |Work.FTS.PhiStar.Gegenbauer.lam m * ρ z - radOp α ρ z|
        ≤ C * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) z := by
  have hd1 : Continuous (deriv ρ) := (hρ 2).continuous_deriv (by norm_num)
  have hd2 : Continuous (deriv (deriv ρ)) := by
    have h := (hρ 2).continuous_iteratedDeriv' 2
    simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using h
  have hc : Continuous (fun z : ℝ => Work.FTS.PhiStar.Gegenbauer.lam m * ρ z - radOp α ρ z) := by
    change Continuous (fun z : ℝ => Work.FTS.PhiStar.Gegenbauer.lam m * ρ z
      - (α ^ 2 * z ^ 2 * deriv (deriv ρ) z + α * (5 + α) * z * deriv ρ z))
    exact (continuous_const.mul (hρ 0).continuous).sub
      (((continuous_const.mul (continuous_id.pow 2)).mul hd2).add
        ((continuous_const.mul continuous_id).mul hd1))
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun z => ?_⟩
  by_cases hz : z ∈ Set.Icc a b
  · rw [Set.indicator_of_mem hz, mul_one]
    have h2 := hC z hz
    rw [Real.norm_eq_abs] at h2
    exact h2.trans (le_max_left _ _)
  · rw [Set.indicator_of_notMem hz, mul_zero]
    have hev : ρ =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.mp fun h => hz (hsub h)
    obtain ⟨h1, h2⟩ := deriv_deriv_eq_zero_of_eventuallyEq_zero hev
    have hρz : ρ z = 0 := image_eq_zero_of_notMem_tsupport fun h => hz (hsub h)
    simp only [radOp, hρz, h1, h2, mul_zero]
    norm_num

/-- **The bound on `bslOp α (ρ ⊗ e_m)`**: a constant times the box indicator in `z`. -/
theorem exists_bound_bslOp_Psi {α : ℝ} {ρ : ℝ → ℝ} {m : ℕ} (hρ : ∀ k : ℕ, ContDiff ℝ k ρ)
    {a b : ℝ} (hsub : tsupport ρ ⊆ Set.Icc a b) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p : ℝ × ℝ, p ∈ Work.FTS.EllipticEst.Q0 →
      |Work.Elliptic.bslOp α (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
          p.1 p.2| ≤ B * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1 := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_bound_modeCoef (α := α) hρ hsub
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_bound_eFam m
  refine ⟨C₁ * C₂, mul_nonneg hC₁0 hC₂0, fun p hp => ?_⟩
  have hcos : Real.cos p.2 ≠ 0 := by
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩)
  rw [bslOp_sepMode (α := α) hcos, abs_mul]
  calc |Work.FTS.PhiStar.Gegenbauer.lam m * ρ p.1 - radOp α ρ p.1|
        * |Work.FTS.PhiStar.Gegenbauer.eFam m p.2|
      ≤ (C₁ * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1) * C₂ := by
        refine mul_le_mul (hC₁ p.1) ?_ (abs_nonneg _)
          (mul_nonneg hC₁0 (indicator_one_nonneg p.1))
        exact hC₂ p.2 ⟨(Work.FTS.EllipticEst.mem_Q0.mp hp).2.1.le,
          (Work.FTS.EllipticEst.mem_Q0.mp hp).2.2.le⟩
    _ = C₁ * C₂ * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1 := by ring

/-- **The product bound**: `|bslOp α (ρ ⊗ e_m)| · |wgt|` is bounded by a constant times the box
indicator (both factors vanish off the support box, and are bounded on it). -/
theorem abs_bslOp_mul_bslWeight_le {α : ℝ} {ρ : ℝ → ℝ} {m : ℕ}
    (hρ : ∀ k : ℕ, ContDiff ℝ k ρ) {a b : ℝ} (ha : 0 < a)
    (hsub : tsupport ρ ⊆ Set.Icc a b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℝ × ℝ, p ∈ Work.FTS.EllipticEst.Q0 →
      |Work.Elliptic.bslOp α (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
          p.1 p.2| * |bslWeight α p|
        ≤ C * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1 := by
  obtain ⟨B, hB0, hB⟩ := exists_bound_bslOp_Psi (α := α) hρ hsub
  obtain ⟨W, hW0, hW⟩ := exists_bound_bslWeight (α := α) ha
  obtain ⟨C₁, -, hC₁⟩ := exists_bound_modeCoef (α := α) hρ hsub
  refine ⟨B * W, mul_nonneg hB0 hW0, fun p hp => ?_⟩
  by_cases hpI : p.1 ∈ Set.Icc a b
  · have h1 : |Work.Elliptic.bslOp α (fun z θ => ρ z *
        Work.FTS.PhiStar.Gegenbauer.eFam m θ) p.1 p.2| ≤ B := by
      have h := hB p hp
      rwa [Set.indicator_of_mem hpI, mul_one] at h
    have h2 : |bslWeight α p| ≤ W := hW p hpI
    calc |Work.Elliptic.bslOp α (fun z θ => ρ z *
            Work.FTS.PhiStar.Gegenbauer.eFam m θ) p.1 p.2| * |bslWeight α p|
        ≤ B * W := mul_le_mul h1 h2 (abs_nonneg _) hB0
      _ = B * W * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1 := by
          rw [Set.indicator_of_mem hpI, mul_one]
  · have hcos : Real.cos p.2 ≠ 0 := by
      obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
      exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩)
    have hz0 : |Work.FTS.PhiStar.Gegenbauer.lam m * ρ p.1 - radOp α ρ p.1| = 0 := by
      have h := hC₁ p.1
      rw [Set.indicator_of_notMem hpI, mul_zero] at h
      exact le_antisymm h (abs_nonneg _)
    rw [bslOp_sepMode (α := α) hcos, abs_mul, hz0, Set.indicator_of_notMem hpI]
    simp

/-- The weight against the box indicator is bounded by a constant times the indicator. -/
theorem abs_bslWeight_mul_indicator_le {α : ℝ} {a b : ℝ} (ha : 0 < a) :
    ∃ W : ℝ, 0 ≤ W ∧ ∀ p : ℝ × ℝ,
      |bslWeight α p| * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1
        ≤ W * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1 := by
  obtain ⟨W, hW0, hW⟩ := exists_bound_bslWeight (α := α) ha
  refine ⟨W, hW0, fun p => ?_⟩
  by_cases hp : p.1 ∈ Set.Icc a b
  · simp only [Set.indicator_of_mem hp, mul_one]
    exact hW p hp
  · simp only [Set.indicator_of_notMem hp, mul_zero, le_refl]

/-! ## Integrability of the mode integrand -/

/-- **Product-measure integrability of the un-cut mode integrand**
`Φ·(bslOp (ρ ⊗ e_m))·z^((5-α)/α)cos θ`. -/
theorem integrableOn_modeIntegrand {α : ℝ} {Φ : ℝ → ℝ → ℝ} {ρ : ℝ → ℝ} {m : ℕ}
    (hsm : ∀ k : ℕ, ContDiffOn ℝ k (Function.uncurry Φ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hρ : ∀ k : ℕ, ContDiff ℝ k ρ) {a b : ℝ} (ha : 0 < a)
    (hsub : tsupport ρ ⊆ Set.Icc a b)
    (hbox : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => |Φ p.1 p.2|
      * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1) Work.FTS.EllipticEst.Q0) :
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => Φ p.1 p.2
      * Work.Elliptic.bslOp α (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) p.1 p.2
      * bslWeight α p) Work.FTS.EllipticEst.Q0 := by
  obtain ⟨C, hC0, hC⟩ := abs_bslOp_mul_bslWeight_le (α := α) hρ ha hsub
  have hψ : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mpr fun k =>
      ((Work.FTS.ClassC.contDiffOn_uncurry_fst (s := Set.Ioi 0)
          (t := Set.Ioo 0 (π / 2)) ((hρ k).contDiffOn)).mul
        (Work.FTS.ClassC.contDiffOn_uncurry_snd (s := Set.Ioi 0)
          (t := Set.Ioo 0 (π / 2)) (Work.FTS.ClassC.contDiff_eFam_nat m k)))
  refine Integrable.mono' (hbox.const_mul C) ?_ ?_
  · have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => Φ p.1 p.2)
        (volume.restrict Work.FTS.EllipticEst.Q0) :=
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall Φ).mpr hsm).continuousOn.aestronglyMeasurable
        (μ := volume) Work.FTS.EllipticEst.isOpen_Q0.measurableSet
    have h2 : AEStronglyMeasurable
        (fun p : ℝ × ℝ => Work.Elliptic.bslOp α
          (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) p.1 p.2)
        (volume.restrict Work.FTS.EllipticEst.Q0) :=
      (continuousOn_bslOp_of_smoothOpen hψ).aestronglyMeasurable
        (μ := volume) Work.FTS.EllipticEst.isOpen_Q0.measurableSet
    have h3 : AEStronglyMeasurable (fun p : ℝ × ℝ => bslWeight α p)
        (volume.restrict Work.FTS.EllipticEst.Q0) :=
      (continuousOn_weight α).aestronglyMeasurable
        (μ := volume) Work.FTS.EllipticEst.isOpen_Q0.measurableSet
    exact (h1.mul h2).mul h3
  · refine MeasureTheory.ae_restrict_of_forall_mem
      Work.FTS.EllipticEst.isOpen_Q0.measurableSet fun p hp => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    calc |Φ p.1 p.2| * |Work.Elliptic.bslOp α (fun z θ => ρ z *
          Work.FTS.PhiStar.Gegenbauer.eFam m θ) p.1 p.2| * |bslWeight α p|
        = |Φ p.1 p.2| * (|Work.Elliptic.bslOp α (fun z θ => ρ z *
            Work.FTS.PhiStar.Gegenbauer.eFam m θ) p.1 p.2| * |bslWeight α p|) := by ring
      _ ≤ |Φ p.1 p.2| * (C * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1) :=
          mul_le_mul_of_nonneg_left (hC p hp) (abs_nonneg _)
      _ = C * (|Φ p.1 p.2| * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1) := by ring

end Work.FTS.StrongEps.EComparison
