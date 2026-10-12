import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.FRK.windowDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.FRK.windowState` — the state of the windowed high-momentum split

The vocabulary of `Work.BoseBoxFock.FRK.windowHigh_le` (the S1 leaf of the FRK design): the
windowed mean-free state `winState ℓ ψ = χ_Λ · 1_Λ(Qψ)` written as a product of the cutoff
`winChi ℓ = χ_Λ` and the *localised* mean-free state `winU ℓ ψ = 1_Λ(Qψ)`, together with the
elementary membership facts used by the assembly:

* `winState_eq_winChi_mul_winU` — the product decomposition (the cutoff vanishes off the box, so
  the indicator is invisible);
* `integrable_winU`, `integrable_winU_sq` — the localised mean-free state is `L¹ ∩ L²`;
* `gapBare_eq_integral_winU` — `gapBare ℓ 0 ψ = ∫_z ‖winU ℓ ψ z‖²`;
* `momForm_eq_winU` — `momForm ℓ d 0 ψ` is the high-momentum mass of `winU ℓ ψ`;
* `winChi_sq_le` — the sharp pointwise bound `‖χ_Λ‖² ≤ 48/π` (`chi_sq_bounds`).
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock.FRK

local notation "E3" => EuclideanSpace ℝ (Fin 3)


/-! ## 1. The windowed mean-free state as a product `χ_Λ · 1_Λ(Qψ)` -/

/-- The cutoff factor `χ_Λ` of `winState`, as a complex function. -/
noncomputable def winChi (ℓ : ℝ) : E3 → ℂ :=
  fun z => ((Submission.BoseGases.chiScale ℓ z : ℝ) : ℂ)

/-- The localised mean-free state `1_{Λ}(Qψ)`, as a complex function. -/
noncomputable def winU (ℓ : ℝ) (ψ : E3 → ℝ) : E3 → ℂ :=
  Work.BoseKinLoc.Momentum.statU ℓ 0 ψ

lemma winChi_apply (ℓ : ℝ) (z : E3) :
    winChi ℓ z = ((Submission.BoseGases.chiScale ℓ z : ℝ) : ℂ) := rfl

lemma winU_apply (ℓ : ℝ) (ψ : E3 → ℝ) (z : E3) :
    winU ℓ ψ z = ((Work.BoseKinLoc.indU ℓ 0 z : ℝ) : ℂ) *
      ((Work.BoseKinLoc.Qfree ℓ 0 ψ z : ℝ) : ℂ) := rfl

/-- **`winState` is the product `χ_Λ · 1_Λ(Qψ)`.**  The only point to check is that `χ_Λ` vanishes
off the box, so that the indicator in `1_Λ(Qψ)` is invisible. -/
lemma winState_eq_winChi_mul_winU {ℓ : ℝ} (hℓ : 0 < ℓ) (ψ : E3 → ℝ) :
    Work.BoseBoxFock.winState ℓ ψ = fun z => winChi ℓ z * winU ℓ ψ z := by
  rw [← Work.BoseBoxFock.winState_eq]
  funext z
  rw [winU_apply, winChi_apply]
  by_cases hz : Submission.BoseGases.chiScale ℓ z = 0
  · have hb : Work.BSKinetic.bsWin ℓ 0 z = 0 := by
      have h : Work.BSKinetic.bsWin ℓ 0 z = Submission.BoseGases.chiScale ℓ z := by
        simp [Work.BSKinetic.bsWin]
      rw [h, hz]
    simp [hb, hz]
  · have hmem : z ∈ Submission.BoseGases.acube ℓ :=
      Submission.BoseGases.chiScale_mem_acube hℓ hz
    have hb : Work.BSKinetic.bsWin ℓ 0 z = Submission.BoseGases.chiScale ℓ z := by
      simp [Work.BSKinetic.bsWin]
    have hind : Work.BoseKinLoc.indU ℓ 0 z = 1 := by
      have hz' : z ∈ Work.BoseKinLoc.lamBox ℓ 0 := by
        simpa [Work.BoseKinLoc.lamBox, Work.BSKinetic.bsBox] using hmem
      simp [Work.BoseKinLoc.indU, hz']
    rw [hb, hind]
    simp only [Complex.ofReal_one, one_mul, Work.BoseKinLoc.Qfree]

/-! ## 2. Membership of the localised mean-free state -/

lemma measurableSet_acube (ℓ : ℝ) : MeasurableSet (Submission.BoseGases.acube ℓ) :=
  Submission.BoseGases.acube_measurable ℓ

lemma volume_acube_lt_top {ℓ : ℝ} (hℓ : 0 < ℓ) :
    volume (Submission.BoseGases.acube ℓ) < ⊤ :=
  (Submission.BoseGases.acube_compact hℓ).measure_lt_top

lemma measurableSet_lamBox_zero (ℓ : ℝ) :
    MeasurableSet (Work.BoseKinLoc.lamBox ℓ (0 : E3)) := by
  have h : Work.BoseKinLoc.lamBox ℓ 0 = Submission.BoseGases.acube ℓ := by
    ext x
    simp [Work.BoseKinLoc.lamBox, Work.BSKinetic.bsBox]
  rw [h]
  exact measurableSet_acube ℓ

lemma winU_support_subset (ℓ : ℝ) (ψ : E3 → ℝ) :
    Function.support (winU ℓ ψ) ⊆ Submission.BoseGases.acube ℓ := by
  intro z hz
  by_contra hmem
  have hind : Work.BoseKinLoc.indU ℓ 0 z = 0 := by
    have hz' : z ∉ Work.BoseKinLoc.lamBox ℓ 0 := by
      simpa [Work.BoseKinLoc.lamBox, Work.BSKinetic.bsBox] using hmem
    simp [Work.BoseKinLoc.indU, hz']
  simp [winU_apply, hind] at hz

lemma measurable_winU {ℓ : ℝ} {ψ : E3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    Measurable (winU ℓ ψ) := by
  rw [show winU ℓ ψ = fun z => ((Work.BoseKinLoc.indU ℓ 0 z : ℝ) : ℂ) *
      ((Work.BoseKinLoc.Qfree ℓ 0 ψ z : ℝ) : ℂ) from rfl]
  refine Measurable.mul ?_ ?_
  · exact Complex.continuous_ofReal.measurable.comp
      (measurable_const.indicator (measurableSet_lamBox_zero ℓ))
  · refine Complex.continuous_ofReal.measurable.comp ?_
    change Measurable (fun z : E3 => ψ z - Work.BSKinetic.bsMean ℓ 0 ψ)
    exact (hψ.continuous.sub continuous_const).measurable

lemma norm_ofReal_complex (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| := by
  have h1 : ‖((r : ℝ) : ℂ)‖ ^ 2 = r ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_ofReal]
    ring
  calc ‖((r : ℝ) : ℂ)‖ = Real.sqrt (‖((r : ℝ) : ℂ)‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (r ^ 2) := by rw [h1]
    _ = |r| := Real.sqrt_sq_eq_abs r

/-- The localised mean-free state is bounded: on the box it is `ψ − ⨍ψ` with `ψ` continuous on a
compact set, and off the box it vanishes. -/
lemma exists_bound_winU {ℓ : ℝ} (hℓ : 0 < ℓ) {ψ : E3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : E3, ‖winU ℓ ψ z‖ ≤ M := by
  obtain ⟨Mψ, hMψ⟩ := (Submission.BoseGases.acube_compact hℓ).exists_bound_of_continuousOn
    hψ.continuous.continuousOn
  have hMψ0 : 0 ≤ Mψ :=
    le_trans (norm_nonneg _) (hMψ 0 (Submission.BoseGases.mem_acube_of_norm_le hℓ.le
      (by rw [norm_zero]; linarith)))
  refine ⟨|Mψ| + |Work.BSKinetic.bsMean ℓ 0 ψ|, by positivity, fun z => ?_⟩
  by_cases hmem : z ∈ Submission.BoseGases.acube ℓ
  · have hind : Work.BoseKinLoc.indU ℓ 0 z = 1 := by
      have hz' : z ∈ Work.BoseKinLoc.lamBox ℓ 0 := by
        simpa [Work.BoseKinLoc.lamBox, Work.BSKinetic.bsBox] using hmem
      simp [Work.BoseKinLoc.indU, hz']
    have hQ : Work.BoseKinLoc.Qfree ℓ 0 ψ z = ψ z - Work.BSKinetic.bsMean ℓ 0 ψ := rfl
    rw [winU_apply, hind, hQ, Complex.ofReal_one, one_mul, norm_ofReal_complex]
    have h := hMψ z hmem
    rw [Real.norm_eq_abs] at h
    have h2 : |ψ z - Work.BSKinetic.bsMean ℓ 0 ψ|
        ≤ |ψ z| + |Work.BSKinetic.bsMean ℓ 0 ψ| := by
      simpa [sub_eq_add_neg] using abs_add_le (ψ z) (-(Work.BSKinetic.bsMean ℓ 0 ψ))
    have h3 : |ψ z| ≤ |Mψ| := le_trans h (le_abs_self Mψ)
    linarith
  · have hind : Work.BoseKinLoc.indU ℓ 0 z = 0 := by
      have hz' : z ∉ Work.BoseKinLoc.lamBox ℓ 0 := by
        simpa [Work.BoseKinLoc.lamBox, Work.BSKinetic.bsBox] using hmem
      simp [Work.BoseKinLoc.indU, hz']
    rw [winU_apply, hind]
    simp only [Complex.ofReal_zero, zero_mul, norm_zero]
    have h3 := abs_nonneg (Work.BSKinetic.bsMean ℓ 0 ψ)
    have h4 := abs_nonneg Mψ
    linarith

lemma integrable_winU {ℓ : ℝ} (hℓ : 0 < ℓ) {ψ : E3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    Integrable (winU ℓ ψ) := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_winU hℓ hψ
  rw [← integrableOn_iff_integrable_of_support_subset (winU_support_subset ℓ ψ)]
  refine IntegrableOn.of_bound (volume_acube_lt_top hℓ) ?_ M ?_
  · exact (measurable_winU hψ).aestronglyMeasurable
  · filter_upwards with z
    exact hM z

lemma winU_norm_sq (ℓ : ℝ) (ψ : E3 → ℝ) (z : E3) :
    ‖winU ℓ ψ z‖ ^ 2 = (Work.BoseKinLoc.indU ℓ 0 z) ^ 2
      * (Work.BoseKinLoc.Qfree ℓ 0 ψ z) ^ 2 := by
  rw [winU_apply, norm_mul, norm_ofReal_complex, norm_ofReal_complex, mul_pow, sq_abs, sq_abs]

lemma integrable_winU_sq {ℓ : ℝ} (hℓ : 0 < ℓ) {ψ : E3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    Integrable (fun z : E3 => ‖winU ℓ ψ z‖ ^ 2) := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_winU hℓ hψ
  have hsupp : Function.support (fun z : E3 => ‖winU ℓ ψ z‖ ^ 2)
      ⊆ Submission.BoseGases.acube ℓ := by
    intro z hz
    refine winU_support_subset ℓ ψ ?_
    simpa [Function.mem_support] using hz
  rw [← integrableOn_iff_integrable_of_support_subset hsupp]
  refine IntegrableOn.of_bound (volume_acube_lt_top hℓ) ?_ (M ^ 2) ?_
  · exact ((measurable_winU hψ).norm.pow_const 2).aestronglyMeasurable
  · filter_upwards with z
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hM z) 2

/-- The bare mean-free box mass is the squared norm of the localised mean-free state. -/
lemma gapBare_eq_integral_winU {ℓ : ℝ} (hℓ : 0 < ℓ) (ψ : E3 → ℝ) :
    Work.BoseKinLoc.gapBare ℓ 0 ψ = ∫ z : E3, ‖winU ℓ ψ z‖ ^ 2 := by
  have hset : Work.BoseKinLoc.lamBox ℓ 0 = Submission.BoseGases.acube ℓ := by
    ext x
    simp [Work.BoseKinLoc.lamBox, Work.BSKinetic.bsBox]
  have hpoint : ∀ z : E3, ‖winU ℓ ψ z‖ ^ 2
      = (Submission.BoseGases.acube ℓ).indicator
          (fun z => (Work.BoseKinLoc.Qfree ℓ 0 ψ z) ^ 2) z := by
    intro z
    rw [winU_norm_sq]
    by_cases hz : z ∈ Submission.BoseGases.acube ℓ
    · have hind : Work.BoseKinLoc.indU ℓ 0 z = 1 := by
        have hz' : z ∈ Work.BoseKinLoc.lamBox ℓ 0 := by
          rw [hset]; exact hz
        simp [Work.BoseKinLoc.indU, hz']
      simp [Set.indicator_of_mem hz, hind]
    · have hind : Work.BoseKinLoc.indU ℓ 0 z = 0 := by
        have hz' : z ∉ Work.BoseKinLoc.lamBox ℓ 0 := by
          rw [hset]; exact hz
        simp [Work.BoseKinLoc.indU, hz']
      simp [Set.indicator_of_notMem hz, hind]
  rw [Work.BoseKinLoc.gapBare, hset]
  calc (∫ z in Submission.BoseGases.acube ℓ, (Work.BoseKinLoc.Qfree ℓ 0 ψ z) ^ 2)
      = ∫ z : E3, (Submission.BoseGases.acube ℓ).indicator
          (fun z => (Work.BoseKinLoc.Qfree ℓ 0 ψ z) ^ 2) z :=
        (integral_indicator (measurableSet_acube ℓ)).symm
    _ = ∫ z : E3, ‖winU ℓ ψ z‖ ^ 2 := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        exact (hpoint z).symm

/-- `momForm` is the high-momentum mass of the localised mean-free state. -/
lemma momForm_eq_winU (ℓ d : ℝ) (ψ : E3 → ℝ) :
    Work.BoseKinLoc.momForm ℓ d 0 ψ
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3,
          (if (d ^ 2 * ℓ)⁻¹ < ‖p‖ then (1 : ℝ) else 0) *
            ‖Submission.BoseGases.kinFT (winU ℓ ψ) p‖ ^ 2 := by
  rfl

/-- The pointwise bound on the cutoff factor: `χ_Λ² ≤ 48/π`. -/
lemma winChi_sq_le (ℓ : ℝ) (z : E3) : ‖winChi ℓ z‖ ^ 2 ≤ 48 / Real.pi := by
  have h := (Work.BoseBoxFock.chi_sq_bounds.2) (ℓ⁻¹ • z)
  rw [winChi_apply, norm_ofReal_complex, sq_abs]
  simpa [Submission.BoseGases.chiScale] using h

lemma winChi_apply_bound (ℓ : ℝ) (z : E3) : ‖winChi ℓ z‖ ^ 2 ≤ (48 / Real.pi) :=
  winChi_sq_le ℓ z

/-- The cutoff factor is supported in the box. -/
lemma winChi_support_subset {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Function.support (winChi ℓ) ⊆ Submission.BoseGases.acube ℓ := by
  intro z hz
  refine Submission.BoseGases.chiScale_mem_acube hℓ ?_
  simpa [winChi, Function.mem_support] using hz

/-- The cutoff factor is smooth. -/
lemma contDiff_winChi {ℓ : ℝ} (hℓ : ℓ ≠ 0) : ContDiff ℝ (⊤ : ℕ∞) (winChi ℓ) := by
  rw [show winChi ℓ = fun z : E3 => ((Submission.BoseGases.chiScale ℓ z : ℝ) : ℂ) from rfl]
  exact Complex.ofRealCLM.contDiff.comp (Submission.BoseGases.chiScale_contDiff hℓ)

/-- Pointwise sup bound on the cutoff factor: `‖χ_Λ‖ ≤ √(48/π)`. -/
lemma winChi_norm_le (ℓ : ℝ) (z : E3) : ‖winChi ℓ z‖ ≤ Real.sqrt (48 / Real.pi) := by
  rw [← Real.sqrt_sq (norm_nonneg _)]
  exact Real.sqrt_le_sqrt (winChi_sq_le ℓ z)

/-- The cutoff factor times an `L¹` function is `L¹`. -/
lemma integrable_winChi_mul {ℓ : ℝ} {h : E3 → ℂ} (hh : Integrable h) :
    Integrable (fun z : E3 => winChi ℓ z * h z) := by
  have hm : AEStronglyMeasurable (fun z : E3 => winChi ℓ z * h z) volume :=
    (Complex.continuous_ofReal.measurable.comp
      (Submission.BoseGases.chiScale_continuous ℓ).measurable).aestronglyMeasurable.mul
        hh.aestronglyMeasurable
  refine Integrable.mono' (g := fun z : E3 => Real.sqrt (48 / Real.pi) * ‖h z‖)
    (hh.norm.const_mul _) hm ?_
  filter_upwards with z
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (winChi_norm_le ℓ z) (norm_nonneg _)

/-- The squared norm of `χ_Λ` times an `L²` function is integrable. -/
lemma integrable_normSq_winChi_mul {ℓ : ℝ} {h : E3 → ℂ}
    (h2 : Integrable (fun z : E3 => ‖h z‖ ^ 2)) :
    Integrable (fun z : E3 => ‖winChi ℓ z * h z‖ ^ 2) := by
  have hbase : Integrable (fun z : E3 => ‖winChi ℓ z‖ ^ 2 * ‖h z‖ ^ 2) := by
    have hm : AEMeasurable (fun z : E3 => ‖winChi ℓ z‖ ^ 2 * ‖h z‖ ^ 2) volume :=
      (((Complex.continuous_ofReal.comp
        (Submission.BoseGases.chiScale_continuous ℓ)).norm.pow 2).aemeasurable).mul
          h2.aemeasurable
    refine Integrable.mono' (g := fun z : E3 => (48 / Real.pi) * ‖h z‖ ^ 2)
      (h2.const_mul _) hm.aestronglyMeasurable ?_
    filter_upwards with z
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_right (winChi_sq_le ℓ z) (sq_nonneg _)
  refine hbase.congr ?_
  filter_upwards with z
  rw [norm_mul, mul_pow]

/-- `‖(c : ℂ) · z‖² = c²‖z‖²` for `c ≥ 0`. -/
lemma norm_mul_ofReal_sq {c : ℝ} (hc : 0 ≤ c) (z : ℂ) :
    ‖(c : ℂ) * z‖ ^ 2 = c ^ 2 * ‖z‖ ^ 2 := by
  rw [norm_mul, norm_ofReal_complex, abs_of_nonneg hc]
  ring

/-- `‖1 - (r : ℂ)‖² ≤ 1` for `0 ≤ r ≤ 1`. -/
lemma norm_one_sub_ofReal_sq_le {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    ‖(1 : ℂ) - (r : ℂ)‖ ^ 2 ≤ 1 := by
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, norm_ofReal_complex, sq_abs]
  nlinarith

/-- **The asymmetric `(x+y)²` splitting at the level of integrals**: for `L²` functions `F`, `G`
and a measurable set `T`,

    `∫_T ‖F + G‖² ≤ 5 ∫_T ‖F‖² + (5/4) ∫_T ‖G‖²`,

from the pointwise `(x+y)² ≤ 5x² + (5/4)y²` (which is `(2x - y/2)² + x² ≥ 0`). -/
theorem integral_norm_add_sq_le {T : Set E3} (hT : MeasurableSet T) {F G : E3 → ℂ}
    (hF : Integrable (fun p : E3 => ‖F p‖ ^ 2))
    (hG : Integrable (fun p : E3 => ‖G p‖ ^ 2)) :
    ∫ p in T, ‖F p + G p‖ ^ 2
      ≤ 5 * (∫ p in T, ‖F p‖ ^ 2) + (5 / 4) * (∫ p in T, ‖G p‖ ^ 2) := by
  have hpt : ∀ p : E3, (T.indicator (fun p : E3 => ‖F p + G p‖ ^ 2)) p
      ≤ 5 * (T.indicator (fun p : E3 => ‖F p‖ ^ 2)) p
        + (5 / 4) * (T.indicator (fun p : E3 => ‖G p‖ ^ 2)) p := by
    intro p
    by_cases hp : p ∈ T
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp, Set.indicator_of_mem hp]
      have h3 : ‖F p + G p‖ ^ 2 ≤ (‖F p‖ + ‖G p‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (F p) (G p)) 2
      have h4 : (‖F p‖ + ‖G p‖) ^ 2 ≤ 5 * ‖F p‖ ^ 2 + (5 / 4) * ‖G p‖ ^ 2 := by
        nlinarith [sq_nonneg (2 * ‖F p‖ - ‖G p‖ / 2)]
      linarith
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp, Set.indicator_of_notMem hp]
      norm_num
  have hgi : Integrable (fun p : E3 => 5 * (T.indicator (fun p : E3 => ‖F p‖ ^ 2)) p
      + (5 / 4) * (T.indicator (fun p : E3 => ‖G p‖ ^ 2)) p) :=
    ((hF.indicator hT).const_mul 5).add ((hG.indicator hT).const_mul (5 / 4))
  have h1 : ∫ p : E3, (T.indicator (fun p : E3 => ‖F p + G p‖ ^ 2)) p
      ≤ ∫ p : E3, (5 * (T.indicator (fun p : E3 => ‖F p‖ ^ 2)) p
          + (5 / 4) * (T.indicator (fun p : E3 => ‖G p‖ ^ 2)) p) :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun p => by
      show (0 : ℝ) ≤ (T.indicator (fun p : E3 => ‖F p + G p‖ ^ 2)) p
      by_cases hp : p ∈ T
      · rw [Set.indicator_of_mem hp]; exact sq_nonneg _
      · rw [Set.indicator_of_notMem hp]) hgi (Filter.Eventually.of_forall hpt)
  have h2 : ∫ p : E3, (5 * (T.indicator (fun p : E3 => ‖F p‖ ^ 2)) p
      + (5 / 4) * (T.indicator (fun p : E3 => ‖G p‖ ^ 2)) p)
      = 5 * (∫ p in T, ‖F p‖ ^ 2) + (5 / 4) * (∫ p in T, ‖G p‖ ^ 2) := by
    rw [integral_add ((hF.indicator hT).const_mul 5) ((hG.indicator hT).const_mul (5 / 4)),
      integral_const_mul, integral_const_mul, integral_indicator hT, integral_indicator hT]
  rw [integral_indicator hT, h2] at h1
  exact h1

end Work.BoseBoxFock.FRK
