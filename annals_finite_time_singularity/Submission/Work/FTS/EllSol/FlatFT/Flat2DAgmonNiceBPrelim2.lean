/-
Copyright: work module for the Elgindi finite-time singularity project.

# Preliminaries for `flat2DAgmonNiceB`, part 2

The fixed-`θ` Plancherel data of the four slots (`g`, `∂_tg`, `∂_θg`, `∂_θ²g`), the pointwise
slice bound `‖Φ_ξ(θ)‖² ≤ 2M ∫_t φ(t,θ)²`, and the per-frequency finiteness of the angular
slots.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllSol.FlatFT.Defs
import Submission.Work.FTS.EllSol.FlatFT.Flat2DAgmonNiceBPrelim1
import Submission.Work.FTS.EllSol.FlatFT.pz_contDiffOn_succ
import Submission.Work.FTS.EllSol.FlatFT.integrable_weighted_slice1
import Submission.Work.FTS.EllSol.FlatFT.sliceContDiffOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.FlatFT

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option maxHeartbeats 1000000

/-! ## Vanishing of the profiles away from the `t`-support -/

theorem pth_eq_zero_of_lt_abs {ψ : ℝ → ℝ → ℝ} {M t θ : ℝ} (ht : M < |t|)
    (hψ : ∀ t' θ' : ℝ, M < |t'| → ψ t' θ' = 0) : Work.Spaces.pth ψ t θ = 0 := by
  have hz : (fun θ' : ℝ => ψ t θ') = fun _ => (0 : ℝ) := funext fun θ' => hψ t θ' ht
  simp only [Work.Spaces.pth]
  rw [hz]
  simp

theorem pth_pth_eq_zero_of_lt_abs {ψ : ℝ → ℝ → ℝ} {M t θ : ℝ} (ht : M < |t|)
    (hψ : ∀ t' θ' : ℝ, M < |t'| → ψ t' θ' = 0) :
    Work.Spaces.pth (Work.Spaces.pth ψ) t θ = 0 := by
  have hz : (fun θ' : ℝ => Work.Spaces.pth ψ t θ') = fun _ => (0 : ℝ) :=
    funext fun θ' => pth_eq_zero_of_lt_abs (ψ := ψ) ht hψ
  have hgoal : Work.Spaces.pth (Work.Spaces.pth ψ) t θ
      = deriv (fun θ' : ℝ => Work.Spaces.pth ψ t θ') θ := rfl
  rw [hgoal, hz]
  simp

theorem supp_pz {g : ℝ → ℝ → ℝ} {M : ℝ} (hM : ∀ t θ : ℝ, M < |t| → g t θ = 0) :
    ∀ t θ : ℝ, M < |t| → Work.Spaces.pz g t θ = 0 :=
  fun t θ ht => pz_eq_zero_of_lt_abs ht fun y hy => hM y θ hy

theorem supp_pth {g : ℝ → ℝ → ℝ} {M : ℝ} (hM : ∀ t θ : ℝ, M < |t| → g t θ = 0) :
    ∀ t θ : ℝ, M < |t| → Work.Spaces.pth g t θ = 0 :=
  fun t θ ht => pth_eq_zero_of_lt_abs ht hM

theorem supp_pzpz {g : ℝ → ℝ → ℝ} {M : ℝ} (hM : ∀ t θ : ℝ, M < |t| → g t θ = 0) :
    ∀ t θ : ℝ, M < |t| → Work.Spaces.pz (Work.Spaces.pz g) t θ = 0 :=
  fun t θ ht => pz_eq_zero_of_lt_abs ht fun y hy =>
    pz_eq_zero_of_lt_abs hy fun z hz => hM z θ hz

theorem supp_pzpth {g : ℝ → ℝ → ℝ} {M : ℝ} (hM : ∀ t θ : ℝ, M < |t| → g t θ = 0) :
    ∀ t θ : ℝ, M < |t| → Work.Spaces.pz (Work.Spaces.pth g) t θ = 0 :=
  fun t θ ht => pz_eq_zero_of_lt_abs ht fun y hy => pth_eq_zero_of_lt_abs hy hM

theorem supp_pthpth {g : ℝ → ℝ → ℝ} {M : ℝ} (hM : ∀ t θ : ℝ, M < |t| → g t θ = 0) :
    ∀ t θ : ℝ, M < |t| → Work.Spaces.pth (Work.Spaces.pth g) t θ = 0 :=
  fun _ θ ht => pth_pth_eq_zero_of_lt_abs ht hM

/-! ## The fixed-`θ` Plancherel data of the four slots -/

theorem plancherel_g_one {g : ℝ → ℝ → ℝ} (hg : NiceFlat g) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    MeasureTheory.Integrable (fun ξ : ℝ => (2 * Real.pi * ξ) ^ 2 * ‖slice g ξ θ‖ ^ 2) ∧
      (∫ ξ : ℝ, (2 * Real.pi * ξ) ^ 2 * ‖slice g ξ θ‖ ^ 2)
        = ∫ t : ℝ, (Work.Spaces.pz g t θ) ^ 2 :=
  ⟨integrable_weighted_slice1 (k := 1) (by norm_num)
      (contDiff_ofReal_comp (niceFlat_slice_contDiff hg hθ (n := 1) (by norm_num)))
      (niceFlat_hasCompactSupport hg θ),
    plancherel_slice_one hg hθ⟩

theorem plancherel_g_two {g : ℝ → ℝ → ℝ} (hg : NiceFlat g) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    MeasureTheory.Integrable (fun ξ : ℝ => (2 * Real.pi * ξ) ^ 4 * ‖slice g ξ θ‖ ^ 2) ∧
      (∫ ξ : ℝ, (2 * Real.pi * ξ) ^ 4 * ‖slice g ξ θ‖ ^ 2)
        = ∫ t : ℝ, (Work.Spaces.pz (Work.Spaces.pz g) t θ) ^ 2 :=
  ⟨integrable_weighted_slice1 (k := 2) (by norm_num)
      (contDiff_ofReal_comp (niceFlat_slice_contDiff hg hθ (n := 2) (by norm_num)))
      (niceFlat_hasCompactSupport hg θ),
    plancherel_slice_two hg hθ⟩

theorem plancherel_pth {g : ℝ → ℝ → ℝ} (hg : NiceFlat g) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    MeasureTheory.Integrable
        (fun ξ : ℝ => (2 * Real.pi * ξ) ^ 2 * ‖slice (Work.Spaces.pth g) ξ θ‖ ^ 2) ∧
      (∫ ξ : ℝ, (2 * Real.pi * ξ) ^ 2 * ‖slice (Work.Spaces.pth g) ξ θ‖ ^ 2)
        = ∫ t : ℝ, (Work.Spaces.pz (Work.Spaces.pth g) t θ) ^ 2 := by
  refine ⟨integrable_weighted_slice1 (k := 1) (by norm_num)
      (contDiff_ofReal_comp (niceFlat_slice_pth_contDiff hg hθ (n := 1) (by norm_num)))
      (niceFlat_hasCompactSupport_pth hg θ), ?_⟩
  have hpt : ∀ ξ : ℝ, (2 * Real.pi * ξ) ^ 2 * ‖slice (Work.Spaces.pth g) ξ θ‖ ^ 2
      = (2 * Real.pi * ξ) ^ 2 * ‖deriv (fun θ' => slice g ξ θ') θ‖ ^ 2 := by
    intro ξ
    rw [(slice_hasDerivAt g hg ξ hθ).1.deriv]
  rw [integral_congr_ae (Eventually.of_forall hpt), plancherel_slice_mixed hg hθ]

theorem plancherel_pthpth {g : ℝ → ℝ → ℝ} (hg : NiceFlat g) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    MeasureTheory.Integrable
        (fun ξ : ℝ => ‖slice (Work.Spaces.pth (Work.Spaces.pth g)) ξ θ‖ ^ 2) ∧
      (∫ ξ : ℝ, ‖slice (Work.Spaces.pth (Work.Spaces.pth g)) ξ θ‖ ^ 2)
        = ∫ t : ℝ, (Work.Spaces.pth (Work.Spaces.pth g) t θ) ^ 2 := by
  refine ⟨?_, ?_⟩
  · exact (integrable_weighted_slice1 (k := 0) (by norm_num)
      (contDiff_ofReal_comp (niceFlat_slice_pthpth_contDiff hg hθ))
      (niceFlat_hasCompactSupport_pthpth hg θ)).congr
        (Eventually.of_forall fun ξ => by
          show (2 * Real.pi * ξ) ^ (2 * 0) * ‖slice1 (fun t : ℝ =>
              ((Work.Spaces.pth (Work.Spaces.pth g) t θ : ℝ) : ℂ)) ξ‖ ^ 2
            = ‖slice (Work.Spaces.pth (Work.Spaces.pth g)) ξ θ‖ ^ 2
          rw [show (2 * Real.pi * ξ) ^ (2 * 0) = 1 by norm_num, one_mul]
          rfl)
  · have hpt : ∀ ξ : ℝ, ‖slice (Work.Spaces.pth (Work.Spaces.pth g)) ξ θ‖ ^ 2
        = ‖deriv (fun θ' => deriv (fun θ'' => slice g ξ θ'') θ') θ‖ ^ 2 := by
      intro ξ
      have hev : (fun θ' => deriv (fun θ'' => slice g ξ θ'') θ') =ᶠ[𝓝 θ]
          (fun θ' => slice (Work.Spaces.pth g) ξ θ') := by
        filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
        exact (slice_hasDerivAt g hg ξ hθ').1.deriv
      rw [hev.deriv_eq, (slice_hasDerivAt g hg ξ hθ).2.deriv]
    rw [integral_congr_ae (Eventually.of_forall hpt), plancherel_slice_pthpth hg hθ]

/-! ## The angular slot of a slice is finite, with an explicit energy bound -/

theorem aemeasurable_slice_sq_mul_snd {ψ : ℝ → ℝ → ℝ} {w : ℝ → ℝ}
    (hsl : ContinuousOn (fun p : ℝ × ℝ => slice ψ p.1 p.2) flStrip) (hw : Measurable w) :
    AEMeasurable (fun p : ℝ × ℝ => ‖slice ψ p.1 p.2‖ ^ 2 * w p.2)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ)) := by
  have h1 : AEMeasurable (fun p : ℝ × ℝ => ‖slice ψ p.1 p.2‖ ^ 2)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ)) :=
    (aemeasurable_of_continuousOn_strip
      (F := fun p : ℝ × ℝ => ‖slice ψ p.1 p.2‖) hsl.norm).pow_const 2
  have h2 : AEMeasurable (fun p : ℝ × ℝ => w p.2)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ)) :=
    (hw.comp measurable_snd).aemeasurable
  exact h1.mul h2

/-- `‖(r : ℂ)‖ = |r|`. -/
theorem norm_ofReal_eq_abs (r : ℝ) : ‖(r : ℂ)‖ = |r| := by
  have h1 : ‖(r : ℂ)‖ = |‖(r : ℂ)‖| := (abs_of_nonneg (norm_nonneg _)).symm
  rw [h1, ← Real.sqrt_sq_eq_abs (‖(r : ℂ)‖), ← Real.sqrt_sq_eq_abs r]
  congr 1
  rw [Complex.sq_norm, Complex.normSq_ofReal]
  ring

/-- The pointwise bound `‖Φ_ξ(θ)‖² ≤ 2M ∫_t φ(t,θ)²` for a profile supported in `[-M,M]`. -/
theorem slice_norm_sq_le_self {φ : ℝ → ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hcont : ContinuousOn (Function.uncurry φ) flStrip)
    (hsupp : ∀ t θ : ℝ, M < |t| → φ t θ = 0) (ξ : ℝ) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ‖slice φ ξ θ‖ ^ 2 ≤ 2 * M * ∫ t : ℝ, (φ t θ) ^ 2 := by
  have hcontθ : Continuous fun t : ℝ => φ t θ := continuous_slice_of_continuousOn_strip hcont hθ
  have hsuppθ : HasCompactSupport fun t : ℝ => φ t θ := slice_hasCompactSupport hM hsupp θ
  -- step 1: `‖Φ_ξ(θ)‖ ≤ ∫_t |φ(t,θ)|`
  have hexpnorm : ∀ t : ℝ, ‖Complex.exp (-(2 * Real.pi * Complex.I * ξ * t))‖ = 1 := by
    intro t
    rw [show -(2 * Real.pi * Complex.I * ξ * t)
        = ((-(2 * Real.pi * ξ * t) : ℝ) : ℂ) * Complex.I from by
      push_cast
      ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hnorm : ‖slice φ ξ θ‖ ≤ ∫ t : ℝ, |φ t θ| := by
    have h := norm_integral_le_integral_norm (μ := MeasureTheory.volume)
      (fun t : ℝ => (φ t θ : ℂ) * Complex.exp (-(2 * Real.pi * Complex.I * ξ * t)))
    refine le_trans h (le_of_eq ?_)
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    show ‖(φ t θ : ℂ) * Complex.exp (-(2 * Real.pi * Complex.I * ξ * t))‖ = |φ t θ|
    rw [norm_mul, hexpnorm t, mul_one, norm_ofReal_eq_abs]
  -- step 2: Cauchy–Schwarz on the box `[-M,M]`
  set μ : Measure ℝ := (MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Icc (-M) M)
    with hμ
  have hmu_univ : μ Set.univ = ENNReal.ofReal (2 * M) := by
    rw [hμ, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Icc]
    congr 1
    ring
  have hmem1 : MemLp (fun _ : ℝ => (1 : ℝ)) (ENNReal.ofReal 2) μ := memLp_const 1
  have hmem2 : MemLp (fun t : ℝ => |φ t θ|) (ENNReal.ofReal 2) μ :=
    (hcontθ.abs).memLp_of_hasCompactSupport
      (hsuppθ.comp_left (g := fun x : ℝ => |x|) (by simp))
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) (p := 2) (q := 2)
    (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩)
    (Eventually.of_forall fun _ => by norm_num)
    (Eventually.of_forall fun t => abs_nonneg _) hmem1 hmem2
  have hp1 : (∫ t : ℝ, (1 : ℝ) ^ (2 : ℝ) ∂μ) = 2 * M := by
    rw [Real.one_rpow, integral_const, Measure.real_def, hmu_univ,
      ENNReal.toReal_ofReal (by linarith), smul_eq_mul, mul_one]
  have hp2 : (∫ t : ℝ, |φ t θ| ^ (2 : ℝ) ∂μ) = ∫ t : ℝ, (φ t θ) ^ 2 := by
    have h1 : (∫ t : ℝ, |φ t θ| ^ (2 : ℝ) ∂μ) = ∫ t : ℝ, (φ t θ) ^ 2 ∂μ :=
      integral_congr_ae (Eventually.of_forall fun t => by
        show |φ t θ| ^ (2 : ℝ) = (φ t θ) ^ 2
        rw [Real.rpow_two, sq_abs])
    rw [h1, hμ, MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro t ht
    have ht' : M < |t| := not_le.mp fun hle => ht (abs_le.mp hle)
    rw [hsupp t θ ht']
    norm_num
  have hCS2 : (∫ t : ℝ, |φ t θ| ∂μ)
      ≤ (∫ t : ℝ, (1 : ℝ) ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2)
        * (∫ t : ℝ, |φ t θ| ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2) := by
    rw [show (∫ t : ℝ, |φ t θ| ∂μ) = ∫ t : ℝ, 1 * |φ t θ| ∂μ from
      integral_congr_ae (Eventually.of_forall fun t => (one_mul _).symm)]
    exact hCS
  have hbound : (∫ t : ℝ, |φ t θ| ∂μ) ≤ Real.sqrt (2 * M) * Real.sqrt (∫ t : ℝ, (φ t θ) ^ 2) := by
    have h := hCS2
    rw [hp1, hp2] at h
    simpa [Real.sqrt_eq_rpow] using h
  have hfull : (∫ t : ℝ, |φ t θ| ∂μ) = ∫ t : ℝ, |φ t θ| :=
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => by
      have ht' : M < |t| := not_le.mp fun hle => ht (abs_le.mp hle)
      rw [hsupp t θ ht', abs_zero]
  rw [hfull] at hbound
  have hsq : (∫ t : ℝ, |φ t θ|) ^ 2 ≤ (2 * M) * ∫ t : ℝ, (φ t θ) ^ 2 := by
    have hnn : 0 ≤ ∫ t : ℝ, |φ t θ| := integral_nonneg fun t => abs_nonneg _
    have hmain := mul_self_le_mul_self hnn hbound
    have hsq2 : (Real.sqrt (2 * M) * Real.sqrt (∫ t : ℝ, (φ t θ) ^ 2))
        * (Real.sqrt (2 * M) * Real.sqrt (∫ t : ℝ, (φ t θ) ^ 2))
        = (2 * M) * ∫ t : ℝ, (φ t θ) ^ 2 := by
      rw [mul_mul_mul_comm, Real.mul_self_sqrt (by linarith),
        Real.mul_self_sqrt (integral_nonneg fun t => sq_nonneg _)]
    calc (∫ t : ℝ, |φ t θ|) ^ 2 = (∫ t : ℝ, |φ t θ|) * (∫ t : ℝ, |φ t θ|) := by ring
      _ ≤ (Real.sqrt (2 * M) * Real.sqrt (∫ t : ℝ, (φ t θ) ^ 2))
            * (Real.sqrt (2 * M) * Real.sqrt (∫ t : ℝ, (φ t θ) ^ 2)) := hmain
      _ = (2 * M) * ∫ t : ℝ, (φ t θ) ^ 2 := hsq2
  have hstep1 : ‖slice φ ξ θ‖ * ‖slice φ ξ θ‖
      ≤ (∫ t : ℝ, |φ t θ|) * (∫ t : ℝ, |φ t θ|) :=
    mul_self_le_mul_self (norm_nonneg _) hnorm
  calc ‖slice φ ξ θ‖ ^ 2 = ‖slice φ ξ θ‖ * ‖slice φ ξ θ‖ := by ring
    _ ≤ (∫ t : ℝ, |φ t θ|) * (∫ t : ℝ, |φ t θ|) := hstep1
    _ = (∫ t : ℝ, |φ t θ|) ^ 2 := by ring
    _ ≤ 2 * M * ∫ t : ℝ, (φ t θ) ^ 2 := hsq

theorem integrableOn_slice_sq_mul {ψ : ℝ → ℝ → ℝ} {w : ℝ → ℝ} {M ξ : ℝ} (hM : 0 ≤ M)
    (hcont : ContinuousOn (Function.uncurry ψ) flStrip)
    (hsupp : ∀ t θ : ℝ, M < |t| → ψ t θ = 0)
    (hwnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ w θ) (hwmeas : Measurable w)
    (hslice : ContinuousOn (fun θ : ℝ => slice ψ ξ θ) (Set.Ioo 0 (Real.pi / 2)))
    (henergy : MeasureTheory.IntegrableOn (fun θ : ℝ => (∫ t : ℝ, (ψ t θ) ^ 2) * w θ)
      Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => ‖slice ψ ξ θ‖ ^ 2 * w θ) Work.Spaces.Iθ := by
  refine MeasureTheory.Integrable.mono' (henergy.const_mul (2 * M)) ?_ ?_
  · have h1 : AEMeasurable (fun θ : ℝ => ‖slice ψ ξ θ‖ ^ 2)
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ) :=
      (aemeasurable_Iθ_of_continuousOn_Ioo hslice.norm).pow_const 2
    have h2 : AEMeasurable (fun θ : ℝ => w θ)
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ) :=
      hwmeas.aemeasurable.restrict
    exact aestronglyMeasurable_iff_aemeasurable.mpr (h1.mul h2)
  · filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
    have hw0 : 0 ≤ w θ := hwnn θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hb := slice_norm_sq_le_self hM hcont hsupp ξ hθ
    calc ‖‖slice ψ ξ θ‖ ^ 2 * w θ‖ = ‖slice ψ ξ θ‖ ^ 2 * w θ :=
          Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hw0)
      _ ≤ ((2 * M) * ∫ t : ℝ, (ψ t θ) ^ 2) * w θ := mul_le_mul_of_nonneg_right hb hw0
      _ = 2 * M * ((∫ t : ℝ, (ψ t θ) ^ 2) * w θ) := by ring

theorem integrableOn_slice_sq_mul_le {ψ : ℝ → ℝ → ℝ} {w w' : ℝ → ℝ} {ξ : ℝ}
    (hwnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ w θ) (hw'nn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ w' θ)
    (hle : ∀ θ ∈ Work.Spaces.Iθ, w θ ≤ w' θ)
    (hslice : ContinuousOn (fun θ : ℝ => slice ψ ξ θ) (Set.Ioo 0 (Real.pi / 2)))
    (hwmeas : Measurable w)
    (h' : MeasureTheory.IntegrableOn (fun θ : ℝ => ‖slice ψ ξ θ‖ ^ 2 * w' θ)
      Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => ‖slice ψ ξ θ‖ ^ 2 * w θ) Work.Spaces.Iθ := by
  refine MeasureTheory.Integrable.mono' h' ?_ ?_
  · have h1 : AEMeasurable (fun θ : ℝ => ‖slice ψ ξ θ‖ ^ 2)
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ) :=
      (aemeasurable_Iθ_of_continuousOn_Ioo hslice.norm).pow_const 2
    have h2 : AEMeasurable (fun θ : ℝ => w θ)
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ) :=
      hwmeas.aemeasurable.restrict
    exact aestronglyMeasurable_iff_aemeasurable.mpr (h1.mul h2)
  · filter_upwards [ae_mem_Iθ] with θ hθ
    have h1 : 0 ≤ ‖slice ψ ξ θ‖ ^ 2 := sq_nonneg _
    calc ‖‖slice ψ ξ θ‖ ^ 2 * w θ‖ = ‖slice ψ ξ θ‖ ^ 2 * w θ :=
          Real.norm_of_nonneg (mul_nonneg h1 (hwnn θ hθ))
      _ ≤ ‖slice ψ ξ θ‖ ^ 2 * w' θ := mul_le_mul_of_nonneg_left (hle θ hθ) h1

end

end Work.FTS.EllSol.FlatFT
