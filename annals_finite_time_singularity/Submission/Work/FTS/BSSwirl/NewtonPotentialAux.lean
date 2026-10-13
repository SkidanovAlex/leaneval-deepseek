/-
# `Work.FTS.BSSwirl.NewtonPotentialAux` — auxiliary estimates for the Newtonian potential

Vocabulary for `Work.FTS.BSSwirl.hasFDerivAt_newtonPotential`: the elementary comparison
`(‖z‖³)⁻¹‖z‖ ≤ (‖z‖²)⁻¹`, the identification of the kernel `Work.StabilityFar.Decay.kf` with the
first-order Taylor coefficient of `‖·‖⁻¹`, operator-norm bounds for `smulRight`, integrability of
the two kernels `‖u - ·‖⁻¹ ⊗ ω` and `‖u - ·‖⁻³⟪u - ·,h⟫ ⊗ ω` over the support ball, the little-o
relation `‖h‖^{3/2} = o(‖h‖)`, and the crude/far pointwise bounds for the Taylor residual
`(‖x+h-y‖)⁻¹ - ‖x-y‖⁻¹ + ‖x-y‖⁻³⟪x-y,h⟫`.
-/
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.BSSwirl.Defs
import Submission.Work.StabilityFar.Decay.KernelDefs
import Submission.Work.StabilityFar.Decay.integrable_indicator_inv_sq
import Submission.Work.FTS.BSSwirl.abs_inv_norm_taylor_residual_le

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

open MeasureTheory Metric Filter Set
open scoped Topology ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FTS.BSSwirl

noncomputable section

/-! ## Elementary auxiliary facts -/

/-- `(‖z‖³)⁻¹ ‖z‖ ≤ (‖z‖²)⁻¹`.  The borderline case `z = 0` is handled by the convention
`0⁻¹ = 0`. -/
lemma inv_cube_mul_self_le (z : R3) :
    (‖z‖ ^ (3 : ℕ) : ℝ)⁻¹ * ‖z‖ ≤ (‖z‖ ^ (2 : ℕ) : ℝ)⁻¹ := by
  rcases eq_or_lt_of_le (norm_nonneg z) with h | h
  · rw [← h]
    norm_num
  · have heq : (‖z‖ ^ (3 : ℕ) : ℝ)⁻¹ * ‖z‖ = (‖z‖ ^ (2 : ℕ) : ℝ)⁻¹ := by
      field_simp
    rw [heq]

/-- The identity `(‖z‖³)⁻¹ ‖z‖ = (‖z‖²)⁻¹`. -/
lemma inv_cube_mul_self_eq (z : R3) :
    (‖z‖ ^ (3 : ℕ) : ℝ)⁻¹ * ‖z‖ = (‖z‖ ^ (2 : ℕ) : ℝ)⁻¹ := by
  rcases eq_or_lt_of_le (norm_nonneg z) with h | h
  · rw [← h]
    norm_num
  · field_simp

/-- `(a ^ n)⁻¹ = a ^ (-n)` for `a ≥ 0`, in real powers. -/
lemma inv_natPow_eq_rpow_neg' {a : ℝ} (ha : 0 ≤ a) (n : ℕ) : (a ^ n)⁻¹ = a ^ (-(n : ℝ)) := by
  rw [← Real.rpow_natCast a n, ← Real.rpow_neg ha (n : ℝ)]

/-- The kernel `kf z = ‖z‖⁻³ • z` tested against `h` is the first-order Taylor coefficient of
`‖·‖⁻¹` at `z`. -/
lemma inner_kf (z h : R3) :
    inner ℝ (Work.StabilityFar.Decay.kf z) h = (‖z‖ ^ (3 : ℕ) : ℝ)⁻¹ * inner ℝ z h := by
  rw [Work.StabilityFar.Decay.kf, inner_smul_left]
  simp [innerSL_apply_apply]

/-- Operator-norm bound for `smulRight`. -/
lemma norm_smulRight_le' (v w : R3) : ‖(innerSL ℝ v).smulRight w‖ ≤ ‖v‖ * ‖w‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  rw [ContinuousLinearMap.smulRight_apply, norm_smul, innerSL_apply_apply, Real.norm_eq_abs]
  calc |inner ℝ v x| * ‖w‖ ≤ (‖v‖ * ‖x‖) * ‖w‖ :=
        mul_le_mul_of_nonneg_right (abs_real_inner_le_norm v x) (norm_nonneg w)
    _ = ‖v‖ * ‖w‖ * ‖x‖ := by ring

/-! ## Integrability of the two kernels -/

/-- The scalar kernel `‖u - ·‖⁻³ ⟪u - ·, h⟫` is integrable against a bounded compactly supported
`ω` (it is dominated by `M ‖h‖ ‖u - ·‖⁻²`, integrable in dimension `3`). -/
lemma integrable_inv_cube_inner_smul' {ω : R3 → R3} {R M : ℝ} (hM : 0 ≤ M)
    (hbdd : ∀ y, ‖ω y‖ ≤ M) (hsupp : ∀ y, ω y ≠ 0 → y ∈ Metric.closedBall 0 R)
    (hmeas : AEStronglyMeasurable ω volume) (u h : R3) :
    Integrable (fun y => ((‖u - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * inner ℝ (u - y) h) • ω y) volume := by
  have hC : 0 ≤ M * ‖h‖ := mul_nonneg hM (norm_nonneg h)
  have hbd : Integrable (fun y : R3 => (Metric.closedBall (0 : R3) R).indicator
      (fun y => (M * ‖h‖) * ((‖u - y‖ ^ (2 : ℕ) : ℝ)⁻¹)) y) volume :=
    Work.StabilityFar.Decay.integrable_indicator_inv_sq u hC
  refine Integrable.mono' hbd ?_ ?_
  · have : Measurable (fun y : R3 => (‖u - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * inner ℝ (u - y) h) := by
      measurability
    exact this.aestronglyMeasurable.smul hmeas
  · filter_upwards with y
    by_cases hy : y ∈ Metric.closedBall (0 : R3) R
    · rw [Set.indicator_of_mem hy]
      have h1 : |(‖u - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * inner ℝ (u - y) h|
          ≤ (‖u - y‖ ^ (2 : ℕ) : ℝ)⁻¹ * ‖h‖ := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (‖u - y‖ ^ (3 : ℕ) : ℝ)⁻¹)]
        calc (‖u - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * |inner ℝ (u - y) h|
            ≤ (‖u - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * (‖u - y‖ * ‖h‖) :=
              mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by positivity)
          _ = ((‖u - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * ‖u - y‖) * ‖h‖ := by ring
          _ ≤ (‖u - y‖ ^ (2 : ℕ) : ℝ)⁻¹ * ‖h‖ :=
              mul_le_mul_of_nonneg_right (inv_cube_mul_self_le _) (norm_nonneg h)
      calc ‖((‖u - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * inner ℝ (u - y) h) • ω y‖
          = |(‖u - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * inner ℝ (u - y) h| * ‖ω y‖ := by
            rw [norm_smul, Real.norm_eq_abs]
        _ ≤ ((‖u - y‖ ^ (2 : ℕ) : ℝ)⁻¹ * ‖h‖) * ‖ω y‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ ≤ ((‖u - y‖ ^ (2 : ℕ) : ℝ)⁻¹ * ‖h‖) * M :=
            mul_le_mul_of_nonneg_left (hbdd y) (by positivity)
        _ = (M * ‖h‖) * ((‖u - y‖ ^ (2 : ℕ) : ℝ)⁻¹) := by ring
    · have hωy : ω y = 0 := by
        by_contra hh
        exact hy (hsupp y hh)
      rw [Set.indicator_of_notMem hy, hωy]
      simp

/-- The rank-one operator map `(c, w) ↦ c.smulRight w` is continuous (it is a bounded
bilinear map, `ContinuousLinearMap.smulRightL`). -/
lemma continuous_smulRightL_pair :
    Continuous (fun p : (R3 →L[ℝ] ℝ) × R3 =>
      ContinuousLinearMap.smulRightL ℝ R3 R3 p.1 p.2) :=
  ContinuousLinearMap.continuous₂ (ContinuousLinearMap.smulRightL ℝ R3 R3)

/-- The operator-valued kernel of `potDeriv` is integrable: it is dominated by
`M ‖x - ·‖⁻²`, integrable in dimension `3` on the support ball. -/
lemma integrable_potDeriv_kernel' {ω : R3 → R3} {R M : ℝ} (hM : 0 ≤ M)
    (hbdd : ∀ y, ‖ω y‖ ≤ M) (hsupp : ∀ y, ω y ≠ 0 → y ∈ Metric.closedBall 0 R)
    (hmeas : AEStronglyMeasurable ω volume) (x : R3) :
    Integrable (fun y => (‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹ •
      (innerSL ℝ (y - x)).smulRight (ω y)) volume := by
  have hbd : Integrable (fun y : R3 => (Metric.closedBall (0 : R3) R).indicator
      (fun y => M * ((‖x - y‖ ^ (2 : ℕ) : ℝ)⁻¹)) y) volume :=
    Work.StabilityFar.Decay.integrable_indicator_inv_sq x hM
  refine Integrable.mono' hbd ?_ ?_
  · first
    | exact ((((continuous_const.sub continuous_id).norm.pow 3).measurable.inv).aestronglyMeasurable).smul
            (Continuous.comp_aestronglyMeasurable₂ (ContinuousLinearMap.smulRightL ℝ Work.FTS.BSSwirl.R3 Work.FTS.BSSwirl.R3).continuous₂
              (((innerSL ℝ).continuous.comp (continuous_id.sub continuous_const)).aestronglyMeasurable) hmeas)
    | measurability
  · filter_upwards with y
    by_cases hy : y ∈ Metric.closedBall (0 : R3) R
    · rw [Set.indicator_of_mem hy]
      have h1 : ‖(innerSL ℝ (y - x)).smulRight (ω y)‖ ≤ ‖y - x‖ * M :=
        (norm_smulRight_le' (y - x) (ω y)).trans
          (mul_le_mul_of_nonneg_left (hbdd y) (norm_nonneg (y - x)))
      calc ‖(‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹ • (innerSL ℝ (y - x)).smulRight (ω y)‖
          = (‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * ‖(innerSL ℝ (y - x)).smulRight (ω y)‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        _ ≤ (‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * (‖y - x‖ * M) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = M * ((‖x - y‖ ^ (2 : ℕ) : ℝ)⁻¹) := by
            rw [norm_sub_rev y x, ← mul_assoc, inv_cube_mul_self_eq (x - y)]
            ring
    · have hωy : ω y = 0 := by
        by_contra hh
        exact hy (hsupp y hh)
      rw [Set.indicator_of_notMem hy, hωy]
      simp

/-- `‖h‖^{3/2} = o(‖h‖)` at `0`. -/
lemma littleO_norm_rpow_three_halves :
    (fun h : R3 => ‖h‖ ^ ((3 : ℝ) / 2)) =o[𝓝 0] (fun h : R3 => h) := by
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  filter_upwards [Metric.ball_mem_nhds (0 : R3) (lt_min one_pos (pow_pos hε 2))] with h hh
  have hnorm : ‖h‖ < min 1 (ε ^ 2) := by simpa [dist_eq_norm] using hh
  rcases eq_or_ne h 0 with rfl | hne
  · rw [norm_zero]
    simp [Real.zero_rpow (by norm_num : ((3 : ℝ) / 2) ≠ 0)]
  · have hpos : 0 < ‖h‖ := norm_pos_iff.mpr hne
    have h2 : ‖h‖ ≤ ε ^ 2 := le_of_lt (lt_of_lt_of_le hnorm (min_le_right _ _))
    have h3 : Real.sqrt ‖h‖ ≤ ε := by
      rw [← Real.sqrt_sq hε.le]
      exact Real.sqrt_le_sqrt h2
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg h) _)]
    rw [show ‖h‖ ^ ((3 : ℝ) / 2) = ‖h‖ * Real.sqrt ‖h‖ by
      rw [Real.sqrt_eq_rpow, show ((3 : ℝ) / 2) = 1 + 1 / 2 by norm_num,
        Real.rpow_add hpos, Real.rpow_one]]
    calc ‖h‖ * Real.sqrt ‖h‖ ≤ ‖h‖ * ε := mul_le_mul_of_nonneg_left h3 (norm_nonneg h)
      _ = ε * ‖h‖ := by ring

/-! ## The pointwise residual bounds -/

/-- **Crude bound for the Taylor residual** `K(h,y)`. -/
lemma abs_residual_crude (x h y : R3) :
    |(‖(x + h) - y‖)⁻¹ - (‖x - y‖)⁻¹
        + (‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * inner ℝ (x - y) h|
      ≤ (‖(x + h) - y‖)⁻¹ + (‖x - y‖)⁻¹ + ‖h‖ * (‖x - y‖ ^ (2 : ℕ) : ℝ)⁻¹ := by
  have hab : |(‖(x + h) - y‖)⁻¹ - (‖x - y‖)⁻¹|
      ≤ (‖(x + h) - y‖)⁻¹ + (‖x - y‖)⁻¹ := by
    have hadd := abs_add_le ((‖(x + h) - y‖)⁻¹) (-(‖x - y‖)⁻¹)
    rw [← sub_eq_add_neg, abs_neg] at hadd
    simpa [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (‖(x + h) - y‖)⁻¹),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (‖x - y‖)⁻¹)] using hadd
  have hc : |(‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * inner ℝ (x - y) h|
      ≤ ‖h‖ * (‖x - y‖ ^ (2 : ℕ) : ℝ)⁻¹ := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹)]
    calc (‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * |inner ℝ (x - y) h|
        ≤ (‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * (‖x - y‖ * ‖h‖) :=
          mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by positivity)
      _ = ((‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * ‖x - y‖) * ‖h‖ := by ring
      _ ≤ (‖x - y‖ ^ (2 : ℕ) : ℝ)⁻¹ * ‖h‖ :=
          mul_le_mul_of_nonneg_right (inv_cube_mul_self_le _) (norm_nonneg h)
      _ = ‖h‖ * (‖x - y‖ ^ (2 : ℕ) : ℝ)⁻¹ := by ring
  calc |(‖(x + h) - y‖)⁻¹ - (‖x - y‖)⁻¹
        + (‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * inner ℝ (x - y) h|
      = |((‖(x + h) - y‖)⁻¹ - (‖x - y‖)⁻¹)
          + (‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * inner ℝ (x - y) h| := rfl
    _ ≤ |(‖(x + h) - y‖)⁻¹ - (‖x - y‖)⁻¹|
        + |(‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * inner ℝ (x - y) h| := abs_add_le _ _
    _ ≤ ((‖(x + h) - y‖)⁻¹ + (‖x - y‖)⁻¹) + ‖h‖ * (‖x - y‖ ^ (2 : ℕ) : ℝ)⁻¹ :=
        add_le_add hab hc

/-- **Taylor bound for the residual** in the far regime `2‖h‖ ≤ ‖x - y‖`. -/
lemma abs_residual_far (x h y : R3) (hy : 2 * ‖h‖ ≤ ‖x - y‖) :
    |(‖(x + h) - y‖)⁻¹ - (‖x - y‖)⁻¹
        + (‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * inner ℝ (x - y) h|
      ≤ 10000 * ‖h‖ ^ ((3 : ℝ) / 2) * ‖x - y‖ ^ (-(5 : ℝ) / 2) := by
  have htay := abs_inv_norm_taylor_residual_le (z := x - y) (h := h) hy
  rw [inner_kf] at htay
  have hz : (x - y) + h = (x + h) - y := by abel
  rwa [hz] at htay

end

end Work.FTS.BSSwirl
