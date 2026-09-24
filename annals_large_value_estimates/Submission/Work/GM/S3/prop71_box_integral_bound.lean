import Mathlib
import Submission.Work.GM.S3.prop71_defs
import Submission.Work.GM.S3.prop71_inner_uniform
import Submission.Work.GM.S3.prop71_inner_support
import Submission.Work.GM.S3.prop71_inner_decay
import Submission.Work.GM.S3.prop71_inner_tail
import Submission.Work.GM.S3.prop71_pbox_measure

namespace Work.GM.S3

open Complex Finset MeasureTheory
open scoped BigOperators
open Submission.GM (Rfun Separated Iterm hhat hfun)

/-- `pbox = [1/2,2]²` is compact. -/
theorem prop71_box_isCompact_pbox : IsCompact pbox := by
  rw [pbox]; exact isCompact_Icc.prod isCompact_Icc

/-- Real-valued version of `Work.GM.S3.integrable_of_measurable_bounded_support`. -/
theorem prop71_box_integrable_of_bounded_support {X : Type*} [MeasurableSpace X]
    [TopologicalSpace X] [OpensMeasurableSpace X] [T2Space X] {μ : Measure X}
    [IsFiniteMeasureOnCompacts μ] {f : X → ℝ} {K : Set X} (hK : IsCompact K)
    (hmeas : Measurable f) (hsub : Function.support f ⊆ K) {C : ℝ}
    (hb : ∀ x, ‖f x‖ ≤ C) : Integrable f μ := by
  have hKmeas : MeasurableSet K := hK.measurableSet
  have hgi : Integrable (K.indicator fun _ => C) μ :=
    (MeasureTheory.integrableOn_const hK.measure_lt_top.ne).integrable_indicator hKmeas
  refine Integrable.mono' hgi hmeas.aestronglyMeasurable ?_
  filter_upwards with x
  by_cases hx : x ∈ K
  · rw [Set.indicator_of_mem hx]; exact hb x
  · have hx0 : f x = 0 := by
      by_contra h
      exact hx (hsub (Function.mem_support.mpr h))
    rw [Set.indicator_of_notMem hx, hx0, norm_zero]

/-- A bounded measurable real-valued function is integrable on `pbox`. -/
theorem prop71_box_integrableOn_of_bounded {g : ℝ × ℝ → ℝ} (hmeas : Measurable g) {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ v, ‖g v‖ ≤ C) :
    IntegrableOn g pbox (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)) := by
  refine (integrable_indicator_iff measurableSet_pbox).mp ?_
  refine prop71_box_integrable_of_bounded_support (C := C) prop71_box_isCompact_pbox
    (hmeas.indicator measurableSet_pbox) Set.support_indicator_subset ?_
  intro x
  by_cases hx : x ∈ pbox
  · rw [Set.indicator_of_mem hx]; exact hb x
  · rw [Set.indicator_of_notMem hx, norm_zero]; exact hC

/-- GM Prop 7.1, the `v`-integral at the heart of the estimate.  `hin` is the uniform bound
`Work.GM.S3.prop71_inner_uniform`, `hdec` the non-stationary-phase bound
`Work.GM.S3.prop71_inner_decay`, `pbox = [1/2,2]²` and `τ = (M N)^η / N`.

Splitting the `v`-integral into the stationary region `|phas m v| ≤ τ` and its complement,
using `hin` on the first part and `hdec` (via the companion fact that
`|phas m v| > τ` implies `‖innerInt N m v‖ ≤ Cj · ((M N)^η)^{-j}`, which is
`Work.GM.S3.prop71_inner_tail`, already proved in this workspace) on the second, then bounding
`∫_{pbox} ‖Rprod W v‖ ≤ ∫_{pbox} |W|³ = |W|³ · vol(pbox) = (9/4)|W|³`
(`Work.GM.S3.norm_Rprod_le`, and `vol(pbox) = 9/4` which is `Work.GM.S3.prop71_pbox_measure`,
being written in parallel) gives the statement.

Proof ingredients: `prop71_inner_support` (the integrand vanishes off `pbox`),
`MeasureTheory.StronglyMeasurable.integral_prod_right'` (measurability in `v` of the Bochner
integral `innerInt`), `Work.GM.S3.integrable_of_measurable_bounded_support` (integrability of
the bounded, `pbox`-supported pieces), `MeasureTheory.integral_mono_ae` + `MeasureTheory.integral_add`,
`MeasureTheory.integral_const_mul`, `MeasureTheory.integral_indicator`, `MeasureTheory.setIntegral_const`. -/
theorem prop71_box_integral_bound (K Cj : ℝ) (hK : 0 < K) (hCj : 0 < Cj) (j : ℕ)
    (hin : ∀ (N : ℕ) (m : ℤ × ℤ × ℤ) (v : ℝ × ℝ), ‖innerInt N m v‖ ≤ K)
    (hdec : ∀ (N : ℕ) (m : ℤ × ℤ × ℤ) (v : ℝ × ℝ), v ∈ pbox → (N : ℝ) * phas m v ≠ 0 →
      ‖innerInt N m v‖ ≤ Cj / |(N : ℝ) * phas m v| ^ j)
    (N : ℕ) (hN : 1 ≤ N) (η : ℝ) (hη : 0 < η) (W : Finset ℝ) (m : ℤ × ℤ × ℤ) :
    (∫ v : ℝ × ℝ, ‖Rprod W v‖ * ‖innerInt N m v‖) ≤
      K * (∫ v in pbox, (if |phas m v| ≤ (Submission.LargeValues.M N) ^ η / (N : ℝ)
        then ‖Rprod W v‖ else 0))
      + (9 / 4) * Cj * ((W.card : ℝ) ^ 3 *
          (((Submission.LargeValues.M N) ^ η) ^ (-(j : ℝ)))) := by
  -- Abbreviate the stationary-region integrand `A` and the tail factor `B`.
  set B : ℝ := (((Submission.LargeValues.M N) ^ η) ^ (-(j : ℝ))) with hB_def
  set A : ℝ × ℝ → ℝ := fun v => (if |phas m v| ≤ (Submission.LargeValues.M N) ^ η / (N : ℝ)
        then ‖Rprod W v‖ else 0) with hA_def
  have hA_eq : ∀ v : ℝ × ℝ, A v = (if |phas m v| ≤ (Submission.LargeValues.M N) ^ η / (N : ℝ)
        then ‖Rprod W v‖ else 0) := fun v => by rw [hA_def]
  have hMpos : 0 < Submission.LargeValues.M N := by
    rw [Submission.LargeValues.M]
    exact Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < N)) _
  have hMNpos : 0 < (Submission.LargeValues.M N) ^ η := Real.rpow_pos_of_pos hMpos η
  have hB_nonneg : 0 ≤ B := by rw [hB_def]; exact Real.rpow_nonneg hMNpos.le _
  have hcardpow_nonneg : (0 : ℝ) ≤ (W.card : ℝ) ^ 3 := by positivity
  have hAnonneg : ∀ v : ℝ × ℝ, 0 ≤ (if |phas m v| ≤ (Submission.LargeValues.M N) ^ η / (N : ℝ)
      then ‖Rprod W v‖ else 0) := by
    intro v
    positivity
  have hA_nonneg : ∀ v, 0 ≤ A v := fun v => by rw [hA_eq v]; exact hAnonneg v
  -- Measurability and the pointwise bound `|A| ≤ |W|³`.
  have hstat_meas : Measurable A := by
    rw [hA_def]
    exact Measurable.ite
      (measurableSet_le (Measurable.abs (by unfold phas; fun_prop)) measurable_const)
      (Rprod_measurable W).norm measurable_const
  have hRf_meas : Measurable (fun v : ℝ × ℝ => ‖Rprod W v‖) := (Rprod_measurable W).norm
  have hstat_le : ∀ v : ℝ × ℝ, A v ≤ (W.card : ℝ) ^ 3 := by
    intro v
    rw [hA_eq v]
    by_cases h : |phas m v| ≤ (Submission.LargeValues.M N) ^ η / (N : ℝ)
    · rw [if_pos h]; exact norm_Rprod_le W v
    · rw [if_neg h]; exact hcardpow_nonneg
  -- Integrability of the pieces on `pbox`.
  have hRf_IO : IntegrableOn (fun v : ℝ × ℝ => ‖Rprod W v‖) pbox :=
    prop71_box_integrableOn_of_bounded hRf_meas hcardpow_nonneg
      (fun v => by rw [Real.norm_of_nonneg (norm_nonneg _)]; exact norm_Rprod_le W v)
  have hstat_IO : IntegrableOn A pbox :=
    prop71_box_integrableOn_of_bounded hstat_meas hcardpow_nonneg
      (fun v => by rw [Real.norm_of_nonneg (hA_nonneg v)]; exact hstat_le v)
  -- The dominating function `K·A + Cj·B·‖Rprod‖`.
  have hg_meas : Measurable (fun v : ℝ × ℝ => K * A v + Cj * B * ‖Rprod W v‖) :=
    (measurable_const.mul hstat_meas).add (measurable_const.mul hRf_meas)
  have hg_bound : ∀ v : ℝ × ℝ, ‖K * A v + Cj * B * ‖Rprod W v‖‖ ≤
      K * (W.card : ℝ) ^ 3 + Cj * B * (W.card : ℝ) ^ 3 := by
    intro v
    have hs : 0 ≤ K * A v := mul_nonneg hK.le (hA_nonneg v)
    have ht : 0 ≤ Cj * B * ‖Rprod W v‖ :=
      mul_nonneg (mul_nonneg hCj.le hB_nonneg) (norm_nonneg _)
    rw [Real.norm_of_nonneg (by linarith)]
    have e1 : K * A v ≤ K * (W.card : ℝ) ^ 3 := mul_le_mul_of_nonneg_left (hstat_le v) hK.le
    have e2 : Cj * B * ‖Rprod W v‖ ≤ Cj * B * (W.card : ℝ) ^ 3 :=
      mul_le_mul_of_nonneg_left (norm_Rprod_le W v) (mul_nonneg hCj.le hB_nonneg)
    linarith
  have hg_IO : IntegrableOn (fun v : ℝ × ℝ => K * A v + Cj * B * ‖Rprod W v‖) pbox :=
    prop71_box_integrableOn_of_bounded hg_meas (by positivity) hg_bound
  -- Pointwise bound on `pbox`: `hin` on the stationary part, `prop71_inner_tail` off it.
  have hpt : ∀ v ∈ pbox, ‖Rprod W v‖ * ‖innerInt N m v‖ ≤ K * A v + Cj * B * ‖Rprod W v‖ := by
    intro v hv
    rw [hA_eq v]
    by_cases h : |phas m v| ≤ (Submission.LargeValues.M N) ^ η / (N : ℝ)
    · rw [if_pos h]
      have h1 : ‖innerInt N m v‖ ≤ K := hin N m v
      have ha : 0 ≤ ‖Rprod W v‖ := norm_nonneg _
      have ht : 0 ≤ Cj * B * ‖Rprod W v‖ :=
        mul_nonneg (mul_nonneg hCj.le hB_nonneg) (norm_nonneg _)
      nlinarith [mul_le_mul_of_nonneg_left h1 ha]
    · rw [if_neg h]
      have hbig : (Submission.LargeValues.M N) ^ η / (N : ℝ) < |phas m v| := not_le.mp h
      have ht := prop71_inner_tail j Cj hCj hdec N hN η hη m v hv hbig
      have htB : ‖innerInt N m v‖ ≤ Cj * B := by rw [hB_def]; exact ht
      have ha : 0 ≤ ‖Rprod W v‖ := norm_nonneg _
      calc ‖Rprod W v‖ * ‖innerInt N m v‖ ≤ ‖Rprod W v‖ * (Cj * B) :=
            mul_le_mul_of_nonneg_left htB ha
        _ = K * 0 + Cj * B * ‖Rprod W v‖ := by ring
  -- The main chain of inequalities.
  have hmain_le : (∫ v : ℝ × ℝ, ‖Rprod W v‖ * ‖innerInt N m v‖) ≤
      K * (∫ v in pbox, A v) + (Cj * B) * (∫ v in pbox, ‖Rprod W v‖) := by
    have h1 : (∫ v : ℝ × ℝ, ‖Rprod W v‖ * ‖innerInt N m v‖)
        = ∫ v in pbox, ‖Rprod W v‖ * ‖innerInt N m v‖ :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero
        (f := fun v : ℝ × ℝ => ‖Rprod W v‖ * ‖innerInt N m v‖) (s := pbox)
        (fun v hv => by simp [prop71_inner_support N m v hv])).symm
    have h2 : ∫ v in pbox, ‖Rprod W v‖ * ‖innerInt N m v‖
        ≤ ∫ v in pbox, (K * A v + Cj * B * ‖Rprod W v‖) :=
      setIntegral_mono_of_nonneg (fun v _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (fun v hv => hpt v hv) hg_IO
    have h3 : ∫ v in pbox, (K * A v + Cj * B * ‖Rprod W v‖)
        = K * (∫ v in pbox, A v) + (Cj * B) * (∫ v in pbox, ‖Rprod W v‖) := by
      have hKi : IntegrableOn (fun v : ℝ × ℝ => K * A v) pbox :=
        prop71_box_integrableOn_of_bounded (C := K * (W.card : ℝ) ^ 3) (hstat_meas.const_mul K)
          (by positivity)
          (fun v => by
            rw [Real.norm_of_nonneg (mul_nonneg hK.le (hA_nonneg v))]
            exact mul_le_mul_of_nonneg_left (hstat_le v) hK.le)
      have hCi : IntegrableOn (fun v : ℝ × ℝ => Cj * B * ‖Rprod W v‖) pbox :=
        prop71_box_integrableOn_of_bounded (C := Cj * B * (W.card : ℝ) ^ 3)
          (measurable_const.mul hRf_meas) (by positivity)
          (fun v => by
            rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg hCj.le hB_nonneg) (norm_nonneg _))]
            exact mul_le_mul_of_nonneg_left (norm_Rprod_le W v) (mul_nonneg hCj.le hB_nonneg))
      rw [integral_add hKi hCi, integral_const_mul, integral_const_mul]
    calc (∫ v : ℝ × ℝ, ‖Rprod W v‖ * ‖innerInt N m v‖)
        = ∫ v in pbox, ‖Rprod W v‖ * ‖innerInt N m v‖ := h1
      _ ≤ ∫ v in pbox, (K * A v + Cj * B * ‖Rprod W v‖) := h2
      _ = K * (∫ v in pbox, A v) + (Cj * B) * (∫ v in pbox, ‖Rprod W v‖) := h3
  -- `∫_{pbox} ‖Rprod W v‖ ≤ (9/4)|W|³`.
  have hpbox_ne_top : (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)) pbox ≠ ⊤ :=
    (prop71_box_isCompact_pbox.measure_lt_top).ne
  have hD : ∫ v in pbox, ‖Rprod W v‖ ≤ (9 / 4) * (W.card : ℝ) ^ 3 := by
    have h := setIntegral_mono_of_nonneg (f := fun v : ℝ × ℝ => ‖Rprod W v‖)
      (g := fun _ : ℝ × ℝ => (W.card : ℝ) ^ 3)
      (fun v _ => norm_nonneg _) (fun v _ => norm_Rprod_le W v)
      (integrableOn_const (C := (W.card : ℝ) ^ 3) hpbox_ne_top)
    rw [setIntegral_const, Measure.real_def, prop71_pbox_measure, smul_eq_mul] at h
    exact h
  have hstep : (Cj * B) * (∫ v in pbox, ‖Rprod W v‖) ≤
      (Cj * B) * ((9 / 4) * (W.card : ℝ) ^ 3) :=
    mul_le_mul_of_nonneg_left hD (mul_nonneg hCj.le hB_nonneg)
  calc (∫ v : ℝ × ℝ, ‖Rprod W v‖ * ‖innerInt N m v‖)
      ≤ K * (∫ v in pbox, A v) + (Cj * B) * (∫ v in pbox, ‖Rprod W v‖) := hmain_le
    _ ≤ K * (∫ v in pbox, A v) + (Cj * B) * ((9 / 4) * (W.card : ℝ) ^ 3) := by
          linarith [hstep]
    _ = K * (∫ v in pbox, A v) + (9 / 4) * Cj * ((W.card : ℝ) ^ 3 * B) := by ring

end Work.GM.S3
