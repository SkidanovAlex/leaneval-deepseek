import Mathlib
import Submission.Work.GM.S3.prop71_box_integral_bound
import Submission.Work.GM.S3.prop71_inner_tail
import Submission.Work.GM.S3.prop71_pbox_measure
import Submission.Work.GM.S3.prop71_defs

namespace Work.GM.S3

open Complex Finset MeasureTheory
open scoped BigOperators
open Submission.GM (Rfun Separated Iterm hhat hfun)

/-- Generalization of `Work.GM.S3.prop71_box_integral_bound` from `S = pbox` to an arbitrary
measurable set `S ⊆ pbox` off which the inner integral `innerInt N m v` vanishes.  All the
`pbox`-occurrences in the *integral domain* become `S`; the error term `(9/4) Cj |W|³ B` is
unchanged since `∫_S ‖Rprod W v‖ ≤ ∫_pbox ‖Rprod W v‖ ≤ (9/4)|W|³`.  Proved by the same
argument as `prop71_box_integral_bound`, with `hvanish` in place of `prop71_inner_support`. -/
theorem box_integral_bound_of_set (K Cj : ℝ) (hK : 0 < K) (hCj : 0 < Cj) (j : ℕ)
    (hin : ∀ (N : ℕ) (m : ℤ × ℤ × ℤ) (v : ℝ × ℝ), ‖innerInt N m v‖ ≤ K)
    (hdec : ∀ (N : ℕ) (m : ℤ × ℤ × ℤ) (v : ℝ × ℝ), v ∈ pbox → (N : ℝ) * phas m v ≠ 0 →
      ‖innerInt N m v‖ ≤ Cj / |(N : ℝ) * phas m v| ^ j)
    (S : Set (ℝ × ℝ)) (hSmeas : MeasurableSet S) (hSsub : S ⊆ pbox)
    (hvanish : ∀ (N : ℕ) (m : ℤ × ℤ × ℤ) (v : ℝ × ℝ), v ∉ S → innerInt N m v = 0)
    (N : ℕ) (hN : 1 ≤ N) (η : ℝ) (hη : 0 < η) (W : Finset ℝ) (m : ℤ × ℤ × ℤ) :
    (∫ v : ℝ × ℝ, ‖Rprod W v‖ * ‖innerInt N m v‖) ≤
      K * (∫ v in S, (if |phas m v| ≤ (Submission.LargeValues.M N) ^ η / (N : ℝ)
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
  -- Integrability of the pieces on `pbox`, hence on `S ⊆ pbox`.
  have hRf_IO_pbox : IntegrableOn (fun v : ℝ × ℝ => ‖Rprod W v‖) pbox :=
    prop71_box_integrableOn_of_bounded hRf_meas hcardpow_nonneg
      (fun v => by rw [Real.norm_of_nonneg (norm_nonneg _)]; exact norm_Rprod_le W v)
  have hstat_IO_pbox : IntegrableOn A pbox :=
    prop71_box_integrableOn_of_bounded hstat_meas hcardpow_nonneg
      (fun v => by rw [Real.norm_of_nonneg (hA_nonneg v)]; exact hstat_le v)
  have hRf_IO : IntegrableOn (fun v : ℝ × ℝ => ‖Rprod W v‖) S := hRf_IO_pbox.mono_set hSsub
  have hstat_IO : IntegrableOn A S := hstat_IO_pbox.mono_set hSsub
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
  have hg_IO_pbox : IntegrableOn (fun v : ℝ × ℝ => K * A v + Cj * B * ‖Rprod W v‖) pbox :=
    prop71_box_integrableOn_of_bounded hg_meas (by positivity) hg_bound
  have hg_IO : IntegrableOn (fun v : ℝ × ℝ => K * A v + Cj * B * ‖Rprod W v‖) S :=
    hg_IO_pbox.mono_set hSsub
  -- Pointwise bound on `pbox` (hence on `S`): `hin` on the stationary part, `prop71_inner_tail`
  -- off it.
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
  -- Off `S` the integrand vanishes, so the full integral may be restricted to `S`.
  have h1 : (∫ v : ℝ × ℝ, ‖Rprod W v‖ * ‖innerInt N m v‖)
      = ∫ v in S, ‖Rprod W v‖ * ‖innerInt N m v‖ :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero
      (f := fun v : ℝ × ℝ => ‖Rprod W v‖ * ‖innerInt N m v‖) (s := S)
      (fun v hv => by rw [hvanish N m v hv]; simp)).symm
  -- The main chain of inequalities, now on `S`.
  have hmain_le : (∫ v : ℝ × ℝ, ‖Rprod W v‖ * ‖innerInt N m v‖) ≤
      K * (∫ v in S, A v) + (Cj * B) * (∫ v in S, ‖Rprod W v‖) := by
    have h2 : ∫ v in S, ‖Rprod W v‖ * ‖innerInt N m v‖
        ≤ ∫ v in S, (K * A v + Cj * B * ‖Rprod W v‖) :=
      setIntegral_mono_of_nonneg (fun v _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (fun v hv => hpt v (hSsub hv)) hg_IO
    have h3 : ∫ v in S, (K * A v + Cj * B * ‖Rprod W v‖)
        = K * (∫ v in S, A v) + (Cj * B) * (∫ v in S, ‖Rprod W v‖) := by
      have hKi : IntegrableOn (fun v : ℝ × ℝ => K * A v) S := hstat_IO.const_mul K
      have hCi : IntegrableOn (fun v : ℝ × ℝ => Cj * B * ‖Rprod W v‖) S :=
        hRf_IO.const_mul (Cj * B)
      rw [integral_add hKi hCi, integral_const_mul, integral_const_mul]
    calc (∫ v : ℝ × ℝ, ‖Rprod W v‖ * ‖innerInt N m v‖)
        = ∫ v in S, ‖Rprod W v‖ * ‖innerInt N m v‖ := h1
      _ ≤ ∫ v in S, (K * A v + Cj * B * ‖Rprod W v‖) := h2
      _ = K * (∫ v in S, A v) + (Cj * B) * (∫ v in S, ‖Rprod W v‖) := h3
  -- `∫_S ‖Rprod W v‖ ≤ vol(S) |W|³ ≤ (9/4)|W|³`, since `S ⊆ pbox` and `vol(pbox) = 9/4`.
  have hpbox_ne_top : (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)) pbox ≠ ⊤ :=
    (prop71_box_isCompact_pbox.measure_lt_top).ne
  have hSne : (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)) S ≠ ⊤ :=
    ne_top_of_le_ne_top hpbox_ne_top (measure_mono hSsub)
  have hvolS : ((MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)) S).toReal ≤ 9 / 4 := by
    have hle : (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)) S
        ≤ (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)) pbox := measure_mono hSsub
    calc ((MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)) S).toReal
        ≤ ((MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)) pbox).toReal :=
          ENNReal.toReal_mono hpbox_ne_top hle
      _ = 9 / 4 := prop71_pbox_measure
  have hD : ∫ v in S, ‖Rprod W v‖ ≤ (9 / 4) * (W.card : ℝ) ^ 3 := by
    have h := setIntegral_mono_of_nonneg (f := fun v : ℝ × ℝ => ‖Rprod W v‖)
      (g := fun _ : ℝ × ℝ => (W.card : ℝ) ^ 3)
      (fun v _ => norm_nonneg _) (fun v _ => norm_Rprod_le W v)
      (integrableOn_const (C := (W.card : ℝ) ^ 3) hSne)
    rw [setIntegral_const, Measure.real_def, smul_eq_mul] at h
    exact h.trans (mul_le_mul_of_nonneg_right hvolS hcardpow_nonneg)
  have hstep : (Cj * B) * (∫ v in S, ‖Rprod W v‖) ≤
      (Cj * B) * ((9 / 4) * (W.card : ℝ) ^ 3) :=
    mul_le_mul_of_nonneg_left hD (mul_nonneg hCj.le hB_nonneg)
  calc (∫ v : ℝ × ℝ, ‖Rprod W v‖ * ‖innerInt N m v‖)
      ≤ K * (∫ v in S, A v) + (Cj * B) * (∫ v in S, ‖Rprod W v‖) := hmain_le
    _ ≤ K * (∫ v in S, A v) + (Cj * B) * ((9 / 4) * (W.card : ℝ) ^ 3) := by
          linarith [hstep]
    _ = K * (∫ v in S, A v) + (9 / 4) * Cj * ((W.card : ℝ) ^ 3 * B) := by ring

end Work.GM.S3
