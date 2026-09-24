/-
# `ApSumTenth.TailAux` — auxiliary material for the classical tail bound

This module collects the elementary analytic facts about the Rosser–Iwaniec profile pair
`(riPhi, riPsi)` that the proof of the classical tail bound

  `∫_{Ici (s-1)} riPsi ≤ 2 e^γ (1 + ∫_2^{s-1} log (t-1)/t) - s`   for `3 ≤ s ≤ 4`

needs: the closed forms of `riPhi` on `[1,3]` and of `riPsi` on `[2,3]`
(writing `Ctot = ∫_2^∞ riPsi`), the crude domination `riPhi ≤ crudeU`, `riPsi ≤ crudeV`,
integrability of `riPhi`, `riPsi` on half lines, measurability, and the Buchstab test
function `buchstabA` of the classical limit argument.
-/
import Mathlib
import Submission.Work.NumberTheory.Chen.APSwitchUpper.prof
import Submission.Work.NumberTheory.Chen.APSwitchUpper.profC_intervalIntegrable
import Submission.Work.NumberTheory.Chen.APSwitchUpper.riPhiDelay
import Submission.Work.NumberTheory.Chen.APSwitchUpper.riPhiLevelCore
import Submission.Work.NumberTheory.Chen.APSwitchUpper.riPhi_le_env
import Submission.Work.NumberTheory.Chen.APSwitchUpper.riPhiSharpCrude
import Submission.Work.NumberTheory.Chen.APSwitchUpper.level_bounds
import Submission.Work.NumberTheory.Chen.APSwitchUpper.crudeLevelBounds
import Submission.Work.NumberTheory.Chen.ApSumTenth.riPhi_delay_identity
import Submission.Work.NumberTheory.Chen.ApSumTenth.riPhi_delay_system
import Submission.Work.NumberTheory.Chen.ApSumTenth.integral_riPhi_Ici_one
import Submission.Work.NumberTheory.Chen.ApSumTenth.Defs

open MeasureTheory Filter
open scoped Topology
open Work.NumberTheory.Chen.APSwitchUpper

namespace Work.NumberTheory.Chen.ApSumTenth

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## §1  The closed form of `riPhi` on `[1,3]` -/

theorem riPhi_eq_of_mem_Icc {s : ℝ} (h1 : 1 ≤ s) (h3 : s ≤ 3) :
    riPhi s = (3 - s + Ctot) / s := by
  have hs : s ≠ 0 := by linarith
  have h := riPhi_delay_system.1 s h1 h3
  rw [riSys_integral_Ici_two_riPsi] at h
  rw [eq_div_iff hs]
  linarith

/-! ## §2  The crude bounds and the pointwise domination by `crudeU`, `crudeV` -/

theorem Ctot_le_four : Ctot ≤ 4 := by
  have hlim := hasSum_P.tendsto_sum_nat
  refine le_of_tendsto hlim ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [← Cv_eq_sum_P]
  exact level_bounds.1 m

theorem riPhi_le_crudeU_of_two_le {s : ℝ} (hs : 2 ≤ s) : riPhi s ≤ crudeU s :=
  le_of_tendsto (tendsto_evenSum s (by linarith))
    (Eventually.of_forall fun n => level_evenSum_le_crudeU n hs)

theorem riPhi_le_crudeU {s : ℝ} (hs : 1 ≤ s) : riPhi s ≤ crudeU s := by
  rcases lt_or_ge s 2 with h2 | h2
  · have h := riPhi_eq_of_mem_Icc hs (by linarith)
    rw [h, crudeU_of_mem hs (by linarith)]
    rw [div_le_div_iff_of_pos_right (by linarith : (0 : ℝ) < s)]
    linarith [Ctot_le_four]
  · exact riPhi_le_crudeU_of_two_le h2

theorem riPsi_le_crudeV {s : ℝ} (hs : 2 ≤ s) : riPsi s ≤ crudeV s := by
  have hsum := riSys_summable_odd s hs
  have hlim : Tendsto (fun n : ℕ => oddSum n s) atTop (𝓝 (riPsi s)) := by
    have h := hsum.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    have hev : (fun n : ℕ => (fun i : ℕ => ∑ j ∈ Finset.range i, profC (2 * j + 1) s) (n + 1))
        =ᶠ[atTop] fun n : ℕ => oddSum n s := by
      filter_upwards with n
      rw [oddSum_eq_sum]
    exact Tendsto.congr' hev h
  exact le_of_tendsto hlim (Eventually.of_forall fun n => riSys_oddSum_le_crudeV n s hs)

/-! ## §3  Measurability -/

theorem profC_eq_zero_of_lt_one (j : ℕ) {s : ℝ} (hs : s < 1) : profC j s = 0 := by
  induction j with
  | zero =>
      rw [profC_zero, if_neg]
      rintro ⟨h, -⟩
      linarith
  | succ n ih =>
      rw [profC_succ]
      by_cases hpar : (n + 1) % 2 = 0
      · rw [if_pos hpar, if_neg]
        rintro ⟨h, -⟩
        linarith
      · rw [if_neg hpar, if_neg]
        rintro ⟨h, -⟩
        linarith

theorem profC_odd_eq_zero_of_lt_two (i : ℕ) {s : ℝ} (hs : s < 2) : profC (2 * i + 1) s = 0 := by
  rw [profC_succ (2 * i) s]
  have hpar : ¬ (2 * i + 1) % 2 = 0 := by omega
  rw [if_neg hpar]
  refine if_neg ?_
  rintro ⟨h, -⟩
  linarith

theorem riPhi_eq_zero_of_lt_one {s : ℝ} (hs : s < 1) : riPhi s = 0 := by
  rw [show riPhi s = ∑' j : ℕ, profC (2 * j) s from rfl]
  rw [tsum_congr (fun j => profC_eq_zero_of_lt_one (2 * j) hs), tsum_zero]

theorem riPsi_eq_zero_of_lt_two {s : ℝ} (hs : s < 2) : riPsi s = 0 := by
  rw [show riPsi s = ∑' j : ℕ, profC (2 * j + 1) s from rfl]
  rw [tsum_congr (fun j => profC_odd_eq_zero_of_lt_two j hs), tsum_zero]

theorem tendsto_evenSum_all (s : ℝ) :
    Tendsto (fun n : ℕ => evenSum n s) atTop (𝓝 (riPhi s)) := by
  rcases lt_or_ge s 1 with h | h
  · have hz : ∀ n : ℕ, evenSum n s = 0 := by
      intro n
      rw [evenSum_eq_sum]
      exact Finset.sum_eq_zero fun j _ => profC_eq_zero_of_lt_one (2 * j) h
    rw [riPhi_eq_zero_of_lt_one h]
    simp only [hz]
    exact tendsto_const_nhds
  · exact tendsto_evenSum s h

theorem tendsto_oddSum_all (s : ℝ) :
    Tendsto (fun n : ℕ => oddSum n s) atTop (𝓝 (riPsi s)) := by
  rcases lt_or_ge s 2 with h | h
  · have hz : ∀ n : ℕ, oddSum n s = 0 := by
      intro n
      rw [oddSum_eq_sum]
      exact Finset.sum_eq_zero fun i _ => profC_odd_eq_zero_of_lt_two i h
    rw [riPsi_eq_zero_of_lt_two h]
    simp only [hz]
    exact tendsto_const_nhds
  · have hsum := riSys_summable_odd s h
    have h2 : Tendsto (fun n : ℕ => ∑ i ∈ Finset.range (n + 1), profC (2 * i + 1) s) atTop
        (𝓝 (riPsi s)) := by
      have h' := hsum.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
      have hev : (fun n : ℕ => (fun i : ℕ => ∑ j ∈ Finset.range i, profC (2 * j + 1) s) (n + 1))
          =ᶠ[atTop] fun n : ℕ => ∑ i ∈ Finset.range (n + 1), profC (2 * i + 1) s :=
        Eventually.of_forall fun n => rfl
      exact Tendsto.congr' hev h'
    exact h2

theorem riPhi_measurable : Measurable riPhi :=
  measurable_of_tendsto_metrizable (f := fun n s => evenSum n s) (g := riPhi)
    (fun n => by
      rw [show (fun s : ℝ => evenSum n s)
          = fun s : ℝ => ∑ j ∈ Finset.range (n + 1), profC (2 * j) s from by
        funext s; rw [evenSum_eq_sum]]
      exact Finset.measurable_sum _ fun j _ => profC_measurable (2 * j))
    (tendsto_pi_nhds.mpr tendsto_evenSum_all)

theorem riPsi_measurable : Measurable riPsi :=
  measurable_of_tendsto_metrizable (f := fun n s => oddSum n s) (g := riPsi)
    (fun n => by
      rw [show (fun s : ℝ => oddSum n s)
          = fun s : ℝ => ∑ j ∈ Finset.range (n + 1), profC (2 * j + 1) s from by
        funext s; rw [oddSum_eq_sum]]
      exact Finset.measurable_sum _ fun j _ => profC_measurable (2 * j + 1))
    (tendsto_pi_nhds.mpr tendsto_oddSum_all)

/-! ## §4  Integrability on half lines -/

theorem integrableOn_exp_three_sub_Ioi (a : ℝ) :
    IntegrableOn (fun s : ℝ => 2 * Real.exp (3 - s)) (Set.Ioi a) := by
  have hmul : IntegrableOn (fun s : ℝ => 2 * Real.exp 3 * Real.exp (-s)) (Set.Ioi a) :=
    Integrable.const_mul (integrableOn_exp_neg_Ioi a) (2 * Real.exp 3)
  refine hmul.congr_fun ?_ measurableSet_Ioi
  intro x _
  simp only []
  rw [show (3 : ℝ) - x = 3 + (-x) by ring, Real.exp_add]
  ring

theorem integrableOn_crudeV_Ici (a : ℝ) : IntegrableOn crudeV (Set.Ici a) := by
  have hmul : IntegrableOn (fun s : ℝ => 6 * Real.exp 2 * Real.exp (-s)) (Set.Ioi a) :=
    Integrable.const_mul (integrableOn_exp_neg_Ioi a) (6 * Real.exp 2)
  have hIoi : IntegrableOn crudeV (Set.Ioi a) := by
    refine hmul.congr_fun ?_ measurableSet_Ioi
    intro x _
    simp only []
    rw [crudeV, show (2 : ℝ) - x = 2 + (-x) by ring, Real.exp_add]
    ring
  exact hIoi.congr_set_ae Ioi_ae_eq_Ici.symm

theorem integrableOn_crudeU_Icc_three (a : ℝ) (ha : 1 ≤ a) :
    IntegrableOn crudeU (Set.Icc a 3) := by
  have hcont : ContinuousOn (fun s : ℝ => (9 - s) / s) (Set.Icc a 3) := by
    refine ContinuousOn.div (by fun_prop) continuousOn_id ?_
    intro x hx
    have : (0 : ℝ) < x := lt_of_lt_of_le (by linarith) hx.1
    exact ne_of_gt this
  refine (hcont.integrableOn_compact isCompact_Icc).congr_fun ?_ measurableSet_Icc
  intro x hx
  rw [crudeU_of_mem (by linarith [ha, hx.1]) hx.2]

theorem integrableOn_crudeU_Ioi_three : IntegrableOn crudeU (Set.Ioi 3) := by
  refine (integrableOn_exp_three_sub_Ioi 3).congr_fun ?_ measurableSet_Ioi
  intro x hx
  rw [crudeU_of_three_le' (le_of_lt hx)]

theorem integrableOn_crudeU_Ici (a : ℝ) (ha : 1 ≤ a) : IntegrableOn crudeU (Set.Ici a) := by
  rcases le_or_gt a 3 with h3 | h3
  · rw [← Set.Icc_union_Ioi_eq_Ici h3]
    exact (integrableOn_crudeU_Icc_three a ha).union integrableOn_crudeU_Ioi_three
  · exact integrableOn_crudeU_Ioi_three.mono_set fun x hx => lt_of_lt_of_le h3 hx

theorem integrableOn_riPhi_Ici_one : IntegrableOn riPhi (Set.Ici 1) := by
  have hunion : IntegrableOn riPhi (Set.Ioi 1) := by
    rw [← Set.Ioc_union_Ici_eq_Ioi (show (1 : ℝ) < 3 by norm_num)]
    refine IntegrableOn.union ?_ ?_
    · have hcont : ContinuousOn (fun s : ℝ => (3 - s + Ctot) / s) (Set.Icc 1 3) := by
        refine ContinuousOn.div (by fun_prop) continuousOn_id ?_
        intro x hx
        exact ne_of_gt (lt_of_lt_of_le (by norm_num) hx.1)
      refine ((hcont.integrableOn_compact isCompact_Icc).mono_set
        Set.Ioc_subset_Icc_self).congr_fun ?_ measurableSet_Ioc
      intro x hx
      rw [riPhi_eq_of_mem_Icc hx.1.le hx.2]
    · refine Integrable.mono' (integrableOn_crudeU_Ici 3 (by norm_num))
        riPhi_measurable.aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (riPhi_nonneg x)]
      exact riPhi_le_crudeU (by linarith [Set.mem_Ici.mp hx])
  exact hunion.congr_set_ae Ioi_ae_eq_Ici.symm

theorem integrableOn_riPhi_Ici_two : IntegrableOn riPhi (Set.Ici 2) :=
  integrableOn_riPhi_Ici_one.mono_set (Set.Ici_subset_Ici.mpr (by norm_num))

theorem integrableOn_riPsi_Ici_two : IntegrableOn riPsi (Set.Ici 2) := by
  refine Integrable.mono' (integrableOn_crudeV_Ici 2) riPsi_measurable.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (riPsi_nonneg x)]
  exact riPsi_le_crudeV (by linarith [Set.mem_Ici.mp hx])

/-! ## §5  The closed form of `riPsi` on `[2,3]` -/

theorem integral_riPhi_one_to (x : ℝ) (hx : 1 ≤ x) (hx3 : x ≤ 3) :
    (∫ s in (1 : ℝ)..x, riPhi s) = (3 + Ctot) * Real.log x - (x - 1) := by
  have hcongr : (∫ s in (1 : ℝ)..x, riPhi s)
      = ∫ s in (1 : ℝ)..x, ((3 + Ctot) * s⁻¹ - 1) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le hx] at hs
    rw [riPhi_eq_of_mem_Icc hs.1 (le_trans hs.2 hx3)]
    have hs0 : s ≠ 0 := by linarith [hs.1]
    field_simp
    ring
  rw [hcongr]
  have hdiv : IntervalIntegrable (fun s : ℝ => (3 + Ctot) * s⁻¹) volume (1 : ℝ) x := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.mul continuousOn_const ?_
    refine ContinuousOn.inv₀ continuousOn_id ?_
    intro y hy
    rw [Set.uIcc_of_le hx] at hy
    exact ne_of_gt (lt_of_lt_of_le (by norm_num) hy.1)
  have hone : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume (1 : ℝ) x :=
    intervalIntegrable_const
  rw [intervalIntegral.integral_sub hdiv hone,
    intervalIntegral.integral_const_mul (3 + Ctot) (fun s : ℝ => s⁻¹),
    integral_inv (a := (1 : ℝ)) (b := x) (by
      rw [Set.uIcc_of_le hx]
      rintro ⟨h1, h2⟩
      linarith),
    intervalIntegral.integral_const, smul_eq_mul, mul_one, Real.log_div (by linarith) (by norm_num),
    Real.log_one, sub_zero]

theorem riPsi_eq_of_mem_Icc {u : ℝ} (h2 : 2 ≤ u) (h3 : u ≤ 3) :
    riPsi u = 1 - (3 + Ctot) * Real.log (u - 1) / u := by
  have hu : u ≠ 0 := by linarith
  have h := riPhi_delay_system.2 u h2
  have hsplit := intervalIntegral.integral_Ici_sub_Ici' (f := riPhi) (a := (1 : ℝ))
    (b := u - 1) integrableOn_riPhi_Ici_one
    (integrableOn_riPhi_Ici_one.mono_set (Set.Ici_subset_Ici.mpr (by linarith)))
  have hval : (∫ s in Set.Ici (u - 1), riPhi s) = u - (3 + Ctot) * Real.log (u - 1) := by
    have h1 := integral_riPhi_one_to (u - 1) (by linarith) (by linarith)
    have h2' := integral_riPhi_Ici_one
    linarith
  rw [hval] at h
  have hdiv : riPsi u = (u - (3 + Ctot) * Real.log (u - 1)) / u := by
    rw [eq_div_iff hu]
    rw [mul_comm]
    exact h
  rw [hdiv]
  field_simp

/-! ## §6  The Buchstab test function -/

/-- The Buchstab test function of the classical limit argument: for `s ≥ 2` it is
`s·(2 + riPhi s - riPsi s) = s·(F s + f s)` (the sum of the Rosser–Iwaniec upper function
`F = 1 + riPhi` and of `f = 1 - riPsi`), frozen at its value `3 + Ctot` on `(-∞,2]`.
It satisfies the Buchstab delay recurrence `A s = (3 + Ctot) + ∫_1^{s-1} A v / v dv`
under the normalization `Ctot log 3 + Ttot = 4 - 3 log 3`. -/
noncomputable def buchstabA (s : ℝ) : ℝ :=
  if s ≤ 2 then (3 + Ctot) else s * (2 + riPhi s - riPsi s)

theorem buchstabA_of_le_two {s : ℝ} (hs : s ≤ 2) : buchstabA s = 3 + Ctot :=
  if_pos hs

theorem buchstabA_of_two_le {s : ℝ} (hs : 2 ≤ s) :
    buchstabA s = s * (2 + riPhi s - riPsi s) := by
  rcases eq_or_lt_of_le hs with h | h
  · subst h
    rw [buchstabA, if_pos le_rfl, riPhi_eq_of_mem_Icc (by norm_num) (by norm_num),
      riPsi_eq_of_mem_Icc (by norm_num) (by norm_num)]
    norm_num [Real.log_one]
    ring
  · rw [buchstabA, if_neg (not_le.mpr h)]

theorem buchstabA_measurable : Measurable buchstabA := by
  have h : buchstabA = fun s : ℝ => if s ≤ 2 then (3 + Ctot) else s * (2 + riPhi s - riPsi s) :=
    funext fun s => rfl
  rw [h]
  exact Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const
    (measurable_id.mul ((measurable_const.add riPhi_measurable).sub riPsi_measurable))

end

end Work.NumberTheory.Chen.ApSumTenth
