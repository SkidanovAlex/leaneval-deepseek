/-
# `ApSumTenth.riPsi_tail_le_classical_of_inputs` — the classical tail bound for `riPsi`

Target (`TailBound`):  for `3 ≤ s ≤ 4`,

  `∫_{Ici (s-1)} riPsi ≤ 2 e^γ (1 + ∫_2^{s-1} log (t-1)/t dt) - s`.

## Route

Write `Ctot = ∫_{Ici 2} riPsi`.  The summed delay identity (`riPhi_delay_identity`) gives, for
`s ≥ 3`, `s · riPhi s = ∫_{Ici (s-1)} riPsi`, and splitting at `2` together with the closed
form `riPsi u = 1 - (3 + Ctot) log (u-1)/u` on `[2,3]` (`TailAux`) yields

  `∫_{Ici (s-1)} riPsi = Ctot - (s-3) + (3+Ctot) · J`,   `J = ∫_2^{s-1} log (t-1)/t dt`.

The target is therefore *equivalent* to `(Ctot + 3 - 2e^γ)(1 + J) ≤ 0`, i.e. to the single
scalar inequality `Ctot ≤ 2e^γ - 3`.

That scalar inequality is the classical mass constant of the linear sieve; it is obtained from
the supplied Buchstab delay-limit theorem `hbuch` applied to the test function

  `buchstabA s = 3 + Ctot` (`s ≤ 2`),   `buchstabA s = s·(2 + riPhi s - riPsi s)` (`s ≥ 2`)

(`TailAux`).  The function is constant `3 + Ctot` on `[1,2]`, satisfies the Buchstab recurrence
`buchstabA s = (3+Ctot) + ∫_1^{s-1} buchstabA v/v dv` for `s ≥ 2`, grows at most linearly, and
`buchstabA s / s → 2`; hence `hbuch` gives `2 = (3 + Ctot) e^{-γ}`, i.e. `Ctot = 2e^γ - 3`.
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
import Submission.Work.NumberTheory.Chen.ApSumTenth.TailAux

open MeasureTheory Filter
open scoped Topology
open Work.NumberTheory.Chen.APSwitchUpper

namespace Work.NumberTheory.Chen.ApSumTenth

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Auxiliary development (kept in a sub-namespace to avoid collisions) -/

namespace TailOfInputs

/-! ### §1  Two-sided bounds for the profiles and for the test function -/

theorem crudeU_le_eight (s : ℝ) : crudeU s ≤ 8 := by
  rcases lt_or_ge s 1 with h | h
  · rw [crudeU, if_pos h]
  · rcases le_or_gt s 3 with h3 | h3
    · rw [crudeU_of_mem h h3, div_le_iff₀ (by linarith : (0 : ℝ) < s)]
      linarith
    · rw [crudeU_of_three_lt h3]
      have h1 := Real.exp_le_one_iff.mpr (show 3 - s ≤ 0 by linarith)
      have h2 := Real.exp_pos (3 - s)
      linarith

theorem abs_riPhi_le_eight (s : ℝ) : |riPhi s| ≤ 8 := by
  rcases lt_or_ge s 1 with h | h
  · rw [riPhi_eq_zero_of_lt_one h, abs_zero]; norm_num
  · rw [abs_of_nonneg (riPhi_nonneg s)]
    exact le_trans (riPhi_le_crudeU h) (crudeU_le_eight s)

theorem abs_riPsi_le_six (s : ℝ) : |riPsi s| ≤ 6 := by
  rcases lt_or_ge s 2 with h | h
  · rw [riPsi_eq_zero_of_lt_two h, abs_zero]; norm_num
  · rw [abs_of_nonneg (riPsi_nonneg s)]
    have h1 : riPsi s ≤ crudeV s := riPsi_le_crudeV h
    have h2 : crudeV s ≤ 6 := by
      have hexp : Real.exp (2 - s) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      have hpos := Real.exp_pos (2 - s)
      rw [crudeV]
      linarith
    linarith

theorem Ctot_nonneg : (0 : ℝ) ≤ Ctot := tsum_nonneg fun i => P_nonneg i

theorem abs_buchstabA_le (s : ℝ) : |buchstabA s| ≤ 7 + 16 * |s| := by
  rcases lt_or_ge s 2 with h | h
  · rw [buchstabA_of_le_two h.le,
      abs_of_nonneg (by linarith [Ctot_nonneg] : (0 : ℝ) ≤ 3 + Ctot)]
    have h4 := Ctot_le_four
    have := abs_nonneg s
    linarith
  · rw [buchstabA_of_two_le h, abs_mul]
    have h2 : |2 + riPhi s - riPsi s| ≤ 16 := by
      have h1 := abs_riPhi_le_eight s
      have h2' := abs_riPsi_le_six s
      calc |2 + riPhi s - riPsi s| = |(2 + riPhi s) - riPsi s| := rfl
        _ ≤ |2 + riPhi s| + |riPsi s| := abs_sub _ _
        _ ≤ (|(2 : ℝ)| + |riPhi s|) + |riPsi s| := by
              have := abs_add_le (2 : ℝ) (riPhi s)
              linarith
        _ ≤ 16 := by norm_num at *; linarith
    have habs : (0 : ℝ) ≤ |s| := abs_nonneg s
    calc |s| * |2 + riPhi s - riPsi s| ≤ |s| * 16 := by nlinarith
      _ ≤ 7 + 16 * |s| := by linarith

theorem abs_le_max_of_mem_uIoc {a b x : ℝ} (hx : x ∈ Set.uIoc a b) :
    |x| ≤ max |a| |b| := by
  have hA : |a| ≤ max |a| |b| := le_max_left _ _
  have hB : |b| ≤ max |a| |b| := le_max_right _ _
  rw [abs_le] at hA hB ⊢
  rcases Set.mem_uIoc.mp hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨by linarith [hA.1], by linarith [hB.2]⟩
  · exact ⟨by linarith [hB.1], by linarith [hA.2]⟩

/-! ### §2  Interval integrability -/

theorem intervalIntegrable_riPhi_any (a b : ℝ) : IntervalIntegrable riPhi volume a b := by
  rw [intervalIntegrable_iff]
  refine IntegrableOn.of_bound ?_ riPhi_measurable.aestronglyMeasurable 8 ?_
  · rw [Real.volume_uIoc]; exact ENNReal.ofReal_lt_top
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with x _
    rw [Real.norm_eq_abs]
    exact abs_riPhi_le_eight x

theorem intervalIntegrable_riPsi_any (a b : ℝ) : IntervalIntegrable riPsi volume a b := by
  rw [intervalIntegrable_iff]
  refine IntegrableOn.of_bound ?_ riPsi_measurable.aestronglyMeasurable 6 ?_
  · rw [Real.volume_uIoc]; exact ENNReal.ofReal_lt_top
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with x _
    rw [Real.norm_eq_abs]
    exact abs_riPsi_le_six x

theorem intervalIntegrable_buchstabA_any (a b : ℝ) : IntervalIntegrable buchstabA volume a b := by
  rw [intervalIntegrable_iff]
  refine IntegrableOn.of_bound ?_ buchstabA_measurable.aestronglyMeasurable
    (7 + 16 * max |a| |b|) ?_
  · rw [Real.volume_uIoc]; exact ENNReal.ofReal_lt_top
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
    rw [Real.norm_eq_abs]
    have h1 := abs_buchstabA_le x
    have h2 := abs_le_max_of_mem_uIoc hx
    linarith

theorem intervalIntegrable_buchstabA_div_any (a b : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    IntervalIntegrable (fun v => buchstabA v / v) volume a b := by
  rw [intervalIntegrable_iff]
  refine IntegrableOn.of_bound ?_
    ((buchstabA_measurable.div measurable_id)).aestronglyMeasurable
    (7 + 16 * max |a| |b|) ?_
  · rw [Real.volume_uIoc]; exact ENNReal.ofReal_lt_top
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
    have hx1 : (1 : ℝ) < x := by
      rcases Set.mem_uIoc.mp hx with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact lt_of_le_of_lt ha h1
      · exact lt_of_le_of_lt hb h1
    have hxpos : (0 : ℝ) < x := by linarith
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hxpos, div_le_iff₀ hxpos]
    have h1 : |buchstabA x| ≤ 7 + 16 * x := by
      have := abs_buchstabA_le x
      rwa [abs_of_pos hxpos] at this
    have h2 : x ≤ max |a| |b| := by
      have := abs_le_max_of_mem_uIoc hx
      rwa [abs_of_pos hxpos] at this
    nlinarith [h1, h2, hxpos, hx1]

/-! ### §3  The limit `buchstabA s / s → 2` -/

theorem tendsto_riPhi_zero : Tendsto riPhi atTop (nhds 0) := by
  have hexp : Tendsto (fun s : ℝ => 2 * Real.exp (3 - s)) atTop (nhds 0) := by
    have h1 : Tendsto (fun s : ℝ => Real.exp (-s)) atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
    have h2 : Tendsto (fun s : ℝ => 2 * Real.exp 3 * Real.exp (-s)) atTop
        (nhds (2 * Real.exp 3 * 0)) := tendsto_const_nhds.mul h1
    rw [mul_zero] at h2
    refine h2.congr' ?_
    filter_upwards with s
    rw [show (3 : ℝ) - s = 3 + (-s) by ring, Real.exp_add]
    ring
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hexp ?_ ?_
  · filter_upwards with s
    exact riPhi_nonneg s
  · filter_upwards [eventually_ge_atTop (3 : ℝ)] with s hs
    rw [← crudeU_of_three_le' hs]
    exact riPhi_le_crudeU (by linarith)

theorem tendsto_riPsi_zero : Tendsto riPsi atTop (nhds 0) := by
  have hexp : Tendsto (fun s : ℝ => 6 * Real.exp (2 - s)) atTop (nhds 0) := by
    have h1 : Tendsto (fun s : ℝ => Real.exp (-s)) atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
    have h2 : Tendsto (fun s : ℝ => 6 * Real.exp 2 * Real.exp (-s)) atTop
        (nhds (6 * Real.exp 2 * 0)) := tendsto_const_nhds.mul h1
    rw [mul_zero] at h2
    refine h2.congr' ?_
    filter_upwards with s
    rw [show (2 : ℝ) - s = 2 + (-s) by ring, Real.exp_add]
    ring
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hexp ?_ ?_
  · filter_upwards with s
    exact riPsi_nonneg s
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with s hs
    exact riPsi_le_crudeV hs

theorem tendsto_buchstabA_div_zero :
    Tendsto (fun s : ℝ => buchstabA s / s) atTop (nhds 2) := by
  have hmain : Tendsto (fun s : ℝ => 2 + riPhi s - riPsi s) atTop (nhds (2 + 0 - 0)) :=
    (tendsto_const_nhds.add tendsto_riPhi_zero).sub tendsto_riPsi_zero
  rw [show (2 + 0 - 0 : ℝ) = 2 by norm_num] at hmain
  refine hmain.congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with s hs
  have hs0 : s ≠ 0 := by linarith
  rw [buchstabA_of_two_le hs, mul_div_cancel_left₀ _ hs0]

theorem buchstabA_lin_bound (s : ℝ) (hs : 1 ≤ s) : |buchstabA s| ≤ 20 * (1 + s) := by
  have h := abs_buchstabA_le s
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ s)] at h
  linarith

/-! ### §4  The global identity `∫_{Ici 2} (riPhi − riPsi)` -/

theorem integral_Ici_two_sub :
    (∫ u in Set.Ici (2 : ℝ), (riPhi u - riPsi u))
      = 6 - (3 + Ctot) * (1 + Real.log 2) := by
  have hΦ : IntegrableOn riPhi (Set.Ici (2 : ℝ)) := integrableOn_riPhi_Ici_two
  have hΨ : IntegrableOn riPsi (Set.Ici (2 : ℝ)) := integrableOn_riPsi_Ici_two
  have hsub : (∫ u in Set.Ici (2 : ℝ), (riPhi u - riPsi u))
      = (∫ u in Set.Ici (2 : ℝ), riPhi u) - (∫ u in Set.Ici (2 : ℝ), riPsi u) :=
    integral_sub hΦ hΨ
  have hΦval : (∫ u in Set.Ici (2 : ℝ), riPhi u) = 3 * riPsi 3 := by
    have h := riSys_mul_riPsi_eq_integral 3 (by norm_num)
    rw [show (3 : ℝ) - 1 = 2 by norm_num] at h
    linarith
  have hΨ3 : riPsi 3 = 1 - (3 + Ctot) * Real.log 2 / 3 := by
    have h := riPsi_eq_of_mem_Icc (u := 3) (by norm_num) (by norm_num)
    rw [show (3 : ℝ) - 1 = 2 by norm_num] at h
    exact h
  rw [hsub, hΦval, riSys_integral_Ici_two_riPsi, hΨ3]
  ring

/-! ### §5  The Buchstab recurrence on `[2,3]` -/

theorem rec_of_le_three (s : ℝ) (hs2 : 2 ≤ s) (hs3 : s ≤ 3) :
    buchstabA s = (3 + Ctot) + ∫ v in (1 : ℝ)..(s - 1), buchstabA v / v := by
  have hs1 : (1 : ℝ) ≤ s - 1 := by linarith
  have h_int : (∫ v in (1 : ℝ)..(s - 1), buchstabA v / v)
      = (3 + Ctot) * Real.log (s - 1) := by
    have hcongr : (∫ v in (1 : ℝ)..(s - 1), buchstabA v / v)
        = ∫ v in (1 : ℝ)..(s - 1), (3 + Ctot) * v⁻¹ := by
      refine intervalIntegral.integral_congr fun v hv => ?_
      rw [Set.uIcc_of_le hs1] at hv
      rw [buchstabA_of_le_two (by linarith [hv.2]), div_eq_mul_inv]
    rw [hcongr, intervalIntegral.integral_const_mul (3 + Ctot),
      integral_inv (a := (1 : ℝ)) (b := s - 1) ?_, div_one]
    rw [Set.uIcc_of_le hs1]
    rintro ⟨h1, h2⟩
    linarith
  rw [h_int, buchstabA_of_two_le hs2, riPhi_eq_of_mem_Icc (by linarith) hs3,
    riPsi_eq_of_mem_Icc hs2 hs3]
  have hs0 : s ≠ 0 := by linarith
  field_simp
  ring

/-! ### §6  The Buchstab recurrence for `s ≥ 3` -/

theorem rec_of_three_le (s : ℝ) (hs : 3 ≤ s) :
    buchstabA s = (3 + Ctot) + ∫ v in (1 : ℝ)..(s - 1), buchstabA v / v := by
  have hs2 : (2 : ℝ) ≤ s := by linarith
  have h2s : (2 : ℝ) ≤ s - 1 := by linarith
  have hIci : Set.Ici (s - 1) ⊆ Set.Ici (2 : ℝ) := Set.Ici_subset_Ici.mpr h2s
  have hΦIci : IntegrableOn riPhi (Set.Ici (s - 1)) :=
    integrableOn_riPhi_Ici_two.mono_set hIci
  have hΨIci : IntegrableOn riPsi (Set.Ici (s - 1)) :=
    integrableOn_riPsi_Ici_two.mono_set hIci
  have hdel1 : s * riPhi s = ∫ u in Set.Ici (s - 1), riPsi u := by
    have h := riPhi_delay_identity s (by linarith : (1 : ℝ) ≤ s)
    have hzero : (3 - s) * (if s ≤ 3 then (1 : ℝ) else 0) = 0 := by
      rcases eq_or_lt_of_le hs with h3 | h3
      · subst h3; norm_num
      · rw [if_neg (not_le.mpr h3), mul_zero]
    rw [max_eq_left h2s, hzero, zero_add] at h
    exact h
  have hdel2 : s * riPsi s = ∫ u in Set.Ici (s - 1), riPhi u :=
    riSys_mul_riPsi_eq_integral s hs2
  have hsubIci : (∫ u in Set.Ici (s - 1), (riPhi u - riPsi u))
      = (∫ u in Set.Ici (s - 1), riPhi u) - (∫ u in Set.Ici (s - 1), riPsi u) :=
    integral_sub hΦIci hΨIci
  have hLHS : buchstabA s = 2 * s - ∫ u in Set.Ici (s - 1), (riPhi u - riPsi u) := by
    rw [buchstabA_of_two_le hs2]
    have hexp : s * (2 + riPhi s - riPsi s) = 2 * s + (s * riPhi s - s * riPsi s) := by ring
    rw [hexp, hdel1, hdel2, hsubIci]
    ring
  have hIntSub2 : IntegrableOn (fun u : ℝ => riPhi u - riPsi u) (Set.Ici (2 : ℝ)) :=
    integrableOn_riPhi_Ici_two.sub integrableOn_riPsi_Ici_two
  have hIntSub3 : IntegrableOn (fun u : ℝ => riPhi u - riPsi u) (Set.Ici (s - 1)) :=
    hIntSub2.mono_set hIci
  have hsplit3 : (∫ u in Set.Ici (2 : ℝ), (riPhi u - riPsi u))
        - (∫ u in Set.Ici (s - 1), (riPhi u - riPsi u))
      = ∫ v in (2 : ℝ)..(s - 1), (riPhi v - riPsi v) :=
    intervalIntegral.integral_Ici_sub_Ici' hIntSub2 hIntSub3
  have hI12val : (∫ v in (1 : ℝ)..(2 : ℝ), buchstabA v / v) = (3 + Ctot) * Real.log 2 := by
    have hcongr : (∫ v in (1 : ℝ)..(2 : ℝ), buchstabA v / v)
        = ∫ v in (1 : ℝ)..(2 : ℝ), (3 + Ctot) * v⁻¹ := by
      refine intervalIntegral.integral_congr fun v hv => ?_
      rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at hv
      rw [buchstabA_of_le_two (by linarith [hv.2]), div_eq_mul_inv]
    rw [hcongr, intervalIntegral.integral_const_mul (3 + Ctot),
      integral_inv (a := (1 : ℝ)) (b := 2) ?_, div_one]
    rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)]
    rintro ⟨h1, h2⟩
    norm_num at h1
  have hI2sval : (∫ v in (2 : ℝ)..(s - 1), buchstabA v / v)
      = ∫ v in (2 : ℝ)..(s - 1), (2 + riPhi v - riPsi v) := by
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [Set.uIcc_of_le h2s] at hv
    have hv2 : (2 : ℝ) ≤ v := hv.1
    have hv0 : v ≠ 0 := by linarith
    rw [buchstabA_of_two_le hv2, mul_div_cancel_left₀ _ hv0]
  have hsplit2 : (∫ v in (2 : ℝ)..(s - 1), (2 + riPhi v - riPsi v))
      = 2 * (s - 3) + ∫ v in (2 : ℝ)..(s - 1), (riPhi v - riPsi v) := by
    have h1 : IntervalIntegrable (fun _ : ℝ => (2 : ℝ)) volume (2 : ℝ) (s - 1) :=
      intervalIntegrable_const
    have h2 : IntervalIntegrable (fun v : ℝ => riPhi v - riPsi v) volume (2 : ℝ) (s - 1) :=
      (intervalIntegrable_riPhi_any 2 (s - 1)).sub (intervalIntegrable_riPsi_any 2 (s - 1))
    have hcongr : (∫ v in (2 : ℝ)..(s - 1), (2 + riPhi v - riPsi v))
        = ∫ v in (2 : ℝ)..(s - 1), ((2 : ℝ) + (riPhi v - riPsi v)) := by
      refine intervalIntegral.integral_congr fun v _ => by ring
    rw [hcongr, intervalIntegral.integral_add h1 h2, intervalIntegral.integral_const,
      smul_eq_mul]
    have : (s - 1 - 2) * 2 = 2 * (s - 3) := by ring
    linarith
  have hI12 : IntervalIntegrable (fun v : ℝ => buchstabA v / v) volume (1 : ℝ) 2 :=
    intervalIntegrable_buchstabA_div_any 1 2 (by norm_num) (by norm_num)
  have hI2s : IntervalIntegrable (fun v : ℝ => buchstabA v / v) volume (2 : ℝ) (s - 1) :=
    intervalIntegrable_buchstabA_div_any 2 (s - 1) (by norm_num) (by linarith)
  have hadd := intervalIntegral.integral_add_adjacent_intervals hI12 hI2s
  have hsplit : (∫ v in (1 : ℝ)..(s - 1), buchstabA v / v)
      = (∫ v in (1 : ℝ)..(2 : ℝ), buchstabA v / v)
        + (∫ v in (2 : ℝ)..(s - 1), buchstabA v / v) := hadd.symm
  rw [hLHS, hsplit, hI12val, hI2sval, hsplit2]
  have h4 : (∫ v in (2 : ℝ)..(s - 1), (riPhi v - riPsi v))
      = (∫ u in Set.Ici (2 : ℝ), (riPhi u - riPsi u))
        - (∫ u in Set.Ici (s - 1), (riPhi u - riPsi u)) := hsplit3.symm
  rw [h4, integral_Ici_two_sub]
  ring

/-! ### §7  The recurrence, and the mass constant -/

theorem rec_all (s : ℝ) (hs : 2 ≤ s) :
    buchstabA s = (3 + Ctot) + ∫ v in (1 : ℝ)..(s - 1), buchstabA v / v := by
  rcases le_or_gt s 3 with h3 | h3
  · exact rec_of_le_three s hs h3
  · exact rec_of_three_le s h3.le

/-- **The mass constant of the linear sieve**: `Ctot ≤ 2 e^γ - 3`, obtained from the Buchstab
delay-limit theorem applied to `buchstabA`. -/
theorem mass_constant
    (hbuch : ∀ (A : ℝ → ℝ) (c₀ L C : ℝ),
      (∀ a b : ℝ, IntervalIntegrable A volume a b) →
      (∀ s ∈ Set.Icc (1 : ℝ) 2, A s = c₀) →
      (∀ s : ℝ, 2 ≤ s → A s = c₀ + ∫ v in (1 : ℝ)..(s - 1), A v / v) →
      (∀ s : ℝ, 1 ≤ s → |A s| ≤ C * (1 + s)) →
      Filter.Tendsto (fun s : ℝ => A s / s) Filter.atTop (nhds L) →
      L = c₀ * Real.exp (-Real.eulerMascheroniConstant)) :
    Ctot ≤ twoExpGamma - 3 := by
  have hkey := hbuch buchstabA (3 + Ctot) 2 20
    (fun a b => intervalIntegrable_buchstabA_any a b)
    (fun s hs => buchstabA_of_le_two hs.2)
    (fun s hs => rec_all s hs)
    (fun s hs => buchstabA_lin_bound s hs)
    tendsto_buchstabA_div_zero
  have he : Real.exp (-Real.eulerMascheroniConstant)
      * Real.exp Real.eulerMascheroniConstant = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have h3 : 3 + Ctot = 2 * Real.exp Real.eulerMascheroniConstant := by
    have h := congrArg (fun x : ℝ => x * Real.exp Real.eulerMascheroniConstant) hkey
    rw [mul_assoc, he, mul_one] at h
    linarith
  rw [twoExpGamma]
  linarith

end TailOfInputs

/-- `∫_2^x log (t-1)/t` is nonnegative for `x ≥ 2`. -/
theorem integral_log_div_nonneg {x : ℝ} (hx : 2 ≤ x) :
    0 ≤ ∫ t in (2 : ℝ)..x, Real.log (t - 1) / t := by
  rw [intervalIntegral.integral_of_le hx]
  refine integral_nonneg_of_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have ht2 : (2 : ℝ) < t := (Set.mem_Ioc.mp ht).1
  exact div_nonneg (Real.log_nonneg (by linarith)) (by linarith)

theorem intervalIntegrable_log_div (a b : ℝ) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    IntervalIntegrable (fun t : ℝ => Real.log (t - 1) / t) volume a b := by
  rw [intervalIntegrable_iff]
  have hsub : Set.uIoc a b ⊆ Set.Icc (2 : ℝ) (max a b) := by
    intro t ht
    rcases Set.mem_uIoc.mp ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨by linarith, by linarith [h2, le_max_right a b]⟩
    · exact ⟨by linarith, by linarith [h2, le_max_left a b]⟩
  have hcont : ContinuousOn (fun t : ℝ => Real.log (t - 1) / t)
      (Set.Icc (2 : ℝ) (max a b)) := by
    refine ContinuousOn.div ?_ continuousOn_id ?_
    · refine ContinuousOn.log (continuousOn_id.sub continuousOn_const) ?_
      intro t ht
      have : 1 < t := by linarith [ht.1]
      linarith
    · intro t ht
      linarith [ht.1]
  exact (hcont.integrableOn_compact isCompact_Icc).mono_set hsub

/-- The target of this module. -/
theorem riPsi_tail_le_classical_of_inputs
    (hbuch : ∀ (A : ℝ → ℝ) (c₀ L C : ℝ),
      (∀ a b : ℝ, IntervalIntegrable A volume a b) →
      (∀ s ∈ Set.Icc (1 : ℝ) 2, A s = c₀) →
      (∀ s : ℝ, 2 ≤ s → A s = c₀ + ∫ v in (1 : ℝ)..(s - 1), A v / v) →
      (∀ s : ℝ, 1 ≤ s → |A s| ≤ C * (1 + s)) →
      Filter.Tendsto (fun s : ℝ => A s / s) Filter.atTop (nhds L) →
      L = c₀ * Real.exp (-Real.eulerMascheroniConstant))
    (hA : (∫ u in Set.Ici (1 : ℝ), Work.NumberTheory.Chen.APSwitchUpper.riPhi u) = 2) :
    ∀ s : ℝ, 3 ≤ s → s ≤ 4 →
      ∫ u in Set.Ici (s - 1), Work.NumberTheory.Chen.APSwitchUpper.riPsi u
        ≤ Work.NumberTheory.Chen.ApSumTenth.twoExpGamma
            * (1 + ∫ t in (2 : ℝ)..(s - 1), Real.log (t - 1) / t) - s := by
  intro s hs3 hs4
  have hC : Ctot ≤ twoExpGamma - 3 := TailOfInputs.mass_constant hbuch
  have hs2 : (2 : ℝ) ≤ s := by linarith
  have h2s : (2 : ℝ) ≤ s - 1 := by linarith
  -- split the tail integral at 2
  have hIci : IntegrableOn riPsi (Set.Ici (2 : ℝ)) := integrableOn_riPsi_Ici_two
  have hIci' : IntegrableOn riPsi (Set.Ici (s - 1)) :=
    hIci.mono_set (Set.Ici_subset_Ici.mpr h2s)
  have hsplit : (∫ u in Set.Ici (2 : ℝ), riPsi u) - (∫ u in Set.Ici (s - 1), riPsi u)
      = ∫ u in (2 : ℝ)..(s - 1), riPsi u :=
    intervalIntegral.integral_Ici_sub_Ici' hIci hIci'
  have hCtot : (∫ u in Set.Ici (2 : ℝ), riPsi u) = Ctot := riSys_integral_Ici_two_riPsi
  -- the closed form on [2,s-1] ⊂ [2,3]
  have hval : (∫ u in (2 : ℝ)..(s - 1), riPsi u)
      = (s - 3) - (3 + Ctot) * ∫ t in (2 : ℝ)..(s - 1), Real.log (t - 1) / t := by
    have hcongr : (∫ u in (2 : ℝ)..(s - 1), riPsi u)
        = ∫ t in (2 : ℝ)..(s - 1), (1 - (3 + Ctot) * (Real.log (t - 1) / t)) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le h2s] at ht
      rw [riPsi_eq_of_mem_Icc ht.1 (by linarith [ht.2, hs4])]
      ring
    rw [hcongr]
    have h1 : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume (2 : ℝ) (s - 1) :=
      intervalIntegrable_const
    have hcont : ContinuousOn (fun t : ℝ => (3 + Ctot) * (Real.log (t - 1) / t))
        (Set.uIcc (2 : ℝ) (s - 1)) := by
      refine ContinuousOn.mul continuousOn_const ?_
      refine ContinuousOn.div ?_ continuousOn_id ?_
      · refine ContinuousOn.log (continuousOn_id.sub continuousOn_const) ?_
        intro t ht
        rw [Set.uIcc_of_le h2s] at ht
        have : 1 < t := by linarith [ht.1]
        linarith
      · intro t ht
        rw [Set.uIcc_of_le h2s] at ht
        linarith [ht.1]
    have h2 : IntervalIntegrable (fun t : ℝ => (3 + Ctot) * (Real.log (t - 1) / t))
        volume (2 : ℝ) (s - 1) := hcont.intervalIntegrable
    rw [intervalIntegral.integral_sub h1 h2, intervalIntegral.integral_const,
      intervalIntegral.integral_const_mul, smul_eq_mul, mul_one]
    ring
  have hbound : (∫ u in Set.Ici (s - 1), riPsi u)
      = Ctot - (s - 3) + (3 + Ctot) * ∫ t in (2 : ℝ)..(s - 1), Real.log (t - 1) / t := by
    linarith [hsplit, hCtot, hval]
  rw [hbound]
  have hJnn : 0 ≤ ∫ t in (2 : ℝ)..(s - 1), Real.log (t - 1) / t :=
    integral_log_div_nonneg h2s
  have hprod : (Ctot + 3 - twoExpGamma)
      * (1 + ∫ t in (2 : ℝ)..(s - 1), Real.log (t - 1) / t) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  have hdiff : twoExpGamma * (1 + ∫ t in (2 : ℝ)..(s - 1), Real.log (t - 1) / t) - s
        - (Ctot - (s - 3) + (3 + Ctot) * ∫ t in (2 : ℝ)..(s - 1), Real.log (t - 1) / t)
      = -((Ctot + 3 - twoExpGamma)
          * (1 + ∫ t in (2 : ℝ)..(s - 1), Real.log (t - 1) / t)) := by
    ring
  linarith [hprod, hdiff]

end

end Work.NumberTheory.Chen.ApSumTenth
