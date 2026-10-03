import Mathlib
import Submission.Work.FIChain.s3RemPlus_maj
import Submission.Work.FIChain.s3Rem_fibre_pt_le
import Submission.Work.FIChain.scale_factsC
import Submission.Work.FIChain.zc_sharp_bounds
import Submission.Work.FIChain.Yc_lower_sharp
import Submission.Work.FIChain.measurable_s3halves
import Submission.Work.FIChain.s3RemPlus_maj_le

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIChain

open Finset MeasureTheory
open scoped BigOperators Interval

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## The `z`-averaged remainder half of the `λ⁺` sum (companion's (8.4))

See `Submission/Work/FIChain/NOTES_S3plusC_session12.md` for the full account.

* `s3RemPlus_maj` (PROVED) contains the §8.4 substitutions, the per-`ℓ` majorant `remMaj1`, the
  per-`ℓ` substitution inequality `remTerm_zavg_le_sub`, the restriction of the `ℓ`-sum to
  `Icc 1 ⌊x/Cm⌋₊` (`remMajU_eq_sum_remTerm'`), the joint integrand `Ksub` and its pointwise `(R′)`
  bound `Ksub_le`.
* What remains for the target is the summation/interchange/measure step, i.e. exactly
  `Work.FIChain.s3RemPlus_maj_le` (delegated; see the NOTES).  The reduction from the target to
  that statement is `s3RemPlus_zavg_le_of_maj` below (PROVED). -/

/-- **The target follows from the `remMajU`-statement** (the analytic core): the `y`-dependence of
`s3RemPlus` is only the divisor cut `sy = sc·y`, so `∫_{Yc}^{e·Yc} dy/y = 1` is free and the
`y`-average is dominated pointwise in `z` by `remMajU` (`rem_yavg_le`). -/
theorem s3RemPlus_zavg_le_of_maj
    (hmaj : ∃ C : ℝ, 0 < C ∧ ∀ B : ℝ, 0 < B → ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
      (x : ℝ) ^ ((1 : ℝ) / 4 + 1 / 64) + 2 < Yc x B / (Deltac x : ℝ) →
      2 ≤ sc x B →
      (∫ z in zc x B..(Real.exp 1 * zc x B),
          remMajU x ⌊(zc x B) ^ (1 - etac)⌋₊ (sc x B) z / z)
        ≤ C * AcountAtilC x * (Real.log (x : ℝ)) ^ (-(1 : ℤ))) :
    ∃ C : ℝ, 0 < C ∧ ∀ B : ℝ, 0 < B → ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
      (x : ℝ) ^ ((1 : ℝ) / 4 + 1 / 64) + 2 < Yc x B / (Deltac x : ℝ) →
      2 ≤ sc x B →
      ∀ lam : ℕ → ℝ, ∀ C_sieve : ℝ,
        SieveInput Submission.ASP.FIgtil (Deltac x) lam C_sieve →
      (∫ z in zc x B..(Real.exp 1 * zc x B),
          (∫ y in Yc x B..(Real.exp 1 * Yc x B),
            |s3RemPlus lam x z (sc x B * y) (sc x B * z)
              ⌊(zc x B) ^ (1 - etac)⌋₊| / y) / z)
        ≤ C * AcountAtilC x * (Real.log (x : ℝ)) ^ (-(1 : ℤ)) := by
  obtain ⟨C, hCpos, hmaj⟩ := hmaj
  refine ⟨C, hCpos, fun B hB => ?_⟩
  obtain ⟨xm, hm⟩ := hmaj B hB
  obtain ⟨xs, hs⟩ := Filter.eventually_atTop.mp (scale_factsC B hB)
  obtain ⟨xg, hg⟩ := Filter.eventually_atTop.mp (Cm_ge_rpow B hB)
  obtain ⟨x2, hx2⟩ := Filter.eventually_atTop.mp (Filter.eventually_ge_atTop 2)
  refine ⟨max (max xm xs) (max xg x2) + 3, fun x hx hYc hsc2 lam Cs hSie => ?_⟩
  have hxmx : xm ≤ x := by omega
  have hxsx : xs ≤ x := by omega
  have hxgx : xg ≤ x := by omega
  have hx2x : x2 ≤ x := by omega
  set Cm : ℕ := ⌊(zc x B) ^ (1 - etac)⌋₊ with hCmdef
  obtain ⟨hY256, -, -, -, -, -, -, -, -, hZc1, -⟩ := hs x hxsx
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
  have hxc_pos : (0 : ℝ) < (x : ℝ) := by linarith
  have hCm_le : (x : ℝ) ^ ((3 : ℝ) / 10) ≤ (Cm : ℝ) := by
    have := hg x hxgx
    rwa [hCmdef]
  have hCm1 : 1 ≤ Cm := by
    have h1 : (1 : ℝ) ≤ (x : ℝ) ^ ((3 : ℝ) / 10) := Real.one_le_rpow hx1 (by norm_num)
    have h2 : (1 : ℝ) ≤ (Cm : ℝ) := le_trans h1 hCm_le
    exact_mod_cast h2
  have hCmpos : (0 : ℝ) < (Cm : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hCm1)
  have hzc1 : (1 : ℝ) ≤ zc x B := by
    have h1 : (1 : ℝ) ≤ (Zc x B : ℕ) := by exact_mod_cast hZc1
    simpa [zc] using h1
  have hzcpos : 0 < zc x B := lt_of_lt_of_le zero_lt_one hzc1
  have hzle : zc x B ≤ Real.exp 1 * zc x B :=
    le_mul_of_one_le_left hzcpos.le (Real.one_le_exp (by norm_num))
  have hCm_lt : (Cm : ℝ) < zc x B := by
    have h1 : (Cm : ℝ) ≤ (zc x B) ^ (1 - etac) := by
      rw [hCmdef]
      exact Nat.floor_le (Real.rpow_nonneg hzcpos.le _)
    have hzc_gt1 : (1 : ℝ) < zc x B := by
      have h : (256 : ℝ) ≤ (Zc x B : ℕ) := by exact_mod_cast hY256
      simp only [zc]
      linarith
    have h2 : (zc x B) ^ (1 - etac) < zc x B :=
      Real.rpow_lt_self_of_one_lt hzc_gt1 (by norm_num [etac])
    linarith
  have hsc1 : (1 : ℝ) ≤ sc x B := by
    rw [sc]
    exact one_le_pow₀ (by norm_num)
  have hCmzc : (Cm : ℝ) ≤ sc x B * zc x B := by
    calc (Cm : ℝ) ≤ zc x B := le_of_lt hCm_lt
      _ = 1 * zc x B := (one_mul _).symm
      _ ≤ sc x B * zc x B := mul_le_mul_of_nonneg_right hsc1 hzcpos.le
  have hYcpos : 0 < Yc x B := by
    rw [Yc]
    have hLpos : 0 < Real.log (x : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < x))
    exact div_pos (Real.sqrt_pos.mpr hxc_pos)
      (mul_pos (pow_pos (by norm_num) _) (Real.rpow_pos_of_pos hLpos _))
  have hlam : ∀ ν : ℕ, |lam ν| ≤ 1 := hSie.2.2.2.1
  have hYc_le : Yc x B ≤ Real.exp 1 * Yc x B :=
    le_mul_of_one_le_left hYcpos.le (Real.one_le_exp (by norm_num))
  -- the `y`-integral
  have hya : ∀ z ∈ Set.Icc (zc x B) (Real.exp 1 * zc x B),
      (∫ y in Yc x B..(Real.exp 1 * Yc x B),
        |s3RemPlus lam x z (sc x B * y) (sc x B * z) Cm| / y) ≤ remMajU x Cm (sc x B) z := by
    intro z hz
    refine rem_yavg_le lam B x Cm z hlam hCm1 ?_ hYcpos
    calc (Cm : ℝ) ≤ sc x B * zc x B := hCmzc
      _ ≤ sc x B * z := mul_le_mul_of_nonneg_left hz.1 (le_trans zero_le_one hsc1)
  -- integrability of `remMajU / z`
  have hCstnn : (0 : ℝ) ≤ 4 * AcountAtilC x * ((x : ℝ) + 1) * ((x : ℝ) ^ 3 + 1) := by
    have hAnn : 0 ≤ AcountAtilC x := AcountAtilC_nonneg x
    have := Nat.cast_nonneg (α := ℝ) x
    positivity
  have hMajI : IntervalIntegrable (fun z : ℝ => remMajU x Cm (sc x B) z / z) volume
      (zc x B) (Real.exp 1 * zc x B) := by
    refine IntervalIntegrable.mono_fun'
      (intervalIntegrable_const_div
        ((4 * AcountAtilC x * ((x : ℝ) + 1) * ((x : ℝ) ^ 3 + 1)) * Real.exp 1 * zc x B)
        (zc x B) (Real.exp 1 * zc x B) hzcpos hzle) ?_ ?_
    · exact ((measurable_remMajU x Cm (sc x B)).aestronglyMeasurable).mono_measure
        Measure.restrict_le_self
    · rw [Set.uIoc_of_le hzle]
      refine eventually_restrict_Ioc (fun z hz => ?_)
      have hz0 : 0 < z := lt_of_lt_of_le hzcpos hz.1.le
      change ‖remMajU x Cm (sc x B) z / z‖
        ≤ (4 * AcountAtilC x * ((x : ℝ) + 1) * ((x : ℝ) ^ 3 + 1)) * Real.exp 1 * zc x B / z
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hz0]
      rw [div_le_div_iff_of_pos_right hz0,
        abs_of_nonneg (remMajU_nonneg x Cm (sc x B) z)]
      refine le_trans (remMajU_le_crude x Cm (sc x B) z hCm1 hz0.le (le_trans zero_le_one hsc1)) ?_
      have hexp1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
      have h1 : (1 : ℝ) ≤ Real.exp 1 * zc x B := by
        calc (1 : ℝ) = 1 * 1 := by ring
          _ ≤ Real.exp 1 * zc x B := mul_le_mul hexp1 hzc1 zero_le_one (by linarith)
      nlinarith [hCstnn, h1]
  -- the outer monotonicity
  have hstep : (∫ z in zc x B..(Real.exp 1 * zc x B),
        (∫ y in Yc x B..(Real.exp 1 * Yc x B),
          |s3RemPlus lam x z (sc x B * y) (sc x B * z) Cm| / y) / z)
      ≤ ∫ z in zc x B..(Real.exp 1 * zc x B), remMajU x Cm (sc x B) z / z := by
    refine intervalIntegral.integral_mono_ae_restrict hzle ?_ hMajI ?_
    · refine hMajI.mono_fun' ?_ ?_
      · refine ((measurable_intervalIntegral_param (α := ℝ) (a := Yc x B)
          (G := fun q : ℝ × ℝ => |s3RemPlus lam x q.1 (sc x B * q.2) (sc x B * q.1) Cm| / q.2)
          ((measurable_s3halves_joint x B lam Cm).2.div measurable_snd) measurable_const).div
            measurable_id).aestronglyMeasurable.mono_measure Measure.restrict_le_self
      · rw [Set.uIoc_of_le hzle]
        refine eventually_restrict_Ioc (fun z hz => ?_)
        have hz0 : 0 < z := lt_of_lt_of_le hzcpos hz.1.le
        change ‖(∫ y in Yc x B..(Real.exp 1 * Yc x B),
            |s3RemPlus lam x z (sc x B * y) (sc x B * z) Cm| / y) / z‖
          ≤ remMajU x Cm (sc x B) z / z
        rw [Real.norm_eq_abs, abs_div, abs_of_pos hz0]
        rw [div_le_div_iff_of_pos_right hz0]
        rw [abs_of_nonneg (intervalIntegral.integral_nonneg hYc_le
          (fun y hy => div_nonneg (abs_nonneg _) (le_of_lt (lt_of_lt_of_le hYcpos hy.1))))]
        exact hya z (Set.Ioc_subset_Icc_self hz)
    · exact eventually_restrict_Icc (fun z hz => by
        have hz0 : 0 < z := lt_of_lt_of_le hzcpos hz.1
        exact div_le_div_of_nonneg_right (hya z hz) hz0.le)
  exact le_trans hstep (hm x hxmx hYc hsc2)

/-! ## The target (companion's (8.4))

It remains to supply `Work.FIChain.s3RemPlus_maj_le` (the summation / interchange / measure step
over the region `[zc, V] × [1, x/Cm]`, with the joint integrand `Ksub` bounded pointwise by
`Ksub_le`).  Then

    theorem s3RemPlus_zavg_le : <statement> :=
      s3RemPlus_zavg_le_of_maj s3RemPlus_maj_le -/
theorem s3RemPlus_zavg_le :
    ∃ C : ℝ, 0 < C ∧ ∀ B : ℝ, 0 < B → ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
      (x : ℝ) ^ ((1 : ℝ) / 4 + 1 / 64) + 2 < Work.FIChain.Yc x B / (Work.FIChain.Deltac x : ℝ) →
      2 ≤ Work.FIChain.sc x B →
      ∀ lam : ℕ → ℝ, ∀ C_sieve : ℝ,
        Work.FIChain.SieveInput Submission.ASP.FIgtil (Work.FIChain.Deltac x) lam C_sieve →
      (∫ z in Work.FIChain.zc x B..(Real.exp 1 * Work.FIChain.zc x B),
          (∫ y in Work.FIChain.Yc x B..(Real.exp 1 * Work.FIChain.Yc x B),
            |Work.FIChain.s3RemPlus lam x z (Work.FIChain.sc x B * y) (Work.FIChain.sc x B * z)
              (⌊(Work.FIChain.zc x B) ^ (1 - Work.FIChain.etac)⌋₊)| / y) / z)
        ≤ C * Work.FIChain.AcountAtilC x * (Real.log (x : ℝ)) ^ (-(1 : ℤ)) :=
  s3RemPlus_zavg_le_of_maj s3RemPlus_maj_le

end

end Work.FIChain
