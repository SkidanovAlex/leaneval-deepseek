/-
# `Submission.Work.FIChain.S3fixed_signed_K` — the fixed-`z` signed `S₃` bound, for the
sieve-gap weights `(λ, C_sieve)` with `C_sieve ≤ Ksie`

This module is the argument of the on-disk `Submission/Work/FIChain/S3fixed_signed_le.lean`
(whose only gap is its `s3f_phi_Bstar` step), with that step replaced by the **proved**
`Work.FIChain.S3phi_Bstar_v2_sieveBound` (`Submission/Work/FIChain/S3phi_Bstar_v2.lean`), whose
`§6`/`S₁` summand needs the uniform sieve-constant hypothesis `C_sieve ≤ K₀`; correspondingly the
statement carries the binder `Cs ≤ Ksie`, exactly the weights the chain supplies through the proved
sieve gap (`Work.FIChain.FIChainSieveGap_proved = rosserLambda_FIgtil_r2`).

The FI endgame consumes `S₃` only through `|∫_Y S₃/y|` at the chain's fixed inner scale
`z = zc x B`.  The companion's §8 proves `S₃ ≪ A(x)(log x)^{-1}` only for the **`z`-averaged**
quantity (`Work.FIChain.S3plusC_zavg_le`, `S3minusC_zavg_le`; `NOTES.md` §46–§49), and the passage
to the fixed `z` goes through the deviation statement `Work.FIChain.S3avgFix_le_of_zavg`
(`S3zdev.lean`), whose inputs are

* the `z`-average of `|∫_Y S₃(z)/y|`, bounded by `(K₊+K₋)·Ã(x)/log x` through the two halves at the
  common level `⌊(zc)^{1-η}⌋` (`S3_eq_S3plusC_sub_S3minusC` + triangle inequality);
* the mean-value extraction of one `z₁ ∈ [zc, e·zc]` attaining that average;
* the `z`-uniform §4–§7 bounds (`hPhi`), i.e. `|Φ(z) − H·Ã(x)| ≪ Ã(x)/log x` for all `z ∈ [zc,e·zc]`;
* the completion deviation `Σ_{zc<n≤e·zc}|ã_n ρ_n Λ n| ≪ Ã(x)/log x`.

Everything is run at the **pinned** scale `HasBc.val = 2^31 + 2`, at which
`Submission.Work.FIChain.windows_at_Bstar` supplies both chain windows (the `b̃`-window for the
`S₂`-term and the `ρ`-window for the `λ⁻`-half) with a common constant and threshold.
-/
import Mathlib
import Submission.Work.FIPiChain.HasB
import Submission.Work.FIPiChain.Defs
import Submission.Work.FIChain.Defs
import Submission.Work.FIChain.S3zdev
import Submission.Work.FIChain.S3splitBstar
import Submission.Work.FIChain.S3plusC_machinery
import Submission.Work.FIPiChain.Chain.s3MainPlus_pt_le_B
import Submission.Work.FIChain.s3RemPlus_zavg_le
import Submission.Work.FIChain.abs_S3minusC_le
import Submission.Work.FIChain.measurable_s3halves
import Submission.Work.FIChain.S3xC_intervalIntegrable
import Submission.Work.FIChain.window_marginsC
import Submission.Work.FITop.BformAtilEqXsum
import Submission.Work.FITop.AtilTauPowFourLe
import Submission.Work.FITop.Defs
import Submission.ASP.S7c
import Submission.ASP.S8b
import Submission.ASP.S20
import Submission.ASP.S21
import Submission.ASP.S22
import Submission.ASP.S23
import Submission.ASP.S24
import Submission.ASP.S25
import Submission.Work.FITop.SingleDvdTauSqLe
import Submission.Work.FITop.WindowRangeMarginsChain
import Submission.Work.FITop.BprimeWindowDelta1
import Submission.Work.FITop.RangeCheckChain
import Submission.ASP.S30
import Submission.Work.FITop.WolkeSquarefreeTau
import Submission.Work.FITop.AdTauAggregate
import Submission.Work.FITop.SumIteDivDvd
import Submission.Work.FIChain.scale_factsC
import Submission.Work.FIChain.rhoWindowC_param
import Submission.Work.FITop.RhoWindowCProp41
import Submission.Work.FIChain.chainRangeFactsC
import Submission.Work.FIChain.Yc_lower_sharp
import Submission.Work.FIChain.assemblyC
import Submission.Work.FIChain.remainder_all
import Submission.Work.FIChain.Tsum_uniformAll
import Submission.Work.FIChain.Tsum2_uniformAll
import Submission.Work.FIChain.LocalS5c
import Submission.Work.FIChain.LocalS6c
import Submission.Work.FIChain.AcountAtilC_ge_const_mul_rpow
import Submission.Work.FIChain.AcountAtilC_le_const_mul_rpow
import Submission.Work.FIPiChain.Chain.S3delSum_B
import Submission.Work.FIPiChain.Chain.chainRangeWideB
import Submission.Work.FIChain.exists_z1_le_of_measurable_zavg
import Submission.Work.FIPiChain.Chain.S3phi_B_v2

set_option autoImplicit false
set_option maxHeartbeats 3200000

open Work.FIChain

namespace Work.FIPiChain

variable [HasBc]

open Finset Filter MeasureTheory
open Submission.ASP
open scoped BigOperators Interval

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 0. Elementary facts about the pinned scale `HasBc.val = 2^31 + 2` -/

lemma s3fB_Bstar_pos : (0 : ℝ) < HasBc.val := by have := HasBc.ge_two; linarith

lemma s3fB_Bstar_ge_two : (2 : ℝ) ≤ HasBc.val := by have := HasBc.ge_two; linarith

/-- `sc x HasBc.val · (e·Yc x HasBc.val) = e√x/(log x)^{HasBc.val+2}`. -/
private lemma s3f_sc_mul_exp_Yc (x : ℕ) (hL : 0 < Real.log (x : ℝ)) :
    sc x HasBc.val * (Real.exp 1 * Yc x HasBc.val)
      = Real.exp 1 * Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ (HasBc.val + 2) := by
  rw [Yc]
  have hsc : sc x HasBc.val ≠ 0 := by rw [sc]; positivity
  have hLp : (Real.log (x : ℝ)) ^ (HasBc.val + 2) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hL _)
  field_simp

/-- **The top margin at `HasBc.val`**: `2·(sc·(e·Yc)) + 1 ≤ √x` eventually. -/
private lemma s3f_top_margin :
    ∀ᶠ x : ℕ in Filter.atTop,
      2 * (sc x HasBc.val * (Real.exp 1 * Yc x HasBc.val)) + 1 ≤ (x : ℝ) ^ ((1 : ℝ) / 2) := by
  have hB : (0 : ℝ) < HasBc.val := s3fB_Bstar_pos
  filter_upwards [Work.FITop.FI_ev_log_ge_nat (4 * Real.exp 1),
      Work.FITop.FI_ev_rpow_ge_nat ((1 : ℝ) / 2) (by norm_num) 4,
      eventually_ge_atTop 2] with x hlog hx4 hx2
  have _ : (0 : ℝ) < HasBc.val := hB
  have hx1 : (1 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 1 < x)
  have hLpos : 0 < Real.log (x : ℝ) := by linarith [Real.exp_pos 1]
  have hLp_pos : 0 < (Real.log (x : ℝ)) ^ (HasBc.val + 2) := Real.rpow_pos_of_pos hLpos _
  have hL1 : (1 : ℝ) ≤ Real.log (x : ℝ) := by
    linarith [Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1), Real.exp_pos 1]
  have hLp_ge : 4 * Real.exp 1 ≤ (Real.log (x : ℝ)) ^ (HasBc.val + 2) := by
    have h2 : Real.log (x : ℝ) ≤ (Real.log (x : ℝ)) ^ (HasBc.val + 2) := by
      have h := Real.rpow_le_rpow_of_exponent_le hL1
        (by linarith [s3fB_Bstar_ge_two] : (1 : ℝ) ≤ HasBc.val + 2)
      rwa [Real.rpow_one] at h
    linarith
  rw [s3f_sc_mul_exp_Yc x hLpos]
  have key : 2 * (Real.exp 1 * Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ (HasBc.val + 2))
      ≤ Real.sqrt (x : ℝ) / 2 := by
    have hdiv : (2 * Real.exp 1) / (Real.log (x : ℝ)) ^ (HasBc.val + 2) ≤ 1 / 2 := by
      rw [div_le_iff₀ hLp_pos]; linarith
    calc 2 * (Real.exp 1 * Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ (HasBc.val + 2))
        = ((2 * Real.exp 1) / (Real.log (x : ℝ)) ^ (HasBc.val + 2)) * Real.sqrt (x : ℝ) := by
          field_simp
      _ ≤ (1 / 2) * Real.sqrt (x : ℝ) := mul_le_mul_of_nonneg_right hdiv (Real.sqrt_nonneg _)
      _ = Real.sqrt (x : ℝ) / 2 := by ring
  have hsqrt : 2 ≤ Real.sqrt (x : ℝ) := by rw [Real.sqrt_eq_rpow]; linarith
  rw [← Real.sqrt_eq_rpow]
  linarith

/-- **The bottom margin at `η_c = 1/32`**: `x^{1/4+η_c} + 2 < Yc/Δ` eventually. -/
private lemma s3f_bottom_margin :
    ∀ᶠ x : ℕ in Filter.atTop,
      (x : ℝ) ^ ((1 : ℝ) / 4 + etac) + 2 < Yc x HasBc.val / (Deltac x : ℝ) := by
  filter_upwards [Work.FITop.FI_ev_Delta1_le_two_Lam1, Work.FITop.FI_ev_Lam1_ge_one,
      Work.FITop.FI_ev_rpow_ge_nat ((17 : ℝ) / 800) (by norm_num) 8,
      Work.FITop.FI_ev_rpow_ge_nat ((9 : ℝ) / 32) (by norm_num) 4,
      Yc_lower_sharp HasBc.val s3fB_Bstar_pos, eventually_ge_atTop 2]
    with x hΔ2 hLam1 hx17 hx9 hYlow hx2
  have hx1 : (1 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 1 < x)
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  have hΔge : (1 : ℝ) ≤ (Deltac x : ℝ) := le_trans hLam1 (Work.FITop.FI_Lam1_le_Delta1 x)
  have hΔpos : 0 < (Deltac x : ℝ) := lt_of_lt_of_le zero_lt_one hΔge
  have hA1 : (x : ℝ) ^ ((5 : ℝ) / 16) / (2 * Work.FITop.Lam1 x)
      ≤ (x : ℝ) ^ ((5 : ℝ) / 16) / (Deltac x : ℝ) :=
    div_le_div_of_nonneg_left (Real.rpow_nonneg hxpos.le _) hΔpos hΔ2
  have hYdiv : (x : ℝ) ^ ((5 : ℝ) / 16) / (Deltac x : ℝ) ≤ Yc x HasBc.val / (Deltac x : ℝ) :=
    div_le_div_of_nonneg_right hYlow hΔpos.le
  refine lt_of_lt_of_le ?_ (le_trans hA1 hYdiv)
  have heq : (x : ℝ) ^ ((5 : ℝ) / 16) / (2 * Work.FITop.Lam1 x)
      = (1 / 2) * ((x : ℝ) ^ ((9 : ℝ) / 32) * (x : ℝ) ^ ((17 : ℝ) / 800)) := by
    rw [Work.FITop.Lam1]
    have hxA : 0 < (x : ℝ) ^ ((1 : ℝ) / 100) := Real.rpow_pos_of_pos hxpos _
    have h1 : (x : ℝ) ^ ((5 : ℝ) / 16) / (x : ℝ) ^ ((1 : ℝ) / 100)
        = (x : ℝ) ^ ((9 : ℝ) / 32) * (x : ℝ) ^ ((17 : ℝ) / 800) := by
      rw [← Real.rpow_sub hxpos, ← Real.rpow_add hxpos]
      congr 1; norm_num
    rw [← h1]
    field_simp
  have hprod : 8 * (x : ℝ) ^ ((9 : ℝ) / 32)
      ≤ (x : ℝ) ^ ((9 : ℝ) / 32) * (x : ℝ) ^ ((17 : ℝ) / 800) := by
    calc 8 * (x : ℝ) ^ ((9 : ℝ) / 32) = (x : ℝ) ^ ((9 : ℝ) / 32) * 8 := by ring
      _ ≤ (x : ℝ) ^ ((9 : ℝ) / 32) * (x : ℝ) ^ ((17 : ℝ) / 800) :=
          mul_le_mul_of_nonneg_left hx17 (Real.rpow_nonneg hxpos.le _)
  have hxeta : (x : ℝ) ^ ((1 : ℝ) / 4 + etac) = (x : ℝ) ^ ((9 : ℝ) / 32) := by
    congr 1; norm_num [etac]
  rw [hxeta, heq]
  have h1 : 4 * (x : ℝ) ^ ((9 : ℝ) / 32)
      ≤ (1 / 2) * ((x : ℝ) ^ ((9 : ℝ) / 32) * (x : ℝ) ^ ((17 : ℝ) / 800)) := by
    nlinarith [hprod]
  have h2 : (x : ℝ) ^ ((9 : ℝ) / 32) + 2 < 4 * (x : ℝ) ^ ((9 : ℝ) / 32) := by
    have hpos : 0 < (x : ℝ) ^ ((9 : ℝ) / 32) := Real.rpow_pos_of_pos hxpos _
    linarith
  linarith

/-- `x^{3/16}/(2(log x)^{HasBc.val+2}) ≥ 1` eventually. -/
private lemma s3f_u_ge_one :
    ∀ᶠ x : ℕ in Filter.atTop,
      1 ≤ (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / (2 * (Real.log (x : ℝ)) ^ (HasBc.val + 2)) := by
  filter_upwards [Work.FITop.FI_ev_log_rpow_le_nat (b := HasBc.val + 2) (ε := (3 : ℝ) / 16)
      (C := 1 / 2) (by norm_num) (by norm_num), eventually_ge_atTop 2] with x hle hx2
  have hx1 : (1 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 1 < x)
  have hLpos : 0 < Real.log (x : ℝ) := Real.log_pos hx1
  have he : (1 : ℝ) / 4 - 2 * etac = 3 / 16 := by norm_num [etac]
  rw [he, le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (Real.log (x : ℝ)) ^ (HasBc.val + 2))]
  linarith

/-- `sc x HasBc.val < x^{3/16}`. -/
private lemma s3f_sc_lt (x : ℕ) (hxpos : 0 < (x : ℝ)) (hL1 : 1 ≤ Real.log (x : ℝ))
    (hu : 1 ≤ (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / (2 * (Real.log (x : ℝ)) ^ (HasBc.val + 2))) :
    sc x HasBc.val < (x : ℝ) ^ ((3 : ℝ) / 16) := by
  have hupos : 0 < (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / (2 * (Real.log (x : ℝ)) ^ (HasBc.val + 2)) :=
    lt_of_lt_of_le zero_lt_one hu
  have ht0 : 0 ≤ Real.log ((x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac)
      / (2 * (Real.log (x : ℝ)) ^ (HasBc.val + 2))) / Real.log 2 :=
    div_nonneg (Real.log_nonneg hu) (Real.log_pos (by norm_num)).le
  have hJlt : (Jc x HasBc.val : ℝ) < Real.log ((x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac)
      / (2 * (Real.log (x : ℝ)) ^ (HasBc.val + 2))) / Real.log 2 + 1 := by
    rw [Jc]; exact Nat.ceil_lt_add_one ht0
  have hpow : (2 : ℝ) ^ (Real.log ((x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac)
      / (2 * (Real.log (x : ℝ)) ^ (HasBc.val + 2))) / Real.log 2)
      = (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / (2 * (Real.log (x : ℝ)) ^ (HasBc.val + 2)) :=
    Work.FITop.FI_two_rpow_log_div_log _ hupos
  have h2lt : (2 : ℝ) ^ (Jc x HasBc.val) < 2 * ((x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac)
      / (2 * (Real.log (x : ℝ)) ^ (HasBc.val + 2))) := by
    calc (2 : ℝ) ^ (Jc x HasBc.val) = (2 : ℝ) ^ ((Jc x HasBc.val : ℕ) : ℝ) :=
          (Real.rpow_natCast 2 (Jc x HasBc.val)).symm
      _ < (2 : ℝ) ^ (Real.log ((x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac)
            / (2 * (Real.log (x : ℝ)) ^ (HasBc.val + 2))) / Real.log 2 + 1) :=
          Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hJlt
      _ = 2 * ((x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac)
            / (2 * (Real.log (x : ℝ)) ^ (HasBc.val + 2))) := by
          rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one, hpow]; ring
  have he : (1 : ℝ) / 4 - 2 * etac = 3 / 16 := by norm_num [etac]
  have hLpos : 0 < Real.log (x : ℝ) := by linarith
  have hden : 0 < (Real.log (x : ℝ)) ^ (HasBc.val + 2) := Real.rpow_pos_of_pos hLpos _
  have hLp1 : (1 : ℝ) ≤ (Real.log (x : ℝ)) ^ (HasBc.val + 2) :=
    Real.one_le_rpow hL1 (by linarith [s3fB_Bstar_ge_two])
  have hxnn : (0 : ℝ) ≤ (x : ℝ) := le_of_lt hxpos
  calc sc x HasBc.val = (2 : ℝ) ^ (Jc x HasBc.val) := rfl
    _ < (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / (Real.log (x : ℝ)) ^ (HasBc.val + 2) := by
        refine lt_of_lt_of_le h2lt (le_of_eq ?_)
        field_simp
    _ ≤ (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / 1 :=
        div_le_div_of_nonneg_left (Real.rpow_nonneg hxnn _) one_pos hLp1
    _ = (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) := div_one _
    _ = (x : ℝ) ^ ((3 : ℝ) / 16) := by rw [he]

/-- At the pinned scale, `Jc x HasBc.val · log ⌊(zc x HasBc.val)^{1-η}⌋ ≤ (log x)²`, and the truncation
level is at least `1`. -/
private lemma s3f_Jc_logC_bound :
    ∀ᶠ x : ℕ in Filter.atTop,
      (Jc x HasBc.val : ℝ) * Real.log (((⌊(zc x HasBc.val) ^ (1 - etac)⌋₊ : ℕ) : ℝ))
        ≤ Real.log (x : ℝ) * Real.log (x : ℝ) ∧
      (1 : ℝ) ≤ (((⌊(zc x HasBc.val) ^ (1 - etac)⌋₊ : ℕ) : ℝ)) := by
  filter_upwards [scale_factsC HasBc.val s3fB_Bstar_pos, s3f_u_ge_one, Work.FITop.FI_ev_log_ge_nat 8,
      Work.FITop.FI_ev_log_ge_nat 2, eventually_ge_atTop 2] with x hsf hu hL8 hL2 hx2
  obtain ⟨hY256, -, -, -, -, -, -, hDz, hzx, hZ1, -, -, -, -, -, -⟩ := hsf
  have hx1 : (1 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 1 < x)
  have hLpos : 0 < Real.log (x : ℝ) := by linarith
  have hzc1 : (1 : ℝ) ≤ zc x HasBc.val := by
    have h : (1 : ℝ) ≤ (⌊Yc x HasBc.val⌋₊ : ℝ) := by
      exact_mod_cast (le_trans (by norm_num : 1 ≤ 256) hY256)
    simpa [zc, Zc] using h
  have hη : (0 : ℝ) < 1 - etac := by norm_num [etac]
  have hzcrp1 : (1 : ℝ) ≤ (zc x HasBc.val) ^ (1 - etac) := by
    calc (1 : ℝ) = (1 : ℝ) ^ (1 - etac) := (Real.one_rpow _).symm
      _ ≤ (zc x HasBc.val) ^ (1 - etac) := Real.rpow_le_rpow zero_le_one hzc1 hη.le
  have hC1 : (1 : ℝ) ≤ (((⌊(zc x HasBc.val) ^ (1 - etac)⌋₊ : ℕ) : ℝ)) := by
    exact_mod_cast (Nat.one_le_floor_iff _).mpr hzcrp1
  have hsc_lt := s3f_sc_lt x (by linarith) (by linarith) hu
  have hlog2 : (9 : ℝ) / 16 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hJ2 : (Jc x HasBc.val : ℝ) * Real.log 2 < (3 : ℝ) / 16 * Real.log (x : ℝ) := by
    have hpos2 : 0 < (2 : ℝ) ^ (Jc x HasBc.val) := by positivity
    have hlt := Real.log_lt_log hpos2 hsc_lt
    rw [Real.log_pow, Real.log_rpow (by linarith : (0 : ℝ) < (x : ℝ))] at hlt
    linarith
  have hJc_le : (Jc x HasBc.val : ℝ) ≤ Real.log (x : ℝ) / 3 := by
    have hlog2pos : (0 : ℝ) < Real.log 2 := by linarith
    have h1 : (Jc x HasBc.val : ℝ) < ((3 : ℝ) / 16 * Real.log (x : ℝ)) / Real.log 2 :=
      (lt_div_iff₀ hlog2pos).mpr hJ2
    have h2 : ((3 : ℝ) / 16 * Real.log (x : ℝ)) / Real.log 2 ≤ Real.log (x : ℝ) / 3 := by
      rw [div_le_iff₀ hlog2pos]
      nlinarith [hlog2, hLpos]
    linarith [h1, h2]
  have hCle : (((⌊(zc x HasBc.val) ^ (1 - etac)⌋₊ : ℕ) : ℝ)) ≤ zc x HasBc.val := by
    calc (((⌊(zc x HasBc.val) ^ (1 - etac)⌋₊ : ℕ) : ℝ)) ≤ (zc x HasBc.val) ^ (1 - etac) :=
          Nat.floor_le (Real.rpow_nonneg (le_trans zero_le_one hzc1) _)
      _ ≤ (zc x HasBc.val) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hzc1 (by norm_num [etac])
      _ = zc x HasBc.val := Real.rpow_one _
  have hlogCle : Real.log (((⌊(zc x HasBc.val) ^ (1 - etac)⌋₊ : ℕ) : ℝ)) ≤ Real.log (x : ℝ) :=
    Real.log_le_log (by linarith) (le_trans hCle hzx)
  refine ⟨?_, hC1⟩
  calc (Jc x HasBc.val : ℝ) * Real.log (((⌊(zc x HasBc.val) ^ (1 - etac)⌋₊ : ℕ) : ℝ))
      ≤ (Real.log (x : ℝ) / 3) * Real.log (((⌊(zc x HasBc.val) ^ (1 - etac)⌋₊ : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_right hJc_le (Real.log_nonneg hC1)
    _ ≤ (Real.log (x : ℝ) / 3) * Real.log (x : ℝ) :=
        mul_le_mul_of_nonneg_left hlogCle (by linarith)
    _ ≤ Real.log (x : ℝ) * Real.log (x : ℝ) := by
        have h3 : (0 : ℝ) < Real.log (x : ℝ) := lt_of_lt_of_le (by norm_num) hL8
        nlinarith

/-! ## 1. The `ρ`-window at `HasBc.val` on the enlarged position range -/

/-- If `f ≤ Cst/y` on `(a, e·a]` and `f` is interval integrable there, then
`∫_a^{e·a} f ≤ Cst`. -/
private lemma s3f_integral_le_const_div (a Cst : ℝ) (ha : 0 < a) {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume a (Real.exp 1 * a)) (hCst : 0 ≤ Cst)
    (hpt : ∀ y ∈ Set.Icc a (Real.exp 1 * a), f y ≤ Cst / y) :
    ∫ y in a..(Real.exp 1 * a), f y ≤ Cst := by
  have hab : a ≤ Real.exp 1 * a := by
    nlinarith [Real.one_le_exp (show (0 : ℝ) ≤ 1 by norm_num), ha]
  have hIntG : IntervalIntegrable (fun y : ℝ => Cst / y) volume a (Real.exp 1 * a) :=
    intervalIntegrable_div_Ioc (G := fun _ : ℝ => Cst) measurable_const ha hab Cst
      (fun _ _ => by simp [abs_of_nonneg hCst])
  have hmono : ∫ y in a..(Real.exp 1 * a), f y ≤ ∫ y in a..(Real.exp 1 * a), Cst / y := by
    refine intervalIntegral.integral_mono_ae_restrict hab hf hIntG ?_
    change ∀ᵐ y ∂(volume.restrict (Set.Icc a (Real.exp 1 * a))), f y ≤ Cst / y
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    exact Filter.Eventually.of_forall (fun y hy => hpt y hy)
  have hfun : (fun y : ℝ => Cst / y) = fun y => Cst * (1 / y) := by
    funext y; rw [div_eq_mul_one_div]
  have hval : ∫ y in a..(Real.exp 1 * a), Cst / y = Cst := by
    rw [hfun, intervalIntegral.integral_const_mul,
      Commons.Analysis.Asymptotics.integral_one_div_Ioc_exp_mul a ha, mul_one]
  linarith [hmono, hval]

/-! ## 4. The remainder term: bounds, measurability and `z`-integrability -/

/-- The `y`-integral of `|s3RemPlus|` is bounded by the crude constant of
`Work.FIChain.abs_s3RemPlus_le_crude`, uniformly in `z ≥ 0` (the bound is the integral of the
constant against `dy/y`). -/
private lemma s3f_rem_yint_le (x : ℕ) (lam : ℕ → ℝ) (Cm : ℕ) (hlam : ∀ ν : ℕ, |lam ν| ≤ 1)
    (hYcpos : 0 < Yc x HasBc.val) :
    ∀ z : ℝ, 0 ≤ z →
      (∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val),
        |s3RemPlus lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) Cm| / y)
      ≤ 4 * AcountAtilC x * (((x : ℝ) ^ 3) + 1) * (((x : ℝ) / (Cm : ℝ)) + 1) + 1 := by
  intro z hz0
  set Cr : ℝ := 4 * AcountAtilC x * (((x : ℝ) ^ 3) + 1) * (((x : ℝ) / (Cm : ℝ)) + 1) + 1
    with hCrdef
  have hAnn : 0 ≤ AcountAtilC x := Work.FITop.AcountAtil_nonneg' x
  have hxnn : (0 : ℝ) ≤ (x : ℝ) := Nat.cast_nonneg x
  have hCmnn : (0 : ℝ) ≤ (Cm : ℝ) := Nat.cast_nonneg Cm
  have hCrnn : 0 ≤ Cr := by
    rw [hCrdef]
    refine add_nonneg ?_ zero_le_one
    exact mul_nonneg (mul_nonneg (by positivity) (by positivity)) (by positivity)
  have hYle : Yc x HasBc.val ≤ Real.exp 1 * Yc x HasBc.val :=
    le_mul_of_one_le_left hYcpos.le (Real.one_le_exp (by norm_num))
  have hsz0 : 0 ≤ sc x HasBc.val * z :=
    mul_nonneg (by rw [sc]; positivity) hz0
  have hptb : ∀ y : ℝ,
      |s3RemPlus lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) Cm| ≤ Cr := by
    intro y
    have h := abs_s3RemPlus_le_crude lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) Cm hlam hsz0
    rw [hCrdef]
    linarith
  rw [intervalIntegral.integral_of_le hYle]
  have hIntCr : Integrable (fun y : ℝ => Cr / y)
      (volume.restrict (Set.Ioc (Yc x HasBc.val) (Real.exp 1 * Yc x HasBc.val))) :=
    (intervalIntegrable_div_Ioc (G := fun _ : ℝ => Cr) measurable_const hYcpos hYle Cr
      (fun _ _ => by simp [abs_of_nonneg hCrnn])).1
  have hval : (∫ y in Set.Ioc (Yc x HasBc.val) (Real.exp 1 * Yc x HasBc.val), Cr / y) = Cr := by
    rw [← intervalIntegral.integral_of_le hYle]
    rw [show (fun y : ℝ => Cr / y) = fun y => Cr * (1 / y) by
          funext y; rw [div_eq_mul_one_div],
      intervalIntegral.integral_const_mul,
      Commons.Analysis.Asymptotics.integral_one_div_Ioc_exp_mul (Yc x HasBc.val) hYcpos, mul_one]
  refine le_trans ?_ (le_of_eq hval)
  refine MeasureTheory.integral_mono_of_nonneg ?_ hIntCr ?_
  · exact ae_restrict_of_forall_mem measurableSet_Ioc (fun y hy =>
      div_nonneg (abs_nonneg _) (le_of_lt (lt_trans hYcpos hy.1)))
  · exact ae_restrict_of_forall_mem measurableSet_Ioc (fun y hy =>
      div_le_div_of_nonneg_right (hptb y) (le_of_lt (lt_trans hYcpos hy.1)))

/-- The `z`-dependence of the `y`-integral of `|s3RemPlus|` is measurable. -/
private lemma s3f_rem_meas (x : ℕ) (lam : ℕ → ℝ) (Cm : ℕ) (hYcpos : 0 < Yc x HasBc.val) :
    Measurable (fun z : ℝ =>
      ∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val),
        |s3RemPlus lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) Cm| / y) := by
  have hjoint : Measurable (fun p : ℝ × ℝ =>
      |s3RemPlus lam x p.1 (sc x HasBc.val * p.2) (sc x HasBc.val * p.1) Cm|) :=
    (measurable_s3halves_joint x HasBc.val lam Cm).2
  have hsm : StronglyMeasurable (Function.uncurry (fun z y : ℝ =>
      |s3RemPlus lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) Cm| / y)) :=
    (hjoint.div measurable_snd).stronglyMeasurable
  have h := hsm.integral_prod_right
    (ν := volume.restrict (Set.Ioc (Yc x HasBc.val) (Real.exp 1 * Yc x HasBc.val)))
  have hYle : Yc x HasBc.val ≤ Real.exp 1 * Yc x HasBc.val :=
    le_mul_of_one_le_left hYcpos.le (Real.one_le_exp (by norm_num))
  have hcongr : (fun z : ℝ => ∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val),
        |s3RemPlus lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) Cm| / y)
      = fun z => ∫ y, |s3RemPlus lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) Cm| / y
          ∂(volume.restrict (Set.Ioc (Yc x HasBc.val) (Real.exp 1 * Yc x HasBc.val))) := by
    funext z
    exact intervalIntegral.integral_of_le hYle
  rw [hcongr]
  exact h.measurable

/-- The `z`-integrand of the remainder is `z`-interval-integrable on `(Z, e·Z]`. -/
private lemma s3f_rem_zint_int (x : ℕ) (lam : ℕ → ℝ) (Cm : ℕ) (hlam : ∀ ν : ℕ, |lam ν| ≤ 1)
    (hYcpos : 0 < Yc x HasBc.val) {Z : ℝ} (hZ : 0 < Z) :
    IntervalIntegrable (fun z : ℝ =>
      (∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val),
        |s3RemPlus lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) Cm| / y) / z)
      volume Z (Real.exp 1 * Z) := by
  set Cr : ℝ := 4 * AcountAtilC x * (((x : ℝ) ^ 3) + 1) * (((x : ℝ) / (Cm : ℝ)) + 1) + 1
    with hCrdef
  have hAnn : 0 ≤ AcountAtilC x := Work.FITop.AcountAtil_nonneg' x
  have hxnn : (0 : ℝ) ≤ (x : ℝ) := Nat.cast_nonneg x
  have hCmnn : (0 : ℝ) ≤ (Cm : ℝ) := Nat.cast_nonneg Cm
  have hCrnn : 0 ≤ Cr := by
    rw [hCrdef]
    refine add_nonneg ?_ zero_le_one
    exact mul_nonneg (mul_nonneg (by positivity) (by positivity)) (by positivity)
  have hZle : Z ≤ Real.exp 1 * Z :=
    le_mul_of_one_le_left hZ.le (Real.one_le_exp (by norm_num))
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hZle]
  have hbdd := s3f_rem_yint_le x lam Cm hlam hYcpos
  have hmeas := s3f_rem_meas x lam Cm hYcpos
  refine MeasureTheory.Measure.integrableOn_of_bounded (s_finite := (measure_Ioc_lt_top).ne)
    (f_mble := (hmeas.div measurable_id).aestronglyMeasurable) (M := max (Cr / Z) 0) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioc (fun z hz => ?_)
  have hz0 : 0 < z := lt_trans hZ hz.1
  have hRnn : 0 ≤ (∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val),
      |s3RemPlus lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) Cm| / y) := by
    have hzle : Yc x HasBc.val ≤ Real.exp 1 * Yc x HasBc.val :=
      le_mul_of_one_le_left hYcpos.le (Real.one_le_exp (by norm_num))
    exact intervalIntegral.integral_nonneg hzle (fun y hy =>
      div_nonneg (abs_nonneg _) (le_of_lt (lt_of_lt_of_le hYcpos hy.1)))
  have hRle : (∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val),
      |s3RemPlus lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) Cm| / y) ≤ Cr := by
    simpa [hCrdef] using hbdd z hz0.le
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hRnn hz0.le)]
  have h1 : (∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val),
      |s3RemPlus lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) Cm| / y) / z ≤ Cr / Z :=
    div_le_div₀ hCrnn hRle hZ (le_of_lt hz.1)
  exact le_trans h1 (le_max_left _ _)

/-! ## 5. The pinned-scale `§4–§7` input

The statement below is the `§4–§7` part of the companion's identity (3.4), uniformly over the
`z`-window, at the pinned scale `HasBc.val`: it is exactly the `hPhi` hypothesis of
`Work.FIChain.S3avgFix_le_of_zavg`.  It is the **proved** `Work.FIChain.S3phi_Bstar_v2_sieveBound`
(module `Submission/Work/FIChain/S3phi_Bstar_v2.lean`), assembled from the four summand estimates
`S3phiT_Bstar`, `S3phiT2_Bstar`, `S3phiS2_Bstar_of_prop41`, `S3phiS1_Bstar (K₀)`; the last one —
the `§6`/`S₁` term — is the only one that is *not* `λ`-uniform (`S1_bound_of_sieve` is proportional
to `C_sieve`, and `SieveInput` bounds `C_sieve` only from below), so it carries the uniform
sieve-constant hypothesis `C_sieve ≤ Ksie`.  That hypothesis is exactly what the endgame has: the
chain only ever uses the `(λ, C_sieve)` supplied by its sieve-gap hypothesis, discharged on disk as
`Work.FIChain.rosserLambda_FIgtil_r2`. -/
private lemma s3f_phi_Bstar_K (Kbp : ℝ) (hKbp : 0 < Kbp) (xbp : ℕ)
    (hBwin : ∀ x : ℕ, xbp ≤ x → Work.FIChain.BprimeWindowInt atilc x wc
      (Kbp * AcountAtilC x * (Real.log (x : ℝ)) ^ (-(4 : ℤ)))
      (Yc x HasBc.val / (Deltac x : ℝ)) (sc x HasBc.val * (Real.exp 1 * Yc x HasBc.val)))
    (Ksie : ℝ) (hKsie : 0 < Ksie) :
    ∃ K H : ℝ, ∃ x₀ : ℕ, 0 < K ∧ ∀ x : ℕ, x₀ ≤ x →
      (x : ℝ) ^ ((1 : ℝ) / 4 + 1 / 64) + 2 < Yc x HasBc.val / (Deltac x : ℝ) →
      ∀ lam : ℕ → ℝ, ∀ C_sieve : ℝ,
        SieveInput Submission.ASP.FIgtil (Deltac x) lam C_sieve → C_sieve ≤ Ksie →
        ∀ z ∈ Set.Icc (zc x HasBc.val) (Real.exp 1 * zc x HasBc.val),
          |(∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val),
              (Submission.ASP.Tsum atilc lam (x : ℝ) y
                - Submission.ASP.Tsum2 atilc lam (x : ℝ) y z
                + Submission.ASP.S2 atilc lam x y z (sc x HasBc.val * y)
                + Submission.ASP.S1 atilc lam x (sc x HasBc.val * y) (sc x HasBc.val * z)) / y)
            - H * AcountAtilC x|
          ≤ K * AcountAtilC x
              * (Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ)) :=
  S3phi_Bstar_v2_sieveBound Kbp hKbp xbp hBwin Ksie hKsie

/-- `2 ≤ sc x HasBc.val` eventually, so that the `λ⁺`-remainder hypothesis `2 ≤ sc x B` of
`Work.FIChain.s3RemPlus_zavg_le` holds at the pinned scale. -/
private lemma s3f_sc_ge_two : ∀ᶠ x : ℕ in Filter.atTop, (2 : ℝ) ≤ sc x HasBc.val := by
  filter_upwards [Work.FITop.FI_ev_log_rpow_le_nat (b := HasBc.val + 2) (ε := (3 : ℝ) / 16)
      (C := 1 / 4) (by norm_num) (by norm_num), eventually_ge_atTop 2] with x hle hx2
  have hx1 : (1 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 1 < x)
  have hLpos : 0 < Real.log (x : ℝ) := Real.log_pos hx1
  have hu1 : (2 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac)
      / (2 * (Real.log (x : ℝ)) ^ (HasBc.val + 2)) := by
    rw [show (1 : ℝ) / 4 - 2 * etac = 3 / 16 by norm_num [etac], le_div_iff₀ (by positivity)]
    linarith
  rw [sc, Jc]
  have hJ1 : (1 : ℕ) ≤ ⌈Real.log ((x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac)
      / (2 * (Real.log (x : ℝ)) ^ (HasBc.val + 2))) / Real.log 2⌉₊ := by
    have h1 : (1 : ℝ) ≤ Real.log ((x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac)
        / (2 * (Real.log (x : ℝ)) ^ (HasBc.val + 2))) / Real.log 2 := by
      rw [le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
      simpa using Real.log_le_log (by norm_num) hu1
    have h4 : (1 : ℝ) ≤ ((⌈Real.log ((x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac)
        / (2 * (Real.log (x : ℝ)) ^ (HasBc.val + 2))) / Real.log 2⌉₊ : ℕ) : ℝ) :=
      le_trans h1 (Nat.le_ceil _)
    exact_mod_cast h4
  calc (2 : ℝ) = 2 ^ (1 : ℕ) := by norm_num
    _ ≤ 2 ^ (⌈Real.log ((x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac)
        / (2 * (Real.log (x : ℝ)) ^ (HasBc.val + 2))) / Real.log 2⌉₊) :=
        pow_le_pow_right₀ (by norm_num) hJ1

/-- **The pointwise-in-`z` bound on the `y`-integral of `|S₃|`.**  Splitting
`S₃ = (main + rem) − S₃⁻` at the fixed `z` (`s3f_S3_eq_S3plusC_sub_S3minusC` +
`S3plusC_eq_main_add_rem`), bounding `|main|` pointwise by `Mplus`, and integrating the triangle
inequality against the integrable comparator `(Mplus + |rem| + |S₃⁻|)/y`.  The `λ⁻`-term stays as
the raw `y`-integral: it is dominated afterwards by the dyadic `Grho`-sum (`Work.FIPiChain.Grho`),
whose `z`-average the caller supplies. -/
private lemma s3f_F_le_psi (x : ℕ) (lam : ℕ → ℝ) (Cm : ℕ) (Mplus : ℝ)
    (hMpnn : 0 ≤ Mplus)
    (hmainb : ∀ z ∈ Set.Icc (zc x HasBc.val) (Real.exp 1 * zc x HasBc.val),
      ∀ y ∈ Set.Icc (Yc x HasBc.val) (Real.exp 1 * Yc x HasBc.val),
      |s3MainPlus lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) Cm| ≤ Mplus)
    (hCm1 : 1 ≤ Cm) (hCmpos : (0 : ℝ) < (Cm : ℝ))
    (hCmdef : Cm = ⌊(zc x HasBc.val) ^ (1 - etac)⌋₊)
    (hzc1 : 1 ≤ zc x HasBc.val) (hzc2 : (2 : ℝ) ≤ zc x HasBc.val) (hzcg1 : 1 < zc x HasBc.val)
    (hzcpos : 0 < zc x HasBc.val)
    (hDz : (Deltac x : ℝ) < zc x HasBc.val)
    (hYcpos : 0 < Yc x HasBc.val) (hYle : Yc x HasBc.val ≤ Real.exp 1 * Yc x HasBc.val)
    (hsupp : ∀ ν : ℕ, Deltac x < ν → lam ν = 0)
    (hlam1 : ∀ ν : ℕ, |lam ν| ≤ 1) :
    ∀ z ∈ Set.Icc (zc x HasBc.val) (Real.exp 1 * zc x HasBc.val),
      (∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val),
        |Submission.ASP.S3 atilc lam x z (sc x HasBc.val * y) (sc x HasBc.val * z)| / y)
      ≤ Mplus + (∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val),
          |s3RemPlus lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) Cm| / y)
        + (∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val),
          |S3minusC atilc lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) ((Cm : ℕ) : ℝ)| / y) := by
  intro z hz
  have hz1 : (1 : ℝ) ≤ z := le_trans hzc1 hz.1
  have hz2 : (2 : ℝ) ≤ z := le_trans hzc2 hz.1
  have hzge0 : 0 ≤ z := le_of_lt (lt_of_lt_of_le hzcpos hz.1)
  have hzCm : ((Cm : ℕ) : ℝ) < z := by
    have h1 : ((Cm : ℕ) : ℝ) ≤ (zc x HasBc.val) ^ (1 - etac) := by
      rw [hCmdef]
      exact Nat.floor_le (Real.rpow_nonneg (le_of_lt hzcpos) _)
    have h2 : (zc x HasBc.val) ^ (1 - etac) < zc x HasBc.val :=
      Real.rpow_lt_self_of_one_lt hzcg1 (by norm_num [etac])
    linarith [h1, h2, hz.1]
  set Rz : ℝ := (∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val),
      |s3RemPlus lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) Cm| / y) with hRzdef
  set Sz : ℝ := (∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val),
      |S3minusC atilc lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) ((Cm : ℕ) : ℝ)| / y) with hSzdef
  have hscnn : 0 ≤ sc x HasBc.val := by rw [sc]; positivity
  have hsc1 : (1 : ℝ) ≤ sc x HasBc.val := by rw [sc]; exact one_le_pow₀ (by norm_num)
  -- the identity at the fixed `z`
  have hsplit : ∀ y : ℝ,
      Submission.ASP.S3 atilc lam x z (sc x HasBc.val * y) (sc x HasBc.val * z)
        = s3MainPlus lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) Cm
          + s3RemPlus lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) Cm
          - S3minusC atilc lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) ((Cm : ℕ) : ℝ) := by
    intro y
    have h1 := s3f_S3_eq_S3plusC_sub_S3minusC atilc lam x z (sc x HasBc.val * y) (sc x HasBc.val * z)
      ((Cm : ℕ) : ℝ) (Deltac x) (fun n hn => Work.FITop.rwcp_atil_eq_zero hn) hsupp
      (lt_of_lt_of_le hDz hz.1) hz1 (by
        have hC1 : (1 : ℝ) ≤ ((Cm : ℕ) : ℝ) := by exact_mod_cast hCm1
        linarith)
    have hsz1 : (1 : ℝ) ≤ sc x HasBc.val * z := by
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ sc x HasBc.val * z := mul_le_mul hsc1 hz1 (by norm_num) (by linarith)
    have hzsz : z ≤ sc x HasBc.val * z := le_mul_of_one_le_left hzge0 hsc1
    have hT : (1 : ℝ) ≤ sc x HasBc.val * z / (Cm : ℝ) := by
      rw [le_div_iff₀ hCmpos, one_mul]
      exact le_trans (le_of_lt hzCm) hzsz
    have h2 := S3plusC_eq_main_add_rem lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) Cm hCm1 hz2
      hzCm hsz1 hzsz hT
    rw [h1, h2]
  -- integrability of the three pieces on `(Y, e·Y]`
  set Cr : ℝ := 4 * AcountAtilC x * (((x : ℝ) ^ 3) + 1) * (((x : ℝ) / (Cm : ℝ)) + 1) + 1
    with hCrdef
  have hAnn : 0 ≤ AcountAtilC x := Work.FITop.AcountAtil_nonneg' x
  have hxnn : (0 : ℝ) ≤ (x : ℝ) := Nat.cast_nonneg x
  have hCmnn : (0 : ℝ) ≤ (Cm : ℝ) := Nat.cast_nonneg Cm
  have hCrnn : 0 ≤ Cr := by
    rw [hCrdef]
    refine add_nonneg ?_ zero_le_one
    exact mul_nonneg (mul_nonneg (by positivity) (by positivity)) (by positivity)
  have hI1 : Integrable (fun y : ℝ => Mplus / y)
      (volume.restrict (Set.Ioc (Yc x HasBc.val) (Real.exp 1 * Yc x HasBc.val))) :=
    (intervalIntegrable_div_Ioc (G := fun _ : ℝ => Mplus) measurable_const hYcpos hYle Mplus
      (fun _ _ => by simp [abs_of_nonneg hMpnn])).1
  have hI2 : Integrable (fun y : ℝ =>
      |s3RemPlus lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) Cm| / y)
      (volume.restrict (Set.Ioc (Yc x HasBc.val) (Real.exp 1 * Yc x HasBc.val))) := by
    refine MeasureTheory.Measure.integrableOn_of_bounded (s_finite := (measure_Ioc_lt_top).ne)
      (f_mble := ?_) (M := Cr / Yc x HasBc.val) ?_
    · have hjoint : Measurable (fun p : ℝ × ℝ =>
          |s3RemPlus lam x p.1 (sc x HasBc.val * p.2) (sc x HasBc.val * p.1) Cm|) :=
        (measurable_s3halves_joint x HasBc.val lam Cm).2
      have hsec : Measurable (fun y : ℝ =>
          |s3RemPlus lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) Cm|) :=
        hjoint.comp (measurable_const.prodMk measurable_id)
      exact (hsec.div measurable_id).aestronglyMeasurable
    · refine ae_restrict_of_forall_mem measurableSet_Ioc (fun y hy => ?_)
      have hy0 : 0 < y := lt_trans hYcpos hy.1
      have hsz0 : 0 ≤ sc x HasBc.val * z := mul_nonneg hscnn hzge0
      have hb := abs_s3RemPlus_le_crude lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) Cm hlam1 hsz0
      have hb' : |s3RemPlus lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) Cm| ≤ Cr := by
        rw [hCrdef]; linarith [hb]
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (abs_nonneg _) (le_of_lt hy0))]
      calc |s3RemPlus lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) Cm| / y
          ≤ Cr / y := div_le_div_of_nonneg_right hb' (le_of_lt hy0)
        _ ≤ Cr / Yc x HasBc.val := div_le_div_of_nonneg_left hCrnn hYcpos (le_of_lt hy.1)
  have hI3 : Integrable (fun y : ℝ =>
      |S3minusC atilc lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) ((Cm : ℕ) : ℝ)| / y)
      (volume.restrict (Set.Ioc (Yc x HasBc.val) (Real.exp 1 * Yc x HasBc.val))) := by
    have h0 := intervalIntegrable_abs_step_div HasBc.val x hYcpos lam
      (fun ℓ => S3minusInnerC atilc x ℓ z (sc x HasBc.val * z) ((Cm : ℕ) : ℝ))
    have hfun : (fun y : ℝ => |S3step x lam
          (fun ℓ => S3minusInnerC atilc x ℓ z (sc x HasBc.val * z) ((Cm : ℕ) : ℝ)) (sc x HasBc.val * y)| / y)
        = fun y : ℝ => |S3minusC atilc lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) ((Cm : ℕ) : ℝ)| / y := by
      funext y; rw [S3minusC_eq_S3step]
    rw [hfun] at h0
    exact h0.1
  have hg : Integrable (fun y : ℝ => (Mplus / y + |s3RemPlus lam x z (sc x HasBc.val * y)
        (sc x HasBc.val * z) Cm| / y)
      + |S3minusC atilc lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) ((Cm : ℕ) : ℝ)| / y)
      (volume.restrict (Set.Ioc (Yc x HasBc.val) (Real.exp 1 * Yc x HasBc.val))) :=
    (hI1.add hI2).add hI3
  -- the pointwise comparison
  have hcmp : (∫ y in Set.Ioc (Yc x HasBc.val) (Real.exp 1 * Yc x HasBc.val),
        |Submission.ASP.S3 atilc lam x z (sc x HasBc.val * y) (sc x HasBc.val * z)| / y)
      ≤ ∫ y in Set.Ioc (Yc x HasBc.val) (Real.exp 1 * Yc x HasBc.val),
          ((Mplus / y + |s3RemPlus lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) Cm| / y)
            + |S3minusC atilc lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) ((Cm : ℕ) : ℝ)| / y) := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ hg ?_
    · exact ae_restrict_of_forall_mem measurableSet_Ioc (fun y hy =>
        div_nonneg (abs_nonneg _) (le_of_lt (lt_trans hYcpos hy.1)))
    · refine ae_restrict_of_forall_mem measurableSet_Ioc (fun y hy => ?_)
      dsimp only
      have hy0 : 0 < y := lt_trans hYcpos hy.1
      have hmainb' : |s3MainPlus lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) Cm| ≤ Mplus :=
        hmainb z hz y ⟨le_of_lt hy.1, hy.2⟩
      have htri : |s3MainPlus lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) Cm
            + s3RemPlus lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) Cm
            - S3minusC atilc lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) ((Cm : ℕ) : ℝ)|
          ≤ |s3MainPlus lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) Cm|
            + |s3RemPlus lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) Cm|
            + |S3minusC atilc lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) ((Cm : ℕ) : ℝ)| := by
        have h2 := abs_sub_le (s3MainPlus lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) Cm
          + s3RemPlus lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) Cm) 0
          (S3minusC atilc lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) ((Cm : ℕ) : ℝ))
        have h3 := abs_add_le (s3MainPlus lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) Cm)
          (s3RemPlus lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) Cm)
        simp only [sub_zero, zero_sub, abs_neg] at h2
        linarith [h2, h3]
      rw [hsplit y]
      calc |s3MainPlus lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) Cm
            + s3RemPlus lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) Cm
            - S3minusC atilc lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) ((Cm : ℕ) : ℝ)| / y
          ≤ (|s3MainPlus lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) Cm|
              + |s3RemPlus lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) Cm|
              + |S3minusC atilc lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) ((Cm : ℕ) : ℝ)|) / y :=
            div_le_div_of_nonneg_right htri (le_of_lt hy0)
        _ ≤ (Mplus + |s3RemPlus lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) Cm|
              + |S3minusC atilc lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) ((Cm : ℕ) : ℝ)|) / y :=
            div_le_div_of_nonneg_right (by linarith [hmainb']) (le_of_lt hy0)
        _ = (Mplus / y + |s3RemPlus lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) Cm| / y)
              + |S3minusC atilc lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) ((Cm : ℕ) : ℝ)| / y := by
            ring
  -- the value of the comparator integral
  have hval : (∫ y in Set.Ioc (Yc x HasBc.val) (Real.exp 1 * Yc x HasBc.val),
        ((Mplus / y + |s3RemPlus lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) Cm| / y)
          + |S3minusC atilc lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) ((Cm : ℕ) : ℝ)| / y))
      = Mplus + Rz + Sz := by
    have heq1 : (∫ y in Set.Ioc (Yc x HasBc.val) (Real.exp 1 * Yc x HasBc.val),
          (Mplus / y + |s3RemPlus lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) Cm| / y)
            + |S3minusC atilc lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) ((Cm : ℕ) : ℝ)| / y)
        = (∫ y in Set.Ioc (Yc x HasBc.val) (Real.exp 1 * Yc x HasBc.val),
            (Mplus / y + |s3RemPlus lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) Cm| / y))
          + (∫ y in Set.Ioc (Yc x HasBc.val) (Real.exp 1 * Yc x HasBc.val),
            |S3minusC atilc lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) ((Cm : ℕ) : ℝ)| / y) :=
      MeasureTheory.integral_add (hI1.add hI2) hI3
    have heq2 : (∫ y in Set.Ioc (Yc x HasBc.val) (Real.exp 1 * Yc x HasBc.val),
          Mplus / y + |s3RemPlus lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) Cm| / y)
        = (∫ y in Set.Ioc (Yc x HasBc.val) (Real.exp 1 * Yc x HasBc.val), Mplus / y)
          + (∫ y in Set.Ioc (Yc x HasBc.val) (Real.exp 1 * Yc x HasBc.val),
            |s3RemPlus lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) Cm| / y) :=
      MeasureTheory.integral_add hI1 hI2
    rw [heq1, heq2]
    have h1 : (∫ y in Set.Ioc (Yc x HasBc.val) (Real.exp 1 * Yc x HasBc.val), Mplus / y) = Mplus := by
      rw [← intervalIntegral.integral_of_le hYle]
      rw [show (fun y : ℝ => Mplus / y) = fun y => Mplus * (1 / y) by
            funext y; rw [div_eq_mul_one_div],
        intervalIntegral.integral_const_mul,
        Commons.Analysis.Asymptotics.integral_one_div_Ioc_exp_mul (Yc x HasBc.val) hYcpos, mul_one]
    have h2 : (∫ y in Set.Ioc (Yc x HasBc.val) (Real.exp 1 * Yc x HasBc.val),
        |s3RemPlus lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) Cm| / y) = Rz := by
      rw [hRzdef]
      exact (intervalIntegral.integral_of_le (f := fun y : ℝ =>
        |s3RemPlus lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) Cm| / y) hYle).symm
    have h3 : (∫ y in Set.Ioc (Yc x HasBc.val) (Real.exp 1 * Yc x HasBc.val),
        |S3minusC atilc lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) ((Cm : ℕ) : ℝ)| / y) = Sz := by
      rw [hSzdef]
      exact (intervalIntegral.integral_of_le (f := fun y : ℝ =>
        |S3minusC atilc lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) ((Cm : ℕ) : ℝ)| / y) hYle).symm
    rw [h1, h2, h3]
  rw [intervalIntegral.integral_of_le hYle, hRzdef]
  calc (∫ y in Set.Ioc (Yc x HasBc.val) (Real.exp 1 * Yc x HasBc.val),
        |Submission.ASP.S3 atilc lam x z (sc x HasBc.val * y) (sc x HasBc.val * z)| / y)
      ≤ _ := hcmp
    _ = Mplus + Rz + Sz := hval
/-- The final arithmetic: the sum of the five bounds is `≤ K·Ã(x)·loglog/log x` for
`K = Kp + Kr + Km + Kd + 2Kφ + 1`.  The terms carrying `(log x)^{-1}` and `(log x)^{-2}` are
absorbed by the factor `loglog x ≥ 1`; the `§6`-term (`S₁`) genuinely carries a `loglog x`. -/
private lemma s3f_final_arith {A L LL Kp Kr Km Kd Kφ : ℝ} (hA : 0 ≤ A) (hL : 1 ≤ L)
    (hLL : 1 ≤ LL) (hKp : 0 ≤ Kp) (hKr : 0 ≤ Kr) (hKm : 0 ≤ Km) (hKd : 0 ≤ Kd)
    (hKφ : 0 ≤ Kφ) :
    Kp * A * L ^ (-(1 : ℤ)) + Km * A * L ^ (-(2 : ℤ)) + Kr * A * L ^ (-(1 : ℤ))
        + 2 * (Kφ * A * (LL / L)) + Kd * A * L ^ (-(1 : ℤ))
      ≤ (Kp + Kr + Km + Kd + 2 * Kφ + 1) * A * (LL / L) := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hLnn : 0 ≤ L := le_of_lt hLpos
  have hLLnn : 0 ≤ LL := le_trans zero_le_one hLL
  have hLLdiv : 0 ≤ LL / L := div_nonneg hLLnn hLnn
  have hp2 : L ^ (-(1 : ℤ)) ≤ LL / L := by
    have h1 : L ^ (-(1 : ℤ)) = L⁻¹ := zpow_neg_one L
    have h2 : LL / L = LL * L⁻¹ := div_eq_mul_inv LL L
    rw [h1, h2]
    calc L⁻¹ = 1 * L⁻¹ := (one_mul _).symm
      _ ≤ LL * L⁻¹ := mul_le_mul_of_nonneg_right hLL (by positivity)
  have hp3 : L ^ (-(2 : ℤ)) ≤ LL / L :=
    le_trans (zpow_le_zpow_right₀ hL (by norm_num : (-(2 : ℤ)) ≤ (-(1 : ℤ)))) hp2
  have h1 : Kp * A * L ^ (-(1 : ℤ)) ≤ Kp * A * (LL / L) :=
    mul_le_mul_of_nonneg_left hp2 (mul_nonneg hKp hA)
  have h2 : Km * A * L ^ (-(2 : ℤ)) ≤ Km * A * (LL / L) :=
    mul_le_mul_of_nonneg_left hp3 (mul_nonneg hKm hA)
  have h3 : Kr * A * L ^ (-(1 : ℤ)) ≤ Kr * A * (LL / L) :=
    mul_le_mul_of_nonneg_left hp2 (mul_nonneg hKr hA)
  have h5 : Kd * A * L ^ (-(1 : ℤ)) ≤ Kd * A * (LL / L) :=
    mul_le_mul_of_nonneg_left hp2 (mul_nonneg hKd hA)
  have hsum : Kp * A * L ^ (-(1 : ℤ)) + Km * A * L ^ (-(2 : ℤ)) + Kr * A * L ^ (-(1 : ℤ))
      + 2 * (Kφ * A * (LL / L)) + Kd * A * L ^ (-(1 : ℤ))
      ≤ (Kp + Kr + Km + Kd + 2 * Kφ) * A * (LL / L) := by
    nlinarith [h1, h2, h3, h5, hA, hLLdiv, hKp, hKr, hKm, hKd, hKφ]
  have hstep : (Kp + Kr + Km + Kd + 2 * Kφ) * A * (LL / L)
      ≤ (Kp + Kr + Km + Kd + 2 * Kφ + 1) * A * (LL / L) := by
    have h64 : 0 ≤ A * (LL / L) := mul_nonneg hA hLLdiv
    nlinarith
  exact le_trans hsum hstep

/-! ## 6. The main statement -/

/-- **The endgame's `§8` `S₃` input, at a free scale `HasBc.val ≥ 2`, from the *integrated* `ρ`-window.**

This is `Work.FIChain.S3fixed_signed_Bstar` with (i) the pin `Bstar` replaced by the free scale
`HasBc.val`, and (ii) the pointwise `ρ`-window of the frozen contract replaced by its **`z`-integrated**
form, exactly as the lead design (`Submission/Work/FIFinal/PIREMOVAL_LEAD.md`, §3 P3/P4) prescribes:
the companion's §8 is proved on disk in its true `z`-averaged shape, and the fixed-`z` consumer only
needs the *average* over `z ∈ [zc x B, e·zc x B]` because the chain integrates `S₃` against `dz/z`
(both endpoints contribute `∫ dz/z = 1`).

The `λ⁻`-half of `S₃` is dominated, at fixed `z`, by the dyadic `Grho`-sum
`Σ_{j < Jc} Grho x Cm (2^j z)` (`Work.FIPiChain.S3minusC_dyadic_le`); that sum is measurable and
bounded (`Work.FIPiChain.Grho_sum_measurable_bdd`) and its `z`-average is controlled by the
integrated `ρ`-window (`Work.FIPiChain.Grho_sum_zavg_le`).  Those three facts are taken here as
hypotheses (`hdyad`, `hWmeas`, `hWint`, `hWbdd`, `hWzavg`), so that this module depends only on the
`Grho` *vocabulary* and not on the delegated `P3` proofs; `Work.FIPiChain` supplies them from `hρ`
in the P4 assembly, where the integrated window is instantiated. -/
theorem S3fixed_signed_Bstar (Kbp : ℝ) (hKbp : 0 < Kbp) (xbp : ℕ)
    (hBwin : ∀ x : ℕ, xbp ≤ x → Work.FIChain.BprimeWindowInt atilc x wc
      (Kbp * AcountAtilC x * (Real.log (x : ℝ)) ^ (-(4 : ℤ)))
      (Yc x HasBc.val / (Deltac x : ℝ)) (sc x HasBc.val * (Real.exp 1 * Yc x HasBc.val)))
    (Ksie : ℝ) (hKsie : 0 < Ksie)
    (hsieve : ∀ Δ : ℕ, 3 ≤ Δ → ∃ lam : ℕ → ℝ, ∃ Cs : ℝ,
      Work.FIChain.SieveInput Submission.ASP.FIgtil Δ lam Cs ∧ Cs ≤ Ksie)
    (Krho : ℝ) (hKrho : 0 ≤ Krho)
    (hdyad : ∀ᶠ x : ℕ in Filter.atTop, ∀ lam' : ℕ → ℝ, (∀ ν : ℕ, |lam' ν| ≤ 1) →
      ∀ z ∈ Set.Icc (zc x HasBc.val) (Real.exp 1 * zc x HasBc.val), ∀ y : ℝ,
      |S3minusC atilc lam' x z (sc x HasBc.val * y) (sc x HasBc.val * z)
          (((⌊(zc x HasBc.val) ^ (1 - etac)⌋₊ : ℕ) : ℝ))|
        ≤ ∑ j ∈ Finset.range (Jc x HasBc.val),
            Grho x (((⌊(zc x HasBc.val) ^ (1 - etac)⌋₊ : ℕ) : ℝ)) ((2 : ℝ) ^ j * z))
    (hWmeas : ∀ᶠ x : ℕ in Filter.atTop, Measurable (fun z : ℝ =>
      ∑ j ∈ Finset.range (Jc x HasBc.val),
        Grho x (((⌊(zc x HasBc.val) ^ (1 - etac)⌋₊ : ℕ) : ℝ)) ((2 : ℝ) ^ j * z)))
    (hWint : ∀ᶠ x : ℕ in Filter.atTop, IntervalIntegrable (fun z : ℝ =>
      (∑ j ∈ Finset.range (Jc x HasBc.val),
        Grho x (((⌊(zc x HasBc.val) ^ (1 - etac)⌋₊ : ℕ) : ℝ)) ((2 : ℝ) ^ j * z)) / z)
      volume (zc x HasBc.val) (Real.exp 1 * zc x HasBc.val))
    (hWbdd : ∀ᶠ x : ℕ in Filter.atTop, ∃ V : ℝ,
      ∀ z ∈ Set.Icc (zc x HasBc.val) (Real.exp 1 * zc x HasBc.val),
        (∑ j ∈ Finset.range (Jc x HasBc.val),
          Grho x (((⌊(zc x HasBc.val) ^ (1 - etac)⌋₊ : ℕ) : ℝ)) ((2 : ℝ) ^ j * z)) ≤ V)
    (hWzavg : ∀ᶠ x : ℕ in Filter.atTop,
      (∫ z in zc x HasBc.val..(Real.exp 1 * zc x HasBc.val),
        (∑ j ∈ Finset.range (Jc x HasBc.val),
          Grho x (((⌊(zc x HasBc.val) ^ (1 - etac)⌋₊ : ℕ) : ℝ)) ((2 : ℝ) ^ j * z)) / z)
        ≤ (Jc x HasBc.val : ℝ)
            * (Krho * AcountAtilC x * (Real.log (x : ℝ)) ^ (-(4 : ℤ)))) :
    ∃ K : ℝ, ∃ x₀ : ℕ, 0 < K ∧ ∀ x : ℕ, x₀ ≤ x →
      (x : ℝ) ^ ((1 : ℝ) / 4 + 1 / 64) + 2 < Work.FIChain.Yc x HasBc.val / (Work.FIChain.Deltac x : ℝ) →
      ∀ lam : ℕ → ℝ, ∀ Cs : ℝ,
        Work.FIChain.SieveInput Submission.ASP.FIgtil (Work.FIChain.Deltac x) lam Cs → Cs ≤ Ksie →
        |(∫ y in Work.FIChain.Yc x HasBc.val..(Real.exp 1 * Work.FIChain.Yc x HasBc.val),
            Submission.ASP.S3 Work.FIChain.atilc lam x (Work.FIChain.zc x HasBc.val)
              (Work.FIChain.sc x HasBc.val * y)
              (Work.FIChain.sc x HasBc.val * Work.FIChain.zc x HasBc.val) / y)|
          ≤ K * Work.FIChain.AcountAtilC x
              * (Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ)) := by
  obtain ⟨Kφ, H, xφ, hKφpos, hphi⟩ := s3f_phi_Bstar_K Kbp hKbp xbp hBwin Ksie hKsie
  obtain ⟨Kd, xd, hKdpos, hdel⟩ := S3delSum_Bstar
  obtain ⟨Kp, hKppos, hmainpt_all⟩ := s3MainPlus_pt_le
  obtain ⟨xmp, hmainpt⟩ := hmainpt_all HasBc.val s3fB_Bstar_pos
  obtain ⟨Kr, hKrpos, hremz_all⟩ := s3RemPlus_zavg_le
  obtain ⟨xrz, hremz⟩ := hremz_all HasBc.val s3fB_Bstar_pos
  obtain ⟨xd1, hd1⟩ := Filter.eventually_atTop.1 hdyad
  obtain ⟨xd2, hd2⟩ := Filter.eventually_atTop.1 hWmeas
  obtain ⟨xd3, hd3⟩ := Filter.eventually_atTop.1 hWint
  obtain ⟨xd4, hd4⟩ := Filter.eventually_atTop.1 hWbdd
  obtain ⟨xd5, hd5⟩ := Filter.eventually_atTop.1 hWzavg
  obtain ⟨xJ, hJ⟩ := Filter.eventually_atTop.1 s3f_Jc_logC_bound
  obtain ⟨xa, ha⟩ := Filter.eventually_atTop.1 (scale_factsC HasBc.val s3fB_Bstar_pos)
  obtain ⟨xb, hb⟩ := Filter.eventually_atTop.1 s3f_sc_ge_two
  obtain ⟨xc, hc⟩ := Filter.eventually_atTop.1 (Work.FITop.FI_ev_log_ge_nat 2)
  obtain ⟨xe, he⟩ := Filter.eventually_atTop.1 (Work.FITop.FI_ev_log_ge_nat (Real.exp 1))
  refine ⟨Kp + Kr + Krho + Kd + 2 * Kφ + 1,
    xmp + xrz + xd + xd1 + xd2 + xd3 + xd4 + xd5 + xJ + xφ + xa + xb + xc + xe + 2,
    by positivity, ?_⟩
  intro x hx hcond lam Cs hSieve hCs
  have hxd : xd ≤ x := by omega
  have hxφ : xφ ≤ x := by omega
  have hxa : xa ≤ x := by omega
  have hxmp : xmp ≤ x := by omega
  have hxrz : xrz ≤ x := by omega
  have hxd1 : xd1 ≤ x := by omega
  have hxd2 : xd2 ≤ x := by omega
  have hxd3 : xd3 ≤ x := by omega
  have hxd4 : xd4 ≤ x := by omega
  have hxd5 : xd5 ≤ x := by omega
  have hxJ : xJ ≤ x := by omega
  have hxb : xb ≤ x := by omega
  have hxc : xc ≤ x := by omega
  have hxe : xe ≤ x := by omega
  have hL2 : (2 : ℝ) ≤ Real.log (x : ℝ) := hc x hxc
  have hLpos : 0 < Real.log (x : ℝ) := by linarith
  have hLL1 : (1 : ℝ) ≤ Real.log (Real.log (x : ℝ)) := by
    have h1 := he x hxe
    have h2 := Real.log_le_log (Real.exp_pos 1) h1
    rwa [Real.log_exp] at h2
  have hsc2x : (2 : ℝ) ≤ sc x HasBc.val := hb x hxb
  have hAnn : 0 ≤ AcountAtilC x := Work.FITop.AcountAtil_nonneg' x
  obtain ⟨hY256, hYc2, -, -, -, -, -, hDz, hzx, -, -, -, -, -, -⟩ := ha x hxa
  have hYcnn : 0 ≤ Yc x HasBc.val := by
    rw [Yc]
    have h2 : (0 : ℝ) < (Real.log (x : ℝ)) ^ (HasBc.val + 2) := Real.rpow_pos_of_pos hLpos _
    positivity
  have hYcpos : 0 < Yc x HasBc.val := by
    have h1 : (1 : ℝ) ≤ (⌊Yc x HasBc.val⌋₊ : ℝ) := by
      exact_mod_cast (le_trans (by norm_num : 1 ≤ 256) hY256)
    have h2 : (1 : ℝ) ≤ Yc x HasBc.val := le_trans h1 (Nat.floor_le hYcnn)
    linarith
  have hzc1 : (1 : ℝ) ≤ zc x HasBc.val := by
    have h1 : (1 : ℝ) ≤ (⌊Yc x HasBc.val⌋₊ : ℝ) := by
      exact_mod_cast (le_trans (by norm_num : 1 ≤ 256) hY256)
    simpa [zc, Zc] using h1
  have hzc2 : (2 : ℝ) ≤ zc x HasBc.val := by
    have h1 : (2 : ℝ) ≤ (⌊Yc x HasBc.val⌋₊ : ℝ) := by
      exact_mod_cast (le_trans (by norm_num : 2 ≤ 256) hY256)
    simpa [zc, Zc] using h1
  have hzcpos : 0 < zc x HasBc.val := lt_of_lt_of_le zero_lt_one hzc1
  have hzcg1 : 1 < zc x HasBc.val := lt_of_lt_of_le (by norm_num) hzc2
  have hYle : Yc x HasBc.val ≤ Real.exp 1 * Yc x HasBc.val :=
    le_mul_of_one_le_left hYcpos.le (Real.one_le_exp (by norm_num))
  have hzle : zc x HasBc.val ≤ Real.exp 1 * zc x HasBc.val :=
    le_mul_of_one_le_left hzcpos.le (Real.one_le_exp (by norm_num))
  set Cm : ℕ := ⌊(zc x HasBc.val) ^ (1 - etac)⌋₊ with hCmdef
  have hCm1 : 1 ≤ Cm := by
    rw [hCmdef]
    refine Nat.le_floor ?_
    have h2 : (0 : ℝ) < 1 - etac := by norm_num [etac]
    have h3 : (1 : ℝ) ^ (1 - etac) ≤ (zc x HasBc.val) ^ (1 - etac) :=
      Real.rpow_le_rpow zero_le_one hzc1 h2.le
    simpa using h3
  have hCmR : (1 : ℝ) ≤ (Cm : ℝ) := by exact_mod_cast hCm1
  have hCmpos : (0 : ℝ) < (Cm : ℝ) := by linarith
  set L : ℝ := Real.log (x : ℝ) with hLdef
  set LL : ℝ := Real.log (Real.log (x : ℝ)) with hLLdef
  have hLL1' : (1 : ℝ) ≤ LL := by rw [hLLdef]; exact hLL1
  set Mplus : ℝ := Kp * AcountAtilC x * L ^ (-(1 : ℤ)) with hMpdef
  set Crz : ℝ := Kr * AcountAtilC x * L ^ (-(1 : ℤ)) with hCrzdef
  have hMpnn : 0 ≤ Mplus := by
    rw [hMpdef]
    exact mul_nonneg (mul_nonneg hKppos.le hAnn) (by positivity)
  -- ## the `ρ`-side data at this `x`
  have hdyadx : ∀ z ∈ Set.Icc (zc x HasBc.val) (Real.exp 1 * zc x HasBc.val), ∀ y : ℝ,
      |S3minusC atilc lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) ((Cm : ℕ) : ℝ)|
        ≤ ∑ j ∈ Finset.range (Jc x HasBc.val),
            Grho x ((Cm : ℕ) : ℝ) ((2 : ℝ) ^ j * z) := by
    intro z hz y
    simpa [hCmdef] using hd1 x hxd1 lam hSieve.2.2.2.1 z hz y
  have hWmeas' : Measurable (fun z : ℝ =>
      ∑ j ∈ Finset.range (Jc x HasBc.val), Grho x ((Cm : ℕ) : ℝ) ((2 : ℝ) ^ j * z)) := by
    simpa [hCmdef] using hd2 x hxd2
  have hWint' : IntervalIntegrable (fun z : ℝ =>
      (∑ j ∈ Finset.range (Jc x HasBc.val), Grho x ((Cm : ℕ) : ℝ) ((2 : ℝ) ^ j * z)) / z)
      volume (zc x HasBc.val) (Real.exp 1 * zc x HasBc.val) := by
    simpa [hCmdef] using hd3 x hxd3
  obtain ⟨Vw, hVw⟩ := hd4 x hxd4
  have hWbdd' : ∃ V : ℝ, ∀ z ∈ Set.Icc (zc x HasBc.val) (Real.exp 1 * zc x HasBc.val),
      (∑ j ∈ Finset.range (Jc x HasBc.val), Grho x ((Cm : ℕ) : ℝ) ((2 : ℝ) ^ j * z)) ≤ V :=
    ⟨Vw, fun z hz => by simpa [hCmdef] using hVw z hz⟩
  have hWzavg' : (∫ z in zc x HasBc.val..(Real.exp 1 * zc x HasBc.val),
      (∑ j ∈ Finset.range (Jc x HasBc.val), Grho x ((Cm : ℕ) : ℝ) ((2 : ℝ) ^ j * z)) / z)
      ≤ (Jc x HasBc.val : ℝ) * (Krho * AcountAtilC x * L ^ (-(4 : ℤ))) := by
    simpa [hCmdef, hLdef] using hd5 x hxd5
  have hWnn : ∀ z : ℝ, 0 ≤ ∑ j ∈ Finset.range (Jc x HasBc.val),
      Grho x ((Cm : ℕ) : ℝ) ((2 : ℝ) ^ j * z) :=
    fun z => Finset.sum_nonneg (fun j _ => Grho_nonneg x hCmR _)
  -- the pointwise `§8.3` main-term bound
  have hmainb : ∀ z ∈ Set.Icc (zc x HasBc.val) (Real.exp 1 * zc x HasBc.val),
      ∀ y ∈ Set.Icc (Yc x HasBc.val) (Real.exp 1 * Yc x HasBc.val),
      |s3MainPlus lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) Cm| ≤ Mplus := by
    intro z hz y hy
    have h1 := hmainpt x hxmp hcond lam Cs hSieve z hz y hy
    simpa [Mplus, hLdef, hCmdef] using h1
  -- the pointwise bound `|∫_Y S₃(z)/y| ≤ Ψ(z)`
  have hFpsi := s3f_F_le_psi x lam Cm Mplus hMpnn hmainb hCm1 hCmpos hCmdef hzc1 hzc2 hzcg1
    hzcpos hDz hYcpos hYle (fun ν hν => hSieve.2.1 ν hν) hSieve.2.2.2.1
  -- the `y`-integral of `|S₃⁻|` is dominated by the dyadic `Grho`-sum
  have hWle : ∀ z ∈ Set.Icc (zc x HasBc.val) (Real.exp 1 * zc x HasBc.val),
      (∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val),
        |S3minusC atilc lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) ((Cm : ℕ) : ℝ)| / y)
      ≤ ∑ j ∈ Finset.range (Jc x HasBc.val), Grho x ((Cm : ℕ) : ℝ) ((2 : ℝ) ^ j * z) := by
    intro z hz
    refine s3f_integral_le_const_div (Yc x HasBc.val) _ hYcpos ?_ ?_ ?_
    · have h0 := intervalIntegrable_abs_step_div HasBc.val x hYcpos lam
        (fun ℓ => S3minusInnerC atilc x ℓ z (sc x HasBc.val * z) ((Cm : ℕ) : ℝ))
      have hfun : (fun y : ℝ => |S3step x lam
            (fun ℓ => S3minusInnerC atilc x ℓ z (sc x HasBc.val * z) ((Cm : ℕ) : ℝ))
            (sc x HasBc.val * y)| / y)
          = fun y : ℝ => |S3minusC atilc lam x z (sc x HasBc.val * y)
              (sc x HasBc.val * z) ((Cm : ℕ) : ℝ)| / y := by
        funext y; rw [S3minusC_eq_S3step]
      rwa [hfun] at h0
    · exact hWnn z
    · intro y hy
      have hy0 : 0 < y := lt_of_lt_of_le hYcpos hy.1
      exact div_le_div_of_nonneg_right (hdyadx z hz y) hy0.le
  -- the weight `Ψ` and the single `z₁ ∈ [zc, e·zc]` attaining its average
  set Ψ : ℝ → ℝ := fun z => Mplus
      + (∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val),
          |s3RemPlus lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) Cm| / y)
      + (∑ j ∈ Finset.range (Jc x HasBc.val), Grho x ((Cm : ℕ) : ℝ) ((2 : ℝ) ^ j * z)) with hΨdef
  have hΨmeas : Measurable Ψ := by
    rw [hΨdef]
    exact (measurable_const.add (s3f_rem_meas x lam Cm hYcpos)).add hWmeas'
  have hΨnn : ∀ z : ℝ, 0 ≤ Ψ z := by
    intro z
    rw [hΨdef]
    refine add_nonneg (add_nonneg hMpnn ?_) (hWnn z)
    exact intervalIntegral.integral_nonneg hYle (fun y hy =>
      div_nonneg (abs_nonneg _) (le_of_lt (lt_of_lt_of_le hYcpos hy.1)))
  have hΨbdd : ∃ C : ℝ, ∀ z ∈ Set.Icc (zc x HasBc.val) (Real.exp 1 * zc x HasBc.val), Ψ z ≤ C := by
    obtain ⟨V, hV⟩ := hWbdd'
    refine ⟨Mplus + (4 * AcountAtilC x * (((x : ℝ) ^ 3) + 1)
      * (((x : ℝ) / (Cm : ℝ)) + 1) + 1) + V, ?_⟩
    intro z hz
    rw [hΨdef]
    have h1 := s3f_rem_yint_le x lam Cm hSieve.2.2.2.1 hYcpos z
      (le_of_lt (lt_of_lt_of_le hzcpos hz.1))
    linarith [h1, hV z hz]
  obtain ⟨z₁, hz₁mem, hz₁le⟩ :=
    exists_z1_le_of_measurable_zavg (Z := zc x HasBc.val) hzcpos hΨmeas hΨnn hΨbdd
  -- the value of the `Ψ`-average
  have hintRz : IntervalIntegrable (fun z : ℝ =>
      (∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val),
        |s3RemPlus lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) Cm| / y) / z)
      volume (zc x HasBc.val) (Real.exp 1 * zc x HasBc.val) :=
    s3f_rem_zint_int x lam Cm hSieve.2.2.2.1 hYcpos hzcpos
  have hIntMp : IntervalIntegrable (fun z : ℝ => Mplus / z) volume (zc x HasBc.val)
      (Real.exp 1 * zc x HasBc.val) :=
    intervalIntegrable_div_Ioc (G := fun _ : ℝ => Mplus) measurable_const hzcpos hzle
      Mplus (fun u _ => le_of_eq (abs_of_nonneg hMpnn))
  have hPsiInt : (∫ z in zc x HasBc.val..(Real.exp 1 * zc x HasBc.val), Ψ z / z)
      = (∫ z in zc x HasBc.val..(Real.exp 1 * zc x HasBc.val), Mplus / z)
        + (∫ z in zc x HasBc.val..(Real.exp 1 * zc x HasBc.val),
            (∑ j ∈ Finset.range (Jc x HasBc.val),
              Grho x ((Cm : ℕ) : ℝ) ((2 : ℝ) ^ j * z)) / z)
        + (∫ z in zc x HasBc.val..(Real.exp 1 * zc x HasBc.val),
            (∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val),
              |s3RemPlus lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) Cm| / y) / z) := by
    rw [show (fun z : ℝ => Ψ z / z)
        = fun z => Mplus / z + ((∑ j ∈ Finset.range (Jc x HasBc.val),
              Grho x ((Cm : ℕ) : ℝ) ((2 : ℝ) ^ j * z)) / z
            + (∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val),
              |s3RemPlus lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) Cm| / y) / z) by
      funext z; rw [hΨdef]; ring]
    rw [intervalIntegral.integral_add hIntMp (hWint'.add hintRz)]
    rw [intervalIntegral.integral_add hWint' hintRz]
    ring
  have hCval : (∫ z in zc x HasBc.val..(Real.exp 1 * zc x HasBc.val), Mplus / z)
      = Mplus := intervalIntegral_const_div_exp Mplus (zc x HasBc.val) hzcpos
  have hRzle : (∫ z in zc x HasBc.val..(Real.exp 1 * zc x HasBc.val),
      (∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val),
        |s3RemPlus lam x z (sc x HasBc.val * y) (sc x HasBc.val * z) Cm| / y) / z) ≤ Crz := by
    rw [hCrzdef, hLdef, hCmdef]
    exact hremz x hxrz hcond hsc2x lam Cs hSieve
  have hPsibound : (∫ z in zc x HasBc.val..(Real.exp 1 * zc x HasBc.val), Ψ z / z)
      ≤ Mplus + (Jc x HasBc.val : ℝ) * (Krho * AcountAtilC x * L ^ (-(4 : ℤ))) + Crz := by
    rw [hPsiInt, hCval]; linarith [hWzavg', hRzle]
  -- hence the `hS3` input of the deviation statement
  have hS3z1 : |S3avgFix atilc lam x z₁ (sc x HasBc.val) (Yc x HasBc.val)|
      ≤ Mplus + (Jc x HasBc.val : ℝ) * (Krho * AcountAtilC x * L ^ (-(4 : ℤ))) + Crz := by
    refine le_trans ?_ hPsibound
    calc |S3avgFix atilc lam x z₁ (sc x HasBc.val) (Yc x HasBc.val)|
        = |∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val),
            Submission.ASP.S3 atilc lam x z₁ (sc x HasBc.val * y) (sc x HasBc.val * z₁) / y| := rfl
      _ ≤ ∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val),
            |Submission.ASP.S3 atilc lam x z₁ (sc x HasBc.val * y) (sc x HasBc.val * z₁)| / y := by
          refine le_trans (intervalIntegral.abs_integral_le_integral_abs (f := fun y : ℝ =>
            Submission.ASP.S3 atilc lam x z₁ (sc x HasBc.val * y) (sc x HasBc.val * z₁) / y) hYle) ?_
          refine le_of_eq (intervalIntegral.integral_congr (fun y hy => ?_))
          have hy0 : (0 : ℝ) ≤ y := by
            have h1 : Yc x HasBc.val ≤ y := by
              have h2 : y ∈ Set.Icc (min (Yc x HasBc.val) (Real.exp 1 * Yc x HasBc.val))
                  (max (Yc x HasBc.val) (Real.exp 1 * Yc x HasBc.val)) := hy
              rw [min_eq_left hYle] at h2
              exact h2.1
            exact le_trans hYcpos.le h1
          rw [abs_div, abs_of_nonneg hy0]
      _ ≤ Ψ z₁ := by
          have h1 := hFpsi z₁ hz₁mem
          have h2 := hWle z₁ hz₁mem
          rw [hΨdef]
          linarith [h1, h2]
      _ ≤ ∫ z in zc x HasBc.val..(Real.exp 1 * zc x HasBc.val), Ψ z / z := hz₁le
  -- the `§4–§7` bounds in the `hPhi` shape
  have hPhiZ : ∀ z ∈ Set.Icc (zc x HasBc.val) (Real.exp 1 * zc x HasBc.val),
      |(∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val),
          (Submission.ASP.Tsum atilc lam (x : ℝ) y - Submission.ASP.Tsum2 atilc lam (x : ℝ) y z
            + Submission.ASP.S2 atilc lam x y z (sc x HasBc.val * y)
            + Submission.ASP.S1 atilc lam x (sc x HasBc.val * y) (sc x HasBc.val * z)) / y)
        - H * AcountAtilC x| ≤ Kφ * AcountAtilC x * (LL / L) := by
    intro z hz
    have h1 := hphi x hxφ hcond lam Cs hSieve hCs z hz
    simpa [hLdef, hLLdef] using h1
  have hdev := S3avgFix_le_of_zavg (a := atilc) (lam := lam) (N := x)
    (Y := Yc x HasBc.val) (Z := zc x HasBc.val) (s := sc x HasBc.val)
    (E := Kφ * AcountAtilC x * (LL / L))
    (E5 := Mplus + (Jc x HasBc.val : ℝ) * (Krho * AcountAtilC x * L ^ (-(4 : ℤ))) + Crz)
    (H := H) (z₁ := z₁)
    (by omega) hYcpos (by rw [sc]; exact one_le_pow₀ (by norm_num)) hzcpos hz₁mem hPhiZ hS3z1
  have hdelx : S3delSum atilc lam x (zc x HasBc.val) ≤ Kd * AcountAtilC x * L ^ (-(1 : ℤ)) := by
    rw [hLdef]
    exact hdel x hxd lam hSieve.2.2.2.1
  -- the two forms of the fixed-`z` integral agree
  change |S3avgFix atilc lam x (zc x HasBc.val) (sc x HasBc.val) (Yc x HasBc.val)|
      ≤ (Kp + Kr + Krho + Kd + 2 * Kφ + 1) * AcountAtilC x
          * (Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ))
  have hbd : |S3avgFix atilc lam x (zc x HasBc.val) (sc x HasBc.val) (Yc x HasBc.val)|
      ≤ Mplus + (Jc x HasBc.val : ℝ) * (Krho * AcountAtilC x * L ^ (-(4 : ℤ))) + Crz
        + 2 * (Kφ * AcountAtilC x * (LL / L))
        + Kd * AcountAtilC x * L ^ (-(1 : ℤ)) := by
    linarith [hdev, hdelx]
  -- the `ρ`-rate: `Jc ≤ (log x)²`, so `Jc·Kρ·Ã·L^{-4} ≤ Kρ·Ã·L^{-2}`
  have hLp : 0 < L := by rw [hLdef]; linarith
  have hzc256 : (256 : ℝ) ≤ zc x HasBc.val := by
    have h : (256 : ℝ) ≤ (⌊Yc x HasBc.val⌋₊ : ℝ) := by exact_mod_cast hY256
    simpa [zc, Zc] using h
  have hCge3 : (3 : ℝ) ≤ ((⌊(zc x HasBc.val) ^ (1 - etac)⌋₊ : ℕ) : ℝ) := by
    have h1 : (16 : ℝ) ≤ (zc x HasBc.val) ^ (1 - etac) := by
      have h2 : (zc x HasBc.val) ^ ((1 : ℝ) / 2) ≤ (zc x HasBc.val) ^ (1 - etac) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num [etac])
      have h3 : (16 : ℝ) ≤ (zc x HasBc.val) ^ ((1 : ℝ) / 2) := by
        rw [← Real.sqrt_eq_rpow]
        calc (16 : ℝ) = Real.sqrt 256 := by
              rw [show (256 : ℝ) = 16 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
          _ ≤ Real.sqrt (zc x HasBc.val) := Real.sqrt_le_sqrt hzc256
      linarith
    have h4 : 16 ≤ ⌊(zc x HasBc.val) ^ (1 - etac)⌋₊ :=
      (Nat.le_floor_iff (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ zc x HasBc.val) _)).mpr h1
    have h5 : (16 : ℝ) ≤ ((⌊(zc x HasBc.val) ^ (1 - etac)⌋₊ : ℕ) : ℝ) := by exact_mod_cast h4
    linarith
  have hlogC1 : (1 : ℝ) ≤ Real.log (((⌊(zc x HasBc.val) ^ (1 - etac)⌋₊ : ℕ) : ℝ)) := by
    rw [Real.le_log_iff_exp_le (by linarith : (0 : ℝ) < ((⌊(zc x HasBc.val) ^ (1 - etac)⌋₊ : ℕ) : ℝ))]
    exact le_trans Real.exp_one_lt_three.le hCge3
  have hJC' : (Jc x HasBc.val : ℝ) ≤ L ^ 2 := by
    obtain ⟨hJC, -⟩ := hJ x hxJ
    have h1 : (Jc x HasBc.val : ℝ) * 1
        ≤ (Jc x HasBc.val : ℝ) * Real.log (((⌊(zc x HasBc.val) ^ (1 - etac)⌋₊ : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hlogC1 (Nat.cast_nonneg _)
    have h2 : (Jc x HasBc.val : ℝ) * Real.log (((⌊(zc x HasBc.val) ^ (1 - etac)⌋₊ : ℕ) : ℝ))
        ≤ L * L := by simpa [hLdef] using hJC
    have h3 : L ^ 2 = L * L := by ring
    linarith [h1, h2, h3]
  have hRhole : (Jc x HasBc.val : ℝ) * (Krho * AcountAtilC x * L ^ (-(4 : ℤ)))
      ≤ Krho * AcountAtilC x * L ^ (-(2 : ℤ)) := by
    have hzpow : (L : ℝ) ^ 2 * L ^ (-(4 : ℤ)) = L ^ (-(2 : ℤ)) := by
      rw [show (L : ℝ) ^ 2 = L ^ (2 : ℤ) from (zpow_natCast L 2).symm]
      rw [← zpow_add₀ (ne_of_gt hLp)]
      norm_num
    have hEρnn : 0 ≤ Krho * AcountAtilC x * L ^ (-(4 : ℤ)) :=
      mul_nonneg (mul_nonneg hKrho hAnn) (by positivity)
    calc (Jc x HasBc.val : ℝ) * (Krho * AcountAtilC x * L ^ (-(4 : ℤ)))
        ≤ L ^ 2 * (Krho * AcountAtilC x * L ^ (-(4 : ℤ))) :=
          mul_le_mul_of_nonneg_right hJC' hEρnn
      _ = (L ^ 2 * L ^ (-(4 : ℤ))) * (Krho * AcountAtilC x) := by ring
      _ = L ^ (-(2 : ℤ)) * (Krho * AcountAtilC x) := by rw [hzpow]
      _ = Krho * AcountAtilC x * L ^ (-(2 : ℤ)) := by ring
  refine le_trans hbd ?_
  rw [hMpdef, hCrzdef]
  have harith := s3f_final_arith (A := AcountAtilC x) (L := L) (LL := LL)
    (Kp := Kp) (Kr := Kr) (Km := Krho) (Kd := Kd) (Kφ := Kφ)
    hAnn (by rw [hLdef]; linarith) hLL1' hKppos.le hKrpos.le hKrho hKdpos.le hKφpos.le
  linarith [harith, hRhole]
end

end Work.FIPiChain
