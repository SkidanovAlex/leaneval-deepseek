import Mathlib
import Submission.Work.FIPiChain.HasB
import Submission.Work.FIPiChain.Chain.S3phiBDefs
import Submission.Work.FIChain.Defs
import Submission.Work.FIChain.scale_factsC
import Submission.Work.FIChain.chainRangeFactsC
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
import Submission.Work.FIChain.rhoWindowC_param
import Submission.Work.FITop.RhoWindowCProp41
import Submission.Work.FIChain.assemblyC
import Submission.Work.FIFinal.abs_smAvg_S2_int_le

set_option maxHeartbeats 1600000

open Work.FIChain

namespace Work.FIPiChain

variable [HasBc]

open Finset Filter
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 0. What this file contains, and why the requested statement needs a hypothesis

The requested lemma `Work.FIChain.S3phiS2_Bstar` (below, statement unchanged) asks for the `S₂`
summand of the `§4–§7` estimate `Work.FIChain.S3phi_Bstar_v2` at the pinned scale
`HasBc.val = 2^31 + 2`, quantified over `(lam, C_sieve)` subject to `SieveInput` *alone*, with no
hypothesis on the bilinear form.

Its own route (the docstring of the request) is `Submission.ASP.abs_smAvg_S2_le`, and that
theorem has the hypothesis

`Submission.ASP.BprimeWindow atilc x wc E (Yc x HasBc.val/Deltac x) (sc x HasBc.val·(e·Yc x HasBc.val))`,
`E = K·Ã(x)·(log x)^{-4}`   —   the companion's hypothesis `(B′)` of §7.

In this workspace the `(B′)`-window for `atilc`/`wc` is available *only* from the frozen contract
`Work.FIChain.Prop41Stmt` (`Work.FIChain.PinBp.bprimeWindow_at_Bstar`,
`Work.FIChain.windows_at_Bstar`; every other producer — `Work.FITop.BprimeWindowPow`,
`BprimeWindowDelta1`, `BprimeWindowOfProp41`, `Work.FIChain.BprimeWindowIntegrated` — likewise
takes `Prop41Statement`/`Prop41StatementPiBig` as a hypothesis, and no theorem in the workspace
concludes `Prop41Statement` unconditionally).  `SieveInput` says nothing about the bilinear form
(it only fixes `λ 1 = 1`, the support `[1, Δ]`, `|λ| ≤ 1`, the squarefree support, the two
positivity conjuncts and the sieve inequality; `Work.FIChain.SieveInput_lamδ_iff` shows it is
satisfied by `λ = δ₁` for every level `Δ ≥ 1`).

The lemma `S3phiS2_Bstar_of_prop41` below is the same conclusion with that missing hypothesis
restored.  It is proved by exactly the route of the request: `abs_smAvg_S2_le` with
`E := Kbp·Ã(x)·(log x)^{-4}` from `PinBp.bprimeWindow_at_Bstar h (1/64) …`, and the `E4`
rate arithmetic `Work.FIChain.E4_rate_aux` of `Work.FIChain.assemblyC` (with `Jc x HasBc.val ≤ log x`
and `1 + log(Deltac x) ≤ 2 log x`, both proved here).  Hence the *only* defect of the requested
statement is the missing hypothesis `h : Prop41Stmt`. -/


/-- **The `S₂`-summand of the `§4–§7` estimate from the `(B′)`-window alone.**  This is the
statement `Work.FIChain.S3phiS2_Bstar` with the hypothesis its own route uses — the companion's
`(B′)`-window `Submission.ASP.BprimeWindow atilc x wc E (Yc x HasBc.val/Deltac x) (sc x HasBc.val·(e·Yc x HasBc.val))`
with `E = Kbp·Ã(x)·(log x)^{-4}` — put back as a parameter, in the form in which
`Work.FIChain.PinBp.bprimeWindow_at_Bstar` / `Work.FIChain.windows_at_Bstar` deliver it.  The
conclusion is exactly that of the requested lemma, with `K := 4·Kbp`; the proof is verbatim the
route of the request (`abs_smAvg_S2_le` plus the `E4` rate arithmetic). -/
theorem S3phiS2_Bstar_of_window (Kbp : ℝ) (hKbp : 0 < Kbp) (xbp : ℕ)
    (hBwin : ∀ x : ℕ, xbp ≤ x → Work.FIChain.BprimeWindowInt atilc x wc
      (Kbp * AcountAtilC x * (Real.log (x : ℝ)) ^ (-(4 : ℤ)))
      (Yc x HasBc.val / (Deltac x : ℝ)) (sc x HasBc.val * (Real.exp 1 * Yc x HasBc.val))) :
    ∃ K : ℝ, ∃ x₀ : ℕ, 0 < K ∧ ∀ x : ℕ, x₀ ≤ x → s3phiCond x →
      ∀ lam : ℕ → ℝ, ∀ C_sieve : ℝ,
        SieveInput Submission.ASP.FIgtil (Deltac x) lam C_sieve →
        ∀ z ∈ s3phiZwin x,
          (∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val), |s3phiS2 x lam y z| / y)
            ≤ K * AcountAtilC x * s3phiRate x := by
  -- the eventual facts consumed by `abs_smAvg_S2_le` and by the rate arithmetic
  have hfacts : ∀ᶠ x : ℕ in Filter.atTop,
      0 < Yc x HasBc.val ∧ 1 ≤ Deltac x ∧ (1 : ℝ) ≤ Real.log (x : ℝ) ∧
      (4 : ℝ) ≤ Real.log (x : ℝ) ∧ (1 : ℝ) ≤ Real.log (Real.log (x : ℝ)) ∧
      (Jc x HasBc.val : ℝ) ≤ Real.log (x : ℝ) ∧
      1 + Real.log (Deltac x : ℝ) ≤ 2 * Real.log (x : ℝ) := by
    filter_upwards [scale_factsC HasBc.val (by have := HasBc.ge_two; linarith),
      Work.FITop.FI_ev_Delta1_le_two_Lam1, Work.FITop.FI_ev_log_ge_nat 4,
      Work.FITop.FI_ev_ge_one] with x hsc hD2 hlog hx1
    have hxpos : (0 : ℝ) < (x : ℝ) := Work.FITop.FI_cast_pos hx1
    have hxge1 : (1 : ℝ) ≤ (x : ℝ) := Work.FITop.FI_cast_one_le hx1
    have hLpos : 0 < Real.log (x : ℝ) := by linarith
    have hlog1 : (1 : ℝ) ≤ Real.log (x : ℝ) := by linarith
    have hloglog1 : (1 : ℝ) ≤ Real.log (Real.log (x : ℝ)) := by
      have h4 : (1 : ℝ) < Real.log (x : ℝ) := by linarith
      calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ ≤ Real.log (Real.log (x : ℝ)) :=
            Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
    have hYpos : 0 < Yc x HasBc.val := by
      rw [Yc]
      exact div_pos (Real.sqrt_pos.mpr hxpos)
        (mul_pos (pow_pos (by norm_num) _) (Real.rpow_pos_of_pos hLpos _))
    have hDelta1 : 1 ≤ Deltac x := by
      have h1 : (1 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 100) := Real.one_le_rpow hxge1 (by norm_num)
      have h2 : (x : ℝ) ^ ((1 : ℝ) / 100) ≤ (Deltac x : ℝ) := by
        simpa [Deltac, Work.FITop.Delta1, Work.FITop.Lam1] using
          Nat.le_ceil ((x : ℝ) ^ ((1 : ℝ) / 100))
      exact_mod_cast (le_trans h1 h2)
    -- `Jc x HasBc.val ≤ log x`
    have hlog2half : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have := Real.log_two_gt_d9; linarith
    have hu_le : (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / (2 * (Real.log (x : ℝ)) ^ (HasBc.val + 2))
        ≤ (x : ℝ) ^ ((1 : ℝ) / 4) := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (Real.log (x : ℝ)) ^ (HasBc.val + 2))]
      have h2 : (1 : ℝ) ≤ 2 * (Real.log (x : ℝ)) ^ (HasBc.val + 2) := by
        have h3 : (1 : ℝ) ≤ (Real.log (x : ℝ)) ^ (HasBc.val + 2) :=
          Real.one_le_rpow hlog1 (by have := HasBc.ge_two; linarith)
        linarith
      calc (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac)
          = (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) * 1 := by ring
        _ ≤ (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) * (2 * (Real.log (x : ℝ)) ^ (HasBc.val + 2)) :=
            mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hxpos.le _)
        _ ≤ (x : ℝ) ^ ((1 : ℝ) / 4) * (2 * (Real.log (x : ℝ)) ^ (HasBc.val + 2)) :=
            mul_le_mul_of_nonneg_right
              (Real.rpow_le_rpow_of_exponent_le hxge1 (by norm_num [etac])) (by positivity)
    have hu_pos : 0 < (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac)
        / (2 * (Real.log (x : ℝ)) ^ (HasBc.val + 2)) :=
      div_pos (Real.rpow_pos_of_pos hxpos _) (by positivity)
    have hlogu : Real.log ((x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac)
        / (2 * (Real.log (x : ℝ)) ^ (HasBc.val + 2))) ≤ Real.log (x : ℝ) / 4 := by
      calc Real.log ((x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac)
            / (2 * (Real.log (x : ℝ)) ^ (HasBc.val + 2)))
          ≤ Real.log ((x : ℝ) ^ ((1 : ℝ) / 4)) := Real.log_le_log hu_pos hu_le
        _ = Real.log (x : ℝ) / 4 := by rw [Real.log_rpow hxpos]; ring
    have hJle : (Jc x HasBc.val : ℝ) ≤ Real.log (x : ℝ) := by
      have ht_le : Real.log ((x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac)
            / (2 * (Real.log (x : ℝ)) ^ (HasBc.val + 2))) / Real.log 2 ≤ Real.log (x : ℝ) / 2 := by
        rw [div_le_iff₀ (by linarith : (0 : ℝ) < Real.log 2)]
        nlinarith only [hlogu, hlog2half, hLpos]
      rw [Jc]
      have h1 : (⌈Real.log ((x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac)
            / (2 * (Real.log (x : ℝ)) ^ (HasBc.val + 2))) / Real.log 2⌉₊ : ℝ)
          ≤ (⌈Real.log (x : ℝ) / 2⌉₊ : ℝ) := by
        exact_mod_cast Nat.ceil_mono ht_le
      have h2 : (⌈Real.log (x : ℝ) / 2⌉₊ : ℝ) < Real.log (x : ℝ) / 2 + 1 :=
        Nat.ceil_lt_add_one (by linarith)
      linarith
    -- `1 + log(Deltac x) ≤ 2 log x`
    have hlogD : 1 + Real.log (Deltac x : ℝ) ≤ 2 * Real.log (x : ℝ) := by
      have hDpos : 0 < (Deltac x : ℝ) := by exact_mod_cast (by omega : 0 < Deltac x)
      have h1 : Real.log (Deltac x : ℝ) ≤ Real.log (2 * Work.FITop.Lam1 x) :=
        Real.log_le_log hDpos hD2
      have hLam1pos : 0 < Work.FITop.Lam1 x := by
        rw [Work.FITop.Lam1]; exact Real.rpow_pos_of_pos hxpos _
      have h2 : Real.log (2 * Work.FITop.Lam1 x)
          = Real.log 2 + Real.log (Work.FITop.Lam1 x) :=
        Real.log_mul (by norm_num) (ne_of_gt hLam1pos)
      have h3 : Real.log (Work.FITop.Lam1 x) = Real.log (x : ℝ) / 100 := by
        rw [Work.FITop.Lam1, Real.log_rpow hxpos]; ring
      have h4 : Real.log 2 ≤ Real.log (x : ℝ) / 4 := by
        have := Real.log_two_lt_d9; linarith
      have h5 : Real.log (Deltac x : ℝ) ≤ Real.log (x : ℝ) := by linarith
      linarith
    exact ⟨hYpos, hDelta1, hlog1, hlog, hloglog1, hJle, hlogD⟩
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.mp hfacts
  refine ⟨4 * Kbp, max (max xbp X) 16, by positivity, ?_⟩
  intro x hx hcond lam Cs hSI z hz
  have hxbp : xbp ≤ x := by omega
  have hXx : X ≤ x := by omega
  have hx1 : 1 ≤ x := by omega
  obtain ⟨hYpos, hDelta1, hlog1, hlog4, hloglog1, hJle, hlogD⟩ := hX x hXx
  have hxpos : (0 : ℝ) < (x : ℝ) := Work.FITop.FI_cast_pos hx1
  have hA0 : 0 ≤ AcountAtilC x := Work.FITop.AcountAtil_nonneg' x
  have hlogpos : 0 < Real.log (x : ℝ) := by linarith
  have hp4 : (0 : ℝ) ≤ (Real.log (x : ℝ)) ^ (-(4 : ℤ)) := by
    rw [zpow_neg]; exact inv_nonneg.mpr (pow_nonneg hlogpos.le 4)
  have hΔlog0 : (0 : ℝ) ≤ Real.log (Deltac x : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hDelta1)
  -- the `(B′)`-window at `x`
  have hBw := hBwin x hxbp
  -- the `λ`-inputs, both conjuncts of `SieveInput`
  have hsupp : ∀ ν, Deltac x < ν → lam ν = 0 := hSI.2.1
  have hle1 : ∀ ν, |lam ν| ≤ 1 := hSI.2.2.2.1
  -- §7, (7.2): the smoothed bound for `S₂`
  have hS2 := Work.FIFinal.abs_smAvg_S2_int_le (a := atilc) (lam := lam) (N := x) (w := wc)
    (s := sc x HasBc.val) (E := Kbp * AcountAtilC x * (Real.log (x : ℝ)) ^ (-(4 : ℤ)))
    (Y := Yc x HasBc.val) (J := Jc x HasBc.val) (Δ := Deltac x) (z := z)
    rfl hYpos hDelta1 (fun ℓ => by simp only [wc, Work.FITop.w0]; positivity)
    (mul_nonneg (mul_nonneg hKbp.le hA0) hp4) hx1 (fun ℓ _ => le_of_eq rfl)
    hsupp hle1 (fun n hn => atilc_eq_zero_of_not_sqfree hn) hBw
  -- the `E4` rate arithmetic
  have hrate := E4_rate_aux (LN := Real.log (x : ℝ)) (LLN := Real.log (Real.log (x : ℝ)))
    (J := (Jc x HasBc.val : ℝ)) (Kbp := Kbp) (Abar := AcountAtilC x)
    (LΔ := Real.log (Deltac x : ℝ)) hlog1 hloglog1 (Nat.cast_nonneg _) hJle hΔlog0 hlogD
    hA0 hKbp.le
  have key : (∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val), |s3phiS2 x lam y z| / y)
      ≤ (4 * Kbp) * (AcountAtilC x * (Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ))) := by
    have heq : (∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val), |s3phiS2 x lam y z| / y)
        = ∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val),
            |Submission.ASP.S2 atilc lam x y z (sc x HasBc.val * y)| / y := by
      refine intervalIntegral.integral_congr (fun y _ => ?_)
      simp only [s3phiS2]
    rw [heq]
    exact le_trans hS2 hrate
  calc (∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val), |s3phiS2 x lam y z| / y)
      ≤ (4 * Kbp) * (AcountAtilC x * (Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ))) := key
    _ = (4 * Kbp) * AcountAtilC x * s3phiRate x := by rw [s3phiRate]; ring

end

end Work.FIPiChain
