import Mathlib
import Submission.Work.FIPiChain.HasB
import Submission.Work.FIPiChain.Chain.S3phiBDefs
import Submission.Work.FIChain.Defs
import Submission.Work.FIChain.scale_factsC
import Submission.Work.FIChain.chainRangeFactsC
import Submission.Work.FIPiChain.Chain.chainRangeWideB
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
import Submission.Work.FIChain.Tsum2_uniformAll
import Submission.Work.FIChain.LocalS4
import Submission.Work.FIChain.LocalS5c
import Submission.Work.FIChain.remainder_all
import Submission.Work.FIChain.FIgtil_tau_div_sum_le
import Submission.Work.FIChain.assemblyC

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

open Work.FIChain

namespace Work.FIPiChain

variable [HasBc]

open Finset Filter
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Elementary arithmetic for the `T₂`-summand

The three lemmas below isolate the pieces of the `z`-uniform `T₂` estimate that are pure
arithmetic: the rate comparison, the log-factor bound at the corrected scale, and the
`B`-input comparison replacing `P = ⌊z⌋₊` by the uniform top `Ze = ⌊e·Yc⌋₊`. -/

/-- Rate arithmetic for the `T₂`-summand, uniform over the `z`-window (`hE2rate` of
`Work.FIChain.assemblyC`, with `logZn ≤ logM` and `hlogfac` supplied). -/
lemma t2RateAux {LN LLN CB1 logM logZn logDP : ℝ}
    (hLN : 1 ≤ LN) (hLLN : 1 ≤ LLN) (hCB1pos : 0 < CB1)
    (hMz : logZn ≤ logM) (hz4 : LN / 4 ≤ logZn)
    (hlogfac : 1 + logDP ≤ 3 * LN) :
    CB1 * LN ^ 3 * (1 + logDP) * logM ^ (-(6 : ℤ)) + LN ^ (-(2 : ℤ))
      ≤ (16384 * CB1 + 1) * (LLN / LN) := by
  have hLNp : 0 < LN := lt_of_lt_of_le zero_lt_one hLN
  have hz4M : LN / 4 ≤ logM := le_trans hz4 hMz
  have hMpos : 0 < logM := lt_of_lt_of_le (by linarith : (0 : ℝ) < LN / 4) hz4M
  have hM0p6 : logM ^ (-(6 : ℤ)) = ((logM) ^ 6)⁻¹ := by simp [zpow_neg]
  have hpow6 : ((logM) ^ 6)⁻¹ ≤ 4096 * (LN ^ 6)⁻¹ := by
    rw [inv_eq_one_div, inv_eq_one_div]
    have hkey : (4096 : ℝ) * (1 / LN ^ 6) = 4096 / LN ^ 6 := by ring
    rw [hkey, div_le_div_iff₀ (pow_pos hMpos 6) (pow_pos hLNp 6)]
    have h := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ LN / 4) hz4M 6
    rw [div_pow] at h
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < (4 : ℝ) ^ 6)] at h
    linarith [h]
  have hkey4 : LN ^ 4 * (LN ^ 6)⁻¹ = (LN ^ 2)⁻¹ := by
    rw [inv_eq_one_div, inv_eq_one_div]
    rw [show LN ^ 4 * (1 / LN ^ 6) = 1 / LN ^ 2 by
      rw [mul_one_div, div_eq_div_iff (pow_ne_zero 6 (ne_of_gt hLNp)) (pow_ne_zero 2 (ne_of_gt hLNp))]
      ring]
  have h1 : CB1 * LN ^ 3 * (1 + logDP) * logM ^ (-(6 : ℤ)) ≤ 12288 * CB1 * (LN ^ 2)⁻¹ := by
    rw [hM0p6]
    have hstep : CB1 * LN ^ 3 * (1 + logDP) * ((logM) ^ 6)⁻¹
        ≤ CB1 * LN ^ 3 * (3 * LN) * (4096 * (LN ^ 6)⁻¹) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hlogfac (by positivity)) hpow6 (by positivity)
        (by positivity)
    refine le_trans hstep (le_of_eq ?_)
    calc CB1 * LN ^ 3 * (3 * LN) * (4096 * (LN ^ 6)⁻¹)
        = 4096 * 3 * CB1 * (LN ^ 4 * (LN ^ 6)⁻¹) := by ring
      _ = 4096 * 3 * CB1 * (LN ^ 2)⁻¹ := by rw [hkey4]
      _ = 12288 * CB1 * (LN ^ 2)⁻¹ := by ring
  have h2 : 12288 * CB1 * (LN ^ 2)⁻¹ ≤ 16384 * CB1 * (LLN / LN) := by
    have h := zpow_two_le_div hLN hLLN
    have hLp2 : LN ^ (-(2 : ℤ)) = (LN ^ 2)⁻¹ := by simp [zpow_neg]
    rw [hLp2] at h
    refine le_trans (mul_le_mul_of_nonneg_left h (by positivity)) ?_
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    refine mul_le_mul_of_nonneg_right ?_ hCB1pos.le
    norm_num
  have h3 : (LN ^ 2)⁻¹ ≤ LLN / LN := by
    have h := zpow_two_le_div hLN hLLN
    have hLp2 : LN ^ (-(2 : ℤ)) = (LN ^ 2)⁻¹ := by simp [zpow_neg]
    rwa [hLp2] at h
  have h4 : (16384 : ℝ) * CB1 * (LLN / LN) + LLN / LN ≤ (16384 * CB1 + 1) * (LLN / LN) := by
    rw [show (16384 : ℝ) * CB1 * (LLN / LN) + LLN / LN
        = (16384 * CB1 + 1) * (LLN / LN) by ring]
  have h5 : LN ^ (-(2 : ℤ)) = (LN ^ 2)⁻¹ := by simp [zpow_neg]
  rw [h5]
  linarith only [h1, h2, h3, h4]

/-- `1 + log(Δ·Z + 2) ≤ 3 log x` at the corrected scale, using `Δ·Z ≤ Dc x ≤ x`. -/
lemma t2LogFacAux {x Ze : ℕ} (hx : 3 ≤ x) (hD : Deltac x * Ze ≤ Dc x) :
    1 + Real.log ((Deltac x : ℝ) * (Ze : ℝ) + 2) ≤ 3 * Real.log (x : ℝ) := by
  have hxR : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  have hx2 : (2 : ℝ) ≤ (x : ℝ) := by linarith
  have hlog1 : (1 : ℝ) ≤ Real.log (x : ℝ) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_three, hxR])
  have hDc_le : (Dc x : ℝ) ≤ (x : ℝ) := by
    have h : Dc x ≤ x := by
      rw [Dc, Work.FITop.Dcut]
      exact Submission.Rcut_le_self x
    exact_mod_cast h
  have hDcast : (Deltac x : ℝ) * (Ze : ℝ) ≤ (x : ℝ) := by
    have h := hD
    have h' : ((Deltac x * Ze : ℕ) : ℝ) ≤ (Dc x : ℝ) := by exact_mod_cast h
    rw [Nat.cast_mul] at h'
    linarith [h', hDc_le]
  have hargpos : 0 < (Deltac x : ℝ) * (Ze : ℝ) + 2 := by positivity
  have harg_le : (Deltac x : ℝ) * (Ze : ℝ) + 2 ≤ 2 * (x : ℝ) := by linarith
  have hlog_le : Real.log ((Deltac x : ℝ) * (Ze : ℝ) + 2) ≤ Real.log (2 * (x : ℝ)) :=
    Real.log_le_log hargpos harg_le
  rw [Real.log_mul (by norm_num) (ne_of_gt hxpos)] at hlog_le
  have hlog2 : Real.log 2 ≤ Real.log (x : ℝ) := Real.log_le_log (by norm_num) hx2
  linarith

/-- The `B`-input comparison for the `T₂`-summand: replacing the `z`-dependent `P` by the
uniform top `Ze` and pulling the factor out of the sum. -/
lemma t2BsumAux {Dn Ze P : ℕ} {CB1 LN : ℝ} {lam : ℕ → ℝ}
    (hlam_le : ∀ ν : ℕ, |lam ν| ≤ 1)
    (hgnn : ∀ n : ℕ, 0 ≤ Submission.ASP.FIgtil n)
    (hZe1 : (1 : ℝ) ≤ (Ze : ℝ)) (hD1 : (1 : ℝ) ≤ (Dn : ℝ))
    (hB1 : (∑ ν ∈ (Finset.Icc 1 Dn).filter Squarefree,
        |lam ν| * Submission.ASP.FIgtil ν * (ν.divisors.card : ℝ)
          * (∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ)))) ≤ CB1 * LN ^ 3)
    (hPZe : P ≤ Ze) :
    (∑ ν ∈ (Finset.Icc 1 Dn).filter Squarefree,
        |lam ν| * Submission.ASP.FIgtil ν * (ν.divisors.card : ℝ)
          * (∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ)))
          * (1 + Real.log ((ν : ℝ) * (P : ℝ) + 2)))
      ≤ CB1 * LN ^ 3 * (1 + Real.log ((Dn : ℝ) * (Ze : ℝ) + 2)) := by
  have hstep1 : (∑ ν ∈ (Finset.Icc 1 Dn).filter Squarefree,
        |lam ν| * Submission.ASP.FIgtil ν * (ν.divisors.card : ℝ)
          * (∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ)))
          * (1 + Real.log ((ν : ℝ) * (P : ℝ) + 2)))
      ≤ (∑ ν ∈ (Finset.Icc 1 Dn).filter Squarefree,
        |lam ν| * Submission.ASP.FIgtil ν * (ν.divisors.card : ℝ)
          * (∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ)))
          * (1 + Real.log ((ν : ℝ) * (Ze : ℝ) + 2))) := by
    refine Finset.sum_le_sum (fun ν _ => ?_)
    have hPZeR : (P : ℝ) ≤ (Ze : ℝ) := by exact_mod_cast hPZe
    have h5 : (ν : ℝ) * (P : ℝ) + 2 ≤ (ν : ℝ) * (Ze : ℝ) + 2 := by
      have := mul_le_mul_of_nonneg_left hPZeR (Nat.cast_nonneg ν)
      linarith
    have h6 : 0 < (ν : ℝ) * (P : ℝ) + 2 := by
      have : (0 : ℝ) ≤ (ν : ℝ) * (P : ℝ) := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      linarith
    have hfac2 : 1 + Real.log ((ν : ℝ) * (P : ℝ) + 2) ≤ 1 + Real.log ((ν : ℝ) * (Ze : ℝ) + 2) :=
      add_le_add (le_refl 1) (Real.log_le_log h6 h5)
    have hCnn : 0 ≤ |lam ν| * Submission.ASP.FIgtil ν * (ν.divisors.card : ℝ)
        * (∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ))) :=
      mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (hgnn ν)) (Nat.cast_nonneg _))
        (Finset.prod_nonneg (fun p _ => by positivity))
    exact mul_le_mul_of_nonneg_left hfac2 hCnn
  exact le_trans hstep1 (sum_local_factor_le hlam_le hgnn hZe1 hD1 hB1)

/-- **The `T₂`-summand of the `§4–§7` estimate `Work.FIChain.S3phi_Bstar_v2`, uniformly over the
`z`-window** `[zc x HasBc.val, e·zc x HasBc.val]`: `|Tsum2 ã λ (x) y z| ≪ Ã(x)·loglog x/log x` for every
`λ` satisfying `Work.FIChain.SieveInput`, every `y ∈ [Yc x HasBc.val, e·Yc x HasBc.val]` and every `z` in
the `z`-window.

Route: `Work.FIChain.Tsum2_uniformAll` at `M := ⌊y⌋₊`, `P := ⌊z⌋₊`, `N := x`,
`D := Submission.Rcut x`, `Δ := Deltac x`.  The `z`-uniformity is what has to be checked:
* the range condition `Δ·M·P ≤ D` is `Deltac x·⌊e·Yc⌋₊·⌊e·Yc⌋₊ ≤ Dc x`, exactly
  `Work.FIChain.chainRangeWideBstar` (the chain's own `scale_factsC` fact only gives one factor `e`);
* `M, P ≥ 256`, `M, P ≤ x`, `(log M)^6 ≤ M^{3/16}`, `Deltac x^4 ≤ M` are the `scale_factsC` facts
  (`M ≥ ⌊Yc⌋₊ = zc x HasBc.val`);
* the `B`-input `∑_{ν ≤ Deltac x, ♠} |λ ν| g ν τ(ν)∏(1+1/√p)(1+log(ν·P+2))` is bounded uniformly
  in `z` by `CB1·(log x)³·(1 + log(Deltac x·⌊e·Yc⌋₊ + 2))` via
  `Work.FIChain.sum_local_factor_le` with `Zn := ⌊Real.exp 1 * Yc x HasBc.val⌋₊`
  (`Work.FIChain.FIgtil_tau_div_sum_le` supplies `CB1`);
* the rate is the `hE2rate`/`hlogfac` arithmetic of `Work.FIChain.assemblyC` (lines 819–874 and
  933–968) with `⌊e·Yc⌋₊` in place of `zc x HasBc.val` in `1 + log(Δ·Z + 2) ≤ 3 log x` (that step uses
  `Deltac x·⌊e·Yc⌋₊ ≤ Dc x`, a `scale_factsC` fact).

The result is stated with `Work.FIChain.s3phiT2`; the wrapper `s3phiIcc`/`Set.mem_Icc` handling of
the two windows is the caller's business. -/
theorem S3phiT2_Bstar :
    ∃ K : ℝ, ∃ x₀ : ℕ, 0 < K ∧ ∀ x : ℕ, x₀ ≤ x → s3phiCond x →
      ∀ lam : ℕ → ℝ, ∀ C_sieve : ℝ,
        SieveInput Submission.ASP.FIgtil (Deltac x) lam C_sieve →
        ∀ y ∈ s3phiYwin x, ∀ z ∈ s3phiZwin x,
          |s3phiT2 x lam y z| ≤ K * AcountAtilC x * s3phiRate x := by
  classical
  have hBstar_pos : (0 : ℝ) < HasBc.val := by have := HasBc.ge_two; linarith
  have hgmul : ∀ m n : ℕ, Nat.Coprime m n →
      Submission.ASP.FIgtil (m * n) = Submission.ASP.FIgtil m * Submission.ASP.FIgtil n :=
    fun m n hmn => Submission.ASP.FIgtil_mul hmn
  have hg1 : Submission.ASP.FIgtil 1 = 1 := Submission.ASP.FIgtil_one
  have hgnn : ∀ n : ℕ, 0 ≤ Submission.ASP.FIgtil n := Submission.ASP.FIgtil_nonneg
  have hgp : ∀ p : ℕ, p.Prime → 0 ≤ Submission.ASP.FIgtil p ∧ Submission.ASP.FIgtil p < 1 :=
    fun p hp => ⟨hgnn p, Submission.ASP.FIgtil_lt_one hp⟩
  obtain ⟨Chb, hChbpos, hboundFI⟩ := Submission.ASP.FIgtil_bound
  obtain ⟨c9, C9, hC9pos, h9real⟩ := Submission.ASP.FIgtil_sum_19_real
  obtain ⟨K2, hK2pos, hTsum2Use⟩ :=
    Tsum2_uniformAll hgmul hg1 hgp ⟨Chb, hChbpos, hboundFI⟩ ⟨c9, C9, h9real⟩
  obtain ⟨CB1, hCB1pos, hB1leUse⟩ := FIgtil_tau_div_sum_le
  obtain ⟨Xr, hRemAll⟩ := remainder_all
  obtain ⟨Xw, hWide⟩ := chainRangeWideBstar
  have hev : ∀ᶠ x : ℕ in Filter.atTop, s3phiCond x →
      ∀ lam : ℕ → ℝ, ∀ C_sieve : ℝ,
        SieveInput Submission.ASP.FIgtil (Deltac x) lam C_sieve →
        ∀ y ∈ s3phiYwin x, ∀ z ∈ s3phiZwin x,
          |s3phiT2 x lam y z| ≤ (K2 * (16384 * CB1 + 1)) * AcountAtilC x * s3phiRate x := by
    filter_upwards [scale_factsC HasBc.val hBstar_pos,
      window_marginsC (1 / 64) HasBc.val (by norm_num) (by norm_num) hBstar_pos,
      chainRangeFactsC HasBc.val hBstar_pos,
      Filter.eventually_ge_atTop Xr, Filter.eventually_ge_atTop Xw,
      Filter.eventually_ge_atTop 3]
      with x hs hw hch hxr hxw hx3
    obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15,
      hs16⟩ := hs
    obtain ⟨hw1, hw2, hw3, hw4, hw5, hw6, hw7⟩ := hw
    intro _hcond lam _Cs hSI y hy z hz
    rw [s3phiYwin] at hy
    rw [s3phiZwin] at hz
    obtain ⟨hy1, hy2⟩ := Set.mem_Icc.mp hy
    obtain ⟨hz1, hz2⟩ := Set.mem_Icc.mp hz
    have hx3R : (3 : ℝ) ≤ (x : ℝ) := hw6
    have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
    have hLNpos : 0 < Real.log (x : ℝ) := Real.log_pos (by linarith : (1 : ℝ) < (x : ℝ))
    have hLN1 : (1 : ℝ) ≤ Real.log (x : ℝ) := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_three, hx3R])
    have hLLN1 : (1 : ℝ) ≤ Real.log (Real.log (x : ℝ)) := by linarith [hw7]
    let Zn : ℕ := ⌊Yc x HasBc.val⌋₊
    let Ze : ℕ := ⌊Real.exp 1 * Yc x HasBc.val⌋₊
    let LN : ℝ := Real.log (x : ℝ)
    let LLN : ℝ := Real.log (Real.log (x : ℝ))
    let Abar : ℝ := AcountAtilC x
    have hLNp : 0 < LN := hLNpos
    have hLNone : (1 : ℝ) ≤ LN := hLN1
    have hLLNone : (1 : ℝ) ≤ LLN := hLLN1
    have hAb0 : 0 ≤ Abar := by
      show 0 ≤ AcountAtilC x
      rw [Work.FIChain.AcountAtilC, Work.FITop.AcountAtil, Submission.ASP.Acount,
        Nat.floor_natCast]
      exact Finset.sum_nonneg (fun n _ => atilc_nonneg n)
    have hYcpos : 0 < Yc x HasBc.val := hch.2.2.1
    have hy0 : 0 ≤ y := le_trans hYcpos.le hy1
    have hzc0 : (0 : ℝ) ≤ zc x HasBc.val := by simp only [zc]; exact Nat.cast_nonneg _
    have hz0 : 0 ≤ z := le_trans hzc0 hz1
    have hMlo : Zn ≤ ⌊y⌋₊ := by
      show ⌊Yc x HasBc.val⌋₊ ≤ ⌊y⌋₊
      exact Nat.floor_mono hy1
    have hMhi : ⌊y⌋₊ ≤ Ze := by
      show ⌊y⌋₊ ≤ ⌊Real.exp 1 * Yc x HasBc.val⌋₊
      exact Nat.floor_mono hy2
    have hPlo : Zn ≤ ⌊z⌋₊ := by
      show ⌊Yc x HasBc.val⌋₊ ≤ ⌊z⌋₊
      have h : ⌊zc x HasBc.val⌋₊ ≤ ⌊z⌋₊ := Nat.floor_mono hz1
      simpa only [zc, Zc, Nat.floor_natCast] using h
    have hPhi0 : ⌊z⌋₊ ≤ ⌊Real.exp 1 * zc x HasBc.val⌋₊ := Nat.floor_mono hz2
    have hPhi : ⌊z⌋₊ ≤ Ze := by
      show ⌊z⌋₊ ≤ ⌊Real.exp 1 * Yc x HasBc.val⌋₊
      refine le_trans hPhi0 (Nat.floor_mono ?_)
      have hzcYc : (Zc x HasBc.val : ℝ) ≤ Yc x HasBc.val := Nat.floor_le hYcpos.le
      exact mul_le_mul_of_nonneg_left hzcYc (Real.exp_pos 1).le
    have h256 : (256 : ℕ) ≤ Zn := hs1
    have hZnZe : Zn ≤ Ze := hs2
    have hZex : Ze ≤ x := hs3
    have hlog4 : LN ≤ 4 * Real.log (Zn : ℝ) := hs4
    have hlog6 : (Real.log (Ze : ℝ)) ^ 6 ≤ (Zn : ℝ) ^ ((3 : ℝ) / 16) := hs5
    have hD4 : Deltac x ^ 4 ≤ Zn := hs7
    have hZeDc : Deltac x * Ze ≤ Dc x := hs15
    have hwide : Deltac x * Ze * Ze ≤ Dc x := hWide x hxw
    have hlam1 : lam 1 = 1 := hSI.1
    have hΔsupp : ∀ ν : ℕ, Deltac x < ν → lam ν = 0 := hSI.2.1
    have hlam_sq : ∀ ν : ℕ, ¬ Squarefree ν → lam ν = 0 := hSI.2.2.1
    have hlam_le : ∀ ν : ℕ, |lam ν| ≤ 1 := hSI.2.2.2.1
    have hD3 : 3 ≤ Deltac x := hch.2.2.2.2.2.1
    have hDx : Deltac x ≤ x := hch.2.2.2.2.1
    have hLΔpos : 0 < Real.log (Deltac x : ℝ) := by
      have h3 : (3 : ℝ) ≤ (Deltac x : ℝ) := by exact_mod_cast hD3
      exact Real.log_pos (by linarith [Real.exp_one_lt_three, h3])
    have hLΔ_le : Real.log (Deltac x : ℝ) ≤ LN := by
      show Real.log (Deltac x : ℝ) ≤ Real.log (x : ℝ)
      exact Real.log_le_log (by positivity) (by exact_mod_cast hDx)
    have hB1raw : (∑ ν ∈ (Finset.Icc 1 (Deltac x)).filter Squarefree,
        |lam ν| * Submission.ASP.FIgtil ν * (ν.divisors.card : ℝ)
          * (∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ))))
      ≤ CB1 * (Real.log (Deltac x : ℝ)) ^ 3 := by
      refine le_trans (Finset.sum_le_sum ?_) (hB1leUse (Deltac x) hD3)
      intro ν _
      have h1 : |lam ν| ≤ 1 := hlam_le ν
      have h2 : 0 ≤ Submission.ASP.FIgtil ν := hgnn ν
      have h3 : 0 ≤ (ν.divisors.card : ℝ) := by positivity
      have h4 : 0 ≤ ∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ)) :=
        Finset.prod_nonneg (fun p _ => by positivity)
      have h5 : |lam ν| * Submission.ASP.FIgtil ν ≤ 1 * Submission.ASP.FIgtil ν :=
        mul_le_mul_of_nonneg_right h1 h2
      have h6 : |lam ν| * Submission.ASP.FIgtil ν * (ν.divisors.card : ℝ)
          ≤ 1 * Submission.ASP.FIgtil ν * (ν.divisors.card : ℝ) :=
        mul_le_mul_of_nonneg_right h5 h3
      have h7 : |lam ν| * Submission.ASP.FIgtil ν * (ν.divisors.card : ℝ)
            * (∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ)))
          ≤ (1 * Submission.ASP.FIgtil ν * (ν.divisors.card : ℝ))
            * (∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ))) :=
        mul_le_mul_of_nonneg_right h6 h4
      simpa using h7
    have hB1 : (∑ ν ∈ (Finset.Icc 1 (Deltac x)).filter Squarefree,
        |lam ν| * Submission.ASP.FIgtil ν * (ν.divisors.card : ℝ)
          * (∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ))))
      ≤ CB1 * LN ^ 3 :=
      le_trans hB1raw
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hLΔpos.le hLΔ_le 3) hCB1pos.le)
    have hs10' : (1 : ℕ) ≤ Zn := hs10
    have hZe1 : (1 : ℝ) ≤ (Ze : ℝ) := by
      exact_mod_cast (le_trans hs10' hZnZe)
    have hDeltac1 : (1 : ℝ) ≤ (Deltac x : ℝ) := by
      exact_mod_cast (by omega : 1 ≤ Deltac x)
    have hBsum : (∑ ν ∈ (Finset.Icc 1 (Deltac x)).filter Squarefree,
        |lam ν| * Submission.ASP.FIgtil ν * (ν.divisors.card : ℝ)
          * (∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ)))
          * (1 + Real.log ((ν : ℝ) * (⌊z⌋₊ : ℝ) + 2)))
      ≤ CB1 * LN ^ 3 * (1 + Real.log ((Deltac x : ℝ) * (Ze : ℝ) + 2)) :=
      t2BsumAux hlam_le hgnn hZe1 hDeltac1 hB1 hPhi
    have hlogfac : 1 + Real.log ((Deltac x : ℝ) * (Ze : ℝ) + 2) ≤ 3 * LN := by
      show 1 + Real.log ((Deltac x : ℝ) * (Ze : ℝ) + 2) ≤ 3 * Real.log (x : ℝ)
      exact t2LogFacAux hx3 hZeDc
    have hMz : Real.log (Zn : ℝ) ≤ Real.log (⌊y⌋₊ : ℝ) :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < Zn)) (by exact_mod_cast hMlo)
    have hz4 : LN / 4 ≤ Real.log (Zn : ℝ) := by
      have hlog4' : Real.log (x : ℝ) ≤ 4 * Real.log (Zn : ℝ) := hs4
      show Real.log (x : ℝ) / 4 ≤ Real.log (Zn : ℝ)
      linarith
    have hrate : CB1 * LN ^ 3 * (1 + Real.log ((Deltac x : ℝ) * (Ze : ℝ) + 2))
          * (Real.log (⌊y⌋₊ : ℝ)) ^ (-(6 : ℤ)) + LN ^ (-(2 : ℤ))
        ≤ (16384 * CB1 + 1) * (LLN / LN) :=
      t2RateAux hLNone hLLNone hCB1pos hMz hz4 hlogfac
    have hAd : Submission.ASP.Approx atilc Submission.ASP.FIgtil
        (Submission.ASP.rtildeFull Submission.ASP.FIr Submission.ASP.FIg Submission.ASP.FIgtil
          Submission.ASP.FIa) (x : ℝ) :=
      Submission.ASP.approx_atil Submission.ASP.FIa Submission.ASP.FIg Submission.ASP.FIr
        Submission.ASP.FIgtil (x : ℝ) (Submission.ASP.FI_approx (x : ℝ))
    have hRemUse : ∀ m : ℕ, m ≤ x →
        Submission.ASP.RemainderSum
          (Submission.ASP.rtildeFull Submission.ASP.FIr Submission.ASP.FIg Submission.ASP.FIgtil
            Submission.ASP.FIa) (Submission.Rcut x) m ≤ Abar * LN ^ (-(3 : ℤ)) := by
      intro m hm
      have h1 := hRemAll x hxr m hm
      have h2 : (Real.log (x : ℝ)) ^ (-(3 : ℝ)) = LN ^ (-(3 : ℤ)) := by
        change (Real.log (x : ℝ)) ^ (-(3 : ℝ)) = (Real.log (x : ℝ)) ^ (-(3 : ℤ))
        rw [show (-(3 : ℝ)) = ((-3 : ℤ) : ℝ) by norm_num]
        exact Real.rpow_intCast _ _
      rw [h2] at h1
      rw [show Abar = AcountAtilC x from rfl]
      exact h1
    have hLNpow3nn : 0 ≤ LN ^ (-(3 : ℤ)) := by
      rw [show LN ^ (-(3 : ℤ)) = (LN ^ 3)⁻¹ by simp [zpow_neg]]
      exact inv_nonneg.mpr (pow_nonneg hLNp.le 3)
    have hlogM : (Real.log (⌊y⌋₊ : ℝ)) ^ 6 ≤ (⌊y⌋₊ : ℝ) ^ ((3 : ℝ) / 16) := by
      have hy1' : (1 : ℕ) ≤ ⌊y⌋₊ := by omega
      have hlogMnn : 0 ≤ Real.log (⌊y⌋₊ : ℝ) := Real.log_nonneg (by exact_mod_cast hy1')
      have hlog_le : Real.log (⌊y⌋₊ : ℝ) ≤ Real.log (Ze : ℝ) :=
        Real.log_le_log (by exact_mod_cast (by omega : 0 < ⌊y⌋₊)) (by exact_mod_cast hMhi)
      have h6 : (Real.log (⌊y⌋₊ : ℝ)) ^ 6 ≤ (Real.log (Ze : ℝ)) ^ 6 :=
        pow_le_pow_left₀ hlogMnn hlog_le 6
      have h7 : (Zn : ℝ) ^ ((3 : ℝ) / 16) ≤ (⌊y⌋₊ : ℝ) ^ ((3 : ℝ) / 16) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hMlo) (by norm_num)
      exact le_trans h6 (le_trans hlog6 h7)
    have hΔMP : Deltac x * ⌊y⌋₊ * ⌊z⌋₊ ≤ Submission.Rcut x := by
      have h1 : Deltac x * ⌊y⌋₊ * ⌊z⌋₊ ≤ Deltac x * Ze * Ze :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hMhi) hPhi
      have h2 : Deltac x * Ze * Ze ≤ Submission.Rcut x := by
        have h := hwide
        rwa [Dc, Work.FITop.Dcut] at h
      exact le_trans h1 h2
    have hΔ4 : Deltac x ^ 4 ≤ ⌊y⌋₊ := le_trans hD4 hMlo
    have hres := hTsum2Use atilc
      (Submission.ASP.rtildeFull Submission.ASP.FIr Submission.ASP.FIg Submission.ASP.FIgtil
        Submission.ASP.FIa) lam x ⌊y⌋₊ ⌊z⌋₊ (Submission.Rcut x) (Deltac x) Abar
      (Abar * LN ^ (-(3 : ℤ)))
      (CB1 * LN ^ 3 * (1 + Real.log ((Deltac x : ℝ) * (Ze : ℝ) + 2)))
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      hlogM (fun n => atilc_nonneg n) (fun n hn => atilc_eq_zero_of_not_sqfree hn)
      rfl hAd hRemUse (mul_nonneg hAb0 hLNpow3nn) (le_of_eq rfl) hΔMP hΔ4 hΔsupp hlam_sq
      hlam_le hBsum
    have hfinal : K2 * Abar * (CB1 * LN ^ 3 * (1 + Real.log ((Deltac x : ℝ) * (Ze : ℝ) + 2))
          * (Real.log (⌊y⌋₊ : ℝ)) ^ (-(6 : ℤ)) + LN ^ (-(2 : ℤ)))
        ≤ K2 * Abar * ((16384 * CB1 + 1) * (LLN / LN)) :=
      mul_le_mul_of_nonneg_left hrate (mul_nonneg hK2pos.le hAb0)
    calc |s3phiT2 x lam y z|
        = |Submission.ASP.Tsum2 atilc lam (x : ℝ) y z| := rfl
      _ = |Submission.ASP.Tsum2 atilc lam (x : ℝ) (⌊y⌋₊ : ℝ) (⌊z⌋₊ : ℝ)| := by
            rw [Tsum2_floor_yC atilc lam (x : ℝ) y z hy0,
              Tsum2_floor_zC atilc lam (x : ℝ) (⌊y⌋₊ : ℝ) z hz0]
      _ ≤ K2 * Abar * (CB1 * LN ^ 3 * (1 + Real.log ((Deltac x : ℝ) * (Ze : ℝ) + 2))
            * (Real.log (⌊y⌋₊ : ℝ)) ^ (-(6 : ℤ)) + LN ^ (-(2 : ℤ))) := hres
      _ ≤ K2 * Abar * ((16384 * CB1 + 1) * (LLN / LN)) := hfinal
      _ = (K2 * (16384 * CB1 + 1)) * AcountAtilC x * s3phiRate x := by
            show K2 * AcountAtilC x
                * ((16384 * CB1 + 1) * (Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ)))
              = (K2 * (16384 * CB1 + 1)) * AcountAtilC x
                * (Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ))
            ring
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨K2 * (16384 * CB1 + 1), x₀, ?_, hx₀⟩
  have hpos : (0 : ℝ) < 16384 * CB1 + 1 := by linarith [hCB1pos]
  exact mul_pos hK2pos hpos

end

end Work.FIPiChain
