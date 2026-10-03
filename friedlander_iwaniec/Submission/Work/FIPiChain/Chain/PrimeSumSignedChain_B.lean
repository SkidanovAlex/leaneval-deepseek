import Mathlib
import Submission.Work.FIPiChain.HasB
import Submission.Work.FIChain.Defs
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
import Submission.Work.FIFinal.abs_smAvg_S2_int_le
import Submission.Work.FIPiChain.Chain.S3fixed_signed_B
import Submission.Work.FIChain.FI_primeSum_of_estimates_signed
import Submission.Work.FIChain.LocalS4
import Submission.Work.FIChain.LocalS5c
import Submission.Work.FIChain.remainder_all
import Submission.Work.FIChain.LocalS6c
import Submission.ASP.S7e
import Submission.Commons.NumberTheory.Chebyshev.sum_prime_log_mul_g_Ioc_le
import Submission.Work.FIChain.chainRangeFactsC
import Submission.Work.FIChain.Tsum_uniformAll
import Submission.Work.FIChain.Tsum2_uniformAll
import Submission.Work.FIChain.FIgtil_prod_sub_le
import Submission.Work.FIChain.FIgtil_tau_div_sum_le
import Submission.Work.FIChain.AcountAtil_log_bound

set_option autoImplicit false
set_option maxHeartbeats 16000000

open Work.FIChain

namespace Work.FIPiChain

variable [HasBc]

open Finset Filter
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section



/-! ## Auxiliary facts for the assembly -/

/-- Adding two bounds of the shape `a ≤ c·X`. -/
private lemma add_const_mul_le {a₁ a₂ c₁ c₂ X : ℝ} (h1 : a₁ ≤ c₁ * X) (h2 : a₂ ≤ c₂ * X) :
    a₁ + a₂ ≤ (c₁ + c₂) * X := by
  have h : (c₁ + c₂) * X = c₁ * X + c₂ * X := by ring
  linarith [h1, h2, h.le]






/-! ## Floor-invariance of the smoothed sums -/

private lemma logWeight_floorC (n : ℕ) (y : ℝ) (hy : 0 ≤ y) :
    Submission.ASP.logWeight n y = Submission.ASP.logWeight n (⌊y⌋₊ : ℝ) := by
  rw [Submission.ASP.logWeight, Submission.ASP.logWeight]
  congr 1
  refine Finset.filter_congr fun b _ => ?_
  rw [(Nat.le_floor_iff hy).symm, Nat.cast_le]









/-- **The FI endgame with the `S₃` input in *signed* form, at the pinned scale `HasBc.val`.**

This is `Work.FIChain.primeSum_bound_of_prop41` (`Submission/Work/FIChain/primeSum_bound_of_prop41.lean`)
with two changes, both forced by the shape in which the `S₃` input is actually available on disk
(`Work.FIChain.S3fixed_signed_Bstar`, see `NOTES.md` §49–§50):

* the `B`-window `(B′)` is taken at the pinned parameter `HasBc.val = 2^31 + 2`
  (`Work.FIChain.windows_at_Bstar`), so the same `HasBc.val` can serve the `S₃` hypothesis;
* the `S₃` hypothesis `hS3` is the *signed* bound `|∫_Y S₃/y| ≤ K·Ã(x)·loglog x/log x` (with the
  sieve-constant bound `Cs ≤ Ksie`), which is what the companion's §8 proves, instead of the
  `∫_Y|S₃|/y`-bound with rate `J·K·Ã·(log x)^{-4}·log⌊s·z⌋` that no proof on disk supplies.

The body is the verbatim endgame; only the `E5` slot changes (it is now directly the signed
bound, so the arithmetic `E5 ≤ K·Ã·loglog/log` of the original collapses to `le_rfl`) and the
final `Submission.ASP.FI_primeSum_of_estimates` is replaced by the signed version
`Work.FIChain.FI_primeSum_of_estimates_signed`.-/
theorem primeSumSignedChain
    (hBp : ∃ Kbp : ℝ, ∃ xbp : ℕ, 0 < Kbp ∧ ∀ x : ℕ, xbp ≤ x →
      Work.FIChain.BprimeWindowInt Work.FIChain.atilc x Work.FIChain.wc
        (Kbp * Work.FIChain.AcountAtilC x * (Real.log (x : ℝ)) ^ (-(4 : ℤ)))
        (Work.FIChain.Yc x HasBc.val / (Work.FIChain.Deltac x : ℝ))
        (Work.FIChain.sc x HasBc.val * (Real.exp 1 * Work.FIChain.Yc x HasBc.val)))
    (Ksie : ℝ) (hKsie : 0 < Ksie)
    (hsieve : ∀ Δ : ℕ, 3 ≤ Δ → ∃ lam : ℕ → ℝ, ∃ Cs : ℝ,
        Work.FIChain.SieveInput Submission.ASP.FIgtil Δ lam Cs ∧ Cs ≤ Ksie)
    (hS3 : ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℕ in Filter.atTop,
        (x : ℝ) ^ ((1 : ℝ) / 4 + 1 / 64) + 2 < Work.FIChain.Yc x HasBc.val / (Work.FIChain.Deltac x : ℝ) →
        ∀ lam : ℕ → ℝ, ∀ Cs : ℝ,
          Work.FIChain.SieveInput Submission.ASP.FIgtil (Work.FIChain.Deltac x) lam Cs → Cs ≤ Ksie →
          |(∫ y in Work.FIChain.Yc x HasBc.val..(Real.exp 1 * Work.FIChain.Yc x HasBc.val),
              Submission.ASP.S3 Work.FIChain.atilc lam x (Work.FIChain.zc x HasBc.val)
                (Work.FIChain.sc x HasBc.val * y) (Work.FIChain.sc x HasBc.val * Work.FIChain.zc x HasBc.val) / y)|
            ≤ K * Work.FIChain.AcountAtilC x
                * (Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ))) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in Filter.atTop,
      |(∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log (p : ℝ) * Submission.ASP.FIa p)
          - (4 / Real.pi) * Submission.ASP.Acount Submission.ASP.FIa (N : ℝ)|
        ≤ C * Work.FIChain.AcountAtilC N
            * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ)) := by
  classical
  -- ## 1. the fixed constants
  have hSieveSpec := hsieve
  obtain ⟨Kbp, xbp, hKbp, hBwinRaw⟩ := hBp
  have hBpos : (0 : ℝ) < HasBc.val := s3fB_Bstar_pos
  obtain ⟨K3, hK3pos, hS3raw⟩ := hS3
  have hgmul : ∀ m n : ℕ, Nat.Coprime m n →
      Submission.ASP.FIgtil (m * n) = Submission.ASP.FIgtil m * Submission.ASP.FIgtil n :=
    fun m n hmn => Submission.ASP.FIgtil_mul hmn
  have hg1 : Submission.ASP.FIgtil 1 = 1 := Submission.ASP.FIgtil_one
  have hgnn : ∀ n : ℕ, 0 ≤ Submission.ASP.FIgtil n := Submission.ASP.FIgtil_nonneg
  have hgp : ∀ p : ℕ, p.Prime → 0 ≤ Submission.ASP.FIgtil p ∧ Submission.ASP.FIgtil p < 1 :=
    fun p hp => ⟨hgnn p, Submission.ASP.FIgtil_lt_one hp⟩
  obtain ⟨Chb, hChbpos, hboundFI⟩ := Submission.ASP.FIgtil_bound
  have hboundFI' : ∃ C : ℝ, ∀ p : ℕ, p.Prime → Submission.ASP.FIgtil p ≤ C / (p : ℝ) :=
    ⟨Chb, hboundFI⟩
  obtain ⟨c9, C9, hC9pos, h9real⟩ := Submission.ASP.FIgtil_sum_19_real
  obtain ⟨K1, H1, hK1pos, hH1pos, hH1tend, hTsumUse⟩ :=
    Tsum_uniformAll hgmul hg1 hgp hboundFI' ⟨c9, C9, h9real⟩
  obtain ⟨K2, hK2pos, hTsum2Use⟩ :=
    Tsum2_uniformAll hgmul hg1 hgp ⟨Chb, hChbpos, hboundFI⟩ ⟨c9, C9, h9real⟩
  obtain ⟨C1p, hC1ppos, hprodsubUse⟩ := FIgtil_prod_sub_le
  obtain ⟨CB1, hCB1pos, hB1leUse⟩ := FIgtil_tau_div_sum_le
  obtain ⟨Htil, hHtilpos, hHtilTend, hHtilProd⟩ := Submission.ASP.FIgtil_H_exists
  have hHmulG : Htil * Submission.ASP.Gprod Submission.ASP.FIg = 4 / Real.pi :=
    Submission.ASP.FIgtil_H_mul_Gprod hHtilProd
  have hGpos : (0 : ℝ) < Submission.ASP.Gprod Submission.ASP.FIg := Submission.ASP.Gprod_FIg_pos
  have hH1eq : H1 = Htil := by
    have hh := tendsto_nhds_unique hH1tend hHtilTend
    linarith
  obtain ⟨Xr, hRemAll⟩ := remainder_all
  obtain ⟨X9, Cg9, hCg9pos, h912raw⟩ := Submission.ASP.FI_912
  obtain ⟨XG, hAseqG⟩ := Submission.ASP.FI_Aseq_le_const_mul_Atil
  obtain ⟨Cas, hCaspos, hAseqle⟩ := Submission.Aseq_le_const_mul_rpow
  obtain ⟨cA9, hcA9pos, XA9, hAle⟩ := Submission.exists_const_mul_rpow_le_Aseq
  obtain ⟨CE6, hCE6pos, hE6bound_ev⟩ := AcountAtil_log_bound
  obtain ⟨C00, hC00pos, hIocle⟩ :=
    Commons.NumberTheory.Chebyshev.sum_prime_log_mul_g_Ioc_le (g := Submission.ASP.FIgtil) (fun p _ => hgnn p) ⟨Chb, hChbpos, hboundFI⟩
  obtain ⟨C6, hC6pos, hC6le_ev⟩ := L6_param_le HasBc.val C00 hBpos hC00pos hIocle
  obtain ⟨X6, hC6le⟩ := Filter.eventually_atTop.mp hC6le_ev
  obtain ⟨Xe6, hXe6, he6⟩ :=
    Commons.Analysis.ExpLog.const_mul_log_pow_le_rpow_threshold (K := Cas / cA9)
      (div_nonneg hCaspos.le hcA9pos.le) (n := 2) (r := 3 / 8) (by norm_num)
  have hC0pos : 0 < max Chb 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  set KX : ℝ := K1 * (1024 * CB1 + 1) + K2 * (16384 * CB1 + 1)
      + (200 * C6 * Real.exp 2 * Ksie * Real.exp (32 * max Chb 1) * C1p + 1)
      + 4 * Kbp + K3 + CE6
      + 2 * |Htil| * Cg9 / Submission.ASP.Gprod Submission.ASP.FIg with hKXdef
  set Cfin : ℝ := KX + 1 with hCfindef
  refine ⟨Cfin, ?_, ?_⟩
  · rw [hCfindef]
    have h1 : 0 < K1 * (1024 * CB1 + 1) := by positivity
    have h2 : 0 < K2 * (16384 * CB1 + 1) := by positivity
    have h3 : 0 < 200 * C6 * Real.exp 2 * Ksie * Real.exp (32 * max Chb 1) * C1p + 1 := by positivity
    have h4 : 0 < 4 * Kbp := by positivity
    have h5 : 0 < K3 := hK3pos
    have h6 : 0 < CE6 := hCE6pos
    have h7 : 0 < 2 * |Htil| * Cg9 / Submission.ASP.Gprod Submission.ASP.FIg := by
      have hHabs : 0 < |Htil| := abs_pos.mpr (ne_of_gt hHtilpos)
      positivity
    rw [show KX = K1 * (1024 * CB1 + 1) + K2 * (16384 * CB1 + 1)
        + (200 * C6 * Real.exp 2 * Ksie * Real.exp (32 * max Chb 1) * C1p + 1)
        + 4 * Kbp + K3 + CE6
        + 2 * |Htil| * Cg9 / Submission.ASP.Gprod Submission.ASP.FIg from hKXdef]
    linarith
  have hevLLN : ∀ᶠ N : ℕ in Filter.atTop,
      100 * (2 * HasBc.val + 6) * Real.log (Real.log (N : ℝ)) ≤ Real.log (N : ℝ) := by
    have hc : (0 : ℝ) < 100 * (2 * HasBc.val + 6) := by linarith
    filter_upwards [Work.FITop.FI_ev_log_ge_nat (4 * (100 * (2 * HasBc.val + 6)) ^ 2),
      Filter.eventually_ge_atTop 3] with M hM h3
    have hM3 : (3 : ℝ) ≤ (M : ℝ) := by exact_mod_cast h3
    have hL1 : (1 : ℝ) ≤ Real.log (M : ℝ) := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_three, hM3])
    have hLp : 0 < Real.log (M : ℝ) := lt_of_lt_of_le zero_lt_one hL1
    have hLLN : Real.log (Real.log (M : ℝ)) ≤ 2 * Real.sqrt (Real.log (M : ℝ)) := by
      have h1 : Real.log (Real.log (M : ℝ)) = 2 * Real.log (Real.sqrt (Real.log (M : ℝ))) := by
        rw [Real.log_sqrt hLp.le]; ring
      rw [h1]
      have h2 : Real.log (Real.sqrt (Real.log (M : ℝ))) ≤ Real.sqrt (Real.log (M : ℝ)) := by
        have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hLp)
        linarith
      linarith
    have hsqrt : Real.sqrt (Real.log (M : ℝ)) ≤ Real.log (M : ℝ) / (2 * (100 * (2 * HasBc.val + 6))) := by
      rw [le_div_iff₀ (by positivity)]
      have h2 : (2 * (100 * (2 * HasBc.val + 6))) ^ 2 ≤ Real.log (M : ℝ) := by nlinarith [hM]
      have h3 : (2 * (100 * (2 * HasBc.val + 6))) ≤ Real.sqrt (Real.log (M : ℝ)) :=
        (Real.le_sqrt (by positivity) (by positivity)).mpr h2
      nlinarith [h3, Real.sqrt_nonneg (Real.log (M : ℝ)), Real.sq_sqrt hLp.le]
    have h4 : 2 * Real.sqrt (Real.log (M : ℝ)) ≤ Real.log (M : ℝ) / (100 * (2 * HasBc.val + 6)) := by
      have h5 := mul_le_mul_of_nonneg_left hsqrt (by norm_num : (0 : ℝ) ≤ 2)
      have h6 : (2 : ℝ) * (Real.log (M : ℝ) / (2 * (100 * (2 * HasBc.val + 6))))
          = Real.log (M : ℝ) / (100 * (2 * HasBc.val + 6)) := by
        field_simp
      rwa [h6] at h5
    have h5 : 100 * (2 * HasBc.val + 6) * (Real.log (M : ℝ) / (100 * (2 * HasBc.val + 6))) = Real.log (M : ℝ) := by
      have h6 : (100 : ℝ) * (2 * HasBc.val + 6) ≠ 0 := ne_of_gt hc
      field_simp
    have h6 : 100 * (2 * HasBc.val + 6) * Real.log (Real.log (M : ℝ))
        ≤ 100 * (2 * HasBc.val + 6) * (Real.log (M : ℝ) / (100 * (2 * HasBc.val + 6))) :=
      mul_le_mul_of_nonneg_left (by linarith [hLLN, h4]) hc.le
    linarith [h6, h5]
  obtain ⟨XJ, hXJ1, hXJ⟩ := Commons.Analysis.ExpLog.const_mul_log_pow_le_rpow_threshold
    (K := 2) (by norm_num) (n := ⌈HasBc.val + 2⌉₊) (r := 3 / 16) (by norm_num)
  filter_upwards [scale_factsC HasBc.val hBpos,
      window_marginsC (1 / 64) HasBc.val (by norm_num) (by norm_num) hBpos,
      chainRangeFactsC HasBc.val hBpos, hS3raw, Filter.eventually_ge_atTop xbp,
      Filter.eventually_ge_atTop Xr, Filter.eventually_ge_atTop X9,
      Filter.eventually_ge_atTop XG, Filter.eventually_ge_atTop XA9,
      Filter.eventually_ge_atTop X6, Filter.eventually_ge_atTop ⌈Xe6⌉₊,
      Filter.eventually_ge_atTop ⌈XJ⌉₊, hevLLN, Work.FITop.FI_ev_log_ge_nat 4,
      Work.FITop.FI_ev_log_ge_nat (2 * Cg9 / Submission.ASP.Gprod Submission.ASP.FIg),
      Work.FITop.FI_ev_rpow_ge_nat ((3 : ℝ) / 4) (by norm_num) (2 / cA9),
      Filter.eventually_ge_atTop 3, hE6bound_ev]
    with N hsc hwm hch hS3N hNxbp hNXr hNX9 hNXG hNXA hNX6 hNe6 hNXJ hLLNthresh hLNbig'
      hLNcg' hNbigpow' hN3 hE6bound
  obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16⟩ := hsc
  obtain ⟨hw1, hw2, hw3, hw4, hw5, hw6, hw7⟩ := hwm
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8⟩ := hch
  have hLNbig : (4 : ℝ) ≤ Real.log (N : ℝ) := hLNbig'
  have hLNcg : 2 * Cg9 ≤ Submission.ASP.Gprod Submission.ASP.FIg * Real.log (N : ℝ) := by
    have h1 : (2 * Cg9 / Submission.ASP.Gprod Submission.ASP.FIg) ≤ Real.log (N : ℝ) := hLNcg'
    have h2 := mul_le_mul_of_nonneg_right h1 hGpos.le
    rw [div_mul_cancel₀ _ (ne_of_gt hGpos)] at h2
    linarith [h2]
  have hNbigpow : (1 : ℝ) ≤ cA9 / 2 * (N : ℝ) ^ ((3 : ℝ) / 4) := by
    have h1 : (2 / cA9) ≤ (N : ℝ) ^ ((3 : ℝ) / 4) := hNbigpow'
    have h2 := mul_le_mul_of_nonneg_right h1 hcA9pos.le
    rw [div_mul_cancel₀ _ (ne_of_gt hcA9pos)] at h2
    linarith [h2]
  set Dn : ℕ := Work.FIChain.Deltac N with hDndef
  set Zn : ℕ := ⌊Work.FIChain.Yc N HasBc.val⌋₊ with hZndef
  set M1n : ℕ := ⌊Real.exp 1 * Work.FIChain.Yc N HasBc.val⌋₊ with hM1ndef
  set d2n : ℕ := Work.FIChain.d2c N HasBc.val with hd2ndef
  set Mcn : ℕ := Work.FIChain.Mc N HasBc.val with hMcndef
  set sr : ℝ := Work.FIChain.sc N HasBc.val with hsrdef
  set Yr : ℝ := Work.FIChain.Yc N HasBc.val with hYrdef
  set Jn : ℕ := Work.FIChain.Jc N HasBc.val with hJndef
  -- ## 2. elementary log facts
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hLNpos : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith : (1 : ℝ) < (N : ℝ))
  have hLN1 : (1 : ℝ) ≤ Real.log (N : ℝ) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_three, hw6])
  have hLLN1 : (1 : ℝ) ≤ Real.log (Real.log (N : ℝ)) := by linarith [hw7]
  have hLLN0 : (0 : ℝ) ≤ Real.log (Real.log (N : ℝ)) := by linarith [hw7]
  set LN : ℝ := Real.log (N : ℝ) with hLNdef
  set LLN : ℝ := Real.log (Real.log (N : ℝ)) with hLLNdef
  have hLNp : 0 < LN := hLNpos
  have hLNone : (1 : ℝ) ≤ LN := hLN1
  have hLLNone : (1 : ℝ) ≤ LLN := hLLN1
  set Abar : ℝ := Work.FIChain.AcountAtilC N with hAbardef
  have hAbar0 : 0 ≤ Abar := by
    rw [hAbardef, Work.FIChain.AcountAtilC, Work.FITop.AcountAtil, Submission.ASP.Acount,
      Nat.floor_natCast]
    exact Finset.sum_nonneg (fun n _ => atilc_nonneg n)
  have hLLN_le : LLN ≤ LN := by
    rw [hLLNdef, hLNdef]
    exact Real.log_le_self hLNpos.le
  -- ## 3. the sieve weight
  obtain ⟨lam, Cs, hSI, hCsle⟩ := hSieveSpec (Dn) hc6
  clear hSieveSpec
  have hlam1 : lam 1 = 1 := hSI.1
  have hΔsupp : ∀ ν : ℕ, Dn < ν → lam ν = 0 := hSI.2.1
  have hlam_sq : ∀ ν : ℕ, ¬ Squarefree ν → lam ν = 0 := hSI.2.2.1
  have hlam_le : ∀ ν : ℕ, |lam ν| ≤ 1 := hSI.2.2.2.1
  have hrho : ∀ n : ℕ, 0 ≤ Submission.ASP.rhoOf lam n := hSI.2.2.2.2.1
  have hpos : ∀ d : ℕ, 0 ≤ ∑ ν ∈ Finset.Icc 1 (Dn),
      lam ν * Submission.ASP.FIgtil (Nat.lcm ν d) := hSI.2.2.2.2.2.1
  have hpos' : ∀ d : ℕ, 0 ≤ ∑ ν ∈ Finset.Icc 1 (Dn),
      lam ν * Submission.ASP.FIgtil (ν / Nat.gcd ν d) := hSI.2.2.2.2.2.2.1
  have hCs0 : 0 < Cs := hSI.2.2.2.2.2.2.2.1
  have hCsie : ∑ ν ∈ (Finset.Icc 1 (Dn)).filter Squarefree,
        lam ν * (Submission.ASP.FIgtil ν *
          Work.FIChain.hSieveC Submission.ASP.FIgtil (1 / Real.log (Dn : ℝ)) ν)
      ≤ Cs * ∏ p ∈ Nat.primesBelow (Dn),
          (1 - Submission.ASP.FIgtil p *
            Work.FIChain.hSieveC Submission.ASP.FIgtil (1 / Real.log (Dn : ℝ)) p) :=
    hSI.2.2.2.2.2.2.2.2
  have hCsie' : ∑ ν ∈ (Finset.Icc 1 (Dn)).filter Squarefree,
        lam ν * (Submission.ASP.FIgtil ν *
          Submission.ASP.hSieve Submission.ASP.FIgtil (1 / Real.log (Dn : ℝ)) ν)
      ≤ Cs * ∏ p ∈ Nat.primesBelow (Dn),
          (1 - Submission.ASP.FIgtil p *
            Submission.ASP.hSieve Submission.ASP.FIgtil (1 / Real.log (Dn : ℝ)) p) := by
    simpa only [Work.FIChain.hSieveC, Submission.ASP.hSieve] using hCsie
  -- ## 4. the rate functions
  have hB1 : (∑ ν ∈ (Finset.Icc 1 (Dn)).filter Squarefree,
        |lam ν| * Submission.ASP.FIgtil ν * (ν.divisors.card : ℝ)
          * (∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ))))
      ≤ CB1 * (Real.log (Dn : ℝ)) ^ 3 := by
    refine le_trans (Finset.sum_le_sum ?_) (hB1leUse (Dn) hc6)
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
  have hLΔ1 : (1 : ℝ) ≤ Real.log (Dn : ℝ) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by
      have h3 : (3 : ℝ) ≤ (Dn : ℝ) := by exact_mod_cast hc6
      linarith [Real.exp_one_lt_three])
  have hLΔpos : 0 < Real.log (Dn : ℝ) := lt_of_lt_of_le zero_lt_one hLΔ1
  have hLΔ_le : Real.log (Dn : ℝ) ≤ LN := by
    rw [hLNdef]
    exact Real.log_le_log (by positivity) (by exact_mod_cast hc5)
  have hLΔ_low : LN / 100 ≤ Real.log (Dn : ℝ) := by
    have h1 : (N : ℝ) ^ ((1 : ℝ) / 100) ≤ (Dn : ℝ) := by
      rw [hDndef, Work.FIChain.Deltac, Work.FITop.Delta1, Work.FITop.Lam1]
      exact Nat.le_ceil _
    have h2 : Real.log ((N : ℝ) ^ ((1 : ℝ) / 100)) ≤ Real.log (Dn : ℝ) :=
      Real.log_le_log (Real.rpow_pos_of_pos hNpos _) h1
    rw [Real.log_rpow hNpos, ← hLNdef] at h2
    linarith [h2]
  have hB1' : (∑ ν ∈ (Finset.Icc 1 (Dn)).filter Squarefree,
        |lam ν| * Submission.ASP.FIgtil ν * (ν.divisors.card : ℝ)
          * (∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ))))
      ≤ CB1 * LN ^ 3 :=
    le_trans hB1 (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hLΔpos.le hLΔ_le 3) hCB1pos.le)
  have hB2 : (∑ ν ∈ (Finset.Icc 1 (Dn)).filter Squarefree,
        |lam ν| * Submission.ASP.FIgtil ν * (ν.divisors.card : ℝ)
          * (∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ)))
          * (1 + Real.log ((ν : ℝ) * (Zn : ℝ) + 2)))
      ≤ CB1 * LN ^ 3 * (1 + Real.log ((Dn : ℝ) * (Zn : ℝ) + 2)) :=
    sum_local_factor_le hlam_le (fun n => hgnn n) (by exact_mod_cast hs10)
      (by exact_mod_cast (by omega : 1 ≤ Dn)) hB1'
  have hB2nn : 0 ≤ CB1 * LN ^ 3
      * (1 + Real.log ((Dn : ℝ) * (Zn : ℝ) + 2)) := by
    have hΔ1 : (1 : ℝ) ≤ (Dn : ℝ) := by exact_mod_cast (by omega : 1 ≤ Dn)
    have hZ1 : (1 : ℝ) ≤ (Zn : ℝ) := by exact_mod_cast hs10
    have h6 : (1 : ℝ) * 1 ≤ (Dn : ℝ) * (Zn : ℝ) := mul_le_mul hΔ1 hZ1 (by norm_num) (by linarith)
    have h3 : (1 : ℝ) ≤ (Dn : ℝ) * (Zn : ℝ) + 2 := by linarith only [h6]
    have h4 : 0 ≤ Real.log ((Dn : ℝ) * (Zn : ℝ) + 2) := Real.log_nonneg h3
    have h5 : (0 : ℝ) ≤ CB1 * LN ^ 3 := mul_nonneg hCB1pos.le (pow_nonneg hLNp.le 3)
    exact mul_nonneg h5 (by linarith only [h4])

  -- ## 5. the (4.5) and (5.1) rates
  have hM0logpos : 0 < Real.log (Zn : ℝ) := by
    apply Real.log_pos
    have h256 : (256 : ℝ) ≤ (Zn : ℝ) := by exact_mod_cast hs1
    linarith
  have hlogM0 : LN / 4 ≤ Real.log (Zn : ℝ) := by
    have h := hs4
    linarith
  have hLp2 : LN ^ (-(2 : ℤ)) = (LN ^ 2)⁻¹ := by simp [zpow_neg]
  have hM0p5 : (Real.log (Zn : ℝ)) ^ (-(5 : ℤ)) = ((Real.log (Zn : ℝ)) ^ 5)⁻¹ := by simp [zpow_neg]
  have hM0p6 : (Real.log (Zn : ℝ)) ^ (-(6 : ℤ)) = ((Real.log (Zn : ℝ)) ^ 6)⁻¹ := by simp [zpow_neg]
  have hpow5 : ((Real.log (Zn : ℝ)) ^ 5)⁻¹ ≤ 1024 * (LN ^ 5)⁻¹ := by
    rw [inv_eq_one_div, inv_eq_one_div]
    have hkey : (1024 : ℝ) * (1 / LN ^ 5) = 1024 / LN ^ 5 := by ring
    rw [hkey, div_le_div_iff₀ (pow_pos hM0logpos 5) (pow_pos hLNp 5)]
    have h := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ LN / 4) hlogM0 5
    rw [div_pow] at h
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < (4 : ℝ) ^ 5)] at h
    linarith [h]
  have hpow6 : ((Real.log (Zn : ℝ)) ^ 6)⁻¹ ≤ 4096 * (LN ^ 6)⁻¹ := by
    rw [inv_eq_one_div, inv_eq_one_div]
    have hkey : (4096 : ℝ) * (1 / LN ^ 6) = 4096 / LN ^ 6 := by ring
    rw [hkey, div_le_div_iff₀ (pow_pos hM0logpos 6) (pow_pos hLNp 6)]
    have h := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ LN / 4) hlogM0 6
    rw [div_pow] at h
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < (4 : ℝ) ^ 6)] at h
    linarith [h]
  have hkey3 : LN ^ 3 * (LN ^ 5)⁻¹ = (LN ^ 2)⁻¹ := by
    rw [inv_eq_one_div, inv_eq_one_div]
    rw [show LN ^ 3 * (1 / LN ^ 5) = 1 / LN ^ 2 by
      rw [mul_one_div, div_eq_div_iff (pow_ne_zero 5 (ne_of_gt hLNp)) (pow_ne_zero 2 (ne_of_gt hLNp))]
      ring]
  have hkey4 : LN ^ 4 * (LN ^ 6)⁻¹ = (LN ^ 2)⁻¹ := by
    rw [inv_eq_one_div, inv_eq_one_div]
    rw [show LN ^ 4 * (1 / LN ^ 6) = 1 / LN ^ 2 by
      rw [mul_one_div, div_eq_div_iff (pow_ne_zero 6 (ne_of_gt hLNp)) (pow_ne_zero 2 (ne_of_gt hLNp))]
      ring]
  have hE1rate : CB1 * LN ^ 3 * (Real.log (Zn : ℝ)) ^ (-(5 : ℤ))
      + LN ^ (-(2 : ℤ)) ≤ (1024 * CB1 + 1) * (LLN / LN) := by
    have h1 : CB1 * LN ^ 3 * (Real.log (Zn : ℝ)) ^ (-(5 : ℤ))
        ≤ 1024 * CB1 * (LN ^ 2)⁻¹ := by
      rw [hM0p5]
      calc CB1 * LN ^ 3 * ((Real.log (Zn : ℝ)) ^ 5)⁻¹
          ≤ CB1 * LN ^ 3 * (1024 * (LN ^ 5)⁻¹) :=
            mul_le_mul_of_nonneg_left hpow5 (by positivity)
        _ = 1024 * CB1 * (LN ^ 3 * (LN ^ 5)⁻¹) := by ring
        _ = 1024 * CB1 * (LN ^ 2)⁻¹ := by rw [hkey3]
    have h2 : 1024 * CB1 * (LN ^ 2)⁻¹ ≤ 1024 * CB1 * (LLN / LN) := by
      have h := zpow_two_le_div hLNone hLLNone
      rw [hLp2] at h
      exact mul_le_mul_of_nonneg_left h (by positivity)
    have h3 : (LN ^ 2)⁻¹ ≤ LLN / LN := by
      have h := zpow_two_le_div hLNone hLLNone
      rwa [hLp2] at h
    have h4 : (1024 : ℝ) * CB1 * (LLN / LN) + LLN / LN ≤ (1024 * CB1 + 1) * (LLN / LN) := by
      rw [show (1024 : ℝ) * CB1 * (LLN / LN) + LLN / LN
          = (1024 * CB1 + 1) * (LLN / LN) by ring]
    have h5 : LN ^ (-(2 : ℤ)) = (LN ^ 2)⁻¹ := hLp2
    rw [h5]
    linarith only [h1, h2, h3, h4]
  have hlogfac : 1 + Real.log ((Dn : ℝ) * (Zn : ℝ) + 2) ≤ 3 * LN := by
    have hprod : (Dn : ℝ) * (Zn : ℝ) ≤ (N : ℝ) := by
      have hZle : (Zn : ℝ) ≤ (M1n : ℝ) := by exact_mod_cast hs2
      have h1 : (Dn : ℝ) * (Zn : ℝ) ≤ (Dn : ℝ) * (M1n : ℝ) :=
        mul_le_mul_of_nonneg_left hZle (by positivity)
      have h2 : (Dn : ℝ) * (M1n : ℝ) ≤ (Submission.Rcut N : ℝ) := by
        have h := hs15
        rw [Work.FIChain.Dc, Work.FITop.Dcut] at h
        exact_mod_cast h
      have h3 : (Submission.Rcut N : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast Submission.Rcut_le_self N
      linarith only [h1, h2, h3]
    have h2 : (Dn : ℝ) * (Zn : ℝ) + 2 ≤ 2 * (N : ℝ) := by linarith only [hprod, hw6]
    have h3 : Real.log ((Dn : ℝ) * (Zn : ℝ) + 2) ≤ Real.log (2 * (N : ℝ)) :=
      Real.log_le_log (by positivity) h2
    rw [Real.log_mul (by norm_num) (ne_of_gt hNpos)] at h3
    have h4 : Real.log 2 ≤ LN := by
      rw [hLNdef]
      exact Real.log_le_log (by norm_num) (by linarith only [hw6])
    linarith only [h3, h4, hLNone]
  have hE2rate : CB1 * LN ^ 3
        * (1 + Real.log ((Dn : ℝ) * (Zn : ℝ) + 2))
        * (Real.log (Zn : ℝ)) ^ (-(6 : ℤ))
      + LN ^ (-(2 : ℤ)) ≤ (16384 * CB1 + 1) * (LLN / LN) := by
    have h1 : CB1 * LN ^ 3 * (1 + Real.log ((Dn : ℝ) * (Zn : ℝ) + 2))
          * (Real.log (Zn : ℝ)) ^ (-(6 : ℤ))
        ≤ 12288 * CB1 * (LN ^ 2)⁻¹ := by
      rw [hM0p6]
      have hstep : CB1 * LN ^ 3 * (1 + Real.log ((Dn : ℝ) * (Zn : ℝ) + 2))
            * ((Real.log (Zn : ℝ)) ^ 6)⁻¹
          ≤ CB1 * LN ^ 3 * (3 * LN) * (4096 * (LN ^ 6)⁻¹) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hlogfac (by positivity)) hpow6
          (by positivity) (by positivity)
      refine le_trans hstep (le_of_eq ?_)
      calc CB1 * LN ^ 3 * (3 * LN) * (4096 * (LN ^ 6)⁻¹)
          = 4096 * 3 * CB1 * (LN ^ 4 * (LN ^ 6)⁻¹) := by ring
        _ = 4096 * 3 * CB1 * (LN ^ 2)⁻¹ := by rw [hkey4]
        _ = 12288 * CB1 * (LN ^ 2)⁻¹ := by ring
    have h2 : 12288 * CB1 * (LN ^ 2)⁻¹ ≤ 16384 * CB1 * (LLN / LN) := by
      have h := zpow_two_le_div hLNone hLLNone
      rw [hLp2] at h
      refine le_trans (mul_le_mul_of_nonneg_left h (by positivity)) ?_
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      refine mul_le_mul_of_nonneg_right ?_ hCB1pos.le
      norm_num
    have h3 : (LN ^ 2)⁻¹ ≤ LLN / LN := by
      have h := zpow_two_le_div hLNone hLLNone
      rwa [hLp2] at h
    have h4 : (16384 : ℝ) * CB1 * (LLN / LN) + LLN / LN ≤ (16384 * CB1 + 1) * (LLN / LN) := by
      rw [show (16384 : ℝ) * CB1 * (LLN / LN) + LLN / LN
          = (16384 * CB1 + 1) * (LLN / LN) by ring]
    have h5 : LN ^ (-(2 : ℤ)) = (LN ^ 2)⁻¹ := hLp2
    rw [h5]
    linarith only [h1, h2, h3, h4]
  clear hIocle hB1leUse
  have hsupp : ∀ ν : ℕ, ν ∉ Finset.Icc 1 (Dn) → lam ν = 0 := by
    intro ν hν
    rcases Nat.eq_zero_or_pos ν with h0 | hpos
    · subst h0
      exact hlam_sq 0 (fun h => h.ne_zero rfl)
    · refine hΔsupp ν ?_
      rw [Finset.mem_Icc] at hν
      by_contra hle
      exact hν ⟨hpos, Nat.le_of_not_lt hle⟩
  have hC0b : ∀ p : ℕ, p.Prime → Submission.ASP.FIgtil p ≤ max Chb 1 / (p : ℝ) := fun p hp =>
    le_trans (hboundFI p hp) (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity))
  have hLLN_le2 : Real.log 3 ≤ 2 * LLN := by
    have h4 : Real.log 3 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
      linarith
    linarith [hLLNone]
  have hthresh : 100 * (Real.log 3 + (2 * HasBc.val + 4) * LLN) ≤ LN := by
    have h1 : 100 * (Real.log 3 + (2 * HasBc.val + 4) * LLN) ≤ 100 * (2 * LLN + (2 * HasBc.val + 4) * LLN) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      linarith [hLLN_le2]
    have h2 : 100 * (2 * LLN + (2 * HasBc.val + 4) * LLN) = 100 * (2 * HasBc.val + 6) * LLN := by ring
    linarith [h1, h2, hLLNthresh]
  have hLNp3 : 0 ≤ LN ^ (-(3 : ℤ)) := by
    rw [show LN ^ (-(3 : ℤ)) = (LN ^ 3)⁻¹ by simp [zpow_neg]]
    exact inv_nonneg.mpr (pow_nonneg hLNp.le 3)
  have hLNp4 : 0 ≤ LN ^ (-(4 : ℤ)) := by
    rw [show LN ^ (-(4 : ℤ)) = (LN ^ 4)⁻¹ by simp [zpow_neg]]
    exact inv_nonneg.mpr (pow_nonneg hLNp.le 4)
  have hδ2pos : (0 : ℝ) < ((d2n : ℕ) : ℝ) := by
    rw [hd2ndef, Work.FIChain.d2c]
    have : 0 < ⌈2 * (Real.log (N : ℝ)) ^ (2 * HasBc.val + 4)⌉₊ := Nat.ceil_pos.mpr (by positivity)
    exact_mod_cast this
  have hδ2ge1 : (1 : ℝ) ≤ ((d2n : ℕ) : ℝ) := by
    rw [hd2ndef, Work.FIChain.d2c]
    have : (1 : ℕ) ≤ ⌈2 * (Real.log (N : ℝ)) ^ (2 * HasBc.val + 4)⌉₊ := Nat.ceil_pos.mpr (by positivity)
    exact_mod_cast this
  have hδ2le : ((d2n : ℕ) : ℝ) ≤ 3 * LN ^ (2 * HasBc.val + 4) := by
    rw [hd2ndef, Work.FIChain.d2c]
    have h1 : ((⌈2 * (Real.log (N : ℝ)) ^ (2 * HasBc.val + 4)⌉₊ : ℕ) : ℝ) < 2 * LN ^ (2 * HasBc.val + 4) + 1 := by
      have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 2 * (Real.log (N : ℝ)) ^ (2 * HasBc.val + 4) by positivity)
      rw [hLNdef]
      exact this
    have h2 : (1 : ℝ) ≤ LN ^ (2 * HasBc.val + 4) := Real.one_le_rpow hLNone (by linarith)
    linarith
  have hlogδ2 : Real.log (((d2n : ℕ) : ℝ)) ≤ Real.log 3 + (2 * HasBc.val + 4) * LLN := by
    have h1 := Real.log_le_log hδ2pos hδ2le
    rw [Real.log_mul (by norm_num) (ne_of_gt (Real.rpow_pos_of_pos hLNp _)),
      Real.log_rpow hLNp] at h1
    linarith [h1]
  have hδ2eps : ((d2n : ℕ) : ℝ)
      ^ (1 / Real.log (Dn : ℝ)) ≤ Real.exp 2 := by
    have hε : 1 / Real.log (Dn : ℝ) ≤ 100 / LN := by
      rw [div_le_div_iff₀ hLΔpos hLNp]
      linarith [hLΔ_low]
    have h1 : (1 / Real.log (Dn : ℝ)) * Real.log (((d2n : ℕ) : ℝ)) ≤ 1 := by
      have h2 : (1 / Real.log (Dn : ℝ)) * Real.log (((d2n : ℕ) : ℝ))
          ≤ (100 / LN) * (Real.log 3 + (2 * HasBc.val + 4) * LLN) :=
        mul_le_mul hε hlogδ2 (Real.log_nonneg hδ2ge1) (by positivity)
      have h3 : (100 / LN) * (Real.log 3 + (2 * HasBc.val + 4) * LLN) ≤ 1 := by
        rw [div_mul_eq_mul_div, div_le_one hLNp]
        linarith [hthresh]
      linarith [h2, h3]
    rw [Real.rpow_def_of_pos hδ2pos]
    calc Real.exp (Real.log (((d2n : ℕ) : ℝ))
          * (1 / Real.log (Dn : ℝ)))
        = Real.exp ((1 / Real.log (Dn : ℝ))
            * Real.log (((d2n : ℕ) : ℝ))) := by rw [mul_comm]
      _ ≤ Real.exp 1 := Real.exp_le_exp.mpr h1
      _ ≤ Real.exp 2 := Real.exp_le_exp.mpr (by norm_num)
  have hMcge1 : (1 : ℝ) ≤ (Mcn : ℝ) := by
    rw [hMcndef, Work.FIChain.Mc]
    have h1 : (0 : ℝ) < Real.sqrt (N : ℝ) * (Real.log (N : ℝ)) ^ (HasBc.val + 2) :=
      mul_pos (Real.sqrt_pos.mpr hNpos) (Real.rpow_pos_of_pos hLNpos _)
    exact_mod_cast Nat.ceil_pos.mpr h1
  have hMcδ2 : Real.log ((Mcn : ℝ) * ((d2n : ℕ) : ℝ)) ≤ LN := by
    have h1 : (Dn : ℝ)
        * ((Mcn : ℝ) * ((d2n : ℕ) : ℝ)) ≤ (Submission.Rcut N : ℝ) := by
      have h := hc7
      rw [Work.FIChain.Dc, Work.FITop.Dcut] at h
      exact_mod_cast h
    have h2 : (1 : ℝ) ≤ (Dn : ℝ) := by exact_mod_cast (by omega : 1 ≤ Dn)
    have h3 : (Submission.Rcut N : ℝ) ≤ (N : ℝ) := by exact_mod_cast Submission.Rcut_le_self N
    have h4 : (0 : ℝ) ≤ (Mcn : ℝ) * ((d2n : ℕ) : ℝ) :=
      mul_nonneg (le_trans zero_le_one hMcge1) hδ2pos.le
    have h5 : (Mcn : ℝ) * ((d2n : ℕ) : ℝ) ≤ (N : ℝ) := by nlinarith only [h1, h2, h3, h4]
    calc Real.log ((Mcn : ℝ) * ((d2n : ℕ) : ℝ))
        ≤ Real.log (N : ℝ) := Real.log_le_log (by positivity) h5
      _ = LN := rfl
  have hC5le : Submission.ASP.L6 Submission.ASP.FIgtil N
      (sr * (Zn : ℝ)) (sr * Yr)
      ≤ C6 * (1 + LLN) := hC6le N hNX6 _ le_rfl
  have hC5pos : 0 ≤ C6 * (1 + LLN) := by
    have h1 : 0 < 1 + LLN := by linarith
    exact mul_nonneg hC6pos.le h1.le
  have hE3le : Abar * (C6 * (1 + LLN))
        * (((d2n : ℕ) : ℝ) ^ (1 / Real.log (Dn : ℝ))
            * Cs * Real.exp (32 * max Chb 1) * C1p / Real.log (Dn : ℝ))
      + Real.log ((Mcn : ℝ) * ((d2n : ℕ) : ℝ))
          * (Abar * LN ^ (-(3 : ℤ)))
      ≤ (200 * C6 * Real.exp 2 * Ksie * Real.exp (32 * max Chb 1) * C1p + 1)
          * (Abar * (LLN / LN)) := by
    have hA0 : 0 ≤ Abar := hAbar0
    have hE0 : 0 ≤ Real.exp (32 * max Chb 1) := (Real.exp_pos _).le
    -- first term
    have h1 : (((d2n : ℕ) : ℝ) ^ (1 / Real.log (Dn : ℝ))
          * Cs * Real.exp (32 * max Chb 1) * C1p / Real.log (Dn : ℝ))
        ≤ 100 * Real.exp 2 * Ksie * Real.exp (32 * max Chb 1) * C1p * (1 / LN) := by
      have hε : 1 / Real.log (Dn : ℝ) ≤ 100 / LN := by
        rw [div_le_div_iff₀ hLΔpos hLNp]
        linarith [hLΔ_low]
      have hnum : ((d2n : ℕ) : ℝ) ^ (1 / Real.log (Dn : ℝ))
            * Cs * Real.exp (32 * max Chb 1) * C1p
          ≤ Real.exp 2 * Ksie * Real.exp (32 * max Chb 1) * C1p := by
        have h1' : ((d2n : ℕ) : ℝ) ^ (1 / Real.log (Dn : ℝ)) * Cs ≤ Real.exp 2 * Ksie :=
          mul_le_mul hδ2eps hCsle (le_of_lt hCs0) (Real.exp_pos 2).le
        have h2' : ((d2n : ℕ) : ℝ) ^ (1 / Real.log (Dn : ℝ)) * Cs * Real.exp (32 * max Chb 1)
            ≤ Real.exp 2 * Ksie * Real.exp (32 * max Chb 1) :=
          mul_le_mul_of_nonneg_right h1' hE0
        exact mul_le_mul_of_nonneg_right h2' hC1ppos.le
      calc ((d2n : ℕ) : ℝ) ^ (1 / Real.log (Dn : ℝ))
            * Cs * Real.exp (32 * max Chb 1) * C1p / Real.log (Dn : ℝ)
          = (((d2n : ℕ) : ℝ) ^ (1 / Real.log (Dn : ℝ))
              * Cs * Real.exp (32 * max Chb 1) * C1p) * (1 / Real.log (Dn : ℝ)) := by
            rw [div_eq_mul_one_div]
        _ ≤ (Real.exp 2 * Ksie * Real.exp (32 * max Chb 1) * C1p) * (100 / LN) :=
            mul_le_mul hnum hε (by positivity) (by positivity)
        _ = 100 * Real.exp 2 * Ksie * Real.exp (32 * max Chb 1) * C1p * (1 / LN) := by
            rw [div_eq_mul_one_div]; ring
    have h2 : Abar * (C6 * (1 + LLN))
          * (((d2n : ℕ) : ℝ) ^ (1 / Real.log (Dn : ℝ))
              * Cs * Real.exp (32 * max Chb 1) * C1p / Real.log (Dn : ℝ))
        ≤ 200 * C6 * Real.exp 2 * Ksie * Real.exp (32 * max Chb 1) * C1p * (Abar * (LLN / LN)) := by
      have h3 : C6 * (1 + LLN) ≤ C6 * (2 * LLN) :=
        mul_le_mul_of_nonneg_left (by linarith [hLLNone]) hC6pos.le
      have h4 : Abar * (C6 * (1 + LLN))
            * (((d2n : ℕ) : ℝ) ^ (1 / Real.log (Dn : ℝ))
                * Cs * Real.exp (32 * max Chb 1) * C1p / Real.log (Dn : ℝ))
          ≤ Abar * (C6 * (2 * LLN))
            * (100 * Real.exp 2 * Ksie * Real.exp (32 * max Chb 1) * C1p * (1 / LN)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h3 hA0) h1 (by positivity) (by positivity)
      refine le_trans h4 (le_of_eq ?_)
      rw [div_eq_mul_one_div]
      ring
    -- second term
    have h5 : Real.log ((Mcn : ℝ) * ((d2n : ℕ) : ℝ))
          * (Abar * LN ^ (-(3 : ℤ))) ≤ Abar * (LLN / LN) := by
      have hlogpos : 0 ≤ Real.log ((Mcn : ℝ) * ((d2n : ℕ) : ℝ)) := by
        apply Real.log_nonneg
        have h7 : (1 : ℝ) ≤ (Mcn : ℝ) := hMcge1
        nlinarith only [hδ2ge1, h7]
      have h6 : Real.log ((Mcn : ℝ) * ((d2n : ℕ) : ℝ))
            * (Abar * LN ^ (-(3 : ℤ))) ≤ LN * (Abar * LN ^ (-(3 : ℤ))) :=
        mul_le_mul_of_nonneg_right hMcδ2 (mul_nonneg hA0 hLNp3)
      refine le_trans h6 ?_
      have h7 : LN * (Abar * LN ^ (-(3 : ℤ))) = Abar * (1 / LN ^ 2) := by
        rw [show LN ^ (-(3 : ℤ)) = (LN ^ 3)⁻¹ by simp [zpow_neg]]
        have hLne : LN ≠ 0 := ne_of_gt hLNp
        field_simp
      rw [h7]
      have h8 : Abar * (1 / LN ^ 2) ≤ Abar * (LLN / LN) := by
        refine mul_le_mul_of_nonneg_left ?_ hA0
        rw [one_div, ← hLp2]
        exact zpow_two_le_div hLNone hLLNone
      exact h8
    linarith [h2, h5]
  -- ## 6c. the E-values and the §6 pointwise bound
  set E1 : ℝ := K1 * Abar
      * (CB1 * LN ^ 3 * (Real.log (Zn : ℝ)) ^ (-(5 : ℤ)) + LN ^ (-(2 : ℤ))) with hE1def
  set E2 : ℝ := K2 * Abar
      * (CB1 * LN ^ 3 * (1 + Real.log ((Dn : ℝ) * (Zn : ℝ) + 2))
          * (Real.log (Zn : ℝ)) ^ (-(6 : ℤ)) + LN ^ (-(2 : ℤ))) with hE2def
  set E3 : ℝ := Abar * (C6 * (1 + LLN))
        * (((d2n : ℕ) : ℝ) ^ (1 / Real.log (Dn : ℝ))
            * Cs * Real.exp (32 * max Chb 1) * C1p / Real.log (Dn : ℝ))
      + Real.log ((Mcn : ℝ) * ((d2n : ℕ) : ℝ))
          * (Abar * LN ^ (-(3 : ℤ))) with hE3def
  set E4 : ℝ := LN * ((Jn : ℝ)
      * ((Kbp * Abar * LN ^ (-(4 : ℤ))) * (1 + Real.log (Dn : ℝ)))) with hE4def
  set E5 : ℝ := K3 * Abar * (LLN / LN) with hE5def
  set E6 : ℝ := Real.log (Zn : ℝ)
      * Work.FIChain.AcountAtilC (Zn) with hE6def
  have hε0 : 0 < 1 / Real.log (Dn : ℝ) := div_pos one_pos hLΔpos
  have hε1 : 1 / Real.log (Dn : ℝ) ≤ 1 := by
    rw [div_le_one hLΔpos]; exact hLΔ1
  have hεΔ : (1 / Real.log (Dn : ℝ)) * Real.log (Dn : ℝ) = 1 :=
    div_mul_cancel₀ _ (ne_of_gt hLΔpos)
  have hEnn : 0 ≤ E1 + E2 + E3 := by
    have h1 : 0 ≤ E1 := by
      rw [hE1def]
      refine mul_nonneg (mul_nonneg hK1pos.le hAbar0) ?_
      refine add_nonneg (mul_nonneg (mul_nonneg hCB1pos.le (pow_nonneg hLNp.le 3)) ?_) ?_
      · rw [show (Real.log (Zn : ℝ)) ^ (-(5 : ℤ))
            = ((Real.log (Zn : ℝ)) ^ 5)⁻¹ by simp [zpow_neg]]
        exact inv_nonneg.mpr (pow_nonneg hM0logpos.le 5)
      · rw [show LN ^ (-(2 : ℤ)) = (LN ^ 2)⁻¹ by simp [zpow_neg]]
        exact inv_nonneg.mpr (pow_nonneg hLNp.le 2)
    have h2 : 0 ≤ E2 := by
      rw [hE2def]
      refine mul_nonneg (mul_nonneg hK2pos.le hAbar0) ?_
      refine add_nonneg (mul_nonneg hB2nn ?_) ?_
      · rw [show (Real.log (Zn : ℝ)) ^ (-(6 : ℤ))
            = ((Real.log (Zn : ℝ)) ^ 6)⁻¹ by simp [zpow_neg]]
        exact inv_nonneg.mpr (pow_nonneg hM0logpos.le 6)
      · rw [show LN ^ (-(2 : ℤ)) = (LN ^ 2)⁻¹ by simp [zpow_neg]]
        exact inv_nonneg.mpr (pow_nonneg hLNp.le 2)
    have h3 : 0 ≤ E3 := by
      rw [hE3def]
      refine add_nonneg (mul_nonneg (mul_nonneg hAbar0 hC5pos) ?_) ?_
      · refine div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ?_ hCs0.le) (Real.exp_pos _).le) hC1ppos.le)
          hLΔpos.le
        exact Real.rpow_nonneg (by positivity) _
      · refine mul_nonneg (Real.log_nonneg ?_) (mul_nonneg hAbar0 hLNp3)
        have h7 : (1 : ℝ) ≤ (Mcn : ℝ) := hMcge1
        nlinarith only [hδ2ge1, h7]
    linarith [h1, h2, h3]
  have hE4nn : 0 ≤ E4 := by
    rw [hE4def]
    refine mul_nonneg hLNp.le (mul_nonneg ?_ ?_)
    · exact_mod_cast Nat.zero_le _
    · exact mul_nonneg (mul_nonneg (mul_nonneg hKbp.le hAbar0) hLNp4) (by linarith [hLΔpos])
  have hE5nn : 0 ≤ E5 := by
    rw [hE5def]
    exact mul_nonneg (mul_nonneg hK3pos.le hAbar0) (div_nonneg hLLN0 hLNp.le)
  have hAd : Submission.ASP.Approx Work.FIChain.atilc Submission.ASP.FIgtil
      (Submission.ASP.rtildeFull Submission.ASP.FIr Submission.ASP.FIg Submission.ASP.FIgtil
        Submission.ASP.FIa) (N : ℝ) :=
    Submission.ASP.approx_atil Submission.ASP.FIa Submission.ASP.FIg Submission.ASP.FIr
      Submission.ASP.FIgtil (N : ℝ) (Submission.ASP.FI_approx (N : ℝ))
  have hRemUse : ∀ m : ℕ, m ≤ N →
      Submission.ASP.RemainderSum
        (Submission.ASP.rtildeFull Submission.ASP.FIr Submission.ASP.FIg Submission.ASP.FIgtil
          Submission.ASP.FIa) (Submission.Rcut N) m ≤ Abar * LN ^ (-(3 : ℤ)) := by
    intro m hm
    have h1 := hRemAll N hNXr m hm
    have h2 : (Real.log (N : ℝ)) ^ (-(3 : ℝ)) = LN ^ (-(3 : ℤ)) := by
      rw [hLNdef, show (-(3 : ℝ)) = ((-3 : ℤ) : ℝ) by norm_num]
      exact Real.rpow_intCast _ _
    rw [h2] at h1
    exact h1
  have hsrpos : 0 < sr := by rw [hsrdef, Work.FIChain.sc]; positivity
  have hYrpos : 0 < Yr := by rw [hYrdef]; exact hc3
  have hscYc_pos : 0 < sr * Yr := mul_pos hsrpos hYrpos
  -- ## 6d. the pointwise (4.5) and (5.1) estimates
  have hTsumAt : ∀ M ∈ Finset.Icc Zn M1n,
      |Submission.ASP.Tsum Work.FIChain.atilc lam (N : ℝ) (M : ℝ) - Htil * Abar| ≤ E1 := by
    intro M hM
    obtain ⟨hM1, hM2⟩ := Finset.mem_Icc.mp hM
    have hM256 : 256 ≤ M := le_trans hs1 hM1
    have hMN : M ≤ N := le_trans hM2 hs3
    have hM2' : 2 ≤ M := by omega
    have hlogMle : Real.log (Zn : ℝ) ≤ Real.log (M : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast hM1)
    have hlog4 : Real.log (N : ℝ) ≤ 4 * Real.log (M : ℝ) := by
      have h := hs4
      linarith only [h, hlogMle]
    have hΔM : Dn * M ≤ Submission.Rcut N := by
      have h1 : Dn * M ≤ Dn * M1n := Nat.mul_le_mul_left _ hM2
      refine le_trans h1 ?_
      have h2 := hs15
      rw [Work.FIChain.Dc, Work.FITop.Dcut] at h2
      exact h2
    have hΔ2 : Dn ^ 2 ≤ M := le_trans hs6 hM1
    have hres := hTsumUse Work.FIChain.atilc
      (Submission.ASP.rtildeFull Submission.ASP.FIr Submission.ASP.FIg Submission.ASP.FIgtil
        Submission.ASP.FIa) lam N M (Submission.Rcut N) Dn Abar (Abar * LN ^ (-(3 : ℤ)))
      (CB1 * LN ^ 3)
      (by omega) hM2' hMN hlog4 (fun n => atilc_nonneg n) rfl hAd hRemUse
      (mul_nonneg hAbar0 hLNp3) (le_of_eq rfl) hΔM hΔ2 (by omega) hlam1 hΔsupp hlam_sq
      hlam_le hB1'
    rw [hH1eq] at hres
    refine le_trans hres ?_
    rw [hE1def]
    refine mul_le_mul_of_nonneg_left (add_le_add ?_ le_rfl) (mul_nonneg hK1pos.le hAbar0)
    exact mul_le_mul_of_nonneg_left (zpow_neg_anti hM0logpos hlogMle 5) (by positivity)
  have hTpoint : ∀ y ∈ Set.Icc (Yr) (Real.exp 1 * Yr),
      |Submission.ASP.Tsum Work.FIChain.atilc lam (N : ℝ) y - Htil * Abar| ≤ E1 := by
    intro y hy
    obtain ⟨hy1, hy2⟩ := Set.mem_Icc.mp hy
    have hy0 : 0 ≤ y := le_trans hc3.le hy1
    rw [Tsum_floorC Work.FIChain.atilc lam (N : ℝ) y hy0]
    exact hTsumAt ⌊y⌋₊ (Finset.mem_Icc.mpr ⟨Nat.floor_mono hy1, Nat.floor_mono hy2⟩)
  have hTsum2At : ∀ M ∈ Finset.Icc Zn M1n,
      |Submission.ASP.Tsum2 Work.FIChain.atilc lam (N : ℝ) (M : ℝ) (Zn : ℝ)| ≤ E2 := by
    intro M hM
    obtain ⟨hM1, hM2⟩ := Finset.mem_Icc.mp hM
    have hM256 : 256 ≤ M := le_trans hs1 hM1
    have hMN : M ≤ N := le_trans hM2 hs3
    have hlogMle : Real.log (Zn : ℝ) ≤ Real.log (M : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast hM1)
    have hlogMle1 : Real.log (M : ℝ) ≤ Real.log (M1n : ℝ) :=
      Real.log_le_log (by exact_mod_cast (by omega : 1 ≤ M)) (by exact_mod_cast hM2)
    have hlogM : (Real.log (M : ℝ)) ^ 6 ≤ (M : ℝ) ^ ((3 : ℝ) / 16) := by
      have h1 : (Real.log (M : ℝ)) ^ 6 ≤ (Real.log (M1n : ℝ)) ^ 6 :=
        pow_le_pow_left₀ (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ M))) hlogMle1 6
      refine le_trans h1 (le_trans hs5 ?_)
      exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hM1) (by norm_num)
    have hΔMP : Dn * M * Zn ≤ Submission.Rcut N := by
      have h1 : Dn * M * Zn ≤ Dn * M1n * Zn :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hM2)
      refine le_trans h1 ?_
      have h2 := hs14
      rw [Work.FIChain.Dc, Work.FITop.Dcut] at h2
      exact h2
    have hΔ4 : Dn ^ 4 ≤ M := le_trans hs7 hM1
    have hres := hTsum2Use Work.FIChain.atilc
      (Submission.ASP.rtildeFull Submission.ASP.FIr Submission.ASP.FIg Submission.ASP.FIgtil
        Submission.ASP.FIa) lam N M Zn (Submission.Rcut N) Dn Abar (Abar * LN ^ (-(3 : ℤ)))
      (CB1 * LN ^ 3 * (1 + Real.log ((Dn : ℝ) * (Zn : ℝ) + 2)))
      (by omega) (by omega) (by omega) (le_trans (by norm_num : (2 : ℕ) ≤ 256) hs1) hMN
      (le_trans hs2 hs3) hM256 hlogM (fun n => atilc_nonneg n)
      (fun n hn => atilc_eq_zero_of_not_sqfree hn) rfl hAd hRemUse
      (mul_nonneg hAbar0 hLNp3) (le_of_eq rfl) hΔMP hΔ4 hΔsupp hlam_sq hlam_le hB2
    refine le_trans hres ?_
    rw [hE2def]
    refine mul_le_mul_of_nonneg_left (add_le_add ?_ le_rfl) (mul_nonneg hK2pos.le hAbar0)
    exact mul_le_mul_of_nonneg_left (zpow_neg_anti hM0logpos hlogMle 6) hB2nn
  have hT2point : ∀ y ∈ Set.Icc (Yr) (Real.exp 1 * Yr),
      |Submission.ASP.Tsum2 Work.FIChain.atilc lam (N : ℝ) y (Zn : ℝ)| ≤ E2 := by
    intro y hy
    obtain ⟨hy1, hy2⟩ := Set.mem_Icc.mp hy
    have hy0 : 0 ≤ y := le_trans hc3.le hy1
    rw [Tsum2_floor_yC Work.FIChain.atilc lam (N : ℝ) y (Zn : ℝ) hy0]
    exact hTsum2At ⌊y⌋₊ (Finset.mem_Icc.mpr ⟨Nat.floor_mono hy1, Nat.floor_mono hy2⟩)
  have hS1point : ∀ y ∈ Set.Icc (Yr) (Real.exp 1 * Yr),
      |Submission.ASP.S1 Work.FIChain.atilc lam N (sr * y)
        (sr * (Zn : ℝ))| ≤ E3 := by
    intro y hy
    obtain ⟨hy1, hy2⟩ := Set.mem_Icc.mp hy
    have hsypos : 0 < sr * y :=
      mul_pos (by rw [hsrdef, Work.FIChain.sc]; positivity) (lt_of_lt_of_le hc3 hy1)
    have hscYc_le : sr * Yr ≤ sr * y :=
      mul_le_mul_of_nonneg_left hy1 (by rw [hsrdef, Work.FIChain.sc]; positivity)
    have hδ2 : ∀ b c : ℕ, sr * y < (b : ℝ) →
        sr * (Zn : ℝ) < (c : ℝ) → N / (b * c) ≤ d2n := by
      intro b c hb hc
      have hcb : (0 : ℝ) < (c : ℝ) := lt_of_lt_of_le (by positivity) (le_of_lt hc)
      have hb' : sr * Yr < (b : ℝ) := lt_of_le_of_lt hscYc_le hb
      have h2 : (sr * Yr) * (sr * (Zn : ℝ))
          < (b : ℝ) * (c : ℝ) :=
        mul_lt_mul hb' (le_of_lt hc) (mul_pos (by rw [hsrdef, Work.FIChain.sc]; positivity) (by positivity))
          (by positivity)
      have h5 : (sr * Yr) * (sr * (Zn : ℝ))
          = sr ^ 2 * Yr * (Zn : ℝ) := by ring
      rw [h5] at h2
      have h6 : (0 : ℝ) < 2 * LN ^ (2 * HasBc.val + 4) := by positivity
      have h4 : (N : ℝ) < (b : ℝ) * (c : ℝ) * (2 * LN ^ (2 * HasBc.val + 4)) := by
        calc (N : ℝ) ≤ 2 * (sr ^ 2 * Yr * (Zn : ℝ) * LN ^ (2 * HasBc.val + 4)) := hs13
          _ = (sr ^ 2 * Yr * (Zn : ℝ)) * (2 * LN ^ (2 * HasBc.val + 4)) := by ring
          _ < ((b : ℝ) * (c : ℝ)) * (2 * LN ^ (2 * HasBc.val + 4)) :=
              mul_lt_mul_of_pos_right h2 h6
      have hbcpos : (0 : ℝ) < (b : ℝ) * (c : ℝ) := mul_pos (by linarith only [hsypos, hb]) hcb
      have h9 : (2 * LN ^ (2 * HasBc.val + 4)) ≤ (d2n : ℝ) := by
        rw [hd2ndef, Work.FIChain.d2c]
        exact Nat.le_ceil _
      have h10 : (N : ℝ) < (b : ℝ) * (c : ℝ) * (d2n : ℝ) :=
        lt_of_lt_of_le h4 (mul_le_mul_of_nonneg_left h9 hbcpos.le)
      have h11 : N < b * c * d2n := by exact_mod_cast h10
      exact Nat.div_le_of_le_mul (le_of_lt h11)
    have hMran : ∀ c ∈ Submission.ASP.cseg N (sr * (Zn : ℝ)) (sr * y), c ≤ Mcn := by
      intro c hc
      rw [Submission.ASP.cseg, Finset.mem_filter, Submission.ASP.seg, Finset.mem_filter] at hc
      obtain ⟨⟨hcIcc, hcgt⟩, hcle⟩ := hc
      have h1 : (c : ℝ) ≤ (N : ℝ) / (sr * y) := hcle
      have h2 : (N : ℝ) / (sr * y) ≤ (N : ℝ) / (sr * Yr) :=
        div_le_div_of_nonneg_left (by positivity) hscYc_pos hscYc_le
      have h3 : (N : ℝ) / (sr * Yr) ≤ (Mcn : ℝ) := hc8
      exact_mod_cast le_trans (le_trans h1 h2) h3
    have hL : Submission.ASP.L6 Submission.ASP.FIgtil N (sr * (Zn : ℝ))
        (sr * y) ≤ C6 * (1 + LLN) := hC6le N hNX6 _ hscYc_le
    have hres := Submission.ASP.S1_bound_of_sieve Work.FIChain.atilc Submission.ASP.FIgtil
      (Submission.ASP.rtildeFull Submission.ASP.FIr Submission.ASP.FIg Submission.ASP.FIgtil
        Submission.ASP.FIa) lam N (sy := sr * y)
      (sz := sr * (Zn : ℝ)) (δ2 := d2n)
      (Δ := Dn) (M := Mcn) (D := Submission.Rcut N)
      (Y := max (Dn) (d2n))
      (ε := 1 / Real.log (Dn : ℝ)) (C_sieve := Cs) (C₁ := C1p)
      (C₀ := max Chb 1) (C₅ := C6 * (1 + LLN))
      (fun n => atilc_nonneg n) hrho hsypos hδ2 (fun n hn => atilc_eq_zero_of_not_sqfree hn) hAd
      hc5 hsupp hs12 hg1 hgmul (fun n => hgnn n) hc6 hε0 hε1 hεΔ
      (le_max_right _ _) (le_max_left _ _) hC0pos hC0b hC1ppos hCs0.le hprodsubUse hlam_sq hlam_le
      hpos hpos' hMran (by simpa [Work.FIChain.Dc, Work.FITop.Dcut] using hc7) hC5pos hL hCsie'
    refine le_trans hres ?_
    refine add_le_add le_rfl ?_
    refine mul_le_mul_of_nonneg_left (hRemUse N le_rfl) ?_
    exact Real.log_nonneg (by
      have h7 : (1 : ℝ) ≤ (Mcn : ℝ) := hMcge1
      nlinarith [hδ2ge1, h7])
  -- ## 8. the §7 and §8 rates
  have hE4le : (∫ y in Yr..Real.exp 1 * Yr,
        |Submission.ASP.S2 Work.FIChain.atilc lam N y ((Zn : ℝ)) (sr * y)| / y)
      ≤ LN * ((Jn : ℝ)
          * ((Kbp * Abar * LN ^ (-(4 : ℤ))) * (1 + Real.log (Dn : ℝ)))) :=
    Work.FIFinal.abs_smAvg_S2_int_le Work.FIChain.atilc lam N (s := sr)
      (J := Jn) (E := Kbp * Abar * LN ^ (-(4 : ℤ))) (Y := Yr)
      (Δ := Dn) (z := (Zn : ℝ)) (w := Work.FITop.w0)
      rfl hc3 (by omega) (fun ℓ => by simp only [Work.FITop.w0]; positivity)
      (mul_nonneg (mul_nonneg hKbp.le hAbar0) hLNp4)
      (by omega) (fun ℓ _ => le_of_eq rfl) hΔsupp hlam_le
      (fun n hn => atilc_eq_zero_of_not_sqfree hn) (hBwinRaw N hNxbp)
  have hJle : (Jn : ℝ) ≤ LN := by
    set a : ℝ := Real.log ((N : ℝ) ^ ((1 : ℝ) / 4 - 2 * Work.FIChain.etac)
      / (2 * (Real.log (N : ℝ)) ^ (HasBc.val + 2))) with hadef
    have harg_ge1 : (1 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 4 - 2 * Work.FIChain.etac)
        / (2 * (Real.log (N : ℝ)) ^ (HasBc.val + 2)) := by
      rw [le_div_iff₀ (by positivity)]
      have h1 : (Real.log (N : ℝ)) ^ (HasBc.val + 2)
          ≤ (Real.log (N : ℝ)) ^ ((⌈HasBc.val + 2⌉₊ : ℕ) : ℝ) := by
        refine Real.rpow_le_rpow_of_exponent_le hLNone ?_
        exact_mod_cast Nat.le_ceil (HasBc.val + 2)
      have h2 : 2 * (Real.log (N : ℝ)) ^ ((⌈HasBc.val + 2⌉₊ : ℕ) : ℝ) ≤ (N : ℝ) ^ ((3 : ℝ) / 16) := by
        have h := hXJ (N : ℝ) (le_trans (Nat.le_ceil XJ) (by exact_mod_cast hNXJ))
        rwa [← Real.rpow_natCast] at h
      have h3 : ((1 : ℝ) / 4 - 2 * Work.FIChain.etac) = 3 / 16 := by
        norm_num [Work.FIChain.etac]
      rw [h3]
      linarith [h1, h2]
    have ha0 : 0 ≤ a := by rw [hadef]; exact Real.log_nonneg harg_ge1
    have hnum : a ≤ LN / 4 := by
      rw [hadef]
      have harg_le : (N : ℝ) ^ ((1 : ℝ) / 4 - 2 * Work.FIChain.etac)
          / (2 * (Real.log (N : ℝ)) ^ (HasBc.val + 2)) ≤ (N : ℝ) ^ ((1 : ℝ) / 4) := by
        rw [div_le_iff₀ (by positivity)]
        have h2 : (1 : ℝ) ≤ 2 * (Real.log (N : ℝ)) ^ (HasBc.val + 2) := by
          have h3 := Real.one_le_rpow hLNone (by linarith : (0 : ℝ) ≤ HasBc.val + 2)
          linarith
        have h4 : (N : ℝ) ^ ((1 : ℝ) / 4 - 2 * Work.FIChain.etac) ≤ (N : ℝ) ^ ((1 : ℝ) / 4) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num [Work.FIChain.etac])
        calc (N : ℝ) ^ ((1 : ℝ) / 4 - 2 * Work.FIChain.etac)
            = (N : ℝ) ^ ((1 : ℝ) / 4 - 2 * Work.FIChain.etac) * 1 := by ring
          _ ≤ (N : ℝ) ^ ((1 : ℝ) / 4 - 2 * Work.FIChain.etac)
                * (2 * (Real.log (N : ℝ)) ^ (HasBc.val + 2)) :=
              mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hNpos.le _)
          _ ≤ (N : ℝ) ^ ((1 : ℝ) / 4) * (2 * (Real.log (N : ℝ)) ^ (HasBc.val + 2)) :=
              mul_le_mul_of_nonneg_right h4 (by positivity)
      have hpos : 0 < (N : ℝ) ^ ((1 : ℝ) / 4 - 2 * Work.FIChain.etac)
          / (2 * (Real.log (N : ℝ)) ^ (HasBc.val + 2)) := lt_of_lt_of_le zero_lt_one harg_ge1
      calc Real.log ((N : ℝ) ^ ((1 : ℝ) / 4 - 2 * Work.FIChain.etac)
            / (2 * (Real.log (N : ℝ)) ^ (HasBc.val + 2)))
          ≤ Real.log ((N : ℝ) ^ ((1 : ℝ) / 4)) := Real.log_le_log hpos harg_le
        _ = LN / 4 := by rw [Real.log_rpow hNpos, hLNdef]; ring
    rw [hJndef, Work.FIChain.Jc]
    have hlog2 : (0.5 : ℝ) ≤ Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    have hlog2pos : (0 : ℝ) < Real.log 2 := by linarith
    have hceil : (↑⌈a / Real.log 2⌉₊ : ℝ) ≤ a / Real.log 2 + 1 :=
      le_of_lt (Nat.ceil_lt_add_one (div_nonneg ha0 (Real.log_nonneg (by norm_num))))
    have hx1 : a / Real.log 2 ≤ 2 * a := by
      rw [div_le_iff₀ hlog2pos]
      calc a = a * 1 := by ring
        _ ≤ a * (2 * Real.log 2) := mul_le_mul_of_nonneg_left (by linarith) ha0
        _ = 2 * a * Real.log 2 := by ring
    have hx2 : 2 * a ≤ LN / 2 := by linarith [hnum]
    have hx3 : LN / 2 + 1 ≤ LN := by linarith [hLNbig]
    calc (↑⌈a / Real.log 2⌉₊ : ℝ) ≤ a / Real.log 2 + 1 := hceil
      _ ≤ 2 * a + 1 := add_le_add_left hx1 1
      _ ≤ LN / 2 + 1 := add_le_add_left hx2 1
      _ ≤ LN := hx3
  have hE4rate : LN * ((Jn : ℝ) * ((Kbp * Abar * LN ^ (-(4 : ℤ)))
        * (1 + Real.log (Dn : ℝ))))
      ≤ (4 * Kbp) * (Abar * (LLN / LN)) := by
    have h1 : 1 + Real.log (Dn : ℝ) ≤ 2 * LN := by linarith [hLΔ_le, hLNone]
    have h1n : 0 ≤ 1 + Real.log (Dn : ℝ) := by linarith [hLΔpos]
    have h2 : (Jn : ℝ) * (1 + Real.log (Dn : ℝ)) ≤ 2 * LN ^ 2 := by
      calc (Jn : ℝ) * (1 + Real.log (Dn : ℝ)) ≤ LN * (1 + Real.log (Dn : ℝ)) :=
            mul_le_mul_of_nonneg_right hJle h1n
        _ ≤ LN * (2 * LN) := mul_le_mul_of_nonneg_left h1 hLNp.le
        _ = 2 * LN ^ 2 := by ring
    have h3 : LN * ((Jn : ℝ) * ((Kbp * Abar * LN ^ (-(4 : ℤ))) * (1 + Real.log (Dn : ℝ))))
        = (LN * (Kbp * Abar * LN ^ (-(4 : ℤ)))) * ((Jn : ℝ) * (1 + Real.log (Dn : ℝ))) := by
      ring
    rw [h3]
    have h4 : (LN * (Kbp * Abar * LN ^ (-(4 : ℤ)))) * ((Jn : ℝ) * (1 + Real.log (Dn : ℝ)))
        ≤ (LN * (Kbp * Abar * LN ^ (-(4 : ℤ)))) * (2 * LN ^ 2) :=
      mul_le_mul_of_nonneg_left h2 (mul_nonneg hLNp.le (mul_nonneg (mul_nonneg hKbp.le hAbar0) hLNp4))
    refine le_trans h4 ?_
    have h5 : (LN * (Kbp * Abar * LN ^ (-(4 : ℤ)))) * (2 * LN ^ 2)
        = 2 * Kbp * Abar * (LN ^ (-(1 : ℤ))) := by
      rw [show LN ^ (-(4 : ℤ)) = (LN ^ 4)⁻¹ by simp [zpow_neg],
        show LN ^ (-(1 : ℤ)) = LN⁻¹ by simp [zpow_neg]]
      have hLne : LN ≠ 0 := ne_of_gt hLNp
      field_simp
    rw [h5]
    have hdiv : LN ^ (-(1 : ℤ)) ≤ LLN / LN := by
      rw [show LN ^ (-(1 : ℤ)) = LN⁻¹ by simp [zpow_neg], inv_eq_one_div]
      rw [div_le_div_iff₀ hLNp hLNp]
      nlinarith [hLLNone, hLNp]
    have h6 : 2 * Kbp * Abar * (LN ^ (-(1 : ℤ))) ≤ 2 * Kbp * Abar * (LLN / LN) :=
      mul_le_mul_of_nonneg_left hdiv (mul_nonneg (mul_nonneg (by norm_num) hKbp.le) hAbar0)
    refine le_trans h6 ?_
    have hX : 0 ≤ Abar * (LLN / LN) := mul_nonneg hAbar0 (by positivity)
    calc 2 * Kbp * Abar * (LLN / LN) = 2 * (Kbp * (Abar * (LLN / LN))) := by ring
      _ ≤ 4 * (Kbp * (Abar * (LLN / LN))) :=
          mul_le_mul_of_nonneg_right (by norm_num) (mul_nonneg hKbp.le hX)
      _ = (4 * Kbp) * (Abar * (LLN / LN)) := by ring
  -- ## 9. the §8 hypothesis at `N`, the (9.12) identity, and the smoothed assembly
  have hS3use : |(∫ y in Work.FIChain.Yc N HasBc.val..(Real.exp 1 * Work.FIChain.Yc N HasBc.val),
      Submission.ASP.S3 Work.FIChain.atilc lam N (Work.FIChain.zc N HasBc.val)
        (Work.FIChain.sc N HasBc.val * y) (Work.FIChain.sc N HasBc.val * Work.FIChain.zc N HasBc.val) / y)| ≤ E5 := by
    have h := hS3N hw1 lam Cs hSI hCsle
    rw [hE5def]
    exact h
  have hE6b : E6 ≤ CE6 * (Abar * (LLN / LN)) := by
    rw [hE6def]
    exact hE6bound Zn (by omega) hc4
  have h912use : |Abar - Submission.ASP.Gprod Submission.ASP.FIg
        * Submission.ASP.Acount Submission.ASP.FIa (N : ℝ)|
      ≤ Submission.ASP.Gprod Submission.ASP.FIg
        * Submission.ASP.Acount Submission.ASP.FIa (N : ℝ)
        * (Cg9 / (Submission.ASP.Gprod Submission.ASP.FIg * LN)) := by
    have h := h912raw N hNX9
    have hR : Submission.ASP.Gprod Submission.ASP.FIg
          * Submission.ASP.Acount Submission.ASP.FIa (N : ℝ)
          * (Cg9 / (Submission.ASP.Gprod Submission.ASP.FIg * LN))
        = Cg9 * Submission.ASP.Acount Submission.ASP.FIa (N : ℝ) / Real.log (N : ℝ) := by
      rw [← hLNdef]
      field_simp
    rw [hR]
    exact h
  have hmain := FI_primeSum_of_estimates_signed lam N Zn Dn
    (Htil := Htil) (G := Submission.ASP.Gprod Submission.ASP.FIg) (H := 4 / Real.pi)
    (E1 := E1) (E2 := E2) (E3 := E3) (E4 := E4) (E5 := E5) (E6 := E6)
    (δ := Cg9 / (Submission.ASP.Gprod Submission.ASP.FIg * LN))
    (Y := Yr) (s := sr) (z := (Zn : ℝ))
    (by omega) hc3 hc1 (by exact_mod_cast (by omega : (0 : ℕ) < Zn)) rfl (by omega)
    (le_trans hs2 hs3) hs11
    hlam1 hΔsupp hTpoint hT2point hS1point hE4le hS3use hEnn hE4nn hE5nn
    (le_of_eq hE6def.symm) hHmulG h912use
  -- ## 10. the four rate bounds and the final constant
  have hE1b : E1 ≤ (K1 * (1024 * CB1 + 1)) * (Abar * (LLN / LN)) := by
    rw [hE1def]
    refine le_trans (mul_le_mul_of_nonneg_left hE1rate (mul_nonneg hK1pos.le hAbar0)) (le_of_eq ?_)
    ring
  have hE2b : E2 ≤ (K2 * (16384 * CB1 + 1)) * (Abar * (LLN / LN)) := by
    rw [hE2def]
    refine le_trans (mul_le_mul_of_nonneg_left hE2rate (mul_nonneg hK2pos.le hAbar0)) (le_of_eq ?_)
    ring
  have hE3b : E3 ≤ (200 * C6 * Real.exp 2 * Ksie * Real.exp (32 * max Chb 1) * C1p + 1)
        * (Abar * (LLN / LN)) := by
    rw [hE3def]
    exact hE3le
  have hE4b : E4 ≤ (4 * Kbp) * (Abar * (LLN / LN)) := by
    rw [hE4def]
    exact hE4rate
  have hE5b : E5 ≤ K3 * (Abar * (LLN / LN)) := by
    rw [hE5def]
    exact le_of_eq (by ring)
  have h912b : |Htil| * Submission.ASP.Gprod Submission.ASP.FIg
        * Submission.ASP.Acount Submission.ASP.FIa (N : ℝ)
        * (Cg9 / (Submission.ASP.Gprod Submission.ASP.FIg * LN))
      ≤ (2 * |Htil| * Cg9 / Submission.ASP.Gprod Submission.ASP.FIg)
          * (Abar * (LLN / LN)) := by
    have hA0 : 0 ≤ Submission.ASP.Acount Submission.ASP.FIa (N : ℝ) := by
      rw [Submission.ASP.Acount, Nat.floor_natCast]
      exact Finset.sum_nonneg (fun n _ => Submission.ASP.FIa_nonneg n)
    have h1 : Submission.ASP.Acount Submission.ASP.FIa (N : ℝ)
        ≤ (2 / Submission.ASP.Gprod Submission.ASP.FIg) * Abar := hAseqG N hNXG
    have h2 : |Htil| * Submission.ASP.Gprod Submission.ASP.FIg
          * Submission.ASP.Acount Submission.ASP.FIa (N : ℝ)
          * (Cg9 / (Submission.ASP.Gprod Submission.ASP.FIg * LN))
        = |Htil| * Submission.ASP.Acount Submission.ASP.FIa (N : ℝ) * Cg9 / LN := by
      field_simp
    rw [h2]
    have h4 : Submission.ASP.Acount Submission.ASP.FIa (N : ℝ) / LN
        ≤ ((2 / Submission.ASP.Gprod Submission.ASP.FIg) * Abar) / LN :=
      div_le_div_of_nonneg_right h1 hLNp.le
    have h3 : |Htil| * Submission.ASP.Acount Submission.ASP.FIa (N : ℝ) * Cg9 / LN
        ≤ |Htil| * ((2 / Submission.ASP.Gprod Submission.ASP.FIg) * Abar) * Cg9 / LN := by
      calc |Htil| * Submission.ASP.Acount Submission.ASP.FIa (N : ℝ) * Cg9 / LN
          = (|Htil| * Cg9) * (Submission.ASP.Acount Submission.ASP.FIa (N : ℝ) / LN) := by ring
        _ ≤ (|Htil| * Cg9) * (((2 / Submission.ASP.Gprod Submission.ASP.FIg) * Abar) / LN) :=
            mul_le_mul_of_nonneg_left h4 (mul_nonneg (abs_nonneg _) hCg9pos.le)
        _ = |Htil| * ((2 / Submission.ASP.Gprod Submission.ASP.FIg) * Abar) * Cg9 / LN := by ring
    refine le_trans h3 ?_
    have h5 : |Htil| * ((2 / Submission.ASP.Gprod Submission.ASP.FIg) * Abar) * Cg9 / LN
        = (2 * |Htil| * Cg9 / Submission.ASP.Gprod Submission.ASP.FIg) * (Abar / LN) := by
      field_simp
    rw [h5]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h6 : (1 : ℝ) ≤ LLN := hLLNone
    calc Abar / LN = Abar * (1 / LN) := by rw [div_eq_mul_one_div]
      _ ≤ Abar * (LLN / LN) := by
          refine mul_le_mul_of_nonneg_left ?_ hAbar0
          rw [div_le_div_iff₀ hLNp hLNp]
          nlinarith [h6, hLNp]
  have hsum : (E1 + E2 + E3 + E4 + E5) + E6
      + |Htil| * Submission.ASP.Gprod Submission.ASP.FIg
          * Submission.ASP.Acount Submission.ASP.FIa (N : ℝ)
          * (Cg9 / (Submission.ASP.Gprod Submission.ASP.FIg * LN))
      ≤ KX * (Abar * (LLN / LN)) :=
    add_const_mul_le (add_const_mul_le (add_const_mul_le (add_const_mul_le
      (add_const_mul_le (add_const_mul_le hE1b hE2b) hE3b) hE4b) hE5b) hE6b) h912b
  refine le_trans hmain (le_trans hsum ?_)
  rw [hCfindef]
  have hX0 : 0 ≤ Abar * (LLN / LN) := mul_nonneg hAbar0 (by positivity)
  refine le_trans (mul_le_mul_of_nonneg_right (by linarith : KX ≤ KX + 1) hX0) (le_of_eq ?_)
  ring
end

end Work.FIPiChain
