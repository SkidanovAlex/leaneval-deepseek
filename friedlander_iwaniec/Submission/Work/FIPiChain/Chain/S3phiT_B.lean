/-
# `Submission.Work.FIChain.S3phiT_Bstar` — the `T`-summand of the `§4–§7` estimate

`|Tsum ã λ (x) y − H·Ã(x)| ≪ Ã(x)·loglog x/log x` uniformly in `y ∈ [Yc x HasBc.val, e·Yc x HasBc.val]`
and in `λ` subject to `Work.FIChain.SieveInput`, with the uniform constant `H` of the
`∑_{d≤n}μ(d)g(d)log d → −H` limit (`Work.FIChain.Tsum_uniformAll`).  This is the `(4.5)` estimate of
`Work.FIChain.assemblyC` (§5–§6, with `K` hoisted out of every parameter) plus the `hE1rate`
arithmetic.
-/
import Mathlib
import Submission.Work.FIPiChain.HasB
import Submission.Work.FIChain.Defs
import Submission.Work.FIPiChain.Chain.S3phiBDefs
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
import Submission.Work.FIChain.Tsum_uniformAll
import Submission.Work.FIChain.remainder_all
import Submission.Work.FIChain.FIgtil_tau_div_sum_le
import Submission.Work.FIChain.assemblyC

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Work.FIChain

namespace Work.FIPiChain

variable [HasBc]

open Finset Filter
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **The `T`-summand of the `§4–§7` estimate.** -/
theorem S3phiT_Bstar :
    ∃ K H : ℝ, ∃ x₀ : ℕ, 0 < K ∧ ∀ x : ℕ, x₀ ≤ x → s3phiCond x →
      ∀ lam : ℕ → ℝ, ∀ C_sieve : ℝ,
        SieveInput Submission.ASP.FIgtil (Deltac x) lam C_sieve →
        ∀ y ∈ s3phiYwin x,
          |s3phiT x lam y - H * AcountAtilC x|
            ≤ K * AcountAtilC x * s3phiRate x := by
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
  have hboundFI' : ∃ C : ℝ, ∀ p : ℕ, p.Prime → Submission.ASP.FIgtil p ≤ C / (p : ℝ) :=
    ⟨Chb, hboundFI⟩
  obtain ⟨c9, C9, hC9pos, h9real⟩ := Submission.ASP.FIgtil_sum_19_real
  obtain ⟨K1, H1, hK1pos, hH1pos, hH1tend, hTsumUse⟩ :=
    Tsum_uniformAll hgmul hg1 hgp hboundFI' ⟨c9, C9, h9real⟩
  obtain ⟨CB1, hCB1pos, hB1leUse⟩ := FIgtil_tau_div_sum_le
  obtain ⟨Xr, hRemAll⟩ := remainder_all
  have hev : ∀ᶠ x : ℕ in Filter.atTop, s3phiCond x →
      ∀ lam : ℕ → ℝ, ∀ C_sieve : ℝ,
        SieveInput Submission.ASP.FIgtil (Deltac x) lam C_sieve →
        ∀ y ∈ s3phiYwin x,
          |s3phiT x lam y - H1 * AcountAtilC x|
            ≤ (K1 * (1024 * CB1 + 1) + 1) * AcountAtilC x * s3phiRate x := by
    filter_upwards [scale_factsC HasBc.val hBstar_pos,
      window_marginsC (1 / 64) HasBc.val (by norm_num) (by norm_num) hBstar_pos,
      chainRangeFactsC HasBc.val hBstar_pos,
      Filter.eventually_ge_atTop Xr, Filter.eventually_ge_atTop 3,
      Work.FITop.FI_ev_log_ge_nat 4]
      with x hs hw hch hxr hx3 hLN4
    obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15,
      hs16⟩ := hs
    obtain ⟨hw1, hw2, hw3, hw4, hw5, hw6, hw7⟩ := hw
    intro hcond lam Cs hSI y hy
    have hx3R : (3 : ℝ) ≤ (x : ℝ) := hw6
    have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
    have hLNpos : 0 < Real.log (x : ℝ) := Real.log_pos (by linarith : (1 : ℝ) < (x : ℝ))
    have hLN1 : (1 : ℝ) ≤ Real.log (x : ℝ) := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_three, hx3R])
    have hLLN1 : (1 : ℝ) ≤ Real.log (Real.log (x : ℝ)) := by linarith [hw7]
    set Dn : ℕ := Deltac x with hDndef
    set Zn : ℕ := ⌊Yc x HasBc.val⌋₊ with hZndef
    set M1n : ℕ := ⌊Real.exp 1 * Yc x HasBc.val⌋₊ with hM1ndef
    set LN : ℝ := Real.log (x : ℝ) with hLNdef
    set LLN : ℝ := Real.log (Real.log (x : ℝ)) with hLLNdef
    set Abar : ℝ := AcountAtilC x with hAbardef
    have hLNp : 0 < LN := hLNpos
    have hLNone : (1 : ℝ) ≤ LN := hLN1
    have hLLNone : (1 : ℝ) ≤ LLN := by rw [hLLNdef]; exact hLLN1
    have hLNpow3 : 0 ≤ LN ^ (-(3 : ℤ)) := by
      rw [show LN ^ (-(3 : ℤ)) = (LN ^ 3)⁻¹ by simp [zpow_neg]]
      exact inv_nonneg.mpr (pow_nonneg hLNp.le 3)
    have hAbar0 : 0 ≤ Abar := by
      rw [hAbardef, Work.FIChain.AcountAtilC, Work.FITop.AcountAtil, Submission.ASP.Acount,
        Nat.floor_natCast]
      exact Finset.sum_nonneg (fun n _ => atilc_nonneg n)
    -- the sieve weight
    have hlam1 : lam 1 = 1 := hSI.1
    have hΔsupp : ∀ ν : ℕ, Dn < ν → lam ν = 0 := hSI.2.1
    have hlam_sq : ∀ ν : ℕ, ¬ Squarefree ν → lam ν = 0 := hSI.2.2.1
    have hlam_le : ∀ ν : ℕ, |lam ν| ≤ 1 := hSI.2.2.2.1
    -- the sequence and its remainder
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
        rw [hLNdef, show (-(3 : ℝ)) = ((-3 : ℤ) : ℝ) by norm_num]
        exact Real.rpow_intCast _ _
      rw [h2] at h1
      exact h1
    -- the `B₁`-input
    have hB1 : (∑ ν ∈ (Finset.Icc 1 (Dn)).filter Squarefree,
          |lam ν| * Submission.ASP.FIgtil ν * (ν.divisors.card : ℝ)
            * (∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ))))
        ≤ CB1 * (Real.log (Dn : ℝ)) ^ 3 := by
      refine le_trans (Finset.sum_le_sum ?_) (hB1leUse (Dn) hch.2.2.2.2.2.1)
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
    have hLΔpos : 0 < Real.log (Dn : ℝ) := by
      have h3 : (3 : ℝ) ≤ (Dn : ℝ) := by exact_mod_cast hch.2.2.2.2.2.1
      exact Real.log_pos (by linarith [Real.exp_one_lt_three, h3])
    have hLΔ_le : Real.log (Dn : ℝ) ≤ LN := by
      rw [hLNdef]
      have hDnpos : (0 : ℝ) < (Dn : ℝ) := by
        have h3 : (1 : ℕ) ≤ Dn := le_trans (by norm_num : (1 : ℕ) ≤ 3) hch.2.2.2.2.2.1
        exact_mod_cast (by omega : 0 < Dn)
      exact Real.log_le_log hDnpos (by exact_mod_cast hch.2.2.2.2.1)
    have hB1' : (∑ ν ∈ (Finset.Icc 1 (Dn)).filter Squarefree,
          |lam ν| * Submission.ASP.FIgtil ν * (ν.divisors.card : ℝ)
            * (∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ))))
        ≤ CB1 * LN ^ 3 :=
      le_trans hB1 (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hLΔpos.le hLΔ_le 3) hCB1pos.le)
    -- the `(4.5)` rate
    have hM0logpos : 0 < Real.log (Zn : ℝ) := by
      apply Real.log_pos
      have h256 : (256 : ℝ) ≤ (Zn : ℝ) := by exact_mod_cast hs1
      linarith
    have hlogM0 : LN / 4 ≤ Real.log (Zn : ℝ) := by
      have h := hs4
      linarith
    have hLp2 : LN ^ (-(2 : ℤ)) = (LN ^ 2)⁻¹ := by simp [zpow_neg]
    have hM0p5 : (Real.log (Zn : ℝ)) ^ (-(5 : ℤ)) = ((Real.log (Zn : ℝ)) ^ 5)⁻¹ := by
      simp [zpow_neg]
    have hpow5 : ((Real.log (Zn : ℝ)) ^ 5)⁻¹ ≤ 1024 * (LN ^ 5)⁻¹ := by
      rw [inv_eq_one_div, inv_eq_one_div]
      have hkey : (1024 : ℝ) * (1 / LN ^ 5) = 1024 / LN ^ 5 := by ring
      rw [hkey, div_le_div_iff₀ (pow_pos hM0logpos 5) (pow_pos hLNp 5)]
      have h := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ LN / 4) hlogM0 5
      rw [div_pow] at h
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < (4 : ℝ) ^ 5)] at h
      linarith [h]
    have hkey3 : LN ^ 3 * (LN ^ 5)⁻¹ = (LN ^ 2)⁻¹ := by
      rw [inv_eq_one_div, inv_eq_one_div]
      rw [show LN ^ 3 * (1 / LN ^ 5) = 1 / LN ^ 2 by
        rw [mul_one_div,
          div_eq_div_iff (pow_ne_zero 5 (ne_of_gt hLNp)) (pow_ne_zero 2 (ne_of_gt hLNp))]
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
      have h4 : (1024 : ℝ) * CB1 * (LLN / LN) + LLN / LN
          ≤ (1024 * CB1 + 1) * (LLN / LN) := by
        rw [show (1024 : ℝ) * CB1 * (LLN / LN) + LLN / LN
            = (1024 * CB1 + 1) * (LLN / LN) by ring]
      have h5 : LN ^ (-(2 : ℤ)) = (LN ^ 2)⁻¹ := hLp2
      rw [h5]
      linarith only [h1, h2, h3, h4]
    -- the pointwise-estimate
    have hTsumAt : ∀ M ∈ Finset.Icc Zn M1n,
        |Submission.ASP.Tsum atilc lam (x : ℝ) (M : ℝ) - H1 * Abar| ≤
          K1 * Abar * (CB1 * LN ^ 3 * (Real.log (Zn : ℝ)) ^ (-(5 : ℤ))
            + LN ^ (-(2 : ℤ))) := by
      intro M hM
      obtain ⟨hM1, hM2⟩ := Finset.mem_Icc.mp hM
      have hM256 : 256 ≤ M := le_trans hs1 hM1
      have hMN : M ≤ x := le_trans hM2 hs3
      have hM2' : 2 ≤ M := by omega
      have hlogMle : Real.log (Zn : ℝ) ≤ Real.log (M : ℝ) :=
        Real.log_le_log (by positivity) (by exact_mod_cast hM1)
      have hlog4 : Real.log (x : ℝ) ≤ 4 * Real.log (M : ℝ) := by
        have h := hs4
        linarith only [h, hlogMle]
      have hΔM : Dn * M ≤ Submission.Rcut x := by
        have h1 : Dn * M ≤ Dn * M1n := Nat.mul_le_mul_left _ hM2
        refine le_trans h1 ?_
        have h2 := hs15
        rw [Work.FIChain.Dc, Work.FITop.Dcut] at h2
        exact h2
      have hΔ2 : Dn ^ 2 ≤ M := le_trans hs6 hM1
      have hres := hTsumUse atilc
        (Submission.ASP.rtildeFull Submission.ASP.FIr Submission.ASP.FIg Submission.ASP.FIgtil
          Submission.ASP.FIa) lam x M (Submission.Rcut x) Dn Abar (Abar * LN ^ (-(3 : ℤ)))
        (CB1 * LN ^ 3)
        (by omega) hM2' hMN hlog4 (fun n => atilc_nonneg n) rfl hAd hRemUse
        (mul_nonneg hAbar0 hLNpow3) (le_of_eq rfl) hΔM hΔ2 (by omega) hlam1 hΔsupp hlam_sq
        hlam_le hB1'
      refine le_trans hres ?_
      refine mul_le_mul_of_nonneg_left (add_le_add ?_ le_rfl) (mul_nonneg hK1pos.le hAbar0)
      exact mul_le_mul_of_nonneg_left (zpow_neg_anti hM0logpos hlogMle 5) (by positivity)
    have hTpoint : ∀ y ∈ Set.Icc (Yc x HasBc.val) (Real.exp 1 * Yc x HasBc.val),
        |Submission.ASP.Tsum atilc lam (x : ℝ) y - H1 * Abar| ≤
          K1 * Abar * (CB1 * LN ^ 3 * (Real.log (Zn : ℝ)) ^ (-(5 : ℤ))
            + LN ^ (-(2 : ℤ))) := by
      intro y hy
      obtain ⟨hy1, hy2⟩ := Set.mem_Icc.mp hy
      have hy0 : 0 ≤ y := le_trans hch.2.2.1.le hy1
      rw [Tsum_floorC atilc lam (x : ℝ) y hy0]
      exact hTsumAt ⌊y⌋₊ (Finset.mem_Icc.mpr ⟨Nat.floor_mono hy1, Nat.floor_mono hy2⟩)
    -- conclude
    have hmain := hTpoint y hy
    have hKnn : 0 ≤ K1 * (1024 * CB1 + 1) + 1 := by positivity
    have hle1 : K1 * Abar * (CB1 * LN ^ 3 * (Real.log (Zn : ℝ)) ^ (-(5 : ℤ))
          + LN ^ (-(2 : ℤ))) ≤ K1 * Abar * ((1024 * CB1 + 1) * (LLN / LN)) :=
      mul_le_mul_of_nonneg_left hE1rate (mul_nonneg hK1pos.le hAbar0)
    have hle2 : K1 * Abar * ((1024 * CB1 + 1) * (LLN / LN))
        ≤ (K1 * (1024 * CB1 + 1) + 1) * (Abar * (LLN / LN)) := by
      have hLLdiv : 0 ≤ LLN / LN := div_nonneg (by linarith [hLLNone]) hLNp.le
      have hAnn : 0 ≤ Abar * (LLN / LN) := mul_nonneg hAbar0 hLLdiv
      have hkey : K1 * Abar * ((1024 * CB1 + 1) * (LLN / LN))
          = K1 * (1024 * CB1 + 1) * (Abar * (LLN / LN)) := by ring
      rw [hkey]
      linarith only [hAnn]
    rw [hAbardef] at hmain
    calc |s3phiT x lam y - H1 * AcountAtilC x|
        = |Submission.ASP.Tsum atilc lam (x : ℝ) y - H1 * AcountAtilC x| := rfl
      _ ≤ K1 * AcountAtilC x * (CB1 * LN ^ 3 * (Real.log (Zn : ℝ)) ^ (-(5 : ℤ))
            + LN ^ (-(2 : ℤ))) := hmain
      _ ≤ K1 * AcountAtilC x * ((1024 * CB1 + 1) * (LLN / LN)) := hle1
      _ ≤ (K1 * (1024 * CB1 + 1) + 1) * (AcountAtilC x * (LLN / LN)) := hle2
      _ = (K1 * (1024 * CB1 + 1) + 1) * AcountAtilC x * s3phiRate x := by
          rw [s3phiRate]
          ring
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp hev
  exact ⟨K1 * (1024 * CB1 + 1) + 1, H1, x₀, by positivity, hx₀⟩

end

end Work.FIPiChain
