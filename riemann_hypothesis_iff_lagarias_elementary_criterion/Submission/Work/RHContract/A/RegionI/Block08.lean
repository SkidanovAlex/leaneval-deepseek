import Mathlib
import Submission.Work.RHContract.A.RegionI.Core
import Submission.Work.RHContract.A.RegionI.blockCert
import Submission.Work.RHContract.A.RegionI.Data11
import Submission.Work.RHContract.A.RegionI.Cuts

/-!  Region I: group certificates.  GENERATED FILE. -/

open scoped BigOperators

namespace Work.RHContract.A.RegionI

noncomputable section

private def xg_280 : Fin 17 → ℕ := fun k => [19441, 181, 37, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_280 : Fin 17 → ℕ := fun k => [19501, 191, 37, 15, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_280 : Fin 17 → ℚ := fun k => [((19231718994518137 : ℚ) / 1000000000000), ((33494406808673 : ℚ) / 200000000000), ((14817649818811 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_280 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨280, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨281, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨281, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨280, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_280 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_280 k + 1) (k.val + 1) < (cut ⟨281, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_280 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_280 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_280 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_280 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_280 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_280 ⟨1, by omega⟩ + 1 ≤ xg_280 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_280 k : ℝ) ≤ Chebyshev.theta ((xg_280 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2203
    · exact Work.RHContract.RegionI.thV_41
    · exact Work.RHContract.RegionI.thV_11
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((19501 : ℕ) : ℝ) ≤ (((286817151289 : ℚ) / 100000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2212
  have hSx : (((226121328479 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 19441, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2203
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_280 k := by decide +kernel
  have hT2 : (∑ k, tg_280 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_280 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_280 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((286817151289 : ℚ) / 100000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_280 k))
      + ((((226121328479 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_280 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_280 (yg_280 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨280, by omega⟩ : ℚ)) (εB := (cut ⟨281, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_280 yg_280 tg_280 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((286817151289 : ℚ) / 100000000000)) (((226121328479 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_281 : Fin 17 → ℕ := fun k => [19501, 191, 37, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_281 : Fin 17 → ℕ := fun k => [19583, 191, 37, 15, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_281 : Fin 17 → ℚ := fun k => [((19320610049101479 : ℚ) / 1000000000000), ((21590538433699 : ℚ) / 125000000000), ((14817649818811 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_281 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨281, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨282, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨282, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨281, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_281 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_281 k + 1) (k.val + 1) < (cut ⟨282, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_281 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_281 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_281 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_281 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_281 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_281 ⟨1, by omega⟩ + 1 ≤ xg_281 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_281 k : ℝ) ≤ Chebyshev.theta ((xg_281 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2212
    · exact Work.RHContract.RegionI.thV_42
    · exact Work.RHContract.RegionI.thV_11
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((19583 : ℕ) : ℝ) ≤ (((358578980513 : ℚ) / 125000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2221
  have hSx : (((28265167543 : ℚ) / 62500000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 19501, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2212
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_281 k := by decide +kernel
  have hT2 : (∑ k, tg_281 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_281 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_281 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((358578980513 : ℚ) / 125000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_281 k))
      + ((((28265167543 : ℚ) / 62500000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_281 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_281 (yg_281 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨281, by omega⟩ : ℚ)) (εB := (cut ⟨282, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_281 yg_281 tg_281 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((358578980513 : ℚ) / 125000000000)) (((28265167543 : ℚ) / 62500000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_282 : Fin 17 → ℕ := fun k => [19583, 191, 37, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_282 : Fin 17 → ℕ := fun k => [19709, 192, 37, 16, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_282 : Fin 17 → ℚ := fun k => [((3881907477057141 : ℚ) / 200000000000), ((21590538433699 : ℚ) / 125000000000), ((14817649818811 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_282 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨282, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨283, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨283, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨282, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_282 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_282 k + 1) (k.val + 1) < (cut ⟨283, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_282 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_282 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_282 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_282 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_282 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_282 ⟨1, by omega⟩ + 1 ≤ xg_282 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_282 k : ℝ) ≤ Chebyshev.theta ((xg_282 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2221
    · exact Work.RHContract.RegionI.thV_42
    · exact Work.RHContract.RegionI.thV_11
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((19709 : ℕ) : ℝ) ≤ (((2869089632433 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2230
  have hSx : (((452242704227 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 19583, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2221
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_282 k := by decide +kernel
  have hT2 : (∑ k, tg_282 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_282 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_282 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2869089632433 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_282 k))
      + ((((452242704227 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_282 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_282 (yg_282 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨282, by omega⟩ : ℚ)) (εB := (cut ⟨283, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_282 yg_282 tg_282 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2869089632433 : ℚ) / 1000000000000)) (((452242704227 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_283 : Fin 17 → ℕ := fun k => [19709, 191, 37, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_283 : Fin 17 → ℕ := fun k => [19793, 192, 37, 16, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_283 : Fin 17 → ℚ := fun k => [((19498514589315383 : ℚ) / 1000000000000), ((21590538433699 : ℚ) / 125000000000), ((14817649818811 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_283 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨283, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨284, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨284, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨283, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_283 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_283 k + 1) (k.val + 1) < (cut ⟨284, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_283 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_283 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_283 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_283 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_283 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_283 ⟨1, by omega⟩ + 1 ≤ xg_283 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_283 k : ℝ) ≤ Chebyshev.theta ((xg_283 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2230
    · exact Work.RHContract.RegionI.thV_42
    · exact Work.RHContract.RegionI.thV_11
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((19793 : ℕ) : ℝ) ≤ (((2869545266419 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2239
  have hSx : (((226121363753 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 19709, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2230
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_283 k := by decide +kernel
  have hT2 : (∑ k, tg_283 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_283 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_283 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2869545266419 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_283 k))
      + ((((226121363753 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_283 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_283 (yg_283 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨283, by omega⟩ : ℚ)) (εB := (cut ⟨284, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_283 yg_283 tg_283 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2869545266419 : ℚ) / 1000000000000)) (((226121363753 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_284 : Fin 17 → ℕ := fun k => [19793, 191, 37, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_284 : Fin 17 → ℕ := fun k => [19889, 192, 37, 16, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_284 : Fin 17 → ℚ := fun k => [((9793767115352641 : ℚ) / 500000000000), ((21590538433699 : ℚ) / 125000000000), ((14817649818811 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_284 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨284, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨285, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨285, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨284, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_284 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_284 k + 1) (k.val + 1) < (cut ⟨285, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_284 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_284 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_284 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_284 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_284 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_284 ⟨1, by omega⟩ + 1 ≤ xg_284 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_284 k : ℝ) ≤ Chebyshev.theta ((xg_284 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2239
    · exact Work.RHContract.RegionI.thV_42
    · exact Work.RHContract.RegionI.thV_11
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((19889 : ℕ) : ℝ) ≤ (((717499709779 : ℚ) / 250000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2248
  have hSx : (((452242750567 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 19793, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2239
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_284 k := by decide +kernel
  have hT2 : (∑ k, tg_284 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_284 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_284 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((717499709779 : ℚ) / 250000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_284 k))
      + ((((452242750567 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_284 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_284 (yg_284 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨284, by omega⟩ : ℚ)) (εB := (cut ⟨285, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_284 yg_284 tg_284 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((717499709779 : ℚ) / 250000000000)) (((452242750567 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_285 : Fin 17 → ℕ := fun k => [19889, 191, 37, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_285 : Fin 17 → ℕ := fun k => [19973, 193, 37, 16, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_285 : Fin 17 → ℚ := fun k => [((19676594681808109 : ℚ) / 1000000000000), ((21590538433699 : ℚ) / 125000000000), ((14817649818811 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_285 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨285, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨286, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨286, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨285, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_285 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_285 k + 1) (k.val + 1) < (cut ⟨286, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_285 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_285 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_285 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_285 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_285 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_285 ⟨1, by omega⟩ + 1 ≤ xg_285 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_285 k : ℝ) ≤ Chebyshev.theta ((xg_285 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2248
    · exact Work.RHContract.RegionI.thV_42
    · exact Work.RHContract.RegionI.thV_11
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((19973 : ℕ) : ℝ) ≤ (((574090054631 : ℚ) / 200000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2257
  have hSx : (((22612138671 : ℚ) / 50000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 19889, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2248
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_285 k := by decide +kernel
  have hT2 : (∑ k, tg_285 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_285 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_285 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((574090054631 : ℚ) / 200000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_285 k))
      + ((((22612138671 : ℚ) / 50000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_285 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_285 (yg_285 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨285, by omega⟩ : ℚ)) (εB := (cut ⟨286, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_285 yg_285 tg_285 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((574090054631 : ℚ) / 200000000000)) (((22612138671 : ℚ) / 50000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_286 : Fin 17 → ℕ := fun k => [19973, 193, 37, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_286 : Fin 17 → ℕ := fun k => [20051, 193, 37, 16, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_286 : Fin 17 → ℚ := fun k => [((19765697667695363 : ℚ) / 1000000000000), ((177986997656677 : ℚ) / 1000000000000), ((14817649818811 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_286 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨286, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨287, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨287, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨286, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_286 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_286 k + 1) (k.val + 1) < (cut ⟨287, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_286 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_286 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_286 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_286 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_286 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_286 ⟨1, by omega⟩ + 1 ≤ xg_286 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_286 k : ℝ) ≤ Chebyshev.theta ((xg_286 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2257
    · exact Work.RHContract.RegionI.thV_43
    · exact Work.RHContract.RegionI.thV_11
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((20051 : ℕ) : ℝ) ≤ (((717737482889 : ℚ) / 250000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2267
  have hSx : (((452242796057 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 19973, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2257
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_286 k := by decide +kernel
  have hT2 : (∑ k, tg_286 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_286 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_286 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((717737482889 : ℚ) / 250000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_286 k))
      + ((((452242796057 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_286 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_286 (yg_286 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨286, by omega⟩ : ℚ)) (εB := (cut ⟨287, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_286 yg_286 tg_286 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((717737482889 : ℚ) / 250000000000)) (((452242796057 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_287 : Fin 17 → ℕ := fun k => [20051, 193, 37, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_287 : Fin 17 → ℕ := fun k => [20143, 194, 37, 16, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_287 : Fin 17 → ℚ := fun k => [((2483092454255399 : ℚ) / 125000000000), ((177986997656677 : ℚ) / 1000000000000), ((14817649818811 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_287 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨287, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨288, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨288, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨287, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_287 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_287 k + 1) (k.val + 1) < (cut ⟨288, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_287 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_287 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_287 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_287 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_287 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_287 ⟨1, by omega⟩ + 1 ≤ xg_287 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_287 k : ℝ) ≤ Chebyshev.theta ((xg_287 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2267
    · exact Work.RHContract.RegionI.thV_43
    · exact Work.RHContract.RegionI.thV_11
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((20143 : ℕ) : ℝ) ≤ (((358930914813 : ℚ) / 125000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2277
  have hSx : (((452242821017 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 20051, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2267
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_287 k := by decide +kernel
  have hT2 : (∑ k, tg_287 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_287 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_287 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((358930914813 : ℚ) / 125000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_287 k))
      + ((((452242821017 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_287 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_287 (yg_287 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨287, by omega⟩ : ℚ)) (εB := (cut ⟨288, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_287 yg_287 tg_287 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((358930914813 : ℚ) / 125000000000)) (((452242821017 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_288 : Fin 17 → ℕ := fun k => [20143, 193, 37, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_288 : Fin 17 → ℕ := fun k => [20233, 194, 37, 16, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_288 : Fin 17 → ℚ := fun k => [((19963827163521503 : ℚ) / 1000000000000), ((177986997656677 : ℚ) / 1000000000000), ((14817649818811 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_288 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨288, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨289, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨289, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨288, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_288 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_288 k + 1) (k.val + 1) < (cut ⟨289, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_288 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_288 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_288 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_288 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_288 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_288 ⟨1, by omega⟩ + 1 ≤ xg_288 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_288 k : ℝ) ≤ Chebyshev.theta ((xg_288 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2277
    · exact Work.RHContract.RegionI.thV_43
    · exact Work.RHContract.RegionI.thV_11
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((20233 : ℕ) : ℝ) ≤ (((3589928363 : ℚ) / 1250000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2287
  have hSx : (((1808971383 : ℚ) / 4000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 20143, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2277
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_288 k := by decide +kernel
  have hT2 : (∑ k, tg_288 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_288 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_288 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((3589928363 : ℚ) / 1250000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_288 k))
      + ((((1808971383 : ℚ) / 4000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_288 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_288 (yg_288 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨288, by omega⟩ : ℚ)) (εB := (cut ⟨289, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_288 yg_288 tg_288 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((3589928363 : ℚ) / 1250000000)) (((1808971383 : ℚ) / 4000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_289 : Fin 17 → ℕ := fun k => [20233, 193, 37, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_289 : Fin 17 → ℕ := fun k => [20347, 195, 37, 16, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_289 : Fin 17 → ℚ := fun k => [((20062955291338591 : ℚ) / 1000000000000), ((177986997656677 : ℚ) / 1000000000000), ((14817649818811 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_289 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨289, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨290, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨290, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨289, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_289 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_289 k + 1) (k.val + 1) < (cut ⟨290, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_289 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_289 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_289 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_289 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_289 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_289 ⟨1, by omega⟩ + 1 ≤ xg_289 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_289 k : ℝ) ≤ Chebyshev.theta ((xg_289 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2287
    · exact Work.RHContract.RegionI.thV_43
    · exact Work.RHContract.RegionI.thV_11
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((20347 : ℕ) : ℝ) ≤ (((2872435232241 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2297
  have hSx : (((113060717571 : ℚ) / 250000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 20233, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2287
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_289 k := by decide +kernel
  have hT2 : (∑ k, tg_289 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_289 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_289 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2872435232241 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_289 k))
      + ((((113060717571 : ℚ) / 250000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_289 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_289 (yg_289 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨289, by omega⟩ : ℚ)) (εB := (cut ⟨290, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_289 yg_289 tg_289 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2872435232241 : ℚ) / 1000000000000)) (((113060717571 : ℚ) / 250000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_290 : Fin 17 → ℕ := fun k => [20347, 193, 37, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_290 : Fin 17 → ℕ := fun k => [20431, 195, 37, 16, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_290 : Fin 17 → ℚ := fun k => [((4032428142775827 : ℚ) / 200000000000), ((177986997656677 : ℚ) / 1000000000000), ((14817649818811 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_290 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨290, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨291, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨291, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨290, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_290 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_290 k + 1) (k.val + 1) < (cut ⟨291, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_290 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_290 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_290 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_290 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_290 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_290 ⟨1, by omega⟩ + 1 ≤ xg_290 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_290 k : ℝ) ≤ Chebyshev.theta ((xg_290 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2297
    · exact Work.RHContract.RegionI.thV_43
    · exact Work.RHContract.RegionI.thV_11
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((20431 : ℕ) : ℝ) ≤ (((1436462879243 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2307
  have hSx : (((226121447269 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 20347, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2297
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_290 k := by decide +kernel
  have hT2 : (∑ k, tg_290 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_290 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_290 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1436462879243 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_290 k))
      + ((((226121447269 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_290 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_290 (yg_290 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨290, by omega⟩ : ℚ)) (εB := (cut ⟨291, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_290 yg_290 tg_290 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1436462879243 : ℚ) / 500000000000)) (((226121447269 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_291 : Fin 17 → ℕ := fun k => [20431, 193, 37, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_291 : Fin 17 → ℕ := fun k => [20543, 196, 37, 16, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_291 : Fin 17 → ℚ := fun k => [((2026136713542881 : ℚ) / 100000000000), ((177986997656677 : ℚ) / 1000000000000), ((14817649818811 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_291 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨291, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨292, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨292, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨291, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_291 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_291 k + 1) (k.val + 1) < (cut ⟨292, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_291 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_291 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_291 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_291 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_291 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_291 ⟨1, by omega⟩ + 1 ≤ xg_291 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_291 k : ℝ) ≤ Chebyshev.theta ((xg_291 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2307
    · exact Work.RHContract.RegionI.thV_43
    · exact Work.RHContract.RegionI.thV_11
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((20543 : ℕ) : ℝ) ≤ (((1436706864451 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2317
  have hSx : (((90448583719 : ℚ) / 200000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 20431, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2307
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_291 k := by decide +kernel
  have hT2 : (∑ k, tg_291 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_291 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_291 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1436706864451 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_291 k))
      + ((((90448583719 : ℚ) / 200000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_291 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_291 (yg_291 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨291, by omega⟩ : ℚ)) (εB := (cut ⟨292, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_291 yg_291 tg_291 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1436706864451 : ℚ) / 500000000000)) (((90448583719 : ℚ) / 200000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_292 : Fin 17 → ℕ := fun k => [20543, 193, 37, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_292 : Fin 17 → ℕ := fun k => [20663, 196, 38, 16, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_292 : Fin 17 → ℚ := fun k => [((10180322900700601 : ℚ) / 500000000000), ((177986997656677 : ℚ) / 1000000000000), ((14817649818811 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_292 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨292, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨293, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨293, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨292, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_292 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_292 k + 1) (k.val + 1) < (cut ⟨293, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_292 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_292 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_292 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_292 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_292 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_292 ⟨1, by omega⟩ + 1 ≤ xg_292 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_292 k : ℝ) ≤ Chebyshev.theta ((xg_292 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2317
    · exact Work.RHContract.RegionI.thV_43
    · exact Work.RHContract.RegionI.thV_11
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((20663 : ℕ) : ℝ) ≤ (((718474773599 : ℚ) / 250000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2327
  have hSx : (((452242942399 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 20543, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2317
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_292 k := by decide +kernel
  have hT2 : (∑ k, tg_292 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_292 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_292 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((718474773599 : ℚ) / 250000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_292 k))
      + ((((452242942399 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_292 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_292 (yg_292 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨292, by omega⟩ : ℚ)) (εB := (cut ⟨293, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_292 yg_292 tg_292 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((718474773599 : ℚ) / 250000000000)) (((452242942399 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_293 : Fin 17 → ℕ := fun k => [20663, 193, 37, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_293 : Fin 17 → ℕ := fun k => [20749, 197, 38, 16, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_293 : Fin 17 → ℚ := fun k => [((20459977995472873 : ℚ) / 1000000000000), ((177986997656677 : ℚ) / 1000000000000), ((14817649818811 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_293 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨293, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨294, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨294, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨293, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_293 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_293 k + 1) (k.val + 1) < (cut ⟨294, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_293 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_293 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_293 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_293 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_293 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_293 ⟨1, by omega⟩ + 1 ≤ xg_293 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_293 k : ℝ) ≤ Chebyshev.theta ((xg_293 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2327
    · exact Work.RHContract.RegionI.thV_43
    · exact Work.RHContract.RegionI.thV_11
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((20749 : ℕ) : ℝ) ≤ (((574866690407 : ℚ) / 200000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2336
  have hSx : (((452242965951 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 20663, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2327
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_293 k := by decide +kernel
  have hT2 : (∑ k, tg_293 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_293 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_293 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((574866690407 : ℚ) / 200000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_293 k))
      + ((((452242965951 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_293 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_293 (yg_293 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨293, by omega⟩ : ℚ)) (εB := (cut ⟨294, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_293 yg_293 tg_293 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((574866690407 : ℚ) / 200000000000)) (((452242965951 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_294 : Fin 17 → ℕ := fun k => [20749, 197, 37, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_294 : Fin 17 → ℕ := fun k => [20873, 197, 38, 16, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_294 : Fin 17 → ℚ := fun k => [((2568678502516253 : ℚ) / 125000000000), ((36654040276719 : ℚ) / 200000000000), ((14817649818811 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_294 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨294, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨295, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨295, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨294, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_294 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_294 k + 1) (k.val + 1) < (cut ⟨295, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_294 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_294 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_294 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_294 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_294 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_294 ⟨1, by omega⟩ + 1 ≤ xg_294 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_294 k : ℝ) ≤ Chebyshev.theta ((xg_294 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2336
    · exact Work.RHContract.RegionI.thV_44
    · exact Work.RHContract.RegionI.thV_11
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((20873 : ℕ) : ℝ) ≤ (((143740707111 : ℚ) / 50000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2346
  have hSx : (((452242986909 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 20749, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2336
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_294 k := by decide +kernel
  have hT2 : (∑ k, tg_294 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_294 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_294 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((143740707111 : ℚ) / 50000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_294 k))
      + ((((452242986909 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_294 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_294 (yg_294 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨294, by omega⟩ : ℚ)) (εB := (cut ⟨295, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_294 yg_294 tg_294 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((143740707111 : ℚ) / 50000000000)) (((452242986909 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_295 : Fin 17 → ℕ := fun k => [20873, 197, 37, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_295 : Fin 17 → ℕ := fun k => [20959, 198, 38, 16, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_295 : Fin 17 → ℚ := fun k => [((5162214251639101 : ℚ) / 250000000000), ((36654040276719 : ℚ) / 200000000000), ((14817649818811 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_295 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨295, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨296, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨296, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨295, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_295 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_295 k + 1) (k.val + 1) < (cut ⟨296, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_295 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_295 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_295 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_295 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_295 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_295 ⟨1, by omega⟩ + 1 ≤ xg_295 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_295 k : ℝ) ≤ Chebyshev.theta ((xg_295 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2346
    · exact Work.RHContract.RegionI.thV_44
    · exact Work.RHContract.RegionI.thV_11
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((20959 : ℕ) : ℝ) ≤ (((143764612863 : ℚ) / 50000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2356
  have hSx : (((56530376251 : ℚ) / 125000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 20873, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2346
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_295 k := by decide +kernel
  have hT2 : (∑ k, tg_295 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_295 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_295 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((143764612863 : ℚ) / 50000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_295 k))
      + ((((56530376251 : ℚ) / 125000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_295 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_295 (yg_295 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨295, by omega⟩ : ℚ)) (εB := (cut ⟨296, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_295 yg_295 tg_295 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((143764612863 : ℚ) / 50000000000)) (((56530376251 : ℚ) / 125000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_296 : Fin 17 → ℕ := fun k => [20959, 197, 37, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_296 : Fin 17 → ℕ := fun k => [21031, 198, 38, 16, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_296 : Fin 17 → ℚ := fun k => [((20748339695974557 : ℚ) / 1000000000000), ((36654040276719 : ℚ) / 200000000000), ((14817649818811 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_296 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨296, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨297, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨297, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨296, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_296 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_296 k + 1) (k.val + 1) < (cut ⟨297, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_296 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_296 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_296 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_296 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_296 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_296 ⟨1, by omega⟩ + 1 ≤ xg_296 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_296 k : ℝ) ≤ Chebyshev.theta ((xg_296 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2356
    · exact Work.RHContract.RegionI.thV_44
    · exact Work.RHContract.RegionI.thV_11
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((21031 : ℕ) : ℝ) ≤ (((2875768364317 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2366
  have hSx : (((22612151643 : ℚ) / 50000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 20959, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2356
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_296 k := by decide +kernel
  have hT2 : (∑ k, tg_296 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_296 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_296 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2875768364317 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_296 k))
      + ((((22612151643 : ℚ) / 50000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_296 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_296 (yg_296 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨296, by omega⟩ : ℚ)) (εB := (cut ⟨297, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_296 yg_296 tg_296 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2875768364317 : ℚ) / 1000000000000)) (((22612151643 : ℚ) / 50000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_297 : Fin 17 → ℕ := fun k => [21031, 197, 37, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_297 : Fin 17 → ℕ := fun k => [21149, 198, 38, 16, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_297 : Fin 17 → ℚ := fun k => [((20847864468059673 : ℚ) / 1000000000000), ((36654040276719 : ℚ) / 200000000000), ((14817649818811 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_297 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨297, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨298, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨298, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨297, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_297 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_297 k + 1) (k.val + 1) < (cut ⟨298, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_297 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_297 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_297 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_297 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_297 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_297 ⟨1, by omega⟩ + 1 ≤ xg_297 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_297 k : ℝ) ≤ Chebyshev.theta ((xg_297 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2366
    · exact Work.RHContract.RegionI.thV_44
    · exact Work.RHContract.RegionI.thV_11
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((21149 : ℕ) : ℝ) ≤ (((2876242229473 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2376
  have hSx : (((452243055521 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 21031, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2366
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_297 k := by decide +kernel
  have hT2 : (∑ k, tg_297 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_297 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_297 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2876242229473 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_297 k))
      + ((((452243055521 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_297 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_297 (yg_297 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨297, by omega⟩ : ℚ)) (εB := (cut ⟨298, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_297 yg_297 tg_297 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2876242229473 : ℚ) / 1000000000000)) (((452243055521 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_298 : Fin 17 → ℕ := fun k => [21149, 197, 37, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_298 : Fin 17 → ℕ := fun k => [21221, 199, 38, 16, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_298 : Fin 17 → ℚ := fun k => [((20947436445394999 : ℚ) / 1000000000000), ((36654040276719 : ℚ) / 200000000000), ((14817649818811 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_298 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨298, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨299, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨299, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨298, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_298 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_298 k + 1) (k.val + 1) < (cut ⟨299, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_298 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_298 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_298 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_298 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_298 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_298 ⟨1, by omega⟩ + 1 ≤ xg_298 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_298 k : ℝ) ≤ Chebyshev.theta ((xg_298 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2376
    · exact Work.RHContract.RegionI.thV_44
    · exact Work.RHContract.RegionI.thV_11
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((21221 : ℕ) : ℝ) ≤ (((1438333527703 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2385
  have hSx : (((452243077969 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 21149, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2376
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_298 k := by decide +kernel
  have hT2 : (∑ k, tg_298 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_298 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_298 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1438333527703 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_298 k))
      + ((((452243077969 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_298 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_298 (yg_298 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨298, by omega⟩ : ℚ)) (εB := (cut ⟨299, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_298 yg_298 tg_298 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1438333527703 : ℚ) / 500000000000)) (((452243077969 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_299 : Fin 17 → ℕ := fun k => [21221, 199, 37, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_299 : Fin 17 → ℕ := fun k => [21341, 199, 38, 16, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_299 : Fin 17 → ℚ := fun k => [((21037086162499263 : ℚ) / 1000000000000), ((188563506206499 : ℚ) / 1000000000000), ((14817649818811 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_299 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨299, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨300, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨300, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨299, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_299 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_299 k + 1) (k.val + 1) < (cut ⟨300, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_299 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_299 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_299 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_299 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_299 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_299 ⟨1, by omega⟩ + 1 ≤ xg_299 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_299 k : ℝ) ≤ Chebyshev.theta ((xg_299 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2385
    · exact Work.RHContract.RegionI.thV_45
    · exact Work.RHContract.RegionI.thV_11
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((21341 : ℕ) : ℝ) ≤ (((5754273473 : ℚ) / 2000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2395
  have hSx : (((14132596813 : ℚ) / 31250000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 21221, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2385
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_299 k := by decide +kernel
  have hT2 : (∑ k, tg_299 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_299 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_299 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((5754273473 : ℚ) / 2000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_299 k))
      + ((((14132596813 : ℚ) / 31250000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_299 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_299 (yg_299 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨299, by omega⟩ : ℚ)) (εB := (cut ⟨300, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_299 yg_299 tg_299 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((5754273473 : ℚ) / 2000000000)) (((14132596813 : ℚ) / 31250000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_300 : Fin 17 → ℕ := fun k => [21341, 199, 37, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_300 : Fin 17 → ℕ := fun k => [21433, 200, 38, 16, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_300 : Fin 17 → ℚ := fun k => [((5284186707008369 : ℚ) / 250000000000), ((188563506206499 : ℚ) / 1000000000000), ((14817649818811 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_300 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨300, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨301, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨301, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨300, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_300 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_300 k + 1) (k.val + 1) < (cut ⟨301, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_300 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_300 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_300 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_300 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_300 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_300 ⟨1, by omega⟩ + 1 ≤ xg_300 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_300 k : ℝ) ≤ Chebyshev.theta ((xg_300 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2395
    · exact Work.RHContract.RegionI.thV_45
    · exact Work.RHContract.RegionI.thV_11
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((21433 : ℕ) : ℝ) ≤ (((575520836369 : ℚ) / 200000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2405
  have hSx : (((45224312007 : ℚ) / 100000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 21341, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2395
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_300 k := by decide +kernel
  have hT2 : (∑ k, tg_300 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_300 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_300 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((575520836369 : ℚ) / 200000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_300 k))
      + ((((45224312007 : ℚ) / 100000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_300 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_300 (yg_300 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨300, by omega⟩ : ℚ)) (εB := (cut ⟨301, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_300 yg_300 tg_300 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((575520836369 : ℚ) / 200000000000)) (((45224312007 : ℚ) / 100000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_301 : Fin 17 → ℕ := fun k => [21433, 199, 37, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_301 : Fin 17 → ℕ := fun k => [21523, 200, 38, 16, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_301 : Fin 17 → ℚ := fun k => [((10618227599856551 : ℚ) / 500000000000), ((188563506206499 : ℚ) / 1000000000000), ((14817649818811 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_301 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨301, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨302, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨302, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨301, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_301 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_301 k + 1) (k.val + 1) < (cut ⟨302, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_301 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_301 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_301 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_301 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_301 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_301 ⟨1, by omega⟩ + 1 ≤ xg_301 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_301 k : ℝ) ≤ Chebyshev.theta ((xg_301 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2405
    · exact Work.RHContract.RegionI.thV_45
    · exact Work.RHContract.RegionI.thV_11
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((21523 : ℕ) : ℝ) ≤ (((89939667131 : ℚ) / 31250000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2415
  have hSx : (((90448628383 : ℚ) / 200000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 21433, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2405
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_301 k := by decide +kernel
  have hT2 : (∑ k, tg_301 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_301 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_301 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((89939667131 : ℚ) / 31250000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_301 k))
      + ((((90448628383 : ℚ) / 200000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_301 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_301 (yg_301 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨301, by omega⟩ : ℚ)) (εB := (cut ⟨302, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_301 yg_301 tg_301 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((89939667131 : ℚ) / 31250000000)) (((90448628383 : ℚ) / 200000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_302 : Fin 17 → ℕ := fun k => [21523, 199, 37, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_302 : Fin 17 → ℕ := fun k => [21601, 201, 38, 16, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_302 : Fin 17 → ℚ := fun k => [((21336212441343429 : ℚ) / 1000000000000), ((188563506206499 : ℚ) / 1000000000000), ((14817649818811 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_302 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨302, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨303, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨303, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨302, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_302 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_302 k + 1) (k.val + 1) < (cut ⟨303, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_302 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_302 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_302 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_302 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_302 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_302 ⟨1, by omega⟩ + 1 ≤ xg_302 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_302 k : ℝ) ≤ Chebyshev.theta ((xg_302 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2415
    · exact Work.RHContract.RegionI.thV_45
    · exact Work.RHContract.RegionI.thV_11
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((21601 : ℕ) : ℝ) ≤ (((2878532901773 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2425
  have hSx : (((226121581773 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 21523, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2415
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_302 k := by decide +kernel
  have hT2 : (∑ k, tg_302 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_302 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_302 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2878532901773 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_302 k))
      + ((((226121581773 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_302 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_302 (yg_302 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨302, by omega⟩ : ℚ)) (εB := (cut ⟨303, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_302 yg_302 tg_302 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2878532901773 : ℚ) / 1000000000000)) (((226121581773 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_303 : Fin 17 → ℕ := fun k => [21601, 199, 37, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_303 : Fin 17 → ℕ := fun k => [21713, 201, 38, 16, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_303 : Fin 17 → ℚ := fun k => [((21436004414661631 : ℚ) / 1000000000000), ((188563506206499 : ℚ) / 1000000000000), ((14817649818811 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_303 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨303, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨304, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨304, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨303, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_303 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_303 k + 1) (k.val + 1) < (cut ⟨304, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_303 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_303 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_303 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_303 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_303 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_303 ⟨1, by omega⟩ + 1 ≤ xg_303 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_303 k : ℝ) ≤ Chebyshev.theta ((xg_303 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2425
    · exact Work.RHContract.RegionI.thV_45
    · exact Work.RHContract.RegionI.thV_11
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((21713 : ℕ) : ℝ) ≤ (((1439497331169 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2435
  have hSx : (((452243185027 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 21601, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2425
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_303 k := by decide +kernel
  have hT2 : (∑ k, tg_303 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_303 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_303 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1439497331169 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_303 k))
      + ((((452243185027 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_303 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_303 (yg_303 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨303, by omega⟩ : ℚ)) (εB := (cut ⟨304, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_303 yg_303 tg_303 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1439497331169 : ℚ) / 500000000000)) (((452243185027 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_304 : Fin 17 → ℕ := fun k => [21713, 199, 37, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_304 : Fin 17 → ℕ := fun k => [21803, 202, 38, 16, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_304 : Fin 17 → ℚ := fun k => [((5383958787431967 : ℚ) / 250000000000), ((188563506206499 : ℚ) / 1000000000000), ((14817649818811 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_304 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨304, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨305, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨305, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨304, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_304 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_304 k + 1) (k.val + 1) < (cut ⟨305, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_304 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_304 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_304 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_304 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_304 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_304 ⟨1, by omega⟩ + 1 ≤ xg_304 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_304 k : ℝ) ≤ Chebyshev.theta ((xg_304 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2435
    · exact Work.RHContract.RegionI.thV_45
    · exact Work.RHContract.RegionI.thV_11
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((21803 : ℕ) : ℝ) ≤ (((89982942121 : ℚ) / 31250000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2445
  have hSx : (((452243206343 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 21713, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2435
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_304 k := by decide +kernel
  have hT2 : (∑ k, tg_304 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_304 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_304 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((89982942121 : ℚ) / 31250000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_304 k))
      + ((((452243206343 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_304 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_304 (yg_304 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨304, by omega⟩ : ℚ)) (εB := (cut ⟨305, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_304 yg_304 tg_304 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((89982942121 : ℚ) / 31250000000)) (((452243206343 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_305 : Fin 17 → ℕ := fun k => [21803, 199, 37, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_305 : Fin 17 → ℕ := fun k => [21893, 202, 38, 16, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_305 : Fin 17 → ℚ := fun k => [((21635715268111873 : ℚ) / 1000000000000), ((188563506206499 : ℚ) / 1000000000000), ((14817649818811 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_305 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨305, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨306, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨306, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨305, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_305 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_305 k + 1) (k.val + 1) < (cut ⟨306, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_305 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_305 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_305 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_305 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_305 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_305 ⟨1, by omega⟩ + 1 ≤ xg_305 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_305 k : ℝ) ≤ Chebyshev.theta ((xg_305 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2445
    · exact Work.RHContract.RegionI.thV_45
    · exact Work.RHContract.RegionI.thV_11
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((21893 : ℕ) : ℝ) ≤ (((1439955874693 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2455
  have hSx : (((9044864549 : ℚ) / 20000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 21803, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2445
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_305 k := by decide +kernel
  have hT2 : (∑ k, tg_305 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_305 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_305 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1439955874693 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_305 k))
      + ((((9044864549 : ℚ) / 20000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_305 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_305 (yg_305 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨305, by omega⟩ : ℚ)) (εB := (cut ⟨306, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_305 yg_305 tg_305 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1439955874693 : ℚ) / 500000000000)) (((9044864549 : ℚ) / 20000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_306 : Fin 17 → ℕ := fun k => [21893, 199, 37, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_306 : Fin 17 → ℕ := fun k => [22013, 203, 38, 16, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_306 : Fin 17 → ℚ := fun k => [((10867818235889707 : ℚ) / 500000000000), ((188563506206499 : ℚ) / 1000000000000), ((14817649818811 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_306 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨306, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨307, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨307, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨306, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_306 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_306 k + 1) (k.val + 1) < (cut ⟨307, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_306 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_306 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_306 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_306 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_306 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_306 ⟨1, by omega⟩ + 1 ≤ xg_306 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_306 k : ℝ) ≤ Chebyshev.theta ((xg_306 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2455
    · exact Work.RHContract.RegionI.thV_45
    · exact Work.RHContract.RegionI.thV_11
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((22013 : ℕ) : ℝ) ≤ (((720091751419 : ℚ) / 250000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2465
  have hSx : (((1766575189 : ℚ) / 3906250000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 21893, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2455
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_306 k := by decide +kernel
  have hT2 : (∑ k, tg_306 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_306 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_306 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((720091751419 : ℚ) / 250000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_306 k))
      + ((((1766575189 : ℚ) / 3906250000) : ℚ) - Work.RHContract.RegionI.s2small (yg_306 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_306 (yg_306 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨306, by omega⟩ : ℚ)) (εB := (cut ⟨307, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_306 yg_306 tg_306 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((720091751419 : ℚ) / 250000000000)) (((1766575189 : ℚ) / 3906250000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_307 : Fin 17 → ℕ := fun k => [22013, 199, 37, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_307 : Fin 17 → ℕ := fun k => [22091, 203, 38, 16, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_307 : Fin 17 → ℚ := fun k => [((10917804531069553 : ℚ) / 500000000000), ((188563506206499 : ℚ) / 1000000000000), ((14817649818811 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_307 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨307, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨308, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨308, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨307, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_307 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_307 k + 1) (k.val + 1) < (cut ⟨308, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_307 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_307 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_307 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_307 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_307 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_307 ⟨1, by omega⟩ + 1 ≤ xg_307 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_307 k : ℝ) ≤ Chebyshev.theta ((xg_307 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2465
    · exact Work.RHContract.RegionI.thV_45
    · exact Work.RHContract.RegionI.thV_11
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((22091 : ℕ) : ℝ) ≤ (((1440410205923 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2475
  have hSx : (((226121634551 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 22013, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2465
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_307 k := by decide +kernel
  have hT2 : (∑ k, tg_307 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_307 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_307 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1440410205923 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_307 k))
      + ((((226121634551 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_307 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_307 (yg_307 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨307, by omega⟩ : ℚ)) (εB := (cut ⟨308, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_307 yg_307 tg_307 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1440410205923 : ℚ) / 500000000000)) (((226121634551 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_308 : Fin 17 → ℕ := fun k => [22091, 199, 37, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_308 : Fin 17 → ℕ := fun k => [22159, 203, 38, 16, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_308 : Fin 17 → ℚ := fun k => [((21935622366476647 : ℚ) / 1000000000000), ((188563506206499 : ℚ) / 1000000000000), ((14817649818811 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_308 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨308, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨309, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨309, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨308, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_308 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_308 k + 1) (k.val + 1) < (cut ⟨309, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_308 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_308 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_308 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_308 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_308 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_308 ⟨1, by omega⟩ + 1 ≤ xg_308 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_308 k : ℝ) ≤ Chebyshev.theta ((xg_308 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2475
    · exact Work.RHContract.RegionI.thV_45
    · exact Work.RHContract.RegionI.thV_11
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((22159 : ℕ) : ℝ) ≤ (((2881272269181 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2485
  have hSx : (((90448657931 : ℚ) / 200000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 22091, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2475
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_308 k := by decide +kernel
  have hT2 : (∑ k, tg_308 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_308 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_308 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2881272269181 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_308 k))
      + ((((90448657931 : ℚ) / 200000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_308 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_308 (yg_308 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨308, by omega⟩ : ℚ)) (εB := (cut ⟨309, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_308 yg_308 tg_308 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2881272269181 : ℚ) / 1000000000000)) (((90448657931 : ℚ) / 200000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_309 : Fin 17 → ℕ := fun k => [22159, 199, 37, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_309 : Fin 17 → ℕ := fun k => [22279, 204, 39, 16, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_309 : Fin 17 → ℚ := fun k => [((22035669888681131 : ℚ) / 1000000000000), ((188563506206499 : ℚ) / 1000000000000), ((14817649818811 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_309 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨309, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨310, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨310, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨309, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_309 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_309 k + 1) (k.val + 1) < (cut ⟨310, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_309 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_309 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_309 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_309 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_309 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_309 ⟨1, by omega⟩ + 1 ≤ xg_309 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_309 k : ℝ) ≤ Chebyshev.theta ((xg_309 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2485
    · exact Work.RHContract.RegionI.thV_45
    · exact Work.RHContract.RegionI.thV_11
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((22279 : ℕ) : ℝ) ≤ (((22513452697 : ℚ) / 7812500000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2495
  have hSx : (((226121655033 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 22159, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2485
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_309 k := by decide +kernel
  have hT2 : (∑ k, tg_309 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_309 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_309 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((22513452697 : ℚ) / 7812500000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_309 k))
      + ((((226121655033 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_309 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_309 (yg_309 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨309, by omega⟩ : ℚ)) (εB := (cut ⟨310, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_309 yg_309 tg_309 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((22513452697 : ℚ) / 7812500000)) (((226121655033 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_310 : Fin 17 → ℕ := fun k => [22279, 199, 37, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_310 : Fin 17 → ℕ := fun k => [22391, 204, 39, 16, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_310 : Fin 17 → ℚ := fun k => [((22135765811342687 : ℚ) / 1000000000000), ((188563506206499 : ℚ) / 1000000000000), ((14817649818811 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_310 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨310, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨311, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨311, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨310, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_310 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_310 k + 1) (k.val + 1) < (cut ⟨311, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_310 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_310 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_310 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_310 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_310 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_310 ⟨1, by omega⟩ + 1 ≤ xg_310 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_310 k : ℝ) ≤ Chebyshev.theta ((xg_310 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2495
    · exact Work.RHContract.RegionI.thV_45
    · exact Work.RHContract.RegionI.thV_11
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((22391 : ℕ) : ℝ) ≤ (((360271202017 : ℚ) / 125000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2505
  have hSx : (((226121665141 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 22279, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2495
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_310 k := by decide +kernel
  have hT2 : (∑ k, tg_310 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_310 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_310 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((360271202017 : ℚ) / 125000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_310 k))
      + ((((226121665141 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_310 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_310 (yg_310 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨310, by omega⟩ : ℚ)) (εB := (cut ⟨311, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_310 yg_310 tg_310 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((360271202017 : ℚ) / 125000000000)) (((226121665141 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_311 : Fin 17 → ℕ := fun k => [22391, 199, 37, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_311 : Fin 17 → ℕ := fun k => [22501, 205, 39, 16, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_311 : Fin 17 → ℚ := fun k => [((22235906421748073 : ℚ) / 1000000000000), ((188563506206499 : ℚ) / 1000000000000), ((14817649818811 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_311 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨311, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨312, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨312, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨311, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_311 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_311 k + 1) (k.val + 1) < (cut ⟨312, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_311 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_311 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_311 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_311 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_311 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_311 ⟨1, by omega⟩ + 1 ≤ xg_311 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_311 k : ℝ) ≤ Chebyshev.theta ((xg_311 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2505
    · exact Work.RHContract.RegionI.thV_45
    · exact Work.RHContract.RegionI.thV_11
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((22501 : ℕ) : ℝ) ≤ (((576523006691 : ℚ) / 200000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2515
  have hSx : (((452243350317 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 22391, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2505
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_311 k := by decide +kernel
  have hT2 : (∑ k, tg_311 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_311 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_311 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((576523006691 : ℚ) / 200000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_311 k))
      + ((((452243350317 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_311 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_311 (yg_311 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨311, by omega⟩ : ℚ)) (εB := (cut ⟨312, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_311 yg_311 tg_311 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((576523006691 : ℚ) / 200000000000)) (((452243350317 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_312 : Fin 17 → ℕ := fun k => [22501, 199, 37, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_312 : Fin 17 → ℕ := fun k => [22619, 205, 39, 16, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_312 : Fin 17 → ℚ := fun k => [((11168048747219691 : ℚ) / 500000000000), ((188563506206499 : ℚ) / 1000000000000), ((14817649818811 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_312 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨312, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨313, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨313, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨312, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_312 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_312 k + 1) (k.val + 1) < (cut ⟨313, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_312 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_312 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_312 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_312 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_312 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_312 ⟨1, by omega⟩ + 1 ≤ xg_312 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_312 k : ℝ) ≤ Chebyshev.theta ((xg_312 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2515
    · exact Work.RHContract.RegionI.thV_45
    · exact Work.RHContract.RegionI.thV_11
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((22619 : ℕ) : ℝ) ≤ (((576611654251 : ℚ) / 200000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2525
  have hSx : (((452243370151 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 22501, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2515
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_312 k := by decide +kernel
  have hT2 : (∑ k, tg_312 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_312 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_312 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((576611654251 : ℚ) / 200000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_312 k))
      + ((((452243370151 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_312 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_312 (yg_312 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨312, by omega⟩ : ℚ)) (εB := (cut ⟨313, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_312 yg_312 tg_312 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((576611654251 : ℚ) / 200000000000)) (((452243370151 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_313 : Fin 17 → ℕ := fun k => [22619, 199, 37, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_313 : Fin 17 → ℕ := fun k => [22699, 206, 39, 16, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_313 : Fin 17 → ℚ := fun k => [((22436337618882527 : ℚ) / 1000000000000), ((188563506206499 : ℚ) / 1000000000000), ((14817649818811 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_313 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨313, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨314, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨314, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨313, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_313 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_313 k + 1) (k.val + 1) < (cut ⟨314, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_313 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_313 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_313 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_313 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_313 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_313 ⟨1, by omega⟩ + 1 ≤ xg_313 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_313 k : ℝ) ≤ Chebyshev.theta ((xg_313 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2525
    · exact Work.RHContract.RegionI.thV_45
    · exact Work.RHContract.RegionI.thV_11
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((22699 : ℕ) : ℝ) ≤ (((2883499537241 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2535
  have hSx : (((45224338979 : ℚ) / 100000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 22619, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2525
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_313 k := by decide +kernel
  have hT2 : (∑ k, tg_313 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_313 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_313 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2883499537241 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_313 k))
      + ((((45224338979 : ℚ) / 100000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_313 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_313 (yg_313 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨313, by omega⟩ : ℚ)) (εB := (cut ⟨314, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_313 yg_313 tg_313 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2883499537241 : ℚ) / 1000000000000)) (((45224338979 : ℚ) / 100000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_314 : Fin 17 → ℕ := fun k => [22699, 199, 37, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_314 : Fin 17 → ℕ := fun k => [22783, 206, 39, 16, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_314 : Fin 17 → ℚ := fun k => [((22536622324623731 : ℚ) / 1000000000000), ((188563506206499 : ℚ) / 1000000000000), ((14817649818811 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_314 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨314, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨315, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨315, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨314, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_314 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_314 k + 1) (k.val + 1) < (cut ⟨315, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_314 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_314 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_314 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_314 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_314 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_314 ⟨1, by omega⟩ + 1 ≤ xg_314 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_314 k : ℝ) ≤ Chebyshev.theta ((xg_314 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2535
    · exact Work.RHContract.RegionI.thV_45
    · exact Work.RHContract.RegionI.thV_11
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((22783 : ℕ) : ℝ) ≤ (((1441969617713 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2545
  have hSx : (((452243409257 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 22699, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2535
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_314 k := by decide +kernel
  have hT2 : (∑ k, tg_314 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_314 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_314 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1441969617713 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_314 k))
      + ((((452243409257 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_314 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_314 (yg_314 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨314, by omega⟩ : ℚ)) (εB := (cut ⟨315, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_314 yg_314 tg_314 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1441969617713 : ℚ) / 500000000000)) (((452243409257 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_315 : Fin 17 → ℕ := fun k => [22783, 199, 37, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_315 : Fin 17 → ℕ := fun k => [22901, 207, 39, 16, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_315 : Fin 17 → ℚ := fun k => [((11318471310714617 : ℚ) / 500000000000), ((188563506206499 : ℚ) / 1000000000000), ((14817649818811 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_315 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨315, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨316, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨316, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨315, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_315 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_315 k + 1) (k.val + 1) < (cut ⟨316, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_315 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_315 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_315 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_315 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_315 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_315 ⟨1, by omega⟩ + 1 ≤ xg_315 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_315 k : ℝ) ≤ Chebyshev.theta ((xg_315 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2545
    · exact Work.RHContract.RegionI.thV_45
    · exact Work.RHContract.RegionI.thV_11
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((22901 : ℕ) : ℝ) ≤ (((2884376990069 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2555
  have hSx : (((90448685717 : ℚ) / 200000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 22783, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2545
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_315 k := by decide +kernel
  have hT2 : (∑ k, tg_315 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_315 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_315 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2884376990069 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_315 k))
      + ((((90448685717 : ℚ) / 200000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_315 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_315 (yg_315 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨315, by omega⟩ : ℚ)) (εB := (cut ⟨316, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_315 yg_315 tg_315 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2884376990069 : ℚ) / 1000000000000)) (((90448685717 : ℚ) / 200000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_316 : Fin 17 → ℕ := fun k => [22901, 199, 37, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_316 : Fin 17 → ℕ := fun k => [23011, 207, 39, 16, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_316 : Fin 17 → ℚ := fun k => [((22737307222698687 : ℚ) / 1000000000000), ((188563506206499 : ℚ) / 1000000000000), ((14817649818811 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_316 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨316, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨317, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨317, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨316, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_316 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_316 k + 1) (k.val + 1) < (cut ⟨317, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_316 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_316 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_316 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_316 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_316 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_316 ⟨1, by omega⟩ + 1 ≤ xg_316 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_316 k : ℝ) ≤ Chebyshev.theta ((xg_316 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2555
    · exact Work.RHContract.RegionI.thV_45
    · exact Work.RHContract.RegionI.thV_11
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((23011 : ℕ) : ℝ) ≤ (((1442406258881 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2565
  have hSx : (((22612172387 : ℚ) / 50000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 22901, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2555
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_316 k := by decide +kernel
  have hT2 : (∑ k, tg_316 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_316 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_316 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1442406258881 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_316 k))
      + ((((22612172387 : ℚ) / 50000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_316 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_316 (yg_316 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨316, by omega⟩ : ℚ)) (εB := (cut ⟨317, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_316 yg_316 tg_316 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1442406258881 : ℚ) / 500000000000)) (((22612172387 : ℚ) / 50000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_317 : Fin 17 → ℕ := fun k => [23011, 199, 37, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_317 : Fin 17 → ℕ := fun k => [23063, 207, 39, 16, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_317 : Fin 17 → ℚ := fun k => [((22837722823509239 : ℚ) / 1000000000000), ((188563506206499 : ℚ) / 1000000000000), ((14817649818811 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_317 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨317, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨318, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨318, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨317, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_317 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_317 k + 1) (k.val + 1) < (cut ⟨318, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_317 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_317 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_317 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_317 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_317 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_317 ⟨1, by omega⟩ + 1 ≤ xg_317 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_317 k : ℝ) ≤ Chebyshev.theta ((xg_317 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2565
    · exact Work.RHContract.RegionI.thV_45
    · exact Work.RHContract.RegionI.thV_11
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((23063 : ℕ) : ℝ) ≤ (((2885246543869 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2575
  have hSx : (((452243466701 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 23011, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2565
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_317 k := by decide +kernel
  have hT2 : (∑ k, tg_317 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_317 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_317 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2885246543869 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_317 k))
      + ((((452243466701 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_317 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_317 (yg_317 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨317, by omega⟩ : ℚ)) (εB := (cut ⟨318, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_317 yg_317 tg_317 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2885246543869 : ℚ) / 1000000000000)) (((452243466701 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_318 : Fin 17 → ℕ := fun k => [23063, 199, 37, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_318 : Fin 17 → ℕ := fun k => [23173, 208, 39, 16, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_318 : Fin 17 → ℚ := fun k => [((4587634590530939 : ℚ) / 200000000000), ((188563506206499 : ℚ) / 1000000000000), ((14817649818811 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_318 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨318, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨319, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨319, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨318, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_318 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_318 k + 1) (k.val + 1) < (cut ⟨319, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_318 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_318 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_318 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_318 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_318 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_318 ⟨1, by omega⟩ + 1 ≤ xg_318 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_318 k : ℝ) ≤ Chebyshev.theta ((xg_318 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2575
    · exact Work.RHContract.RegionI.thV_45
    · exact Work.RHContract.RegionI.thV_11
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((23173 : ℕ) : ℝ) ≤ (((1442839513909 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2585
  have hSx : (((113060871383 : ℚ) / 250000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 23063, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2575
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_318 k := by decide +kernel
  have hT2 : (∑ k, tg_318 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_318 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_318 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1442839513909 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_318 k))
      + ((((113060871383 : ℚ) / 250000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_318 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_318 (yg_318 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨318, by omega⟩ : ℚ)) (εB := (cut ⟨319, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_318 yg_318 tg_318 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1442839513909 : ℚ) / 500000000000)) (((113060871383 : ℚ) / 250000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_319 : Fin 17 → ℕ := fun k => [23173, 199, 37, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_319 : Fin 17 → ℕ := fun k => [23291, 208, 39, 16, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_319 : Fin 17 → ℚ := fun k => [((719958083909027 : ℚ) / 31250000000), ((188563506206499 : ℚ) / 1000000000000), ((14817649818811 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_319 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨319, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨320, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨320, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨319, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_319 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_319 k + 1) (k.val + 1) < (cut ⟨320, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_319 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_319 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_319 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_319 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_319 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_319 ⟨1, by omega⟩ + 1 ≤ xg_319 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_319 k : ℝ) ≤ Chebyshev.theta ((xg_319 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2585
    · exact Work.RHContract.RegionI.thV_45
    · exact Work.RHContract.RegionI.thV_11
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((23291 : ℕ) : ℝ) ≤ (((1443054743147 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2595
  have hSx : (((452243504233 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 23173, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2585
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_319 k := by decide +kernel
  have hT2 : (∑ k, tg_319 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_319 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_319 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1443054743147 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_319 k))
      + ((((452243504233 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_319 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_319 (yg_319 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨319, by omega⟩ : ℚ)) (εB := (cut ⟨320, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_319 yg_319 tg_319 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1443054743147 : ℚ) / 500000000000)) (((452243504233 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

end

end Work.RHContract.A.RegionI
