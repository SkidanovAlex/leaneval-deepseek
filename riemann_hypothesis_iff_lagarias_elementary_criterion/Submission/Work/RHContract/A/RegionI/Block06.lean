import Mathlib
import Submission.Work.RHContract.A.RegionI.Core
import Submission.Work.RHContract.A.RegionI.blockCert
import Submission.Work.RHContract.A.RegionI.Data11
import Submission.Work.RHContract.A.RegionI.Cuts

/-!  Region I: group certificates.  GENERATED FILE. -/

open scoped BigOperators

namespace Work.RHContract.A.RegionI

noncomputable section

private def xg_200 : Fin 16 → ℕ := fun k => [12611, 151, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_200 : Fin 16 → ℕ := fun k => [12671, 153, 32, 14, 8, 6, 4, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_200 : Fin 16 → ℚ := fun k => [((1560120871509593 : ℚ) / 125000000000), ((34166217451027 : ℚ) / 250000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_200 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨200, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨201, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨201, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨200, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_200 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_200 k + 1) (k.val + 1) < (cut ⟨201, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_200 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_200 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_200 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_200 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_200 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_200 ⟨1, by omega⟩ + 1 ≤ xg_200 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_200 k : ℝ) ≤ Chebyshev.theta ((xg_200 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1505
    · exact Work.RHContract.RegionI.thV_35
    · exact Work.RHContract.RegionI.thV_10
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((12671 : ℕ) : ℝ) ≤ (((14119953479 : ℚ) / 5000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1513
  have hSx : (((452239795537 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 12611, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1505
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_200 k := by decide +kernel
  have hT2 : (∑ k, tg_200 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_200 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_200 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((14119953479 : ℚ) / 5000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_200 k))
      + ((((452239795537 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_200 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_200 (yg_200 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨200, by omega⟩ : ℚ)) (εB := (cut ⟨201, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_200 yg_200 tg_200 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((14119953479 : ℚ) / 5000000000)) (((452239795537 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_201 : Fin 16 → ℕ := fun k => [12671, 151, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_201 : Fin 16 → ℕ := fun k => [12757, 154, 32, 14, 8, 6, 4, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_201 : Fin 16 → ℚ := fun k => [((3139131379789801 : ℚ) / 250000000000), ((34166217451027 : ℚ) / 250000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_201 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨201, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨202, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨202, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨201, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_201 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_201 k + 1) (k.val + 1) < (cut ⟨202, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_201 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_201 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_201 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_201 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_201 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_201 ⟨1, by omega⟩ + 1 ≤ xg_201 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_201 k : ℝ) ≤ Chebyshev.theta ((xg_201 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1513
    · exact Work.RHContract.RegionI.thV_35
    · exact Work.RHContract.RegionI.thV_10
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((12757 : ℕ) : ℝ) ≤ (((2824619640969 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1521
  have hSx : (((226119922793 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 12671, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1513
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_201 k := by decide +kernel
  have hT2 : (∑ k, tg_201 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_201 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_201 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2824619640969 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_201 k))
      + ((((226119922793 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_201 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_201 (yg_201 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨201, by omega⟩ : ℚ)) (εB := (cut ⟨202, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_201 yg_201 tg_201 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2824619640969 : ℚ) / 1000000000000)) (((226119922793 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_202 : Fin 16 → ℕ := fun k => [12757, 151, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_202 : Fin 16 → ℕ := fun k => [12829, 154, 32, 14, 8, 6, 4, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_202 : Fin 16 → ℚ := fun k => [((6316066555215311 : ℚ) / 500000000000), ((34166217451027 : ℚ) / 250000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_202 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨202, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨203, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨203, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨202, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_202 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_202 k + 1) (k.val + 1) < (cut ⟨203, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_202 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_202 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_202 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_202 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_202 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_202 ⟨1, by omega⟩ + 1 ≤ xg_202 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_202 k : ℝ) ≤ Chebyshev.theta ((xg_202 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1521
    · exact Work.RHContract.RegionI.thV_35
    · exact Work.RHContract.RegionI.thV_10
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((12829 : ℕ) : ℝ) ≤ (((706311142373 : ℚ) / 250000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1529
  have hSx : (((18089595801 : ℚ) / 40000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 12757, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1521
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_202 k := by decide +kernel
  have hT2 : (∑ k, tg_202 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_202 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_202 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((706311142373 : ℚ) / 250000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_202 k))
      + ((((18089595801 : ℚ) / 40000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_202 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_202 (yg_202 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨202, by omega⟩ : ℚ)) (εB := (cut ⟨203, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_202 yg_202 tg_202 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((706311142373 : ℚ) / 250000000000)) (((18089595801 : ℚ) / 40000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_203 : Fin 16 → ℕ := fun k => [12829, 151, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_203 : Fin 16 → ℕ := fun k => [12917, 155, 32, 14, 8, 6, 4, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_203 : Fin 16 → ℚ := fun k => [((6353895976348623 : ℚ) / 500000000000), ((34166217451027 : ℚ) / 250000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_203 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨203, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨204, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨204, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨203, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_203 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_203 k + 1) (k.val + 1) < (cut ⟨204, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_203 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_203 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_203 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_203 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_203 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_203 ⟨1, by omega⟩ + 1 ≤ xg_203 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_203 k : ℝ) ≤ Chebyshev.theta ((xg_203 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1529
    · exact Work.RHContract.RegionI.thV_35
    · exact Work.RHContract.RegionI.thV_10
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((12917 : ℕ) : ℝ) ≤ (((2825865292403 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1537
  have hSx : (((452239943833 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 12829, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1529
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_203 k := by decide +kernel
  have hT2 : (∑ k, tg_203 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_203 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_203 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2825865292403 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_203 k))
      + ((((452239943833 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_203 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_203 (yg_203 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨203, by omega⟩ : ℚ)) (εB := (cut ⟨204, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_203 yg_203 tg_203 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2825865292403 : ℚ) / 1000000000000)) (((452239943833 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_204 : Fin 16 → ℕ := fun k => [12917, 151, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_204 : Fin 16 → ℕ := fun k => [12979, 155, 32, 14, 8, 6, 4, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_204 : Fin 16 → ℚ := fun k => [((1278350481761217 : ℚ) / 100000000000), ((34166217451027 : ℚ) / 250000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_204 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨204, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨205, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨205, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨204, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_204 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_204 k + 1) (k.val + 1) < (cut ⟨205, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_204 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_204 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_204 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_204 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_204 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_204 ⟨1, by omega⟩ + 1 ≤ xg_204 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_204 k : ℝ) ≤ Chebyshev.theta ((xg_204 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1537
    · exact Work.RHContract.RegionI.thV_35
    · exact Work.RHContract.RegionI.thV_10
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((12979 : ℕ) : ℝ) ≤ (((282648299501 : ℚ) / 100000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1545
  have hSx : (((113059997997 : ℚ) / 250000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 12917, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1537
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_204 k := by decide +kernel
  have hT2 : (∑ k, tg_204 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_204 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_204 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((282648299501 : ℚ) / 100000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_204 k))
      + ((((113059997997 : ℚ) / 250000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_204 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_204 (yg_204 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨204, by omega⟩ : ℚ)) (εB := (cut ⟨205, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_204 yg_204 tg_204 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((282648299501 : ℚ) / 100000000000)) (((113059997997 : ℚ) / 250000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_205 : Fin 16 → ℕ := fun k => [12979, 151, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_205 : Fin 16 → ℕ := fun k => [13043, 155, 32, 14, 8, 6, 4, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_205 : Fin 16 → ℚ := fun k => [((3214814174176803 : ℚ) / 250000000000), ((34166217451027 : ℚ) / 250000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_205 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨205, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨206, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨206, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨205, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_205 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_205 k + 1) (k.val + 1) < (cut ⟨206, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_205 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_205 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_205 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_205 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_205 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_205 ⟨1, by omega⟩ + 1 ≤ xg_205 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_205 k : ℝ) ≤ Chebyshev.theta ((xg_205 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1545
    · exact Work.RHContract.RegionI.thV_35
    · exact Work.RHContract.RegionI.thV_10
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((13043 : ℕ) : ℝ) ≤ (((565419543801 : ℚ) / 200000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1553
  have hSx : (((18089601587 : ℚ) / 40000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 12979, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1545
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_205 k := by decide +kernel
  have hT2 : (∑ k, tg_205 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_205 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_205 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((565419543801 : ℚ) / 200000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_205 k))
      + ((((18089601587 : ℚ) / 40000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_205 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_205 (yg_205 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨205, by omega⟩ : ℚ)) (εB := (cut ⟨206, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_205 yg_205 tg_205 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((565419543801 : ℚ) / 200000000000)) (((18089601587 : ℚ) / 40000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_206 : Fin 16 → ℕ := fun k => [13043, 151, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_206 : Fin 16 → ℕ := fun k => [13127, 156, 32, 14, 8, 6, 4, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_206 : Fin 16 → ℚ := fun k => [((202110113169709 : ℚ) / 15625000000), ((34166217451027 : ℚ) / 250000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_206 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨206, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨207, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨207, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨206, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_206 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_206 k + 1) (k.val + 1) < (cut ⟨207, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_206 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_206 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_206 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_206 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_206 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_206 ⟨1, by omega⟩ + 1 ≤ xg_206 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_206 k : ℝ) ≤ Chebyshev.theta ((xg_206 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1553
    · exact Work.RHContract.RegionI.thV_35
    · exact Work.RHContract.RegionI.thV_10
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((13127 : ℕ) : ℝ) ≤ (((2827708641489 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1561
  have hSx : (((452240086903 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 13043, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1553
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_206 k := by decide +kernel
  have hT2 : (∑ k, tg_206 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_206 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_206 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2827708641489 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_206 k))
      + ((((452240086903 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_206 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_206 (yg_206 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨206, by omega⟩ : ℚ)) (εB := (cut ⟨207, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_206 yg_206 tg_206 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2827708641489 : ℚ) / 1000000000000)) (((452240086903 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_207 : Fin 16 → ℕ := fun k => [13127, 151, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_207 : Fin 16 → ℕ := fun k => [13187, 156, 32, 14, 8, 6, 4, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_207 : Fin 16 → ℚ := fun k => [((1626360927426203 : ℚ) / 125000000000), ((34166217451027 : ℚ) / 250000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_207 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨207, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨208, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨208, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨207, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_207 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_207 k + 1) (k.val + 1) < (cut ⟨208, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_207 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_207 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_207 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_207 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_207 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_207 ⟨1, by omega⟩ + 1 ≤ xg_207 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_207 k : ℝ) ≤ Chebyshev.theta ((xg_207 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1561
    · exact Work.RHContract.RegionI.thV_35
    · exact Work.RHContract.RegionI.thV_10
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((13187 : ℕ) : ℝ) ≤ (((1414158116623 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1569
  have hSx : (((9044802671 : ℚ) / 20000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 13127, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1561
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_207 k := by decide +kernel
  have hT2 : (∑ k, tg_207 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_207 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_207 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1414158116623 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_207 k))
      + ((((9044802671 : ℚ) / 20000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_207 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_207 (yg_207 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨207, by omega⟩ : ℚ)) (εB := (cut ⟨208, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_207 yg_207 tg_207 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1414158116623 : ℚ) / 500000000000)) (((9044802671 : ℚ) / 20000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_208 : Fin 16 → ℕ := fun k => [13187, 151, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_208 : Fin 16 → ℕ := fun k => [13291, 157, 32, 14, 8, 6, 4, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_208 : Fin 16 → ℚ := fun k => [((13086771318755309 : ℚ) / 1000000000000), ((34166217451027 : ℚ) / 250000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_208 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨208, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨209, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨209, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨208, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_208 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_208 k + 1) (k.val + 1) < (cut ⟨209, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_208 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_208 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_208 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_208 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_208 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_208 ⟨1, by omega⟩ + 1 ≤ xg_208 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_208 k : ℝ) ≤ Chebyshev.theta ((xg_208 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1569
    · exact Work.RHContract.RegionI.thV_35
    · exact Work.RHContract.RegionI.thV_10
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((13291 : ℕ) : ℝ) ≤ (((2828920191109 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1577
  have hSx : (((45224017969 : ℚ) / 100000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 13187, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1569
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_208 k := by decide +kernel
  have hT2 : (∑ k, tg_208 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_208 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_208 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2828920191109 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_208 k))
      + ((((45224017969 : ℚ) / 100000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_208 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_208 (yg_208 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨208, by omega⟩ : ℚ)) (εB := (cut ⟨209, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_208 yg_208 tg_208 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2828920191109 : ℚ) / 1000000000000)) (((45224017969 : ℚ) / 100000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_209 : Fin 16 → ℕ := fun k => [13291, 157, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_209 : Fin 16 → ℕ := fun k => [13367, 157, 32, 14, 8, 6, 4, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_209 : Fin 16 → ℚ := fun k => [((3290675803750683 : ℚ) / 250000000000), ((35430278901909 : ℚ) / 250000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_209 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨209, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨210, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨210, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨209, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_209 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_209 k + 1) (k.val + 1) < (cut ⟨210, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_209 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_209 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_209 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_209 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_209 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_209 ⟨1, by omega⟩ + 1 ≤ xg_209 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_209 k : ℝ) ≤ Chebyshev.theta ((xg_209 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1577
    · exact Work.RHContract.RegionI.thV_36
    · exact Work.RHContract.RegionI.thV_10
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((13367 : ℕ) : ℝ) ≤ (((44211257463 : ℚ) / 15625000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1585
  have hSx : (((226120112639 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 13291, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1577
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_209 k := by decide +kernel
  have hT2 : (∑ k, tg_209 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_209 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_209 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((44211257463 : ℚ) / 15625000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_209 k))
      + ((((226120112639 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_209 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_209 (yg_209 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨209, by omega⟩ : ℚ)) (εB := (cut ⟨210, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_209 yg_209 tg_209 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((44211257463 : ℚ) / 15625000000)) (((226120112639 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_210 : Fin 16 → ℕ := fun k => [13367, 157, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_210 : Fin 16 → ℕ := fun k => [13451, 158, 32, 14, 8, 6, 4, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_210 : Fin 16 → ℚ := fun k => [((6619341942270749 : ℚ) / 500000000000), ((35430278901909 : ℚ) / 250000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_210 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨210, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨211, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨211, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨210, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_210 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_210 k + 1) (k.val + 1) < (cut ⟨211, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_210 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_210 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_210 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_210 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_210 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_210 ⟨1, by omega⟩ + 1 ≤ xg_210 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_210 k : ℝ) ≤ Chebyshev.theta ((xg_210 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1585
    · exact Work.RHContract.RegionI.thV_36
    · exact Work.RHContract.RegionI.thV_10
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((13451 : ℕ) : ℝ) ≤ (((283011685991 : ℚ) / 100000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1593
  have hSx : (((452240270313 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 13367, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1585
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_210 k := by decide +kernel
  have hT2 : (∑ k, tg_210 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_210 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_210 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((283011685991 : ℚ) / 100000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_210 k))
      + ((((452240270313 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_210 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_210 (yg_210 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨210, by omega⟩ : ℚ)) (εB := (cut ⟨211, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_210 yg_210 tg_210 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((283011685991 : ℚ) / 100000000000)) (((452240270313 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_211 : Fin 16 → ℕ := fun k => [13451, 157, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_211 : Fin 16 → ℕ := fun k => [13523, 158, 32, 14, 8, 6, 4, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_211 : Fin 16 → ℚ := fun k => [((13314716755074809 : ℚ) / 1000000000000), ((35430278901909 : ℚ) / 250000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_211 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨211, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨212, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨212, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨211, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_211 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_211 k + 1) (k.val + 1) < (cut ⟨212, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_211 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_211 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_211 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_211 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_211 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_211 ⟨1, by omega⟩ + 1 ≤ xg_211 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_211 k : ℝ) ≤ Chebyshev.theta ((xg_211 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1593
    · exact Work.RHContract.RegionI.thV_36
    · exact Work.RHContract.RegionI.thV_10
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((13523 : ℕ) : ℝ) ≤ (((176919380707 : ℚ) / 62500000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1601
  have hSx : (((226120157383 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 13451, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1593
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_211 k := by decide +kernel
  have hT2 : (∑ k, tg_211 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_211 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_211 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((176919380707 : ℚ) / 62500000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_211 k))
      + ((((226120157383 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_211 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_211 (yg_211 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨211, by omega⟩ : ℚ)) (εB := (cut ⟨212, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_211 yg_211 tg_211 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((176919380707 : ℚ) / 62500000000)) (((226120157383 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_212 : Fin 16 → ℕ := fun k => [13523, 157, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_212 : Fin 16 → ℕ := fun k => [13619, 159, 33, 14, 8, 6, 4, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_212 : Fin 16 → ℚ := fun k => [((1673849000393437 : ℚ) / 125000000000), ((35430278901909 : ℚ) / 250000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_212 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨212, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨213, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨213, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨212, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_212 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_212 k + 1) (k.val + 1) < (cut ⟨213, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_212 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_212 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_212 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_212 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_212 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_212 ⟨1, by omega⟩ + 1 ≤ xg_212 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_212 k : ℝ) ≤ Chebyshev.theta ((xg_212 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1601
    · exact Work.RHContract.RegionI.thV_36
    · exact Work.RHContract.RegionI.thV_10
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((13619 : ℕ) : ℝ) ≤ (((1415649570507 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1609
  have hSx : (((361792287 : ℚ) / 800000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 13523, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1601
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_212 k := by decide +kernel
  have hT2 : (∑ k, tg_212 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_212 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_212 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1415649570507 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_212 k))
      + ((((361792287 : ℚ) / 800000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_212 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_212 (yg_212 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨212, by omega⟩ : ℚ)) (εB := (cut ⟨213, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_212 yg_212 tg_212 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1415649570507 : ℚ) / 500000000000)) (((361792287 : ℚ) / 800000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_213 : Fin 16 → ℕ := fun k => [13619, 157, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_213 : Fin 16 → ℕ := fun k => [13691, 159, 33, 14, 8, 6, 4, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_213 : Fin 16 → ℚ := fun k => [((6733461922798469 : ℚ) / 500000000000), ((35430278901909 : ℚ) / 250000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_213 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨213, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨214, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨214, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨213, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_213 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_213 k + 1) (k.val + 1) < (cut ⟨214, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_213 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_213 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_213 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_213 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_213 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_213 ⟨1, by omega⟩ + 1 ≤ xg_213 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_213 k : ℝ) ≤ Chebyshev.theta ((xg_213 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1609
    · exact Work.RHContract.RegionI.thV_36
    · exact Work.RHContract.RegionI.thV_10
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((13691 : ℕ) : ℝ) ≤ (((2831884622819 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1617
  have hSx : (((90448080423 : ℚ) / 200000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 13619, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1609
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_213 k := by decide +kernel
  have hT2 : (∑ k, tg_213 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_213 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_213 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2831884622819 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_213 k))
      + ((((90448080423 : ℚ) / 200000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_213 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_213 (yg_213 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨213, by omega⟩ : ℚ)) (εB := (cut ⟨214, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_213 yg_213 tg_213 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2831884622819 : ℚ) / 1000000000000)) (((90448080423 : ℚ) / 200000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_214 : Fin 16 → ℕ := fun k => [13691, 157, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_214 : Fin 16 → ℕ := fun k => [13751, 160, 33, 14, 8, 6, 4, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_214 : Fin 16 → ℚ := fun k => [((6771552142988849 : ℚ) / 500000000000), ((35430278901909 : ℚ) / 250000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_214 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨214, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨215, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨215, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨214, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_214 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_214 k + 1) (k.val + 1) < (cut ⟨215, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_214 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_214 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_214 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_214 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_214 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_214 ⟨1, by omega⟩ + 1 ≤ xg_214 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_214 k : ℝ) ≤ Chebyshev.theta ((xg_214 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1617
    · exact Work.RHContract.RegionI.thV_36
    · exact Work.RHContract.RegionI.thV_10
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((13751 : ℕ) : ℝ) ≤ (((2832467873559 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1625
  have hSx : (((452240444957 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 13691, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1617
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_214 k := by decide +kernel
  have hT2 : (∑ k, tg_214 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_214 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_214 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2832467873559 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_214 k))
      + ((((452240444957 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_214 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_214 (yg_214 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨214, by omega⟩ : ℚ)) (εB := (cut ⟨215, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_214 yg_214 tg_214 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2832467873559 : ℚ) / 1000000000000)) (((452240444957 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_215 : Fin 16 → ℕ := fun k => [13751, 157, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_215 : Fin 16 → ℕ := fun k => [13829, 160, 33, 14, 8, 6, 4, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_215 : Fin 16 → ℚ := fun k => [((1361931526344433 : ℚ) / 100000000000), ((35430278901909 : ℚ) / 250000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_215 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨215, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨216, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨216, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨215, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_215 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_215 k + 1) (k.val + 1) < (cut ⟨216, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_215 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_215 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_215 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_215 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_215 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_215 ⟨1, by omega⟩ + 1 ≤ xg_215 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_215 k : ℝ) ≤ Chebyshev.theta ((xg_215 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1625
    · exact Work.RHContract.RegionI.thV_36
    · exact Work.RHContract.RegionI.thV_10
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((13829 : ℕ) : ℝ) ≤ (((354131027033 : ℚ) / 125000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1633
  have hSx : (((452240487473 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 13751, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1625
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_215 k := by decide +kernel
  have hT2 : (∑ k, tg_215 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_215 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_215 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((354131027033 : ℚ) / 125000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_215 k))
      + ((((452240487473 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_215 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_215 (yg_215 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨215, by omega⟩ : ℚ)) (εB := (cut ⟨216, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_215 yg_215 tg_215 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((354131027033 : ℚ) / 125000000000)) (((452240487473 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_216 : Fin 16 → ℕ := fun k => [13829, 157, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_216 : Fin 16 → ℕ := fun k => [13901, 161, 33, 14, 8, 6, 4, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_216 : Fin 16 → ℚ := fun k => [((13695566232099009 : ℚ) / 1000000000000), ((35430278901909 : ℚ) / 250000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_216 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨216, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨217, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨217, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨216, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_216 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_216 k + 1) (k.val + 1) < (cut ⟨217, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_216 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_216 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_216 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_216 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_216 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_216 ⟨1, by omega⟩ + 1 ≤ xg_216 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_216 k : ℝ) ≤ Chebyshev.theta ((xg_216 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1633
    · exact Work.RHContract.RegionI.thV_36
    · exact Work.RHContract.RegionI.thV_10
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((13901 : ℕ) : ℝ) ≤ (((2833625106073 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1641
  have hSx : (((90448105913 : ℚ) / 200000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 13829, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1633
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_216 k := by decide +kernel
  have hT2 : (∑ k, tg_216 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_216 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_216 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2833625106073 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_216 k))
      + ((((90448105913 : ℚ) / 200000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_216 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_216 (yg_216 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨216, by omega⟩ : ℚ)) (εB := (cut ⟨217, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_216 yg_216 tg_216 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2833625106073 : ℚ) / 1000000000000)) (((90448105913 : ℚ) / 200000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_217 : Fin 16 → ℕ := fun k => [13901, 157, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_217 : Fin 16 → ℕ := fun k => [13967, 161, 33, 14, 8, 6, 4, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_217 : Fin 16 → ℚ := fun k => [((688593246842569 : ℚ) / 50000000000), ((35430278901909 : ℚ) / 250000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_217 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨217, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨218, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨218, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨217, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_217 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_217 k + 1) (k.val + 1) < (cut ⟨218, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_217 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_217 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_217 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_217 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_217 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_217 ⟨1, by omega⟩ + 1 ≤ xg_217 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_217 k : ℝ) ≤ Chebyshev.theta ((xg_217 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1641
    · exact Work.RHContract.RegionI.thV_36
    · exact Work.RHContract.RegionI.thV_10
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((13967 : ℕ) : ℝ) ≤ (((566839887717 : ℚ) / 200000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1649
  have hSx : (((452240571157 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 13901, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1641
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_217 k := by decide +kernel
  have hT2 : (∑ k, tg_217 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_217 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_217 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((566839887717 : ℚ) / 200000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_217 k))
      + ((((452240571157 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_217 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_217 (yg_217 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨217, by omega⟩ : ℚ)) (εB := (cut ⟨218, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_217 yg_217 tg_217 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((566839887717 : ℚ) / 200000000000)) (((452240571157 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_218 : Fin 16 → ℕ := fun k => [13967, 157, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_218 : Fin 16 → ℕ := fun k => [14071, 162, 33, 14, 8, 6, 4, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_218 : Fin 16 → ℚ := fun k => [((1731024897904411 : ℚ) / 125000000000), ((35430278901909 : ℚ) / 250000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_218 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨218, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨219, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨219, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨218, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_218 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_218 k + 1) (k.val + 1) < (cut ⟨219, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_218 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_218 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_218 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_218 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_218 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_218 ⟨1, by omega⟩ + 1 ≤ xg_218 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_218 k : ℝ) ≤ Chebyshev.theta ((xg_218 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1649
    · exact Work.RHContract.RegionI.thV_36
    · exact Work.RHContract.RegionI.thV_10
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((14071 : ℕ) : ℝ) ≤ (((1417420506053 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1658
  have hSx : (((14132519137 : ℚ) / 31250000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 13967, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1649
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_218 k := by decide +kernel
  have hT2 : (∑ k, tg_218 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_218 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_218 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1417420506053 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_218 k))
      + ((((14132519137 : ℚ) / 31250000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_218 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_218 (yg_218 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨218, by omega⟩ : ℚ)) (εB := (cut ⟨219, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_218 yg_218 tg_218 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1417420506053 : ℚ) / 500000000000)) (((14132519137 : ℚ) / 31250000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_219 : Fin 16 → ℕ := fun k => [14071, 157, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_219 : Fin 16 → ℕ := fun k => [14173, 162, 33, 14, 8, 6, 4, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_219 : Fin 16 → ℚ := fun k => [((3483534705166757 : ℚ) / 250000000000), ((35430278901909 : ℚ) / 250000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_219 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨219, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨220, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨220, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨219, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_219 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_219 k + 1) (k.val + 1) < (cut ⟨220, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_219 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_219 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_219 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_219 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_219 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_219 ⟨1, by omega⟩ + 1 ≤ xg_219 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_219 k : ℝ) ≤ Chebyshev.theta ((xg_219 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1658
    · exact Work.RHContract.RegionI.thV_36
    · exact Work.RHContract.RegionI.thV_10
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((14173 : ℕ) : ℝ) ≤ (((2835478156449 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1667
  have hSx : (((7066260283 : ℚ) / 15625000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 14071, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1658
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_219 k := by decide +kernel
  have hT2 : (∑ k, tg_219 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_219 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_219 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2835478156449 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_219 k))
      + ((((7066260283 : ℚ) / 15625000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_219 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_219 (yg_219 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨219, by omega⟩ : ℚ)) (εB := (cut ⟨220, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_219 yg_219 tg_219 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2835478156449 : ℚ) / 1000000000000)) (((7066260283 : ℚ) / 15625000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_220 : Fin 16 → ℕ := fun k => [14173, 157, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_220 : Fin 16 → ℕ := fun k => [14281, 163, 33, 14, 8, 6, 4, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_220 : Fin 16 → ℚ := fun k => [((14020140816007463 : ℚ) / 1000000000000), ((35430278901909 : ℚ) / 250000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_220 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨220, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨221, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨221, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨220, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_220 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_220 k + 1) (k.val + 1) < (cut ⟨221, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_220 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_220 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_220 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_220 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_220 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_220 ⟨1, by omega⟩ + 1 ≤ xg_220 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_220 k : ℝ) ≤ Chebyshev.theta ((xg_220 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1667
    · exact Work.RHContract.RegionI.thV_36
    · exact Work.RHContract.RegionI.thV_10
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((14281 : ℕ) : ℝ) ≤ (((709010110177 : ℚ) / 250000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1675
  have hSx : (((113060175803 : ℚ) / 250000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 14173, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1667
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_220 k := by decide +kernel
  have hT2 : (∑ k, tg_220 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_220 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_220 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((709010110177 : ℚ) / 250000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_220 k))
      + ((((113060175803 : ℚ) / 250000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_220 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_220 (yg_220 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨220, by omega⟩ : ℚ)) (εB := (cut ⟨221, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_220 yg_220 tg_220 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((709010110177 : ℚ) / 250000000000)) (((113060175803 : ℚ) / 250000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_221 : Fin 16 → ℕ := fun k => [14281, 163, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_221 : Fin 16 → ℕ := fun k => [14387, 163, 33, 14, 8, 6, 4, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_221 : Fin 16 → ℚ := fun k => [((14096644673715307 : ℚ) / 1000000000000), ((146814865806623 : ℚ) / 1000000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_221 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨221, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨222, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨222, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨221, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_221 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_221 k + 1) (k.val + 1) < (cut ⟨222, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_221 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_221 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_221 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_221 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_221 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_221 ⟨1, by omega⟩ + 1 ≤ xg_221 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_221 k : ℝ) ≤ Chebyshev.theta ((xg_221 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1675
    · exact Work.RHContract.RegionI.thV_37
    · exact Work.RHContract.RegionI.thV_10
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((14387 : ℕ) : ℝ) ≤ (((567333663701 : ℚ) / 200000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1684
  have hSx : (((226120371363 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 14281, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1675
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_221 k := by decide +kernel
  have hT2 : (∑ k, tg_221 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_221 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_221 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((567333663701 : ℚ) / 200000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_221 k))
      + ((((226120371363 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_221 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_221 (yg_221 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨221, by omega⟩ : ℚ)) (εB := (cut ⟨222, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_221 yg_221 tg_221 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((567333663701 : ℚ) / 200000000000)) (((226120371363 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_222 : Fin 16 → ℕ := fun k => [14387, 163, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_222 : Fin 16 → ℕ := fun k => [14447, 164, 33, 14, 8, 6, 4, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_222 : Fin 16 → ℚ := fun k => [((7091389255731749 : ℚ) / 500000000000), ((146814865806623 : ℚ) / 1000000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_222 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨222, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨223, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨223, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨222, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_222 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_222 k + 1) (k.val + 1) < (cut ⟨223, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_222 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_222 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_222 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_222 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_222 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_222 ⟨1, by omega⟩ + 1 ≤ xg_222 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_222 k : ℝ) ≤ Chebyshev.theta ((xg_222 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1684
    · exact Work.RHContract.RegionI.thV_37
    · exact Work.RHContract.RegionI.thV_10
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((14447 : ℕ) : ℝ) ≤ (((2837292546351 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1693
  have hSx : (((452240786523 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 14387, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1684
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_222 k := by decide +kernel
  have hT2 : (∑ k, tg_222 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_222 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_222 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2837292546351 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_222 k))
      + ((((452240786523 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_222 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_222 (yg_222 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨222, by omega⟩ : ℚ)) (εB := (cut ⟨223, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_222 yg_222 tg_222 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2837292546351 : ℚ) / 1000000000000)) (((452240786523 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_223 : Fin 16 → ℕ := fun k => [14447, 163, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_223 : Fin 16 → ℕ := fun k => [14543, 164, 33, 14, 8, 6, 4, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_223 : Fin 16 → ℚ := fun k => [((1783620600920541 : ℚ) / 125000000000), ((146814865806623 : ℚ) / 1000000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_223 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨223, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨224, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨224, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨223, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_223 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_223 k + 1) (k.val + 1) < (cut ⟨224, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_223 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_223 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_223 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_223 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_223 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_223 ⟨1, by omega⟩ + 1 ≤ xg_223 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_223 k : ℝ) ≤ Chebyshev.theta ((xg_223 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1693
    · exact Work.RHContract.RegionI.thV_37
    · exact Work.RHContract.RegionI.thV_10
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((14543 : ℕ) : ℝ) ≤ (((2837913198651 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1702
  have hSx : (((45224082981 : ℚ) / 100000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 14447, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1693
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_223 k := by decide +kernel
  have hT2 : (∑ k, tg_223 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_223 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_223 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2837913198651 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_223 k))
      + ((((45224082981 : ℚ) / 100000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_223 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_223 (yg_223 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨223, by omega⟩ : ℚ)) (εB := (cut ⟨224, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_223 yg_223 tg_223 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2837913198651 : ℚ) / 1000000000000)) (((45224082981 : ℚ) / 100000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_224 : Fin 16 → ℕ := fun k => [14543, 163, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_224 : Fin 16 → ℕ := fun k => [14627, 165, 33, 14, 8, 6, 4, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_224 : Fin 16 → ℚ := fun k => [((2871040563395279 : ℚ) / 200000000000), ((146814865806623 : ℚ) / 1000000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_224 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨224, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨225, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨225, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨224, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_224 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_224 k + 1) (k.val + 1) < (cut ⟨225, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_224 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_224 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_224 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_224 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_224 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_224 ⟨1, by omega⟩ + 1 ≤ xg_224 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_224 k : ℝ) ≤ Chebyshev.theta ((xg_224 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1702
    · exact Work.RHContract.RegionI.thV_37
    · exact Work.RHContract.RegionI.thV_10
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((14627 : ℕ) : ℝ) ≤ (((354816317377 : ℚ) / 125000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1711
  have hSx : (((113060218151 : ℚ) / 250000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 14543, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1702
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_224 k := by decide +kernel
  have hT2 : (∑ k, tg_224 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_224 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_224 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((354816317377 : ℚ) / 125000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_224 k))
      + ((((113060218151 : ℚ) / 250000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_224 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_224 (yg_224 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨224, by omega⟩ : ℚ)) (εB := (cut ⟨225, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_224 yg_224 tg_224 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((354816317377 : ℚ) / 125000000000)) (((113060218151 : ℚ) / 250000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_225 : Fin 16 → ℕ := fun k => [14627, 163, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_225 : Fin 16 → ℕ := fun k => [14713, 165, 33, 14, 8, 6, 4, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_225 : Fin 16 → ℚ := fun k => [((14441488974053447 : ℚ) / 1000000000000), ((146814865806623 : ℚ) / 1000000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_225 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨225, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨226, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨226, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨225, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_225 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_225 k + 1) (k.val + 1) < (cut ⟨226, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_225 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_225 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_225 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_225 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_225 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_225 ⟨1, by omega⟩ + 1 ≤ xg_225 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_225 k : ℝ) ≤ Chebyshev.theta ((xg_225 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1711
    · exact Work.RHContract.RegionI.thV_37
    · exact Work.RHContract.RegionI.thV_10
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((14713 : ℕ) : ℝ) ≤ (((283914431477 : ℚ) / 100000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1720
  have hSx : (((452240914943 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 14627, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1711
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_225 k := by decide +kernel
  have hT2 : (∑ k, tg_225 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_225 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_225 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((283914431477 : ℚ) / 100000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_225 k))
      + ((((452240914943 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_225 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_225 (yg_225 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨225, by omega⟩ : ℚ)) (εB := (cut ⟨226, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_225 yg_225 tg_225 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((283914431477 : ℚ) / 100000000000)) (((452240914943 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_226 : Fin 16 → ℕ := fun k => [14713, 163, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_226 : Fin 16 → ℕ := fun k => [14767, 166, 33, 14, 8, 6, 4, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_226 : Fin 16 → ℚ := fun k => [((14527827246682327 : ℚ) / 1000000000000), ((146814865806623 : ℚ) / 1000000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_226 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨226, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨227, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨227, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨226, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_226 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_226 k + 1) (k.val + 1) < (cut ⟨227, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_226 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_226 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_226 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_226 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_226 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_226 ⟨1, by omega⟩ + 1 ≤ xg_226 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_226 k : ℝ) ≤ Chebyshev.theta ((xg_226 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1720
    · exact Work.RHContract.RegionI.thV_37
    · exact Work.RHContract.RegionI.thV_10
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((14767 : ℕ) : ℝ) ≤ (((1419877425291 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1729
  have hSx : (((226120478397 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 14713, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1720
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_226 k := by decide +kernel
  have hT2 : (∑ k, tg_226 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_226 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_226 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1419877425291 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_226 k))
      + ((((226120478397 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_226 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_226 (yg_226 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨226, by omega⟩ : ℚ)) (εB := (cut ⟨227, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_226 yg_226 tg_226 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1419877425291 : ℚ) / 500000000000)) (((226120478397 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_227 : Fin 16 → ℕ := fun k => [14767, 163, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_227 : Fin 16 → ℕ := fun k => [14843, 166, 33, 14, 8, 6, 4, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_227 : Fin 16 → ℚ := fun k => [((14614213140681837 : ℚ) / 1000000000000), ((146814865806623 : ℚ) / 1000000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_227 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨227, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨228, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨228, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨227, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_227 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_227 k + 1) (k.val + 1) < (cut ⟨228, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_227 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_227 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_227 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_227 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_227 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_227 ⟨1, by omega⟩ + 1 ≤ xg_227 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_227 k : ℝ) ≤ Chebyshev.theta ((xg_227 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1729
    · exact Work.RHContract.RegionI.thV_37
    · exact Work.RHContract.RegionI.thV_10
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((14843 : ℕ) : ℝ) ≤ (((568072536847 : ℚ) / 200000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1738
  have hSx : (((113060249551 : ℚ) / 250000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 14767, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1729
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_227 k := by decide +kernel
  have hT2 : (∑ k, tg_227 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_227 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_227 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((568072536847 : ℚ) / 200000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_227 k))
      + ((((113060249551 : ℚ) / 250000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_227 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_227 (yg_227 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨227, by omega⟩ : ℚ)) (εB := (cut ⟨228, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_227 yg_227 tg_227 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((568072536847 : ℚ) / 200000000000)) (((113060249551 : ℚ) / 250000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_228 : Fin 16 → ℕ := fun k => [14843, 163, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_228 : Fin 16 → ℕ := fun k => [14929, 166, 34, 14, 8, 6, 4, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_228 : Fin 16 → ℚ := fun k => [((14700638961614001 : ℚ) / 1000000000000), ((146814865806623 : ℚ) / 1000000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_228 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨228, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨229, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨229, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨228, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_228 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_228 k + 1) (k.val + 1) < (cut ⟨229, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_228 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_228 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_228 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_228 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_228 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_228 ⟨1, by omega⟩ + 1 ≤ xg_228 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_228 k : ℝ) ≤ Chebyshev.theta ((xg_228 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1738
    · exact Work.RHContract.RegionI.thV_37
    · exact Work.RHContract.RegionI.thV_10
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((14929 : ℕ) : ℝ) ≤ (((113638688613 : ℚ) / 40000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1747
  have hSx : (((28265064953 : ℚ) / 62500000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 14843, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1738
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_228 k := by decide +kernel
  have hT2 : (∑ k, tg_228 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_228 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_228 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((113638688613 : ℚ) / 40000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_228 k))
      + ((((28265064953 : ℚ) / 62500000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_228 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_228 (yg_228 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨228, by omega⟩ : ℚ)) (εB := (cut ⟨229, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_228 yg_228 tg_228 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((113638688613 : ℚ) / 40000000000)) (((28265064953 : ℚ) / 62500000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_229 : Fin 16 → ℕ := fun k => [14929, 163, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_229 : Fin 16 → ℕ := fun k => [15017, 167, 34, 14, 8, 6, 4, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_229 : Fin 16 → ℚ := fun k => [((1848389226762573 : ℚ) / 125000000000), ((146814865806623 : ℚ) / 1000000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_229 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨229, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨230, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨230, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨229, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_229 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_229 k + 1) (k.val + 1) < (cut ⟨230, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_229 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_229 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_229 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_229 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_229 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_229 ⟨1, by omega⟩ + 1 ≤ xg_229 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_229 k : ℝ) ≤ Chebyshev.theta ((xg_229 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1747
    · exact Work.RHContract.RegionI.thV_37
    · exact Work.RHContract.RegionI.thV_10
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((15017 : ℕ) : ℝ) ≤ (((177593847861 : ℚ) / 62500000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1755
  have hSx : (((452241079849 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 14929, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1747
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_229 k := by decide +kernel
  have hT2 : (∑ k, tg_229 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_229 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_229 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((177593847861 : ℚ) / 62500000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_229 k))
      + ((((452241079849 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_229 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_229 (yg_229 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨229, by omega⟩ : ℚ)) (εB := (cut ⟨230, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_229 yg_229 tg_229 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((177593847861 : ℚ) / 62500000000)) (((452241079849 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_230 : Fin 16 → ℕ := fun k => [15017, 167, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_230 : Fin 16 → ℕ := fun k => [15107, 167, 34, 14, 8, 6, 4, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_230 : Fin 16 → ℚ := fun k => [((7432012648385149 : ℚ) / 500000000000), ((7596642980861 : ℚ) / 50000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_230 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨230, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨231, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨231, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨230, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_230 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_230 k + 1) (k.val + 1) < (cut ⟨231, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_230 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_230 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_230 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_230 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_230 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_230 ⟨1, by omega⟩ + 1 ≤ xg_230 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_230 k : ℝ) ≤ Chebyshev.theta ((xg_230 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1755
    · exact Work.RHContract.RegionI.thV_38
    · exact Work.RHContract.RegionI.thV_10
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((15107 : ℕ) : ℝ) ≤ (((2842098593063 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1764
  have hSx : (((226120557767 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 15017, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1755
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_230 k := by decide +kernel
  have hT2 : (∑ k, tg_230 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_230 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_230 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2842098593063 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_230 k))
      + ((((226120557767 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_230 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_230 (yg_230 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨230, by omega⟩ : ℚ)) (εB := (cut ⟨231, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_230 yg_230 tg_230 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2842098593063 : ℚ) / 1000000000000)) (((226120557767 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_231 : Fin 16 → ℕ := fun k => [15107, 167, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_231 : Fin 16 → ℕ := fun k => [15193, 168, 34, 14, 9, 6, 4, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_231 : Fin 16 → ℚ := fun k => [((14950612556382381 : ℚ) / 1000000000000), ((7596642980861 : ℚ) / 50000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_231 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨231, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨232, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨232, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨231, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_231 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_231 k + 1) (k.val + 1) < (cut ⟨232, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_231 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_231 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_231 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_231 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_231 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_231 ⟨1, by omega⟩ + 1 ≤ xg_231 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_231 k : ℝ) ≤ Chebyshev.theta ((xg_231 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1764
    · exact Work.RHContract.RegionI.thV_38
    · exact Work.RHContract.RegionI.thV_10
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((15193 : ℕ) : ℝ) ≤ (((2842692494977 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1773
  have hSx : (((452241155133 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 15107, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1764
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_231 k := by decide +kernel
  have hT2 : (∑ k, tg_231 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_231 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_231 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2842692494977 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_231 k))
      + ((((452241155133 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_231 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_231 (yg_231 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨231, by omega⟩ : ℚ)) (εB := (cut ⟨232, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_231 yg_231 tg_231 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2842692494977 : ℚ) / 1000000000000)) (((452241155133 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_232 : Fin 16 → ℕ := fun k => [15193, 167, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_232 : Fin 16 → ℕ := fun k => [15271, 168, 34, 15, 9, 6, 4, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_232 : Fin 16 → ℚ := fun k => [((15037247053252841 : ℚ) / 1000000000000), ((7596642980861 : ℚ) / 50000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_232 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨232, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨233, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨233, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨232, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_232 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_232 k + 1) (k.val + 1) < (cut ⟨233, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_232 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_232 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_232 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_232 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_232 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_232 ⟨1, by omega⟩ + 1 ≤ xg_232 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_232 k : ℝ) ≤ Chebyshev.theta ((xg_232 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1773
    · exact Work.RHContract.RegionI.thV_38
    · exact Work.RHContract.RegionI.thV_10
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((15271 : ℕ) : ℝ) ≤ (((1421641492587 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1782
  have hSx : (((452241194317 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 15193, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1773
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_232 k := by decide +kernel
  have hT2 : (∑ k, tg_232 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_232 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_232 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1421641492587 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_232 k))
      + ((((452241194317 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_232 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_232 (yg_232 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨232, by omega⟩ : ℚ)) (εB := (cut ⟨233, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_232 yg_232 tg_232 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1421641492587 : ℚ) / 500000000000)) (((452241194317 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_233 : Fin 16 → ℕ := fun k => [15271, 167, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_233 : Fin 16 → ℕ := fun k => [15331, 169, 34, 15, 9, 6, 4, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_233 : Fin 16 → ℚ := fun k => [((7561966699189673 : ℚ) / 500000000000), ((7596642980861 : ℚ) / 50000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_233 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨233, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨234, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨234, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨233, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_233 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_233 k + 1) (k.val + 1) < (cut ⟨234, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_233 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_233 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_233 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_233 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_233 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_233 ⟨1, by omega⟩ + 1 ≤ xg_233 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_233 k : ℝ) ≤ Chebyshev.theta ((xg_233 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1782
    · exact Work.RHContract.RegionI.thV_38
    · exact Work.RHContract.RegionI.thV_10
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((15331 : ℕ) : ℝ) ≤ (((2843871022711 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1791
  have hSx : (((452241233051 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 15271, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1782
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_233 k := by decide +kernel
  have hT2 : (∑ k, tg_233 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_233 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_233 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2843871022711 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_233 k))
      + ((((452241233051 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_233 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_233 (yg_233 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨233, by omega⟩ : ℚ)) (εB := (cut ⟨234, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_233 yg_233 tg_233 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2843871022711 : ℚ) / 1000000000000)) (((452241233051 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_234 : Fin 16 → ℕ := fun k => [15331, 167, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_234 : Fin 16 → ℕ := fun k => [15413, 169, 34, 15, 9, 6, 4, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_234 : Fin 16 → ℚ := fun k => [((15210657197816019 : ℚ) / 1000000000000), ((7596642980861 : ℚ) / 50000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_234 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨234, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨235, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨235, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨234, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_234 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_234 k + 1) (k.val + 1) < (cut ⟨235, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_234 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_234 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_234 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_234 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_234 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_234 ⟨1, by omega⟩ + 1 ≤ xg_234 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_234 k : ℝ) ≤ Chebyshev.theta ((xg_234 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1791
    · exact Work.RHContract.RegionI.thV_38
    · exact Work.RHContract.RegionI.thV_10
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((15413 : ℕ) : ℝ) ≤ (((2844456273211 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1800
  have hSx : (((90448254293 : ℚ) / 200000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 15331, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1791
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_234 k := by decide +kernel
  have hT2 : (∑ k, tg_234 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_234 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_234 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2844456273211 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_234 k))
      + ((((90448254293 : ℚ) / 200000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_234 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_234 (yg_234 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨234, by omega⟩ : ℚ)) (εB := (cut ⟨235, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_234 yg_234 tg_234 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2844456273211 : ℚ) / 1000000000000)) (((90448254293 : ℚ) / 200000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_235 : Fin 16 → ℕ := fun k => [15413, 167, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_235 : Fin 16 → ℕ := fun k => [15497, 170, 34, 15, 9, 6, 4, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_235 : Fin 16 → ℚ := fun k => [((15297423754361549 : ℚ) / 1000000000000), ((7596642980861 : ℚ) / 50000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_235 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨235, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨236, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨236, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨235, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_235 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_235 k + 1) (k.val + 1) < (cut ⟨236, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_235 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_235 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_235 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_235 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_235 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_235 ⟨1, by omega⟩ + 1 ≤ xg_235 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_235 k : ℝ) ≤ Chebyshev.theta ((xg_235 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1800
    · exact Work.RHContract.RegionI.thV_38
    · exact Work.RHContract.RegionI.thV_10
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((15497 : ℕ) : ℝ) ≤ (((1422519197367 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1809
  have hSx : (((452241309517 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 15413, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1800
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_235 k := by decide +kernel
  have hT2 : (∑ k, tg_235 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_235 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_235 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1422519197367 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_235 k))
      + ((((452241309517 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_235 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_235 (yg_235 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨235, by omega⟩ : ℚ)) (εB := (cut ⟨236, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_235 yg_235 tg_235 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1422519197367 : ℚ) / 500000000000)) (((452241309517 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_236 : Fin 16 → ℕ := fun k => [15497, 167, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_236 : Fin 16 → ℕ := fun k => [15601, 170, 34, 15, 9, 6, 4, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_236 : Fin 16 → ℚ := fun k => [((15384238558172573 : ℚ) / 1000000000000), ((7596642980861 : ℚ) / 50000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_236 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨236, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨237, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨237, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨236, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_236 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_236 k + 1) (k.val + 1) < (cut ⟨237, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_236 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_236 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_236 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_236 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_236 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_236 ⟨1, by omega⟩ + 1 ≤ xg_236 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_236 k : ℝ) ≤ Chebyshev.theta ((xg_236 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1809
    · exact Work.RHContract.RegionI.thV_38
    · exact Work.RHContract.RegionI.thV_10
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((15601 : ℕ) : ℝ) ≤ (((711404222871 : ℚ) / 250000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1818
  have hSx : (((226120673581 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 15497, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1809
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_236 k := by decide +kernel
  have hT2 : (∑ k, tg_236 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_236 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_236 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((711404222871 : ℚ) / 250000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_236 k))
      + ((((226120673581 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_236 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_236 (yg_236 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨236, by omega⟩ : ℚ)) (εB := (cut ⟨237, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_236 yg_236 tg_236 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((711404222871 : ℚ) / 250000000000)) (((226120673581 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_237 : Fin 16 → ℕ := fun k => [15601, 167, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_237 : Fin 16 → ℕ := fun k => [15667, 171, 34, 15, 9, 6, 4, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_237 : Fin 16 → ℚ := fun k => [((15471109581006313 : ℚ) / 1000000000000), ((7596642980861 : ℚ) / 50000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_237 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨237, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨238, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨238, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨237, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_237 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_237 k + 1) (k.val + 1) < (cut ⟨238, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_237 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_237 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_237 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_237 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_237 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_237 ⟨1, by omega⟩ + 1 ≤ xg_237 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_237 k : ℝ) ≤ Chebyshev.theta ((xg_237 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1818
    · exact Work.RHContract.RegionI.thV_38
    · exact Work.RHContract.RegionI.thV_10
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((15667 : ℕ) : ℝ) ≤ (((1423096172983 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1827
  have hSx : (((22612069217 : ℚ) / 50000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 15601, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1818
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_237 k := by decide +kernel
  have hT2 : (∑ k, tg_237 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_237 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_237 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1423096172983 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_237 k))
      + ((((22612069217 : ℚ) / 50000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_237 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_237 (yg_237 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨237, by omega⟩ : ℚ)) (εB := (cut ⟨238, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_237 yg_237 tg_237 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1423096172983 : ℚ) / 500000000000)) (((22612069217 : ℚ) / 50000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_238 : Fin 16 → ℕ := fun k => [15667, 167, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_238 : Fin 16 → ℕ := fun k => [15749, 171, 34, 15, 9, 6, 4, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_238 : Fin 16 → ℚ := fun k => [((7779014024932349 : ℚ) / 500000000000), ((7596642980861 : ℚ) / 50000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_238 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨238, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨239, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨239, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨238, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_238 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_238 k + 1) (k.val + 1) < (cut ⟨239, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_238 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_238 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_238 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_238 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_238 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_238 ⟨1, by omega⟩ + 1 ≤ xg_238 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_238 k : ℝ) ≤ Chebyshev.theta ((xg_238 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1827
    · exact Work.RHContract.RegionI.thV_38
    · exact Work.RHContract.RegionI.thV_10
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((15749 : ℕ) : ℝ) ≤ (((711691252649 : ℚ) / 250000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1836
  have hSx : (((56530177641 : ℚ) / 125000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 15667, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1827
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_238 k := by decide +kernel
  have hT2 : (∑ k, tg_238 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_238 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_238 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((711691252649 : ℚ) / 250000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_238 k))
      + ((((56530177641 : ℚ) / 125000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_238 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_238 (yg_238 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨238, by omega⟩ : ℚ)) (εB := (cut ⟨239, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_238 yg_238 tg_238 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((711691252649 : ℚ) / 250000000000)) (((56530177641 : ℚ) / 125000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_239 : Fin 16 → ℕ := fun k => [15749, 167, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_239 : Fin 16 → ℕ := fun k => [15817, 171, 34, 15, 9, 6, 4, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_239 : Fin 16 → ℚ := fun k => [((782249513233459 : ℚ) / 50000000000), ((7596642980861 : ℚ) / 50000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_239 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨239, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨240, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨240, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨239, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_239 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_239 k + 1) (k.val + 1) < (cut ⟨240, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_239 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_239 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_239 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_239 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_239 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_239 ⟨1, by omega⟩ + 1 ≤ xg_239 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_239 k : ℝ) ≤ Chebyshev.theta ((xg_239 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1836
    · exact Work.RHContract.RegionI.thV_38
    · exact Work.RHContract.RegionI.thV_10
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((15817 : ℕ) : ℝ) ≤ (((1423667515231 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1845
  have hSx : (((452241457557 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 15749, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1836
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_239 k := by decide +kernel
  have hT2 : (∑ k, tg_239 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_239 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_239 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1423667515231 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_239 k))
      + ((((452241457557 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_239 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_239 (yg_239 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨239, by omega⟩ : ℚ)) (εB := (cut ⟨240, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_239 yg_239 tg_239 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1423667515231 : ℚ) / 500000000000)) (((452241457557 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

end

end Work.RHContract.A.RegionI
