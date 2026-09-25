import Mathlib
import Submission.Work.RHContract.A.RegionI.Core
import Submission.Work.RHContract.A.RegionI.blockCert
import Submission.Work.RHContract.A.RegionI.Data11
import Submission.Work.RHContract.A.RegionI.Cuts

/-!  Region I: group certificates.  GENERATED FILE. -/

open scoped BigOperators

namespace Work.RHContract.A.RegionI

noncomputable section

private def xg_0 : Fin 12 → ℕ := fun k => [1523, 47, 13, 7, 5, 3, 3, 3, 2, 2, 2, 2].getD k.val 0
private def yg_0 : Fin 13 → ℕ := fun k => [1549, 53, 15, 8, 5, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_0 : Fin 12 → ℚ := fun k => [((1476790615592679 : ℚ) / 1000000000000), ((40960219417829 : ℚ) / 1000000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_0 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨0, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨1, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (13 + 1) < (cut ⟨1, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 12, (cut ⟨0, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_0 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 13, Work.RHContract.RegionI.Fhi (yg_0 k + 1) (k.val + 1) < (cut ⟨1, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 12, 2 ≤ xg_0 k := by decide +kernel
  have hxhi : ∀ k : Fin 12, xg_0 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 13, yg_0 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 13, 1 ≤ yg_0 k := by decide +kernel
  have hposy : ∀ k : Fin 13, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_0 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_0 ⟨1, by omega⟩ + 1 ≤ xg_0 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 12, (tg_0 k : ℝ) ≤ Chebyshev.theta ((xg_0 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_240
    · exact Work.RHContract.RegionI.thV_14
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((1549 : ℕ) : ℝ) ≤ (((1287286593769 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_243
  have hSx : (((14130270203 : ℚ) / 31250000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 1523, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_240
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_0 k := by decide +kernel
  have hT2 : (∑ k, tg_0 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_0 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_0 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1287286593769 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_0 k))
      + ((((14130270203 : ℚ) / 31250000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_0 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_0 (yg_0 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨0, by omega⟩ : ℚ)) (εB := (cut ⟨1, by omega⟩ : ℚ)) hhi hlo
    12 13 (by norm_num) (by norm_num) hKtop xg_0 yg_0 tg_0 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1287286593769 : ℚ) / 500000000000)) (((14130270203 : ℚ) / 31250000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_1 : Fin 13 → ℕ := fun k => [1549, 53, 13, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_1 : Fin 13 → ℕ := fun k => [1571, 53, 15, 8, 5, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_1 : Fin 13 → ℚ := fun k => [((1498811140673317 : ℚ) / 1000000000000), ((44930511330081 : ℚ) / 1000000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_1 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨1, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨2, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (13 + 1) < (cut ⟨2, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 13, (cut ⟨1, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_1 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 13, Work.RHContract.RegionI.Fhi (yg_1 k + 1) (k.val + 1) < (cut ⟨2, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 13, 2 ≤ xg_1 k := by decide +kernel
  have hxhi : ∀ k : Fin 13, xg_1 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 13, yg_1 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 13, 1 ≤ yg_1 k := by decide +kernel
  have hposy : ∀ k : Fin 13, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_1 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_1 ⟨1, by omega⟩ + 1 ≤ xg_1 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 13, (tg_1 k : ℝ) ≤ Chebyshev.theta ((xg_1 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_243
    · exact Work.RHContract.RegionI.thV_15
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((1571 : ℕ) : ℝ) ≤ (((644283514573 : ℚ) / 250000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_247
  have hSx : (((56521238739 : ℚ) / 125000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 1549, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_243
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_1 k := by decide +kernel
  have hT2 : (∑ k, tg_1 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_1 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_1 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((644283514573 : ℚ) / 250000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_1 k))
      + ((((56521238739 : ℚ) / 125000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_1 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_1 (yg_1 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨1, by omega⟩ : ℚ)) (εB := (cut ⟨2, by omega⟩ : ℚ)) hhi hlo
    13 13 (by norm_num) (by norm_num) hKtop xg_1 yg_1 tg_1 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((644283514573 : ℚ) / 250000000000)) (((56521238739 : ℚ) / 125000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_2 : Fin 13 → ℕ := fun k => [1571, 53, 13, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_2 : Fin 13 → ℕ := fun k => [1601, 53, 15, 8, 5, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_2 : Fin 13 → ℚ := fun k => [((191028408779467 : ℚ) / 125000000000), ((44930511330081 : ℚ) / 1000000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_2 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨2, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨3, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (13 + 1) < (cut ⟨3, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 13, (cut ⟨2, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_2 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 13, Work.RHContract.RegionI.Fhi (yg_2 k + 1) (k.val + 1) < (cut ⟨3, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 13, 2 ≤ xg_2 k := by decide +kernel
  have hxhi : ∀ k : Fin 13, xg_2 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 13, yg_2 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 13, 1 ≤ yg_2 k := by decide +kernel
  have hposy : ∀ k : Fin 13, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_2 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_2 ⟨1, by omega⟩ + 1 ≤ xg_2 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 13, (tg_2 k : ℝ) ≤ Chebyshev.theta ((xg_2 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_247
    · exact Work.RHContract.RegionI.thV_15
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((1601 : ℕ) : ℝ) ≤ (((2579650657671 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_251
  have hSx : (((56521443551 : ℚ) / 125000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 1571, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_247
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_2 k := by decide +kernel
  have hT2 : (∑ k, tg_2 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_2 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_2 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2579650657671 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_2 k))
      + ((((56521443551 : ℚ) / 125000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_2 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_2 (yg_2 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨2, by omega⟩ : ℚ)) (εB := (cut ⟨3, by omega⟩ : ℚ)) hhi hlo
    13 13 (by norm_num) (by norm_num) hKtop xg_2 yg_2 tg_2 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2579650657671 : ℚ) / 1000000000000)) (((56521443551 : ℚ) / 125000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_3 : Fin 13 → ℕ := fun k => [1601, 53, 13, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_3 : Fin 13 → ℕ := fun k => [1619, 54, 15, 8, 5, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_3 : Fin 13 → ℚ := fun k => [((311542632032137 : ℚ) / 200000000000), ((44930511330081 : ℚ) / 1000000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_3 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨3, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨4, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (13 + 1) < (cut ⟨4, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 13, (cut ⟨3, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_3 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 13, Work.RHContract.RegionI.Fhi (yg_3 k + 1) (k.val + 1) < (cut ⟨4, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 13, 2 ≤ xg_3 k := by decide +kernel
  have hxhi : ∀ k : Fin 13, xg_3 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 13, yg_3 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 13, 1 ≤ yg_3 k := by decide +kernel
  have hposy : ∀ k : Fin 13, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_3 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_3 ⟨1, by omega⟩ + 1 ≤ xg_3 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 13, (tg_3 k : ℝ) ≤ Chebyshev.theta ((xg_3 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_251
    · exact Work.RHContract.RegionI.thV_15
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((1619 : ℕ) : ℝ) ≤ (((103285313491 : ℚ) / 40000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_255
  have hSx : (((452173130781 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 1601, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_251
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_3 k := by decide +kernel
  have hT2 : (∑ k, tg_3 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_3 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_3 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((103285313491 : ℚ) / 40000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_3 k))
      + ((((452173130781 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_3 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_3 (yg_3 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨3, by omega⟩ : ℚ)) (εB := (cut ⟨4, by omega⟩ : ℚ)) hhi hlo
    13 13 (by norm_num) (by norm_num) hKtop xg_3 yg_3 tg_3 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((103285313491 : ℚ) / 40000000000)) (((452173130781 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_4 : Fin 13 → ℕ := fun k => [1619, 53, 13, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_4 : Fin 13 → ℕ := fun k => [1657, 54, 16, 8, 5, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_4 : Fin 13 → ℚ := fun k => [((793627033847409 : ℚ) / 500000000000), ((44930511330081 : ℚ) / 1000000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_4 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨4, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨5, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (13 + 1) < (cut ⟨5, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 13, (cut ⟨4, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_4 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 13, Work.RHContract.RegionI.Fhi (yg_4 k + 1) (k.val + 1) < (cut ⟨5, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 13, 2 ≤ xg_4 k := by decide +kernel
  have hxhi : ∀ k : Fin 13, xg_4 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 13, yg_4 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 13, 1 ≤ yg_4 k := by decide +kernel
  have hposy : ∀ k : Fin 13, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_4 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_4 ⟨1, by omega⟩ + 1 ≤ xg_4 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 13, (tg_4 k : ℝ) ≤ Chebyshev.theta ((xg_4 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_255
    · exact Work.RHContract.RegionI.thV_15
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((1657 : ℕ) : ℝ) ≤ (((646144872647 : ℚ) / 250000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_259
  have hSx : (((22608733507 : ℚ) / 50000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 1619, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_255
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_4 k := by decide +kernel
  have hT2 : (∑ k, tg_4 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_4 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_4 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((646144872647 : ℚ) / 250000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_4 k))
      + ((((22608733507 : ℚ) / 50000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_4 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_4 (yg_4 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨4, by omega⟩ : ℚ)) (εB := (cut ⟨5, by omega⟩ : ℚ)) hhi hlo
    13 13 (by norm_num) (by norm_num) hKtop xg_4 yg_4 tg_4 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((646144872647 : ℚ) / 250000000000)) (((22608733507 : ℚ) / 50000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_5 : Fin 13 → ℕ := fun k => [1657, 53, 13, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_5 : Fin 13 → ℕ := fun k => [1693, 55, 16, 8, 5, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_5 : Fin 13 → ℚ := fun k => [((1616852743908171 : ℚ) / 1000000000000), ((44930511330081 : ℚ) / 1000000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_5 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨5, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨6, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (13 + 1) < (cut ⟨6, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 13, (cut ⟨5, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_5 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 13, Work.RHContract.RegionI.Fhi (yg_5 k + 1) (k.val + 1) < (cut ⟨6, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 13, 2 ≤ xg_5 k := by decide +kernel
  have hxhi : ∀ k : Fin 13, xg_5 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 13, yg_5 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 13, 1 ≤ yg_5 k := by decide +kernel
  have hposy : ∀ k : Fin 13, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_5 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_5 ⟨1, by omega⟩ + 1 ≤ xg_5 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 13, (tg_5 k : ℝ) ≤ Chebyshev.theta ((xg_5 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_259
    · exact Work.RHContract.RegionI.thV_15
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((1693 : ℕ) : ℝ) ≤ (((1293485618551 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_263
  have hSx : (((226088082927 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 1657, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_259
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_5 k := by decide +kernel
  have hT2 : (∑ k, tg_5 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_5 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_5 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1293485618551 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_5 k))
      + ((((226088082927 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_5 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_5 (yg_5 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨5, by omega⟩ : ℚ)) (εB := (cut ⟨6, by omega⟩ : ℚ)) hhi hlo
    13 13 (by norm_num) (by norm_num) hKtop xg_5 yg_5 tg_5 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1293485618551 : ℚ) / 500000000000)) (((226088082927 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_6 : Fin 13 → ℕ := fun k => [1693, 53, 13, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_6 : Fin 13 → ℕ := fun k => [1721, 55, 16, 8, 5, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_6 : Fin 13 → ℚ := fun k => [((164654214056551 : ℚ) / 100000000000), ((44930511330081 : ℚ) / 1000000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_6 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨6, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨7, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (13 + 1) < (cut ⟨7, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 13, (cut ⟨6, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_6 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 13, Work.RHContract.RegionI.Fhi (yg_6 k + 1) (k.val + 1) < (cut ⟨7, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 13, 2 ≤ xg_6 k := by decide +kernel
  have hxhi : ∀ k : Fin 13, xg_6 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 13, yg_6 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 13, 1 ≤ yg_6 k := by decide +kernel
  have hposy : ∀ k : Fin 13, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_6 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_6 ⟨1, by omega⟩ + 1 ≤ xg_6 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 13, (tg_6 k : ℝ) ≤ Chebyshev.theta ((xg_6 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_263
    · exact Work.RHContract.RegionI.thV_15
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((1721 : ℕ) : ℝ) ≤ (((2589315975959 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_267
  have hSx : (((452177595181 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 1693, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_263
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_6 k := by decide +kernel
  have hT2 : (∑ k, tg_6 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_6 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_6 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2589315975959 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_6 k))
      + ((((452177595181 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_6 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_6 (yg_6 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨6, by omega⟩ : ℚ)) (εB := (cut ⟨7, by omega⟩ : ℚ)) hhi hlo
    13 13 (by norm_num) (by norm_num) hKtop xg_6 yg_6 tg_6 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2589315975959 : ℚ) / 1000000000000)) (((452177595181 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_7 : Fin 13 → ℕ := fun k => [1721, 53, 13, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_7 : Fin 13 → ℕ := fun k => [1747, 56, 16, 8, 5, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_7 : Fin 13 → ℚ := fun k => [((52384714919417 : ℚ) / 31250000000), ((44930511330081 : ℚ) / 1000000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_7 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨7, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨8, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (13 + 1) < (cut ⟨8, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 13, (cut ⟨7, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_7 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 13, Work.RHContract.RegionI.Fhi (yg_7 k + 1) (k.val + 1) < (cut ⟨8, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 13, 2 ≤ xg_7 k := by decide +kernel
  have hxhi : ∀ k : Fin 13, xg_7 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 13, yg_7 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 13, 1 ≤ yg_7 k := by decide +kernel
  have hposy : ∀ k : Fin 13, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_7 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_7 ⟨1, by omega⟩ + 1 ≤ xg_7 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 13, (tg_7 k : ℝ) ≤ Chebyshev.theta ((xg_7 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_267
    · exact Work.RHContract.RegionI.thV_15
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((1747 : ℕ) : ℝ) ≤ (((2591620849389 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_271
  have hSx : (((226089484433 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 1721, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_267
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_7 k := by decide +kernel
  have hT2 : (∑ k, tg_7 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_7 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_7 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2591620849389 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_7 k))
      + ((((226089484433 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_7 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_7 (yg_7 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨7, by omega⟩ : ℚ)) (εB := (cut ⟨8, by omega⟩ : ℚ)) hhi hlo
    13 13 (by norm_num) (by norm_num) hKtop xg_7 yg_7 tg_7 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2591620849389 : ℚ) / 1000000000000)) (((226089484433 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_8 : Fin 13 → ℕ := fun k => [1747, 53, 13, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_8 : Fin 13 → ℕ := fun k => [1783, 56, 16, 8, 5, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_8 : Fin 13 → ℚ := fun k => [((170614817918709 : ℚ) / 100000000000), ((44930511330081 : ℚ) / 1000000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_8 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨8, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨9, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (13 + 1) < (cut ⟨9, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 13, (cut ⟨8, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_8 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 13, Work.RHContract.RegionI.Fhi (yg_8 k + 1) (k.val + 1) < (cut ⟨9, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 13, 2 ≤ xg_8 k := by decide +kernel
  have hxhi : ∀ k : Fin 13, xg_8 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 13, yg_8 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 13, 1 ≤ yg_8 k := by decide +kernel
  have hposy : ∀ k : Fin 13, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_8 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_8 ⟨1, by omega⟩ + 1 ≤ xg_8 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 13, (tg_8 k : ℝ) ≤ Chebyshev.theta ((xg_8 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_271
    · exact Work.RHContract.RegionI.thV_15
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((1783 : ℕ) : ℝ) ≤ (((2593884043743 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_275
  have hSx : (((226090148123 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 1747, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_271
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_8 k := by decide +kernel
  have hT2 : (∑ k, tg_8 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_8 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_8 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2593884043743 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_8 k))
      + ((((226090148123 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_8 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_8 (yg_8 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨8, by omega⟩ : ℚ)) (εB := (cut ⟨9, by omega⟩ : ℚ)) hhi hlo
    13 13 (by norm_num) (by norm_num) hKtop xg_8 yg_8 tg_8 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2593884043743 : ℚ) / 1000000000000)) (((226090148123 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_9 : Fin 13 → ℕ := fun k => [1783, 53, 13, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_9 : Fin 13 → ℕ := fun k => [1811, 57, 16, 8, 5, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_9 : Fin 13 → ℚ := fun k => [((1736058498252367 : ℚ) / 1000000000000), ((44930511330081 : ℚ) / 1000000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_9 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨9, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨10, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (13 + 1) < (cut ⟨10, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 13, (cut ⟨9, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_9 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 13, Work.RHContract.RegionI.Fhi (yg_9 k + 1) (k.val + 1) < (cut ⟨10, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 13, 2 ≤ xg_9 k := by decide +kernel
  have hxhi : ∀ k : Fin 13, xg_9 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 13, yg_9 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 13, 1 ≤ yg_9 k := by decide +kernel
  have hposy : ∀ k : Fin 13, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_9 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_9 ⟨1, by omega⟩ + 1 ≤ xg_9 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 13, (tg_9 k : ℝ) ≤ Chebyshev.theta ((xg_9 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_275
    · exact Work.RHContract.RegionI.thV_15
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((1811 : ℕ) : ℝ) ≤ (((1298055330079 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_279
  have hSx : (((226090788047 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 1783, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_275
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_9 k := by decide +kernel
  have hT2 : (∑ k, tg_9 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_9 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_9 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1298055330079 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_9 k))
      + ((((226090788047 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_9 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_9 (yg_9 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨9, by omega⟩ : ℚ)) (εB := (cut ⟨10, by omega⟩ : ℚ)) hhi hlo
    13 13 (by norm_num) (by norm_num) hKtop xg_9 yg_9 tg_9 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1298055330079 : ℚ) / 500000000000)) (((226090788047 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_10 : Fin 13 → ℕ := fun k => [1811, 53, 13, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_10 : Fin 13 → ℕ := fun k => [1861, 58, 16, 8, 5, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_10 : Fin 13 → ℚ := fun k => [((883016967821847 : ℚ) / 500000000000), ((44930511330081 : ℚ) / 1000000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_10 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨10, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨11, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (13 + 1) < (cut ⟨11, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 13, (cut ⟨10, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_10 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 13, Work.RHContract.RegionI.Fhi (yg_10 k + 1) (k.val + 1) < (cut ⟨11, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 13, 2 ≤ xg_10 k := by decide +kernel
  have hxhi : ∀ k : Fin 13, xg_10 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 13, yg_10 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 13, 1 ≤ yg_10 k := by decide +kernel
  have hposy : ∀ k : Fin 13, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_10 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_10 ⟨1, by omega⟩ + 1 ≤ xg_10 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 13, (tg_10 k : ℝ) ≤ Chebyshev.theta ((xg_10 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_279
    · exact Work.RHContract.RegionI.thV_15
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((1861 : ℕ) : ℝ) ≤ (((259828471093 : ℚ) / 100000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_283
  have hSx : (((452182814893 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 1811, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_279
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_10 k := by decide +kernel
  have hT2 : (∑ k, tg_10 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_10 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_10 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((259828471093 : ℚ) / 100000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_10 k))
      + ((((452182814893 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_10 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_10 (yg_10 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨10, by omega⟩ : ℚ)) (εB := (cut ⟨11, by omega⟩ : ℚ)) hhi hlo
    13 13 (by norm_num) (by norm_num) hKtop xg_10 yg_10 tg_10 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((259828471093 : ℚ) / 100000000000)) (((452182814893 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_11 : Fin 13 → ℕ := fun k => [1861, 53, 13, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_11 : Fin 13 → ℕ := fun k => [1877, 58, 16, 8, 5, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_11 : Fin 13 → ℚ := fun k => [((1796104979189489 : ℚ) / 1000000000000), ((44930511330081 : ℚ) / 1000000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_11 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨11, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨12, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (13 + 1) < (cut ⟨12, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 13, (cut ⟨11, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_11 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 13, Work.RHContract.RegionI.Fhi (yg_11 k + 1) (k.val + 1) < (cut ⟨12, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 13, 2 ≤ xg_11 k := by decide +kernel
  have hxhi : ∀ k : Fin 13, xg_11 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 13, yg_11 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 13, 1 ≤ yg_11 k := by decide +kernel
  have hposy : ∀ k : Fin 13, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_11 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_11 ⟨1, by omega⟩ + 1 ≤ xg_11 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 13, (tg_11 k : ℝ) ≤ Chebyshev.theta ((xg_11 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_283
    · exact Work.RHContract.RegionI.thV_15
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((1877 : ℕ) : ℝ) ≤ (((2600422041919 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_287
  have hSx : (((452183995949 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 1861, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_283
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_11 k := by decide +kernel
  have hT2 : (∑ k, tg_11 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_11 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_11 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2600422041919 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_11 k))
      + ((((452183995949 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_11 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_11 (yg_11 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨11, by omega⟩ : ℚ)) (εB := (cut ⟨12, by omega⟩ : ℚ)) hhi hlo
    13 13 (by norm_num) (by norm_num) hKtop xg_11 yg_11 tg_11 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2600422041919 : ℚ) / 1000000000000)) (((452183995949 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_12 : Fin 13 → ℕ := fun k => [1877, 53, 13, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_12 : Fin 13 → ℕ := fun k => [1907, 58, 16, 8, 5, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_12 : Fin 13 → ℚ := fun k => [((57070125699623 : ℚ) / 31250000000), ((44930511330081 : ℚ) / 1000000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_12 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨12, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨13, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (13 + 1) < (cut ⟨13, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 13, (cut ⟨12, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_12 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 13, Work.RHContract.RegionI.Fhi (yg_12 k + 1) (k.val + 1) < (cut ⟨13, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 13, 2 ≤ xg_12 k := by decide +kernel
  have hxhi : ∀ k : Fin 13, xg_12 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 13, yg_12 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 13, 1 ≤ yg_12 k := by decide +kernel
  have hposy : ∀ k : Fin 13, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_12 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_12 ⟨1, by omega⟩ + 1 ≤ xg_12 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 13, (tg_12 k : ℝ) ≤ Chebyshev.theta ((xg_12 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_287
    · exact Work.RHContract.RegionI.thV_15
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((1907 : ℕ) : ℝ) ≤ (((2602534601083 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_291
  have hSx : (((452185137387 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 1877, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_287
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_12 k := by decide +kernel
  have hT2 : (∑ k, tg_12 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_12 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_12 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2602534601083 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_12 k))
      + ((((452185137387 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_12 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_12 (yg_12 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨12, by omega⟩ : ℚ)) (εB := (cut ⟨13, by omega⟩ : ℚ)) hhi hlo
    13 13 (by norm_num) (by norm_num) hKtop xg_12 yg_12 tg_12 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2602534601083 : ℚ) / 1000000000000)) (((452185137387 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_13 : Fin 13 → ℕ := fun k => [1907, 53, 13, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_13 : Fin 13 → ℕ := fun k => [1949, 59, 16, 8, 5, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_13 : Fin 13 → ℚ := fun k => [((92821487109627 : ℚ) / 50000000000), ((44930511330081 : ℚ) / 1000000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_13 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨13, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨14, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (13 + 1) < (cut ⟨14, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 13, (cut ⟨13, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_13 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 13, Work.RHContract.RegionI.Fhi (yg_13 k + 1) (k.val + 1) < (cut ⟨14, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 13, 2 ≤ xg_13 k := by decide +kernel
  have hxhi : ∀ k : Fin 13, xg_13 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 13, yg_13 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 13, 1 ≤ yg_13 k := by decide +kernel
  have hposy : ∀ k : Fin 13, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_13 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_13 ⟨1, by omega⟩ + 1 ≤ xg_13 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 13, (tg_13 k : ℝ) ≤ Chebyshev.theta ((xg_13 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_291
    · exact Work.RHContract.RegionI.thV_15
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((1949 : ℕ) : ℝ) ≤ (((20348485603 : ℚ) / 7812500000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_295
  have hSx : (((226093126279 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 1907, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_291
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_13 k := by decide +kernel
  have hT2 : (∑ k, tg_13 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_13 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_13 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((20348485603 : ℚ) / 7812500000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_13 k))
      + ((((226093126279 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_13 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_13 (yg_13 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨13, by omega⟩ : ℚ)) (εB := (cut ⟨14, by omega⟩ : ℚ)) hhi hlo
    13 13 (by norm_num) (by norm_num) hKtop xg_13 yg_13 tg_13 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((20348485603 : ℚ) / 7812500000)) (((226093126279 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_14 : Fin 13 → ℕ := fun k => [1949, 59, 13, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_14 : Fin 13 → ℕ := fun k => [1987, 60, 17, 8, 5, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_14 : Fin 13 → ℚ := fun k => [((75467754544509 : ℚ) / 40000000000), ((24504024386343 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_14 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨14, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨15, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (13 + 1) < (cut ⟨15, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 13, (cut ⟨14, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_14 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 13, Work.RHContract.RegionI.Fhi (yg_14 k + 1) (k.val + 1) < (cut ⟨15, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 13, 2 ≤ xg_14 k := by decide +kernel
  have hxhi : ∀ k : Fin 13, xg_14 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 13, yg_14 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 13, 1 ≤ yg_14 k := by decide +kernel
  have hposy : ∀ k : Fin 13, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_14 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_14 ⟨1, by omega⟩ + 1 ≤ xg_14 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 13, (tg_14 k : ℝ) ≤ Chebyshev.theta ((xg_14 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_295
    · exact Work.RHContract.RegionI.thV_16
    · exact Work.RHContract.RegionI.thV_5
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((1987 : ℕ) : ℝ) ≤ (((1303317324239 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_299
  have hSx : (((452187324883 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 1949, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_295
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_14 k := by decide +kernel
  have hT2 : (∑ k, tg_14 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_14 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_14 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1303317324239 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_14 k))
      + ((((452187324883 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_14 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_14 (yg_14 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨14, by omega⟩ : ℚ)) (εB := (cut ⟨15, by omega⟩ : ℚ)) hhi hlo
    13 13 (by norm_num) (by norm_num) hKtop xg_14 yg_14 tg_14 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1303317324239 : ℚ) / 500000000000)) (((452187324883 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_15 : Fin 13 → ℕ := fun k => [1987, 59, 17, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_15 : Fin 13 → ℕ := fun k => [2003, 60, 17, 8, 5, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_15 : Fin 13 → ℚ := fun k => [((958520999818563 : ℚ) / 500000000000), ((24504024386343 : ℚ) / 500000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_15 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨15, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨16, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (13 + 1) < (cut ⟨16, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 13, (cut ⟨15, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_15 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 13, Work.RHContract.RegionI.Fhi (yg_15 k + 1) (k.val + 1) < (cut ⟨16, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 13, 2 ≤ xg_15 k := by decide +kernel
  have hxhi : ∀ k : Fin 13, xg_15 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 13, yg_15 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 13, 1 ≤ yg_15 k := by decide +kernel
  have hposy : ∀ k : Fin 13, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_15 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_15 ⟨1, by omega⟩ + 1 ≤ xg_15 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 13, (tg_15 k : ℝ) ≤ Chebyshev.theta ((xg_15 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_299
    · exact Work.RHContract.RegionI.thV_16
    · exact Work.RHContract.RegionI.thV_6
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((2003 : ℕ) : ℝ) ≤ (((104345486327 : ℚ) / 40000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_303
  have hSx : (((452188353101 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 1987, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_299
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_15 k := by decide +kernel
  have hT2 : (∑ k, tg_15 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_15 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_15 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((104345486327 : ℚ) / 40000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_15 k))
      + ((((452188353101 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_15 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_15 (yg_15 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨15, by omega⟩ : ℚ)) (εB := (cut ⟨16, by omega⟩ : ℚ)) hhi hlo
    13 13 (by norm_num) (by norm_num) hKtop xg_15 yg_15 tg_15 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((104345486327 : ℚ) / 40000000000)) (((452188353101 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_16 : Fin 13 → ℕ := fun k => [2003, 59, 17, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_16 : Fin 13 → ℕ := fun k => [2029, 60, 17, 8, 5, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_16 : Fin 13 → ℚ := fun k => [((1947441600950521 : ℚ) / 1000000000000), ((24504024386343 : ℚ) / 500000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_16 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨16, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨17, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (13 + 1) < (cut ⟨17, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 13, (cut ⟨16, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_16 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 13, Work.RHContract.RegionI.Fhi (yg_16 k + 1) (k.val + 1) < (cut ⟨17, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 13, 2 ≤ xg_16 k := by decide +kernel
  have hxhi : ∀ k : Fin 13, xg_16 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 13, yg_16 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 13, 1 ≤ yg_16 k := by decide +kernel
  have hposy : ∀ k : Fin 13, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_16 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_16 ⟨1, by omega⟩ + 1 ≤ xg_16 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 13, (tg_16 k : ℝ) ≤ Chebyshev.theta ((xg_16 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_303
    · exact Work.RHContract.RegionI.thV_16
    · exact Work.RHContract.RegionI.thV_6
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((2029 : ℕ) : ℝ) ≤ (((2610616892417 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_307
  have hSx : (((56523669389 : ℚ) / 125000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 2003, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_303
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_16 k := by decide +kernel
  have hT2 : (∑ k, tg_16 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_16 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_16 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2610616892417 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_16 k))
      + ((((56523669389 : ℚ) / 125000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_16 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_16 (yg_16 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨16, by omega⟩ : ℚ)) (εB := (cut ⟨17, by omega⟩ : ℚ)) hhi hlo
    13 13 (by norm_num) (by norm_num) hKtop xg_16 yg_16 tg_16 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2610616892417 : ℚ) / 1000000000000)) (((56523669389 : ℚ) / 125000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_17 : Fin 13 → ℕ := fun k => [2029, 59, 17, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_17 : Fin 13 → ℕ := fun k => [2069, 61, 17, 8, 5, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_17 : Fin 13 → ℚ := fun k => [((988943482677063 : ℚ) / 500000000000), ((24504024386343 : ℚ) / 500000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_17 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨17, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨18, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (13 + 1) < (cut ⟨18, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 13, (cut ⟨17, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_17 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 13, Work.RHContract.RegionI.Fhi (yg_17 k + 1) (k.val + 1) < (cut ⟨18, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 13, 2 ≤ xg_17 k := by decide +kernel
  have hxhi : ∀ k : Fin 13, xg_17 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 13, yg_17 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 13, 1 ≤ yg_17 k := by decide +kernel
  have hposy : ∀ k : Fin 13, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_17 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_17 ⟨1, by omega⟩ + 1 ≤ xg_17 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 13, (tg_17 k : ℝ) ≤ Chebyshev.theta ((xg_17 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_307
    · exact Work.RHContract.RegionI.thV_16
    · exact Work.RHContract.RegionI.thV_6
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((2069 : ℕ) : ℝ) ≤ (((2612562950551 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_311
  have hSx : (((18087613379 : ℚ) / 40000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 2029, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_307
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_17 k := by decide +kernel
  have hT2 : (∑ k, tg_17 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_17 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_17 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2612562950551 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_17 k))
      + ((((18087613379 : ℚ) / 40000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_17 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_17 (yg_17 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨17, by omega⟩ : ℚ)) (εB := (cut ⟨18, by omega⟩ : ℚ)) hhi hlo
    13 13 (by norm_num) (by norm_num) hKtop xg_17 yg_17 tg_17 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2612562950551 : ℚ) / 1000000000000)) (((18087613379 : ℚ) / 40000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_18 : Fin 13 → ℕ := fun k => [2069, 61, 17, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_18 : Fin 13 → ℕ := fun k => [2089, 61, 17, 8, 5, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_18 : Fin 13 → ℚ := fun k => [((2008400974721357 : ℚ) / 1000000000000), ((53118922635559 : ℚ) / 1000000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_18 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨18, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨19, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (13 + 1) < (cut ⟨19, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 13, (cut ⟨18, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_18 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 13, Work.RHContract.RegionI.Fhi (yg_18 k + 1) (k.val + 1) < (cut ⟨19, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 13, 2 ≤ xg_18 k := by decide +kernel
  have hxhi : ∀ k : Fin 13, xg_18 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 13, yg_18 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 13, 1 ≤ yg_18 k := by decide +kernel
  have hposy : ∀ k : Fin 13, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_18 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_18 ⟨1, by omega⟩ + 1 ≤ xg_18 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 13, (tg_18 k : ℝ) ≤ Chebyshev.theta ((xg_18 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_311
    · exact Work.RHContract.RegionI.thV_17
    · exact Work.RHContract.RegionI.thV_6
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((2089 : ℕ) : ℝ) ≤ (((2614481880409 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_315
  have hSx : (((452191280827 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 2069, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_311
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_18 k := by decide +kernel
  have hT2 : (∑ k, tg_18 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_18 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_18 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2614481880409 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_18 k))
      + ((((452191280827 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_18 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_18 (yg_18 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨18, by omega⟩ : ℚ)) (εB := (cut ⟨19, by omega⟩ : ℚ)) hhi hlo
    13 13 (by norm_num) (by norm_num) hKtop xg_18 yg_18 tg_18 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2614481880409 : ℚ) / 1000000000000)) (((452191280827 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_19 : Fin 13 → ℕ := fun k => [2089, 61, 17, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_19 : Fin 13 → ℕ := fun k => [2129, 62, 17, 9, 5, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_19 : Fin 13 → ℚ := fun k => [((1019485533323103 : ℚ) / 500000000000), ((53118922635559 : ℚ) / 1000000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_19 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨19, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨20, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (13 + 1) < (cut ⟨20, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 13, (cut ⟨19, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_19 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 13, Work.RHContract.RegionI.Fhi (yg_19 k + 1) (k.val + 1) < (cut ⟨20, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 13, 2 ≤ xg_19 k := by decide +kernel
  have hxhi : ∀ k : Fin 13, xg_19 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 13, yg_19 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 13, 1 ≤ yg_19 k := by decide +kernel
  have hposy : ∀ k : Fin 13, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_19 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_19 ⟨1, by omega⟩ + 1 ≤ xg_19 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 13, (tg_19 k : ℝ) ≤ Chebyshev.theta ((xg_19 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_315
    · exact Work.RHContract.RegionI.thV_17
    · exact Work.RHContract.RegionI.thV_6
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((2129 : ℕ) : ℝ) ≤ (((20931003359 : ℚ) / 8000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_319
  have hSx : (((226096100479 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 2089, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_315
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_19 k := by decide +kernel
  have hT2 : (∑ k, tg_19 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_19 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_19 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((20931003359 : ℚ) / 8000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_19 k))
      + ((((226096100479 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_19 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_19 (yg_19 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨19, by omega⟩ : ℚ)) (εB := (cut ⟨20, by omega⟩ : ℚ)) hhi hlo
    13 13 (by norm_num) (by norm_num) hKtop xg_19 yg_19 tg_19 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((20931003359 : ℚ) / 8000000000)) (((226096100479 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_20 : Fin 13 → ℕ := fun k => [2129, 61, 17, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_20 : Fin 13 → ℕ := fun k => [2143, 62, 17, 9, 5, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_20 : Fin 13 → ℚ := fun k => [((413918894336989 : ℚ) / 200000000000), ((53118922635559 : ℚ) / 1000000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_20 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨20, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨21, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (13 + 1) < (cut ⟨21, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 13, (cut ⟨20, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_20 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 13, Work.RHContract.RegionI.Fhi (yg_20 k + 1) (k.val + 1) < (cut ⟨21, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 13, 2 ≤ xg_20 k := by decide +kernel
  have hxhi : ∀ k : Fin 13, xg_20 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 13, yg_20 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 13, 1 ≤ yg_20 k := by decide +kernel
  have hposy : ∀ k : Fin 13, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_20 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_20 ⟨1, by omega⟩ + 1 ≤ xg_20 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 13, (tg_20 k : ℝ) ≤ Chebyshev.theta ((xg_20 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_319
    · exact Work.RHContract.RegionI.thV_17
    · exact Work.RHContract.RegionI.thV_6
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((2143 : ℕ) : ℝ) ≤ (((2618246773551 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_323
  have hSx : (((452193096927 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 2129, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_319
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_20 k := by decide +kernel
  have hT2 : (∑ k, tg_20 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_20 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_20 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2618246773551 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_20 k))
      + ((((452193096927 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_20 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_20 (yg_20 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨20, by omega⟩ : ℚ)) (εB := (cut ⟨21, by omega⟩ : ℚ)) hhi hlo
    13 13 (by norm_num) (by norm_num) hKtop xg_20 yg_20 tg_20 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2618246773551 : ℚ) / 1000000000000)) (((452193096927 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_21 : Fin 13 → ℕ := fun k => [2143, 61, 17, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_21 : Fin 13 → ℕ := fun k => [2203, 63, 17, 9, 6, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_21 : Fin 13 → ℚ := fun k => [((2100264966844987 : ℚ) / 1000000000000), ((53118922635559 : ℚ) / 1000000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_21 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨21, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨22, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (13 + 1) < (cut ⟨22, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 13, (cut ⟨21, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_21 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 13, Work.RHContract.RegionI.Fhi (yg_21 k + 1) (k.val + 1) < (cut ⟨22, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 13, 2 ≤ xg_21 k := by decide +kernel
  have hxhi : ∀ k : Fin 13, xg_21 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 13, yg_21 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 13, 1 ≤ yg_21 k := by decide +kernel
  have hposy : ∀ k : Fin 13, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_21 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_21 ⟨1, by omega⟩ + 1 ≤ xg_21 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 13, (tg_21 k : ℝ) ≤ Chebyshev.theta ((xg_21 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_323
    · exact Work.RHContract.RegionI.thV_17
    · exact Work.RHContract.RegionI.thV_6
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((2203 : ℕ) : ℝ) ≤ (((524017453287 : ℚ) / 200000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_327
  have hSx : (((452193972011 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 2143, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_323
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_21 k := by decide +kernel
  have hT2 : (∑ k, tg_21 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_21 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_21 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((524017453287 : ℚ) / 200000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_21 k))
      + ((((452193972011 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_21 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_21 (yg_21 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨21, by omega⟩ : ℚ)) (εB := (cut ⟨22, by omega⟩ : ℚ)) hhi hlo
    13 13 (by norm_num) (by norm_num) hKtop xg_21 yg_21 tg_21 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((524017453287 : ℚ) / 200000000000)) (((452193972011 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_22 : Fin 13 → ℕ := fun k => [2203, 61, 17, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_22 : Fin 13 → ℕ := fun k => [2239, 63, 17, 9, 6, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_22 : Fin 13 → ℚ := fun k => [((426200421473833 : ℚ) / 200000000000), ((53118922635559 : ℚ) / 1000000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_22 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨22, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨23, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (13 + 1) < (cut ⟨23, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 13, (cut ⟨22, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_22 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 13, Work.RHContract.RegionI.Fhi (yg_22 k + 1) (k.val + 1) < (cut ⟨23, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 13, 2 ≤ xg_22 k := by decide +kernel
  have hxhi : ∀ k : Fin 13, xg_22 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 13, yg_22 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 13, 1 ≤ yg_22 k := by decide +kernel
  have hposy : ∀ k : Fin 13, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_22 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_22 ⟨1, by omega⟩ + 1 ≤ xg_22 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 13, (tg_22 k : ℝ) ≤ Chebyshev.theta ((xg_22 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_327
    · exact Work.RHContract.RegionI.thV_17
    · exact Work.RHContract.RegionI.thV_6
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((2239 : ℕ) : ℝ) ≤ (((131116832713 : ℚ) / 50000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_332
  have hSx : (((452194818539 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 2203, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_327
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_22 k := by decide +kernel
  have hT2 : (∑ k, tg_22 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_22 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_22 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((131116832713 : ℚ) / 50000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_22 k))
      + ((((452194818539 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_22 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_22 (yg_22 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨22, by omega⟩ : ℚ)) (εB := (cut ⟨23, by omega⟩ : ℚ)) hhi hlo
    13 13 (by norm_num) (by norm_num) hKtop xg_22 yg_22 tg_22 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((131116832713 : ℚ) / 50000000000)) (((452194818539 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_23 : Fin 13 → ℕ := fun k => [2239, 61, 17, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_23 : Fin 13 → ℕ := fun k => [2273, 64, 17, 9, 6, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_23 : Fin 13 → ℚ := fun k => [((2169535989503157 : ℚ) / 1000000000000), ((53118922635559 : ℚ) / 1000000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_23 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨23, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨24, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (13 + 1) < (cut ⟨24, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 13, (cut ⟨23, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_23 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 13, Work.RHContract.RegionI.Fhi (yg_23 k + 1) (k.val + 1) < (cut ⟨24, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 13, 2 ≤ xg_23 k := by decide +kernel
  have hxhi : ∀ k : Fin 13, xg_23 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 13, yg_23 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 13, 1 ≤ yg_23 k := by decide +kernel
  have hposy : ∀ k : Fin 13, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_23 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_23 ⟨1, by omega⟩ + 1 ≤ xg_23 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 13, (tg_23 k : ℝ) ≤ Chebyshev.theta ((xg_23 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_332
    · exact Work.RHContract.RegionI.thV_17
    · exact Work.RHContract.RegionI.thV_6
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((2273 : ℕ) : ℝ) ≤ (((2624549003723 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_337
  have hSx : (((28262239379 : ℚ) / 62500000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 2239, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_332
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_23 k := by decide +kernel
  have hT2 : (∑ k, tg_23 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_23 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_23 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2624549003723 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_23 k))
      + ((((28262239379 : ℚ) / 62500000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_23 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_23 (yg_23 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨23, by omega⟩ : ℚ)) (εB := (cut ⟨24, by omega⟩ : ℚ)) hhi hlo
    13 13 (by norm_num) (by norm_num) hKtop xg_23 yg_23 tg_23 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2624549003723 : ℚ) / 1000000000000)) (((28262239379 : ℚ) / 62500000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_24 : Fin 13 → ℕ := fun k => [2273, 61, 17, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_24 : Fin 13 → ℕ := fun k => [2309, 64, 18, 9, 6, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_24 : Fin 13 → ℚ := fun k => [((88326114072937 : ℚ) / 40000000000), ((53118922635559 : ℚ) / 1000000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_24 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨24, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨25, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (13 + 1) < (cut ⟨25, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 13, (cut ⟨24, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_24 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 13, Work.RHContract.RegionI.Fhi (yg_24 k + 1) (k.val + 1) < (cut ⟨25, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 13, 2 ≤ xg_24 k := by decide +kernel
  have hxhi : ∀ k : Fin 13, xg_24 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 13, yg_24 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 13, 1 ≤ yg_24 k := by decide +kernel
  have hposy : ∀ k : Fin 13, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_24 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_24 ⟨1, by omega⟩ + 1 ≤ xg_24 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 13, (tg_24 k : ℝ) ≤ Chebyshev.theta ((xg_24 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_337
    · exact Work.RHContract.RegionI.thV_17
    · exact Work.RHContract.RegionI.thV_6
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((2309 : ℕ) : ℝ) ≤ (((2626729685729 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_342
  have hSx : (((56524601069 : ℚ) / 125000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 2273, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_337
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_24 k := by decide +kernel
  have hT2 : (∑ k, tg_24 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_24 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_24 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2626729685729 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_24 k))
      + ((((56524601069 : ℚ) / 125000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_24 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_24 (yg_24 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨24, by omega⟩ : ℚ)) (εB := (cut ⟨25, by omega⟩ : ℚ)) hhi hlo
    13 13 (by norm_num) (by norm_num) hKtop xg_24 yg_24 tg_24 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2626729685729 : ℚ) / 1000000000000)) (((56524601069 : ℚ) / 125000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_25 : Fin 13 → ℕ := fun k => [2309, 61, 17, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_25 : Fin 13 → ℕ := fun k => [2347, 65, 18, 9, 6, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_25 : Fin 13 → ℚ := fun k => [((1123420881260167 : ℚ) / 500000000000), ((53118922635559 : ℚ) / 1000000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_25 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨25, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨26, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (13 + 1) < (cut ⟨26, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 13, (cut ⟨25, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_25 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 13, Work.RHContract.RegionI.Fhi (yg_25 k + 1) (k.val + 1) < (cut ⟨26, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 13, 2 ≤ xg_25 k := by decide +kernel
  have hxhi : ∀ k : Fin 13, xg_25 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 13, yg_25 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 13, 1 ≤ yg_25 k := by decide +kernel
  have hposy : ∀ k : Fin 13, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_25 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_25 ⟨1, by omega⟩ + 1 ≤ xg_25 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 13, (tg_25 k : ℝ) ≤ Chebyshev.theta ((xg_25 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_342
    · exact Work.RHContract.RegionI.thV_17
    · exact Work.RHContract.RegionI.thV_6
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((2347 : ℕ) : ℝ) ≤ (((2628872267371 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_347
  have hSx : (((452197759227 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 2309, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_342
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_25 k := by decide +kernel
  have hT2 : (∑ k, tg_25 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_25 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_25 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2628872267371 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_25 k))
      + ((((452197759227 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_25 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_25 (yg_25 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨25, by omega⟩ : ℚ)) (εB := (cut ⟨26, by omega⟩ : ℚ)) hhi hlo
    13 13 (by norm_num) (by norm_num) hKtop xg_25 yg_25 tg_25 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2628872267371 : ℚ) / 1000000000000)) (((452197759227 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_26 : Fin 13 → ℕ := fun k => [2347, 61, 17, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_26 : Fin 13 → ℕ := fun k => [2381, 65, 18, 9, 6, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_26 : Fin 13 → ℚ := fun k => [((142851175863641 : ℚ) / 62500000000), ((53118922635559 : ℚ) / 1000000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_26 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨26, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨27, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (13 + 1) < (cut ⟨27, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 13, (cut ⟨26, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_26 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 13, Work.RHContract.RegionI.Fhi (yg_26 k + 1) (k.val + 1) < (cut ⟨27, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 13, 2 ≤ xg_26 k := by decide +kernel
  have hxhi : ∀ k : Fin 13, xg_26 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 13, yg_26 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 13, 1 ≤ yg_26 k := by decide +kernel
  have hposy : ∀ k : Fin 13, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_26 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_26 ⟨1, by omega⟩ + 1 ≤ xg_26 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 13, (tg_26 k : ℝ) ≤ Chebyshev.theta ((xg_26 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_347
    · exact Work.RHContract.RegionI.thV_17
    · exact Work.RHContract.RegionI.thV_6
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((2381 : ℕ) : ℝ) ≤ (((105239391423 : ℚ) / 40000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_352
  have hSx : (((113049669247 : ℚ) / 250000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 2347, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_347
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_26 k := by decide +kernel
  have hT2 : (∑ k, tg_26 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_26 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_26 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((105239391423 : ℚ) / 40000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_26 k))
      + ((((113049669247 : ℚ) / 250000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_26 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_26 (yg_26 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨26, by omega⟩ : ℚ)) (εB := (cut ⟨27, by omega⟩ : ℚ)) hhi hlo
    13 13 (by norm_num) (by norm_num) hKtop xg_26 yg_26 tg_26 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((105239391423 : ℚ) / 40000000000)) (((113049669247 : ℚ) / 250000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_27 : Fin 13 → ℕ := fun k => [2381, 61, 17, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_27 : Fin 13 → ℕ := fun k => [2411, 66, 18, 9, 6, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_27 : Fin 13 → ℚ := fun k => [((464893298431069 : ℚ) / 200000000000), ((53118922635559 : ℚ) / 1000000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_27 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨27, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨28, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (13 + 1) < (cut ⟨28, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 13, (cut ⟨27, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_27 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 13, Work.RHContract.RegionI.Fhi (yg_27 k + 1) (k.val + 1) < (cut ⟨28, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 13, 2 ≤ xg_27 k := by decide +kernel
  have hxhi : ∀ k : Fin 13, xg_27 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 13, yg_27 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 13, 1 ≤ yg_27 k := by decide +kernel
  have hposy : ∀ k : Fin 13, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_27 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_27 ⟨1, by omega⟩ + 1 ≤ xg_27 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 13, (tg_27 k : ℝ) ≤ Chebyshev.theta ((xg_27 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_352
    · exact Work.RHContract.RegionI.thV_17
    · exact Work.RHContract.RegionI.thV_6
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((2411 : ℕ) : ℝ) ≤ (((2633072937361 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_357
  have hSx : (((452199569177 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 2381, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_352
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_27 k := by decide +kernel
  have hT2 : (∑ k, tg_27 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_27 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_27 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2633072937361 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_27 k))
      + ((((452199569177 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_27 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_27 (yg_27 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨27, by omega⟩ : ℚ)) (εB := (cut ⟨28, by omega⟩ : ℚ)) hhi hlo
    13 13 (by norm_num) (by norm_num) hKtop xg_27 yg_27 tg_27 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2633072937361 : ℚ) / 1000000000000)) (((452199569177 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_28 : Fin 13 → ℕ := fun k => [2411, 61, 17, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_28 : Fin 13 → ℕ := fun k => [2447, 66, 18, 9, 6, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_28 : Fin 13 → ℚ := fun k => [((2363372144994399 : ℚ) / 1000000000000), ((53118922635559 : ℚ) / 1000000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_28 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨28, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨29, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (13 + 1) < (cut ⟨29, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 13, (cut ⟨28, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_28 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 13, Work.RHContract.RegionI.Fhi (yg_28 k + 1) (k.val + 1) < (cut ⟨29, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 13, 2 ≤ xg_28 k := by decide +kernel
  have hxhi : ∀ k : Fin 13, xg_28 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 13, yg_28 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 13, 1 ≤ yg_28 k := by decide +kernel
  have hposy : ∀ k : Fin 13, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_28 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_28 ⟨1, by omega⟩ + 1 ≤ xg_28 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 13, (tg_28 k : ℝ) ≤ Chebyshev.theta ((xg_28 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_357
    · exact Work.RHContract.RegionI.thV_17
    · exact Work.RHContract.RegionI.thV_6
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((2447 : ℕ) : ℝ) ≤ (((658782119953 : ℚ) / 250000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_362
  have hSx : (((452200440899 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 2411, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_357
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_28 k := by decide +kernel
  have hT2 : (∑ k, tg_28 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_28 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_28 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((658782119953 : ℚ) / 250000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_28 k))
      + ((((452200440899 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_28 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_28 (yg_28 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨28, by omega⟩ : ℚ)) (εB := (cut ⟨29, by omega⟩ : ℚ)) hhi hlo
    13 13 (by norm_num) (by norm_num) hKtop xg_28 yg_28 tg_28 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((658782119953 : ℚ) / 250000000000)) (((452200440899 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_29 : Fin 13 → ℕ := fun k => [2447, 61, 17, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_29 : Fin 13 → ℕ := fun k => [2477, 67, 18, 9, 6, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_29 : Fin 13 → ℚ := fun k => [((2402356493269081 : ℚ) / 1000000000000), ((53118922635559 : ℚ) / 1000000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_29 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨29, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨30, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (13 + 1) < (cut ⟨30, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 13, (cut ⟨29, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_29 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 13, Work.RHContract.RegionI.Fhi (yg_29 k + 1) (k.val + 1) < (cut ⟨30, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 13, 2 ≤ xg_29 k := by decide +kernel
  have hxhi : ∀ k : Fin 13, xg_29 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 13, yg_29 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 13, 1 ≤ yg_29 k := by decide +kernel
  have hposy : ∀ k : Fin 13, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_29 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_29 ⟨1, by omega⟩ + 1 ≤ xg_29 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 13, (tg_29 k : ℝ) ≤ Chebyshev.theta ((xg_29 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_362
    · exact Work.RHContract.RegionI.thV_17
    · exact Work.RHContract.RegionI.thV_6
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((2477 : ℕ) : ℝ) ≤ (((1318374454669 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_366
  have hSx : (((226100642809 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 2447, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_362
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_29 k := by decide +kernel
  have hT2 : (∑ k, tg_29 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_29 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_29 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1318374454669 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_29 k))
      + ((((226100642809 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_29 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_29 (yg_29 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨29, by omega⟩ : ℚ)) (εB := (cut ⟨30, by omega⟩ : ℚ)) hhi hlo
    13 13 (by norm_num) (by norm_num) hKtop xg_29 yg_29 tg_29 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1318374454669 : ℚ) / 500000000000)) (((226100642809 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_30 : Fin 13 → ℕ := fun k => [2477, 67, 17, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_30 : Fin 13 → ℕ := fun k => [2543, 68, 18, 9, 6, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_30 : Fin 13 → ℚ := fun k => [((2433602752113397 : ℚ) / 1000000000000), ((5732361525339 : ℚ) / 100000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_30 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨30, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨31, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (13 + 1) < (cut ⟨31, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 13, (cut ⟨30, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_30 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 13, Work.RHContract.RegionI.Fhi (yg_30 k + 1) (k.val + 1) < (cut ⟨31, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 13, 2 ≤ xg_30 k := by decide +kernel
  have hxhi : ∀ k : Fin 13, xg_30 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 13, yg_30 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 13, 1 ≤ yg_30 k := by decide +kernel
  have hposy : ∀ k : Fin 13, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_30 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_30 ⟨1, by omega⟩ + 1 ≤ xg_30 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 13, (tg_30 k : ℝ) ≤ Chebyshev.theta ((xg_30 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_366
    · exact Work.RHContract.RegionI.thV_18
    · exact Work.RHContract.RegionI.thV_6
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((2543 : ℕ) : ℝ) ≤ (((1319363841177 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_371
  have hSx : (((452201941803 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 2477, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_366
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_30 k := by decide +kernel
  have hT2 : (∑ k, tg_30 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_30 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_30 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1319363841177 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_30 k))
      + ((((452201941803 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_30 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_30 (yg_30 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨30, by omega⟩ : ℚ)) (εB := (cut ⟨31, by omega⟩ : ℚ)) hhi hlo
    13 13 (by norm_num) (by norm_num) hKtop xg_30 yg_30 tg_30 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1319363841177 : ℚ) / 500000000000)) (((452201941803 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_31 : Fin 13 → ℕ := fun k => [2543, 67, 17, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_31 : Fin 13 → ℕ := fun k => [2591, 68, 18, 9, 6, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_31 : Fin 13 → ℚ := fun k => [((2472777403425389 : ℚ) / 1000000000000), ((5732361525339 : ℚ) / 100000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_31 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨31, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨32, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (13 + 1) < (cut ⟨32, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 13, (cut ⟨31, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_31 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 13, Work.RHContract.RegionI.Fhi (yg_31 k + 1) (k.val + 1) < (cut ⟨32, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 13, 2 ≤ xg_31 k := by decide +kernel
  have hxhi : ∀ k : Fin 13, xg_31 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 13, yg_31 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 13, 1 ≤ yg_31 k := by decide +kernel
  have hposy : ∀ k : Fin 13, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_31 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_31 ⟨1, by omega⟩ + 1 ≤ xg_31 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 13, (tg_31 k : ℝ) ≤ Chebyshev.theta ((xg_31 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_371
    · exact Work.RHContract.RegionI.thV_18
    · exact Work.RHContract.RegionI.thV_6
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((2591 : ℕ) : ℝ) ≤ (((105627086323 : ℚ) / 40000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_376
  have hSx : (((28262670289 : ℚ) / 62500000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 2543, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_371
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_31 k := by decide +kernel
  have hT2 : (∑ k, tg_31 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_31 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_31 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((105627086323 : ℚ) / 40000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_31 k))
      + ((((28262670289 : ℚ) / 62500000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_31 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_31 (yg_31 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨31, by omega⟩ : ℚ)) (εB := (cut ⟨32, by omega⟩ : ℚ)) hhi hlo
    13 13 (by norm_num) (by norm_num) hKtop xg_31 yg_31 tg_31 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((105627086323 : ℚ) / 40000000000)) (((28262670289 : ℚ) / 62500000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_32 : Fin 13 → ℕ := fun k => [2591, 67, 17, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_32 : Fin 13 → ℕ := fun k => [2633, 69, 18, 9, 6, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_32 : Fin 13 → ℚ := fun k => [((2512026646695341 : ℚ) / 1000000000000), ((5732361525339 : ℚ) / 100000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_32 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨32, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨33, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (13 + 1) < (cut ⟨33, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 13, (cut ⟨32, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_32 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 13, Work.RHContract.RegionI.Fhi (yg_32 k + 1) (k.val + 1) < (cut ⟨33, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 13, 2 ≤ xg_32 k := by decide +kernel
  have hxhi : ∀ k : Fin 13, xg_32 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 13, yg_32 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 13, 1 ≤ yg_32 k := by decide +kernel
  have hposy : ∀ k : Fin 13, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_32 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_32 ⟨1, by omega⟩ + 1 ≤ xg_32 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 13, (tg_32 k : ℝ) ≤ Chebyshev.theta ((xg_32 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_376
    · exact Work.RHContract.RegionI.thV_18
    · exact Work.RHContract.RegionI.thV_6
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((2633 : ℕ) : ℝ) ≤ (((10322616843 : ℚ) / 3906250000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_381
  have hSx : (((14131358889 : ℚ) / 31250000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 2591, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_376
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_32 k := by decide +kernel
  have hT2 : (∑ k, tg_32 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_32 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_32 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((10322616843 : ℚ) / 3906250000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_32 k))
      + ((((14131358889 : ℚ) / 31250000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_32 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_32 (yg_32 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨32, by omega⟩ : ℚ)) (εB := (cut ⟨33, by omega⟩ : ℚ)) hhi hlo
    13 13 (by norm_num) (by norm_num) hKtop xg_32 yg_32 tg_32 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((10322616843 : ℚ) / 3906250000)) (((14131358889 : ℚ) / 31250000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_33 : Fin 13 → ℕ := fun k => [2633, 67, 17, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_33 : Fin 13 → ℕ := fun k => [2671, 69, 18, 9, 6, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_33 : Fin 13 → ℚ := fun k => [((2551370914017067 : ℚ) / 1000000000000), ((5732361525339 : ℚ) / 100000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_33 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨33, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨34, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (13 + 1) < (cut ⟨34, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 13, (cut ⟨33, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_33 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 13, Work.RHContract.RegionI.Fhi (yg_33 k + 1) (k.val + 1) < (cut ⟨34, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 13, 2 ≤ xg_33 k := by decide +kernel
  have hxhi : ∀ k : Fin 13, xg_33 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 13, yg_33 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 13, 1 ≤ yg_33 k := by decide +kernel
  have hposy : ∀ k : Fin 13, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_33 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_33 ⟨1, by omega⟩ + 1 ≤ xg_33 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 13, (tg_33 k : ℝ) ≤ Chebyshev.theta ((xg_33 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_381
    · exact Work.RHContract.RegionI.thV_18
    · exact Work.RHContract.RegionI.thV_6
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((2671 : ℕ) : ℝ) ≤ (((264447040507 : ℚ) / 100000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_386
  have hSx : (((452204215911 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 2633, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_381
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_33 k := by decide +kernel
  have hT2 : (∑ k, tg_33 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_33 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_33 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((264447040507 : ℚ) / 100000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_33 k))
      + ((((452204215911 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_33 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_33 (yg_33 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨33, by omega⟩ : ℚ)) (εB := (cut ⟨34, by omega⟩ : ℚ)) hhi hlo
    13 13 (by norm_num) (by norm_num) hKtop xg_33 yg_33 tg_33 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((264447040507 : ℚ) / 100000000000)) (((452204215911 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_34 : Fin 13 → ℕ := fun k => [2671, 67, 17, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_34 : Fin 13 → ℕ := fun k => [2693, 70, 18, 9, 6, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_34 : Fin 13 → ℚ := fun k => [((2590800171340921 : ℚ) / 1000000000000), ((5732361525339 : ℚ) / 100000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_34 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨34, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨35, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (13 + 1) < (cut ⟨35, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 13, (cut ⟨34, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_34 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 13, Work.RHContract.RegionI.Fhi (yg_34 k + 1) (k.val + 1) < (cut ⟨35, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 13, 2 ≤ xg_34 k := by decide +kernel
  have hxhi : ∀ k : Fin 13, xg_34 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 13, yg_34 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 13, 1 ≤ yg_34 k := by decide +kernel
  have hposy : ∀ k : Fin 13, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_34 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_34 ⟨1, by omega⟩ + 1 ≤ xg_34 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 13, (tg_34 k : ℝ) ≤ Chebyshev.theta ((xg_34 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_386
    · exact Work.RHContract.RegionI.thV_18
    · exact Work.RHContract.RegionI.thV_6
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((2693 : ℕ) : ℝ) ≤ (((1323166201067 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_391
  have hSx : (((452204922901 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 2671, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_386
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_34 k := by decide +kernel
  have hT2 : (∑ k, tg_34 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_34 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_34 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1323166201067 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_34 k))
      + ((((452204922901 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_34 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_34 (yg_34 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨34, by omega⟩ : ℚ)) (εB := (cut ⟨35, by omega⟩ : ℚ)) hhi hlo
    13 13 (by norm_num) (by norm_num) hKtop xg_34 yg_34 tg_34 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1323166201067 : ℚ) / 500000000000)) (((452204922901 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_35 : Fin 13 → ℕ := fun k => [2693, 67, 17, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_35 : Fin 13 → ℕ := fun k => [2719, 70, 19, 9, 6, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_35 : Fin 13 → ℚ := fun k => [((328784853822283 : ℚ) / 125000000000), ((5732361525339 : ℚ) / 100000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_35 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨35, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨36, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (13 + 1) < (cut ⟨36, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 13, (cut ⟨35, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_35 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 13, Work.RHContract.RegionI.Fhi (yg_35 k + 1) (k.val + 1) < (cut ⟨36, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 13, 2 ≤ xg_35 k := by decide +kernel
  have hxhi : ∀ k : Fin 13, xg_35 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 13, yg_35 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 13, 1 ≤ yg_35 k := by decide +kernel
  have hposy : ∀ k : Fin 13, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_35 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_35 ⟨1, by omega⟩ + 1 ≤ xg_35 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 13, (tg_35 k : ℝ) ≤ Chebyshev.theta ((xg_35 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_391
    · exact Work.RHContract.RegionI.thV_18
    · exact Work.RHContract.RegionI.thV_6
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((2719 : ℕ) : ℝ) ≤ (((529635581683 : ℚ) / 200000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_396
  have hSx : (((9044112321 : ℚ) / 20000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 2693, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_391
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_35 k := by decide +kernel
  have hT2 : (∑ k, tg_35 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_35 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_35 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((529635581683 : ℚ) / 200000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_35 k))
      + ((((9044112321 : ℚ) / 20000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_35 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_35 (yg_35 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨35, by omega⟩ : ℚ)) (εB := (cut ⟨36, by omega⟩ : ℚ)) hhi hlo
    13 13 (by norm_num) (by norm_num) hKtop xg_35 yg_35 tg_35 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((529635581683 : ℚ) / 200000000000)) (((9044112321 : ℚ) / 20000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_36 : Fin 13 → ℕ := fun k => [2719, 67, 19, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_36 : Fin 13 → ℕ := fun k => [2753, 71, 19, 9, 6, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_36 : Fin 13 → ℚ := fun k => [((2669801966073387 : ℚ) / 1000000000000), ((5732361525339 : ℚ) / 100000000000), ((8043802239499 : ℚ) / 500000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_36 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨36, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨37, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (13 + 1) < (cut ⟨37, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 13, (cut ⟨36, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_36 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 13, Work.RHContract.RegionI.Fhi (yg_36 k + 1) (k.val + 1) < (cut ⟨37, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 13, 2 ≤ xg_36 k := by decide +kernel
  have hxhi : ∀ k : Fin 13, xg_36 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 13, yg_36 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 13, 1 ≤ yg_36 k := by decide +kernel
  have hposy : ∀ k : Fin 13, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_36 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_36 ⟨1, by omega⟩ + 1 ≤ xg_36 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 13, (tg_36 k : ℝ) ≤ Chebyshev.theta ((xg_36 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_396
    · exact Work.RHContract.RegionI.thV_18
    · exact Work.RHContract.RegionI.thV_7
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((2753 : ℕ) : ℝ) ≤ (((265000268129 : ℚ) / 100000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_401
  have hSx : (((226103148489 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 2719, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_396
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_36 k := by decide +kernel
  have hT2 : (∑ k, tg_36 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_36 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_36 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((265000268129 : ℚ) / 100000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_36 k))
      + ((((226103148489 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_36 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_36 (yg_36 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨36, by omega⟩ : ℚ)) (εB := (cut ⟨37, by omega⟩ : ℚ)) hhi hlo
    13 13 (by norm_num) (by norm_num) hKtop xg_36 yg_36 tg_36 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((265000268129 : ℚ) / 100000000000)) (((226103148489 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_37 : Fin 13 → ℕ := fun k => [2753, 71, 19, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_37 : Fin 13 → ℕ := fun k => [2797, 71, 19, 9, 6, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_37 : Fin 13 → ℚ := fun k => [((16933634979943 : ℚ) / 6250000000), ((61586295128871 : ℚ) / 1000000000000), ((8043802239499 : ℚ) / 500000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_37 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨37, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨38, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (13 + 1) < (cut ⟨38, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 13, (cut ⟨37, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_37 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 13, Work.RHContract.RegionI.Fhi (yg_37 k + 1) (k.val + 1) < (cut ⟨38, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 13, 2 ≤ xg_37 k := by decide +kernel
  have hxhi : ∀ k : Fin 13, xg_37 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 13, yg_37 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 13, 1 ≤ yg_37 k := by decide +kernel
  have hposy : ∀ k : Fin 13, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_37 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_37 ⟨1, by omega⟩ + 1 ≤ xg_37 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 13, (tg_37 k : ℝ) ≤ Chebyshev.theta ((xg_37 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_401
    · exact Work.RHContract.RegionI.thV_19
    · exact Work.RHContract.RegionI.thV_7
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((2797 : ℕ) : ℝ) ≤ (((662949719713 : ℚ) / 250000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_406
  have hSx : (((4522069627 : ℚ) / 10000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 2753, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_401
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_37 k := by decide +kernel
  have hT2 : (∑ k, tg_37 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_37 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_37 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((662949719713 : ℚ) / 250000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_37 k))
      + ((((4522069627 : ℚ) / 10000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_37 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_37 (yg_37 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨37, by omega⟩ : ℚ)) (εB := (cut ⟨38, by omega⟩ : ℚ)) hhi hlo
    13 13 (by norm_num) (by norm_num) hKtop xg_37 yg_37 tg_37 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((662949719713 : ℚ) / 250000000000)) (((4522069627 : ℚ) / 10000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_38 : Fin 13 → ℕ := fun k => [2797, 71, 19, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_38 : Fin 13 → ℕ := fun k => [2837, 72, 19, 9, 6, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_38 : Fin 13 → ℚ := fun k => [((68726003463951 : ℚ) / 25000000000), ((61586295128871 : ℚ) / 1000000000000), ((8043802239499 : ℚ) / 500000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_38 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨38, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨39, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (13 + 1) < (cut ⟨39, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 13, (cut ⟨38, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_38 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 13, Work.RHContract.RegionI.Fhi (yg_38 k + 1) (k.val + 1) < (cut ⟨39, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 13, 2 ≤ xg_38 k := by decide +kernel
  have hxhi : ∀ k : Fin 13, xg_38 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 13, yg_38 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 13, 1 ≤ yg_38 k := by decide +kernel
  have hposy : ∀ k : Fin 13, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_38 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_38 ⟨1, by omega⟩ + 1 ≤ xg_38 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 13, (tg_38 k : ℝ) ≤ Chebyshev.theta ((xg_38 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_406
    · exact Work.RHContract.RegionI.thV_19
    · exact Work.RHContract.RegionI.thV_7
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((2837 : ℕ) : ℝ) ≤ (((2653573173047 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_411
  have hSx : (((22610380387 : ℚ) / 50000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 2797, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_406
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_38 k := by decide +kernel
  have hT2 : (∑ k, tg_38 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_38 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_38 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2653573173047 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_38 k))
      + ((((22610380387 : ℚ) / 50000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_38 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_38 (yg_38 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨38, by omega⟩ : ℚ)) (εB := (cut ⟨39, by omega⟩ : ℚ)) hhi hlo
    13 13 (by norm_num) (by norm_num) hKtop xg_38 yg_38 tg_38 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2653573173047 : ℚ) / 1000000000000)) (((22610380387 : ℚ) / 50000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_39 : Fin 13 → ℕ := fun k => [2837, 71, 19, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_39 : Fin 14 → ℕ := fun k => [2879, 72, 19, 9, 6, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_39 : Fin 13 → ℚ := fun k => [((2788760047295919 : ℚ) / 1000000000000), ((61586295128871 : ℚ) / 1000000000000), ((8043802239499 : ℚ) / 500000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_39 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨39, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨40, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (14 + 1) < (cut ⟨40, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 13, (cut ⟨39, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_39 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 14, Work.RHContract.RegionI.Fhi (yg_39 k + 1) (k.val + 1) < (cut ⟨40, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 13, 2 ≤ xg_39 k := by decide +kernel
  have hxhi : ∀ k : Fin 13, xg_39 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 14, yg_39 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 14, 1 ≤ yg_39 k := by decide +kernel
  have hposy : ∀ k : Fin 14, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_39 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_39 ⟨1, by omega⟩ + 1 ≤ xg_39 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 13, (tg_39 k : ℝ) ≤ Chebyshev.theta ((xg_39 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_411
    · exact Work.RHContract.RegionI.thV_19
    · exact Work.RHContract.RegionI.thV_7
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((2879 : ℕ) : ℝ) ≤ (((531064572573 : ℚ) / 200000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_416
  have hSx : (((90441647431 : ℚ) / 200000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 2837, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_411
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_39 k := by decide +kernel
  have hT2 : (∑ k, tg_39 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_39 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_39 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((531064572573 : ℚ) / 200000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_39 k))
      + ((((90441647431 : ℚ) / 200000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_39 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_39 (yg_39 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨39, by omega⟩ : ℚ)) (εB := (cut ⟨40, by omega⟩ : ℚ)) hhi hlo
    13 14 (by norm_num) (by norm_num) hKtop xg_39 yg_39 tg_39 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((531064572573 : ℚ) / 200000000000)) (((90441647431 : ℚ) / 200000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

end

end Work.RHContract.A.RegionI
