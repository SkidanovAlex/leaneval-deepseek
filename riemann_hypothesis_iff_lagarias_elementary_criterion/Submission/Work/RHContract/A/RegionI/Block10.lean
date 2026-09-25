import Mathlib
import Submission.Work.RHContract.A.RegionI.Core
import Submission.Work.RHContract.A.RegionI.blockCert
import Submission.Work.RHContract.A.RegionI.Data11
import Submission.Work.RHContract.A.RegionI.Cuts

/-!  Region I: group certificates.  GENERATED FILE. -/

open scoped BigOperators

namespace Work.RHContract.A.RegionI

noncomputable section

private def xg_360 : Fin 17 → ℕ := fun k => [27407, 223, 41, 17, 7, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_360 : Fin 17 → ℕ := fun k => [27509, 227, 41, 17, 10, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_360 : Fin 17 → ℚ := fun k => [((27184510338433283 : ℚ) / 1000000000000), ((39864507221559 : ℚ) / 200000000000), ((16674435851513 : ℚ) / 500000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_360 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨360, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨361, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨361, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨360, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_360 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_360 k + 1) (k.val + 1) < (cut ⟨361, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_360 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_360 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_360 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_360 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_360 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_360 ⟨1, by omega⟩ + 1 ≤ xg_360 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_360 k : ℝ) ≤ Chebyshev.theta ((xg_360 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2994
    · exact Work.RHContract.RegionI.thV_47
    · exact Work.RHContract.RegionI.thV_12
    · exact Work.RHContract.RegionI.thV_6
    · exact Work.RHContract.RegionI.thV_3
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
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((27509 : ℕ) : ℝ) ≤ (((362782598271 : ℚ) / 125000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_3004
  have hSx : (((56530518569 : ℚ) / 125000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 27407, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2994
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_360 k := by decide +kernel
  have hT2 : (∑ k, tg_360 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_360 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_360 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((362782598271 : ℚ) / 125000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_360 k))
      + ((((56530518569 : ℚ) / 125000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_360 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_360 (yg_360 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨360, by omega⟩ : ℚ)) (εB := (cut ⟨361, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_360 yg_360 tg_360 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((362782598271 : ℚ) / 125000000000)) (((56530518569 : ℚ) / 125000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_361 : Fin 17 → ℕ := fun k => [27509, 227, 41, 17, 7, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_361 : Fin 17 → ℕ := fun k => [27631, 227, 41, 17, 10, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_361 : Fin 17 → ℚ := fun k => [((27286713950975983 : ℚ) / 1000000000000), ((3199179470679 : ℚ) / 15625000000), ((16674435851513 : ℚ) / 500000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_361 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨361, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨362, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨362, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨361, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_361 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_361 k + 1) (k.val + 1) < (cut ⟨362, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_361 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_361 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_361 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_361 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_361 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_361 ⟨1, by omega⟩ + 1 ≤ xg_361 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_361 k : ℝ) ≤ Chebyshev.theta ((xg_361 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_3004
    · exact Work.RHContract.RegionI.thV_48
    · exact Work.RHContract.RegionI.thV_12
    · exact Work.RHContract.RegionI.thV_6
    · exact Work.RHContract.RegionI.thV_3
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
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((27631 : ℕ) : ℝ) ≤ (((362827936667 : ℚ) / 125000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_3014
  have hSx : (((452244161813 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 27509, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_3004
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_361 k := by decide +kernel
  have hT2 : (∑ k, tg_361 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_361 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_361 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((362827936667 : ℚ) / 125000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_361 k))
      + ((((452244161813 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_361 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_361 (yg_361 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨361, by omega⟩ : ℚ)) (εB := (cut ⟨362, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_361 yg_361 tg_361 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((362827936667 : ℚ) / 125000000000)) (((452244161813 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_362 : Fin 17 → ℕ := fun k => [27631, 227, 41, 17, 7, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_362 : Fin 17 → ℕ := fun k => [27739, 228, 42, 17, 10, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_362 : Fin 17 → ℚ := fun k => [((1369447956987687 : ℚ) / 50000000000), ((3199179470679 : ℚ) / 15625000000), ((16674435851513 : ℚ) / 500000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_362 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨362, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨363, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨363, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨362, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_362 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_362 k + 1) (k.val + 1) < (cut ⟨363, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_362 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_362 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_362 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_362 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_362 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_362 ⟨1, by omega⟩ + 1 ≤ xg_362 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_362 k : ℝ) ≤ Chebyshev.theta ((xg_362 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_3014
    · exact Work.RHContract.RegionI.thV_48
    · exact Work.RHContract.RegionI.thV_12
    · exact Work.RHContract.RegionI.thV_6
    · exact Work.RHContract.RegionI.thV_3
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
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((27739 : ℕ) : ℝ) ≤ (((290298456329 : ℚ) / 100000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_3024
  have hSx : (((452244174963 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 27631, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_3014
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_362 k := by decide +kernel
  have hT2 : (∑ k, tg_362 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_362 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_362 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((290298456329 : ℚ) / 100000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_362 k))
      + ((((452244174963 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_362 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_362 (yg_362 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨362, by omega⟩ : ℚ)) (εB := (cut ⟨363, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_362 yg_362 tg_362 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((290298456329 : ℚ) / 100000000000)) (((452244174963 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_363 : Fin 17 → ℕ := fun k => [27739, 227, 41, 17, 7, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_363 : Fin 17 → ℕ := fun k => [27799, 228, 42, 17, 10, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_363 : Fin 17 → ℚ := fun k => [((1718203097882357 : ℚ) / 62500000000), ((3199179470679 : ℚ) / 15625000000), ((16674435851513 : ℚ) / 500000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_363 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨363, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨364, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨364, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨363, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_363 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_363 k + 1) (k.val + 1) < (cut ⟨364, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_363 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_363 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_363 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_363 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_363 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_363 ⟨1, by omega⟩ + 1 ≤ xg_363 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_363 k : ℝ) ≤ Chebyshev.theta ((xg_363 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_3024
    · exact Work.RHContract.RegionI.thV_48
    · exact Work.RHContract.RegionI.thV_12
    · exact Work.RHContract.RegionI.thV_6
    · exact Work.RHContract.RegionI.thV_3
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
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((27799 : ℕ) : ℝ) ≤ (((2903344660397 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_3034
  have hSx : (((90448837599 : ℚ) / 200000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 27739, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_3024
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_363 k := by decide +kernel
  have hT2 : (∑ k, tg_363 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_363 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_363 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2903344660397 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_363 k))
      + ((((90448837599 : ℚ) / 200000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_363 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_363 (yg_363 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨363, by omega⟩ : ℚ)) (εB := (cut ⟨364, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_363 yg_363 tg_363 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2903344660397 : ℚ) / 1000000000000)) (((90448837599 : ℚ) / 200000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_364 : Fin 17 → ℕ := fun k => [27799, 227, 41, 17, 7, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_364 : Fin 17 → ℕ := fun k => [27901, 228, 42, 17, 10, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_364 : Fin 17 → ℚ := fun k => [((27593566967702359 : ℚ) / 1000000000000), ((3199179470679 : ℚ) / 15625000000), ((16674435851513 : ℚ) / 500000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_364 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨364, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨365, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨365, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨364, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_364 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_364 k + 1) (k.val + 1) < (cut ⟨365, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_364 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_364 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_364 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_364 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_364 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_364 ⟨1, by omega⟩ + 1 ≤ xg_364 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_364 k : ℝ) ≤ Chebyshev.theta ((xg_364 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_3034
    · exact Work.RHContract.RegionI.thV_48
    · exact Work.RHContract.RegionI.thV_12
    · exact Work.RHContract.RegionI.thV_6
    · exact Work.RHContract.RegionI.thV_3
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
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((27901 : ℕ) : ℝ) ≤ (((290370379313 : ℚ) / 100000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_3044
  have hSx : (((452244200957 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 27799, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_3034
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_364 k := by decide +kernel
  have hT2 : (∑ k, tg_364 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_364 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_364 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((290370379313 : ℚ) / 100000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_364 k))
      + ((((452244200957 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_364 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_364 (yg_364 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨364, by omega⟩ : ℚ)) (εB := (cut ⟨365, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_364 yg_364 tg_364 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((290370379313 : ℚ) / 100000000000)) (((452244200957 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_365 : Fin 17 → ℕ := fun k => [27901, 227, 41, 17, 7, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_365 : Fin 17 → ℕ := fun k => [27997, 229, 42, 17, 10, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_365 : Fin 17 → ℚ := fun k => [((2769591119081629 : ℚ) / 100000000000), ((3199179470679 : ℚ) / 15625000000), ((16674435851513 : ℚ) / 500000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_365 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨365, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨366, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨366, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨365, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_365 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_365 k + 1) (k.val + 1) < (cut ⟨366, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_365 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_365 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_365 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_365 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_365 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_365 ⟨1, by omega⟩ + 1 ≤ xg_365 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_365 k : ℝ) ≤ Chebyshev.theta ((xg_365 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_3044
    · exact Work.RHContract.RegionI.thV_48
    · exact Work.RHContract.RegionI.thV_12
    · exact Work.RHContract.RegionI.thV_6
    · exact Work.RHContract.RegionI.thV_3
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
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((27997 : ℕ) : ℝ) ≤ (((2904061545717 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_3054
  have hSx : (((9044884277 : ℚ) / 20000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 27901, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_3044
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_365 k := by decide +kernel
  have hT2 : (∑ k, tg_365 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_365 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_365 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2904061545717 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_365 k))
      + ((((9044884277 : ℚ) / 20000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_365 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_365 (yg_365 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨365, by omega⟩ : ℚ)) (εB := (cut ⟨366, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_365 yg_365 tg_365 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2904061545717 : ℚ) / 1000000000000)) (((9044884277 : ℚ) / 20000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_366 : Fin 17 → ℕ := fun k => [27997, 229, 41, 17, 7, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_366 : Fin 17 → ℕ := fun k => [28097, 229, 42, 17, 10, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_366 : Fin 17 → ℚ := fun k => [((27798293913575771 : ℚ) / 1000000000000), ((21018120812519 : ℚ) / 100000000000), ((16674435851513 : ℚ) / 500000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_366 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨366, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨367, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨367, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨366, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_366 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_366 k + 1) (k.val + 1) < (cut ⟨367, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_366 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_366 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_366 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_366 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_366 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_366 ⟨1, by omega⟩ + 1 ≤ xg_366 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_366 k : ℝ) ≤ Chebyshev.theta ((xg_366 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_3054
    · exact Work.RHContract.RegionI.thV_49
    · exact Work.RHContract.RegionI.thV_12
    · exact Work.RHContract.RegionI.thV_6
    · exact Work.RHContract.RegionI.thV_3
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
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((28097 : ℕ) : ℝ) ≤ (((2904418033311 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_3064
  have hSx : (((452244226643 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 27997, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_3054
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_366 k := by decide +kernel
  have hT2 : (∑ k, tg_366 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_366 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_366 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2904418033311 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_366 k))
      + ((((452244226643 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_366 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_366 (yg_366 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨366, by omega⟩ : ℚ)) (εB := (cut ⟨367, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_366 yg_366 tg_366 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2904418033311 : ℚ) / 1000000000000)) (((452244226643 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_367 : Fin 17 → ℕ := fun k => [28097, 229, 41, 17, 7, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_367 : Fin 17 → ℕ := fun k => [28211, 230, 42, 17, 10, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_367 : Fin 17 → ℚ := fun k => [((13950356029907007 : ℚ) / 500000000000), ((21018120812519 : ℚ) / 100000000000), ((16674435851513 : ℚ) / 500000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_367 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨367, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨368, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨368, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨367, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_367 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_367 k + 1) (k.val + 1) < (cut ⟨368, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_367 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_367 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_367 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_367 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_367 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_367 ⟨1, by omega⟩ + 1 ≤ xg_367 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_367 k : ℝ) ≤ Chebyshev.theta ((xg_367 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_3064
    · exact Work.RHContract.RegionI.thV_49
    · exact Work.RHContract.RegionI.thV_12
    · exact Work.RHContract.RegionI.thV_6
    · exact Work.RHContract.RegionI.thV_3
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
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((28211 : ℕ) : ℝ) ≤ (((580954647941 : ℚ) / 200000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_3074
  have hSx : (((226122119673 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 28097, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_3064
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_367 k := by decide +kernel
  have hT2 : (∑ k, tg_367 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_367 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_367 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((580954647941 : ℚ) / 200000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_367 k))
      + ((((226122119673 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_367 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_367 (yg_367 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨367, by omega⟩ : ℚ)) (εB := (cut ⟨368, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_367 yg_367 tg_367 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((580954647941 : ℚ) / 200000000000)) (((226122119673 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_368 : Fin 17 → ℕ := fun k => [28211, 229, 41, 17, 7, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_368 : Fin 17 → ℕ := fun k => [28319, 230, 42, 17, 10, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_368 : Fin 17 → ℚ := fun k => [((437549472083929 : ℚ) / 15625000000), ((21018120812519 : ℚ) / 100000000000), ((16674435851513 : ℚ) / 500000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_368 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨368, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨369, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨369, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨368, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_368 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_368 k + 1) (k.val + 1) < (cut ⟨369, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_368 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_368 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_368 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_368 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_368 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_368 ⟨1, by omega⟩ + 1 ≤ xg_368 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_368 k : ℝ) ≤ Chebyshev.theta ((xg_368 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_3074
    · exact Work.RHContract.RegionI.thV_49
    · exact Work.RHContract.RegionI.thV_12
    · exact Work.RHContract.RegionI.thV_6
    · exact Work.RHContract.RegionI.thV_3
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
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((28319 : ℕ) : ℝ) ≤ (((145256342159 : ℚ) / 50000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_3084
  have hSx : (((452244251957 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 28211, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_3074
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_368 k := by decide +kernel
  have hT2 : (∑ k, tg_368 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_368 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_368 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((145256342159 : ℚ) / 50000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_368 k))
      + ((((452244251957 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_368 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_368 (yg_368 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨368, by omega⟩ : ℚ)) (εB := (cut ⟨369, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_368 yg_368 tg_368 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((145256342159 : ℚ) / 50000000000)) (((452244251957 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_369 : Fin 17 → ℕ := fun k => [28319, 229, 41, 17, 7, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_369 : Fin 17 → ℕ := fun k => [28439, 230, 42, 17, 10, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_369 : Fin 17 → ℚ := fun k => [((3513208198911099 : ℚ) / 125000000000), ((21018120812519 : ℚ) / 100000000000), ((16674435851513 : ℚ) / 500000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_369 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨369, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨370, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨370, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨369, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_369 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_369 k + 1) (k.val + 1) < (cut ⟨370, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_369 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_369 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_369 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_369 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_369 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_369 ⟨1, by omega⟩ + 1 ≤ xg_369 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_369 k : ℝ) ≤ Chebyshev.theta ((xg_369 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_3084
    · exact Work.RHContract.RegionI.thV_49
    · exact Work.RHContract.RegionI.thV_12
    · exact Work.RHContract.RegionI.thV_6
    · exact Work.RHContract.RegionI.thV_3
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
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((28439 : ℕ) : ℝ) ≤ (((290547895749 : ℚ) / 100000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_3094
  have hSx : (((452244264453 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 28319, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_3084
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_369 k := by decide +kernel
  have hT2 : (∑ k, tg_369 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_369 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_369 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((290547895749 : ℚ) / 100000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_369 k))
      + ((((452244264453 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_369 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_369 (yg_369 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨369, by omega⟩ : ℚ)) (εB := (cut ⟨370, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_369 yg_369 tg_369 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((290547895749 : ℚ) / 100000000000)) (((452244264453 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_370 : Fin 17 → ℕ := fun k => [28439, 229, 41, 17, 7, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_370 : Fin 17 → ℕ := fun k => [28547, 231, 42, 17, 10, 7, 5, 4, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_370 : Fin 17 → ℚ := fun k => [((881506474088467 : ℚ) / 31250000000), ((21018120812519 : ℚ) / 100000000000), ((16674435851513 : ℚ) / 500000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_370 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨370, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨371, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨371, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨370, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_370 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_370 k + 1) (k.val + 1) < (cut ⟨371, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_370 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_370 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_370 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_370 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_370 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_370 ⟨1, by omega⟩ + 1 ≤ xg_370 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_370 k : ℝ) ≤ Chebyshev.theta ((xg_370 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_3094
    · exact Work.RHContract.RegionI.thV_49
    · exact Work.RHContract.RegionI.thV_12
    · exact Work.RHContract.RegionI.thV_6
    · exact Work.RHContract.RegionI.thV_3
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
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((28547 : ℕ) : ℝ) ≤ (((2905829799437 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_3104
  have hSx : (((226122138423 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 28439, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_3094
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_370 k := by decide +kernel
  have hT2 : (∑ k, tg_370 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_370 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_370 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2905829799437 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_370 k))
      + ((((226122138423 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_370 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_370 (yg_370 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨370, by omega⟩ : ℚ)) (εB := (cut ⟨371, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_370 yg_370 tg_370 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2905829799437 : ℚ) / 1000000000000)) (((226122138423 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_371 : Fin 17 → ℕ := fun k => [28547, 229, 41, 17, 7, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_371 : Fin 17 → ℕ := fun k => [28619, 231, 42, 17, 10, 7, 5, 4, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_371 : Fin 17 → ℚ := fun k => [((14155392475496153 : ℚ) / 500000000000), ((21018120812519 : ℚ) / 100000000000), ((16674435851513 : ℚ) / 500000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_371 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨371, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨372, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨372, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨371, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_371 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_371 k + 1) (k.val + 1) < (cut ⟨372, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_371 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_371 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_371 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_371 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_371 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_371 ⟨1, by omega⟩ + 1 ≤ xg_371 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_371 k : ℝ) ≤ Chebyshev.theta ((xg_371 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_3104
    · exact Work.RHContract.RegionI.thV_49
    · exact Work.RHContract.RegionI.thV_12
    · exact Work.RHContract.RegionI.thV_6
    · exact Work.RHContract.RegionI.thV_3
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((28619 : ℕ) : ℝ) ≤ (((2906179642031 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_3114
  have hSx : (((9044885783 : ℚ) / 20000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 28547, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_3104
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_371 k := by decide +kernel
  have hT2 : (∑ k, tg_371 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_371 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_371 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2906179642031 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_371 k))
      + ((((9044885783 : ℚ) / 20000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_371 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_371 (yg_371 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨371, by omega⟩ : ℚ)) (εB := (cut ⟨372, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_371 yg_371 tg_371 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2906179642031 : ℚ) / 1000000000000)) (((9044885783 : ℚ) / 20000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_372 : Fin 17 → ℕ := fun k => [28619, 229, 41, 17, 7, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_372 : Fin 17 → ℕ := fun k => [28687, 232, 42, 17, 10, 7, 5, 4, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_372 : Fin 17 → ℚ := fun k => [((3551673906509653 : ℚ) / 125000000000), ((21018120812519 : ℚ) / 100000000000), ((16674435851513 : ℚ) / 500000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_372 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨372, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨373, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨373, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨372, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_372 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_372 k + 1) (k.val + 1) < (cut ⟨373, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_372 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_372 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_372 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_372 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_372 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_372 ⟨1, by omega⟩ + 1 ≤ xg_372 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_372 k : ℝ) ≤ Chebyshev.theta ((xg_372 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_3114
    · exact Work.RHContract.RegionI.thV_49
    · exact Work.RHContract.RegionI.thV_12
    · exact Work.RHContract.RegionI.thV_6
    · exact Work.RHContract.RegionI.thV_3
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((28687 : ℕ) : ℝ) ≤ (((2906528678683 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_3124
  have hSx : (((452244301383 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 28619, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_3114
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_372 k := by decide +kernel
  have hT2 : (∑ k, tg_372 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_372 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_372 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2906528678683 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_372 k))
      + ((((452244301383 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_372 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_372 (yg_372 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨372, by omega⟩ : ℚ)) (εB := (cut ⟨373, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_372 yg_372 tg_372 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2906528678683 : ℚ) / 1000000000000)) (((452244301383 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_373 : Fin 17 → ℕ := fun k => [28687, 229, 41, 17, 7, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_373 : Fin 17 → ℕ := fun k => [28789, 232, 42, 17, 10, 7, 5, 4, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_373 : Fin 17 → ℚ := fun k => [((14258010308074703 : ℚ) / 500000000000), ((21018120812519 : ℚ) / 100000000000), ((16674435851513 : ℚ) / 500000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_373 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨373, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨374, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨374, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨373, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_373 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_373 k + 1) (k.val + 1) < (cut ⟨374, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_373 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_373 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_373 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_373 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_373 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_373 ⟨1, by omega⟩ + 1 ≤ xg_373 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_373 k : ℝ) ≤ Chebyshev.theta ((xg_373 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_3124
    · exact Work.RHContract.RegionI.thV_49
    · exact Work.RHContract.RegionI.thV_12
    · exact Work.RHContract.RegionI.thV_6
    · exact Work.RHContract.RegionI.thV_3
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((28789 : ℕ) : ℝ) ≤ (((72671916229 : ℚ) / 25000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_3134
  have hSx : (((11306107839 : ℚ) / 25000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 28687, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_3124
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_373 k := by decide +kernel
  have hT2 : (∑ k, tg_373 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_373 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_373 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((72671916229 : ℚ) / 25000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_373 k))
      + ((((11306107839 : ℚ) / 25000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_373 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_373 (yg_373 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨373, by omega⟩ : ℚ)) (εB := (cut ⟨374, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_373 yg_373 tg_373 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((72671916229 : ℚ) / 25000000000)) (((11306107839 : ℚ) / 25000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_374 : Fin 17 → ℕ := fun k => [28789, 229, 41, 17, 7, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_374 : Fin 17 → ℕ := fun k => [28879, 232, 42, 17, 10, 7, 5, 4, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_374 : Fin 17 → ℚ := fun k => [((14309340287724439 : ℚ) / 500000000000), ((21018120812519 : ℚ) / 100000000000), ((16674435851513 : ℚ) / 500000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_374 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨374, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨375, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨375, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨374, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_374 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_374 k + 1) (k.val + 1) < (cut ⟨375, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_374 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_374 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_374 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_374 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_374 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_374 ⟨1, by omega⟩ + 1 ≤ xg_374 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_374 k : ℝ) ≤ Chebyshev.theta ((xg_374 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_3134
    · exact Work.RHContract.RegionI.thV_49
    · exact Work.RHContract.RegionI.thV_12
    · exact Work.RHContract.RegionI.thV_6
    · exact Work.RHContract.RegionI.thV_3
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((28879 : ℕ) : ℝ) ≤ (((2907223412987 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_3144
  have hSx : (((14132635177 : ℚ) / 31250000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 28789, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_3134
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_374 k := by decide +kernel
  have hT2 : (∑ k, tg_374 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_374 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_374 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2907223412987 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_374 k))
      + ((((14132635177 : ℚ) / 31250000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_374 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_374 (yg_374 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨374, by omega⟩ : ℚ)) (εB := (cut ⟨375, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_374 yg_374 tg_374 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2907223412987 : ℚ) / 1000000000000)) (((14132635177 : ℚ) / 31250000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_375 : Fin 17 → ℕ := fun k => [28879, 229, 41, 17, 7, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_375 : Fin 17 → ℕ := fun k => [29017, 233, 42, 17, 10, 7, 5, 4, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_375 : Fin 17 → ℚ := fun k => [((14360687635495933 : ℚ) / 500000000000), ((21018120812519 : ℚ) / 100000000000), ((16674435851513 : ℚ) / 500000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_375 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨375, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨376, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨376, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨375, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_375 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_375 k + 1) (k.val + 1) < (cut ⟨376, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_375 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_375 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_375 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_375 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_375 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_375 ⟨1, by omega⟩ + 1 ≤ xg_375 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_375 k : ℝ) ≤ Chebyshev.theta ((xg_375 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_3144
    · exact Work.RHContract.RegionI.thV_49
    · exact Work.RHContract.RegionI.thV_12
    · exact Work.RHContract.RegionI.thV_6
    · exact Work.RHContract.RegionI.thV_3
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((29017 : ℕ) : ℝ) ≤ (((2907568835547 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_3154
  have hSx : (((90448867537 : ℚ) / 200000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 28879, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_3144
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_375 k := by decide +kernel
  have hT2 : (∑ k, tg_375 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_375 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_375 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2907568835547 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_375 k))
      + ((((90448867537 : ℚ) / 200000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_375 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_375 (yg_375 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨375, by omega⟩ : ℚ)) (εB := (cut ⟨376, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_375 yg_375 tg_375 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2907568835547 : ℚ) / 1000000000000)) (((90448867537 : ℚ) / 200000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_376 : Fin 17 → ℕ := fun k => [29017, 233, 41, 17, 7, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_376 : Fin 17 → ℕ := fun k => [29129, 233, 42, 17, 10, 7, 5, 4, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_376 : Fin 17 → ℚ := fun k => [((3603013590536153 : ℚ) / 125000000000), ((26954030822117 : ℚ) / 125000000000), ((16674435851513 : ℚ) / 500000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_376 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨376, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨377, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨377, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨376, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_376 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_376 k + 1) (k.val + 1) < (cut ⟨377, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_376 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_376 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_376 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_376 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_376 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_376 ⟨1, by omega⟩ + 1 ≤ xg_376 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_376 k : ℝ) ≤ Chebyshev.theta ((xg_376 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_3154
    · exact Work.RHContract.RegionI.thV_50
    · exact Work.RHContract.RegionI.thV_12
    · exact Work.RHContract.RegionI.thV_6
    · exact Work.RHContract.RegionI.thV_3
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((29129 : ℕ) : ℝ) ≤ (((2907912891409 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_3164
  have hSx : (((113061087403 : ℚ) / 250000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 29017, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_3154
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_376 k := by decide +kernel
  have hT2 : (∑ k, tg_376 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_376 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_376 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2907912891409 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_376 k))
      + ((((113061087403 : ℚ) / 250000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_376 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_376 (yg_376 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨376, by omega⟩ : ℚ)) (εB := (cut ⟨377, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_376 yg_376 tg_376 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2907912891409 : ℚ) / 1000000000000)) (((113061087403 : ℚ) / 250000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_377 : Fin 17 → ℕ := fun k => [29129, 233, 41, 17, 7, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_377 : Fin 17 → ℕ := fun k => [29207, 234, 42, 17, 10, 7, 5, 4, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_377 : Fin 17 → ℚ := fun k => [((57853763643099 : ℚ) / 2000000000), ((26954030822117 : ℚ) / 125000000000), ((16674435851513 : ℚ) / 500000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_377 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨377, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨378, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨378, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨377, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_377 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_377 k + 1) (k.val + 1) < (cut ⟨378, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_377 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_377 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_377 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_377 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_377 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_377 ⟨1, by omega⟩ + 1 ≤ xg_377 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_377 k : ℝ) ≤ Chebyshev.theta ((xg_377 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_3164
    · exact Work.RHContract.RegionI.thV_50
    · exact Work.RHContract.RegionI.thV_12
    · exact Work.RHContract.RegionI.thV_6
    · exact Work.RHContract.RegionI.thV_3
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((29207 : ℕ) : ℝ) ≤ (((2908255731961 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_3174
  have hSx : (((113061090361 : ℚ) / 250000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 29129, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_3164
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_377 k := by decide +kernel
  have hT2 : (∑ k, tg_377 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_377 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_377 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2908255731961 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_377 k))
      + ((((113061090361 : ℚ) / 250000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_377 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_377 (yg_377 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨377, by omega⟩ : ℚ)) (εB := (cut ⟨378, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_377 yg_377 tg_377 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2908255731961 : ℚ) / 1000000000000)) (((113061090361 : ℚ) / 250000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_378 : Fin 17 → ℕ := fun k => [29207, 233, 41, 17, 7, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_378 : Fin 17 → ℕ := fun k => [29311, 234, 42, 17, 10, 7, 5, 4, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_378 : Fin 17 → ℚ := fun k => [((29029690298495439 : ℚ) / 1000000000000), ((26954030822117 : ℚ) / 125000000000), ((16674435851513 : ℚ) / 500000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_378 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨378, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨379, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨379, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨378, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_378 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_378 k + 1) (k.val + 1) < (cut ⟨379, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_378 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_378 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_378 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_378 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_378 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_378 ⟨1, by omega⟩ + 1 ≤ xg_378 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_378 k : ℝ) ≤ Chebyshev.theta ((xg_378 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_3174
    · exact Work.RHContract.RegionI.thV_50
    · exact Work.RHContract.RegionI.thV_12
    · exact Work.RHContract.RegionI.thV_6
    · exact Work.RHContract.RegionI.thV_3
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((29311 : ℕ) : ℝ) ≤ (((1454298738043 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_3184
  have hSx : (((56530546649 : ℚ) / 125000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 29207, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_3174
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_378 k := by decide +kernel
  have hT2 : (∑ k, tg_378 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_378 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_378 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1454298738043 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_378 k))
      + ((((56530546649 : ℚ) / 125000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_378 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_378 (yg_378 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨378, by omega⟩ : ℚ)) (εB := (cut ⟨379, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_378 yg_378 tg_378 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1454298738043 : ℚ) / 500000000000)) (((56530546649 : ℚ) / 125000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_379 : Fin 17 → ℕ := fun k => [29311, 233, 41, 17, 7, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_379 : Fin 17 → ℕ := fun k => [29401, 234, 42, 17, 10, 7, 5, 4, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_379 : Fin 17 → ℚ := fun k => [((5826506162019869 : ℚ) / 200000000000), ((26954030822117 : ℚ) / 125000000000), ((16674435851513 : ℚ) / 500000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_379 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨379, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨380, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨380, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨379, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_379 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_379 k + 1) (k.val + 1) < (cut ⟨380, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_379 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_379 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_379 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_379 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_379 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_379 ⟨1, by omega⟩ + 1 ≤ xg_379 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_379 k : ℝ) ≤ Chebyshev.theta ((xg_379 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_3184
    · exact Work.RHContract.RegionI.thV_50
    · exact Work.RHContract.RegionI.thV_12
    · exact Work.RHContract.RegionI.thV_6
    · exact Work.RHContract.RegionI.thV_3
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((29401 : ℕ) : ℝ) ≤ (((2908938002763 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_3194
  have hSx : (((226122192433 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 29311, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_3184
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_379 k := by decide +kernel
  have hT2 : (∑ k, tg_379 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_379 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_379 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2908938002763 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_379 k))
      + ((((226122192433 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_379 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_379 (yg_379 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨379, by omega⟩ : ℚ)) (εB := (cut ⟨380, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_379 yg_379 tg_379 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2908938002763 : ℚ) / 1000000000000)) (((226122192433 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_380 : Fin 17 → ℕ := fun k => [29401, 233, 41, 17, 7, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_380 : Fin 17 → ℕ := fun k => [29527, 235, 42, 17, 10, 7, 5, 4, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_380 : Fin 17 → ℚ := fun k => [((730885175161993 : ℚ) / 25000000000), ((26954030822117 : ℚ) / 125000000000), ((16674435851513 : ℚ) / 500000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_380 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨380, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨381, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨381, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨380, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_380 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_380 k + 1) (k.val + 1) < (cut ⟨381, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_380 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_380 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_380 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_380 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_380 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_380 ⟨1, by omega⟩ + 1 ≤ xg_380 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_380 k : ℝ) ≤ Chebyshev.theta ((xg_380 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_3194
    · exact Work.RHContract.RegionI.thV_50
    · exact Work.RHContract.RegionI.thV_12
    · exact Work.RHContract.RegionI.thV_6
    · exact Work.RHContract.RegionI.thV_3
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((29527 : ℕ) : ℝ) ≤ (((2909277475377 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_3204
  have hSx : (((56530549557 : ℚ) / 125000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 29401, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_3194
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_380 k := by decide +kernel
  have hT2 : (∑ k, tg_380 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_380 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_380 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2909277475377 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_380 k))
      + ((((56530549557 : ℚ) / 125000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_380 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_380 (yg_380 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨380, by omega⟩ : ℚ)) (εB := (cut ⟨381, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_380 yg_380 tg_380 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2909277475377 : ℚ) / 1000000000000)) (((56530549557 : ℚ) / 125000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_381 : Fin 17 → ℕ := fun k => [29527, 233, 41, 17, 7, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_381 : Fin 17 → ℕ := fun k => [29629, 235, 42, 17, 10, 7, 5, 4, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_381 : Fin 17 → ℚ := fun k => [((29338314207277277 : ℚ) / 1000000000000), ((26954030822117 : ℚ) / 125000000000), ((16674435851513 : ℚ) / 500000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_381 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨381, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨382, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨382, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨381, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_381 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_381 k + 1) (k.val + 1) < (cut ⟨382, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_381 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_381 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_381 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_381 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_381 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_381 ⟨1, by omega⟩ + 1 ≤ xg_381 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_381 k : ℝ) ≤ Chebyshev.theta ((xg_381 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_3204
    · exact Work.RHContract.RegionI.thV_50
    · exact Work.RHContract.RegionI.thV_12
    · exact Work.RHContract.RegionI.thV_6
    · exact Work.RHContract.RegionI.thV_3
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((29629 : ℕ) : ℝ) ≤ (((581923113193 : ℚ) / 200000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_3214
  have hSx : (((56530550997 : ℚ) / 125000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 29527, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_3204
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_381 k := by decide +kernel
  have hT2 : (∑ k, tg_381 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_381 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_381 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((581923113193 : ℚ) / 200000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_381 k))
      + ((((56530550997 : ℚ) / 125000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_381 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_381 (yg_381 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨381, by omega⟩ : ℚ)) (εB := (cut ⟨382, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_381 yg_381 tg_381 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((581923113193 : ℚ) / 200000000000)) (((56530550997 : ℚ) / 125000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_382 : Fin 17 → ℕ := fun k => [29629, 233, 41, 17, 7, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_382 : Fin 17 → ℕ := fun k => [29753, 236, 43, 17, 10, 7, 5, 4, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_382 : Fin 17 → ℚ := fun k => [((7360315549729623 : ℚ) / 250000000000), ((26954030822117 : ℚ) / 125000000000), ((16674435851513 : ℚ) / 500000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_382 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨382, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨383, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨383, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨382, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_382 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_382 k + 1) (k.val + 1) < (cut ⟨383, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_382 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_382 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_382 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_382 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_382 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_382 ⟨1, by omega⟩ + 1 ≤ xg_382 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_382 k : ℝ) ≤ Chebyshev.theta ((xg_382 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_3214
    · exact Work.RHContract.RegionI.thV_50
    · exact Work.RHContract.RegionI.thV_12
    · exact Work.RHContract.RegionI.thV_6
    · exact Work.RHContract.RegionI.thV_3
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((29753 : ℕ) : ℝ) ≤ (((727488098197 : ℚ) / 250000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_3224
  have hSx : (((452244419401 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 29629, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_3214
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_382 k := by decide +kernel
  have hT2 : (∑ k, tg_382 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_382 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_382 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((727488098197 : ℚ) / 250000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_382 k))
      + ((((452244419401 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_382 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_382 (yg_382 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨382, by omega⟩ : ℚ)) (εB := (cut ⟨383, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_382 yg_382 tg_382 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((727488098197 : ℚ) / 250000000000)) (((452244419401 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_383 : Fin 17 → ℕ := fun k => [29753, 233, 43, 17, 7, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_383 : Fin 17 → ℕ := fun k => [29867, 236, 43, 17, 10, 7, 5, 4, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_383 : Fin 17 → ℚ := fun k => [((7386061910903469 : ℚ) / 250000000000), ((26954030822117 : ℚ) / 125000000000), ((37110071817419 : ℚ) / 1000000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_383 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨383, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨384, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨384, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨383, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_383 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_383 k + 1) (k.val + 1) < (cut ⟨384, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_383 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_383 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_383 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_383 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_383 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_383 ⟨1, by omega⟩ + 1 ≤ xg_383 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_383 k : ℝ) ≤ Chebyshev.theta ((xg_383 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_3224
    · exact Work.RHContract.RegionI.thV_50
    · exact Work.RHContract.RegionI.thV_13
    · exact Work.RHContract.RegionI.thV_6
    · exact Work.RHContract.RegionI.thV_3
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((29867 : ℕ) : ℝ) ≤ (((291028776459 : ℚ) / 100000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_3234
  have hSx : (((22612221537 : ℚ) / 50000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 29753, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_3224
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_383 k := by decide +kernel
  have hT2 : (∑ k, tg_383 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_383 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_383 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((291028776459 : ℚ) / 100000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_383 k))
      + ((((22612221537 : ℚ) / 50000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_383 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_383 (yg_383 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨383, by omega⟩ : ℚ)) (εB := (cut ⟨384, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_383 yg_383 tg_383 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((291028776459 : ℚ) / 100000000000)) (((22612221537 : ℚ) / 50000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_384 : Fin 17 → ℕ := fun k => [29867, 233, 43, 17, 7, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_384 : Fin 17 → ℕ := fun k => [29989, 237, 43, 17, 10, 7, 5, 4, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_384 : Fin 17 → ℚ := fun k => [((14823638189001611 : ℚ) / 500000000000), ((26954030822117 : ℚ) / 125000000000), ((37110071817419 : ℚ) / 1000000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_384 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨384, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨385, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨385, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨384, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_384 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_384 k + 1) (k.val + 1) < (cut ⟨385, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_384 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_384 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_384 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_384 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_384 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_384 ⟨1, by omega⟩ + 1 ≤ xg_384 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_384 k : ℝ) ≤ Chebyshev.theta ((xg_384 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_3234
    · exact Work.RHContract.RegionI.thV_50
    · exact Work.RHContract.RegionI.thV_13
    · exact Work.RHContract.RegionI.thV_6
    · exact Work.RHContract.RegionI.thV_3
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((29989 : ℕ) : ℝ) ≤ (((582124382099 : ℚ) / 200000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_3244
  have hSx : (((452244441983 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 29867, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_3234
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_384 k := by decide +kernel
  have hT2 : (∑ k, tg_384 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_384 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_384 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((582124382099 : ℚ) / 200000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_384 k))
      + ((((452244441983 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_384 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_384 (yg_384 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨384, by omega⟩ : ℚ)) (εB := (cut ⟨385, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_384 yg_384 tg_384 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((582124382099 : ℚ) / 200000000000)) (((452244441983 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_385 : Fin 17 → ℕ := fun k => [29989, 233, 43, 17, 7, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_385 : Fin 17 → ℕ := fun k => [30011, 237, 43, 17, 10, 7, 5, 4, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_385 : Fin 17 → ℚ := fun k => [((14875170866606059 : ℚ) / 500000000000), ((26954030822117 : ℚ) / 125000000000), ((37110071817419 : ℚ) / 1000000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_385 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨385, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨386, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨386, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨385, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_385 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_385 k + 1) (k.val + 1) < (cut ⟨386, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_385 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_385 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_385 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_385 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_385 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_385 ⟨1, by omega⟩ + 1 ≤ xg_385 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_385 k : ℝ) ≤ Chebyshev.theta ((xg_385 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_3244
    · exact Work.RHContract.RegionI.thV_50
    · exact Work.RHContract.RegionI.thV_13
    · exact Work.RHContract.RegionI.thV_6
    · exact Work.RHContract.RegionI.thV_3
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((30011 : ℕ) : ℝ) ≤ (((1455327616083 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_3245
  have hSx : (((452244453143 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 29989, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_3244
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_385 k := by decide +kernel
  have hT2 : (∑ k, tg_385 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_385 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_385 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1455327616083 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_385 k))
      + ((((452244453143 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_385 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_385 (yg_385 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨385, by omega⟩ : ℚ)) (εB := (cut ⟨386, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_385 yg_385 tg_385 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1455327616083 : ℚ) / 500000000000)) (((452244453143 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

end

end Work.RHContract.A.RegionI
