import Mathlib
import Submission.Work.RHContract.A.RegionI.Core
import Submission.Work.RHContract.A.RegionI.blockCert
import Submission.Work.RHContract.A.RegionI.Data11
import Submission.Work.RHContract.A.RegionI.Cuts

/-!  Region I: group certificates.  GENERATED FILE. -/

open scoped BigOperators

namespace Work.RHContract.A.RegionI

noncomputable section

private def xg_40 : Fin 14 → ℕ := fun k => [2879, 71, 19, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_40 : Fin 14 → ℕ := fun k => [2909, 73, 19, 9, 6, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_40 : Fin 14 → ℚ := fun k => [((707137434917019 : ℚ) / 250000000000), ((61586295128871 : ℚ) / 1000000000000), ((8043802239499 : ℚ) / 500000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_40 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨40, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨41, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (14 + 1) < (cut ⟨41, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 14, (cut ⟨40, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_40 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 14, Work.RHContract.RegionI.Fhi (yg_40 k + 1) (k.val + 1) < (cut ⟨41, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 14, 2 ≤ xg_40 k := by decide +kernel
  have hxhi : ∀ k : Fin 14, xg_40 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 14, yg_40 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 14, 1 ≤ yg_40 k := by decide +kernel
  have hposy : ∀ k : Fin 14, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_40 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_40 ⟨1, by omega⟩ + 1 ≤ xg_40 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 14, (tg_40 k : ℝ) ≤ Chebyshev.theta ((xg_40 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_416
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
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((2909 : ℕ) : ℝ) ≤ (((1328351448941 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_420
  have hSx : (((28263053077 : ℚ) / 62500000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 2879, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_416
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_40 k := by decide +kernel
  have hT2 : (∑ k, tg_40 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_40 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_40 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1328351448941 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_40 k))
      + ((((28263053077 : ℚ) / 62500000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_40 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_40 (yg_40 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨40, by omega⟩ : ℚ)) (εB := (cut ⟨41, by omega⟩ : ℚ)) hhi hlo
    14 14 (by norm_num) (by norm_num) hKtop xg_40 yg_40 tg_40 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1328351448941 : ℚ) / 500000000000)) (((28263053077 : ℚ) / 62500000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_41 : Fin 14 → ℕ := fun k => [2909, 73, 19, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_41 : Fin 14 → ℕ := fun k => [2957, 73, 19, 9, 6, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_41 : Fin 14 → ℚ := fun k => [((715109552114147 : ℚ) / 250000000000), ((65876754568459 : ℚ) / 1000000000000), ((8043802239499 : ℚ) / 500000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_41 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨41, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨42, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (14 + 1) < (cut ⟨42, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 14, (cut ⟨41, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_41 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 14, Work.RHContract.RegionI.Fhi (yg_41 k + 1) (k.val + 1) < (cut ⟨42, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 14, 2 ≤ xg_41 k := by decide +kernel
  have hxhi : ∀ k : Fin 14, xg_41 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 14, yg_41 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 14, 1 ≤ yg_41 k := by decide +kernel
  have hposy : ∀ k : Fin 14, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_41 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_41 ⟨1, by omega⟩ + 1 ≤ xg_41 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 14, (tg_41 k : ℝ) ≤ Chebyshev.theta ((xg_41 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_420
    · exact Work.RHContract.RegionI.thV_20
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
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((2957 : ℕ) : ℝ) ≤ (((2658404723229 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_425
  have hSx : (((226104662597 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 2909, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_420
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_41 k := by decide +kernel
  have hT2 : (∑ k, tg_41 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_41 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_41 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2658404723229 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_41 k))
      + ((((226104662597 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_41 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_41 (yg_41 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨41, by omega⟩ : ℚ)) (εB := (cut ⟨42, by omega⟩ : ℚ)) hhi hlo
    14 14 (by norm_num) (by norm_num) hKtop xg_41 yg_41 tg_41 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2658404723229 : ℚ) / 1000000000000)) (((226104662597 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_42 : Fin 14 → ℕ := fun k => [2957, 73, 19, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_42 : Fin 14 → ℕ := fun k => [3001, 74, 19, 9, 6, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_42 : Fin 14 → ℚ := fun k => [((181272911547929 : ℚ) / 62500000000), ((65876754568459 : ℚ) / 1000000000000), ((8043802239499 : ℚ) / 500000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_42 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨42, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨43, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (14 + 1) < (cut ⟨43, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 14, (cut ⟨42, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_42 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 14, Work.RHContract.RegionI.Fhi (yg_42 k + 1) (k.val + 1) < (cut ⟨43, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 14, 2 ≤ xg_42 k := by decide +kernel
  have hxhi : ∀ k : Fin 14, xg_42 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 14, yg_42 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 14, 1 ≤ yg_42 k := by decide +kernel
  have hposy : ∀ k : Fin 14, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_42 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_42 ⟨1, by omega⟩ + 1 ≤ xg_42 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 14, (tg_42 k : ℝ) ≤ Chebyshev.theta ((xg_42 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_425
    · exact Work.RHContract.RegionI.thV_20
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
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((3001 : ℕ) : ℝ) ≤ (((665020641999 : ℚ) / 250000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_430
  have hSx : (((452209904253 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 2957, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_425
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_42 k := by decide +kernel
  have hT2 : (∑ k, tg_42 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_42 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_42 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((665020641999 : ℚ) / 250000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_42 k))
      + ((((452209904253 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_42 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_42 (yg_42 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨42, by omega⟩ : ℚ)) (εB := (cut ⟨43, by omega⟩ : ℚ)) hhi hlo
    14 14 (by norm_num) (by norm_num) hKtop xg_42 yg_42 tg_42 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((665020641999 : ℚ) / 250000000000)) (((452209904253 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_43 : Fin 14 → ℕ := fun k => [3001, 73, 19, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_43 : Fin 14 → ℕ := fun k => [3041, 74, 19, 9, 6, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_43 : Fin 14 → ℚ := fun k => [((1470182955837277 : ℚ) / 500000000000), ((65876754568459 : ℚ) / 1000000000000), ((8043802239499 : ℚ) / 500000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_43 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨43, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨44, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (14 + 1) < (cut ⟨44, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 14, (cut ⟨43, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_43 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 14, Work.RHContract.RegionI.Fhi (yg_43 k + 1) (k.val + 1) < (cut ⟨44, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 14, 2 ≤ xg_43 k := by decide +kernel
  have hxhi : ∀ k : Fin 14, xg_43 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 14, yg_43 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 14, 1 ≤ yg_43 k := by decide +kernel
  have hposy : ∀ k : Fin 14, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_43 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_43 ⟨1, by omega⟩ + 1 ≤ xg_43 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 14, (tg_43 k : ℝ) ≤ Chebyshev.theta ((xg_43 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_430
    · exact Work.RHContract.RegionI.thV_20
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
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((3041 : ℕ) : ℝ) ≤ (((2661735100871 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_435
  have hSx : (((452210467111 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 3001, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_430
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_43 k := by decide +kernel
  have hT2 : (∑ k, tg_43 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_43 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_43 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2661735100871 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_43 k))
      + ((((452210467111 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_43 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_43 (yg_43 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨43, by omega⟩ : ℚ)) (εB := (cut ⟨44, by omega⟩ : ℚ)) hhi hlo
    14 14 (by norm_num) (by norm_num) hKtop xg_43 yg_43 tg_43 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2661735100871 : ℚ) / 1000000000000)) (((452210467111 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_44 : Fin 14 → ℕ := fun k => [3041, 73, 19, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_44 : Fin 14 → ℕ := fun k => [3083, 75, 19, 9, 6, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_44 : Fin 14 → ℚ := fun k => [((1490220596132973 : ℚ) / 500000000000), ((65876754568459 : ℚ) / 1000000000000), ((8043802239499 : ℚ) / 500000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_44 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨44, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨45, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (14 + 1) < (cut ⟨45, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 14, (cut ⟨44, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_44 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 14, Work.RHContract.RegionI.Fhi (yg_44 k + 1) (k.val + 1) < (cut ⟨45, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 14, 2 ≤ xg_44 k := by decide +kernel
  have hxhi : ∀ k : Fin 14, xg_44 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 14, yg_44 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 14, 1 ≤ yg_44 k := by decide +kernel
  have hposy : ∀ k : Fin 14, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_44 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_44 ⟨1, by omega⟩ + 1 ≤ xg_44 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 14, (tg_44 k : ℝ) ≤ Chebyshev.theta ((xg_44 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_435
    · exact Work.RHContract.RegionI.thV_20
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
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((3083 : ℕ) : ℝ) ≤ (((665841306317 : ℚ) / 250000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_440
  have hSx : (((113052753277 : ℚ) / 250000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 3041, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_435
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_44 k := by decide +kernel
  have hT2 : (∑ k, tg_44 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_44 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_44 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((665841306317 : ℚ) / 250000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_44 k))
      + ((((113052753277 : ℚ) / 250000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_44 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_44 (yg_44 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨44, by omega⟩ : ℚ)) (εB := (cut ⟨45, by omega⟩ : ℚ)) hhi hlo
    14 14 (by norm_num) (by norm_num) hKtop xg_44 yg_44 tg_44 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((665841306317 : ℚ) / 250000000000)) (((113052753277 : ℚ) / 250000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_45 : Fin 14 → ℕ := fun k => [3083, 73, 19, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_45 : Fin 14 → ℕ := fun k => [3137, 75, 20, 9, 6, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_45 : Fin 14 → ℚ := fun k => [((604116946375501 : ℚ) / 200000000000), ((65876754568459 : ℚ) / 1000000000000), ((8043802239499 : ℚ) / 500000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_45 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨45, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨46, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (14 + 1) < (cut ⟨46, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 14, (cut ⟨45, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_45 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 14, Work.RHContract.RegionI.Fhi (yg_45 k + 1) (k.val + 1) < (cut ⟨46, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 14, 2 ≤ xg_45 k := by decide +kernel
  have hxhi : ∀ k : Fin 14, xg_45 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 14, yg_45 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 14, 1 ≤ yg_45 k := by decide +kernel
  have hposy : ∀ k : Fin 14, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_45 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_45 ⟨1, by omega⟩ + 1 ≤ xg_45 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 14, (tg_45 k : ℝ) ≤ Chebyshev.theta ((xg_45 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_440
    · exact Work.RHContract.RegionI.thV_20
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
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((3137 : ℕ) : ℝ) ≤ (((1332485330397 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_445
  have hSx : (((226105772201 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 3083, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_440
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_45 k := by decide +kernel
  have hT2 : (∑ k, tg_45 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_45 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_45 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1332485330397 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_45 k))
      + ((((226105772201 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_45 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_45 (yg_45 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨45, by omega⟩ : ℚ)) (εB := (cut ⟨46, by omega⟩ : ℚ)) hhi hlo
    14 14 (by norm_num) (by norm_num) hKtop xg_45 yg_45 tg_45 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1332485330397 : ℚ) / 500000000000)) (((226105772201 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_46 : Fin 14 → ℕ := fun k => [3137, 73, 19, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_46 : Fin 14 → ℕ := fun k => [3187, 76, 20, 10, 6, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_46 : Fin 14 → ℚ := fun k => [((3060804589633253 : ℚ) / 1000000000000), ((65876754568459 : ℚ) / 1000000000000), ((8043802239499 : ℚ) / 500000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_46 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨46, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨47, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (14 + 1) < (cut ⟨47, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 14, (cut ⟨46, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_46 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 14, Work.RHContract.RegionI.Fhi (yg_46 k + 1) (k.val + 1) < (cut ⟨47, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 14, 2 ≤ xg_46 k := by decide +kernel
  have hxhi : ∀ k : Fin 14, xg_46 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 14, yg_46 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 14, 1 ≤ yg_46 k := by decide +kernel
  have hposy : ∀ k : Fin 14, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_46 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_46 ⟨1, by omega⟩ + 1 ≤ xg_46 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 14, (tg_46 k : ℝ) ≤ Chebyshev.theta ((xg_46 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_445
    · exact Work.RHContract.RegionI.thV_20
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
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((3187 : ℕ) : ℝ) ≤ (((2666546519109 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_450
  have hSx : (((113053014933 : ℚ) / 250000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 3137, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_445
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_46 k := by decide +kernel
  have hT2 : (∑ k, tg_46 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_46 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_46 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2666546519109 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_46 k))
      + ((((113053014933 : ℚ) / 250000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_46 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_46 (yg_46 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨46, by omega⟩ : ℚ)) (εB := (cut ⟨47, by omega⟩ : ℚ)) hhi hlo
    14 14 (by norm_num) (by norm_num) hKtop xg_46 yg_46 tg_46 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2666546519109 : ℚ) / 1000000000000)) (((113053014933 : ℚ) / 250000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_47 : Fin 14 → ℕ := fun k => [3187, 73, 19, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_47 : Fin 14 → ℕ := fun k => [3221, 76, 20, 10, 6, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_47 : Fin 14 → ℚ := fun k => [((620223472690931 : ℚ) / 200000000000), ((65876754568459 : ℚ) / 1000000000000), ((8043802239499 : ℚ) / 500000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_47 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨47, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨48, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (14 + 1) < (cut ⟨48, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 14, (cut ⟨47, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_47 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 14, Work.RHContract.RegionI.Fhi (yg_47 k + 1) (k.val + 1) < (cut ⟨48, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 14, 2 ≤ xg_47 k := by decide +kernel
  have hxhi : ∀ k : Fin 14, xg_47 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 14, yg_47 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 14, 1 ≤ yg_47 k := by decide +kernel
  have hposy : ∀ k : Fin 14, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_47 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_47 ⟨1, by omega⟩ + 1 ≤ xg_47 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 14, (tg_47 k : ℝ) ≤ Chebyshev.theta ((xg_47 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_450
    · exact Work.RHContract.RegionI.thV_20
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
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((3221 : ℕ) : ℝ) ≤ (((33351316069 : ℚ) / 12500000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_455
  have hSx : (((113053139061 : ℚ) / 250000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 3187, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_450
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_47 k := by decide +kernel
  have hT2 : (∑ k, tg_47 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_47 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_47 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((33351316069 : ℚ) / 12500000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_47 k))
      + ((((113053139061 : ℚ) / 250000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_47 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_47 (yg_47 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨47, by omega⟩ : ℚ)) (εB := (cut ⟨48, by omega⟩ : ℚ)) hhi hlo
    14 14 (by norm_num) (by norm_num) hKtop xg_47 yg_47 tg_47 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((33351316069 : ℚ) / 12500000000)) (((113053139061 : ℚ) / 250000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_48 : Fin 14 → ℕ := fun k => [3221, 73, 19, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_48 : Fin 14 → ℕ := fun k => [3259, 77, 20, 10, 6, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_48 : Fin 14 → ℚ := fun k => [((1570742331266961 : ℚ) / 500000000000), ((65876754568459 : ℚ) / 1000000000000), ((8043802239499 : ℚ) / 500000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_48 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨48, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨49, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (14 + 1) < (cut ⟨49, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 14, (cut ⟨48, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_48 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 14, Work.RHContract.RegionI.Fhi (yg_48 k + 1) (k.val + 1) < (cut ⟨49, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 14, 2 ≤ xg_48 k := by decide +kernel
  have hxhi : ∀ k : Fin 14, xg_48 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 14, yg_48 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 14, 1 ≤ yg_48 k := by decide +kernel
  have hposy : ∀ k : Fin 14, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_48 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_48 ⟨1, by omega⟩ + 1 ≤ xg_48 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 14, (tg_48 k : ℝ) ≤ Chebyshev.theta ((xg_48 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_455
    · exact Work.RHContract.RegionI.thV_20
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
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((3259 : ℕ) : ℝ) ≤ (((1334822047753 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_460
  have hSx : (((226106521023 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 3221, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_455
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_48 k := by decide +kernel
  have hT2 : (∑ k, tg_48 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_48 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_48 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1334822047753 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_48 k))
      + ((((226106521023 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_48 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_48 (yg_48 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨48, by omega⟩ : ℚ)) (εB := (cut ⟨49, by omega⟩ : ℚ)) hhi hlo
    14 14 (by norm_num) (by norm_num) hKtop xg_48 yg_48 tg_48 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1334822047753 : ℚ) / 500000000000)) (((226106521023 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_49 : Fin 14 → ℕ := fun k => [3259, 73, 19, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_49 : Fin 14 → ℕ := fun k => [3313, 78, 20, 10, 6, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_49 : Fin 14 → ℚ := fun k => [((3181916378621271 : ℚ) / 1000000000000), ((65876754568459 : ℚ) / 1000000000000), ((8043802239499 : ℚ) / 500000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_49 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨49, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨50, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (14 + 1) < (cut ⟨50, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 14, (cut ⟨49, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_49 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 14, Work.RHContract.RegionI.Fhi (yg_49 k + 1) (k.val + 1) < (cut ⟨50, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 14, 2 ≤ xg_49 k := by decide +kernel
  have hxhi : ∀ k : Fin 14, xg_49 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 14, yg_49 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 14, 1 ≤ yg_49 k := by decide +kernel
  have hposy : ∀ k : Fin 14, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_49 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_49 ⟨1, by omega⟩ + 1 ≤ xg_49 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 14, (tg_49 k : ℝ) ≤ Chebyshev.theta ((xg_49 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_460
    · exact Work.RHContract.RegionI.thV_20
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
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((3313 : ℕ) : ℝ) ≤ (((2671160333059 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_465
  have hSx : (((113053378873 : ℚ) / 250000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 3259, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_460
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_49 k := by decide +kernel
  have hT2 : (∑ k, tg_49 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_49 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_49 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2671160333059 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_49 k))
      + ((((113053378873 : ℚ) / 250000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_49 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_49 (yg_49 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨49, by omega⟩ : ℚ)) (εB := (cut ⟨50, by omega⟩ : ℚ)) hhi hlo
    14 14 (by norm_num) (by norm_num) hKtop xg_49 yg_49 tg_49 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2671160333059 : ℚ) / 1000000000000)) (((113053378873 : ℚ) / 250000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_50 : Fin 14 → ℕ := fun k => [3313, 73, 19, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_50 : Fin 14 → ℕ := fun k => [3343, 78, 20, 10, 6, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_50 : Fin 14 → ℚ := fun k => [((3222421991152873 : ℚ) / 1000000000000), ((65876754568459 : ℚ) / 1000000000000), ((8043802239499 : ℚ) / 500000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_50 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨50, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨51, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (14 + 1) < (cut ⟨51, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 14, (cut ⟨50, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_50 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 14, Work.RHContract.RegionI.Fhi (yg_50 k + 1) (k.val + 1) < (cut ⟨51, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 14, 2 ≤ xg_50 k := by decide +kernel
  have hxhi : ∀ k : Fin 14, xg_50 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 14, yg_50 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 14, 1 ≤ yg_50 k := by decide +kernel
  have hposy : ∀ k : Fin 14, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_50 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_50 ⟨1, by omega⟩ + 1 ≤ xg_50 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 14, (tg_50 k : ℝ) ≤ Chebyshev.theta ((xg_50 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_465
    · exact Work.RHContract.RegionI.thV_20
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
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((3343 : ℕ) : ℝ) ≤ (((267266252033 : ℚ) / 100000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_470
  have hSx : (((90442795031 : ℚ) / 200000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 3313, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_465
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_50 k := by decide +kernel
  have hT2 : (∑ k, tg_50 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_50 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_50 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((267266252033 : ℚ) / 100000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_50 k))
      + ((((90442795031 : ℚ) / 200000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_50 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_50 (yg_50 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨50, by omega⟩ : ℚ)) (εB := (cut ⟨51, by omega⟩ : ℚ)) hhi hlo
    14 14 (by norm_num) (by norm_num) hKtop xg_50 yg_50 tg_50 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((267266252033 : ℚ) / 100000000000)) (((90442795031 : ℚ) / 200000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_51 : Fin 14 → ℕ := fun k => [3343, 73, 19, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_51 : Fin 14 → ℕ := fun k => [3373, 78, 20, 10, 6, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_51 : Fin 14 → ℚ := fun k => [((3262974112180837 : ℚ) / 1000000000000), ((65876754568459 : ℚ) / 1000000000000), ((8043802239499 : ℚ) / 500000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_51 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨51, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨52, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (14 + 1) < (cut ⟨52, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 14, (cut ⟨51, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_51 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 14, Work.RHContract.RegionI.Fhi (yg_51 k + 1) (k.val + 1) < (cut ⟨52, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 14, 2 ≤ xg_51 k := by decide +kernel
  have hxhi : ∀ k : Fin 14, xg_51 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 14, yg_51 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 14, 1 ≤ yg_51 k := by decide +kernel
  have hposy : ∀ k : Fin 14, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_51 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_51 ⟨1, by omega⟩ + 1 ≤ xg_51 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 14, (tg_51 k : ℝ) ≤ Chebyshev.theta ((xg_51 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_470
    · exact Work.RHContract.RegionI.thV_20
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
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((3373 : ℕ) : ℝ) ≤ (((1337074937283 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_475
  have hSx : (((226107213167 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 3343, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_470
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_51 k := by decide +kernel
  have hT2 : (∑ k, tg_51 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_51 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_51 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1337074937283 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_51 k))
      + ((((226107213167 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_51 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_51 (yg_51 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨51, by omega⟩ : ℚ)) (εB := (cut ⟨52, by omega⟩ : ℚ)) hhi hlo
    14 14 (by norm_num) (by norm_num) hKtop xg_51 yg_51 tg_51 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1337074937283 : ℚ) / 500000000000)) (((226107213167 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_52 : Fin 14 → ℕ := fun k => [3373, 73, 19, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_52 : Fin 14 → ℕ := fun k => [3433, 79, 20, 10, 6, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_52 : Fin 14 → ℚ := fun k => [((3303575846835381 : ℚ) / 1000000000000), ((65876754568459 : ℚ) / 1000000000000), ((8043802239499 : ℚ) / 500000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_52 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨52, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨53, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (14 + 1) < (cut ⟨53, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 14, (cut ⟨52, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_52 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 14, Work.RHContract.RegionI.Fhi (yg_52 k + 1) (k.val + 1) < (cut ⟨53, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 14, 2 ≤ xg_52 k := by decide +kernel
  have hxhi : ∀ k : Fin 14, xg_52 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 14, yg_52 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 14, 1 ≤ yg_52 k := by decide +kernel
  have hposy : ∀ k : Fin 14, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_52 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_52 ⟨1, by omega⟩ + 1 ≤ xg_52 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 14, (tg_52 k : ℝ) ≤ Chebyshev.theta ((xg_52 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_475
    · exact Work.RHContract.RegionI.thV_20
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
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((3433 : ℕ) : ℝ) ≤ (((2675617861739 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_480
  have hSx : (((452214868647 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 3373, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_475
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_52 k := by decide +kernel
  have hT2 : (∑ k, tg_52 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_52 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_52 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2675617861739 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_52 k))
      + ((((452214868647 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_52 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_52 (yg_52 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨52, by omega⟩ : ℚ)) (εB := (cut ⟨53, by omega⟩ : ℚ)) hhi hlo
    14 14 (by norm_num) (by norm_num) hKtop xg_52 yg_52 tg_52 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2675617861739 : ℚ) / 1000000000000)) (((452214868647 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_53 : Fin 14 → ℕ := fun k => [3433, 79, 19, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_53 : Fin 14 → ℕ := fun k => [3467, 79, 20, 10, 6, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_53 : Fin 14 → ℚ := fun k => [((83606078532371 : ℚ) / 25000000000), ((35123101209683 : ℚ) / 500000000000), ((8043802239499 : ℚ) / 500000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_53 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨53, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨54, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (14 + 1) < (cut ⟨54, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 14, (cut ⟨53, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_53 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 14, Work.RHContract.RegionI.Fhi (yg_53 k + 1) (k.val + 1) < (cut ⟨54, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 14, 2 ≤ xg_53 k := by decide +kernel
  have hxhi : ∀ k : Fin 14, xg_53 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 14, yg_53 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 14, 1 ≤ yg_53 k := by decide +kernel
  have hposy : ∀ k : Fin 14, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_53 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_53 ⟨1, by omega⟩ + 1 ≤ xg_53 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 14, (tg_53 k : ℝ) ≤ Chebyshev.theta ((xg_53 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_480
    · exact Work.RHContract.RegionI.thV_21
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
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((3467 : ℕ) : ℝ) ≤ (((334632926569 : ℚ) / 125000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_485
  have hSx : (((18088611981 : ℚ) / 40000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 3433, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_480
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_53 k := by decide +kernel
  have hT2 : (∑ k, tg_53 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_53 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_53 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((334632926569 : ℚ) / 125000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_53 k))
      + ((((18088611981 : ℚ) / 40000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_53 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_53 (yg_53 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨53, by omega⟩ : ℚ)) (εB := (cut ⟨54, by omega⟩ : ℚ)) hhi hlo
    14 14 (by norm_num) (by norm_num) hKtop xg_53 yg_53 tg_53 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((334632926569 : ℚ) / 125000000000)) (((18088611981 : ℚ) / 40000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_54 : Fin 14 → ℕ := fun k => [3467, 79, 19, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_54 : Fin 14 → ℕ := fun k => [3527, 80, 20, 10, 6, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_54 : Fin 14 → ℚ := fun k => [((1692493692833561 : ℚ) / 500000000000), ((35123101209683 : ℚ) / 500000000000), ((8043802239499 : ℚ) / 500000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_54 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨54, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨55, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (14 + 1) < (cut ⟨55, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 14, (cut ⟨54, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_54 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 14, Work.RHContract.RegionI.Fhi (yg_54 k + 1) (k.val + 1) < (cut ⟨55, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 14, 2 ≤ xg_54 k := by decide +kernel
  have hxhi : ∀ k : Fin 14, xg_54 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 14, yg_54 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 14, 1 ≤ yg_54 k := by decide +kernel
  have hposy : ∀ k : Fin 14, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_54 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_54 ⟨1, by omega⟩ + 1 ≤ xg_54 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 14, (tg_54 k : ℝ) ≤ Chebyshev.theta ((xg_54 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_485
    · exact Work.RHContract.RegionI.thV_21
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
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((3527 : ℕ) : ℝ) ≤ (((1339388425489 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_491
  have hSx : (((452215717327 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 3467, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_485
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_54 k := by decide +kernel
  have hT2 : (∑ k, tg_54 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_54 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_54 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1339388425489 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_54 k))
      + ((((452215717327 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_54 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_54 (yg_54 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨54, by omega⟩ : ℚ)) (εB := (cut ⟨55, by omega⟩ : ℚ)) hhi hlo
    14 14 (by norm_num) (by norm_num) hKtop xg_54 yg_54 tg_54 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1339388425489 : ℚ) / 500000000000)) (((452215717327 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_55 : Fin 14 → ℕ := fun k => [3527, 79, 19, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_55 : Fin 14 → ℕ := fun k => [3557, 80, 20, 10, 6, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_55 : Fin 14 → ℚ := fun k => [((858488601508821 : ℚ) / 250000000000), ((35123101209683 : ℚ) / 500000000000), ((8043802239499 : ℚ) / 500000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_55 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨55, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨56, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (14 + 1) < (cut ⟨56, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 14, (cut ⟨55, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_55 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 14, Work.RHContract.RegionI.Fhi (yg_55 k + 1) (k.val + 1) < (cut ⟨56, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 14, 2 ≤ xg_55 k := by decide +kernel
  have hxhi : ∀ k : Fin 14, xg_55 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 14, yg_55 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 14, 1 ≤ yg_55 k := by decide +kernel
  have hposy : ∀ k : Fin 14, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_55 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_55 ⟨1, by omega⟩ + 1 ≤ xg_55 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 14, (tg_55 k : ℝ) ≤ Chebyshev.theta ((xg_55 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_491
    · exact Work.RHContract.RegionI.thV_21
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
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((3557 : ℕ) : ℝ) ≤ (((2680471538229 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_497
  have hSx : (((452216206511 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 3527, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_491
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_55 k := by decide +kernel
  have hT2 : (∑ k, tg_55 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_55 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_55 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2680471538229 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_55 k))
      + ((((452216206511 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_55 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_55 (yg_55 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨55, by omega⟩ : ℚ)) (εB := (cut ⟨56, by omega⟩ : ℚ)) hhi hlo
    14 14 (by norm_num) (by norm_num) hKtop xg_55 yg_55 tg_55 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2680471538229 : ℚ) / 1000000000000)) (((452216206511 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_56 : Fin 14 → ℕ := fun k => [3557, 79, 19, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_56 : Fin 14 → ℕ := fun k => [3607, 81, 20, 10, 6, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_56 : Fin 14 → ℚ := fun k => [((3482987372648339 : ℚ) / 1000000000000), ((35123101209683 : ℚ) / 500000000000), ((8043802239499 : ℚ) / 500000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_56 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨56, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨57, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (14 + 1) < (cut ⟨57, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 14, (cut ⟨56, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_56 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 14, Work.RHContract.RegionI.Fhi (yg_56 k + 1) (k.val + 1) < (cut ⟨57, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 14, 2 ≤ xg_56 k := by decide +kernel
  have hxhi : ∀ k : Fin 14, xg_56 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 14, yg_56 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 14, 1 ≤ yg_56 k := by decide +kernel
  have hposy : ∀ k : Fin 14, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_56 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_56 ⟨1, by omega⟩ + 1 ≤ xg_56 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 14, (tg_56 k : ℝ) ≤ Chebyshev.theta ((xg_56 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_497
    · exact Work.RHContract.RegionI.thV_21
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
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((3607 : ℕ) : ℝ) ≤ (((2682146688457 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_503
  have hSx : (((452216685037 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 3557, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_497
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_56 k := by decide +kernel
  have hT2 : (∑ k, tg_56 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_56 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_56 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2682146688457 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_56 k))
      + ((((452216685037 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_56 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_56 (yg_56 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨56, by omega⟩ : ℚ)) (εB := (cut ⟨57, by omega⟩ : ℚ)) hhi hlo
    14 14 (by norm_num) (by norm_num) hKtop xg_56 yg_56 tg_56 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2682146688457 : ℚ) / 1000000000000)) (((452216685037 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_57 : Fin 14 → ℕ := fun k => [3607, 79, 19, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_57 : Fin 14 → ℕ := fun k => [3643, 81, 21, 10, 6, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_57 : Fin 14 → ℚ := fun k => [((1766044968009803 : ℚ) / 500000000000), ((35123101209683 : ℚ) / 500000000000), ((8043802239499 : ℚ) / 500000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_57 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨57, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨58, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (14 + 1) < (cut ⟨58, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 14, (cut ⟨57, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_57 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 14, Work.RHContract.RegionI.Fhi (yg_57 k + 1) (k.val + 1) < (cut ⟨58, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 14, 2 ≤ xg_57 k := by decide +kernel
  have hxhi : ∀ k : Fin 14, xg_57 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 14, yg_57 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 14, 1 ≤ yg_57 k := by decide +kernel
  have hposy : ∀ k : Fin 14, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_57 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_57 ⟨1, by omega⟩ + 1 ≤ xg_57 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 14, (tg_57 k : ℝ) ≤ Chebyshev.theta ((xg_57 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_503
    · exact Work.RHContract.RegionI.thV_21
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
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((3643 : ℕ) : ℝ) ≤ (((2683801038529 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_509
  have hSx : (((2261085763 : ℚ) / 5000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 3607, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_503
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_57 k := by decide +kernel
  have hT2 : (∑ k, tg_57 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_57 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_57 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2683801038529 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_57 k))
      + ((((2261085763 : ℚ) / 5000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_57 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_57 (yg_57 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨57, by omega⟩ : ℚ)) (εB := (cut ⟨58, by omega⟩ : ℚ)) hhi hlo
    14 14 (by norm_num) (by norm_num) hKtop xg_57 yg_57 tg_57 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2683801038529 : ℚ) / 1000000000000)) (((2261085763 : ℚ) / 5000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_58 : Fin 14 → ℕ := fun k => [3643, 79, 19, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_58 : Fin 14 → ℕ := fun k => [3697, 82, 21, 10, 6, 4, 4, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_58 : Fin 14 → ℚ := fun k => [((3581267428269851 : ℚ) / 1000000000000), ((35123101209683 : ℚ) / 500000000000), ((8043802239499 : ℚ) / 500000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_58 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨58, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨59, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (14 + 1) < (cut ⟨59, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 14, (cut ⟨58, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_58 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 14, Work.RHContract.RegionI.Fhi (yg_58 k + 1) (k.val + 1) < (cut ⟨59, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 14, 2 ≤ xg_58 k := by decide +kernel
  have hxhi : ∀ k : Fin 14, xg_58 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 14, yg_58 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 14, 1 ≤ yg_58 k := by decide +kernel
  have hposy : ∀ k : Fin 14, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_58 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_58 ⟨1, by omega⟩ + 1 ≤ xg_58 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 14, (tg_58 k : ℝ) ≤ Chebyshev.theta ((xg_58 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_509
    · exact Work.RHContract.RegionI.thV_21
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
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((3697 : ℕ) : ℝ) ≤ (((21483460809 : ℚ) / 8000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_515
  have hSx : (((22610880431 : ℚ) / 50000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 3643, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_509
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_58 k := by decide +kernel
  have hT2 : (∑ k, tg_58 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_58 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_58 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((21483460809 : ℚ) / 8000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_58 k))
      + ((((22610880431 : ℚ) / 50000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_58 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_58 (yg_58 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨58, by omega⟩ : ℚ)) (εB := (cut ⟨59, by omega⟩ : ℚ)) hhi hlo
    14 14 (by norm_num) (by norm_num) hKtop xg_58 yg_58 tg_58 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((21483460809 : ℚ) / 8000000000)) (((22610880431 : ℚ) / 50000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_59 : Fin 14 → ℕ := fun k => [3697, 79, 19, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_59 : Fin 14 → ℕ := fun k => [3739, 82, 21, 10, 6, 4, 4, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_59 : Fin 14 → ℚ := fun k => [((726105627798059 : ℚ) / 200000000000), ((35123101209683 : ℚ) / 500000000000), ((8043802239499 : ℚ) / 500000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_59 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨59, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨60, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (14 + 1) < (cut ⟨60, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 14, (cut ⟨59, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_59 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 14, Work.RHContract.RegionI.Fhi (yg_59 k + 1) (k.val + 1) < (cut ⟨60, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 14, 2 ≤ xg_59 k := by decide +kernel
  have hxhi : ∀ k : Fin 14, xg_59 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 14, yg_59 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 14, 1 ≤ yg_59 k := by decide +kernel
  have hposy : ∀ k : Fin 14, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_59 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_59 ⟨1, by omega⟩ + 1 ≤ xg_59 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 14, (tg_59 k : ℝ) ≤ Chebyshev.theta ((xg_59 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_515
    · exact Work.RHContract.RegionI.thV_21
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
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((3739 : ℕ) : ℝ) ≤ (((537409032711 : ℚ) / 200000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_521
  have hSx : (((452218052167 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 3697, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_515
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_59 k := by decide +kernel
  have hT2 : (∑ k, tg_59 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_59 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_59 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((537409032711 : ℚ) / 200000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_59 k))
      + ((((452218052167 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_59 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_59 (yg_59 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨59, by omega⟩ : ℚ)) (εB := (cut ⟨60, by omega⟩ : ℚ)) hhi hlo
    14 14 (by norm_num) (by norm_num) hKtop xg_59 yg_59 tg_59 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((537409032711 : ℚ) / 200000000000)) (((452218052167 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_60 : Fin 14 → ℕ := fun k => [3739, 79, 19, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_60 : Fin 14 → ℕ := fun k => [3793, 83, 21, 10, 6, 4, 4, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_60 : Fin 14 → ℚ := fun k => [((3679859124830307 : ℚ) / 1000000000000), ((35123101209683 : ℚ) / 500000000000), ((8043802239499 : ℚ) / 500000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_60 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨60, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨61, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (14 + 1) < (cut ⟨61, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 14, (cut ⟨60, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_60 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 14, Work.RHContract.RegionI.Fhi (yg_60 k + 1) (k.val + 1) < (cut ⟨61, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 14, 2 ≤ xg_60 k := by decide +kernel
  have hxhi : ∀ k : Fin 14, xg_60 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 14, yg_60 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 14, 1 ≤ yg_60 k := by decide +kernel
  have hposy : ∀ k : Fin 14, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_60 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_60 ⟨1, by omega⟩ + 1 ≤ xg_60 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 14, (tg_60 k : ℝ) ≤ Chebyshev.theta ((xg_60 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_521
    · exact Work.RHContract.RegionI.thV_21
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
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((3793 : ℕ) : ℝ) ≤ (((2688370275291 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_526
  have hSx : (((226109242723 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 3739, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_521
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_60 k := by decide +kernel
  have hT2 : (∑ k, tg_60 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_60 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_60 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2688370275291 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_60 k))
      + ((((226109242723 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_60 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_60 (yg_60 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨60, by omega⟩ : ℚ)) (εB := (cut ⟨61, by omega⟩ : ℚ)) hhi hlo
    14 14 (by norm_num) (by norm_num) hKtop xg_60 yg_60 tg_60 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2688370275291 : ℚ) / 1000000000000)) (((226109242723 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_61 : Fin 14 → ℕ := fun k => [3793, 83, 19, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_61 : Fin 14 → ℕ := fun k => [3847, 84, 21, 10, 6, 5, 4, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_61 : Fin 14 → ℚ := fun k => [((148841531656819 : ℚ) / 40000000000), ((37332521512801 : ℚ) / 500000000000), ((8043802239499 : ℚ) / 500000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_61 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨61, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨62, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (14 + 1) < (cut ⟨62, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 14, (cut ⟨61, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_61 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 14, Work.RHContract.RegionI.Fhi (yg_61 k + 1) (k.val + 1) < (cut ⟨62, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 14, 2 ≤ xg_61 k := by decide +kernel
  have hxhi : ∀ k : Fin 14, xg_61 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 14, yg_61 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 14, 1 ≤ yg_61 k := by decide +kernel
  have hposy : ∀ k : Fin 14, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_61 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_61 ⟨1, by omega⟩ + 1 ≤ xg_61 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 14, (tg_61 k : ℝ) ≤ Chebyshev.theta ((xg_61 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_526
    · exact Work.RHContract.RegionI.thV_22
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
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((3847 : ℕ) : ℝ) ≤ (((2689940918311 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_532
  have hSx : (((56527354567 : ℚ) / 125000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 3793, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_526
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_61 k := by decide +kernel
  have hT2 : (∑ k, tg_61 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_61 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_61 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2689940918311 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_61 k))
      + ((((56527354567 : ℚ) / 125000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_61 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_61 (yg_61 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨61, by omega⟩ : ℚ)) (εB := (cut ⟨62, by omega⟩ : ℚ)) hhi hlo
    14 14 (by norm_num) (by norm_num) hKtop xg_61 yg_61 tg_61 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2689940918311 : ℚ) / 1000000000000)) (((56527354567 : ℚ) / 125000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_62 : Fin 14 → ℕ := fun k => [3847, 83, 19, 7, 5, 5, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_62 : Fin 14 → ℕ := fun k => [3889, 84, 21, 10, 6, 5, 4, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_62 : Fin 14 → ℚ := fun k => [((235657957101297 : ℚ) / 62500000000), ((37332521512801 : ℚ) / 500000000000), ((8043802239499 : ℚ) / 500000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_62 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨62, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨63, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (14 + 1) < (cut ⟨63, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 14, (cut ⟨62, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_62 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 14, Work.RHContract.RegionI.Fhi (yg_62 k + 1) (k.val + 1) < (cut ⟨63, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 14, 2 ≤ xg_62 k := by decide +kernel
  have hxhi : ∀ k : Fin 14, xg_62 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 14, yg_62 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 14, 1 ≤ yg_62 k := by decide +kernel
  have hposy : ∀ k : Fin 14, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_62 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_62 ⟨1, by omega⟩ + 1 ≤ xg_62 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 14, (tg_62 k : ℝ) ≤ Chebyshev.theta ((xg_62 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_532
    · exact Work.RHContract.RegionI.thV_22
    · exact Work.RHContract.RegionI.thV_7
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((3889 : ℕ) : ℝ) ≤ (((2691491928221 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_538
  have hSx : (((226109623793 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 3847, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_532
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_62 k := by decide +kernel
  have hT2 : (∑ k, tg_62 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_62 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_62 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2691491928221 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_62 k))
      + ((((226109623793 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_62 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_62 (yg_62 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨62, by omega⟩ : ℚ)) (εB := (cut ⟨63, by omega⟩ : ℚ)) hhi hlo
    14 14 (by norm_num) (by norm_num) hKtop xg_62 yg_62 tg_62 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2691491928221 : ℚ) / 1000000000000)) (((226109623793 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_63 : Fin 14 → ℕ := fun k => [3889, 83, 19, 7, 5, 5, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_63 : Fin 14 → ℕ := fun k => [3929, 85, 21, 10, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_63 : Fin 14 → ℚ := fun k => [((764018356169579 : ℚ) / 200000000000), ((37332521512801 : ℚ) / 500000000000), ((8043802239499 : ℚ) / 500000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_63 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨63, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨64, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (14 + 1) < (cut ⟨64, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 14, (cut ⟨63, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_63 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 14, Work.RHContract.RegionI.Fhi (yg_63 k + 1) (k.val + 1) < (cut ⟨64, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 14, 2 ≤ xg_63 k := by decide +kernel
  have hxhi : ∀ k : Fin 14, xg_63 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 14, yg_63 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 14, 1 ≤ yg_63 k := by decide +kernel
  have hposy : ∀ k : Fin 14, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_63 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_63 ⟨1, by omega⟩ + 1 ≤ xg_63 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 14, (tg_63 k : ℝ) ≤ Chebyshev.theta ((xg_63 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_538
    · exact Work.RHContract.RegionI.thV_22
    · exact Work.RHContract.RegionI.thV_7
    · exact Work.RHContract.RegionI.thV_3
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_2
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_1
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((3929 : ℕ) : ℝ) ≤ (((673255913217 : ℚ) / 250000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_544
  have hSx : (((226109824211 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 3889, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_538
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_63 k := by decide +kernel
  have hT2 : (∑ k, tg_63 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_63 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_63 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((673255913217 : ℚ) / 250000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_63 k))
      + ((((226109824211 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_63 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_63 (yg_63 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨63, by omega⟩ : ℚ)) (εB := (cut ⟨64, by omega⟩ : ℚ)) hhi hlo
    14 14 (by norm_num) (by norm_num) hKtop xg_63 yg_63 tg_63 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((673255913217 : ℚ) / 250000000000)) (((226109824211 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_64 : Fin 14 → ℕ := fun k => [3929, 83, 19, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_64 : Fin 14 → ℕ := fun k => [4001, 85, 21, 10, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_64 : Fin 14 → ℚ := fun k => [((3869731279598181 : ℚ) / 1000000000000), ((37332521512801 : ℚ) / 500000000000), ((8043802239499 : ℚ) / 500000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_64 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨64, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨65, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (14 + 1) < (cut ⟨65, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 14, (cut ⟨64, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_64 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 14, Work.RHContract.RegionI.Fhi (yg_64 k + 1) (k.val + 1) < (cut ⟨65, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 14, 2 ≤ xg_64 k := by decide +kernel
  have hxhi : ∀ k : Fin 14, xg_64 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 14, yg_64 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 14, 1 ≤ yg_64 k := by decide +kernel
  have hposy : ∀ k : Fin 14, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_64 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_64 ⟨1, by omega⟩ + 1 ≤ xg_64 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 14, (tg_64 k : ℝ) ≤ Chebyshev.theta ((xg_64 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_544
    · exact Work.RHContract.RegionI.thV_22
    · exact Work.RHContract.RegionI.thV_7
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((4001 : ℕ) : ℝ) ≤ (((336817238711 : ℚ) / 125000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_550
  have hSx : (((9044400787 : ℚ) / 20000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 3929, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_544
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_64 k := by decide +kernel
  have hT2 : (∑ k, tg_64 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_64 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_64 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((336817238711 : ℚ) / 125000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_64 k))
      + ((((9044400787 : ℚ) / 20000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_64 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_64 (yg_64 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨64, by omega⟩ : ℚ)) (εB := (cut ⟨65, by omega⟩ : ℚ)) hhi hlo
    14 14 (by norm_num) (by norm_num) hKtop xg_64 yg_64 tg_64 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((336817238711 : ℚ) / 125000000000)) (((9044400787 : ℚ) / 20000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_65 : Fin 14 → ℕ := fun k => [4001, 83, 19, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_65 : Fin 14 → ℕ := fun k => [4027, 86, 21, 10, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_65 : Fin 14 → ℚ := fun k => [((3919439697797261 : ℚ) / 1000000000000), ((37332521512801 : ℚ) / 500000000000), ((8043802239499 : ℚ) / 500000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_65 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨65, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨66, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (14 + 1) < (cut ⟨66, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 14, (cut ⟨65, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_65 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 14, Work.RHContract.RegionI.Fhi (yg_65 k + 1) (k.val + 1) < (cut ⟨66, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 14, 2 ≤ xg_65 k := by decide +kernel
  have hxhi : ∀ k : Fin 14, xg_65 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 14, yg_65 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 14, 1 ≤ yg_65 k := by decide +kernel
  have hposy : ∀ k : Fin 14, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_65 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_65 ⟨1, by omega⟩ + 1 ≤ xg_65 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 14, (tg_65 k : ℝ) ≤ Chebyshev.theta ((xg_65 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_550
    · exact Work.RHContract.RegionI.thV_22
    · exact Work.RHContract.RegionI.thV_7
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((4027 : ℕ) : ℝ) ≤ (((1348016249073 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_556
  have hSx : (((452220421429 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 4001, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_550
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_65 k := by decide +kernel
  have hT2 : (∑ k, tg_65 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_65 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_65 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1348016249073 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_65 k))
      + ((((452220421429 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_65 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_65 (yg_65 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨65, by omega⟩ : ℚ)) (εB := (cut ⟨66, by omega⟩ : ℚ)) hhi hlo
    14 14 (by norm_num) (by norm_num) hKtop xg_65 yg_65 tg_65 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1348016249073 : ℚ) / 500000000000)) (((452220421429 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_66 : Fin 14 → ℕ := fun k => [4027, 83, 19, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_66 : Fin 14 → ℕ := fun k => [4091, 86, 21, 10, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_66 : Fin 14 → ℚ := fun k => [((793845288176439 : ℚ) / 200000000000), ((37332521512801 : ℚ) / 500000000000), ((8043802239499 : ℚ) / 500000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_66 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨66, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨67, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (14 + 1) < (cut ⟨67, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 14, (cut ⟨66, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_66 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 14, Work.RHContract.RegionI.Fhi (yg_66 k + 1) (k.val + 1) < (cut ⟨67, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 14, 2 ≤ xg_66 k := by decide +kernel
  have hxhi : ∀ k : Fin 14, xg_66 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 14, yg_66 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 14, 1 ≤ yg_66 k := by decide +kernel
  have hposy : ∀ k : Fin 14, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_66 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_66 ⟨1, by omega⟩ + 1 ≤ xg_66 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 14, (tg_66 k : ℝ) ≤ Chebyshev.theta ((xg_66 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_556
    · exact Work.RHContract.RegionI.thV_22
    · exact Work.RHContract.RegionI.thV_7
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((4091 : ℕ) : ℝ) ≤ (((1348754055373 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_562
  have hSx : (((452220793633 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 4027, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_556
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_66 k := by decide +kernel
  have hT2 : (∑ k, tg_66 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_66 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_66 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1348754055373 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_66 k))
      + ((((452220793633 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_66 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_66 (yg_66 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨66, by omega⟩ : ℚ)) (εB := (cut ⟨67, by omega⟩ : ℚ)) hhi hlo
    14 14 (by norm_num) (by norm_num) hKtop xg_66 yg_66 tg_66 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1348754055373 : ℚ) / 500000000000)) (((452220793633 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_67 : Fin 14 → ℕ := fun k => [4091, 83, 19, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_67 : Fin 14 → ℕ := fun k => [4133, 87, 21, 10, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_67 : Fin 14 → ℚ := fun k => [((4019089871152373 : ℚ) / 1000000000000), ((37332521512801 : ℚ) / 500000000000), ((8043802239499 : ℚ) / 500000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_67 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨67, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨68, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (14 + 1) < (cut ⟨68, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 14, (cut ⟨67, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_67 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 14, Work.RHContract.RegionI.Fhi (yg_67 k + 1) (k.val + 1) < (cut ⟨68, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 14, 2 ≤ xg_67 k := by decide +kernel
  have hxhi : ∀ k : Fin 14, xg_67 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 14, yg_67 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 14, 1 ≤ yg_67 k := by decide +kernel
  have hposy : ∀ k : Fin 14, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_67 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_67 ⟨1, by omega⟩ + 1 ≤ xg_67 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 14, (tg_67 k : ℝ) ≤ Chebyshev.theta ((xg_67 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_562
    · exact Work.RHContract.RegionI.thV_22
    · exact Work.RHContract.RegionI.thV_7
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((4133 : ℕ) : ℝ) ≤ (((2698966270401 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_568
  have hSx : (((113055289113 : ℚ) / 250000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 4091, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_562
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_67 k := by decide +kernel
  have hT2 : (∑ k, tg_67 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_67 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_67 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2698966270401 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_67 k))
      + ((((113055289113 : ℚ) / 250000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_67 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_67 (yg_67 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨67, by omega⟩ : ℚ)) (εB := (cut ⟨68, by omega⟩ : ℚ)) hhi hlo
    14 14 (by norm_num) (by norm_num) hKtop xg_67 yg_67 tg_67 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2698966270401 : ℚ) / 1000000000000)) (((113055289113 : ℚ) / 250000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_68 : Fin 14 → ℕ := fun k => [4133, 83, 19, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_68 : Fin 14 → ℕ := fun k => [4201, 87, 22, 10, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_68 : Fin 14 → ℚ := fun k => [((4069024679887959 : ℚ) / 1000000000000), ((37332521512801 : ℚ) / 500000000000), ((8043802239499 : ℚ) / 500000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_68 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨68, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨69, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (14 + 1) < (cut ⟨69, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 14, (cut ⟨68, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_68 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 14, Work.RHContract.RegionI.Fhi (yg_68 k + 1) (k.val + 1) < (cut ⟨69, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 14, 2 ≤ xg_68 k := by decide +kernel
  have hxhi : ∀ k : Fin 14, xg_68 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 14, yg_68 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 14, 1 ≤ yg_68 k := by decide +kernel
  have hposy : ∀ k : Fin 14, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_68 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_68 ⟨1, by omega⟩ + 1 ≤ xg_68 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 14, (tg_68 k : ℝ) ≤ Chebyshev.theta ((xg_68 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_568
    · exact Work.RHContract.RegionI.thV_22
    · exact Work.RHContract.RegionI.thV_7
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((4201 : ℕ) : ℝ) ≤ (((2700407282823 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_574
  have hSx : (((22611075537 : ℚ) / 50000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 4133, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_568
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_68 k := by decide +kernel
  have hT2 : (∑ k, tg_68 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_68 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_68 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2700407282823 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_68 k))
      + ((((22611075537 : ℚ) / 50000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_68 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_68 (yg_68 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨68, by omega⟩ : ℚ)) (εB := (cut ⟨69, by omega⟩ : ℚ)) hhi hlo
    14 14 (by norm_num) (by norm_num) hKtop xg_68 yg_68 tg_68 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2700407282823 : ℚ) / 1000000000000)) (((22611075537 : ℚ) / 50000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_69 : Fin 14 → ℕ := fun k => [4201, 83, 19, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_69 : Fin 14 → ℕ := fun k => [4241, 88, 22, 10, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_69 : Fin 14 → ℚ := fun k => [((2059515240459641 : ℚ) / 500000000000), ((37332521512801 : ℚ) / 500000000000), ((8043802239499 : ℚ) / 500000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_69 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨69, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨70, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (14 + 1) < (cut ⟨70, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 14, (cut ⟨69, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_69 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 14, Work.RHContract.RegionI.Fhi (yg_69 k + 1) (k.val + 1) < (cut ⟨70, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 14, 2 ≤ xg_69 k := by decide +kernel
  have hxhi : ∀ k : Fin 14, xg_69 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 14, yg_69 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 14, 1 ≤ yg_69 k := by decide +kernel
  have hposy : ∀ k : Fin 14, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_69 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_69 ⟨1, by omega⟩ + 1 ≤ xg_69 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 14, (tg_69 k : ℝ) ≤ Chebyshev.theta ((xg_69 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_574
    · exact Work.RHContract.RegionI.thV_22
    · exact Work.RHContract.RegionI.thV_7
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((4241 : ℕ) : ℝ) ≤ (((2701827689333 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_580
  have hSx : (((113055464187 : ℚ) / 250000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 4201, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_574
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_69 k := by decide +kernel
  have hT2 : (∑ k, tg_69 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_69 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_69 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2701827689333 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_69 k))
      + ((((113055464187 : ℚ) / 250000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_69 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_69 (yg_69 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨69, by omega⟩ : ℚ)) (εB := (cut ⟨70, by omega⟩ : ℚ)) hhi hlo
    14 14 (by norm_num) (by norm_num) hKtop xg_69 yg_69 tg_69 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2701827689333 : ℚ) / 1000000000000)) (((113055464187 : ℚ) / 250000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_70 : Fin 14 → ℕ := fun k => [4241, 83, 19, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_70 : Fin 14 → ℕ := fun k => [4273, 88, 22, 10, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_70 : Fin 14 → ℚ := fun k => [((4169122637852263 : ℚ) / 1000000000000), ((37332521512801 : ℚ) / 500000000000), ((8043802239499 : ℚ) / 500000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_70 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨70, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨71, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (14 + 1) < (cut ⟨71, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 14, (cut ⟨70, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_70 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 14, Work.RHContract.RegionI.Fhi (yg_70 k + 1) (k.val + 1) < (cut ⟨71, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 14, 2 ≤ xg_70 k := by decide +kernel
  have hxhi : ∀ k : Fin 14, xg_70 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 14, yg_70 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 14, 1 ≤ yg_70 k := by decide +kernel
  have hposy : ∀ k : Fin 14, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_70 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_70 ⟨1, by omega⟩ + 1 ≤ xg_70 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 14, (tg_70 k : ℝ) ≤ Chebyshev.theta ((xg_70 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_580
    · exact Work.RHContract.RegionI.thV_22
    · exact Work.RHContract.RegionI.thV_7
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((4273 : ℕ) : ℝ) ≤ (((2703236313533 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_586
  have hSx : (((226111096463 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 4241, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_580
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_70 k := by decide +kernel
  have hT2 : (∑ k, tg_70 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_70 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_70 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2703236313533 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_70 k))
      + ((((226111096463 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_70 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_70 (yg_70 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨70, by omega⟩ : ℚ)) (εB := (cut ⟨71, by omega⟩ : ℚ)) hhi hlo
    14 14 (by norm_num) (by norm_num) hKtop xg_70 yg_70 tg_70 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2703236313533 : ℚ) / 1000000000000)) (((226111096463 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_71 : Fin 14 → ℕ := fun k => [4273, 83, 19, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_71 : Fin 14 → ℕ := fun k => [4337, 89, 22, 10, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_71 : Fin 14 → ℚ := fun k => [((1054816191775977 : ℚ) / 250000000000), ((37332521512801 : ℚ) / 500000000000), ((8043802239499 : ℚ) / 500000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_71 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨71, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨72, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (14 + 1) < (cut ⟨72, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 14, (cut ⟨71, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_71 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 14, Work.RHContract.RegionI.Fhi (yg_71 k + 1) (k.val + 1) < (cut ⟨72, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 14, 2 ≤ xg_71 k := by decide +kernel
  have hxhi : ∀ k : Fin 14, xg_71 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 14, yg_71 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 14, 1 ≤ yg_71 k := by decide +kernel
  have hposy : ∀ k : Fin 14, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_71 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_71 ⟨1, by omega⟩ + 1 ≤ xg_71 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 14, (tg_71 k : ℝ) ≤ Chebyshev.theta ((xg_71 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_586
    · exact Work.RHContract.RegionI.thV_22
    · exact Work.RHContract.RegionI.thV_7
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((4337 : ℕ) : ℝ) ≤ (((2704397485781 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_591
  have hSx : (((452222523551 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 4273, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_586
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_71 k := by decide +kernel
  have hT2 : (∑ k, tg_71 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_71 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_71 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2704397485781 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_71 k))
      + ((((452222523551 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_71 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_71 (yg_71 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨71, by omega⟩ : ℚ)) (εB := (cut ⟨72, by omega⟩ : ℚ)) hhi hlo
    14 14 (by norm_num) (by norm_num) hKtop xg_71 yg_71 tg_71 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2704397485781 : ℚ) / 1000000000000)) (((452222523551 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_72 : Fin 14 → ℕ := fun k => [4337, 89, 19, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_72 : Fin 14 → ℕ := fun k => [4391, 89, 22, 10, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_72 : Fin 14 → ℚ := fun k => [((4261104225218277 : ℚ) / 1000000000000), ((39576839696887 : ℚ) / 500000000000), ((8043802239499 : ℚ) / 500000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_72 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨72, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨73, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (14 + 1) < (cut ⟨73, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 14, (cut ⟨72, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_72 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 14, Work.RHContract.RegionI.Fhi (yg_72 k + 1) (k.val + 1) < (cut ⟨73, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 14, 2 ≤ xg_72 k := by decide +kernel
  have hxhi : ∀ k : Fin 14, xg_72 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 14, yg_72 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 14, 1 ≤ yg_72 k := by decide +kernel
  have hposy : ∀ k : Fin 14, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_72 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_72 ⟨1, by omega⟩ + 1 ≤ xg_72 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 14, (tg_72 k : ℝ) ≤ Chebyshev.theta ((xg_72 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_591
    · exact Work.RHContract.RegionI.thV_23
    · exact Work.RHContract.RegionI.thV_7
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((4391 : ℕ) : ℝ) ≤ (((676443294897 : ℚ) / 250000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_597
  have hSx : (((452222793157 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 4337, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_591
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_72 k := by decide +kernel
  have hT2 : (∑ k, tg_72 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_72 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_72 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((676443294897 : ℚ) / 250000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_72 k))
      + ((((452222793157 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_72 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_72 (yg_72 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨72, by omega⟩ : ℚ)) (εB := (cut ⟨73, by omega⟩ : ℚ)) hhi hlo
    14 14 (by norm_num) (by norm_num) hKtop xg_72 yg_72 tg_72 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((676443294897 : ℚ) / 250000000000)) (((452222793157 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_73 : Fin 14 → ℕ := fun k => [4391, 89, 19, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_73 : Fin 14 → ℕ := fun k => [4447, 90, 22, 10, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_73 : Fin 14 → ℚ := fun k => [((4311388296619171 : ℚ) / 1000000000000), ((39576839696887 : ℚ) / 500000000000), ((8043802239499 : ℚ) / 500000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_73 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨73, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨74, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (14 + 1) < (cut ⟨74, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 14, (cut ⟨73, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_73 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 14, Work.RHContract.RegionI.Fhi (yg_73 k + 1) (k.val + 1) < (cut ⟨74, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 14, 2 ≤ xg_73 k := by decide +kernel
  have hxhi : ∀ k : Fin 14, xg_73 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 14, yg_73 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 14, 1 ≤ yg_73 k := by decide +kernel
  have hposy : ∀ k : Fin 14, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_73 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_73 ⟨1, by omega⟩ + 1 ≤ xg_73 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 14, (tg_73 k : ℝ) ≤ Chebyshev.theta ((xg_73 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_597
    · exact Work.RHContract.RegionI.thV_23
    · exact Work.RHContract.RegionI.thV_7
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((4447 : ℕ) : ℝ) ≤ (((2707129898831 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_603
  have hSx : (((113055777127 : ℚ) / 250000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 4391, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_597
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_73 k := by decide +kernel
  have hT2 : (∑ k, tg_73 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_73 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_73 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2707129898831 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_73 k))
      + ((((113055777127 : ℚ) / 250000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_73 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_73 (yg_73 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨73, by omega⟩ : ℚ)) (εB := (cut ⟨74, by omega⟩ : ℚ)) hhi hlo
    14 14 (by norm_num) (by norm_num) hKtop xg_73 yg_73 tg_73 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2707129898831 : ℚ) / 1000000000000)) (((113055777127 : ℚ) / 250000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_74 : Fin 14 → ℕ := fun k => [4447, 89, 19, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_74 : Fin 14 → ℕ := fun k => [4493, 91, 22, 10, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_74 : Fin 14 → ℚ := fun k => [((4361755692072487 : ℚ) / 1000000000000), ((39576839696887 : ℚ) / 500000000000), ((8043802239499 : ℚ) / 500000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_74 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨74, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨75, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (14 + 1) < (cut ⟨75, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 14, (cut ⟨74, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_74 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 14, Work.RHContract.RegionI.Fhi (yg_74 k + 1) (k.val + 1) < (cut ⟨75, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 14, 2 ≤ xg_74 k := by decide +kernel
  have hxhi : ∀ k : Fin 14, xg_74 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 14, yg_74 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 14, 1 ≤ yg_74 k := by decide +kernel
  have hposy : ∀ k : Fin 14, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_74 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_74 ⟨1, by omega⟩ + 1 ≤ xg_74 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 14, (tg_74 k : ℝ) ≤ Chebyshev.theta ((xg_74 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_603
    · exact Work.RHContract.RegionI.thV_23
    · exact Work.RHContract.RegionI.thV_7
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((4493 : ℕ) : ℝ) ≤ (((2708471946049 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_609
  have hSx : (((226111707611 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 4447, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_603
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_74 k := by decide +kernel
  have hT2 : (∑ k, tg_74 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_74 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_74 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2708471946049 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_74 k))
      + ((((226111707611 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_74 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_74 (yg_74 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨74, by omega⟩ : ℚ)) (εB := (cut ⟨75, by omega⟩ : ℚ)) hhi hlo
    14 14 (by norm_num) (by norm_num) hKtop xg_74 yg_74 tg_74 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2708471946049 : ℚ) / 1000000000000)) (((226111707611 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_75 : Fin 14 → ℕ := fun k => [4493, 89, 19, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_75 : Fin 14 → ℕ := fun k => [4547, 91, 22, 10, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_75 : Fin 14 → ℚ := fun k => [((4412188308928371 : ℚ) / 1000000000000), ((39576839696887 : ℚ) / 500000000000), ((8043802239499 : ℚ) / 500000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_75 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨75, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨76, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (14 + 1) < (cut ⟨76, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 14, (cut ⟨75, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_75 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 14, Work.RHContract.RegionI.Fhi (yg_75 k + 1) (k.val + 1) < (cut ⟨76, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 14, 2 ≤ xg_75 k := by decide +kernel
  have hxhi : ∀ k : Fin 14, xg_75 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 14, yg_75 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 14, 1 ≤ yg_75 k := by decide +kernel
  have hposy : ∀ k : Fin 14, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_75 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_75 ⟨1, by omega⟩ + 1 ≤ xg_75 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 14, (tg_75 k : ℝ) ≤ Chebyshev.theta ((xg_75 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_609
    · exact Work.RHContract.RegionI.thV_23
    · exact Work.RHContract.RegionI.thV_7
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((4547 : ℕ) : ℝ) ≤ (((2709799243221 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_615
  have hSx : (((56527964417 : ℚ) / 125000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 4493, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_609
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_75 k := by decide +kernel
  have hT2 : (∑ k, tg_75 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_75 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_75 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2709799243221 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_75 k))
      + ((((56527964417 : ℚ) / 125000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_75 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_75 (yg_75 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨75, by omega⟩ : ℚ)) (εB := (cut ⟨76, by omega⟩ : ℚ)) hhi hlo
    14 14 (by norm_num) (by norm_num) hKtop xg_75 yg_75 tg_75 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2709799243221 : ℚ) / 1000000000000)) (((56527964417 : ℚ) / 125000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_76 : Fin 14 → ℕ := fun k => [4547, 89, 19, 7, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_76 : Fin 14 → ℕ := fun k => [4597, 92, 22, 11, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_76 : Fin 14 → ℚ := fun k => [((2231343608200269 : ℚ) / 500000000000), ((39576839696887 : ℚ) / 500000000000), ((8043802239499 : ℚ) / 500000000000), ((5347107529157 : ℚ) / 1000000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_76 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨76, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨77, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (14 + 1) < (cut ⟨77, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 14, (cut ⟨76, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_76 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 14, Work.RHContract.RegionI.Fhi (yg_76 k + 1) (k.val + 1) < (cut ⟨77, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 14, 2 ≤ xg_76 k := by decide +kernel
  have hxhi : ∀ k : Fin 14, xg_76 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 14, yg_76 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 14, 1 ≤ yg_76 k := by decide +kernel
  have hposy : ∀ k : Fin 14, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_76 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_76 ⟨1, by omega⟩ + 1 ≤ xg_76 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 14, (tg_76 k : ℝ) ≤ Chebyshev.theta ((xg_76 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_615
    · exact Work.RHContract.RegionI.thV_23
    · exact Work.RHContract.RegionI.thV_7
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((4597 : ℕ) : ℝ) ≤ (((10844443903 : ℚ) / 4000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_621
  have hSx : (((45222400889 : ℚ) / 100000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 4547, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_615
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_76 k := by decide +kernel
  have hT2 : (∑ k, tg_76 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_76 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_76 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((10844443903 : ℚ) / 4000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_76 k))
      + ((((45222400889 : ℚ) / 100000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_76 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_76 (yg_76 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨76, by omega⟩ : ℚ)) (εB := (cut ⟨77, by omega⟩ : ℚ)) hhi hlo
    14 14 (by norm_num) (by norm_num) hKtop xg_76 yg_76 tg_76 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((10844443903 : ℚ) / 4000000000)) (((45222400889 : ℚ) / 100000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_77 : Fin 14 → ℕ := fun k => [4597, 89, 19, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_77 : Fin 14 → ℕ := fun k => [4649, 92, 22, 11, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_77 : Fin 14 → ℚ := fun k => [((4513256909503849 : ℚ) / 1000000000000), ((39576839696887 : ℚ) / 500000000000), ((8043802239499 : ℚ) / 500000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_77 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨77, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨78, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (14 + 1) < (cut ⟨78, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 14, (cut ⟨77, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_77 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 14, Work.RHContract.RegionI.Fhi (yg_77 k + 1) (k.val + 1) < (cut ⟨78, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 14, 2 ≤ xg_77 k := by decide +kernel
  have hxhi : ∀ k : Fin 14, xg_77 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 14, yg_77 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 14, 1 ≤ yg_77 k := by decide +kernel
  have hposy : ∀ k : Fin 14, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_77 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_77 ⟨1, by omega⟩ + 1 ≤ xg_77 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 14, (tg_77 k : ℝ) ≤ Chebyshev.theta ((xg_77 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_621
    · exact Work.RHContract.RegionI.thV_23
    · exact Work.RHContract.RegionI.thV_7
    · exact Work.RHContract.RegionI.thV_4
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((4649 : ℕ) : ℝ) ≤ (((2712406466981 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_627
  have hSx : (((226112147801 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 4597, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_621
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_77 k := by decide +kernel
  have hT2 : (∑ k, tg_77 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_77 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_77 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2712406466981 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_77 k))
      + ((((226112147801 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_77 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_77 (yg_77 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨77, by omega⟩ : ℚ)) (εB := (cut ⟨78, by omega⟩ : ℚ)) hhi hlo
    14 14 (by norm_num) (by norm_num) hKtop xg_77 yg_77 tg_77 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2712406466981 : ℚ) / 1000000000000)) (((226112147801 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_78 : Fin 14 → ℕ := fun k => [4649, 89, 19, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_78 : Fin 14 → ℕ := fun k => [4691, 93, 22, 11, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_78 : Fin 14 → ℚ := fun k => [((4563901339838671 : ℚ) / 1000000000000), ((39576839696887 : ℚ) / 500000000000), ((8043802239499 : ℚ) / 500000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_78 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨78, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨79, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (14 + 1) < (cut ⟨79, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 14, (cut ⟨78, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_78 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 14, Work.RHContract.RegionI.Fhi (yg_78 k + 1) (k.val + 1) < (cut ⟨79, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 14, 2 ≤ xg_78 k := by decide +kernel
  have hxhi : ∀ k : Fin 14, xg_78 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 14, yg_78 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 14, 1 ≤ yg_78 k := by decide +kernel
  have hposy : ∀ k : Fin 14, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_78 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_78 ⟨1, by omega⟩ + 1 ≤ xg_78 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 14, (tg_78 k : ℝ) ≤ Chebyshev.theta ((xg_78 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_627
    · exact Work.RHContract.RegionI.thV_23
    · exact Work.RHContract.RegionI.thV_7
    · exact Work.RHContract.RegionI.thV_4
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((4691 : ℕ) : ℝ) ≤ (((1356845843607 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_633
  have hSx : (((226112287629 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 4649, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_627
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_78 k := by decide +kernel
  have hT2 : (∑ k, tg_78 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_78 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_78 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1356845843607 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_78 k))
      + ((((226112287629 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_78 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_78 (yg_78 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨78, by omega⟩ : ℚ)) (εB := (cut ⟨79, by omega⟩ : ℚ)) hhi hlo
    14 14 (by norm_num) (by norm_num) hKtop xg_78 yg_78 tg_78 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1356845843607 : ℚ) / 500000000000)) (((226112287629 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_79 : Fin 14 → ℕ := fun k => [4691, 89, 19, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_79 : Fin 14 → ℕ := fun k => [4751, 93, 23, 11, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_79 : Fin 14 → ℚ := fun k => [((2307296757840431 : ℚ) / 500000000000), ((39576839696887 : ℚ) / 500000000000), ((8043802239499 : ℚ) / 500000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_79 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨79, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨80, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (14 + 1) < (cut ⟨80, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 14, (cut ⟨79, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_79 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 14, Work.RHContract.RegionI.Fhi (yg_79 k + 1) (k.val + 1) < (cut ⟨80, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 14, 2 ≤ xg_79 k := by decide +kernel
  have hxhi : ∀ k : Fin 14, xg_79 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 14, yg_79 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 14, 1 ≤ yg_79 k := by decide +kernel
  have hposy : ∀ k : Fin 14, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_79 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_79 ⟨1, by omega⟩ + 1 ≤ xg_79 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 14, (tg_79 k : ℝ) ≤ Chebyshev.theta ((xg_79 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_633
    · exact Work.RHContract.RegionI.thV_23
    · exact Work.RHContract.RegionI.thV_7
    · exact Work.RHContract.RegionI.thV_4
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((4751 : ℕ) : ℝ) ≤ (((2714961226803 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_639
  have hSx : (((452224850497 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 4691, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_633
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_79 k := by decide +kernel
  have hT2 : (∑ k, tg_79 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_79 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_79 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2714961226803 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_79 k))
      + ((((452224850497 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_79 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_79 (yg_79 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨79, by omega⟩ : ℚ)) (εB := (cut ⟨80, by omega⟩ : ℚ)) hhi hlo
    14 14 (by norm_num) (by norm_num) hKtop xg_79 yg_79 tg_79 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2714961226803 : ℚ) / 1000000000000)) (((452224850497 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

end

end Work.RHContract.A.RegionI
