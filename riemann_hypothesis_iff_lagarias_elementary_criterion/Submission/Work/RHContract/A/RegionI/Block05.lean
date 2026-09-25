import Mathlib
import Submission.Work.RHContract.A.RegionI.Core
import Submission.Work.RHContract.A.RegionI.blockCert
import Submission.Work.RHContract.A.RegionI.Data11
import Submission.Work.RHContract.A.RegionI.Cuts

/-!  Region I: group certificates.  GENERATED FILE. -/

open scoped BigOperators

namespace Work.RHContract.A.RegionI

noncomputable section

private def xg_160 : Fin 15 → ℕ := fun k => [9629, 131, 29, 13, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_160 : Fin 15 → ℕ := fun k => [9697, 134, 29, 13, 8, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_160 : Fin 15 → ℚ := fun k => [((9528368870561749 : ℚ) / 1000000000000), ((116789188809669 : ℚ) / 1000000000000), ((22590394522833 : ℚ) / 1000000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_160 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨160, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨161, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨161, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨160, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_160 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_160 k + 1) (k.val + 1) < (cut ⟨161, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_160 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_160 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_160 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_160 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_160 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_160 ⟨1, by omega⟩ + 1 ≤ xg_160 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_160 k : ℝ) ≤ Chebyshev.theta ((xg_160 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1188
    · exact Work.RHContract.RegionI.thV_31
    · exact Work.RHContract.RegionI.thV_9
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
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((9697 : ℕ) : ℝ) ≤ (((559104179141 : ℚ) / 200000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1196
  have hSx : (((452237187519 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 9629, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1188
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_160 k := by decide +kernel
  have hT2 : (∑ k, tg_160 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_160 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_160 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((559104179141 : ℚ) / 200000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_160 k))
      + ((((452237187519 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_160 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_160 (yg_160 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨160, by omega⟩ : ℚ)) (εB := (cut ⟨161, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_160 yg_160 tg_160 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((559104179141 : ℚ) / 200000000000)) (((452237187519 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_161 : Fin 15 → ℕ := fun k => [9697, 131, 29, 13, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_161 : Fin 15 → ℕ := fun k => [9769, 134, 29, 13, 8, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_161 : Fin 15 → ℚ := fun k => [((120022245023063 : ℚ) / 12500000000), ((116789188809669 : ℚ) / 1000000000000), ((22590394522833 : ℚ) / 1000000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_161 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨161, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨162, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨162, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨161, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_161 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_161 k + 1) (k.val + 1) < (cut ⟨162, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_161 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_161 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_161 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_161 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_161 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_161 ⟨1, by omega⟩ + 1 ≤ xg_161 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_161 k : ℝ) ≤ Chebyshev.theta ((xg_161 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1196
    · exact Work.RHContract.RegionI.thV_31
    · exact Work.RHContract.RegionI.thV_9
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
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((9769 : ℕ) : ℝ) ≤ (((1398171042493 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1204
  have hSx : (((90447454629 : ℚ) / 200000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 9697, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1196
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_161 k := by decide +kernel
  have hT2 : (∑ k, tg_161 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_161 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_161 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1398171042493 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_161 k))
      + ((((90447454629 : ℚ) / 200000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_161 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_161 (yg_161 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨161, by omega⟩ : ℚ)) (εB := (cut ⟨162, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_161 yg_161 tg_161 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1398171042493 : ℚ) / 500000000000)) (((90447454629 : ℚ) / 200000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_162 : Fin 15 → ℕ := fun k => [9769, 131, 29, 13, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_162 : Fin 15 → ℕ := fun k => [9833, 135, 29, 13, 8, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_162 : Fin 15 → ℚ := fun k => [((9675253613149869 : ℚ) / 1000000000000), ((116789188809669 : ℚ) / 1000000000000), ((22590394522833 : ℚ) / 1000000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_162 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨162, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨163, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨163, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨162, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_162 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_162 k + 1) (k.val + 1) < (cut ⟨163, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_162 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_162 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_162 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_162 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_162 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_162 ⟨1, by omega⟩ + 1 ≤ xg_162 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_162 k : ℝ) ≤ Chebyshev.theta ((xg_162 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1204
    · exact Work.RHContract.RegionI.thV_31
    · exact Work.RHContract.RegionI.thV_9
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
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((9833 : ℕ) : ℝ) ≤ (((559431582963 : ℚ) / 200000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1212
  have hSx : (((452237357427 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 9769, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1204
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_162 k := by decide +kernel
  have hT2 : (∑ k, tg_162 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_162 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_162 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((559431582963 : ℚ) / 200000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_162 k))
      + ((((452237357427 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_162 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_162 (yg_162 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨162, by omega⟩ : ℚ)) (εB := (cut ⟨163, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_162 yg_162 tg_162 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((559431582963 : ℚ) / 200000000000)) (((452237357427 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_163 : Fin 15 → ℕ := fun k => [9833, 131, 29, 13, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_163 : Fin 16 → ℕ := fun k => [9901, 135, 29, 13, 8, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_163 : Fin 15 → ℚ := fun k => [((4874390002586183 : ℚ) / 500000000000), ((116789188809669 : ℚ) / 1000000000000), ((22590394522833 : ℚ) / 1000000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_163 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨163, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨164, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨164, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨163, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_163 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_163 k + 1) (k.val + 1) < (cut ⟨164, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_163 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_163 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_163 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_163 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_163 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_163 ⟨1, by omega⟩ + 1 ≤ xg_163 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_163 k : ℝ) ≤ Chebyshev.theta ((xg_163 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1212
    · exact Work.RHContract.RegionI.thV_31
    · exact Work.RHContract.RegionI.thV_9
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
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((9901 : ℕ) : ℝ) ≤ (((699492154803 : ℚ) / 250000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1220
  have hSx : (((452237440611 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 9833, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1212
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_163 k := by decide +kernel
  have hT2 : (∑ k, tg_163 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_163 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_163 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((699492154803 : ℚ) / 250000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_163 k))
      + ((((452237440611 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_163 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_163 (yg_163 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨163, by omega⟩ : ℚ)) (εB := (cut ⟨164, by omega⟩ : ℚ)) hhi hlo
    15 16 (by norm_num) (by norm_num) hKtop xg_163 yg_163 tg_163 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((699492154803 : ℚ) / 250000000000)) (((452237440611 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_164 : Fin 16 → ℕ := fun k => [9901, 131, 29, 13, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_164 : Fin 16 → ℕ := fun k => [9973, 136, 29, 13, 8, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_164 : Fin 16 → ℚ := fun k => [((9822356814836103 : ℚ) / 1000000000000), ((116789188809669 : ℚ) / 1000000000000), ((22590394522833 : ℚ) / 1000000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_164 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨164, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨165, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨165, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨164, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_164 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_164 k + 1) (k.val + 1) < (cut ⟨165, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_164 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_164 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_164 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_164 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_164 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_164 ⟨1, by omega⟩ + 1 ≤ xg_164 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_164 k : ℝ) ≤ Chebyshev.theta ((xg_164 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1220
    · exact Work.RHContract.RegionI.thV_31
    · exact Work.RHContract.RegionI.thV_9
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
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((9973 : ℕ) : ℝ) ≤ (((2798773492221 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1228
  have hSx : (((226118761377 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 9901, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1220
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_164 k := by decide +kernel
  have hT2 : (∑ k, tg_164 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_164 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_164 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2798773492221 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_164 k))
      + ((((226118761377 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_164 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_164 (yg_164 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨164, by omega⟩ : ℚ)) (εB := (cut ⟨165, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_164 yg_164 tg_164 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2798773492221 : ℚ) / 1000000000000)) (((226118761377 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_165 : Fin 16 → ℕ := fun k => [9973, 131, 29, 13, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_165 : Fin 16 → ℕ := fun k => [10079, 136, 29, 13, 8, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_165 : Fin 16 → ℚ := fun k => [((494799568780003 : ℚ) / 50000000000), ((116789188809669 : ℚ) / 1000000000000), ((22590394522833 : ℚ) / 1000000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_165 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨165, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨166, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨166, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨165, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_165 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_165 k + 1) (k.val + 1) < (cut ⟨166, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_165 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_165 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_165 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_165 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_165 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_165 ⟨1, by omega⟩ + 1 ≤ xg_165 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_165 k : ℝ) ≤ Chebyshev.theta ((xg_165 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1228
    · exact Work.RHContract.RegionI.thV_31
    · exact Work.RHContract.RegionI.thV_9
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
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((10079 : ℕ) : ℝ) ≤ (((2799569873951 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1236
  have hSx : (((11305940093 : ℚ) / 25000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 9973, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1228
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_165 k := by decide +kernel
  have hT2 : (∑ k, tg_165 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_165 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_165 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2799569873951 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_165 k))
      + ((((11305940093 : ℚ) / 25000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_165 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_165 (yg_165 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨165, by omega⟩ : ℚ)) (εB := (cut ⟨166, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_165 yg_165 tg_165 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2799569873951 : ℚ) / 1000000000000)) (((11305940093 : ℚ) / 25000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_166 : Fin 16 → ℕ := fun k => [10079, 131, 29, 13, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_166 : Fin 16 → ℕ := fun k => [10139, 137, 29, 13, 8, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_166 : Fin 16 → ℚ := fun k => [((9969710787873129 : ℚ) / 1000000000000), ((116789188809669 : ℚ) / 1000000000000), ((22590394522833 : ℚ) / 1000000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_166 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨166, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨167, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨167, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨166, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_166 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_166 k + 1) (k.val + 1) < (cut ⟨167, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_166 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_166 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_166 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_166 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_166 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_166 ⟨1, by omega⟩ + 1 ≤ xg_166 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_166 k : ℝ) ≤ Chebyshev.theta ((xg_166 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1236
    · exact Work.RHContract.RegionI.thV_31
    · exact Work.RHContract.RegionI.thV_9
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
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((10139 : ℕ) : ℝ) ≤ (((2800262303879 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1243
  have hSx : (((113059420747 : ℚ) / 250000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 10079, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1236
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_166 k := by decide +kernel
  have hT2 : (∑ k, tg_166 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_166 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_166 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2800262303879 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_166 k))
      + ((((113059420747 : ℚ) / 250000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_166 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_166 (yg_166 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨166, by omega⟩ : ℚ)) (εB := (cut ⟨167, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_166 yg_166 tg_166 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2800262303879 : ℚ) / 1000000000000)) (((113059420747 : ℚ) / 250000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_167 : Fin 16 → ℕ := fun k => [10139, 137, 29, 13, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_167 : Fin 16 → ℕ := fun k => [10193, 137, 29, 13, 8, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_167 : Fin 16 → ℚ := fun k => [((5017129820205561 : ℚ) / 500000000000), ((121709169733677 : ℚ) / 1000000000000), ((22590394522833 : ℚ) / 1000000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_167 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨167, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨168, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨168, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨167, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_167 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_167 k + 1) (k.val + 1) < (cut ⟨168, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_167 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_167 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_167 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_167 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_167 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_167 ⟨1, by omega⟩ + 1 ≤ xg_167 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_167 k : ℝ) ≤ Chebyshev.theta ((xg_167 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1243
    · exact Work.RHContract.RegionI.thV_32
    · exact Work.RHContract.RegionI.thV_9
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
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((10193 : ℕ) : ℝ) ≤ (((350131152909 : ℚ) / 125000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1251
  have hSx : (((28264859467 : ℚ) / 62500000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 10139, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1243
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_167 k := by decide +kernel
  have hT2 : (∑ k, tg_167 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_167 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_167 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((350131152909 : ℚ) / 125000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_167 k))
      + ((((28264859467 : ℚ) / 62500000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_167 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_167 (yg_167 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨167, by omega⟩ : ℚ)) (εB := (cut ⟨168, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_167 yg_167 tg_167 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((350131152909 : ℚ) / 125000000000)) (((28264859467 : ℚ) / 62500000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_168 : Fin 16 → ℕ := fun k => [10193, 137, 29, 13, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_168 : Fin 16 → ℕ := fun k => [10271, 138, 29, 13, 8, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_168 : Fin 16 → ℚ := fun k => [((1263509331716871 : ℚ) / 125000000000), ((121709169733677 : ℚ) / 1000000000000), ((22590394522833 : ℚ) / 1000000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_168 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨168, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨169, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨169, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨168, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_168 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_168 k + 1) (k.val + 1) < (cut ⟨169, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_168 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_168 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_168 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_168 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_168 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_168 ⟨1, by omega⟩ + 1 ≤ xg_168 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_168 k : ℝ) ≤ Chebyshev.theta ((xg_168 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1251
    · exact Work.RHContract.RegionI.thV_32
    · exact Work.RHContract.RegionI.thV_9
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
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((10271 : ℕ) : ℝ) ≤ (((2801829999563 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1259
  have hSx : (((90447565773 : ℚ) / 200000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 10193, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1251
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_168 k := by decide +kernel
  have hT2 : (∑ k, tg_168 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_168 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_168 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2801829999563 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_168 k))
      + ((((90447565773 : ℚ) / 200000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_168 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_168 (yg_168 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨168, by omega⟩ : ℚ)) (εB := (cut ⟨169, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_168 yg_168 tg_168 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2801829999563 : ℚ) / 1000000000000)) (((90447565773 : ℚ) / 200000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_169 : Fin 16 → ℕ := fun k => [10271, 137, 29, 13, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_169 : Fin 16 → ℕ := fun k => [10333, 138, 30, 13, 8, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_169 : Fin 16 → ℚ := fun k => [((10181952366092701 : ℚ) / 1000000000000), ((121709169733677 : ℚ) / 1000000000000), ((22590394522833 : ℚ) / 1000000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_169 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨169, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨170, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨170, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨169, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_169 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_169 k + 1) (k.val + 1) < (cut ⟨170, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_169 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_169 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_169 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_169 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_169 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_169 ⟨1, by omega⟩ + 1 ≤ xg_169 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_169 k : ℝ) ≤ Chebyshev.theta ((xg_169 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1259
    · exact Work.RHContract.RegionI.thV_32
    · exact Work.RHContract.RegionI.thV_9
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
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((10333 : ℕ) : ℝ) ≤ (((2802606136199 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1267
  have hSx : (((90447581011 : ℚ) / 200000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 10271, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1259
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_169 k := by decide +kernel
  have hT2 : (∑ k, tg_169 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_169 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_169 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2802606136199 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_169 k))
      + ((((90447581011 : ℚ) / 200000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_169 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_169 (yg_169 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨169, by omega⟩ : ℚ)) (εB := (cut ⟨170, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_169 yg_169 tg_169 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2802606136199 : ℚ) / 1000000000000)) (((90447581011 : ℚ) / 200000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_170 : Fin 16 → ℕ := fun k => [10333, 137, 29, 13, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_170 : Fin 16 → ℕ := fun k => [10427, 139, 30, 13, 8, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_170 : Fin 16 → ℚ := fun k => [((10255877756479029 : ℚ) / 1000000000000), ((121709169733677 : ℚ) / 1000000000000), ((22590394522833 : ℚ) / 1000000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_170 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨170, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨171, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨171, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨170, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_170 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_170 k + 1) (k.val + 1) < (cut ⟨171, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_170 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_170 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_170 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_170 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_170 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_170 ⟨1, by omega⟩ + 1 ≤ xg_170 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_170 k : ℝ) ≤ Chebyshev.theta ((xg_170 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1267
    · exact Work.RHContract.RegionI.thV_32
    · exact Work.RHContract.RegionI.thV_9
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
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((10427 : ℕ) : ℝ) ≤ (((175205055737 : ℚ) / 62500000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1274
  have hSx : (((452237980343 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 10333, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1267
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_170 k := by decide +kernel
  have hT2 : (∑ k, tg_170 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_170 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_170 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((175205055737 : ℚ) / 62500000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_170 k))
      + ((((452237980343 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_170 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_170 (yg_170 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨170, by omega⟩ : ℚ)) (εB := (cut ⟨171, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_170 yg_170 tg_170 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((175205055737 : ℚ) / 62500000000)) (((452237980343 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_171 : Fin 16 → ℕ := fun k => [10427, 139, 29, 13, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_171 : Fin 16 → ℕ := fun k => [10487, 139, 30, 13, 8, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_171 : Fin 16 → ℚ := fun k => [((5160303807278883 : ℚ) / 500000000000), ((31660910916247 : ℚ) / 250000000000), ((22590394522833 : ℚ) / 1000000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_171 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨171, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨172, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨172, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨171, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_171 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_171 k + 1) (k.val + 1) < (cut ⟨172, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_171 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_171 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_171 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_171 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_171 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_171 ⟨1, by omega⟩ + 1 ≤ xg_171 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_171 k : ℝ) ≤ Chebyshev.theta ((xg_171 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1274
    · exact Work.RHContract.RegionI.thV_33
    · exact Work.RHContract.RegionI.thV_9
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
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((10487 : ℕ) : ℝ) ≤ (((701011487559 : ℚ) / 250000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1282
  have hSx : (((3617904363 : ℚ) / 8000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 10427, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1274
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_171 k := by decide +kernel
  have hT2 : (∑ k, tg_171 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_171 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_171 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((701011487559 : ℚ) / 250000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_171 k))
      + ((((3617904363 : ℚ) / 8000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_171 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_171 (yg_171 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨171, by omega⟩ : ℚ)) (εB := (cut ⟨172, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_171 yg_171 tg_171 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((701011487559 : ℚ) / 250000000000)) (((3617904363 : ℚ) / 8000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_172 : Fin 16 → ℕ := fun k => [10487, 139, 29, 13, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_172 : Fin 16 → ℕ := fun k => [10589, 140, 30, 13, 8, 5, 4, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_172 : Fin 16 → ℚ := fun k => [((1039464800848777 : ℚ) / 100000000000), ((31660910916247 : ℚ) / 250000000000), ((22590394522833 : ℚ) / 1000000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_172 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨172, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨173, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨173, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨172, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_172 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_172 k + 1) (k.val + 1) < (cut ⟨173, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_172 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_172 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_172 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_172 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_172 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_172 ⟨1, by omega⟩ + 1 ≤ xg_172 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_172 k : ℝ) ≤ Chebyshev.theta ((xg_172 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1282
    · exact Work.RHContract.RegionI.thV_33
    · exact Work.RHContract.RegionI.thV_9
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
    · exact Work.RHContract.RegionI.thV_0
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((10589 : ℕ) : ℝ) ≤ (((2804805294121 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1290
  have hSx : (((45223811853 : ℚ) / 100000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 10487, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1282
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_172 k := by decide +kernel
  have hT2 : (∑ k, tg_172 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_172 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_172 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2804805294121 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_172 k))
      + ((((45223811853 : ℚ) / 100000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_172 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_172 (yg_172 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨172, by omega⟩ : ℚ)) (εB := (cut ⟨173, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_172 yg_172 tg_172 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2804805294121 : ℚ) / 1000000000000)) (((45223811853 : ℚ) / 100000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_173 : Fin 16 → ℕ := fun k => [10589, 139, 29, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_173 : Fin 16 → ℕ := fun k => [10651, 140, 30, 13, 8, 5, 4, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_173 : Fin 16 → ℚ := fun k => [((2617187100167111 : ℚ) / 250000000000), ((31660910916247 : ℚ) / 250000000000), ((22590394522833 : ℚ) / 1000000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_173 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨173, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨174, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨174, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨173, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_173 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_173 k + 1) (k.val + 1) < (cut ⟨174, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_173 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_173 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_173 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_173 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_173 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_173 ⟨1, by omega⟩ + 1 ≤ xg_173 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_173 k : ℝ) ≤ Chebyshev.theta ((xg_173 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1290
    · exact Work.RHContract.RegionI.thV_33
    · exact Work.RHContract.RegionI.thV_9
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((10651 : ℕ) : ℝ) ≤ (((2805558574227 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1298
  have hSx : (((90447638119 : ℚ) / 200000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 10589, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1290
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_173 k := by decide +kernel
  have hT2 : (∑ k, tg_173 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_173 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_173 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2805558574227 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_173 k))
      + ((((90447638119 : ℚ) / 200000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_173 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_173 (yg_173 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨173, by omega⟩ : ℚ)) (εB := (cut ⟨174, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_173 yg_173 tg_173 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2805558574227 : ℚ) / 1000000000000)) (((90447638119 : ℚ) / 200000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_174 : Fin 16 → ℕ := fun k => [10651, 139, 29, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_174 : Fin 16 → ℕ := fun k => [10723, 141, 30, 13, 8, 5, 4, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_174 : Fin 16 → ℚ := fun k => [((5271456454224871 : ℚ) / 500000000000), ((31660910916247 : ℚ) / 250000000000), ((22590394522833 : ℚ) / 1000000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_174 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨174, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨175, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨175, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨174, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_174 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_174 k + 1) (k.val + 1) < (cut ⟨175, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_174 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_174 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_174 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_174 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_174 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_174 ⟨1, by omega⟩ + 1 ≤ xg_174 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_174 k : ℝ) ≤ Chebyshev.theta ((xg_174 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1298
    · exact Work.RHContract.RegionI.thV_33
    · exact Work.RHContract.RegionI.thV_9
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((10723 : ℕ) : ℝ) ≤ (((2806307080689 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1306
  have hSx : (((226119130757 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 10651, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1298
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_174 k := by decide +kernel
  have hT2 : (∑ k, tg_174 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_174 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_174 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2806307080689 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_174 k))
      + ((((226119130757 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_174 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_174 (yg_174 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨174, by omega⟩ : ℚ)) (εB := (cut ⟨175, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_174 yg_174 tg_174 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2806307080689 : ℚ) / 1000000000000)) (((226119130757 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_175 : Fin 16 → ℕ := fun k => [10723, 139, 29, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_175 : Fin 16 → ℕ := fun k => [10799, 141, 30, 13, 8, 5, 4, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_175 : Fin 16 → ℚ := fun k => [((2654282069829873 : ℚ) / 250000000000), ((31660910916247 : ℚ) / 250000000000), ((22590394522833 : ℚ) / 1000000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_175 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨175, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨176, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨176, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨175, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_175 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_175 k + 1) (k.val + 1) < (cut ⟨176, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_175 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_175 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_175 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_175 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_175 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_175 ⟨1, by omega⟩ + 1 ≤ xg_175 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_175 k : ℝ) ≤ Chebyshev.theta ((xg_175 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1306
    · exact Work.RHContract.RegionI.thV_33
    · exact Work.RHContract.RegionI.thV_9
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((10799 : ℕ) : ℝ) ≤ (((2807050492831 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1314
  have hSx : (((452238331537 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 10723, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1306
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_175 k := by decide +kernel
  have hT2 : (∑ k, tg_175 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_175 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_175 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2807050492831 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_175 k))
      + ((((452238331537 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_175 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_175 (yg_175 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨175, by omega⟩ : ℚ)) (εB := (cut ⟨176, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_175 yg_175 tg_175 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2807050492831 : ℚ) / 1000000000000)) (((452238331537 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_176 : Fin 16 → ℕ := fun k => [10799, 139, 29, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_176 : Fin 16 → ℕ := fun k => [10883, 142, 30, 13, 8, 6, 4, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_176 : Fin 16 → ℚ := fun k => [((2138279657008899 : ℚ) / 200000000000), ((31660910916247 : ℚ) / 250000000000), ((22590394522833 : ℚ) / 1000000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_176 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨176, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨177, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨177, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨176, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_176 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_176 k + 1) (k.val + 1) < (cut ⟨177, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_176 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_176 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_176 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_176 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_176 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_176 ⟨1, by omega⟩ + 1 ≤ xg_176 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_176 k : ℝ) ≤ Chebyshev.theta ((xg_176 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1314
    · exact Work.RHContract.RegionI.thV_33
    · exact Work.RHContract.RegionI.thV_9
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((10883 : ℕ) : ℝ) ≤ (((2807787532847 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1322
  have hSx : (((452238400609 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 10799, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1314
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_176 k := by decide +kernel
  have hT2 : (∑ k, tg_176 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_176 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_176 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2807787532847 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_176 k))
      + ((((452238400609 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_176 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_176 (yg_176 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨176, by omega⟩ : ℚ)) (εB := (cut ⟨177, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_176 yg_176 tg_176 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2807787532847 : ℚ) / 1000000000000)) (((452238400609 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_177 : Fin 16 → ℕ := fun k => [10883, 139, 29, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_177 : Fin 16 → ℕ := fun k => [10957, 142, 30, 13, 8, 6, 4, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_177 : Fin 16 → ℚ := fun k => [((2691434285290989 : ℚ) / 250000000000), ((31660910916247 : ℚ) / 250000000000), ((22590394522833 : ℚ) / 1000000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_177 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨177, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨178, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨178, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨177, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_177 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_177 k + 1) (k.val + 1) < (cut ⟨178, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_177 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_177 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_177 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_177 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_177 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_177 ⟨1, by omega⟩ + 1 ≤ xg_177 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_177 k : ℝ) ≤ Chebyshev.theta ((xg_177 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1322
    · exact Work.RHContract.RegionI.thV_33
    · exact Work.RHContract.RegionI.thV_9
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((10957 : ℕ) : ℝ) ≤ (((2808520053609 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1330
  have hSx : (((226119234251 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 10883, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1322
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_177 k := by decide +kernel
  have hT2 : (∑ k, tg_177 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_177 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_177 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2808520053609 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_177 k))
      + ((((226119234251 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_177 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_177 (yg_177 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨177, by omega⟩ : ℚ)) (εB := (cut ⟨178, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_177 yg_177 tg_177 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2808520053609 : ℚ) / 1000000000000)) (((226119234251 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_178 : Fin 16 → ℕ := fun k => [10957, 139, 29, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_178 : Fin 16 → ℕ := fun k => [11057, 143, 30, 13, 8, 6, 4, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_178 : Fin 16 → ℚ := fun k => [((5420062605961189 : ℚ) / 500000000000), ((31660910916247 : ℚ) / 250000000000), ((22590394522833 : ℚ) / 1000000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_178 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨178, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨179, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨179, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨178, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_178 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_178 k + 1) (k.val + 1) < (cut ⟨179, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_178 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_178 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_178 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_178 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_178 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_178 ⟨1, by omega⟩ + 1 ≤ xg_178 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_178 k : ℝ) ≤ Chebyshev.theta ((xg_178 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1330
    · exact Work.RHContract.RegionI.thV_33
    · exact Work.RHContract.RegionI.thV_9
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((11057 : ℕ) : ℝ) ≤ (((351155852447 : ℚ) / 125000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1338
  have hSx : (((113059633891 : ℚ) / 250000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 10957, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1330
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_178 k := by decide +kernel
  have hT2 : (∑ k, tg_178 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_178 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_178 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((351155852447 : ℚ) / 125000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_178 k))
      + ((((113059633891 : ℚ) / 250000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_178 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_178 (yg_178 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨178, by omega⟩ : ℚ)) (εB := (cut ⟨179, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_178 yg_178 tg_178 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((351155852447 : ℚ) / 125000000000)) (((113059633891 : ℚ) / 250000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_179 : Fin 16 → ℕ := fun k => [11057, 139, 29, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_179 : Fin 16 → ℕ := fun k => [11117, 143, 30, 13, 8, 6, 4, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_179 : Fin 16 → ℚ := fun k => [((682161024064993 : ℚ) / 62500000000), ((31660910916247 : ℚ) / 250000000000), ((22590394522833 : ℚ) / 1000000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_179 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨179, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨180, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨180, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨179, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_179 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_179 k + 1) (k.val + 1) < (cut ⟨180, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_179 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_179 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_179 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_179 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_179 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_179 ⟨1, by omega⟩ + 1 ≤ xg_179 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_179 k : ℝ) ≤ Chebyshev.theta ((xg_179 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1338
    · exact Work.RHContract.RegionI.thV_33
    · exact Work.RHContract.RegionI.thV_9
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((11117 : ℕ) : ℝ) ≤ (((2809968452659 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1346
  have hSx : (((452238601579 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 11057, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1338
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_179 k := by decide +kernel
  have hT2 : (∑ k, tg_179 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_179 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_179 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2809968452659 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_179 k))
      + ((((452238601579 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_179 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_179 (yg_179 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨179, by omega⟩ : ℚ)) (εB := (cut ⟨180, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_179 yg_179 tg_179 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2809968452659 : ℚ) / 1000000000000)) (((452238601579 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_180 : Fin 16 → ℕ := fun k => [11117, 139, 29, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_180 : Fin 16 → ℕ := fun k => [11177, 144, 30, 13, 8, 6, 4, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_180 : Fin 16 → ℚ := fun k => [((5494542120150439 : ℚ) / 500000000000), ((31660910916247 : ℚ) / 250000000000), ((22590394522833 : ℚ) / 1000000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_180 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨180, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨181, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨181, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨180, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_180 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_180 k + 1) (k.val + 1) < (cut ⟨181, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_180 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_180 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_180 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_180 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_180 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_180 ⟨1, by omega⟩ + 1 ≤ xg_180 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_180 k : ℝ) ≤ Chebyshev.theta ((xg_180 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1346
    · exact Work.RHContract.RegionI.thV_33
    · exact Work.RHContract.RegionI.thV_9
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((11177 : ℕ) : ℝ) ≤ (((2810685654181 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1354
  have hSx : (((56529833333 : ℚ) / 125000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 11117, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1346
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_180 k := by decide +kernel
  have hT2 : (∑ k, tg_180 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_180 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_180 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2810685654181 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_180 k))
      + ((((56529833333 : ℚ) / 125000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_180 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_180 (yg_180 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨180, by omega⟩ : ℚ)) (εB := (cut ⟨181, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_180 yg_180 tg_180 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2810685654181 : ℚ) / 1000000000000)) (((56529833333 : ℚ) / 125000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_181 : Fin 16 → ℕ := fun k => [11177, 139, 29, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_181 : Fin 16 → ℕ := fun k => [11273, 144, 30, 13, 8, 6, 4, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_181 : Fin 16 → ℚ := fun k => [((11063641372968149 : ℚ) / 1000000000000), ((31660910916247 : ℚ) / 250000000000), ((22590394522833 : ℚ) / 1000000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_181 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨181, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨182, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨182, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨181, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_181 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_181 k + 1) (k.val + 1) < (cut ⟨182, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_181 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_181 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_181 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_181 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_181 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_181 ⟨1, by omega⟩ + 1 ≤ xg_181 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_181 k : ℝ) ≤ Chebyshev.theta ((xg_181 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1354
    · exact Work.RHContract.RegionI.thV_33
    · exact Work.RHContract.RegionI.thV_9
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((11273 : ℕ) : ℝ) ≤ (((2811397321989 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1362
  have hSx : (((56529841369 : ℚ) / 125000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 11177, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1354
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_181 k := by decide +kernel
  have hT2 : (∑ k, tg_181 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_181 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_181 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2811397321989 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_181 k))
      + ((((56529841369 : ℚ) / 125000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_181 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_181 (yg_181 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨181, by omega⟩ : ℚ)) (εB := (cut ⟨182, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_181 yg_181 tg_181 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2811397321989 : ℚ) / 1000000000000)) (((56529841369 : ℚ) / 125000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_182 : Fin 16 → ℕ := fun k => [11273, 139, 29, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_182 : Fin 16 → ℕ := fun k => [11329, 145, 31, 13, 8, 6, 4, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_182 : Fin 16 → ℚ := fun k => [((5569130236774383 : ℚ) / 500000000000), ((31660910916247 : ℚ) / 250000000000), ((22590394522833 : ℚ) / 1000000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_182 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨182, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨183, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨183, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨182, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_182 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_182 k + 1) (k.val + 1) < (cut ⟨183, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_182 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_182 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_182 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_182 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_182 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_182 ⟨1, by omega⟩ + 1 ≤ xg_182 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_182 k : ℝ) ≤ Chebyshev.theta ((xg_182 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1362
    · exact Work.RHContract.RegionI.thV_33
    · exact Work.RHContract.RegionI.thV_9
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((11329 : ℕ) : ℝ) ≤ (((1406008241621 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1369
  have hSx : (((113059698563 : ℚ) / 250000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 11273, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1362
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_182 k := by decide +kernel
  have hT2 : (∑ k, tg_182 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_182 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_182 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1406008241621 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_182 k))
      + ((((113059698563 : ℚ) / 250000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_182 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_182 (yg_182 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨182, by omega⟩ : ℚ)) (εB := (cut ⟨183, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_182 yg_182 tg_182 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1406008241621 : ℚ) / 500000000000)) (((113059698563 : ℚ) / 250000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_183 : Fin 16 → ℕ := fun k => [11329, 139, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_183 : Fin 16 → ℕ := fun k => [11423, 145, 31, 13, 8, 6, 4, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_183 : Fin 16 → ℚ := fun k => [((11203592175856361 : ℚ) / 1000000000000), ((31660910916247 : ℚ) / 250000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_183 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨183, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨184, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨184, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨183, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_183 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_183 k + 1) (k.val + 1) < (cut ⟨184, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_183 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_183 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_183 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_183 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_183 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_183 ⟨1, by omega⟩ + 1 ≤ xg_183 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_183 k : ℝ) ≤ Chebyshev.theta ((xg_183 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1369
    · exact Work.RHContract.RegionI.thV_33
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((11423 : ℕ) : ℝ) ≤ (((2812719180907 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1377
  have hSx : (((452238849009 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 11329, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1369
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_183 k := by decide +kernel
  have hT2 : (∑ k, tg_183 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_183 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_183 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2812719180907 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_183 k))
      + ((((452238849009 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_183 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_183 (yg_183 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨183, by omega⟩ : ℚ)) (εB := (cut ⟨184, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_183 yg_183 tg_183 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2812719180907 : ℚ) / 1000000000000)) (((452238849009 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_184 : Fin 16 → ℕ := fun k => [11423, 139, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_184 : Fin 16 → ℕ := fun k => [11491, 146, 31, 13, 8, 6, 4, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_184 : Fin 16 → ℚ := fun k => [((56391563743669 : ℚ) / 5000000000), ((31660910916247 : ℚ) / 250000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_184 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨184, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨185, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨185, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨184, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_184 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_184 k + 1) (k.val + 1) < (cut ⟨185, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_184 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_184 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_184 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_184 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_184 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_184 ⟨1, by omega⟩ + 1 ≤ xg_184 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_184 k : ℝ) ≤ Chebyshev.theta ((xg_184 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1377
    · exact Work.RHContract.RegionI.thV_33
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((11491 : ℕ) : ℝ) ≤ (((562683385689 : ℚ) / 200000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1385
  have hSx : (((452238910723 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 11423, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1377
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_184 k := by decide +kernel
  have hT2 : (∑ k, tg_184 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_184 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_184 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((562683385689 : ℚ) / 200000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_184 k))
      + ((((452238910723 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_184 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_184 (yg_184 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨184, by omega⟩ : ℚ)) (εB := (cut ⟨185, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_184 yg_184 tg_184 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((562683385689 : ℚ) / 200000000000)) (((452238910723 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_185 : Fin 16 → ℕ := fun k => [11491, 139, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_185 : Fin 16 → ℕ := fun k => [11587, 146, 31, 13, 8, 6, 4, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_185 : Fin 16 → ℚ := fun k => [((5676544933920993 : ℚ) / 500000000000), ((31660910916247 : ℚ) / 250000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_185 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨185, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨186, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨186, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨185, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_185 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_185 k + 1) (k.val + 1) < (cut ⟨186, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_185 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_185 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_185 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_185 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_185 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_185 ⟨1, by omega⟩ + 1 ≤ xg_185 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_185 k : ℝ) ≤ Chebyshev.theta ((xg_185 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1385
    · exact Work.RHContract.RegionI.thV_33
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((11587 : ℕ) : ℝ) ≤ (((562822052903 : ℚ) / 200000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1393
  have hSx : (((452238971569 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 11491, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1385
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_185 k := by decide +kernel
  have hT2 : (∑ k, tg_185 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_185 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_185 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((562822052903 : ℚ) / 200000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_185 k))
      + ((((452238971569 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_185 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_185 (yg_185 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨185, by omega⟩ : ℚ)) (εB := (cut ⟨186, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_185 yg_185 tg_185 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((562822052903 : ℚ) / 200000000000)) (((452238971569 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_186 : Fin 16 → ℕ := fun k => [11587, 139, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_186 : Fin 16 → ℕ := fun k => [11681, 147, 31, 14, 8, 6, 4, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_186 : Fin 16 → ℚ := fun k => [((11427917741764137 : ℚ) / 1000000000000), ((31660910916247 : ℚ) / 250000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_186 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨186, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨187, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨187, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨186, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_186 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_186 k + 1) (k.val + 1) < (cut ⟨187, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_186 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_186 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_186 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_186 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_186 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_186 ⟨1, by omega⟩ + 1 ≤ xg_186 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_186 k : ℝ) ≤ Chebyshev.theta ((xg_186 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1393
    · exact Work.RHContract.RegionI.thV_33
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((11681 : ℕ) : ℝ) ≤ (((703699477333 : ℚ) / 250000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1401
  have hSx : (((9044780633 : ℚ) / 20000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 11587, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1393
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_186 k := by decide +kernel
  have hT2 : (∑ k, tg_186 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_186 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_186 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((703699477333 : ℚ) / 250000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_186 k))
      + ((((9044780633 : ℚ) / 20000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_186 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_186 (yg_186 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨186, by omega⟩ : ℚ)) (εB := (cut ⟨187, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_186 yg_186 tg_186 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((703699477333 : ℚ) / 250000000000)) (((9044780633 : ℚ) / 20000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_187 : Fin 16 → ℕ := fun k => [11681, 139, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_187 : Fin 16 → ℕ := fun k => [11777, 148, 31, 14, 8, 6, 4, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_187 : Fin 16 → ℚ := fun k => [((11502811552659431 : ℚ) / 1000000000000), ((31660910916247 : ℚ) / 250000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_187 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨187, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨188, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨188, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨187, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_187 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_187 k + 1) (k.val + 1) < (cut ⟨188, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_187 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_187 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_187 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_187 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_187 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_187 ⟨1, by omega⟩ + 1 ≤ xg_187 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_187 k : ℝ) ≤ Chebyshev.theta ((xg_187 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1401
    · exact Work.RHContract.RegionI.thV_33
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((11777 : ℕ) : ℝ) ≤ (((2815480419337 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1409
  have hSx : (((452239090747 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 11681, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1401
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_187 k := by decide +kernel
  have hT2 : (∑ k, tg_187 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_187 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_187 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2815480419337 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_187 k))
      + ((((452239090747 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_187 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_187 (yg_187 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨187, by omega⟩ : ℚ)) (εB := (cut ⟨188, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_187 yg_187 tg_187 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2815480419337 : ℚ) / 1000000000000)) (((452239090747 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_188 : Fin 16 → ℕ := fun k => [11777, 139, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_188 : Fin 16 → ℕ := fun k => [11827, 148, 31, 14, 8, 6, 4, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_188 : Fin 16 → ℚ := fun k => [((5788882656854953 : ℚ) / 500000000000), ((31660910916247 : ℚ) / 250000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_188 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨188, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨189, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨189, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨188, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_188 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_188 k + 1) (k.val + 1) < (cut ⟨189, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_188 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_188 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_188 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_188 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_188 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_188 ⟨1, by omega⟩ + 1 ≤ xg_188 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_188 k : ℝ) ≤ Chebyshev.theta ((xg_188 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1409
    · exact Work.RHContract.RegionI.thV_33
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((11827 : ℕ) : ℝ) ≤ (((563231654377 : ℚ) / 200000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1417
  have hSx : (((113059787241 : ℚ) / 250000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 11777, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1409
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_188 k := by decide +kernel
  have hT2 : (∑ k, tg_188 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_188 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_188 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((563231654377 : ℚ) / 200000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_188 k))
      + ((((113059787241 : ℚ) / 250000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_188 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_188 (yg_188 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨188, by omega⟩ : ℚ)) (εB := (cut ⟨189, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_188 yg_188 tg_188 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((563231654377 : ℚ) / 200000000000)) (((113059787241 : ℚ) / 250000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_189 : Fin 16 → ℕ := fun k => [11827, 139, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_189 : Fin 16 → ℕ := fun k => [11903, 148, 31, 14, 8, 6, 4, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_189 : Fin 16 → ℚ := fun k => [((2330554767808263 : ℚ) / 200000000000), ((31660910916247 : ℚ) / 250000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_189 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨189, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨190, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨190, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨189, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_189 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_189 k + 1) (k.val + 1) < (cut ⟨190, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_189 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_189 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_189 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_189 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_189 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_189 ⟨1, by omega⟩ + 1 ≤ xg_189 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_189 k : ℝ) ≤ Chebyshev.theta ((xg_189 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1417
    · exact Work.RHContract.RegionI.thV_33
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((11903 : ℕ) : ℝ) ≤ (((704208138947 : ℚ) / 250000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1425
  have hSx : (((56529900799 : ℚ) / 125000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 11827, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1417
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_189 k := by decide +kernel
  have hT2 : (∑ k, tg_189 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_189 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_189 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((704208138947 : ℚ) / 250000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_189 k))
      + ((((56529900799 : ℚ) / 125000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_189 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_189 (yg_189 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨189, by omega⟩ : ℚ)) (εB := (cut ⟨190, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_189 yg_189 tg_189 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((704208138947 : ℚ) / 250000000000)) (((56529900799 : ℚ) / 125000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_190 : Fin 16 → ℕ := fun k => [11903, 139, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_190 : Fin 16 → ℕ := fun k => [11959, 149, 31, 14, 8, 6, 4, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_190 : Fin 16 → ℚ := fun k => [((5863912301855139 : ℚ) / 500000000000), ((31660910916247 : ℚ) / 250000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_190 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨190, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨191, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨191, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨190, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_190 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_190 k + 1) (k.val + 1) < (cut ⟨191, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_190 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_190 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_190 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_190 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_190 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_190 ⟨1, by omega⟩ + 1 ≤ xg_190 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_190 k : ℝ) ≤ Chebyshev.theta ((xg_190 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1425
    · exact Work.RHContract.RegionI.thV_33
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((11959 : ℕ) : ℝ) ≤ (((1408751427159 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1433
  have hSx : (((28264953951 : ℚ) / 62500000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 11903, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1425
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_190 k := by decide +kernel
  have hT2 : (∑ k, tg_190 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_190 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_190 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1408751427159 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_190 k))
      + ((((28264953951 : ℚ) / 62500000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_190 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_190 (yg_190 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨190, by omega⟩ : ℚ)) (εB := (cut ⟨191, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_190 yg_190 tg_190 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1408751427159 : ℚ) / 500000000000)) (((28264953951 : ℚ) / 62500000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_191 : Fin 16 → ℕ := fun k => [11959, 149, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_191 : Fin 16 → ℕ := fun k => [12041, 149, 31, 14, 8, 6, 4, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_191 : Fin 16 → ℚ := fun k => [((368841336771359 : ℚ) / 31250000000), ((131647589969113 : ℚ) / 1000000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_191 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨191, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨192, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨192, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨191, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_191 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_191 k + 1) (k.val + 1) < (cut ⟨192, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_191 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_191 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_191 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_191 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_191 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_191 ⟨1, by omega⟩ + 1 ≤ xg_191 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_191 k : ℝ) ≤ Chebyshev.theta ((xg_191 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1433
    · exact Work.RHContract.RegionI.thV_34
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((12041 : ℕ) : ℝ) ≤ (((1409084762099 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1441
  have hSx : (((45223931937 : ℚ) / 100000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 11959, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1433
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_191 k := by decide +kernel
  have hT2 : (∑ k, tg_191 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_191 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_191 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1409084762099 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_191 k))
      + ((((45223931937 : ℚ) / 100000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_191 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_191 (yg_191 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨191, by omega⟩ : ℚ)) (εB := (cut ⟨192, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_191 yg_191 tg_191 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1409084762099 : ℚ) / 500000000000)) (((45223931937 : ℚ) / 100000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_192 : Fin 16 → ℕ := fun k => [12041, 149, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_192 : Fin 16 → ℕ := fun k => [12109, 150, 31, 14, 8, 6, 4, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_192 : Fin 16 → ℚ := fun k => [((11878064386153279 : ℚ) / 1000000000000), ((131647589969113 : ℚ) / 1000000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_192 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨192, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨193, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨193, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨192, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_192 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_192 k + 1) (k.val + 1) < (cut ⟨193, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_192 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_192 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_192 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_192 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_192 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_192 ⟨1, by omega⟩ + 1 ≤ xg_192 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_192 k : ℝ) ≤ Chebyshev.theta ((xg_192 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1441
    · exact Work.RHContract.RegionI.thV_34
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((12109 : ℕ) : ℝ) ≤ (((2818831737439 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1449
  have hSx : (((226119687459 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 12041, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1441
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_192 k := by decide +kernel
  have hT2 : (∑ k, tg_192 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_192 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_192 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2818831737439 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_192 k))
      + ((((226119687459 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_192 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_192 (yg_192 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨192, by omega⟩ : ℚ)) (εB := (cut ⟨193, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_192 yg_192 tg_192 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2818831737439 : ℚ) / 1000000000000)) (((226119687459 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_193 : Fin 16 → ℕ := fun k => [12109, 149, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_193 : Fin 16 → ℕ := fun k => [12197, 150, 31, 14, 8, 6, 4, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_193 : Fin 16 → ℚ := fun k => [((5976629824699339 : ℚ) / 500000000000), ((131647589969113 : ℚ) / 1000000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_193 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨193, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨194, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨194, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨193, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_193 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_193 k + 1) (k.val + 1) < (cut ⟨194, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_193 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_193 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_193 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_193 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_193 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_193 ⟨1, by omega⟩ + 1 ≤ xg_193 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_193 k : ℝ) ≤ Chebyshev.theta ((xg_193 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1449
    · exact Work.RHContract.RegionI.thV_34
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((12197 : ℕ) : ℝ) ≤ (((2819490189953 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1457
  have hSx : (((18089577189 : ℚ) / 40000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 12109, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1449
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_193 k := by decide +kernel
  have hT2 : (∑ k, tg_193 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_193 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_193 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2819490189953 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_193 k))
      + ((((18089577189 : ℚ) / 40000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_193 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_193 (yg_193 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨193, by omega⟩ : ℚ)) (εB := (cut ⟨194, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_193 yg_193 tg_193 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2819490189953 : ℚ) / 1000000000000)) (((18089577189 : ℚ) / 40000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_194 : Fin 16 → ℕ := fun k => [12197, 149, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_194 : Fin 16 → ℕ := fun k => [12263, 151, 31, 14, 8, 6, 4, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_194 : Fin 16 → ℚ := fun k => [((3007125118221133 : ℚ) / 250000000000), ((131647589969113 : ℚ) / 1000000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_194 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨194, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨195, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨195, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨194, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_194 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_194 k + 1) (k.val + 1) < (cut ⟨195, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_194 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_194 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_194 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_194 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_194 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_194 ⟨1, by omega⟩ + 1 ≤ xg_194 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_194 k : ℝ) ≤ Chebyshev.theta ((xg_194 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1457
    · exact Work.RHContract.RegionI.thV_34
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((12263 : ℕ) : ℝ) ≤ (((705036006697 : ℚ) / 250000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1465
  have hSx : (((452239483911 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 12197, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1457
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_194 k := by decide +kernel
  have hT2 : (∑ k, tg_194 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_194 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_194 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((705036006697 : ℚ) / 250000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_194 k))
      + ((((452239483911 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_194 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_194 (yg_194 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨194, by omega⟩ : ℚ)) (εB := (cut ⟨195, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_194 yg_194 tg_194 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((705036006697 : ℚ) / 250000000000)) (((452239483911 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_195 : Fin 16 → ℕ := fun k => [12263, 151, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_195 : Fin 16 → ℕ := fun k => [12343, 151, 31, 14, 8, 6, 4, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_195 : Fin 16 → ℚ := fun k => [((6051898782118033 : ℚ) / 500000000000), ((34166217451027 : ℚ) / 250000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_195 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨195, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨196, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨196, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨195, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_195 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_195 k + 1) (k.val + 1) < (cut ⟨196, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_195 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_195 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_195 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_195 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_195 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_195 ⟨1, by omega⟩ + 1 ≤ xg_195 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_195 k : ℝ) ≤ Chebyshev.theta ((xg_195 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1465
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((12343 : ℕ) : ℝ) ≤ (((2820794383201 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1473
  have hSx : (((452239537339 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 12263, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1465
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_195 k := by decide +kernel
  have hT2 : (∑ k, tg_195 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_195 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_195 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2820794383201 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_195 k))
      + ((((452239537339 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_195 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_195 (yg_195 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨195, by omega⟩ : ℚ)) (εB := (cut ⟨196, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_195 yg_195 tg_195 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2820794383201 : ℚ) / 1000000000000)) (((452239537339 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_196 : Fin 16 → ℕ := fun k => [12343, 151, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_196 : Fin 16 → ℕ := fun k => [12413, 152, 31, 14, 8, 6, 4, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_196 : Fin 16 → ℚ := fun k => [((6089568679501157 : ℚ) / 500000000000), ((34166217451027 : ℚ) / 250000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_196 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨196, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨197, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨197, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨196, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_196 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_196 k + 1) (k.val + 1) < (cut ⟨197, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_196 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_196 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_196 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_196 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_196 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_196 ⟨1, by omega⟩ + 1 ≤ xg_196 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_196 k : ℝ) ≤ Chebyshev.theta ((xg_196 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1473
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((12413 : ℕ) : ℝ) ≤ (((2821440288517 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1481
  have hSx : (((452239590201 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 12343, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1473
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_196 k := by decide +kernel
  have hT2 : (∑ k, tg_196 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_196 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_196 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2821440288517 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_196 k))
      + ((((452239590201 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_196 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_196 (yg_196 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨196, by omega⟩ : ℚ)) (εB := (cut ⟨197, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_196 yg_196 tg_196 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2821440288517 : ℚ) / 1000000000000)) (((452239590201 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_197 : Fin 16 → ℕ := fun k => [12413, 151, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_197 : Fin 16 → ℕ := fun k => [12487, 152, 32, 14, 8, 6, 4, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_197 : Fin 16 → ℚ := fun k => [((12254532086248539 : ℚ) / 1000000000000), ((34166217451027 : ℚ) / 250000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_197 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨197, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨198, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨198, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨197, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_197 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_197 k + 1) (k.val + 1) < (cut ⟨198, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_197 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_197 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_197 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_197 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_197 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_197 ⟨1, by omega⟩ + 1 ≤ xg_197 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_197 k : ℝ) ≤ Chebyshev.theta ((xg_197 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1481
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((12487 : ℕ) : ℝ) ≤ (((56441652831 : ℚ) / 20000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1489
  have hSx : (((452239642343 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 12413, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1481
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_197 k := by decide +kernel
  have hT2 : (∑ k, tg_197 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_197 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_197 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((56441652831 : ℚ) / 20000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_197 k))
      + ((((452239642343 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_197 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_197 (yg_197 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨197, by omega⟩ : ℚ)) (εB := (cut ⟨198, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_197 yg_197 tg_197 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((56441652831 : ℚ) / 20000000000)) (((452239642343 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_198 : Fin 16 → ℕ := fun k => [12487, 151, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_198 : Fin 16 → ℕ := fun k => [12541, 152, 32, 14, 8, 6, 4, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_198 : Fin 16 → ℚ := fun k => [((6164985466234119 : ℚ) / 500000000000), ((34166217451027 : ℚ) / 250000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_198 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨198, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨199, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨199, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨198, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_198 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_198 k + 1) (k.val + 1) < (cut ⟨199, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_198 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_198 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_198 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_198 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_198 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_198 ⟨1, by omega⟩ + 1 ≤ xg_198 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_198 k : ℝ) ≤ Chebyshev.theta ((xg_198 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1489
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((12541 : ℕ) : ℝ) ≤ (((2822721862959 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1497
  have hSx : (((452239693913 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 12487, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1489
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_198 k := by decide +kernel
  have hT2 : (∑ k, tg_198 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_198 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_198 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2822721862959 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_198 k))
      + ((((452239693913 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_198 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_198 (yg_198 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨198, by omega⟩ : ℚ)) (εB := (cut ⟨199, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_198 yg_198 tg_198 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2822721862959 : ℚ) / 1000000000000)) (((452239693913 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_199 : Fin 16 → ℕ := fun k => [12541, 151, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_199 : Fin 16 → ℕ := fun k => [12611, 153, 32, 14, 8, 6, 4, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_199 : Fin 16 → ℚ := fun k => [((248108977392913 : ℚ) / 20000000000), ((34166217451027 : ℚ) / 250000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_199 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨199, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨200, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨200, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨199, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_199 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_199 k + 1) (k.val + 1) < (cut ⟨200, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_199 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_199 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_199 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_199 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_199 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_199 ⟨1, by omega⟩ + 1 ≤ xg_199 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_199 k : ℝ) ≤ Chebyshev.theta ((xg_199 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1497
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((12611 : ℕ) : ℝ) ≤ (((282335788321 : ℚ) / 100000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1505
  have hSx : (((452239744981 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 12541, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1497
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_199 k := by decide +kernel
  have hT2 : (∑ k, tg_199 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_199 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_199 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((282335788321 : ℚ) / 100000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_199 k))
      + ((((452239744981 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_199 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_199 (yg_199 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨199, by omega⟩ : ℚ)) (εB := (cut ⟨200, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_199 yg_199 tg_199 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((282335788321 : ℚ) / 100000000000)) (((452239744981 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

end

end Work.RHContract.A.RegionI
