import Mathlib
import Submission.Work.RHContract.A.RegionI.Core
import Submission.Work.RHContract.A.RegionI.blockCert
import Submission.Work.RHContract.A.RegionI.Data11
import Submission.Work.RHContract.A.RegionI.Cuts

/-!  Region I: group certificates.  GENERATED FILE. -/

open scoped BigOperators

namespace Work.RHContract.A.RegionI

noncomputable section

private def xg_240 : Fin 16 → ℕ := fun k => [15817, 167, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_240 : Fin 16 → ℕ := fun k => [15913, 172, 34, 15, 9, 6, 4, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_240 : Fin 16 → ℚ := fun k => [((15731994130976699 : ℚ) / 1000000000000), ((7596642980861 : ℚ) / 50000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_240 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨240, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨241, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨241, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨240, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_240 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_240 k + 1) (k.val + 1) < (cut ⟨241, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_240 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_240 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_240 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_240 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_240 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_240 ⟨1, by omega⟩ + 1 ≤ xg_240 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_240 k : ℝ) ≤ Chebyshev.theta ((xg_240 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1845
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((15913 : ℕ) : ℝ) ≤ (((2847901733047 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1854
  have hSx : (((226120746827 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 15817, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1845
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_240 k := by decide +kernel
  have hT2 : (∑ k, tg_240 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_240 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_240 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2847901733047 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_240 k))
      + ((((226120746827 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_240 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_240 (yg_240 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨240, by omega⟩ : ℚ)) (εB := (cut ⟨241, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_240 yg_240 tg_240 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2847901733047 : ℚ) / 1000000000000)) (((226120746827 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_241 : Fin 16 → ℕ := fun k => [15913, 167, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_241 : Fin 16 → ℕ := fun k => [16007, 172, 34, 15, 9, 6, 4, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_241 : Fin 16 → ℚ := fun k => [((15819050531004717 : ℚ) / 1000000000000), ((7596642980861 : ℚ) / 50000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_241 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨241, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨242, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨242, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨241, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_241 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_241 k + 1) (k.val + 1) < (cut ⟨242, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_241 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_241 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_241 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_241 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_241 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_241 ⟨1, by omega⟩ + 1 ≤ xg_241 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_241 k : ℝ) ≤ Chebyshev.theta ((xg_241 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1854
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((16007 : ℕ) : ℝ) ≤ (((1424232750833 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1863
  have hSx : (((90448305867 : ℚ) / 200000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 15913, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1854
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_241 k := by decide +kernel
  have hT2 : (∑ k, tg_241 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_241 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_241 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1424232750833 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_241 k))
      + ((((90448305867 : ℚ) / 200000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_241 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_241 (yg_241 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨241, by omega⟩ : ℚ)) (εB := (cut ⟨242, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_241 yg_241 tg_241 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1424232750833 : ℚ) / 500000000000)) (((90448305867 : ℚ) / 200000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_242 : Fin 16 → ℕ := fun k => [16007, 167, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_242 : Fin 16 → ℕ := fun k => [16087, 173, 34, 15, 9, 6, 4, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_242 : Fin 16 → ℚ := fun k => [((15906153650622991 : ℚ) / 1000000000000), ((7596642980861 : ℚ) / 50000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_242 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨242, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨243, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨243, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨242, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_242 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_242 k + 1) (k.val + 1) < (cut ⟨243, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_242 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_242 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_242 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_242 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_242 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_242 ⟨1, by omega⟩ + 1 ≤ xg_242 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_242 k : ℝ) ≤ Chebyshev.theta ((xg_242 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1863
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((16087 : ℕ) : ℝ) ≤ (((2848963533293 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1871
  have hSx : (((113060391161 : ℚ) / 250000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 16007, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1863
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_242 k := by decide +kernel
  have hT2 : (∑ k, tg_242 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_242 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_242 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2848963533293 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_242 k))
      + ((((113060391161 : ℚ) / 250000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_242 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_242 (yg_242 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨242, by omega⟩ : ℚ)) (εB := (cut ⟨243, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_242 yg_242 tg_242 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2848963533293 : ℚ) / 1000000000000)) (((113060391161 : ℚ) / 250000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_243 : Fin 16 → ℕ := fun k => [16087, 173, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_243 : Fin 16 → ℕ := fun k => [16187, 173, 34, 15, 9, 6, 4, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_243 : Fin 16 → ℚ := fun k => [((15983628211048357 : ℚ) / 1000000000000), ((78543075604949 : ℚ) / 500000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_243 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨243, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨244, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨244, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨243, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_243 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_243 k + 1) (k.val + 1) < (cut ⟨244, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_243 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_243 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_243 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_243 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_243 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_243 ⟨1, by omega⟩ + 1 ≤ xg_243 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_243 k : ℝ) ≤ Chebyshev.theta ((xg_243 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1871
    · exact Work.RHContract.RegionI.thV_39
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((16187 : ℕ) : ℝ) ≤ (((569904296979 : ℚ) / 200000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1880
  have hSx : (((226120797821 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 16087, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1871
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_243 k := by decide +kernel
  have hT2 : (∑ k, tg_243 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_243 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_243 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((569904296979 : ℚ) / 200000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_243 k))
      + ((((226120797821 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_243 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_243 (yg_243 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨243, by omega⟩ : ℚ)) (εB := (cut ⟨244, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_243 yg_243 tg_243 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((569904296979 : ℚ) / 200000000000)) (((226120797821 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_244 : Fin 16 → ℕ := fun k => [16187, 173, 31, 13, 7, 5, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_244 : Fin 16 → ℕ := fun k => [16267, 174, 35, 15, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_244 : Fin 16 → ℚ := fun k => [((2008853084422919 : ℚ) / 125000000000), ((78543075604949 : ℚ) / 500000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_244 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨244, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨245, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨245, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨244, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_244 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_244 k + 1) (k.val + 1) < (cut ⟨245, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_244 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_244 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_244 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_244 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_244 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_244 ⟨1, by omega⟩ + 1 ≤ xg_244 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_244 k : ℝ) ≤ Chebyshev.theta ((xg_244 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1880
    · exact Work.RHContract.RegionI.thV_39
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((16267 : ℕ) : ℝ) ≤ (((2850076104063 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1889
  have hSx : (((226120815113 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 16187, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1880
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_244 k := by decide +kernel
  have hT2 : (∑ k, tg_244 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_244 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_244 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2850076104063 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_244 k))
      + ((((226120815113 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_244 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_244 (yg_244 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨244, by omega⟩ : ℚ)) (εB := (cut ⟨245, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_244 yg_244 tg_244 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2850076104063 : ℚ) / 1000000000000)) (((226120815113 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_245 : Fin 16 → ℕ := fun k => [16267, 173, 31, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_245 : Fin 16 → ℕ := fun k => [16369, 174, 35, 15, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_245 : Fin 16 → ℚ := fun k => [((16158075044126873 : ℚ) / 1000000000000), ((78543075604949 : ℚ) / 500000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_245 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨245, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨246, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨246, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨245, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_245 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_245 k + 1) (k.val + 1) < (cut ⟨246, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_245 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_245 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_245 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_245 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_245 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_245 ⟨1, by omega⟩ + 1 ≤ xg_245 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_245 k : ℝ) ≤ Chebyshev.theta ((xg_245 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1889
    · exact Work.RHContract.RegionI.thV_39
    · exact Work.RHContract.RegionI.thV_10
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((16369 : ℕ) : ℝ) ≤ (((2850627116963 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1898
  have hSx : (((452241664397 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 16267, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1889
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_245 k := by decide +kernel
  have hT2 : (∑ k, tg_245 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_245 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_245 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2850627116963 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_245 k))
      + ((((452241664397 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_245 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_245 (yg_245 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨245, by omega⟩ : ℚ)) (εB := (cut ⟨246, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_245 yg_245 tg_245 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2850627116963 : ℚ) / 1000000000000)) (((452241664397 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_246 : Fin 16 → ℕ := fun k => [16369, 173, 31, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_246 : Fin 16 → ℕ := fun k => [16453, 175, 35, 15, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_246 : Fin 16 → ℚ := fun k => [((4061346031773967 : ℚ) / 250000000000), ((78543075604949 : ℚ) / 500000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_246 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨246, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨247, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨247, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨246, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_246 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_246 k + 1) (k.val + 1) < (cut ⟨247, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_246 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_246 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_246 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_246 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_246 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_246 ⟨1, by omega⟩ + 1 ≤ xg_246 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_246 k : ℝ) ≤ Chebyshev.theta ((xg_246 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1898
    · exact Work.RHContract.RegionI.thV_39
    · exact Work.RHContract.RegionI.thV_10
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((16453 : ℕ) : ℝ) ≤ (((2851175020497 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1907
  have hSx : (((226120849063 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 16369, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1898
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_246 k := by decide +kernel
  have hT2 : (∑ k, tg_246 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_246 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_246 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2851175020497 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_246 k))
      + ((((226120849063 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_246 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_246 (yg_246 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨246, by omega⟩ : ℚ)) (εB := (cut ⟨247, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_246 yg_246 tg_246 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2851175020497 : ℚ) / 1000000000000)) (((226120849063 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_247 : Fin 16 → ℕ := fun k => [16453, 173, 31, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_247 : Fin 16 → ℕ := fun k => [16561, 175, 35, 15, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_247 : Fin 16 → ℚ := fun k => [((510398254123341 : ℚ) / 31250000000), ((78543075604949 : ℚ) / 500000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_247 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨247, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨248, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨248, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨247, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_247 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_247 k + 1) (k.val + 1) < (cut ⟨248, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_247 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_247 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_247 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_247 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_247 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_247 ⟨1, by omega⟩ + 1 ≤ xg_247 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_247 k : ℝ) ≤ Chebyshev.theta ((xg_247 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1907
    · exact Work.RHContract.RegionI.thV_39
    · exact Work.RHContract.RegionI.thV_10
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((16561 : ℕ) : ℝ) ≤ (((712929988513 : ℚ) / 250000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1916
  have hSx : (((113060432869 : ℚ) / 250000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 16453, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1907
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_247 k := by decide +kernel
  have hT2 : (∑ k, tg_247 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_247 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_247 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((712929988513 : ℚ) / 250000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_247 k))
      + ((((113060432869 : ℚ) / 250000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_247 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_247 (yg_247 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨247, by omega⟩ : ℚ)) (εB := (cut ⟨248, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_247 yg_247 tg_247 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((712929988513 : ℚ) / 250000000000)) (((113060432869 : ℚ) / 250000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_248 : Fin 16 → ℕ := fun k => [16561, 173, 31, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_248 : Fin 16 → ℕ := fun k => [16651, 176, 35, 15, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_248 : Fin 16 → ℚ := fun k => [((4105038265422067 : ℚ) / 250000000000), ((78543075604949 : ℚ) / 500000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_248 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨248, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨249, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨249, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨248, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_248 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_248 k + 1) (k.val + 1) < (cut ⟨249, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_248 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_248 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_248 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_248 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_248 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_248 ⟨1, by omega⟩ + 1 ≤ xg_248 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_248 k : ℝ) ≤ Chebyshev.theta ((xg_248 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1916
    · exact Work.RHContract.RegionI.thV_39
    · exact Work.RHContract.RegionI.thV_10
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((16651 : ℕ) : ℝ) ≤ (((2852261658407 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1925
  have hSx : (((90448352893 : ℚ) / 200000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 16561, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1916
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_248 k := by decide +kernel
  have hT2 : (∑ k, tg_248 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_248 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_248 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2852261658407 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_248 k))
      + ((((90448352893 : ℚ) / 200000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_248 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_248 (yg_248 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨248, by omega⟩ : ℚ)) (εB := (cut ⟨249, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_248 yg_248 tg_248 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2852261658407 : ℚ) / 1000000000000)) (((90448352893 : ℚ) / 200000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_249 : Fin 16 → ℕ := fun k => [16651, 173, 31, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_249 : Fin 16 → ℕ := fun k => [16741, 176, 35, 15, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_249 : Fin 16 → ℚ := fun k => [((3301523095727497 : ℚ) / 200000000000), ((78543075604949 : ℚ) / 500000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_249 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨249, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨250, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨250, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨249, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_249 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_249 k + 1) (k.val + 1) < (cut ⟨250, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_249 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_249 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_249 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_249 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_249 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_249 ⟨1, by omega⟩ + 1 ≤ xg_249 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_249 k : ℝ) ≤ Chebyshev.theta ((xg_249 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1925
    · exact Work.RHContract.RegionI.thV_39
    · exact Work.RHContract.RegionI.thV_10
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((16741 : ℕ) : ℝ) ≤ (((1426400394103 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1934
  have hSx : (((226120898531 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 16651, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1925
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_249 k := by decide +kernel
  have hT2 : (∑ k, tg_249 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_249 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_249 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1426400394103 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_249 k))
      + ((((226120898531 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_249 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_249 (yg_249 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨249, by omega⟩ : ℚ)) (εB := (cut ⟨250, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_249 yg_249 tg_249 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1426400394103 : ℚ) / 500000000000)) (((226120898531 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_250 : Fin 16 → ℕ := fun k => [16741, 173, 31, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_250 : Fin 16 → ℕ := fun k => [16843, 177, 35, 15, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_250 : Fin 16 → ℚ := fun k => [((8297560384405819 : ℚ) / 500000000000), ((78543075604949 : ℚ) / 500000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_250 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨250, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨251, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨251, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨250, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_250 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_250 k + 1) (k.val + 1) < (cut ⟨251, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_250 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_250 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_250 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_250 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_250 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_250 ⟨1, by omega⟩ + 1 ≤ xg_250 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_250 k : ℝ) ≤ Chebyshev.theta ((xg_250 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1934
    · exact Work.RHContract.RegionI.thV_39
    · exact Work.RHContract.RegionI.thV_10
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((16843 : ℕ) : ℝ) ≤ (((178333534089 : ℚ) / 62500000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1943
  have hSx : (((452241829353 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 16741, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1934
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_250 k := by decide +kernel
  have hT2 : (∑ k, tg_250 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_250 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_250 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((178333534089 : ℚ) / 62500000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_250 k))
      + ((((452241829353 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_250 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_250 (yg_250 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨250, by omega⟩ : ℚ)) (εB := (cut ⟨251, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_250 yg_250 tg_250 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((178333534089 : ℚ) / 62500000000)) (((452241829353 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_251 : Fin 16 → ℕ := fun k => [16843, 173, 31, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_251 : Fin 16 → ℕ := fun k => [16931, 177, 35, 15, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_251 : Fin 16 → ℚ := fun k => [((16682682541293743 : ℚ) / 1000000000000), ((78543075604949 : ℚ) / 500000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_251 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨251, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨252, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨252, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨251, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_251 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_251 k + 1) (k.val + 1) < (cut ⟨252, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_251 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_251 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_251 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_251 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_251 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_251 ⟨1, by omega⟩ + 1 ≤ xg_251 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_251 k : ℝ) ≤ Chebyshev.theta ((xg_251 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1943
    · exact Work.RHContract.RegionI.thV_39
    · exact Work.RHContract.RegionI.thV_10
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((16931 : ℕ) : ℝ) ≤ (((2853869088851 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1952
  have hSx : (((11306046531 : ℚ) / 25000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 16843, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1943
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_251 k := by decide +kernel
  have hT2 : (∑ k, tg_251 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_251 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_251 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2853869088851 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_251 k))
      + ((((11306046531 : ℚ) / 25000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_251 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_251 (yg_251 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨251, by omega⟩ : ℚ)) (εB := (cut ⟨252, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_251 yg_251 tg_251 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2853869088851 : ℚ) / 1000000000000)) (((11306046531 : ℚ) / 25000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_252 : Fin 16 → ℕ := fun k => [16931, 173, 31, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_252 : Fin 16 → ℕ := fun k => [17021, 178, 35, 15, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_252 : Fin 16 → ℚ := fun k => [((16770298450518267 : ℚ) / 1000000000000), ((78543075604949 : ℚ) / 500000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_252 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨252, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨253, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨253, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨252, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_252 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_252 k + 1) (k.val + 1) < (cut ⟨253, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_252 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_252 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_252 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_252 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_252 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_252 ⟨1, by omega⟩ + 1 ≤ xg_252 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_252 k : ℝ) ≤ Chebyshev.theta ((xg_252 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1952
    · exact Work.RHContract.RegionI.thV_39
    · exact Work.RHContract.RegionI.thV_10
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((17021 : ℕ) : ℝ) ≤ (((713599789611 : ℚ) / 250000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1961
  have hSx : (((90448378549 : ℚ) / 200000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 16931, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1952
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_252 k := by decide +kernel
  have hT2 : (∑ k, tg_252 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_252 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_252 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((713599789611 : ℚ) / 250000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_252 k))
      + ((((90448378549 : ℚ) / 200000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_252 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_252 (yg_252 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨252, by omega⟩ : ℚ)) (εB := (cut ⟨253, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_252 yg_252 tg_252 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((713599789611 : ℚ) / 250000000000)) (((90448378549 : ℚ) / 200000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_253 : Fin 16 → ℕ := fun k => [17021, 173, 31, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_253 : Fin 16 → ℕ := fun k => [17099, 178, 35, 15, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_253 : Fin 16 → ℚ := fun k => [((16857956268112887 : ℚ) / 1000000000000), ((78543075604949 : ℚ) / 500000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_253 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨253, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨254, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨254, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨253, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_253 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_253 k + 1) (k.val + 1) < (cut ⟨254, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_253 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_253 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_253 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_253 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_253 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_253 ⟨1, by omega⟩ + 1 ≤ xg_253 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_253 k : ℝ) ≤ Chebyshev.theta ((xg_253 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1961
    · exact Work.RHContract.RegionI.thV_39
    · exact Work.RHContract.RegionI.thV_10
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((17099 : ℕ) : ℝ) ≤ (((713731716469 : ℚ) / 250000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1970
  have hSx : (((452241923957 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 17021, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1961
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_253 k := by decide +kernel
  have hT2 : (∑ k, tg_253 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_253 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_253 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((713731716469 : ℚ) / 250000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_253 k))
      + ((((452241923957 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_253 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_253 (yg_253 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨253, by omega⟩ : ℚ)) (εB := (cut ⟨254, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_253 yg_253 tg_253 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((713731716469 : ℚ) / 250000000000)) (((452241923957 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_254 : Fin 16 → ℕ := fun k => [17099, 173, 31, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_254 : Fin 16 → ℕ := fun k => [17189, 179, 35, 15, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_254 : Fin 16 → ℚ := fun k => [((8472827140219051 : ℚ) / 500000000000), ((78543075604949 : ℚ) / 500000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_254 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨254, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨255, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨255, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨254, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_254 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_254 k + 1) (k.val + 1) < (cut ⟨255, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_254 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_254 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_254 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_254 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_254 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_254 ⟨1, by omega⟩ + 1 ≤ xg_254 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_254 k : ℝ) ≤ Chebyshev.theta ((xg_254 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1970
    · exact Work.RHContract.RegionI.thV_39
    · exact Work.RHContract.RegionI.thV_10
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((17189 : ℕ) : ℝ) ≤ (((2855393414337 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1978
  have hSx : (((452241954893 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 17099, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1970
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_254 k := by decide +kernel
  have hT2 : (∑ k, tg_254 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_254 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_254 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2855393414337 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_254 k))
      + ((((452241954893 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_254 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_254 (yg_254 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨254, by omega⟩ : ℚ)) (εB := (cut ⟨255, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_254 yg_254 tg_254 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2855393414337 : ℚ) / 1000000000000)) (((452241954893 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_255 : Fin 16 → ℕ := fun k => [17189, 179, 31, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_255 : Fin 16 → ℕ := fun k => [17293, 179, 35, 15, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_255 : Fin 16 → ℚ := fun k => [((17023651246877613 : ℚ) / 1000000000000), ((162273537013919 : ℚ) / 1000000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_255 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨255, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨256, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨256, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨255, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_255 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_255 k + 1) (k.val + 1) < (cut ⟨256, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_255 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_255 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_255 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_255 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_255 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_255 ⟨1, by omega⟩ + 1 ≤ xg_255 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_255 k : ℝ) ≤ Chebyshev.theta ((xg_255 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1978
    · exact Work.RHContract.RegionI.thV_40
    · exact Work.RHContract.RegionI.thV_10
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((17293 : ℕ) : ℝ) ≤ (((1427957802367 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1987
  have hSx : (((452241982097 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 17189, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1978
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_255 k := by decide +kernel
  have hT2 : (∑ k, tg_255 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_255 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_255 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1427957802367 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_255 k))
      + ((((452241982097 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_255 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_255 (yg_255 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨255, by omega⟩ : ℚ)) (εB := (cut ⟨256, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_255 yg_255 tg_255 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1427957802367 : ℚ) / 500000000000)) (((452241982097 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_256 : Fin 16 → ℕ := fun k => [17293, 179, 31, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_256 : Fin 16 → ℕ := fun k => [17377, 180, 35, 15, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_256 : Fin 16 → ℚ := fun k => [((17111443853049127 : ℚ) / 1000000000000), ((162273537013919 : ℚ) / 1000000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_256 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨256, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨257, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨257, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨256, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_256 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_256 k + 1) (k.val + 1) < (cut ⟨257, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_256 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_256 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_256 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_256 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_256 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_256 ⟨1, by omega⟩ + 1 ≤ xg_256 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_256 k : ℝ) ≤ Chebyshev.theta ((xg_256 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1987
    · exact Work.RHContract.RegionI.thV_40
    · exact Work.RHContract.RegionI.thV_10
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((17377 : ℕ) : ℝ) ≤ (((2856434768149 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1996
  have hSx : (((113060503097 : ℚ) / 250000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 17293, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1987
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_256 k := by decide +kernel
  have hT2 : (∑ k, tg_256 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_256 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_256 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2856434768149 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_256 k))
      + ((((113060503097 : ℚ) / 250000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_256 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_256 (yg_256 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨256, by omega⟩ : ℚ)) (εB := (cut ⟨257, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_256 yg_256 tg_256 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2856434768149 : ℚ) / 1000000000000)) (((113060503097 : ℚ) / 250000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_257 : Fin 16 → ℕ := fun k => [17377, 179, 31, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_257 : Fin 16 → ℕ := fun k => [17443, 180, 35, 15, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_257 : Fin 16 → ℚ := fun k => [((17199288768095283 : ℚ) / 1000000000000), ((162273537013919 : ℚ) / 1000000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_257 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨257, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨258, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨258, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨257, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_257 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_257 k + 1) (k.val + 1) < (cut ⟨258, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_257 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_257 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_257 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_257 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_257 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_257 ⟨1, by omega⟩ + 1 ≤ xg_257 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_257 k : ℝ) ≤ Chebyshev.theta ((xg_257 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1996
    · exact Work.RHContract.RegionI.thV_40
    · exact Work.RHContract.RegionI.thV_10
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((17443 : ℕ) : ℝ) ≤ (((1428475908537 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2005
  have hSx : (((452242042329 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 17377, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1996
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_257 k := by decide +kernel
  have hT2 : (∑ k, tg_257 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_257 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_257 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1428475908537 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_257 k))
      + ((((452242042329 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_257 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_257 (yg_257 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨257, by omega⟩ : ℚ)) (εB := (cut ⟨258, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_257 yg_257 tg_257 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1428475908537 : ℚ) / 500000000000)) (((452242042329 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_258 : Fin 16 → ℕ := fun k => [17443, 179, 31, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_258 : Fin 16 → ℕ := fun k => [17509, 180, 35, 15, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_258 : Fin 16 → ℚ := fun k => [((8643585205686611 : ℚ) / 500000000000), ((162273537013919 : ℚ) / 1000000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_258 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨258, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨259, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨259, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨258, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_258 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_258 k + 1) (k.val + 1) < (cut ⟨259, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_258 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_258 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_258 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_258 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_258 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_258 ⟨1, by omega⟩ + 1 ≤ xg_258 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_258 k : ℝ) ≤ Chebyshev.theta ((xg_258 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2005
    · exact Work.RHContract.RegionI.thV_40
    · exact Work.RHContract.RegionI.thV_10
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((17509 : ℕ) : ℝ) ≤ (((71436666597 : ℚ) / 25000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2014
  have hSx : (((452242072027 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 17443, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2005
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_258 k := by decide +kernel
  have hT2 : (∑ k, tg_258 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_258 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_258 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((71436666597 : ℚ) / 25000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_258 k))
      + ((((452242072027 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_258 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_258 (yg_258 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨258, by omega⟩ : ℚ)) (εB := (cut ⟨259, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_258 yg_258 tg_258 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((71436666597 : ℚ) / 25000000000)) (((452242072027 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_259 : Fin 16 → ℕ := fun k => [17509, 179, 31, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_259 : Fin 16 → ℕ := fun k => [17599, 181, 36, 15, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_259 : Fin 16 → ℚ := fun k => [((17375090464699557 : ℚ) / 1000000000000), ((162273537013919 : ℚ) / 1000000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_259 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨259, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨260, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨260, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨259, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_259 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_259 k + 1) (k.val + 1) < (cut ⟨260, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_259 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_259 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_259 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_259 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_259 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_259 ⟨1, by omega⟩ + 1 ≤ xg_259 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_259 k : ℝ) ≤ Chebyshev.theta ((xg_259 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2014
    · exact Work.RHContract.RegionI.thV_40
    · exact Work.RHContract.RegionI.thV_10
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((17599 : ℕ) : ℝ) ≤ (((2857978990791 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2023
  have hSx : (((14132565671 : ℚ) / 31250000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 17509, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2014
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_259 k := by decide +kernel
  have hT2 : (∑ k, tg_259 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_259 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_259 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2857978990791 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_259 k))
      + ((((14132565671 : ℚ) / 31250000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_259 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_259 (yg_259 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨259, by omega⟩ : ℚ)) (εB := (cut ⟨260, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_259 yg_259 tg_259 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2857978990791 : ℚ) / 1000000000000)) (((14132565671 : ℚ) / 31250000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_260 : Fin 16 → ℕ := fun k => [17599, 181, 31, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_260 : Fin 16 → ℕ := fun k => [17707, 181, 36, 15, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_260 : Fin 16 → ℚ := fun k => [((2182881835000013 : ℚ) / 125000000000), ((33494406808673 : ℚ) / 200000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_260 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨260, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨261, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨261, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨260, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_260 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_260 k + 1) (k.val + 1) < (cut ⟨261, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_260 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_260 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_260 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_260 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_260 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_260 ⟨1, by omega⟩ + 1 ≤ xg_260 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_260 k : ℝ) ≤ Chebyshev.theta ((xg_260 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2023
    · exact Work.RHContract.RegionI.thV_41
    · exact Work.RHContract.RegionI.thV_10
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((17707 : ℕ) : ℝ) ≤ (((1429244356589 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2032
  have hSx : (((452242130631 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 17599, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2023
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_260 k := by decide +kernel
  have hT2 : (∑ k, tg_260 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_260 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_260 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1429244356589 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_260 k))
      + ((((452242130631 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_260 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_260 (yg_260 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨260, by omega⟩ : ℚ)) (εB := (cut ⟨261, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_260 yg_260 tg_260 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1429244356589 : ℚ) / 500000000000)) (((452242130631 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_261 : Fin 16 → ℕ := fun k => [17707, 181, 31, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_261 : Fin 16 → ℕ := fun k => [17791, 182, 36, 15, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_261 : Fin 16 → ℚ := fun k => [((8775532384123731 : ℚ) / 500000000000), ((33494406808673 : ℚ) / 200000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_261 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨261, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨262, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨262, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨261, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_261 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_261 k + 1) (k.val + 1) < (cut ⟨262, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_261 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_261 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_261 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_261 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_261 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_261 ⟨1, by omega⟩ + 1 ≤ xg_261 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_261 k : ℝ) ≤ Chebyshev.theta ((xg_261 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2032
    · exact Work.RHContract.RegionI.thV_41
    · exact Work.RHContract.RegionI.thV_10
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((17791 : ℕ) : ℝ) ≤ (((285899561533 : ℚ) / 100000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2041
  have hSx : (((226121079747 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 17707, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2032
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_261 k := by decide +kernel
  have hT2 : (∑ k, tg_261 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_261 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_261 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((285899561533 : ℚ) / 100000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_261 k))
      + ((((226121079747 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_261 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_261 (yg_261 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨261, by omega⟩ : ℚ)) (εB := (cut ⟨262, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_261 yg_261 tg_261 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((285899561533 : ℚ) / 100000000000)) (((226121079747 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_262 : Fin 16 → ℕ := fun k => [17791, 181, 31, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_262 : Fin 16 → ℕ := fun k => [17903, 182, 36, 15, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_262 : Fin 16 → ℚ := fun k => [((17639124785780057 : ℚ) / 1000000000000), ((33494406808673 : ℚ) / 200000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_262 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨262, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨263, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨263, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨262, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_262 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_262 k + 1) (k.val + 1) < (cut ⟨263, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_262 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_262 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_262 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_262 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_262 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_262 ⟨1, by omega⟩ + 1 ≤ xg_262 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_262 k : ℝ) ≤ Chebyshev.theta ((xg_262 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2041
    · exact Work.RHContract.RegionI.thV_41
    · exact Work.RHContract.RegionI.thV_10
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((17903 : ℕ) : ℝ) ≤ (((7148749197 : ℚ) / 2500000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2050
  have hSx : (((11306054701 : ℚ) / 25000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 17791, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2041
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_262 k := by decide +kernel
  have hT2 : (∑ k, tg_262 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_262 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_262 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((7148749197 : ℚ) / 2500000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_262 k))
      + ((((11306054701 : ℚ) / 25000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_262 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_262 (yg_262 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨262, by omega⟩ : ℚ)) (εB := (cut ⟨263, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_262 yg_262 tg_262 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((7148749197 : ℚ) / 2500000000)) (((11306054701 : ℚ) / 25000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_263 : Fin 16 → ℕ := fun k => [17903, 181, 31, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_263 : Fin 16 → ℕ := fun k => [17971, 183, 36, 15, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_263 : Fin 16 → ℚ := fun k => [((4431808836732919 : ℚ) / 250000000000), ((33494406808673 : ℚ) / 200000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_263 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨263, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨264, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨264, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨263, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_263 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_263 k + 1) (k.val + 1) < (cut ⟨264, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_263 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_263 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_263 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_263 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_263 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_263 ⟨1, by omega⟩ + 1 ≤ xg_263 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_263 k : ℝ) ≤ Chebyshev.theta ((xg_263 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2050
    · exact Work.RHContract.RegionI.thV_41
    · exact Work.RHContract.RegionI.thV_10
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((17971 : ℕ) : ℝ) ≤ (((2860001493151 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2059
  have hSx : (((90448443253 : ℚ) / 200000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 17903, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2050
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_263 k := by decide +kernel
  have hT2 : (∑ k, tg_263 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_263 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_263 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2860001493151 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_263 k))
      + ((((90448443253 : ℚ) / 200000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_263 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_263 (yg_263 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨263, by omega⟩ : ℚ)) (εB := (cut ⟨264, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_263 yg_263 tg_263 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2860001493151 : ℚ) / 1000000000000)) (((90448443253 : ℚ) / 200000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_264 : Fin 16 → ℕ := fun k => [17971, 181, 31, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_264 : Fin 16 → ℕ := fun k => [18049, 183, 36, 15, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_264 : Fin 16 → ℚ := fun k => [((17815386148220573 : ℚ) / 1000000000000), ((33494406808673 : ℚ) / 200000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_264 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨264, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨265, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨265, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨264, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_264 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_264 k + 1) (k.val + 1) < (cut ⟨265, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_264 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_264 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_264 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_264 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_264 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_264 ⟨1, by omega⟩ + 1 ≤ xg_264 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_264 k : ℝ) ≤ Chebyshev.theta ((xg_264 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2059
    · exact Work.RHContract.RegionI.thV_41
    · exact Work.RHContract.RegionI.thV_10
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((18049 : ℕ) : ℝ) ≤ (((2860501116673 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2068
  have hSx : (((226121122119 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 17971, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2059
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_264 k := by decide +kernel
  have hT2 : (∑ k, tg_264 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_264 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_264 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2860501116673 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_264 k))
      + ((((226121122119 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_264 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_264 (yg_264 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨264, by omega⟩ : ℚ)) (εB := (cut ⟨265, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_264 yg_264 tg_264 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2860501116673 : ℚ) / 1000000000000)) (((226121122119 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_265 : Fin 16 → ℕ := fun k => [18049, 181, 31, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_265 : Fin 16 → ℕ := fun k => [18131, 184, 36, 15, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_265 : Fin 16 → ℚ := fun k => [((1118973520778231 : ℚ) / 62500000000), ((33494406808673 : ℚ) / 200000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_265 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨265, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨266, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨266, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨265, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_265 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_265 k + 1) (k.val + 1) < (cut ⟨266, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_265 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_265 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_265 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_265 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_265 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_265 ⟨1, by omega⟩ + 1 ≤ xg_265 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_265 k : ℝ) ≤ Chebyshev.theta ((xg_265 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2068
    · exact Work.RHContract.RegionI.thV_41
    · exact Work.RHContract.RegionI.thV_10
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((18131 : ℕ) : ℝ) ≤ (((2860998427053 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2077
  have hSx : (((452242271967 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 18049, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2068
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_265 k := by decide +kernel
  have hT2 : (∑ k, tg_265 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_265 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_265 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2860998427053 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_265 k))
      + ((((452242271967 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_265 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_265 (yg_265 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨265, by omega⟩ : ℚ)) (εB := (cut ⟨266, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_265 yg_265 tg_265 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2860998427053 : ℚ) / 1000000000000)) (((452242271967 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_266 : Fin 16 → ℕ := fun k => [18131, 181, 31, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_266 : Fin 16 → ℕ := fun k => [18217, 184, 36, 15, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_266 : Fin 16 → ℚ := fun k => [((17991808277950187 : ℚ) / 1000000000000), ((33494406808673 : ℚ) / 200000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_266 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨266, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨267, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨267, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨266, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_266 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_266 k + 1) (k.val + 1) < (cut ⟨267, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_266 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_266 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_266 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_266 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_266 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_266 ⟨1, by omega⟩ + 1 ≤ xg_266 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_266 k : ℝ) ≤ Chebyshev.theta ((xg_266 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2077
    · exact Work.RHContract.RegionI.thV_41
    · exact Work.RHContract.RegionI.thV_10
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((18217 : ℕ) : ℝ) ≤ (((1117770927 : ℚ) / 390625000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2086
  have hSx : (((226121149721 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 18131, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2077
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_266 k := by decide +kernel
  have hT2 : (∑ k, tg_266 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_266 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_266 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1117770927 : ℚ) / 390625000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_266 k))
      + ((((226121149721 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_266 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_266 (yg_266 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨266, by omega⟩ : ℚ)) (εB := (cut ⟨267, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_266 yg_266 tg_266 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1117770927 : ℚ) / 390625000)) (((226121149721 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_267 : Fin 16 → ℕ := fun k => [18217, 181, 31, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_267 : Fin 16 → ℕ := fun k => [18289, 184, 36, 15, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_267 : Fin 16 → ℚ := fun k => [((18080079477767921 : ℚ) / 1000000000000), ((33494406808673 : ℚ) / 200000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_267 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨267, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨268, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨268, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨267, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_267 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_267 k + 1) (k.val + 1) < (cut ⟨268, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_267 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_267 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_267 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_267 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_267 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_267 ⟨1, by omega⟩ + 1 ≤ xg_267 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_267 k : ℝ) ≤ Chebyshev.theta ((xg_267 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2086
    · exact Work.RHContract.RegionI.thV_41
    · exact Work.RHContract.RegionI.thV_10
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((18289 : ℕ) : ℝ) ≤ (((1430993307499 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2095
  have hSx : (((452242326677 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 18217, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2086
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_267 k := by decide +kernel
  have hT2 : (∑ k, tg_267 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_267 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_267 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1430993307499 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_267 k))
      + ((((452242326677 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_267 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_267 (yg_267 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨267, by omega⟩ : ℚ)) (εB := (cut ⟨268, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_267 yg_267 tg_267 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1430993307499 : ℚ) / 500000000000)) (((452242326677 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_268 : Fin 16 → ℕ := fun k => [18289, 181, 31, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_268 : Fin 16 → ℕ := fun k => [18371, 185, 36, 15, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_268 : Fin 16 → ℚ := fun k => [((18168389000386843 : ℚ) / 1000000000000), ((33494406808673 : ℚ) / 200000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_268 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨268, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨269, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨269, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨268, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_268 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_268 k + 1) (k.val + 1) < (cut ⟨269, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_268 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_268 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_268 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_268 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_268 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_268 ⟨1, by omega⟩ + 1 ≤ xg_268 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_268 k : ℝ) ≤ Chebyshev.theta ((xg_268 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2095
    · exact Work.RHContract.RegionI.thV_41
    · exact Work.RHContract.RegionI.thV_10
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((18371 : ℕ) : ℝ) ≤ (((286247755923 : ℚ) / 100000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2104
  have hSx : (((452242353683 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 18289, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2095
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_268 k := by decide +kernel
  have hT2 : (∑ k, tg_268 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_268 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_268 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((286247755923 : ℚ) / 100000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_268 k))
      + ((((452242353683 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_268 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_268 (yg_268 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨268, by omega⟩ : ℚ)) (εB := (cut ⟨269, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_268 yg_268 tg_268 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((286247755923 : ℚ) / 100000000000)) (((452242353683 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_269 : Fin 16 → ℕ := fun k => [18371, 181, 31, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_269 : Fin 16 → ℕ := fun k => [18451, 185, 36, 15, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_269 : Fin 16 → ℚ := fun k => [((18256736895686083 : ℚ) / 1000000000000), ((33494406808673 : ℚ) / 200000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_269 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨269, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨270, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (16 + 1) < (cut ⟨270, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨269, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_269 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 16, Work.RHContract.RegionI.Fhi (yg_269 k + 1) (k.val + 1) < (cut ⟨270, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_269 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_269 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 16, yg_269 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 16, 1 ≤ yg_269 k := by decide +kernel
  have hposy : ∀ k : Fin 16, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_269 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_269 ⟨1, by omega⟩ + 1 ≤ xg_269 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_269 k : ℝ) ≤ Chebyshev.theta ((xg_269 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2104
    · exact Work.RHContract.RegionI.thV_41
    · exact Work.RHContract.RegionI.thV_10
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((18451 : ℕ) : ℝ) ≤ (((1431483081877 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2113
  have hSx : (((452242380457 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 18371, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2104
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_269 k := by decide +kernel
  have hT2 : (∑ k, tg_269 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_269 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_269 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1431483081877 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_269 k))
      + ((((452242380457 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_269 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_269 (yg_269 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨269, by omega⟩ : ℚ)) (εB := (cut ⟨270, by omega⟩ : ℚ)) hhi hlo
    16 16 (by norm_num) (by norm_num) hKtop xg_269 yg_269 tg_269 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1431483081877 : ℚ) / 500000000000)) (((452242380457 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_270 : Fin 16 → ℕ := fun k => [18451, 181, 31, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_270 : Fin 17 → ℕ := fun k => [18539, 186, 36, 15, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_270 : Fin 16 → ℚ := fun k => [((1834512778239619 : ℚ) / 100000000000), ((33494406808673 : ℚ) / 200000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_270 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨270, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨271, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨271, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 16, (cut ⟨270, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_270 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_270 k + 1) (k.val + 1) < (cut ⟨271, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 16, 2 ≤ xg_270 k := by decide +kernel
  have hxhi : ∀ k : Fin 16, xg_270 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_270 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_270 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_270 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_270 ⟨1, by omega⟩ + 1 ≤ xg_270 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 16, (tg_270 k : ℝ) ≤ Chebyshev.theta ((xg_270 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2113
    · exact Work.RHContract.RegionI.thV_41
    · exact Work.RHContract.RegionI.thV_10
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((18539 : ℕ) : ℝ) ≤ (((2863452679041 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2122
  have hSx : (((226121203489 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 18451, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2113
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_270 k := by decide +kernel
  have hT2 : (∑ k, tg_270 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_270 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_270 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2863452679041 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_270 k))
      + ((((226121203489 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_270 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_270 (yg_270 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨270, by omega⟩ : ℚ)) (εB := (cut ⟨271, by omega⟩ : ℚ)) hhi hlo
    16 17 (by norm_num) (by norm_num) hKtop xg_270 yg_270 tg_270 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2863452679041 : ℚ) / 1000000000000)) (((226121203489 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_271 : Fin 17 → ℕ := fun k => [18539, 181, 31, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_271 : Fin 17 → ℕ := fun k => [18671, 186, 36, 15, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_271 : Fin 17 → ℚ := fun k => [((18433557236592779 : ℚ) / 1000000000000), ((33494406808673 : ℚ) / 200000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_271 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨271, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨272, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨272, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨271, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_271 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_271 k + 1) (k.val + 1) < (cut ⟨272, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_271 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_271 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_271 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_271 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_271 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_271 ⟨1, by omega⟩ + 1 ≤ xg_271 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_271 k : ℝ) ≤ Chebyshev.theta ((xg_271 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2122
    · exact Work.RHContract.RegionI.thV_41
    · exact Work.RHContract.RegionI.thV_10
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((18671 : ℕ) : ℝ) ≤ (((2863936441303 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2131
  have hSx : (((56530304159 : ℚ) / 125000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 18539, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2122
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_271 k := by decide +kernel
  have hT2 : (∑ k, tg_271 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_271 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_271 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2863936441303 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_271 k))
      + ((((56530304159 : ℚ) / 125000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_271 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_271 (yg_271 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨271, by omega⟩ : ℚ)) (εB := (cut ⟨272, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_271 yg_271 tg_271 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2863936441303 : ℚ) / 1000000000000)) (((56530304159 : ℚ) / 125000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_272 : Fin 17 → ℕ := fun k => [18671, 181, 31, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_272 : Fin 17 → ℕ := fun k => [18757, 187, 36, 15, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_272 : Fin 17 → ℚ := fun k => [((231525472201577 : ℚ) / 12500000000), ((33494406808673 : ℚ) / 200000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_272 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨272, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨273, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨273, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨272, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_272 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_272 k + 1) (k.val + 1) < (cut ⟨273, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_272 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_272 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_272 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_272 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_272 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_272 ⟨1, by omega⟩ + 1 ≤ xg_272 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_272 k : ℝ) ≤ Chebyshev.theta ((xg_272 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2131
    · exact Work.RHContract.RegionI.thV_41
    · exact Work.RHContract.RegionI.thV_10
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((18757 : ℕ) : ℝ) ≤ (((1432208607851 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2140
  have hSx : (((452242459269 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 18671, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2131
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_272 k := by decide +kernel
  have hT2 : (∑ k, tg_272 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_272 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_272 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1432208607851 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_272 k))
      + ((((452242459269 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_272 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_272 (yg_272 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨272, by omega⟩ : ℚ)) (εB := (cut ⟨273, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_272 yg_272 tg_272 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1432208607851 : ℚ) / 500000000000)) (((452242459269 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_273 : Fin 17 → ℕ := fun k => [18757, 181, 31, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_273 : Fin 17 → ℕ := fun k => [18899, 188, 36, 15, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_273 : Fin 17 → ℚ := fun k => [((9305287028917057 : ℚ) / 500000000000), ((33494406808673 : ℚ) / 200000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_273 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨273, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨274, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨274, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨273, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_273 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_273 k + 1) (k.val + 1) < (cut ⟨274, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_273 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_273 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_273 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_273 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_273 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_273 ⟨1, by omega⟩ + 1 ≤ xg_273 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_273 k : ℝ) ≤ Chebyshev.theta ((xg_273 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2140
    · exact Work.RHContract.RegionI.thV_41
    · exact Work.RHContract.RegionI.thV_10
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((18899 : ℕ) : ℝ) ≤ (((1432447667631 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2149
  have hSx : (((226121242473 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 18757, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2140
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_273 k := by decide +kernel
  have hT2 : (∑ k, tg_273 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_273 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_273 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1432447667631 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_273 k))
      + ((((226121242473 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_273 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_273 (yg_273 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨273, by omega⟩ : ℚ)) (εB := (cut ⟨274, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_273 yg_273 tg_273 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1432447667631 : ℚ) / 500000000000)) (((226121242473 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_274 : Fin 17 → ℕ := fun k => [18899, 181, 31, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_274 : Fin 17 → ℕ := fun k => [19001, 188, 36, 15, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_274 : Fin 17 → ℚ := fun k => [((18699160187112239 : ℚ) / 1000000000000), ((33494406808673 : ℚ) / 200000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_274 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨274, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨275, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨275, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨274, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_274 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_274 k + 1) (k.val + 1) < (cut ⟨275, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_274 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_274 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_274 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_274 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_274 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_274 ⟨1, by omega⟩ + 1 ≤ xg_274 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_274 k : ℝ) ≤ Chebyshev.theta ((xg_274 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2149
    · exact Work.RHContract.RegionI.thV_41
    · exact Work.RHContract.RegionI.thV_10
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((19001 : ℕ) : ℝ) ≤ (((179085648093 : ℚ) / 62500000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2158
  have hSx : (((22612125517 : ℚ) / 50000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 18899, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2149
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_274 k := by decide +kernel
  have hT2 : (∑ k, tg_274 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_274 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_274 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((179085648093 : ℚ) / 62500000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_274 k))
      + ((((22612125517 : ℚ) / 50000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_274 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_274 (yg_274 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨274, by omega⟩ : ℚ)) (εB := (cut ⟨275, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_274 yg_274 tg_274 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((179085648093 : ℚ) / 62500000000)) (((22612125517 : ℚ) / 50000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_275 : Fin 17 → ℕ := fun k => [19001, 181, 31, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_275 : Fin 17 → ℕ := fun k => [19081, 188, 37, 15, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_275 : Fin 17 → ℚ := fun k => [((4696951142889307 : ℚ) / 250000000000), ((33494406808673 : ℚ) / 200000000000), ((13012190863139 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_275 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨275, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨276, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨276, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨275, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_275 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_275 k + 1) (k.val + 1) < (cut ⟨276, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_275 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_275 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_275 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_275 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_275 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_275 ⟨1, by omega⟩ + 1 ≤ xg_275 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_275 k : ℝ) ≤ Chebyshev.theta ((xg_275 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2158
    · exact Work.RHContract.RegionI.thV_41
    · exact Work.RHContract.RegionI.thV_10
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((19081 : ℕ) : ℝ) ≤ (((573168568607 : ℚ) / 200000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2167
  have hSx : (((452242535407 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 19001, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2158
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_275 k := by decide +kernel
  have hT2 : (∑ k, tg_275 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_275 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_275 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((573168568607 : ℚ) / 200000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_275 k))
      + ((((452242535407 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_275 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_275 (yg_275 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨275, by omega⟩ : ℚ)) (εB := (cut ⟨276, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_275 yg_275 tg_275 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((573168568607 : ℚ) / 200000000000)) (((452242535407 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_276 : Fin 17 → ℕ := fun k => [19081, 181, 37, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_276 : Fin 17 → ℕ := fun k => [19207, 189, 37, 15, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_276 : Fin 17 → ℚ := fun k => [((9438248798424947 : ℚ) / 500000000000), ((33494406808673 : ℚ) / 200000000000), ((14817649818811 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_276 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨276, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨277, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨277, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨276, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_276 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_276 k + 1) (k.val + 1) < (cut ⟨277, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_276 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_276 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_276 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_276 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_276 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_276 ⟨1, by omega⟩ + 1 ≤ xg_276 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_276 k : ℝ) ≤ Chebyshev.theta ((xg_276 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2167
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((19207 : ℕ) : ℝ) ≤ (((2866312751617 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2176
  have hSx : (((226121280103 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 19081, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2167
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_276 k := by decide +kernel
  have hT2 : (∑ k, tg_276 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_276 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_276 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2866312751617 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_276 k))
      + ((((226121280103 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_276 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_276 (yg_276 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨276, by omega⟩ : ℚ)) (εB := (cut ⟨277, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_276 yg_276 tg_276 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2866312751617 : ℚ) / 1000000000000)) (((226121280103 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_277 : Fin 17 → ℕ := fun k => [19207, 181, 37, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_277 : Fin 17 → ℕ := fun k => [19273, 189, 37, 15, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_277 : Fin 17 → ℚ := fun k => [((18965239618772239 : ℚ) / 1000000000000), ((33494406808673 : ℚ) / 200000000000), ((14817649818811 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_277 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨277, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨278, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨278, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨277, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_277 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_277 k + 1) (k.val + 1) < (cut ⟨278, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_277 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_277 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_277 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_277 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_277 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_277 ⟨1, by omega⟩ + 1 ≤ xg_277 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_277 k : ℝ) ≤ Chebyshev.theta ((xg_277 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2176
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((19273 : ℕ) : ℝ) ≤ (((17917378391 : ℚ) / 6250000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2185
  have hSx : (((90448516947 : ℚ) / 200000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 19207, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2176
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_277 k := by decide +kernel
  have hT2 : (∑ k, tg_277 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_277 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_277 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((17917378391 : ℚ) / 6250000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_277 k))
      + ((((90448516947 : ℚ) / 200000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_277 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_277 (yg_277 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨277, by omega⟩ : ℚ)) (εB := (cut ⟨278, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_277 yg_277 tg_277 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((17917378391 : ℚ) / 6250000000)) (((90448516947 : ℚ) / 200000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_278 : Fin 17 → ℕ := fun k => [19273, 181, 37, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_278 : Fin 17 → ℕ := fun k => [19387, 190, 37, 15, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_278 : Fin 17 → ℚ := fun k => [((19054022281392411 : ℚ) / 1000000000000), ((33494406808673 : ℚ) / 200000000000), ((14817649818811 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_278 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨278, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨279, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨279, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨278, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_278 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_278 k + 1) (k.val + 1) < (cut ⟨279, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_278 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_278 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_278 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_278 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_278 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_278 ⟨1, by omega⟩ + 1 ≤ xg_278 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_278 k : ℝ) ≤ Chebyshev.theta ((xg_278 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2185
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((19387 : ℕ) : ℝ) ≤ (((716811470907 : ℚ) / 250000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2194
  have hSx : (((113060652261 : ℚ) / 250000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 19273, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2185
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_278 k := by decide +kernel
  have hT2 : (∑ k, tg_278 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_278 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_278 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((716811470907 : ℚ) / 250000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_278 k))
      + ((((113060652261 : ℚ) / 250000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_278 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_278 (yg_278 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨278, by omega⟩ : ℚ)) (εB := (cut ⟨279, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_278 yg_278 tg_278 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((716811470907 : ℚ) / 250000000000)) (((113060652261 : ℚ) / 250000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_279 : Fin 17 → ℕ := fun k => [19387, 181, 37, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_279 : Fin 17 → ℕ := fun k => [19441, 190, 37, 15, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_279 : Fin 17 → ℚ := fun k => [((19142852210912921 : ℚ) / 1000000000000), ((33494406808673 : ℚ) / 200000000000), ((14817649818811 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_279 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨279, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨280, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨280, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨279, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_279 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_279 k + 1) (k.val + 1) < (cut ⟨280, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_279 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_279 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_279 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_279 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_279 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_279 ⟨1, by omega⟩ + 1 ≤ xg_279 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_279 k : ℝ) ≤ Chebyshev.theta ((xg_279 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2194
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((19441 : ℕ) : ℝ) ≤ (((1433854661159 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2203
  have hSx : (((452242633099 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 19387, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2194
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_279 k := by decide +kernel
  have hT2 : (∑ k, tg_279 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_279 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_279 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1433854661159 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_279 k))
      + ((((452242633099 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_279 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_279 (yg_279 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨279, by omega⟩ : ℚ)) (εB := (cut ⟨280, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_279 yg_279 tg_279 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1433854661159 : ℚ) / 500000000000)) (((452242633099 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

end

end Work.RHContract.A.RegionI
