import Mathlib
import Submission.Work.RHContract.A.RegionI.Core
import Submission.Work.RHContract.A.RegionI.blockCert
import Submission.Work.RHContract.A.RegionI.Data11
import Submission.Work.RHContract.A.RegionI.Cuts

/-!  Region I: group certificates.  GENERATED FILE. -/

open scoped BigOperators

namespace Work.RHContract.A.RegionI

noncomputable section

private def xg_320 : Fin 17 → ℕ := fun k => [23291, 199, 37, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_320 : Fin 17 → ℕ := fun k => [23371, 209, 39, 16, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_320 : Fin 17 → ℚ := fun k => [((23139191360152919 : ℚ) / 1000000000000), ((188563506206499 : ℚ) / 1000000000000), ((14817649818811 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_320 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨320, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨321, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨321, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨320, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_320 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_320 k + 1) (k.val + 1) < (cut ⟨321, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_320 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_320 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_320 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_320 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_320 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_320 ⟨1, by omega⟩ + 1 ≤ xg_320 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_320 k : ℝ) ≤ Chebyshev.theta ((xg_320 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2595
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((23371 : ℕ) : ℝ) ≤ (((1443269047811 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2605
  have hSx : (((113060880689 : ℚ) / 250000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 23291, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2595
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_320 k := by decide +kernel
  have hT2 : (∑ k, tg_320 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_320 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_320 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1443269047811 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_320 k))
      + ((((113060880689 : ℚ) / 250000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_320 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_320 (yg_320 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨320, by omega⟩ : ℚ)) (εB := (cut ⟨321, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_320 yg_320 tg_320 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1443269047811 : ℚ) / 500000000000)) (((113060880689 : ℚ) / 250000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_321 : Fin 17 → ℕ := fun k => [23371, 199, 37, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_321 : Fin 17 → ℕ := fun k => [23537, 210, 39, 16, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_321 : Fin 17 → ℚ := fun k => [((11619883539470393 : ℚ) / 500000000000), ((188563506206499 : ℚ) / 1000000000000), ((14817649818811 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_321 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨321, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨322, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨322, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨321, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_321 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_321 k + 1) (k.val + 1) < (cut ⟨322, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_321 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_321 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_321 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_321 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_321 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_321 ⟨1, by omega⟩ + 1 ≤ xg_321 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_321 k : ℝ) ≤ Chebyshev.theta ((xg_321 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2605
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((23537 : ℕ) : ℝ) ≤ (((2886964182131 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2615
  have hSx : (((452243541121 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 23371, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2605
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_321 k := by decide +kernel
  have hT2 : (∑ k, tg_321 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_321 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_321 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2886964182131 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_321 k))
      + ((((452243541121 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_321 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_321 (yg_321 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨321, by omega⟩ : ℚ)) (εB := (cut ⟨322, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_321 yg_321 tg_321 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2886964182131 : ℚ) / 1000000000000)) (((452243541121 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_322 : Fin 17 → ℕ := fun k => [23537, 199, 37, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_322 : Fin 17 → ℕ := fun k => [23603, 210, 39, 16, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_322 : Fin 17 → ℚ := fun k => [((11670200921597321 : ℚ) / 500000000000), ((188563506206499 : ℚ) / 1000000000000), ((14817649818811 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_322 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨322, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨323, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨323, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨322, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_322 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_322 k + 1) (k.val + 1) < (cut ⟨323, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_322 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_322 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_322 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_322 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_322 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_322 ⟨1, by omega⟩ + 1 ≤ xg_322 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_322 k : ℝ) ≤ Chebyshev.theta ((xg_322 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2615
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((23603 : ℕ) : ℝ) ≤ (((2887388437999 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2625
  have hSx : (((452243559271 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 23537, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2615
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_322 k := by decide +kernel
  have hT2 : (∑ k, tg_322 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_322 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_322 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2887388437999 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_322 k))
      + ((((452243559271 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_322 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_322 (yg_322 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨322, by omega⟩ : ℚ)) (εB := (cut ⟨323, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_322 yg_322 tg_322 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2887388437999 : ℚ) / 1000000000000)) (((452243559271 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_323 : Fin 17 → ℕ := fun k => [23603, 199, 37, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_323 : Fin 17 → ℕ := fun k => [23687, 210, 39, 16, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_323 : Fin 17 → ℚ := fun k => [((5860269912094759 : ℚ) / 250000000000), ((188563506206499 : ℚ) / 1000000000000), ((14817649818811 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_323 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨323, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨324, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨324, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨323, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_323 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_323 k + 1) (k.val + 1) < (cut ⟨324, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_323 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_323 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_323 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_323 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_323 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_323 ⟨1, by omega⟩ + 1 ≤ xg_323 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_323 k : ℝ) ≤ Chebyshev.theta ((xg_323 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2625
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((23687 : ℕ) : ℝ) ≤ (((2887811301891 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2635
  have hSx : (((226121788633 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 23603, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2625
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_323 k := by decide +kernel
  have hT2 : (∑ k, tg_323 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_323 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_323 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2887811301891 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_323 k))
      + ((((226121788633 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_323 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_323 (yg_323 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨323, by omega⟩ : ℚ)) (εB := (cut ⟨324, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_323 yg_323 tg_323 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2887811301891 : ℚ) / 1000000000000)) (((226121788633 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_324 : Fin 17 → ℕ := fun k => [23687, 199, 37, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_324 : Fin 17 → ℕ := fun k => [23773, 211, 39, 16, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_324 : Fin 17 → ℚ := fun k => [((5885447579714559 : ℚ) / 250000000000), ((188563506206499 : ℚ) / 1000000000000), ((14817649818811 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_324 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨324, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨325, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨325, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨324, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_324 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_324 k + 1) (k.val + 1) < (cut ⟨325, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_324 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_324 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_324 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_324 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_324 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_324 ⟨1, by omega⟩ + 1 ≤ xg_324 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_324 k : ℝ) ≤ Chebyshev.theta ((xg_324 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2635
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((23773 : ℕ) : ℝ) ≤ (((2888190358731 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2644
  have hSx : (((226121797571 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 23687, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2635
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_324 k := by decide +kernel
  have hT2 : (∑ k, tg_324 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_324 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_324 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2888190358731 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_324 k))
      + ((((226121797571 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_324 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_324 (yg_324 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨324, by omega⟩ : ℚ)) (εB := (cut ⟨325, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_324 yg_324 tg_324 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2888190358731 : ℚ) / 1000000000000)) (((226121797571 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_325 : Fin 17 → ℕ := fun k => [23773, 211, 37, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_325 : Fin 17 → ℕ := fun k => [23873, 211, 39, 16, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_325 : Fin 17 → ℚ := fun k => [((23632465953990879 : ℚ) / 1000000000000), ((38783072867631 : ℚ) / 200000000000), ((14817649818811 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_325 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨325, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨326, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨326, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨325, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_325 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_325 k + 1) (k.val + 1) < (cut ⟨326, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_325 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_325 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_325 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_325 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_325 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_325 ⟨1, by omega⟩ + 1 ≤ xg_325 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_325 k : ℝ) ≤ Chebyshev.theta ((xg_325 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2644
    · exact Work.RHContract.RegionI.thV_46
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((23873 : ℕ) : ℝ) ≤ (((2888609986041 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2654
  have hSx : (((226121805551 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 23773, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2644
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_325 k := by decide +kernel
  have hT2 : (∑ k, tg_325 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_325 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_325 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2888609986041 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_325 k))
      + ((((226121805551 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_325 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_325 (yg_325 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨325, by omega⟩ : ℚ)) (εB := (cut ⟨326, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_325 yg_325 tg_325 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2888609986041 : ℚ) / 1000000000000)) (((226121805551 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_326 : Fin 17 → ℕ := fun k => [23873, 211, 37, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_326 : Fin 17 → ℕ := fun k => [23971, 211, 39, 16, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_326 : Fin 17 → ℚ := fun k => [((1483328341063523 : ℚ) / 62500000000), ((38783072867631 : ℚ) / 200000000000), ((14817649818811 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_326 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨326, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨327, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨327, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨326, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_326 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_326 k + 1) (k.val + 1) < (cut ⟨327, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_326 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_326 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_326 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_326 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_326 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_326 ⟨1, by omega⟩ + 1 ≤ xg_326 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_326 k : ℝ) ≤ Chebyshev.theta ((xg_326 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2654
    · exact Work.RHContract.RegionI.thV_46
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((23971 : ℕ) : ℝ) ≤ (((72225703487 : ℚ) / 25000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2664
  have hSx : (((90448725741 : ℚ) / 200000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 23873, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2654
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_326 k := by decide +kernel
  have hT2 : (∑ k, tg_326 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_326 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_326 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((72225703487 : ℚ) / 25000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_326 k))
      + ((((90448725741 : ℚ) / 200000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_326 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_326 (yg_326 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨326, by omega⟩ : ℚ)) (εB := (cut ⟨327, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_326 yg_326 tg_326 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((72225703487 : ℚ) / 25000000000)) (((90448725741 : ℚ) / 200000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_327 : Fin 17 → ℕ := fun k => [23971, 211, 37, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_327 : Fin 17 → ℕ := fun k => [24049, 212, 40, 16, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_327 : Fin 17 → ℚ := fun k => [((595851903630133 : ℚ) / 25000000000), ((38783072867631 : ℚ) / 200000000000), ((14817649818811 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_327 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨327, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨328, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨328, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨327, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_327 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_327 k + 1) (k.val + 1) < (cut ⟨328, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_327 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_327 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_327 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_327 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_327 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_327 ⟨1, by omega⟩ + 1 ≤ xg_327 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_327 k : ℝ) ≤ Chebyshev.theta ((xg_327 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2664
    · exact Work.RHContract.RegionI.thV_46
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((24049 : ℕ) : ℝ) ≤ (((2889444603523 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2674
  have hSx : (((90448729237 : ℚ) / 200000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 23971, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2664
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_327 k := by decide +kernel
  have hT2 : (∑ k, tg_327 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_327 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_327 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2889444603523 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_327 k))
      + ((((90448729237 : ℚ) / 200000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_327 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_327 (yg_327 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨327, by omega⟩ : ℚ)) (εB := (cut ⟨328, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_327 yg_327 tg_327 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2889444603523 : ℚ) / 1000000000000)) (((90448729237 : ℚ) / 200000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_328 : Fin 17 → ℕ := fun k => [24049, 211, 37, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_328 : Fin 17 → ℕ := fun k => [24113, 212, 40, 16, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_328 : Fin 17 → ℚ := fun k => [((1495933707096909 : ℚ) / 62500000000), ((38783072867631 : ℚ) / 200000000000), ((14817649818811 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_328 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨328, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨329, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨329, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨328, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_328 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_328 k + 1) (k.val + 1) < (cut ⟨329, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_328 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_328 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_328 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_328 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_328 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_328 ⟨1, by omega⟩ + 1 ≤ xg_328 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_328 k : ℝ) ≤ Chebyshev.theta ((xg_328 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2674
    · exact Work.RHContract.RegionI.thV_46
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((24113 : ℕ) : ℝ) ≤ (((361232462709 : ℚ) / 125000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2684
  have hSx : (((452243663523 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 24049, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2674
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_328 k := by decide +kernel
  have hT2 : (∑ k, tg_328 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_328 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_328 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((361232462709 : ℚ) / 125000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_328 k))
      + ((((452243663523 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_328 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_328 (yg_328 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨328, by omega⟩ : ℚ)) (εB := (cut ⟨329, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_328 yg_328 tg_328 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((361232462709 : ℚ) / 125000000000)) (((452243663523 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_329 : Fin 17 → ℕ := fun k => [24113, 211, 37, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_329 : Fin 17 → ℕ := fun k => [24223, 213, 40, 16, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_329 : Fin 17 → ℚ := fun k => [((2403583533017413 : ℚ) / 100000000000), ((38783072867631 : ℚ) / 200000000000), ((14817649818811 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_329 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨329, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨330, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨330, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨329, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_329 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_329 k + 1) (k.val + 1) < (cut ⟨330, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_329 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_329 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_329 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_329 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_329 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_329 ⟨1, by omega⟩ + 1 ≤ xg_329 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_329 k : ℝ) ≤ Chebyshev.theta ((xg_329 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2684
    · exact Work.RHContract.RegionI.thV_46
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((24223 : ℕ) : ℝ) ≤ (((578054691451 : ℚ) / 200000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2694
  have hSx : (((452243680749 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 24113, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2684
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_329 k := by decide +kernel
  have hT2 : (∑ k, tg_329 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_329 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_329 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((578054691451 : ℚ) / 200000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_329 k))
      + ((((452243680749 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_329 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_329 (yg_329 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨329, by omega⟩ : ℚ)) (εB := (cut ⟨330, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_329 yg_329 tg_329 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((578054691451 : ℚ) / 200000000000)) (((452243680749 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_330 : Fin 17 → ℕ := fun k => [24223, 211, 37, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_330 : Fin 17 → ℕ := fun k => [24371, 213, 40, 16, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_330 : Fin 17 → ℚ := fun k => [((4827352749606259 : ℚ) / 200000000000), ((38783072867631 : ℚ) / 200000000000), ((14817649818811 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_330 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨330, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨331, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨331, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨330, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_330 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_330 k + 1) (k.val + 1) < (cut ⟨331, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_330 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_330 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_330 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_330 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_330 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_330 ⟨1, by omega⟩ + 1 ≤ xg_330 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_330 k : ℝ) ≤ Chebyshev.theta ((xg_330 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2694
    · exact Work.RHContract.RegionI.thV_46
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((24371 : ℕ) : ℝ) ≤ (((1445342528937 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2704
  have hSx : (((452243697863 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 24223, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2694
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_330 k := by decide +kernel
  have hT2 : (∑ k, tg_330 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_330 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_330 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1445342528937 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_330 k))
      + ((((452243697863 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_330 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_330 (yg_330 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨330, by omega⟩ : ℚ)) (εB := (cut ⟨331, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_330 yg_330 tg_330 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1445342528937 : ℚ) / 500000000000)) (((452243697863 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_331 : Fin 17 → ℕ := fun k => [24371, 211, 37, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_331 : Fin 17 → ℕ := fun k => [24469, 214, 40, 16, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_331 : Fin 17 → ℚ := fun k => [((969509775868959 : ℚ) / 40000000000), ((38783072867631 : ℚ) / 200000000000), ((14817649818811 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_331 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨331, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨332, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨332, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨331, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_331 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_331 k + 1) (k.val + 1) < (cut ⟨332, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_331 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_331 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_331 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_331 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_331 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_331 ⟨1, by omega⟩ + 1 ≤ xg_331 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_331 k : ℝ) ≤ Chebyshev.theta ((xg_331 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2704
    · exact Work.RHContract.RegionI.thV_46
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((24469 : ℕ) : ℝ) ≤ (((2891094644381 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2714
  have hSx : (((1130609287 : ℚ) / 2500000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 24371, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2704
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_331 k := by decide +kernel
  have hT2 : (∑ k, tg_331 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_331 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_331 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2891094644381 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_331 k))
      + ((((1130609287 : ℚ) / 2500000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_331 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_331 (yg_331 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨331, by omega⟩ : ℚ)) (εB := (cut ⟨332, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_331 yg_331 tg_331 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2891094644381 : ℚ) / 1000000000000)) (((1130609287 : ℚ) / 2500000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_332 : Fin 17 → ℕ := fun k => [24469, 211, 37, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_332 : Fin 17 → ℕ := fun k => [24571, 214, 40, 16, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_332 : Fin 17 → ℚ := fun k => [((608469352088759 : ℚ) / 25000000000), ((38783072867631 : ℚ) / 200000000000), ((14817649818811 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_332 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨332, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨333, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨333, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨332, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_332 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_332 k + 1) (k.val + 1) < (cut ⟨333, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_332 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_332 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_332 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_332 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_332 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_332 ⟨1, by omega⟩ + 1 ≤ xg_332 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_332 k : ℝ) ≤ Chebyshev.theta ((xg_332 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2714
    · exact Work.RHContract.RegionI.thV_46
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((24571 : ℕ) : ℝ) ≤ (((578300494067 : ℚ) / 200000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2724
  have hSx : (((45224373157 : ℚ) / 100000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 24469, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2714
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_332 k := by decide +kernel
  have hT2 : (∑ k, tg_332 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_332 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_332 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((578300494067 : ℚ) / 200000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_332 k))
      + ((((45224373157 : ℚ) / 100000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_332 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_332 (yg_332 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨332, by omega⟩ : ℚ)) (εB := (cut ⟨333, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_332 yg_332 tg_332 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((578300494067 : ℚ) / 200000000000)) (((45224373157 : ℚ) / 100000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_333 : Fin 17 → ℕ := fun k => [24571, 211, 37, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_333 : Fin 17 → ℕ := fun k => [24697, 215, 40, 16, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_333 : Fin 17 → ℚ := fun k => [((2443984684635233 : ℚ) / 100000000000), ((38783072867631 : ℚ) / 200000000000), ((14817649818811 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_333 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨333, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨334, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨334, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨333, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_333 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_333 k + 1) (k.val + 1) < (cut ⟨334, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_333 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_333 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_333 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_333 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_333 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_333 ⟨1, by omega⟩ + 1 ≤ xg_333 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_333 k : ℝ) ≤ Chebyshev.theta ((xg_333 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2724
    · exact Work.RHContract.RegionI.thV_46
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((24697 : ℕ) : ℝ) ≤ (((2891908099641 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2734
  have hSx : (((452243748197 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 24571, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2724
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_333 k := by decide +kernel
  have hT2 : (∑ k, tg_333 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_333 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_333 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2891908099641 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_333 k))
      + ((((452243748197 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_333 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_333 (yg_333 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨333, by omega⟩ : ℚ)) (εB := (cut ⟨334, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_333 yg_333 tg_333 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2891908099641 : ℚ) / 1000000000000)) (((452243748197 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_334 : Fin 17 → ℕ := fun k => [24697, 211, 37, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_334 : Fin 17 → ℕ := fun k => [24821, 215, 40, 16, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_334 : Fin 17 → ℚ := fun k => [((24540973618607533 : ℚ) / 1000000000000), ((38783072867631 : ℚ) / 200000000000), ((14817649818811 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_334 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨334, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨335, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨335, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨334, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_334 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_334 k + 1) (k.val + 1) < (cut ⟨335, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_334 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_334 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_334 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_334 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_334 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_334 ⟨1, by omega⟩ + 1 ≤ xg_334 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_334 k : ℝ) ≤ Chebyshev.theta ((xg_334 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2734
    · exact Work.RHContract.RegionI.thV_46
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((24821 : ℕ) : ℝ) ≤ (((1446155891793 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2744
  have hSx : (((90448752929 : ℚ) / 200000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 24697, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2734
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_334 k := by decide +kernel
  have hT2 : (∑ k, tg_334 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_334 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_334 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1446155891793 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_334 k))
      + ((((90448752929 : ℚ) / 200000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_334 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_334 (yg_334 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨334, by omega⟩ : ℚ)) (εB := (cut ⟨335, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_334 yg_334 tg_334 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1446155891793 : ℚ) / 500000000000)) (((90448752929 : ℚ) / 200000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_335 : Fin 17 → ℕ := fun k => [24821, 211, 37, 13, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_335 : Fin 17 → ℕ := fun k => [24923, 216, 40, 17, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_335 : Fin 17 → ℚ := fun k => [((12321074231789953 : ℚ) / 500000000000), ((38783072867631 : ℚ) / 200000000000), ((14817649818811 : ℚ) / 500000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_335 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨335, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨336, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨336, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨335, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_335 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_335 k + 1) (k.val + 1) < (cut ⟨336, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_335 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_335 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_335 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_335 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_335 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_335 ⟨1, by omega⟩ + 1 ≤ xg_335 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_335 k : ℝ) ≤ Chebyshev.theta ((xg_335 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2744
    · exact Work.RHContract.RegionI.thV_46
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((24923 : ℕ) : ℝ) ≤ (((723178418269 : ℚ) / 250000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2754
  have hSx : (((90448756187 : ℚ) / 200000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 24821, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2744
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_335 k := by decide +kernel
  have hT2 : (∑ k, tg_335 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_335 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_335 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((723178418269 : ℚ) / 250000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_335 k))
      + ((((90448756187 : ℚ) / 200000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_335 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_335 (yg_335 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨335, by omega⟩ : ℚ)) (εB := (cut ⟨336, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_335 yg_335 tg_335 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((723178418269 : ℚ) / 250000000000)) (((90448756187 : ℚ) / 200000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_336 : Fin 17 → ℕ := fun k => [24923, 211, 37, 17, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_336 : Fin 17 → ℕ := fun k => [25033, 216, 40, 17, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_336 : Fin 17 → ℚ := fun k => [((24743367857168463 : ℚ) / 1000000000000), ((38783072867631 : ℚ) / 200000000000), ((14817649818811 : ℚ) / 500000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_336 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨336, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨337, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨337, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨336, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_336 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_336 k + 1) (k.val + 1) < (cut ⟨337, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_336 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_336 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_336 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_336 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_336 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_336 ⟨1, by omega⟩ + 1 ≤ xg_336 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_336 k : ℝ) ≤ Chebyshev.theta ((xg_336 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2754
    · exact Work.RHContract.RegionI.thV_46
    · exact Work.RHContract.RegionI.thV_11
    · exact Work.RHContract.RegionI.thV_6
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((25033 : ℕ) : ℝ) ≤ (((180819619511 : ℚ) / 62500000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2764
  have hSx : (((11306094927 : ℚ) / 25000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 24923, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2754
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_336 k := by decide +kernel
  have hT2 : (∑ k, tg_336 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_336 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_336 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((180819619511 : ℚ) / 62500000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_336 k))
      + ((((11306094927 : ℚ) / 25000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_336 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_336 (yg_336 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨336, by omega⟩ : ℚ)) (εB := (cut ⟨337, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_336 yg_336 tg_336 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((180819619511 : ℚ) / 62500000000)) (((11306094927 : ℚ) / 25000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_337 : Fin 17 → ℕ := fun k => [25033, 211, 37, 17, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_337 : Fin 17 → ℕ := fun k => [25147, 217, 40, 17, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_337 : Fin 17 → ℚ := fun k => [((6211157099901417 : ℚ) / 250000000000), ((38783072867631 : ℚ) / 200000000000), ((14817649818811 : ℚ) / 500000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_337 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨337, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨338, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨338, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨337, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_337 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_337 k + 1) (k.val + 1) < (cut ⟨338, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_337 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_337 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_337 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_337 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_337 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_337 ⟨1, by omega⟩ + 1 ≤ xg_337 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_337 k : ℝ) ≤ Chebyshev.theta ((xg_337 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2764
    · exact Work.RHContract.RegionI.thV_46
    · exact Work.RHContract.RegionI.thV_11
    · exact Work.RHContract.RegionI.thV_6
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((25147 : ℕ) : ℝ) ≤ (((723378092107 : ℚ) / 250000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2774
  have hSx : (((226121906547 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 25033, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2764
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_337 k := by decide +kernel
  have hT2 : (∑ k, tg_337 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_337 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_337 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((723378092107 : ℚ) / 250000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_337 k))
      + ((((226121906547 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_337 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_337 (yg_337 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨337, by omega⟩ : ℚ)) (εB := (cut ⟨338, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_337 yg_337 tg_337 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((723378092107 : ℚ) / 250000000000)) (((226121906547 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_338 : Fin 17 → ℕ := fun k => [25147, 211, 37, 17, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_338 : Fin 17 → ℕ := fun k => [25243, 217, 40, 17, 10, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_338 : Fin 17 → ℚ := fun k => [((2494593358661509 : ℚ) / 100000000000), ((38783072867631 : ℚ) / 200000000000), ((14817649818811 : ℚ) / 500000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_338 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨338, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨339, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨339, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨338, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_338 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_338 k + 1) (k.val + 1) < (cut ⟨339, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_338 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_338 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_338 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_338 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_338 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_338 ⟨1, by omega⟩ + 1 ≤ xg_338 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_338 k : ℝ) ≤ Chebyshev.theta ((xg_338 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2774
    · exact Work.RHContract.RegionI.thV_46
    · exact Work.RHContract.RegionI.thV_11
    · exact Work.RHContract.RegionI.thV_6
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((25243 : ℕ) : ℝ) ≤ (((2893909271633 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2784
  have hSx : (((113060957241 : ℚ) / 250000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 25147, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2774
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_338 k := by decide +kernel
  have hT2 : (∑ k, tg_338 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_338 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_338 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2893909271633 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_338 k))
      + ((((113060957241 : ℚ) / 250000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_338 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_338 (yg_338 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨338, by omega⟩ : ℚ)) (εB := (cut ⟨339, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_338 yg_338 tg_338 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2893909271633 : ℚ) / 1000000000000)) (((113060957241 : ℚ) / 250000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_339 : Fin 17 → ℕ := fun k => [25243, 211, 37, 17, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_339 : Fin 17 → ℕ := fun k => [25343, 217, 40, 17, 10, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_339 : Fin 17 → ℚ := fun k => [((12523638912620977 : ℚ) / 500000000000), ((38783072867631 : ℚ) / 200000000000), ((14817649818811 : ℚ) / 500000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_339 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨339, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨340, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨340, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨339, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_339 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_339 k + 1) (k.val + 1) < (cut ⟨340, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_339 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_339 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_339 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_339 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_339 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_339 ⟨1, by omega⟩ + 1 ≤ xg_339 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_339 k : ℝ) ≤ Chebyshev.theta ((xg_339 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2784
    · exact Work.RHContract.RegionI.thV_46
    · exact Work.RHContract.RegionI.thV_11
    · exact Work.RHContract.RegionI.thV_6
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((25343 : ℕ) : ℝ) ≤ (((723576140503 : ℚ) / 250000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2794
  have hSx : (((452243844713 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 25243, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2784
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_339 k := by decide +kernel
  have hT2 : (∑ k, tg_339 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_339 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_339 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((723576140503 : ℚ) / 250000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_339 k))
      + ((((452243844713 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_339 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_339 (yg_339 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨339, by omega⟩ : ℚ)) (εB := (cut ⟨340, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_339 yg_339 tg_339 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((723576140503 : ℚ) / 250000000000)) (((452243844713 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_340 : Fin 17 → ℕ := fun k => [25343, 211, 37, 17, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_340 : Fin 17 → ℕ := fun k => [25447, 218, 40, 17, 10, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_340 : Fin 17 → ℚ := fun k => [((628716569533603 : ℚ) / 25000000000), ((38783072867631 : ℚ) / 200000000000), ((14817649818811 : ℚ) / 500000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_340 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨340, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨341, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨341, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨340, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_340 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_340 k + 1) (k.val + 1) < (cut ⟨341, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_340 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_340 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_340 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_340 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_340 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_340 ⟨1, by omega⟩ + 1 ≤ xg_340 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_340 k : ℝ) ≤ Chebyshev.theta ((xg_340 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2794
    · exact Work.RHContract.RegionI.thV_46
    · exact Work.RHContract.RegionI.thV_11
    · exact Work.RHContract.RegionI.thV_6
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((25447 : ℕ) : ℝ) ≤ (((1447349161959 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2804
  have hSx : (((452243860333 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 25343, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2794
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_340 k := by decide +kernel
  have hT2 : (∑ k, tg_340 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_340 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_340 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1447349161959 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_340 k))
      + ((((452243860333 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_340 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_340 (yg_340 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨340, by omega⟩ : ℚ)) (εB := (cut ⟨341, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_340 yg_340 tg_340 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1447349161959 : ℚ) / 500000000000)) (((452243860333 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_341 : Fin 17 → ℕ := fun k => [25447, 211, 37, 17, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_341 : Fin 17 → ℕ := fun k => [25577, 218, 40, 17, 10, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_341 : Fin 17 → ℚ := fun k => [((25250086478875479 : ℚ) / 1000000000000), ((38783072867631 : ℚ) / 200000000000), ((14817649818811 : ℚ) / 500000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_341 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨341, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨342, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨342, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨341, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_341 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_341 k + 1) (k.val + 1) < (cut ⟨342, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_341 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_341 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_341 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_341 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_341 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_341 ⟨1, by omega⟩ + 1 ≤ xg_341 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_341 k : ℝ) ≤ Chebyshev.theta ((xg_341 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2804
    · exact Work.RHContract.RegionI.thV_46
    · exact Work.RHContract.RegionI.thV_11
    · exact Work.RHContract.RegionI.thV_6
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((25577 : ℕ) : ℝ) ≤ (((361886301217 : ℚ) / 125000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2814
  have hSx : (((226121937917 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 25447, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2804
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_341 k := by decide +kernel
  have hT2 : (∑ k, tg_341 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_341 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_341 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((361886301217 : ℚ) / 125000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_341 k))
      + ((((226121937917 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_341 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_341 (yg_341 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨341, by omega⟩ : ℚ)) (εB := (cut ⟨342, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_341 yg_341 tg_341 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((361886301217 : ℚ) / 125000000000)) (((226121937917 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_342 : Fin 17 → ℕ := fun k => [25577, 211, 37, 17, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_342 : Fin 17 → ℕ := fun k => [25643, 219, 40, 17, 10, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_342 : Fin 17 → ℚ := fun k => [((25351552839645917 : ℚ) / 1000000000000), ((38783072867631 : ℚ) / 200000000000), ((14817649818811 : ℚ) / 500000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_342 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨342, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨343, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨343, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨342, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_342 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_342 k + 1) (k.val + 1) < (cut ⟨343, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_342 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_342 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_342 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_342 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_342 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_342 ⟨1, by omega⟩ + 1 ≤ xg_342 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_342 k : ℝ) ≤ Chebyshev.theta ((xg_342 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2814
    · exact Work.RHContract.RegionI.thV_46
    · exact Work.RHContract.RegionI.thV_11
    · exact Work.RHContract.RegionI.thV_6
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((25643 : ℕ) : ℝ) ≤ (((723870222531 : ℚ) / 250000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2824
  have hSx : (((226121945601 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 25577, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2814
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_342 k := by decide +kernel
  have hT2 : (∑ k, tg_342 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_342 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_342 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((723870222531 : ℚ) / 250000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_342 k))
      + ((((226121945601 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_342 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_342 (yg_342 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨342, by omega⟩ : ℚ)) (εB := (cut ⟨343, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_342 yg_342 tg_342 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((723870222531 : ℚ) / 250000000000)) (((226121945601 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_343 : Fin 17 → ℕ := fun k => [25643, 211, 37, 17, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_343 : Fin 17 → ℕ := fun k => [25747, 219, 40, 17, 10, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_343 : Fin 17 → ℚ := fun k => [((198852032950863 : ℚ) / 7812500000), ((38783072867631 : ℚ) / 200000000000), ((14817649818811 : ℚ) / 500000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_343 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨343, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨344, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨344, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨343, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_343 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_343 k + 1) (k.val + 1) < (cut ⟨344, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_343 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_343 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_343 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_343 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_343 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_343 ⟨1, by omega⟩ + 1 ≤ xg_343 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_343 k : ℝ) ≤ Chebyshev.theta ((xg_343 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2824
    · exact Work.RHContract.RegionI.thV_46
    · exact Work.RHContract.RegionI.thV_11
    · exact Work.RHContract.RegionI.thV_6
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((25747 : ℕ) : ℝ) ≤ (((2895869988173 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2834
  have hSx : (((452243906443 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 25643, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2824
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_343 k := by decide +kernel
  have hT2 : (∑ k, tg_343 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_343 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_343 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2895869988173 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_343 k))
      + ((((452243906443 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_343 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_343 (yg_343 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨343, by omega⟩ : ℚ)) (εB := (cut ⟨344, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_343 yg_343 tg_343 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2895869988173 : ℚ) / 1000000000000)) (((452243906443 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_344 : Fin 17 → ℕ := fun k => [25747, 211, 37, 17, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_344 : Fin 17 → ℕ := fun k => [25849, 220, 41, 17, 10, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_344 : Fin 17 → ℚ := fun k => [((5110920612469527 : ℚ) / 200000000000), ((38783072867631 : ℚ) / 200000000000), ((14817649818811 : ℚ) / 500000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_344 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨344, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨345, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨345, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨344, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_344 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_344 k + 1) (k.val + 1) < (cut ⟨345, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_344 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_344 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_344 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_344 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_344 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_344 ⟨1, by omega⟩ + 1 ≤ xg_344 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_344 k : ℝ) ≤ Chebyshev.theta ((xg_344 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2834
    · exact Work.RHContract.RegionI.thV_46
    · exact Work.RHContract.RegionI.thV_11
    · exact Work.RHContract.RegionI.thV_6
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((25849 : ℕ) : ℝ) ≤ (((1448128765053 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2844
  have hSx : (((226121960789 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 25747, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2834
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_344 k := by decide +kernel
  have hT2 : (∑ k, tg_344 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_344 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_344 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1448128765053 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_344 k))
      + ((((226121960789 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_344 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_344 (yg_344 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨344, by omega⟩ : ℚ)) (εB := (cut ⟨345, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_344 yg_344 tg_344 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1448128765053 : ℚ) / 500000000000)) (((226121960789 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_345 : Fin 17 → ℕ := fun k => [25849, 211, 41, 17, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_345 : Fin 17 → ℕ := fun k => [25943, 220, 41, 17, 10, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_345 : Fin 17 → ℚ := fun k => [((12828092989986257 : ℚ) / 500000000000), ((38783072867631 : ℚ) / 200000000000), ((16674435851513 : ℚ) / 500000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_345 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨345, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨346, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨346, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨345, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_345 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_345 k + 1) (k.val + 1) < (cut ⟨346, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_345 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_345 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_345 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_345 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_345 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_345 ⟨1, by omega⟩ + 1 ≤ xg_345 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_345 k : ℝ) ≤ Chebyshev.theta ((xg_345 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2844
    · exact Work.RHContract.RegionI.thV_46
    · exact Work.RHContract.RegionI.thV_12
    · exact Work.RHContract.RegionI.thV_6
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((25943 : ℕ) : ℝ) ≤ (((1448321737209 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2854
  have hSx : (((28265246037 : ℚ) / 62500000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 25849, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2844
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_345 k := by decide +kernel
  have hT2 : (∑ k, tg_345 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_345 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_345 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1448321737209 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_345 k))
      + ((((28265246037 : ℚ) / 62500000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_345 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_345 (yg_345 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨345, by omega⟩ : ℚ)) (εB := (cut ⟨346, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_345 yg_345 tg_345 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1448321737209 : ℚ) / 500000000000)) (((28265246037 : ℚ) / 62500000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_346 : Fin 17 → ℕ := fun k => [25943, 211, 41, 17, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_346 : Fin 17 → ℕ := fun k => [26041, 220, 41, 17, 10, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_346 : Fin 17 → ℚ := fun k => [((1609863137727083 : ℚ) / 62500000000), ((38783072867631 : ℚ) / 200000000000), ((16674435851513 : ℚ) / 500000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_346 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨346, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨347, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨347, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨346, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_346 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_346 k + 1) (k.val + 1) < (cut ⟨347, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_346 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_346 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_346 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_346 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_346 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_346 ⟨1, by omega⟩ + 1 ≤ xg_346 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_346 k : ℝ) ≤ Chebyshev.theta ((xg_346 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2854
    · exact Work.RHContract.RegionI.thV_46
    · exact Work.RHContract.RegionI.thV_12
    · exact Work.RHContract.RegionI.thV_6
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((26041 : ℕ) : ℝ) ≤ (((1448514042883 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2864
  have hSx : (((226121975741 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 25943, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2854
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_346 k := by decide +kernel
  have hT2 : (∑ k, tg_346 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_346 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_346 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1448514042883 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_346 k))
      + ((((226121975741 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_346 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_346 (yg_346 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨346, by omega⟩ : ℚ)) (εB := (cut ⟨347, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_346 yg_346 tg_346 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1448514042883 : ℚ) / 500000000000)) (((226121975741 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_347 : Fin 17 → ℕ := fun k => [26041, 211, 41, 17, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_347 : Fin 17 → ℕ := fun k => [26161, 221, 41, 17, 10, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_347 : Fin 17 → ℚ := fun k => [((25859469024285303 : ℚ) / 1000000000000), ((38783072867631 : ℚ) / 200000000000), ((16674435851513 : ℚ) / 500000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_347 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨347, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨348, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨348, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨347, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_347 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_347 k + 1) (k.val + 1) < (cut ⟨348, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_347 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_347 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_347 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_347 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_347 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_347 ⟨1, by omega⟩ + 1 ≤ xg_347 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_347 k : ℝ) ≤ Chebyshev.theta ((xg_347 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2864
    · exact Work.RHContract.RegionI.thV_46
    · exact Work.RHContract.RegionI.thV_12
    · exact Work.RHContract.RegionI.thV_6
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((26161 : ℕ) : ℝ) ≤ (((2897411029991 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2874
  have hSx : (((452243966267 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 26041, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2864
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_347 k := by decide +kernel
  have hT2 : (∑ k, tg_347 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_347 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_347 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2897411029991 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_347 k))
      + ((((452243966267 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_347 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_347 (yg_347 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨347, by omega⟩ : ℚ)) (εB := (cut ⟨348, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_347 yg_347 tg_347 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2897411029991 : ℚ) / 1000000000000)) (((452243966267 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_348 : Fin 17 → ℕ := fun k => [26161, 211, 41, 17, 7, 5, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_348 : Fin 17 → ℕ := fun k => [26251, 221, 41, 17, 10, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_348 : Fin 17 → ℚ := fun k => [((2596117128579837 : ℚ) / 100000000000), ((38783072867631 : ℚ) / 200000000000), ((16674435851513 : ℚ) / 500000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_348 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨348, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨349, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨349, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨348, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_348 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_348 k + 1) (k.val + 1) < (cut ⟨349, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_348 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_348 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_348 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_348 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_348 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_348 ⟨1, by omega⟩ + 1 ≤ xg_348 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_348 k : ℝ) ≤ Chebyshev.theta ((xg_348 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2874
    · exact Work.RHContract.RegionI.thV_46
    · exact Work.RHContract.RegionI.thV_12
    · exact Work.RHContract.RegionI.thV_6
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((26251 : ℕ) : ℝ) ≤ (((2897792577311 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2884
  have hSx : (((452243980927 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 26161, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2874
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_348 k := by decide +kernel
  have hT2 : (∑ k, tg_348 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_348 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_348 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2897792577311 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_348 k))
      + ((((452243980927 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_348 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_348 (yg_348 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨348, by omega⟩ : ℚ)) (εB := (cut ⟨349, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_348 yg_348 tg_348 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2897792577311 : ℚ) / 1000000000000)) (((452243980927 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_349 : Fin 17 → ℕ := fun k => [26251, 211, 41, 17, 7, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_349 : Fin 17 → ℕ := fun k => [26347, 222, 41, 17, 10, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_349 : Fin 17 → ℚ := fun k => [((26062910090253047 : ℚ) / 1000000000000), ((38783072867631 : ℚ) / 200000000000), ((16674435851513 : ℚ) / 500000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_349 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨349, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨350, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨350, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨349, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_349 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_349 k + 1) (k.val + 1) < (cut ⟨350, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_349 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_349 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_349 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_349 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_349 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_349 ⟨1, by omega⟩ + 1 ≤ xg_349 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_349 k : ℝ) ≤ Chebyshev.theta ((xg_349 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2884
    · exact Work.RHContract.RegionI.thV_46
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((26347 : ℕ) : ℝ) ≤ (((2898172792913 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2894
  have hSx : (((11306099887 : ℚ) / 25000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 26251, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2884
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_349 k := by decide +kernel
  have hT2 : (∑ k, tg_349 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_349 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_349 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2898172792913 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_349 k))
      + ((((11306099887 : ℚ) / 25000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_349 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_349 (yg_349 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨349, by omega⟩ : ℚ)) (εB := (cut ⟨350, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_349 yg_349 tg_349 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2898172792913 : ℚ) / 1000000000000)) (((11306099887 : ℚ) / 25000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_350 : Fin 17 → ℕ := fun k => [26347, 211, 41, 17, 7, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_350 : Fin 17 → ℕ := fun k => [26437, 222, 41, 17, 10, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_350 : Fin 17 → ℚ := fun k => [((26164683858517521 : ℚ) / 1000000000000), ((38783072867631 : ℚ) / 200000000000), ((16674435851513 : ℚ) / 500000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_350 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨350, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨351, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨351, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨350, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_350 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_350 k + 1) (k.val + 1) < (cut ⟨351, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_350 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_350 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_350 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_350 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_350 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_350 ⟨1, by omega⟩ + 1 ≤ xg_350 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_350 k : ℝ) ≤ Chebyshev.theta ((xg_350 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2894
    · exact Work.RHContract.RegionI.thV_46
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((26437 : ℕ) : ℝ) ≤ (((1449275778367 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2904
  have hSx : (((452244009931 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 26347, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2894
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_350 k := by decide +kernel
  have hT2 : (∑ k, tg_350 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_350 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_350 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1449275778367 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_350 k))
      + ((((452244009931 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_350 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_350 (yg_350 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨350, by omega⟩ : ℚ)) (εB := (cut ⟨351, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_350 yg_350 tg_350 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1449275778367 : ℚ) / 500000000000)) (((452244009931 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_351 : Fin 17 → ℕ := fun k => [26437, 211, 41, 17, 7, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_351 : Fin 17 → ℕ := fun k => [26561, 223, 41, 17, 10, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_351 : Fin 17 → ℚ := fun k => [((3283311985040649 : ℚ) / 125000000000), ((38783072867631 : ℚ) / 200000000000), ((16674435851513 : ℚ) / 500000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_351 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨351, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨352, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨352, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨351, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_351 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_351 k + 1) (k.val + 1) < (cut ⟨352, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_351 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_351 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_351 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_351 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_351 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_351 ⟨1, by omega⟩ + 1 ≤ xg_351 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_351 k : ℝ) ≤ Chebyshev.theta ((xg_351 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2904
    · exact Work.RHContract.RegionI.thV_46
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((26561 : ℕ) : ℝ) ≤ (((2898928860417 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2914
  have hSx : (((452244024271 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 26437, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2904
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_351 k := by decide +kernel
  have hT2 : (∑ k, tg_351 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_351 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_351 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2898928860417 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_351 k))
      + ((((452244024271 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_351 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_351 (yg_351 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨351, by omega⟩ : ℚ)) (εB := (cut ⟨352, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_351 yg_351 tg_351 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2898928860417 : ℚ) / 1000000000000)) (((452244024271 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_352 : Fin 17 → ℕ := fun k => [26561, 223, 41, 17, 7, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_352 : Fin 17 → ℕ := fun k => [26683, 223, 41, 17, 10, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_352 : Fin 17 → ℚ := fun k => [((3296043316396079 : ℚ) / 125000000000), ((39864507221559 : ℚ) / 200000000000), ((16674435851513 : ℚ) / 500000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_352 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨352, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨353, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨353, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨352, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_352 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_352 k + 1) (k.val + 1) < (cut ⟨353, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_352 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_352 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_352 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_352 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_352 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_352 ⟨1, by omega⟩ + 1 ≤ xg_352 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_352 k : ℝ) ≤ Chebyshev.theta ((xg_352 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2914
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((26683 : ℕ) : ℝ) ≤ (((2899304325281 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2924
  have hSx : (((452244038501 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 26561, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2914
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_352 k := by decide +kernel
  have hT2 : (∑ k, tg_352 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_352 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_352 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2899304325281 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_352 k))
      + ((((452244038501 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_352 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_352 (yg_352 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨352, by omega⟩ : ℚ)) (εB := (cut ⟨353, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_352 yg_352 tg_352 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2899304325281 : ℚ) / 1000000000000)) (((452244038501 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_353 : Fin 17 → ℕ := fun k => [26683, 223, 41, 17, 7, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_353 : Fin 17 → ℕ := fun k => [26731, 223, 41, 17, 10, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_353 : Fin 17 → ℚ := fun k => [((26470246035770567 : ℚ) / 1000000000000), ((39864507221559 : ℚ) / 200000000000), ((16674435851513 : ℚ) / 500000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_353 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨353, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨354, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨354, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨353, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_353 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_353 k + 1) (k.val + 1) < (cut ⟨354, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_353 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_353 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_353 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_353 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_353 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_353 ⟨1, by omega⟩ + 1 ≤ xg_353 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_353 k : ℝ) ≤ Chebyshev.theta ((xg_353 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2924
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((26731 : ℕ) : ℝ) ≤ (((289967871841 : ℚ) / 100000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2934
  have hSx : (((452244052593 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 26683, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2924
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_353 k := by decide +kernel
  have hT2 : (∑ k, tg_353 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_353 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_353 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((289967871841 : ℚ) / 100000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_353 k))
      + ((((452244052593 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_353 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_353 (yg_353 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨353, by omega⟩ : ℚ)) (εB := (cut ⟨354, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_353 yg_353 tg_353 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((289967871841 : ℚ) / 100000000000)) (((452244052593 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_354 : Fin 17 → ℕ := fun k => [26731, 223, 41, 17, 7, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_354 : Fin 17 → ℕ := fun k => [26849, 224, 41, 17, 10, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_354 : Fin 17 → ℚ := fun k => [((5314434823423023 : ℚ) / 200000000000), ((39864507221559 : ℚ) / 200000000000), ((16674435851513 : ℚ) / 500000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_354 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨354, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨355, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨355, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨354, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_354 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_354 k + 1) (k.val + 1) < (cut ⟨355, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_354 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_354 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_354 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_354 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_354 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_354 ⟨1, by omega⟩ + 1 ≤ xg_354 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_354 k : ℝ) ≤ Chebyshev.theta ((xg_354 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2934
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((26849 : ℕ) : ℝ) ≤ (((23200414749 : ℚ) / 8000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2944
  have hSx : (((113061016651 : ℚ) / 250000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 26731, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2934
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_354 k := by decide +kernel
  have hT2 : (∑ k, tg_354 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_354 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_354 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((23200414749 : ℚ) / 8000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_354 k))
      + ((((113061016651 : ℚ) / 250000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_354 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_354 (yg_354 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨354, by omega⟩ : ℚ)) (εB := (cut ⟨355, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_354 yg_354 tg_354 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((23200414749 : ℚ) / 8000000000)) (((113061016651 : ℚ) / 250000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_355 : Fin 17 → ℕ := fun k => [26849, 223, 41, 17, 7, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_355 : Fin 17 → ℕ := fun k => [26947, 224, 41, 17, 10, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_355 : Fin 17 → ℚ := fun k => [((26674136128086547 : ℚ) / 1000000000000), ((39864507221559 : ℚ) / 200000000000), ((16674435851513 : ℚ) / 500000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_355 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨355, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨356, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨356, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨355, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_355 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_355 k + 1) (k.val + 1) < (cut ⟨356, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_355 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_355 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_355 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_355 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_355 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_355 ⟨1, by omega⟩ + 1 ≤ xg_355 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_355 k : ℝ) ≤ Chebyshev.theta ((xg_355 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2944
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((26947 : ℕ) : ℝ) ≤ (((290042364511 : ℚ) / 100000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2954
  have hSx : (((452244080521 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 26849, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2944
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_355 k := by decide +kernel
  have hT2 : (∑ k, tg_355 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_355 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_355 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((290042364511 : ℚ) / 100000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_355 k))
      + ((((452244080521 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_355 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_355 (yg_355 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨355, by omega⟩ : ℚ)) (εB := (cut ⟨356, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_355 yg_355 tg_355 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((290042364511 : ℚ) / 100000000000)) (((452244080521 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_356 : Fin 17 → ℕ := fun k => [26947, 223, 41, 17, 7, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_356 : Fin 17 → ℕ := fun k => [27043, 225, 41, 17, 10, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_356 : Fin 17 → ℚ := fun k => [((13388066837391827 : ℚ) / 500000000000), ((39864507221559 : ℚ) / 200000000000), ((16674435851513 : ℚ) / 500000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_356 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨356, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨357, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨357, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨356, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_356 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_356 k + 1) (k.val + 1) < (cut ⟨357, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_356 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_356 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_356 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_356 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_356 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_356 ⟨1, by omega⟩ + 1 ≤ xg_356 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_356 k : ℝ) ≤ Chebyshev.theta ((xg_356 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2954
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((27043 : ℕ) : ℝ) ≤ (((2900794124369 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2964
  have hSx : (((226122047169 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 26947, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2954
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_356 k := by decide +kernel
  have hT2 : (∑ k, tg_356 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_356 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_356 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2900794124369 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_356 k))
      + ((((226122047169 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_356 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_356 (yg_356 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨356, by omega⟩ : ℚ)) (εB := (cut ⟨357, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_356 yg_356 tg_356 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2900794124369 : ℚ) / 1000000000000)) (((226122047169 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_357 : Fin 17 → ℕ := fun k => [27043, 223, 41, 17, 7, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_357 : Fin 17 → ℕ := fun k => [27127, 225, 41, 17, 10, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_357 : Fin 17 → ℚ := fun k => [((6719541712133203 : ℚ) / 250000000000), ((39864507221559 : ℚ) / 200000000000), ((16674435851513 : ℚ) / 500000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_357 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨357, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨358, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨358, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨357, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_357 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_357 k + 1) (k.val + 1) < (cut ⟨358, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_357 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_357 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_357 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_357 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_357 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_357 ⟨1, by omega⟩ + 1 ≤ xg_357 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_357 k : ℝ) ≤ Chebyshev.theta ((xg_357 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2964
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((27127 : ℕ) : ℝ) ≤ (((2901163306773 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2974
  have hSx : (((226122054029 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 27043, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2964
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_357 k := by decide +kernel
  have hT2 : (∑ k, tg_357 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_357 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_357 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2901163306773 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_357 k))
      + ((((226122054029 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_357 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_357 (yg_357 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨357, by omega⟩ : ℚ)) (εB := (cut ⟨358, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_357 yg_357 tg_357 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2901163306773 : ℚ) / 1000000000000)) (((226122054029 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_358 : Fin 17 → ℕ := fun k => [27127, 223, 41, 17, 7, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_358 : Fin 17 → ℕ := fun k => [27271, 226, 41, 17, 10, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_358 : Fin 17 → ℚ := fun k => [((3372529385586461 : ℚ) / 125000000000), ((39864507221559 : ℚ) / 200000000000), ((16674435851513 : ℚ) / 500000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_358 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨358, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨359, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨359, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨358, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_358 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_358 k + 1) (k.val + 1) < (cut ⟨359, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_358 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_358 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_358 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_358 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_358 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_358 ⟨1, by omega⟩ + 1 ≤ xg_358 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_358 k : ℝ) ≤ Chebyshev.theta ((xg_358 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2974
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((27271 : ℕ) : ℝ) ≤ (((3626913391 : ℚ) / 1250000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2984
  have hSx : (((5653051521 : ℚ) / 12500000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 27127, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2974
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_358 k := by decide +kernel
  have hT2 : (∑ k, tg_358 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_358 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_358 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((3626913391 : ℚ) / 1250000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_358 k))
      + ((((5653051521 : ℚ) / 12500000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_358 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_358 (yg_358 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨358, by omega⟩ : ℚ)) (εB := (cut ⟨359, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_358 yg_358 tg_358 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((3626913391 : ℚ) / 1250000000)) (((5653051521 : ℚ) / 12500000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_359 : Fin 17 → ℕ := fun k => [27271, 223, 41, 17, 7, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_359 : Fin 17 → ℕ := fun k => [27407, 226, 41, 17, 10, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_359 : Fin 17 → ℚ := fun k => [((6770587889859149 : ℚ) / 250000000000), ((39864507221559 : ℚ) / 200000000000), ((16674435851513 : ℚ) / 500000000000), ((1642895687609 : ℚ) / 125000000000), ((5347107529157 : ℚ) / 1000000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_359 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨359, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨360, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (17 + 1) < (cut ⟨360, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 17, (cut ⟨359, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_359 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 17, Work.RHContract.RegionI.Fhi (yg_359 k + 1) (k.val + 1) < (cut ⟨360, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 17, 2 ≤ xg_359 k := by decide +kernel
  have hxhi : ∀ k : Fin 17, xg_359 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 17, yg_359 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 17, 1 ≤ yg_359 k := by decide +kernel
  have hposy : ∀ k : Fin 17, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_359 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_359 ⟨1, by omega⟩ + 1 ≤ xg_359 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 17, (tg_359 k : ℝ) ≤ Chebyshev.theta ((xg_359 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_2984
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((27407 : ℕ) : ℝ) ≤ (((2901896567939 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_2994
  have hSx : (((113061033793 : ℚ) / 250000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 27271, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_2984
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_359 k := by decide +kernel
  have hT2 : (∑ k, tg_359 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_359 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_359 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2901896567939 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_359 k))
      + ((((113061033793 : ℚ) / 250000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_359 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_359 (yg_359 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨359, by omega⟩ : ℚ)) (εB := (cut ⟨360, by omega⟩ : ℚ)) hhi hlo
    17 17 (by norm_num) (by norm_num) hKtop xg_359 yg_359 tg_359 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2901896567939 : ℚ) / 1000000000000)) (((113061033793 : ℚ) / 250000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

end

end Work.RHContract.A.RegionI
