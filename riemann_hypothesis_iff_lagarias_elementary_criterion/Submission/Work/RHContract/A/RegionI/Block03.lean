import Mathlib
import Submission.Work.RHContract.A.RegionI.Core
import Submission.Work.RHContract.A.RegionI.blockCert
import Submission.Work.RHContract.A.RegionI.Data11
import Submission.Work.RHContract.A.RegionI.Cuts

/-!  Region I: group certificates.  GENERATED FILE. -/

open scoped BigOperators

namespace Work.RHContract.A.RegionI

noncomputable section

private def xg_80 : Fin 14 → ℕ := fun k => [4751, 89, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_80 : Fin 14 → ℕ := fun k => [4799, 94, 23, 11, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_80 : Fin 14 → ℚ := fun k => [((2332679670454133 : ℚ) / 500000000000), ((39576839696887 : ℚ) / 500000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_80 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨80, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨81, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (14 + 1) < (cut ⟨81, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 14, (cut ⟨80, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_80 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 14, Work.RHContract.RegionI.Fhi (yg_80 k + 1) (k.val + 1) < (cut ⟨81, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 14, 2 ≤ xg_80 k := by decide +kernel
  have hxhi : ∀ k : Fin 14, xg_80 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 14, yg_80 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 14, 1 ≤ yg_80 k := by decide +kernel
  have hposy : ∀ k : Fin 14, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_80 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_80 ⟨1, by omega⟩ + 1 ≤ xg_80 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 14, (tg_80 k : ℝ) ≤ Chebyshev.theta ((xg_80 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_639
    · exact Work.RHContract.RegionI.thV_23
    · exact Work.RHContract.RegionI.thV_8
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((4799 : ℕ) : ℝ) ≤ (((2716215285139 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_645
  have hSx : (((452225119061 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 4751, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_639
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_80 k := by decide +kernel
  have hT2 : (∑ k, tg_80 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_80 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_80 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2716215285139 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_80 k))
      + ((((452225119061 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_80 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_80 (yg_80 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨80, by omega⟩ : ℚ)) (εB := (cut ⟨81, by omega⟩ : ℚ)) hhi hlo
    14 14 (by norm_num) (by norm_num) hKtop xg_80 yg_80 tg_80 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2716215285139 : ℚ) / 1000000000000)) (((452225119061 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_81 : Fin 14 → ℕ := fun k => [4799, 89, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_81 : Fin 14 → ℕ := fun k => [4871, 94, 23, 11, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_81 : Fin 14 → ℚ := fun k => [((4716198767705101 : ℚ) / 1000000000000), ((39576839696887 : ℚ) / 500000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_81 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨81, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨82, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (14 + 1) < (cut ⟨82, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 14, (cut ⟨81, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_81 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 14, Work.RHContract.RegionI.Fhi (yg_81 k + 1) (k.val + 1) < (cut ⟨82, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 14, 2 ≤ xg_81 k := by decide +kernel
  have hxhi : ∀ k : Fin 14, xg_81 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 14, yg_81 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 14, 1 ≤ yg_81 k := by decide +kernel
  have hposy : ∀ k : Fin 14, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_81 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_81 ⟨1, by omega⟩ + 1 ≤ xg_81 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 14, (tg_81 k : ℝ) ≤ Chebyshev.theta ((xg_81 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_645
    · exact Work.RHContract.RegionI.thV_23
    · exact Work.RHContract.RegionI.thV_8
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((4871 : ℕ) : ℝ) ≤ (((1358728542207 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_651
  have hSx : (((226112690557 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 4799, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_645
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_81 k := by decide +kernel
  have hT2 : (∑ k, tg_81 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_81 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_81 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1358728542207 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_81 k))
      + ((((226112690557 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_81 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_81 (yg_81 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨81, by omega⟩ : ℚ)) (εB := (cut ⟨82, by omega⟩ : ℚ)) hhi hlo
    14 14 (by norm_num) (by norm_num) hKtop xg_81 yg_81 tg_81 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1358728542207 : ℚ) / 500000000000)) (((226112690557 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_82 : Fin 14 → ℕ := fun k => [4871, 89, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_82 : Fin 14 → ℕ := fun k => [4931, 95, 23, 11, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_82 : Fin 14 → ℚ := fun k => [((4767097192426253 : ℚ) / 1000000000000), ((39576839696887 : ℚ) / 500000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_82 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨82, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨83, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (14 + 1) < (cut ⟨83, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 14, (cut ⟨82, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_82 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 14, Work.RHContract.RegionI.Fhi (yg_82 k + 1) (k.val + 1) < (cut ⟨83, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 14, 2 ≤ xg_82 k := by decide +kernel
  have hxhi : ∀ k : Fin 14, xg_82 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 14, yg_82 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 14, 1 ≤ yg_82 k := by decide +kernel
  have hposy : ∀ k : Fin 14, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_82 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_82 ⟨1, by omega⟩ + 1 ≤ xg_82 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 14, (tg_82 k : ℝ) ≤ Chebyshev.theta ((xg_82 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_651
    · exact Work.RHContract.RegionI.thV_23
    · exact Work.RHContract.RegionI.thV_8
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((4931 : ℕ) : ℝ) ≤ (((2718680550251 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_657
  have hSx : (((18089025523 : ℚ) / 40000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 4871, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_651
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_82 k := by decide +kernel
  have hT2 : (∑ k, tg_82 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_82 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_82 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2718680550251 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_82 k))
      + ((((18089025523 : ℚ) / 40000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_82 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_82 (yg_82 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨82, by omega⟩ : ℚ)) (εB := (cut ⟨83, by omega⟩ : ℚ)) hhi hlo
    14 14 (by norm_num) (by norm_num) hKtop xg_82 yg_82 tg_82 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2718680550251 : ℚ) / 1000000000000)) (((18089025523 : ℚ) / 40000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_83 : Fin 14 → ℕ := fun k => [4931, 89, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_83 : Fin 14 → ℕ := fun k => [4967, 95, 23, 11, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_83 : Fin 14 → ℚ := fun k => [((96361696134491 : ℚ) / 20000000000), ((39576839696887 : ℚ) / 500000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_83 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨83, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨84, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (14 + 1) < (cut ⟨84, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 14, (cut ⟨83, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_83 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 14, Work.RHContract.RegionI.Fhi (yg_83 k + 1) (k.val + 1) < (cut ⟨84, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 14, 2 ≤ xg_83 k := by decide +kernel
  have hxhi : ∀ k : Fin 14, xg_83 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 14, yg_83 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 14, 1 ≤ yg_83 k := by decide +kernel
  have hposy : ∀ k : Fin 14, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_83 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_83 ⟨1, by omega⟩ + 1 ≤ xg_83 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 14, (tg_83 k : ℝ) ≤ Chebyshev.theta ((xg_83 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_657
    · exact Work.RHContract.RegionI.thV_23
    · exact Work.RHContract.RegionI.thV_8
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((4967 : ℕ) : ℝ) ≤ (((543978658149 : ℚ) / 200000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_663
  have hSx : (((452225887503 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 4931, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_657
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_83 k := by decide +kernel
  have hT2 : (∑ k, tg_83 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_83 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_83 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((543978658149 : ℚ) / 200000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_83 k))
      + ((((452225887503 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_83 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_83 (yg_83 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨83, by omega⟩ : ℚ)) (εB := (cut ⟨84, by omega⟩ : ℚ)) hhi hlo
    14 14 (by norm_num) (by norm_num) hKtop xg_83 yg_83 tg_83 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((543978658149 : ℚ) / 200000000000)) (((452225887503 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_84 : Fin 14 → ℕ := fun k => [4967, 89, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_84 : Fin 14 → ℕ := fun k => [5003, 96, 23, 11, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_84 : Fin 14 → ℚ := fun k => [((4869125222327121 : ℚ) / 1000000000000), ((39576839696887 : ℚ) / 500000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_84 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨84, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨85, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (14 + 1) < (cut ⟨85, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 14, (cut ⟨84, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_84 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 14, Work.RHContract.RegionI.Fhi (yg_84 k + 1) (k.val + 1) < (cut ⟨85, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 14, 2 ≤ xg_84 k := by decide +kernel
  have hxhi : ∀ k : Fin 14, xg_84 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 14, yg_84 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 14, 1 ≤ yg_84 k := by decide +kernel
  have hposy : ∀ k : Fin 14, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_84 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_84 ⟨1, by omega⟩ + 1 ≤ xg_84 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 14, (tg_84 k : ℝ) ≤ Chebyshev.theta ((xg_84 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_663
    · exact Work.RHContract.RegionI.thV_23
    · exact Work.RHContract.RegionI.thV_8
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((5003 : ℕ) : ℝ) ≤ (((544219293361 : ℚ) / 200000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_669
  have hSx : (((226113066287 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 4967, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_663
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_84 k := by decide +kernel
  have hT2 : (∑ k, tg_84 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_84 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_84 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((544219293361 : ℚ) / 200000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_84 k))
      + ((((226113066287 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_84 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_84 (yg_84 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨84, by omega⟩ : ℚ)) (εB := (cut ⟨85, by omega⟩ : ℚ)) hhi hlo
    14 14 (by norm_num) (by norm_num) hKtop xg_84 yg_84 tg_84 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((544219293361 : ℚ) / 200000000000)) (((226113066287 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_85 : Fin 14 → ℕ := fun k => [5003, 89, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_85 : Fin 14 → ℕ := fun k => [5051, 96, 23, 11, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_85 : Fin 14 → ℚ := fun k => [((4920213142957667 : ℚ) / 1000000000000), ((39576839696887 : ℚ) / 500000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_85 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨85, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨86, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (14 + 1) < (cut ⟨86, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 14, (cut ⟨85, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_85 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 14, Work.RHContract.RegionI.Fhi (yg_85 k + 1) (k.val + 1) < (cut ⟨86, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 14, 2 ≤ xg_85 k := by decide +kernel
  have hxhi : ∀ k : Fin 14, xg_85 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 14, yg_85 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 14, 1 ≤ yg_85 k := by decide +kernel
  have hposy : ∀ k : Fin 14, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_85 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_85 ⟨1, by omega⟩ + 1 ≤ xg_85 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 14, (tg_85 k : ℝ) ≤ Chebyshev.theta ((xg_85 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_669
    · exact Work.RHContract.RegionI.thV_23
    · exact Work.RHContract.RegionI.thV_8
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((5051 : ℕ) : ℝ) ≤ (((1361145233807 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_675
  have hSx : (((452226373797 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 5003, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_669
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_85 k := by decide +kernel
  have hT2 : (∑ k, tg_85 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_85 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_85 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1361145233807 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_85 k))
      + ((((452226373797 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_85 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_85 (yg_85 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨85, by omega⟩ : ℚ)) (εB := (cut ⟨86, by omega⟩ : ℚ)) hhi hlo
    14 14 (by norm_num) (by norm_num) hKtop xg_85 yg_85 tg_85 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1361145233807 : ℚ) / 500000000000)) (((452226373797 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_86 : Fin 14 → ℕ := fun k => [5051, 89, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_86 : Fin 14 → ℕ := fun k => [5101, 97, 23, 11, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_86 : Fin 14 → ℚ := fun k => [((4971346996778199 : ℚ) / 1000000000000), ((39576839696887 : ℚ) / 500000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_86 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨86, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨87, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (14 + 1) < (cut ⟨87, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 14, (cut ⟨86, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_86 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 14, Work.RHContract.RegionI.Fhi (yg_86 k + 1) (k.val + 1) < (cut ⟨87, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 14, 2 ≤ xg_86 k := by decide +kernel
  have hxhi : ∀ k : Fin 14, xg_86 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 14, yg_86 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 14, 1 ≤ yg_86 k := by decide +kernel
  have hposy : ∀ k : Fin 14, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_86 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_86 ⟨1, by omega⟩ + 1 ≤ xg_86 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 14, (tg_86 k : ℝ) ≤ Chebyshev.theta ((xg_86 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_675
    · exact Work.RHContract.RegionI.thV_23
    · exact Work.RHContract.RegionI.thV_8
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((5101 : ℕ) : ℝ) ≤ (((544694153197 : ℚ) / 200000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_681
  have hSx : (((113056652839 : ℚ) / 250000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 5051, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_675
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_86 k := by decide +kernel
  have hT2 : (∑ k, tg_86 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_86 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_86 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((544694153197 : ℚ) / 200000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_86 k))
      + ((((113056652839 : ℚ) / 250000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_86 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_86 (yg_86 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨86, by omega⟩ : ℚ)) (εB := (cut ⟨87, by omega⟩ : ℚ)) hhi hlo
    14 14 (by norm_num) (by norm_num) hKtop xg_86 yg_86 tg_86 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((544694153197 : ℚ) / 200000000000)) (((113056652839 : ℚ) / 250000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_87 : Fin 14 → ℕ := fun k => [5101, 97, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_87 : Fin 14 → ℕ := fun k => [5167, 97, 23, 11, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_87 : Fin 14 → ℚ := fun k => [((2511275047602057 : ℚ) / 500000000000), ((83728390370717 : ℚ) / 1000000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_87 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨87, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨88, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (14 + 1) < (cut ⟨88, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 14, (cut ⟨87, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_87 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 14, Work.RHContract.RegionI.Fhi (yg_87 k + 1) (k.val + 1) < (cut ⟨88, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 14, 2 ≤ xg_87 k := by decide +kernel
  have hxhi : ∀ k : Fin 14, xg_87 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 14, yg_87 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 14, 1 ≤ yg_87 k := by decide +kernel
  have hposy : ∀ k : Fin 14, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_87 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_87 ⟨1, by omega⟩ + 1 ≤ xg_87 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 14, (tg_87 k : ℝ) ≤ Chebyshev.theta ((xg_87 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_681
    · exact Work.RHContract.RegionI.thV_24
    · exact Work.RHContract.RegionI.thV_8
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((5167 : ℕ) : ℝ) ≤ (((1362319752791 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_687
  have hSx : (((113056710873 : ℚ) / 250000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 5101, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_681
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_87 k := by decide +kernel
  have hT2 : (∑ k, tg_87 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_87 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_87 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1362319752791 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_87 k))
      + ((((113056710873 : ℚ) / 250000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_87 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_87 (yg_87 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨87, by omega⟩ : ℚ)) (εB := (cut ⟨88, by omega⟩ : ℚ)) hhi hlo
    14 14 (by norm_num) (by norm_num) hKtop xg_87 yg_87 tg_87 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1362319752791 : ℚ) / 500000000000)) (((113056710873 : ℚ) / 250000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_88 : Fin 14 → ℕ := fun k => [5167, 97, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_88 : Fin 14 → ℕ := fun k => [5227, 98, 23, 11, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_88 : Fin 14 → ℚ := fun k => [((634226533721231 : ℚ) / 125000000000), ((83728390370717 : ℚ) / 1000000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_88 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨88, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨89, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (14 + 1) < (cut ⟨89, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 14, (cut ⟨88, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_88 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 14, Work.RHContract.RegionI.Fhi (yg_88 k + 1) (k.val + 1) < (cut ⟨89, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 14, 2 ≤ xg_88 k := by decide +kernel
  have hxhi : ∀ k : Fin 14, xg_88 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 14, yg_88 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 14, 1 ≤ yg_88 k := by decide +kernel
  have hposy : ∀ k : Fin 14, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_88 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_88 ⟨1, by omega⟩ + 1 ≤ xg_88 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 14, (tg_88 k : ℝ) ≤ Chebyshev.theta ((xg_88 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_687
    · exact Work.RHContract.RegionI.thV_24
    · exact Work.RHContract.RegionI.thV_8
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((5227 : ℕ) : ℝ) ≤ (((2725794514229 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_693
  have hSx : (((452227071107 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 5167, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_687
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_88 k := by decide +kernel
  have hT2 : (∑ k, tg_88 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_88 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_88 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2725794514229 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_88 k))
      + ((((452227071107 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_88 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_88 (yg_88 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨88, by omega⟩ : ℚ)) (εB := (cut ⟨89, by omega⟩ : ℚ)) hhi hlo
    14 14 (by norm_num) (by norm_num) hKtop xg_88 yg_88 tg_88 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2725794514229 : ℚ) / 1000000000000)) (((452227071107 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_89 : Fin 14 → ℕ := fun k => [5227, 97, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_89 : Fin 14 → ℕ := fun k => [5279, 98, 23, 11, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def tg_89 : Fin 14 → ℚ := fun k => [((5125145327440783 : ℚ) / 1000000000000), ((83728390370717 : ℚ) / 1000000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_89 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨89, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨90, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (14 + 1) < (cut ⟨90, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 14, (cut ⟨89, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_89 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 14, Work.RHContract.RegionI.Fhi (yg_89 k + 1) (k.val + 1) < (cut ⟨90, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 14, 2 ≤ xg_89 k := by decide +kernel
  have hxhi : ∀ k : Fin 14, xg_89 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 14, yg_89 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 14, 1 ≤ yg_89 k := by decide +kernel
  have hposy : ∀ k : Fin 14, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_89 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_89 ⟨1, by omega⟩ + 1 ≤ xg_89 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 14, (tg_89 k : ℝ) ≤ Chebyshev.theta ((xg_89 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_693
    · exact Work.RHContract.RegionI.thV_24
    · exact Work.RHContract.RegionI.thV_8
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((5279 : ℕ) : ℝ) ≤ (((2726936988137 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_699
  have hSx : (((90445458681 : ℚ) / 200000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 5227, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_693
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_89 k := by decide +kernel
  have hT2 : (∑ k, tg_89 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_89 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_89 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2726936988137 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_89 k))
      + ((((90445458681 : ℚ) / 200000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_89 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_89 (yg_89 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨89, by omega⟩ : ℚ)) (εB := (cut ⟨90, by omega⟩ : ℚ)) hhi hlo
    14 14 (by norm_num) (by norm_num) hKtop xg_89 yg_89 tg_89 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2726936988137 : ℚ) / 1000000000000)) (((90445458681 : ℚ) / 200000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_90 : Fin 14 → ℕ := fun k => [5279, 97, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2].getD k.val 0
private def yg_90 : Fin 15 → ℕ := fun k => [5333, 99, 23, 11, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_90 : Fin 14 → ℚ := fun k => [((1294135963093043 : ℚ) / 250000000000), ((83728390370717 : ℚ) / 1000000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_90 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨90, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨91, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨91, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 14, (cut ⟨90, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_90 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_90 k + 1) (k.val + 1) < (cut ⟨91, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 14, 2 ≤ xg_90 k := by decide +kernel
  have hxhi : ∀ k : Fin 14, xg_90 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_90 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_90 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_90 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_90 ⟨1, by omega⟩ + 1 ≤ xg_90 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 14, (tg_90 k : ℝ) ≤ Chebyshev.theta ((xg_90 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_699
    · exact Work.RHContract.RegionI.thV_24
    · exact Work.RHContract.RegionI.thV_8
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((5333 : ℕ) : ℝ) ≤ (((42626055413 : ℚ) / 15625000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_705
  have hSx : (((90445502181 : ℚ) / 200000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 5279, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_699
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_90 k := by decide +kernel
  have hT2 : (∑ k, tg_90 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_90 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_90 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((42626055413 : ℚ) / 15625000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_90 k))
      + ((((90445502181 : ℚ) / 200000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_90 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_90 (yg_90 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨90, by omega⟩ : ℚ)) (εB := (cut ⟨91, by omega⟩ : ℚ)) hhi hlo
    14 15 (by norm_num) (by norm_num) hKtop xg_90 yg_90 tg_90 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((42626055413 : ℚ) / 15625000000)) (((90445502181 : ℚ) / 200000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_91 : Fin 15 → ℕ := fun k => [5333, 97, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_91 : Fin 15 → ℕ := fun k => [5399, 99, 24, 11, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_91 : Fin 15 → ℚ := fun k => [((5228005267301199 : ℚ) / 1000000000000), ((83728390370717 : ℚ) / 1000000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_91 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨91, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨92, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨92, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨91, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_91 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_91 k + 1) (k.val + 1) < (cut ⟨92, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_91 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_91 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_91 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_91 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_91 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_91 ⟨1, by omega⟩ + 1 ≤ xg_91 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_91 k : ℝ) ≤ Chebyshev.theta ((xg_91 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_705
    · exact Work.RHContract.RegionI.thV_24
    · exact Work.RHContract.RegionI.thV_8
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
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((5399 : ℕ) : ℝ) ≤ (((1364591834067 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_711
  have hSx : (((452227723891 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 5333, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_705
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_91 k := by decide +kernel
  have hT2 : (∑ k, tg_91 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_91 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_91 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1364591834067 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_91 k))
      + ((((452227723891 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_91 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_91 (yg_91 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨91, by omega⟩ : ℚ)) (εB := (cut ⟨92, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_91 yg_91 tg_91 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1364591834067 : ℚ) / 500000000000)) (((452227723891 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_92 : Fin 15 → ℕ := fun k => [5399, 97, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_92 : Fin 15 → ℕ := fun k => [5437, 100, 24, 11, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_92 : Fin 15 → ℚ := fun k => [((1055908759302693 : ℚ) / 200000000000), ((83728390370717 : ℚ) / 1000000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_92 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨92, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨93, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨93, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨92, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_92 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_92 k + 1) (k.val + 1) < (cut ⟨93, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_92 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_92 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_92 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_92 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_92 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_92 ⟨1, by omega⟩ + 1 ≤ xg_92 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_92 k : ℝ) ≤ Chebyshev.theta ((xg_92 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_711
    · exact Work.RHContract.RegionI.thV_24
    · exact Work.RHContract.RegionI.thV_8
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
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((5437 : ℕ) : ℝ) ≤ (((2730290649157 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_717
  have hSx : (((226113965737 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 5399, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_711
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_92 k := by decide +kernel
  have hT2 : (∑ k, tg_92 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_92 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_92 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2730290649157 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_92 k))
      + ((((226113965737 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_92 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_92 (yg_92 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨92, by omega⟩ : ℚ)) (εB := (cut ⟨93, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_92 yg_92 tg_92 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2730290649157 : ℚ) / 1000000000000)) (((226113965737 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_93 : Fin 15 → ℕ := fun k => [5437, 97, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_93 : Fin 15 → ℕ := fun k => [5479, 100, 24, 11, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_93 : Fin 15 → ℚ := fun k => [((5331131630217329 : ℚ) / 1000000000000), ((83728390370717 : ℚ) / 1000000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_93 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨93, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨94, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨94, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨93, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_93 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_93 k + 1) (k.val + 1) < (cut ⟨94, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_93 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_93 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_93 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_93 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_93 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_93 ⟨1, by omega⟩ + 1 ≤ xg_93 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_93 k : ℝ) ≤ Chebyshev.theta ((xg_93 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_717
    · exact Work.RHContract.RegionI.thV_24
    · exact Work.RHContract.RegionI.thV_8
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
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((5479 : ℕ) : ℝ) ≤ (((2731389660379 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_723
  have hSx : (((452228135669 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 5437, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_717
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_93 k := by decide +kernel
  have hT2 : (∑ k, tg_93 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_93 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_93 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2731389660379 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_93 k))
      + ((((452228135669 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_93 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_93 (yg_93 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨93, by omega⟩ : ℚ)) (εB := (cut ⟨94, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_93 yg_93 tg_93 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2731389660379 : ℚ) / 1000000000000)) (((452228135669 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_94 : Fin 15 → ℕ := fun k => [5479, 97, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_94 : Fin 15 → ℕ := fun k => [5521, 101, 24, 11, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_94 : Fin 15 → ℚ := fun k => [((5382762828748499 : ℚ) / 1000000000000), ((83728390370717 : ℚ) / 1000000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_94 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨94, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨95, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨95, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨94, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_94 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_94 k + 1) (k.val + 1) < (cut ⟨95, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_94 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_94 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_94 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_94 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_94 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_94 ⟨1, by omega⟩ + 1 ≤ xg_94 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_94 k : ℝ) ≤ Chebyshev.theta ((xg_94 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_723
    · exact Work.RHContract.RegionI.thV_24
    · exact Work.RHContract.RegionI.thV_8
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
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((5521 : ℕ) : ℝ) ≤ (((683119887847 : ℚ) / 250000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_729
  have hSx : (((90445667387 : ℚ) / 200000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 5479, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_723
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_94 k := by decide +kernel
  have hT2 : (∑ k, tg_94 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_94 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_94 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((683119887847 : ℚ) / 250000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_94 k))
      + ((((90445667387 : ℚ) / 200000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_94 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_94 (yg_94 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨94, by omega⟩ : ℚ)) (εB := (cut ⟨95, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_94 yg_94 tg_94 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((683119887847 : ℚ) / 250000000000)) (((90445667387 : ℚ) / 200000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_95 : Fin 15 → ℕ := fun k => [5521, 101, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_95 : Fin 15 → ℕ := fun k => [5573, 101, 24, 11, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_95 : Fin 15 → ℚ := fun k => [((2717222005895053 : ℚ) / 500000000000), ((44171755442999 : ℚ) / 500000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_95 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨95, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨96, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨96, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨95, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_95 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_95 k + 1) (k.val + 1) < (cut ⟨96, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_95 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_95 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_95 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_95 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_95 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_95 ⟨1, by omega⟩ + 1 ≤ xg_95 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_95 k : ℝ) ≤ Chebyshev.theta ((xg_95 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_729
    · exact Work.RHContract.RegionI.thV_25
    · exact Work.RHContract.RegionI.thV_8
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
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((5573 : ℕ) : ℝ) ≤ (((2733560092151 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_735
  have hSx : (((452228534873 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 5521, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_729
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_95 k := by decide +kernel
  have hT2 : (∑ k, tg_95 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_95 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_95 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2733560092151 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_95 k))
      + ((((452228534873 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_95 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_95 (yg_95 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨95, by omega⟩ : ℚ)) (εB := (cut ⟨96, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_95 yg_95 tg_95 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2733560092151 : ℚ) / 1000000000000)) (((452228534873 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_96 : Fin 15 → ℕ := fun k => [5573, 101, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_96 : Fin 15 → ℕ := fun k => [5651, 102, 24, 11, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_96 : Fin 15 → ℚ := fun k => [((5486176902187729 : ℚ) / 1000000000000), ((44171755442999 : ℚ) / 500000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_96 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨96, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨97, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨97, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨96, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_96 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_96 k + 1) (k.val + 1) < (cut ⟨97, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_96 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_96 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_96 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_96 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_96 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_96 ⟨1, by omega⟩ + 1 ≤ xg_96 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_96 k : ℝ) ≤ Chebyshev.theta ((xg_96 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_735
    · exact Work.RHContract.RegionI.thV_25
    · exact Work.RHContract.RegionI.thV_8
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
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((5651 : ℕ) : ℝ) ≤ (((2734804737001 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_742
  have hSx : (((56528591179 : ℚ) / 125000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 5573, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_735
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_96 k := by decide +kernel
  have hT2 : (∑ k, tg_96 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_96 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_96 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2734804737001 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_96 k))
      + ((((56528591179 : ℚ) / 125000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_96 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_96 (yg_96 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨96, by omega⟩ : ℚ)) (εB := (cut ⟨97, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_96 yg_96 tg_96 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2734804737001 : ℚ) / 1000000000000)) (((56528591179 : ℚ) / 125000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_97 : Fin 15 → ℕ := fun k => [5651, 101, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_97 : Fin 15 → ℕ := fun k => [5693, 102, 24, 11, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_97 : Fin 15 → ℚ := fun k => [((5546621305632847 : ℚ) / 1000000000000), ((44171755442999 : ℚ) / 500000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_97 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨97, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨98, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨98, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨97, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_97 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_97 k + 1) (k.val + 1) < (cut ⟨98, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_97 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_97 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_97 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_97 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_97 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_97 ⟨1, by omega⟩ + 1 ≤ xg_97 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_97 k : ℝ) ≤ Chebyshev.theta ((xg_97 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_742
    · exact Work.RHContract.RegionI.thV_25
    · exact Work.RHContract.RegionI.thV_8
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
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((5693 : ℕ) : ℝ) ≤ (((342004877291 : ℚ) / 125000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_749
  have hSx : (((4522289507 : ℚ) / 10000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 5651, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_742
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_97 k := by decide +kernel
  have hT2 : (∑ k, tg_97 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_97 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_97 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((342004877291 : ℚ) / 125000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_97 k))
      + ((((4522289507 : ℚ) / 10000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_97 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_97 (yg_97 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨97, by omega⟩ : ℚ)) (εB := (cut ⟨98, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_97 yg_97 tg_97 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((342004877291 : ℚ) / 125000000000)) (((4522289507 : ℚ) / 10000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_98 : Fin 15 → ℕ := fun k => [5693, 101, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_98 : Fin 15 → ℕ := fun k => [5743, 103, 24, 11, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_98 : Fin 15 → ℚ := fun k => [((5607124183689491 : ℚ) / 1000000000000), ((44171755442999 : ℚ) / 500000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_98 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨98, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨99, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨99, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨98, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_98 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_98 k + 1) (k.val + 1) < (cut ⟨99, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_98 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_98 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_98 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_98 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_98 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_98 ⟨1, by omega⟩ + 1 ≤ xg_98 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_98 k : ℝ) ≤ Chebyshev.theta ((xg_98 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_749
    · exact Work.RHContract.RegionI.thV_25
    · exact Work.RHContract.RegionI.thV_8
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
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((5743 : ℕ) : ℝ) ≤ (((2737087153129 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_755
  have hSx : (((56528646037 : ℚ) / 125000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 5693, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_749
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_98 k := by decide +kernel
  have hT2 : (∑ k, tg_98 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_98 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_98 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2737087153129 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_98 k))
      + ((((56528646037 : ℚ) / 125000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_98 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_98 (yg_98 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨98, by omega⟩ : ℚ)) (εB := (cut ⟨99, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_98 yg_98 tg_98 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2737087153129 : ℚ) / 1000000000000)) (((56528646037 : ℚ) / 125000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_99 : Fin 15 → ℕ := fun k => [5743, 103, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_99 : Fin 15 → ℕ := fun k => [5813, 103, 24, 11, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_99 : Fin 15 → ℚ := fun k => [((2829519873416683 : ℚ) / 500000000000), ((92978239872667 : ℚ) / 1000000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_99 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨99, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨100, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨100, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨99, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_99 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_99 k + 1) (k.val + 1) < (cut ⟨100, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_99 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_99 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_99 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_99 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_99 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_99 ⟨1, by omega⟩ + 1 ≤ xg_99 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_99 k : ℝ) ≤ Chebyshev.theta ((xg_99 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_755
    · exact Work.RHContract.RegionI.thV_26
    · exact Work.RHContract.RegionI.thV_8
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
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((5813 : ℕ) : ℝ) ≤ (((2738296461819 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_762
  have hSx : (((452229351359 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 5743, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_755
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_99 k := by decide +kernel
  have hT2 : (∑ k, tg_99 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_99 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_99 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2738296461819 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_99 k))
      + ((((452229351359 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_99 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_99 (yg_99 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨99, by omega⟩ : ℚ)) (εB := (cut ⟨100, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_99 yg_99 tg_99 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2738296461819 : ℚ) / 1000000000000)) (((452229351359 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_100 : Fin 15 → ℕ := fun k => [5813, 103, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_100 : Fin 15 → ℕ := fun k => [5857, 104, 24, 11, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_100 : Fin 15 → ℚ := fun k => [((5719685709107391 : ℚ) / 1000000000000), ((92978239872667 : ℚ) / 1000000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_100 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨100, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨101, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨101, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨100, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_100 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_100 k + 1) (k.val + 1) < (cut ⟨101, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_100 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_100 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_100 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_100 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_100 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_100 ⟨1, by omega⟩ + 1 ≤ xg_100 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_100 k : ℝ) ≤ Chebyshev.theta ((xg_100 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_762
    · exact Work.RHContract.RegionI.thV_26
    · exact Work.RHContract.RegionI.thV_8
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
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((5857 : ℕ) : ℝ) ≤ (((2739494994493 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_769
  have hSx : (((452229560239 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 5813, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_762
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_100 k := by decide +kernel
  have hT2 : (∑ k, tg_100 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_100 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_100 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2739494994493 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_100 k))
      + ((((452229560239 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_100 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_100 (yg_100 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨100, by omega⟩ : ℚ)) (εB := (cut ⟨101, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_100 yg_100 tg_100 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2739494994493 : ℚ) / 1000000000000)) (((452229560239 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_101 : Fin 15 → ℕ := fun k => [5857, 103, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_101 : Fin 15 → ℕ := fun k => [5903, 104, 24, 11, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_101 : Fin 15 → ℚ := fun k => [((2890197147564063 : ℚ) / 500000000000), ((92978239872667 : ℚ) / 1000000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_101 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨101, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨102, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨102, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨101, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_101 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_101 k + 1) (k.val + 1) < (cut ⟨102, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_101 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_101 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_101 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_101 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_101 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_101 ⟨1, by omega⟩ + 1 ≤ xg_101 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_101 k : ℝ) ≤ Chebyshev.theta ((xg_101 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_769
    · exact Work.RHContract.RegionI.thV_26
    · exact Work.RHContract.RegionI.thV_8
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
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((5903 : ℕ) : ℝ) ≤ (((1370342832973 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_776
  have hSx : (((113057441353 : ℚ) / 250000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 5857, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_769
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_101 k := by decide +kernel
  have hT2 : (∑ k, tg_101 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_101 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_101 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1370342832973 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_101 k))
      + ((((113057441353 : ℚ) / 250000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_101 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_101 (yg_101 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨101, by omega⟩ : ℚ)) (εB := (cut ⟨102, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_101 yg_101 tg_101 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1370342832973 : ℚ) / 500000000000)) (((113057441353 : ℚ) / 250000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_102 : Fin 15 → ℕ := fun k => [5903, 103, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_102 : Fin 15 → ℕ := fun k => [6007, 105, 24, 11, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_102 : Fin 15 → ℚ := fun k => [((5841148947926351 : ℚ) / 1000000000000), ((92978239872667 : ℚ) / 1000000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_102 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨102, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨103, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨103, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨102, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_102 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_102 k + 1) (k.val + 1) < (cut ⟨103, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_102 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_102 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_102 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_102 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_102 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_102 ⟨1, by omega⟩ + 1 ≤ xg_102 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_102 k : ℝ) ≤ Chebyshev.theta ((xg_102 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_776
    · exact Work.RHContract.RegionI.thV_26
    · exact Work.RHContract.RegionI.thV_8
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
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((6007 : ℕ) : ℝ) ≤ (((2741860375471 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_783
  have hSx : (((452229967903 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 5903, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_776
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_102 k := by decide +kernel
  have hT2 : (∑ k, tg_102 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_102 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_102 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2741860375471 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_102 k))
      + ((((452229967903 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_102 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_102 (yg_102 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨102, by omega⟩ : ℚ)) (εB := (cut ⟨103, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_102 yg_102 tg_102 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2741860375471 : ℚ) / 1000000000000)) (((452229967903 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_103 : Fin 15 → ℕ := fun k => [6007, 103, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_103 : Fin 15 → ℕ := fun k => [6067, 105, 25, 11, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_103 : Fin 15 → ℚ := fun k => [((5901998135866567 : ℚ) / 1000000000000), ((92978239872667 : ℚ) / 1000000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_103 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨103, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨104, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨104, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨103, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_103 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_103 k + 1) (k.val + 1) < (cut ⟨104, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_103 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_103 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_103 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_103 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_103 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_103 ⟨1, by omega⟩ + 1 ≤ xg_103 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_103 k : ℝ) ≤ Chebyshev.theta ((xg_103 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_783
    · exact Work.RHContract.RegionI.thV_26
    · exact Work.RHContract.RegionI.thV_8
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
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((6067 : ℕ) : ℝ) ≤ (((2743019228661 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_790
  have hSx : (((452230165007 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 6007, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_783
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_103 k := by decide +kernel
  have hT2 : (∑ k, tg_103 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_103 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_103 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2743019228661 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_103 k))
      + ((((452230165007 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_103 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_103 (yg_103 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨103, by omega⟩ : ℚ)) (εB := (cut ⟨104, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_103 yg_103 tg_103 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2743019228661 : ℚ) / 1000000000000)) (((452230165007 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_104 : Fin 15 → ℕ := fun k => [6067, 103, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_104 : Fin 15 → ℕ := fun k => [6121, 106, 25, 11, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_104 : Fin 15 → ℚ := fun k => [((2981471191702761 : ℚ) / 500000000000), ((92978239872667 : ℚ) / 1000000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_104 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨104, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨105, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨105, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨104, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_104 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_104 k + 1) (k.val + 1) < (cut ⟨105, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_104 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_104 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_104 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_104 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_104 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_104 ⟨1, by omega⟩ + 1 ≤ xg_104 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_104 k : ℝ) ≤ Chebyshev.theta ((xg_104 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_790
    · exact Work.RHContract.RegionI.thV_26
    · exact Work.RHContract.RegionI.thV_8
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
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((6121 : ℕ) : ℝ) ≤ (((686041939869 : ℚ) / 250000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_797
  have hSx : (((226115178411 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 6067, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_790
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_104 k := by decide +kernel
  have hT2 : (∑ k, tg_104 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_104 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_104 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((686041939869 : ℚ) / 250000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_104 k))
      + ((((226115178411 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_104 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_104 (yg_104 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨104, by omega⟩ : ℚ)) (εB := (cut ⟨105, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_104 yg_104 tg_104 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((686041939869 : ℚ) / 250000000000)) (((226115178411 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_105 : Fin 15 → ℕ := fun k => [6121, 103, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_105 : Fin 15 → ℕ := fun k => [6173, 106, 25, 11, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_105 : Fin 15 → ℚ := fun k => [((6023949255223807 : ℚ) / 1000000000000), ((92978239872667 : ℚ) / 1000000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_105 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨105, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨106, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨106, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨105, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_105 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_105 k + 1) (k.val + 1) < (cut ⟨106, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_105 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_105 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_105 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_105 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_105 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_105 ⟨1, by omega⟩ + 1 ≤ xg_105 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_105 k : ℝ) ≤ Chebyshev.theta ((xg_105 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_797
    · exact Work.RHContract.RegionI.thV_26
    · exact Work.RHContract.RegionI.thV_8
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
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((6173 : ℕ) : ℝ) ≤ (((2745143613233 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_803
  have hSx : (((226115272617 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 6121, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_797
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_105 k := by decide +kernel
  have hT2 : (∑ k, tg_105 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_105 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_105 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2745143613233 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_105 k))
      + ((((226115272617 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_105 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_105 (yg_105 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨105, by omega⟩ : ℚ)) (εB := (cut ⟨106, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_105 yg_105 tg_105 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2745143613233 : ℚ) / 1000000000000)) (((226115272617 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_106 : Fin 15 → ℕ := fun k => [6173, 103, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_106 : Fin 15 → ℕ := fun k => [6221, 107, 25, 11, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_106 : Fin 15 → ℚ := fun k => [((1215258701056441 : ℚ) / 200000000000), ((92978239872667 : ℚ) / 1000000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_106 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨106, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨107, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨107, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨106, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_106 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_106 k + 1) (k.val + 1) < (cut ⟨107, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_106 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_106 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_106 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_106 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_106 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_106 ⟨1, by omega⟩ + 1 ≤ xg_106 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_106 k : ℝ) ≤ Chebyshev.theta ((xg_106 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_803
    · exact Work.RHContract.RegionI.thV_26
    · exact Work.RHContract.RegionI.thV_8
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
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((6221 : ℕ) : ℝ) ≤ (((2746110187963 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_809
  have hSx : (((452230703921 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 6173, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_803
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_106 k := by decide +kernel
  have hT2 : (∑ k, tg_106 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_106 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_106 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2746110187963 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_106 k))
      + ((((452230703921 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_106 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_106 (yg_106 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨106, by omega⟩ : ℚ)) (εB := (cut ⟨107, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_106 yg_106 tg_106 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2746110187963 : ℚ) / 1000000000000)) (((452230703921 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_107 : Fin 15 → ℕ := fun k => [6221, 107, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_107 : Fin 15 → ℕ := fun k => [6277, 107, 25, 11, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_107 : Fin 15 → ℚ := fun k => [((1225739012666093 : ℚ) / 200000000000), ((97651068705569 : ℚ) / 1000000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_107 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨107, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨108, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨108, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨107, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_107 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_107 k + 1) (k.val + 1) < (cut ⟨108, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_107 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_107 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_107 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_107 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_107 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_107 ⟨1, by omega⟩ + 1 ≤ xg_107 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_107 k : ℝ) ≤ Chebyshev.theta ((xg_107 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_809
    · exact Work.RHContract.RegionI.thV_27
    · exact Work.RHContract.RegionI.thV_8
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
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((6277 : ℕ) : ℝ) ≤ (((274722867351 : ℚ) / 100000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_816
  have hSx : (((113057714901 : ℚ) / 250000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 6221, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_809
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_107 k := by decide +kernel
  have hT2 : (∑ k, tg_107 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_107 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_107 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((274722867351 : ℚ) / 100000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_107 k))
      + ((((113057714901 : ℚ) / 250000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_107 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_107 (yg_107 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨107, by omega⟩ : ℚ)) (εB := (cut ⟨108, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_107 yg_107 tg_107 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((274722867351 : ℚ) / 100000000000)) (((113057714901 : ℚ) / 250000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_108 : Fin 15 → ℕ := fun k => [6277, 107, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_108 : Fin 15 → ℕ := fun k => [6329, 108, 25, 11, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_108 : Fin 15 → ℚ := fun k => [((6189887472400033 : ℚ) / 1000000000000), ((97651068705569 : ℚ) / 1000000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_108 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨108, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨109, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨109, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨108, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_108 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_108 k + 1) (k.val + 1) < (cut ⟨109, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_108 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_108 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_108 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_108 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_108 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_108 ⟨1, by omega⟩ + 1 ≤ xg_108 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_108 k : ℝ) ≤ Chebyshev.theta ((xg_108 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_816
    · exact Work.RHContract.RegionI.thV_27
    · exact Work.RHContract.RegionI.thV_8
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
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((6329 : ℕ) : ℝ) ≤ (((549667638449 : ℚ) / 200000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_823
  have hSx : (((28264439893 : ℚ) / 62500000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 6277, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_816
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_108 k := by decide +kernel
  have hT2 : (∑ k, tg_108 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_108 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_108 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((549667638449 : ℚ) / 200000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_108 k))
      + ((((28264439893 : ℚ) / 62500000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_108 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_108 (yg_108 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨108, by omega⟩ : ℚ)) (εB := (cut ⟨109, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_108 yg_108 tg_108 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((549667638449 : ℚ) / 200000000000)) (((28264439893 : ℚ) / 62500000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_109 : Fin 15 → ℕ := fun k => [6329, 107, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_109 : Fin 15 → ℕ := fun k => [6373, 108, 25, 11, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_109 : Fin 15 → ℚ := fun k => [((6251136217161457 : ℚ) / 1000000000000), ((97651068705569 : ℚ) / 1000000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_109 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨109, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨110, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨110, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨109, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_109 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_109 k + 1) (k.val + 1) < (cut ⟨110, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_109 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_109 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_109 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_109 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_109 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_109 ⟨1, by omega⟩ + 1 ≤ xg_109 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_109 k : ℝ) ≤ Chebyshev.theta ((xg_109 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_823
    · exact Work.RHContract.RegionI.thV_27
    · exact Work.RHContract.RegionI.thV_8
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
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((6373 : ℕ) : ℝ) ≤ (((2749439579553 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_830
  have hSx : (((452231214119 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 6329, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_823
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_109 k := by decide +kernel
  have hT2 : (∑ k, tg_109 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_109 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_109 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2749439579553 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_109 k))
      + ((((452231214119 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_109 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_109 (yg_109 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨109, by omega⟩ : ℚ)) (εB := (cut ⟨110, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_109 yg_109 tg_109 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2749439579553 : ℚ) / 1000000000000)) (((452231214119 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_110 : Fin 15 → ℕ := fun k => [6373, 107, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_110 : Fin 15 → ℕ := fun k => [6449, 109, 25, 12, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_110 : Fin 15 → ℚ := fun k => [((78905455549939 : ℚ) / 12500000000), ((97651068705569 : ℚ) / 1000000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_110 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨110, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨111, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨111, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨110, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_110 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_110 k + 1) (k.val + 1) < (cut ⟨111, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_110 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_110 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_110 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_110 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_110 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_110 ⟨1, by omega⟩ + 1 ≤ xg_110 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_110 k : ℝ) ≤ Chebyshev.theta ((xg_110 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_830
    · exact Work.RHContract.RegionI.thV_27
    · exact Work.RHContract.RegionI.thV_8
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
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((6449 : ℕ) : ℝ) ≤ (((2750375654621 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_836
  have hSx : (((452231387381 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 6373, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_830
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_110 k := by decide +kernel
  have hT2 : (∑ k, tg_110 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_110 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_110 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2750375654621 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_110 k))
      + ((((452231387381 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_110 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_110 (yg_110 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨110, by omega⟩ : ℚ)) (εB := (cut ⟨111, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_110 yg_110 tg_110 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2750375654621 : ℚ) / 1000000000000)) (((452231387381 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_111 : Fin 15 → ℕ := fun k => [6449, 109, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_111 : Fin 15 → ℕ := fun k => [6529, 109, 25, 12, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_111 : Fin 15 → ℚ := fun k => [((636503040070287 : ℚ) / 100000000000), ((51171208293119 : ℚ) / 500000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_111 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨111, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨112, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨112, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨111, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_111 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_111 k + 1) (k.val + 1) < (cut ⟨112, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_111 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_111 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_111 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_111 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_111 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_111 ⟨1, by omega⟩ + 1 ≤ xg_111 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_111 k : ℝ) ≤ Chebyshev.theta ((xg_111 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_836
    · exact Work.RHContract.RegionI.thV_28
    · exact Work.RHContract.RegionI.thV_8
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
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((6529 : ℕ) : ℝ) ≤ (((2751454693953 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_843
  have hSx : (((452231533397 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 6449, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_836
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_111 k := by decide +kernel
  have hT2 : (∑ k, tg_111 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_111 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_111 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2751454693953 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_111 k))
      + ((((452231533397 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_111 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_111 (yg_111 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨111, by omega⟩ : ℚ)) (εB := (cut ⟨112, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_111 yg_111 tg_111 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2751454693953 : ℚ) / 1000000000000)) (((452231533397 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_112 : Fin 15 → ℕ := fun k => [6529, 109, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_112 : Fin 15 → ℕ := fun k => [6577, 110, 25, 12, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_112 : Fin 15 → ℚ := fun k => [((3213237078480097 : ℚ) / 500000000000), ((51171208293119 : ℚ) / 500000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_112 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨112, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨113, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨113, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨112, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_112 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_112 k + 1) (k.val + 1) < (cut ⟨113, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_112 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_112 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_112 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_112 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_112 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_112 ⟨1, by omega⟩ + 1 ≤ xg_112 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_112 k : ℝ) ≤ Chebyshev.theta ((xg_112 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_843
    · exact Work.RHContract.RegionI.thV_28
    · exact Work.RHContract.RegionI.thV_8
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
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((6577 : ℕ) : ℝ) ≤ (((2752521595643 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_850
  have hSx : (((452231699703 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 6529, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_843
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_112 k := by decide +kernel
  have hT2 : (∑ k, tg_112 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_112 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_112 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2752521595643 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_112 k))
      + ((((452231699703 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_112 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_112 (yg_112 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨112, by omega⟩ : ℚ)) (εB := (cut ⟨113, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_112 yg_112 tg_112 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2752521595643 : ℚ) / 1000000000000)) (((452231699703 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_113 : Fin 15 → ℕ := fun k => [6577, 109, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_113 : Fin 15 → ℕ := fun k => [6659, 111, 25, 12, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_113 : Fin 15 → ℚ := fun k => [((3243998522831067 : ℚ) / 500000000000), ((51171208293119 : ℚ) / 500000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_113 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨113, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨114, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨114, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨113, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_113 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_113 k + 1) (k.val + 1) < (cut ⟨114, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_113 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_113 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_113 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_113 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_113 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_113 ⟨1, by omega⟩ + 1 ≤ xg_113 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_113 k : ℝ) ≤ Chebyshev.theta ((xg_113 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_850
    · exact Work.RHContract.RegionI.thV_28
    · exact Work.RHContract.RegionI.thV_8
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
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((6659 : ℕ) : ℝ) ≤ (((550715750467 : ℚ) / 200000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_857
  have hSx : (((452231862287 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 6577, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_850
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_113 k := by decide +kernel
  have hT2 : (∑ k, tg_113 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_113 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_113 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((550715750467 : ℚ) / 200000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_113 k))
      + ((((452231862287 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_113 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_113 (yg_113 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨113, by omega⟩ : ℚ)) (εB := (cut ⟨114, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_113 yg_113 tg_113 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((550715750467 : ℚ) / 200000000000)) (((452231862287 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_114 : Fin 15 → ℕ := fun k => [6659, 109, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_114 : Fin 15 → ℕ := fun k => [6703, 111, 25, 12, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_114 : Fin 15 → ℚ := fun k => [((3274792104338641 : ℚ) / 500000000000), ((51171208293119 : ℚ) / 500000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_114 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨114, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨115, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨115, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨114, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_114 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_114 k + 1) (k.val + 1) < (cut ⟨115, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_114 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_114 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_114 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_114 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_114 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_114 ⟨1, by omega⟩ + 1 ≤ xg_114 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_114 k : ℝ) ≤ Chebyshev.theta ((xg_114 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_857
    · exact Work.RHContract.RegionI.thV_28
    · exact Work.RHContract.RegionI.thV_8
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
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((6703 : ℕ) : ℝ) ≤ (((1377312955487 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_864
  have hSx : (((113058005479 : ℚ) / 250000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 6659, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_857
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_114 k := by decide +kernel
  have hT2 : (∑ k, tg_114 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_114 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_114 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1377312955487 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_114 k))
      + ((((113058005479 : ℚ) / 250000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_114 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_114 (yg_114 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨114, by omega⟩ : ℚ)) (εB := (cut ⟨115, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_114 yg_114 tg_114 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1377312955487 : ℚ) / 500000000000)) (((113058005479 : ℚ) / 250000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_115 : Fin 15 → ℕ := fun k => [6703, 109, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_115 : Fin 15 → ℕ := fun k => [6779, 112, 26, 12, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_115 : Fin 15 → ℚ := fun k => [((3305618921361859 : ℚ) / 500000000000), ((51171208293119 : ℚ) / 500000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_115 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨115, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨116, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨116, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨115, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_115 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_115 k + 1) (k.val + 1) < (cut ⟨116, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_115 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_115 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_115 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_115 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_115 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_115 ⟨1, by omega⟩ + 1 ≤ xg_115 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_115 k : ℝ) ≤ Chebyshev.theta ((xg_115 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_864
    · exact Work.RHContract.RegionI.thV_28
    · exact Work.RHContract.RegionI.thV_8
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
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((6779 : ℕ) : ℝ) ≤ (((1377832057121 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_871
  have hSx : (((452232178539 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 6703, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_864
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_115 k := by decide +kernel
  have hT2 : (∑ k, tg_115 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_115 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_115 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1377832057121 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_115 k))
      + ((((452232178539 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_115 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_115 (yg_115 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨115, by omega⟩ : ℚ)) (εB := (cut ⟨116, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_115 yg_115 tg_115 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1377832057121 : ℚ) / 500000000000)) (((452232178539 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_116 : Fin 15 → ℕ := fun k => [6779, 109, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_116 : Fin 15 → ℕ := fun k => [6829, 112, 26, 12, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_116 : Fin 15 → ℚ := fun k => [((1668237905353491 : ℚ) / 250000000000), ((51171208293119 : ℚ) / 500000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_116 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨116, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨117, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨117, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨116, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_116 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_116 k + 1) (k.val + 1) < (cut ⟨117, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_116 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_116 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_116 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_116 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_116 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_116 ⟨1, by omega⟩ + 1 ≤ xg_116 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_116 k : ℝ) ≤ Chebyshev.theta ((xg_116 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_871
    · exact Work.RHContract.RegionI.thV_28
    · exact Work.RHContract.RegionI.thV_8
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
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((6829 : ℕ) : ℝ) ≤ (((2756692593369 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_878
  have hSx : (((226116166247 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 6779, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_871
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_116 k := by decide +kernel
  have hT2 : (∑ k, tg_116 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_116 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_116 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2756692593369 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_116 k))
      + ((((226116166247 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_116 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_116 (yg_116 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨116, by omega⟩ : ℚ)) (εB := (cut ⟨117, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_116 yg_116 tg_116 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2756692593369 : ℚ) / 1000000000000)) (((226116166247 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_117 : Fin 15 → ℕ := fun k => [6829, 109, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_117 : Fin 15 → ℕ := fun k => [6883, 112, 26, 12, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_117 : Fin 15 → ℚ := fun k => [((6734731250342653 : ℚ) / 1000000000000), ((51171208293119 : ℚ) / 500000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_117 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨117, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨118, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨118, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨117, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_117 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_117 k + 1) (k.val + 1) < (cut ⟨118, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_117 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_117 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_117 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_117 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_117 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_117 ⟨1, by omega⟩ + 1 ≤ xg_117 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_117 k : ℝ) ≤ Chebyshev.theta ((xg_117 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_878
    · exact Work.RHContract.RegionI.thV_28
    · exact Work.RHContract.RegionI.thV_8
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
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((6883 : ℕ) : ℝ) ≤ (((1378856572689 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_885
  have hSx : (((452232483579 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 6829, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_878
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_117 k := by decide +kernel
  have hT2 : (∑ k, tg_117 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_117 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_117 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1378856572689 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_117 k))
      + ((((452232483579 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_117 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_117 (yg_117 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨117, by omega⟩ : ℚ)) (εB := (cut ⟨118, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_117 yg_117 tg_117 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1378856572689 : ℚ) / 500000000000)) (((452232483579 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_118 : Fin 15 → ℕ := fun k => [6883, 109, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_118 : Fin 15 → ℕ := fun k => [6949, 113, 26, 12, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_118 : Fin 15 → ℚ := fun k => [((6796565032496193 : ℚ) / 1000000000000), ((51171208293119 : ℚ) / 500000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_118 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨118, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨119, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨119, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨118, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_118 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_118 k + 1) (k.val + 1) < (cut ⟨119, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_118 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_118 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_118 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_118 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_118 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_118 ⟨1, by omega⟩ + 1 ≤ xg_118 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_118 k : ℝ) ≤ Chebyshev.theta ((xg_118 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_885
    · exact Work.RHContract.RegionI.thV_28
    · exact Work.RHContract.RegionI.thV_8
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
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((6949 : ℕ) : ℝ) ≤ (((2758580058039 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_891
  have hSx : (((56529079043 : ℚ) / 125000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 6883, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_885
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_118 k := by decide +kernel
  have hT2 : (∑ k, tg_118 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_118 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_118 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2758580058039 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_118 k))
      + ((((56529079043 : ℚ) / 125000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_118 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_118 (yg_118 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨118, by omega⟩ : ℚ)) (εB := (cut ⟨119, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_118 yg_118 tg_118 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2758580058039 : ℚ) / 1000000000000)) (((56529079043 : ℚ) / 125000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_119 : Fin 15 → ℕ := fun k => [6949, 113, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_119 : Fin 15 → ℕ := fun k => [6991, 113, 26, 12, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_119 : Fin 15 → ℚ := fun k => [((428101217511613 : ℚ) / 62500000000), ((10706980440339 : ℚ) / 100000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_119 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨119, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨120, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨120, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨119, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_119 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_119 k + 1) (k.val + 1) < (cut ⟨120, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_119 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_119 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_119 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_119 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_119 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_119 ⟨1, by omega⟩ + 1 ≤ xg_119 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_119 k : ℝ) ≤ Chebyshev.theta ((xg_119 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_891
    · exact Work.RHContract.RegionI.thV_29
    · exact Work.RHContract.RegionI.thV_8
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
    · exact Work.RHContract.RegionI.thV_0
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((6991 : ℕ) : ℝ) ≤ (((689896011417 : ℚ) / 250000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_898
  have hSx : (((22611637879 : ℚ) / 50000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 6949, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_891
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_119 k := by decide +kernel
  have hT2 : (∑ k, tg_119 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_119 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_119 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((689896011417 : ℚ) / 250000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_119 k))
      + ((((22611637879 : ℚ) / 50000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_119 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_119 (yg_119 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨119, by omega⟩ : ℚ)) (εB := (cut ⟨120, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_119 yg_119 tg_119 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((689896011417 : ℚ) / 250000000000)) (((22611637879 : ℚ) / 50000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

end

end Work.RHContract.A.RegionI
