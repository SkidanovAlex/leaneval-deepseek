import Mathlib
import Submission.Work.RHContract.A.RegionI.Core
import Submission.Work.RHContract.A.RegionI.blockCert
import Submission.Work.RHContract.A.RegionI.Data11
import Submission.Work.RHContract.A.RegionI.Cuts

/-!  Region I: group certificates.  GENERATED FILE. -/

open scoped BigOperators

namespace Work.RHContract.A.RegionI

noncomputable section

private def xg_120 : Fin 15 → ℕ := fun k => [6991, 113, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_120 : Fin 15 → ℕ := fun k => [7043, 114, 26, 12, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_120 : Fin 15 → ℚ := fun k => [((1727891947675949 : ℚ) / 250000000000), ((10706980440339 : ℚ) / 100000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_120 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨120, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨121, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨121, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨120, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_120 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_120 k + 1) (k.val + 1) < (cut ⟨121, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_120 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_120 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_120 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_120 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_120 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_120 ⟨1, by omega⟩ + 1 ≤ xg_120 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_120 k : ℝ) ≤ Chebyshev.theta ((xg_120 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_898
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((7043 : ℕ) : ℝ) ≤ (((110423251737 : ℚ) / 40000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_905
  have hSx : (((226116450777 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 6991, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_898
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_120 k := by decide +kernel
  have hT2 : (∑ k, tg_120 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_120 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_120 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((110423251737 : ℚ) / 40000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_120 k))
      + ((((226116450777 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_120 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_120 (yg_120 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨120, by omega⟩ : ℚ)) (εB := (cut ⟨121, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_120 yg_120 tg_120 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((110423251737 : ℚ) / 40000000000)) (((226116450777 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_121 : Fin 15 → ℕ := fun k => [7043, 113, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_121 : Fin 15 → ℕ := fun k => [7127, 114, 26, 12, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_121 : Fin 15 → ℚ := fun k => [((6973563258646493 : ℚ) / 1000000000000), ((10706980440339 : ℚ) / 100000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_121 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨121, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨122, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨122, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨121, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_121 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_121 k + 1) (k.val + 1) < (cut ⟨122, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_121 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_121 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_121 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_121 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_121 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_121 ⟨1, by omega⟩ + 1 ≤ xg_121 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_121 k : ℝ) ≤ Chebyshev.theta ((xg_121 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_905
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((7127 : ℕ) : ℝ) ≤ (((552313597081 : ℚ) / 200000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_912
  have hSx : (((226116521801 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 7043, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_905
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_121 k := by decide +kernel
  have hT2 : (∑ k, tg_121 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_121 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_121 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((552313597081 : ℚ) / 200000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_121 k))
      + ((((226116521801 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_121 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_121 (yg_121 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨121, by omega⟩ : ℚ)) (εB := (cut ⟨122, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_121 yg_121 tg_121 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((552313597081 : ℚ) / 200000000000)) (((226116521801 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_122 : Fin 15 → ℕ := fun k => [7127, 113, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_122 : Fin 15 → ℕ := fun k => [7207, 115, 26, 12, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_122 : Fin 15 → ℚ := fun k => [((7035633234662011 : ℚ) / 1000000000000), ((10706980440339 : ℚ) / 100000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_122 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨122, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨123, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨123, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨122, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_122 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_122 k + 1) (k.val + 1) < (cut ⟨123, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_122 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_122 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_122 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_122 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_122 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_122 ⟨1, by omega⟩ + 1 ≤ xg_122 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_122 k : ℝ) ≤ Chebyshev.theta ((xg_122 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_912
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((7207 : ℕ) : ℝ) ≤ (((86329503207 : ℚ) / 31250000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_919
  have hSx : (((452233182661 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 7127, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_912
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_122 k := by decide +kernel
  have hT2 : (∑ k, tg_122 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_122 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_122 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((86329503207 : ℚ) / 31250000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_122 k))
      + ((((452233182661 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_122 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_122 (yg_122 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨122, by omega⟩ : ℚ)) (εB := (cut ⟨123, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_122 yg_122 tg_122 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((86329503207 : ℚ) / 31250000000)) (((452233182661 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_123 : Fin 15 → ℕ := fun k => [7207, 113, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_123 : Fin 15 → ℕ := fun k => [7247, 115, 26, 12, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_123 : Fin 15 → ℚ := fun k => [((3548889315746213 : ℚ) / 500000000000), ((10706980440339 : ℚ) / 100000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_123 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨123, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨124, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨124, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨123, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_123 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_123 k + 1) (k.val + 1) < (cut ⟨124, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_123 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_123 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_123 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_123 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_123 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_123 ⟨1, by omega⟩ + 1 ≤ xg_123 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_123 k : ℝ) ≤ Chebyshev.theta ((xg_123 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_919
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((7247 : ℕ) : ℝ) ≤ (((552702514309 : ℚ) / 200000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_926
  have hSx : (((226116659377 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 7207, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_919
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_123 k := by decide +kernel
  have hT2 : (∑ k, tg_123 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_123 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_123 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((552702514309 : ℚ) / 200000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_123 k))
      + ((((226116659377 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_123 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_123 (yg_123 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨123, by omega⟩ : ℚ)) (εB := (cut ⟨124, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_123 yg_123 tg_123 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((552702514309 : ℚ) / 200000000000)) (((226116659377 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_124 : Fin 15 → ℕ := fun k => [7247, 113, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_124 : Fin 15 → ℕ := fun k => [7331, 116, 26, 12, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_124 : Fin 15 → ℚ := fun k => [((1789994764499829 : ℚ) / 250000000000), ((10706980440339 : ℚ) / 100000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_124 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨124, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨125, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨125, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨124, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_124 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_124 k + 1) (k.val + 1) < (cut ⟨125, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_124 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_124 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_124 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_124 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_124 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_124 ⟨1, by omega⟩ + 1 ≤ xg_124 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_124 k : ℝ) ≤ Chebyshev.theta ((xg_124 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_926
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((7331 : ℕ) : ℝ) ≤ (((2764471532983 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_933
  have hSx : (((226116726361 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 7247, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_926
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_124 k := by decide +kernel
  have hT2 : (∑ k, tg_124 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_124 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_124 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2764471532983 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_124 k))
      + ((((226116726361 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_124 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_124 (yg_124 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨124, by omega⟩ : ℚ)) (εB := (cut ⟨125, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_124 yg_124 tg_124 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2764471532983 : ℚ) / 1000000000000)) (((226116726361 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_125 : Fin 15 → ℕ := fun k => [7331, 113, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_125 : Fin 15 → ℕ := fun k => [7417, 117, 26, 12, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_125 : Fin 15 → ℚ := fun k => [((7222248564397967 : ℚ) / 1000000000000), ((10706980440339 : ℚ) / 100000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_125 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨125, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨126, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨126, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨125, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_125 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_125 k + 1) (k.val + 1) < (cut ⟨126, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_125 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_125 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_125 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_125 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_125 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_125 ⟨1, by omega⟩ + 1 ≤ xg_125 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_125 k : ℝ) ≤ Chebyshev.theta ((xg_125 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_933
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((7417 : ℕ) : ℝ) ≤ (((2765420802701 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_940
  have hSx : (((226116792037 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 7331, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_933
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_125 k := by decide +kernel
  have hT2 : (∑ k, tg_125 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_125 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_125 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2765420802701 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_125 k))
      + ((((226116792037 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_125 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_125 (yg_125 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨125, by omega⟩ : ℚ)) (εB := (cut ⟨126, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_125 yg_125 tg_125 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2765420802701 : ℚ) / 1000000000000)) (((226116792037 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_126 : Fin 15 → ℕ := fun k => [7417, 113, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_126 : Fin 15 → ℕ := fun k => [7487, 117, 26, 12, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_126 : Fin 15 → ℚ := fun k => [((7284589192310137 : ℚ) / 1000000000000), ((10706980440339 : ℚ) / 100000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_126 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨126, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨127, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨127, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨126, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_126 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_126 k + 1) (k.val + 1) < (cut ⟨127, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_126 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_126 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_126 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_126 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_126 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_126 ⟨1, by omega⟩ + 1 ≤ xg_126 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_126 k : ℝ) ≤ Chebyshev.theta ((xg_126 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_940
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((7487 : ℕ) : ℝ) ≤ (((1383179379803 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_947
  have hSx : (((90446742557 : ℚ) / 200000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 7417, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_940
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_126 k := by decide +kernel
  have hT2 : (∑ k, tg_126 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_126 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_126 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1383179379803 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_126 k))
      + ((((90446742557 : ℚ) / 200000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_126 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_126 (yg_126 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨126, by omega⟩ : ℚ)) (εB := (cut ⟨127, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_126 yg_126 tg_126 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1383179379803 : ℚ) / 500000000000)) (((90446742557 : ℚ) / 200000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_127 : Fin 15 → ℕ := fun k => [7487, 113, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_127 : Fin 15 → ℕ := fun k => [7537, 118, 26, 12, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_127 : Fin 15 → ℚ := fun k => [((7347013697882179 : ℚ) / 1000000000000), ((10706980440339 : ℚ) / 100000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_127 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨127, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨128, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨128, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨127, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_127 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_127 k + 1) (k.val + 1) < (cut ⟨128, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_127 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_127 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_127 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_127 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_127 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_127 ⟨1, by omega⟩ + 1 ≤ xg_127 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_127 k : ℝ) ≤ Chebyshev.theta ((xg_127 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_947
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((7537 : ℕ) : ℝ) ≤ (((2767290366931 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_954
  have hSx : (((226116919223 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 7487, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_947
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_127 k := by decide +kernel
  have hT2 : (∑ k, tg_127 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_127 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_127 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2767290366931 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_127 k))
      + ((((226116919223 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_127 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_127 (yg_127 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨127, by omega⟩ : ℚ)) (εB := (cut ⟨128, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_127 yg_127 tg_127 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2767290366931 : ℚ) / 1000000000000)) (((226116919223 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_128 : Fin 15 → ℕ := fun k => [7537, 113, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_128 : Fin 15 → ℕ := fun k => [7577, 118, 27, 12, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_128 : Fin 15 → ℚ := fun k => [((926185718032487 : ℚ) / 125000000000), ((10706980440339 : ℚ) / 100000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_128 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨128, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨129, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨129, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨128, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_128 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_128 k + 1) (k.val + 1) < (cut ⟨129, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_128 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_128 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_128 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_128 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_128 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_128 ⟨1, by omega⟩ + 1 ≤ xg_128 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_128 k : ℝ) ≤ Chebyshev.theta ((xg_128 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_954
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((7577 : ℕ) : ℝ) ≤ (((692054146041 : ℚ) / 250000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_961
  have hSx : (((113058490603 : ℚ) / 250000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 7537, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_954
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_128 k := by decide +kernel
  have hT2 : (∑ k, tg_128 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_128 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_128 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((692054146041 : ℚ) / 250000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_128 k))
      + ((((113058490603 : ℚ) / 250000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_128 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_128 (yg_128 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨128, by omega⟩ : ℚ)) (εB := (cut ⟨129, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_128 yg_128 tg_128 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((692054146041 : ℚ) / 250000000000)) (((113058490603 : ℚ) / 250000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_129 : Fin 15 → ℕ := fun k => [7577, 113, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_129 : Fin 15 → ℕ := fun k => [7639, 119, 27, 12, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_129 : Fin 15 → ℚ := fun k => [((373599920011179 : ℚ) / 50000000000), ((10706980440339 : ℚ) / 100000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_129 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨129, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨130, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨130, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨129, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_129 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_129 k + 1) (k.val + 1) < (cut ⟨130, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_129 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_129 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_129 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_129 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_129 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_129 ⟨1, by omega⟩ + 1 ≤ xg_129 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_129 k : ℝ) ≤ Chebyshev.theta ((xg_129 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_961
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((7639 : ℕ) : ℝ) ≤ (((2769137131699 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_968
  have hSx : (((452234084947 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 7577, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_961
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_129 k := by decide +kernel
  have hT2 : (∑ k, tg_129 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_129 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_129 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2769137131699 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_129 k))
      + ((((452234084947 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_129 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_129 (yg_129 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨129, by omega⟩ : ℚ)) (εB := (cut ⟨130, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_129 yg_129 tg_129 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2769137131699 : ℚ) / 1000000000000)) (((452234084947 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_130 : Fin 15 → ℕ := fun k => [7639, 113, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_130 : Fin 15 → ℕ := fun k => [7691, 119, 27, 12, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_130 : Fin 15 → ℚ := fun k => [((470909627831331 : ℚ) / 62500000000), ((10706980440339 : ℚ) / 100000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_130 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨130, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨131, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨131, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨130, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_130 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_130 k + 1) (k.val + 1) < (cut ⟨131, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_130 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_130 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_130 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_130 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_130 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_130 ⟨1, by omega⟩ + 1 ≤ xg_130 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_130 k : ℝ) ≤ Chebyshev.theta ((xg_130 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_968
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((7691 : ℕ) : ℝ) ≤ (((1385024895691 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_975
  have hSx : (((452234205987 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 7639, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_968
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_130 k := by decide +kernel
  have hT2 : (∑ k, tg_130 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_130 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_130 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1385024895691 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_130 k))
      + ((((452234205987 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_130 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_130 (yg_130 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨130, by omega⟩ : ℚ)) (εB := (cut ⟨131, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_130 yg_130 tg_130 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1385024895691 : ℚ) / 500000000000)) (((452234205987 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_131 : Fin 15 → ℕ := fun k => [7691, 113, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_131 : Fin 15 → ℕ := fun k => [7753, 119, 27, 12, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_131 : Fin 15 → ℚ := fun k => [((7597169922402369 : ℚ) / 1000000000000), ((10706980440339 : ℚ) / 100000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_131 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨131, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨132, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨132, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨131, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_131 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_131 k + 1) (k.val + 1) < (cut ⟨132, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_131 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_131 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_131 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_131 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_131 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_131 ⟨1, by omega⟩ + 1 ≤ xg_131 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_131 k : ℝ) ≤ Chebyshev.theta ((xg_131 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_975
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((7753 : ℕ) : ℝ) ≤ (((346369525619 : ℚ) / 125000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_982
  have hSx : (((2826464531 : ℚ) / 6250000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 7691, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_975
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_131 k := by decide +kernel
  have hT2 : (∑ k, tg_131 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_131 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_131 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((346369525619 : ℚ) / 125000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_131 k))
      + ((((2826464531 : ℚ) / 6250000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_131 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_131 (yg_131 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨131, by omega⟩ : ℚ)) (εB := (cut ⟨132, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_131 yg_131 tg_131 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((346369525619 : ℚ) / 125000000000)) (((2826464531 : ℚ) / 6250000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_132 : Fin 15 → ℕ := fun k => [7753, 113, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_132 : Fin 15 → ℕ := fun k => [7829, 120, 27, 12, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_132 : Fin 15 → ℚ := fun k => [((1531966773931309 : ℚ) / 200000000000), ((10706980440339 : ℚ) / 100000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_132 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨132, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨133, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨133, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨132, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_132 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_132 k + 1) (k.val + 1) < (cut ⟨133, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_132 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_132 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_132 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_132 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_132 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_132 ⟨1, by omega⟩ + 1 ≤ xg_132 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_132 k : ℝ) ≤ Chebyshev.theta ((xg_132 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_982
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((7829 : ℕ) : ℝ) ≤ (((1385927126093 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_989
  have hSx : (((56529305289 : ℚ) / 125000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 7753, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_982
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_132 k := by decide +kernel
  have hT2 : (∑ k, tg_132 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_132 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_132 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1385927126093 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_132 k))
      + ((((56529305289 : ℚ) / 125000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_132 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_132 (yg_132 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨132, by omega⟩ : ℚ)) (εB := (cut ⟨133, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_132 yg_132 tg_132 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1385927126093 : ℚ) / 500000000000)) (((56529305289 : ℚ) / 125000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_133 : Fin 15 → ℕ := fun k => [7829, 113, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_133 : Fin 15 → ℕ := fun k => [7883, 120, 27, 12, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_133 : Fin 15 → ℚ := fun k => [((7722562747835667 : ℚ) / 1000000000000), ((10706980440339 : ℚ) / 100000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_133 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨133, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨134, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨134, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨133, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_133 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_133 k + 1) (k.val + 1) < (cut ⟨134, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_133 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_133 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_133 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_133 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_133 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_133 ⟨1, by omega⟩ + 1 ≤ xg_133 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_133 k : ℝ) ≤ Chebyshev.theta ((xg_133 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_989
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((7883 : ℕ) : ℝ) ≤ (((21662062811 : ℚ) / 7812500000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_996
  have hSx : (((45223455751 : ℚ) / 100000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 7829, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_989
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_133 k := by decide +kernel
  have hT2 : (∑ k, tg_133 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_133 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_133 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((21662062811 : ℚ) / 7812500000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_133 k))
      + ((((45223455751 : ℚ) / 100000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_133 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_133 (yg_133 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨133, by omega⟩ : ℚ)) (εB := (cut ⟨134, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_133 yg_133 tg_133 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((21662062811 : ℚ) / 7812500000)) (((45223455751 : ℚ) / 100000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_134 : Fin 15 → ℕ := fun k => [7883, 113, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_134 : Fin 15 → ℕ := fun k => [7949, 121, 27, 12, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_134 : Fin 15 → ℚ := fun k => [((1946339067350739 : ℚ) / 250000000000), ((10706980440339 : ℚ) / 100000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_134 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨134, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨135, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨135, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨134, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_134 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_134 k + 1) (k.val + 1) < (cut ⟨135, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_134 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_134 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_134 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_134 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_134 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_134 ⟨1, by omega⟩ + 1 ≤ xg_134 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_134 k : ℝ) ≤ Chebyshev.theta ((xg_134 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_996
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((7949 : ℕ) : ℝ) ≤ (((554725482323 : ℚ) / 200000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1003
  have hSx : (((113058667649 : ℚ) / 250000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 7883, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_996
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_134 k := by decide +kernel
  have hT2 : (∑ k, tg_134 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_134 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_134 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((554725482323 : ℚ) / 200000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_134 k))
      + ((((113058667649 : ℚ) / 250000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_134 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_134 (yg_134 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨134, by omega⟩ : ℚ)) (εB := (cut ⟨135, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_134 yg_134 tg_134 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((554725482323 : ℚ) / 200000000000)) (((113058667649 : ℚ) / 250000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_135 : Fin 15 → ℕ := fun k => [7949, 113, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_135 : Fin 15 → ℕ := fun k => [8039, 122, 27, 12, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_135 : Fin 15 → ℚ := fun k => [((1962050111619731 : ℚ) / 250000000000), ((10706980440339 : ℚ) / 100000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_135 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨135, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨136, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨136, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨135, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_135 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_135 k + 1) (k.val + 1) < (cut ⟨136, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_135 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_135 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_135 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_135 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_135 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_135 ⟨1, by omega⟩ + 1 ≤ xg_135 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_135 k : ℝ) ≤ Chebyshev.theta ((xg_135 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1003
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((8039 : ℕ) : ℝ) ≤ (((554900548677 : ℚ) / 200000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1010
  have hSx : (((452234782059 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 7949, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1003
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_135 k := by decide +kernel
  have hT2 : (∑ k, tg_135 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_135 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_135 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((554900548677 : ℚ) / 200000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_135 k))
      + ((((452234782059 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_135 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_135 (yg_135 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨135, by omega⟩ : ℚ)) (εB := (cut ⟨136, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_135 yg_135 tg_135 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((554900548677 : ℚ) / 200000000000)) (((452234782059 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_136 : Fin 15 → ℕ := fun k => [8039, 113, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_136 : Fin 15 → ℕ := fun k => [8093, 122, 27, 12, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_136 : Fin 15 → ℚ := fun k => [((395555432678989 : ℚ) / 50000000000), ((10706980440339 : ℚ) / 100000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_136 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨136, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨137, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨137, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨136, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_136 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_136 k + 1) (k.val + 1) < (cut ⟨137, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_136 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_136 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_136 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_136 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_136 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_136 ⟨1, by omega⟩ + 1 ≤ xg_136 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_136 k : ℝ) ≤ Chebyshev.theta ((xg_136 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1010
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((8093 : ℕ) : ℝ) ≤ (((173460598807 : ℚ) / 62500000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1017
  have hSx : (((452234891501 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 8039, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1010
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_136 k := by decide +kernel
  have hT2 : (∑ k, tg_136 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_136 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_136 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((173460598807 : ℚ) / 62500000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_136 k))
      + ((((452234891501 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_136 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_136 (yg_136 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨136, by omega⟩ : ℚ)) (εB := (cut ⟨137, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_136 yg_136 tg_136 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((173460598807 : ℚ) / 62500000000)) (((452234891501 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_137 : Fin 15 → ℕ := fun k => [8093, 113, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_137 : Fin 15 → ℕ := fun k => [8167, 123, 27, 12, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_137 : Fin 15 → ℚ := fun k => [((3987042541153877 : ℚ) / 500000000000), ((10706980440339 : ℚ) / 100000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_137 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨137, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨138, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨138, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨137, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_137 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_137 k + 1) (k.val + 1) < (cut ⟨138, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_137 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_137 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_137 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_137 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_137 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_137 ⟨1, by omega⟩ + 1 ≤ xg_137 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_137 k : ℝ) ≤ Chebyshev.theta ((xg_137 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1017
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((8167 : ℕ) : ℝ) ≤ (((1388115196379 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1024
  have hSx : (((452234998829 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 8093, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1017
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_137 k := by decide +kernel
  have hT2 : (∑ k, tg_137 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_137 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_137 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1388115196379 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_137 k))
      + ((((452234998829 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_137 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_137 (yg_137 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨137, by omega⟩ : ℚ)) (εB := (cut ⟨138, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_137 yg_137 tg_137 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1388115196379 : ℚ) / 500000000000)) (((452234998829 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_138 : Fin 15 → ℕ := fun k => [8167, 113, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_138 : Fin 15 → ℕ := fun k => [8231, 123, 27, 12, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_138 : Fin 15 → ℚ := fun k => [((4018555178101383 : ℚ) / 500000000000), ((10706980440339 : ℚ) / 100000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_138 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨138, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨139, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨139, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨138, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_138 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_138 k + 1) (k.val + 1) < (cut ⟨139, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_138 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_138 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_138 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_138 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_138 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_138 ⟨1, by omega⟩ + 1 ≤ xg_138 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_138 k : ℝ) ≤ Chebyshev.theta ((xg_138 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1024
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((8231 : ℕ) : ℝ) ≤ (((2777083796817 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1031
  have hSx : (((45223510467 : ℚ) / 100000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 8167, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1024
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_138 k := by decide +kernel
  have hT2 : (∑ k, tg_138 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_138 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_138 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2777083796817 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_138 k))
      + ((((45223510467 : ℚ) / 100000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_138 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_138 (yg_138 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨138, by omega⟩ : ℚ)) (εB := (cut ⟨139, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_138 yg_138 tg_138 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2777083796817 : ℚ) / 1000000000000)) (((45223510467 : ℚ) / 100000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_139 : Fin 15 → ℕ := fun k => [8231, 113, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_139 : Fin 15 → ℕ := fun k => [8287, 124, 27, 12, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_139 : Fin 15 → ℚ := fun k => [((506262257459259 : ℚ) / 62500000000), ((10706980440339 : ℚ) / 100000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_139 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨139, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨140, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨140, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨139, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_139 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_139 k + 1) (k.val + 1) < (cut ⟨140, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_139 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_139 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_139 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_139 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_139 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_139 ⟨1, by omega⟩ + 1 ≤ xg_139 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_139 k : ℝ) ≤ Chebyshev.theta ((xg_139 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1031
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((8287 : ℕ) : ℝ) ≤ (((2777931530131 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1038
  have hSx : (((452235208697 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 8231, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1031
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_139 k := by decide +kernel
  have hT2 : (∑ k, tg_139 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_139 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_139 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2777931530131 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_139 k))
      + ((((452235208697 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_139 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_139 (yg_139 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨139, by omega⟩ : ℚ)) (εB := (cut ⟨140, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_139 yg_139 tg_139 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2777931530131 : ℚ) / 1000000000000)) (((452235208697 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_140 : Fin 15 → ℕ := fun k => [8287, 113, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_140 : Fin 15 → ℕ := fun k => [8353, 124, 27, 12, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_140 : Fin 15 → ℚ := fun k => [((8163328543823499 : ℚ) / 1000000000000), ((10706980440339 : ℚ) / 100000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_140 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨140, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨141, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨141, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨140, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_140 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_140 k + 1) (k.val + 1) < (cut ⟨141, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_140 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_140 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_140 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_140 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_140 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_140 ⟨1, by omega⟩ + 1 ≤ xg_140 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_140 k : ℝ) ≤ Chebyshev.theta ((xg_140 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1038
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((8353 : ℕ) : ℝ) ≤ (((2778773640639 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1045
  have hSx : (((226117655673 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 8287, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1038
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_140 k := by decide +kernel
  have hT2 : (∑ k, tg_140 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_140 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_140 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2778773640639 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_140 k))
      + ((((226117655673 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_140 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_140 (yg_140 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨140, by omega⟩ : ℚ)) (εB := (cut ⟨141, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_140 yg_140 tg_140 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2778773640639 : ℚ) / 1000000000000)) (((226117655673 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_141 : Fin 15 → ℕ := fun k => [8353, 113, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_141 : Fin 15 → ℕ := fun k => [8423, 125, 28, 12, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_141 : Fin 15 → ℚ := fun k => [((514156722052449 : ℚ) / 62500000000), ((10706980440339 : ℚ) / 100000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_141 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨141, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨142, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨142, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨141, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_141 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_141 k + 1) (k.val + 1) < (cut ⟨142, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_141 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_141 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_141 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_141 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_141 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_141 ⟨1, by omega⟩ + 1 ≤ xg_141 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_141 k : ℝ) ≤ Chebyshev.theta ((xg_141 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1045
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((8423 : ℕ) : ℝ) ≤ (((2779608065119 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1052
  have hSx : (((226117706319 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 8353, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1045
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_141 k := by decide +kernel
  have hT2 : (∑ k, tg_141 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_141 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_141 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2779608065119 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_141 k))
      + ((((226117706319 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_141 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_141 (yg_141 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨141, by omega⟩ : ℚ)) (εB := (cut ⟨142, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_141 yg_141 tg_141 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2779608065119 : ℚ) / 1000000000000)) (((226117706319 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_142 : Fin 15 → ℕ := fun k => [8423, 113, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_142 : Fin 15 → ℕ := fun k => [8501, 125, 28, 12, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_142 : Fin 15 → ℚ := fun k => [((8289750742568579 : ℚ) / 1000000000000), ((10706980440339 : ℚ) / 100000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_142 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨142, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨143, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨143, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨142, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_142 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_142 k + 1) (k.val + 1) < (cut ⟨143, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_142 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_142 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_142 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_142 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_142 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_142 ⟨1, by omega⟩ + 1 ≤ xg_142 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_142 k : ℝ) ≤ Chebyshev.theta ((xg_142 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1052
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((8501 : ℕ) : ℝ) ≤ (((695109029177 : ℚ) / 250000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1059
  have hSx : (((452235512091 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 8423, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1052
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_142 k := by decide +kernel
  have hT2 : (∑ k, tg_142 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_142 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_142 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((695109029177 : ℚ) / 250000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_142 k))
      + ((((452235512091 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_142 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_142 (yg_142 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨142, by omega⟩ : ℚ)) (εB := (cut ⟨143, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_142 yg_142 tg_142 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((695109029177 : ℚ) / 250000000000)) (((452235512091 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_143 : Fin 15 → ℕ := fun k => [8501, 113, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_143 : Fin 15 → ℕ := fun k => [8563, 126, 28, 12, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_143 : Fin 15 → ℚ := fun k => [((8353047599500423 : ℚ) / 1000000000000), ((10706980440339 : ℚ) / 100000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_143 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨143, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨144, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨144, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨143, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_143 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_143 k + 1) (k.val + 1) < (cut ⟨144, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_143 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_143 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_143 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_143 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_143 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_143 ⟨1, by omega⟩ + 1 ≤ xg_143 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_143 k : ℝ) ≤ Chebyshev.theta ((xg_143 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1059
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((8563 : ℕ) : ℝ) ≤ (((22250050777 : ℚ) / 8000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1066
  have hSx : (((452235610029 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 8501, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1059
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_143 k := by decide +kernel
  have hT2 : (∑ k, tg_143 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_143 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_143 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((22250050777 : ℚ) / 8000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_143 k))
      + ((((452235610029 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_143 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_143 (yg_143 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨143, by omega⟩ : ℚ)) (εB := (cut ⟨144, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_143 yg_143 tg_143 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((22250050777 : ℚ) / 8000000000)) (((452235610029 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_144 : Fin 15 → ℕ := fun k => [8563, 113, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_144 : Fin 15 → ℕ := fun k => [8627, 126, 28, 12, 8, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_144 : Fin 15 → ℚ := fun k => [((4208205434267157 : ℚ) / 500000000000), ((10706980440339 : ℚ) / 100000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_144 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨144, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨145, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨145, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨144, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_144 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_144 k + 1) (k.val + 1) < (cut ⟨145, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_144 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_144 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_144 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_144 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_144 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_144 ⟨1, by omega⟩ + 1 ≤ xg_144 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_144 k : ℝ) ≤ Chebyshev.theta ((xg_144 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1066
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((8627 : ℕ) : ℝ) ≤ (((2782070230077 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1073
  have hSx : (((3617885649 : ℚ) / 8000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 8563, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1066
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_144 k := by decide +kernel
  have hT2 : (∑ k, tg_144 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_144 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_144 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2782070230077 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_144 k))
      + ((((3617885649 : ℚ) / 8000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_144 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_144 (yg_144 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨144, by omega⟩ : ℚ)) (εB := (cut ⟨145, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_144 yg_144 tg_144 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2782070230077 : ℚ) / 1000000000000)) (((3617885649 : ℚ) / 8000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_145 : Fin 15 → ℕ := fun k => [8627, 113, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_145 : Fin 15 → ℕ := fun k => [8681, 126, 28, 12, 8, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_145 : Fin 15 → ℚ := fun k => [((4239914260456207 : ℚ) / 500000000000), ((10706980440339 : ℚ) / 100000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_145 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨145, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨146, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨146, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨145, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_145 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_145 k + 1) (k.val + 1) < (cut ⟨146, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_145 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_145 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_145 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_145 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_145 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_145 ⟨1, by omega⟩ + 1 ≤ xg_145 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_145 k : ℝ) ≤ Chebyshev.theta ((xg_145 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1073
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((8681 : ℕ) : ℝ) ≤ (((347859845971 : ℚ) / 125000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1080
  have hSx : (((22611790037 : ℚ) / 50000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 8627, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1073
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_145 k := by decide +kernel
  have hT2 : (∑ k, tg_145 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_145 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_145 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((347859845971 : ℚ) / 125000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_145 k))
      + ((((22611790037 : ℚ) / 50000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_145 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_145 (yg_145 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨145, by omega⟩ : ℚ)) (εB := (cut ⟨146, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_145 yg_145 tg_145 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((347859845971 : ℚ) / 125000000000)) (((22611790037 : ℚ) / 50000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_146 : Fin 15 → ℕ := fun k => [8681, 113, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_146 : Fin 15 → ℕ := fun k => [8731, 127, 28, 12, 8, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_146 : Fin 15 → ℚ := fun k => [((8543292294325011 : ℚ) / 1000000000000), ((10706980440339 : ℚ) / 100000000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_146 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨146, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨147, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨147, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨146, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_146 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_146 k + 1) (k.val + 1) < (cut ⟨147, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_146 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_146 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_146 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_146 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_146 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_146 ⟨1, by omega⟩ + 1 ≤ xg_146 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_146 k : ℝ) ≤ Chebyshev.theta ((xg_146 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1080
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((8731 : ℕ) : ℝ) ≤ (((2783682740431 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1087
  have hSx : (((113058973529 : ℚ) / 250000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 8681, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1080
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_146 k := by decide +kernel
  have hT2 : (∑ k, tg_146 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_146 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_146 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2783682740431 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_146 k))
      + ((((113058973529 : ℚ) / 250000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_146 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_146 (yg_146 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨146, by omega⟩ : ℚ)) (εB := (cut ⟨147, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_146 yg_146 tg_146 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2783682740431 : ℚ) / 1000000000000)) (((113058973529 : ℚ) / 250000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_147 : Fin 15 → ℕ := fun k => [8731, 127, 23, 11, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_147 : Fin 15 → ℕ := fun k => [8783, 127, 28, 13, 8, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_147 : Fin 15 → ℚ := fun k => [((2151698923304769 : ℚ) / 250000000000), ((3497312234009 : ℚ) / 31250000000), ((19223098693887 : ℚ) / 1000000000000), ((309800112047 : ℚ) / 40000000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_147 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨147, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨148, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨148, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨147, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_147 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_147 k + 1) (k.val + 1) < (cut ⟨148, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_147 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_147 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_147 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_147 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_147 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_147 ⟨1, by omega⟩ + 1 ≤ xg_147 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_147 k : ℝ) ≤ Chebyshev.theta ((xg_147 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1087
    · exact Work.RHContract.RegionI.thV_30
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((8783 : ℕ) : ℝ) ≤ (((556896424681 : ℚ) / 200000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1094
  have hSx : (((226117993221 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 8731, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1087
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_147 k := by decide +kernel
  have hT2 : (∑ k, tg_147 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_147 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_147 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((556896424681 : ℚ) / 200000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_147 k))
      + ((((226117993221 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_147 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_147 (yg_147 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨147, by omega⟩ : ℚ)) (εB := (cut ⟨148, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_147 yg_147 tg_147 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((556896424681 : ℚ) / 200000000000)) (((226117993221 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_148 : Fin 15 → ℕ := fun k => [8783, 127, 23, 13, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_148 : Fin 15 → ℕ := fun k => [8849, 128, 28, 13, 8, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_148 : Fin 15 → ℚ := fun k => [((4335169584753479 : ℚ) / 500000000000), ((3497312234009 : ℚ) / 31250000000), ((19223098693887 : ℚ) / 1000000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_148 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨148, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨149, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨149, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨148, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_148 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_148 k + 1) (k.val + 1) < (cut ⟨149, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_148 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_148 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_148 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_148 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_148 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_148 ⟨1, by omega⟩ + 1 ≤ xg_148 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_148 k : ℝ) ≤ Chebyshev.theta ((xg_148 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1094
    · exact Work.RHContract.RegionI.thV_30
    · exact Work.RHContract.RegionI.thV_8
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((8849 : ℕ) : ℝ) ≤ (((139269430797 : ℚ) / 50000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1102
  have hSx : (((226118038859 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 8783, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1094
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_148 k := by decide +kernel
  have hT2 : (∑ k, tg_148 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_148 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_148 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((139269430797 : ℚ) / 50000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_148 k))
      + ((((226118038859 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_148 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_148 (yg_148 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨148, by omega⟩ : ℚ)) (εB := (cut ⟨149, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_148 yg_148 tg_148 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((139269430797 : ℚ) / 50000000000)) (((226118038859 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_149 : Fin 15 → ℕ := fun k => [8849, 127, 23, 13, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_149 : Fin 15 → ℕ := fun k => [8933, 128, 28, 13, 8, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_149 : Fin 15 → ℚ := fun k => [((1092877823598581 : ℚ) / 125000000000), ((3497312234009 : ℚ) / 31250000000), ((19223098693887 : ℚ) / 1000000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_149 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨149, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨150, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨150, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨149, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_149 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_149 k + 1) (k.val + 1) < (cut ⟨150, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_149 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_149 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_149 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_149 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_149 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_149 ⟨1, by omega⟩ + 1 ≤ xg_149 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_149 k : ℝ) ≤ Chebyshev.theta ((xg_149 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1102
    · exact Work.RHContract.RegionI.thV_30
    · exact Work.RHContract.RegionI.thV_8
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((8933 : ℕ) : ℝ) ≤ (((1393144053927 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1110
  have hSx : (((226118090209 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 8849, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1102
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_149 k := by decide +kernel
  have hT2 : (∑ k, tg_149 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_149 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_149 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1393144053927 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_149 k))
      + ((((226118090209 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_149 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_149 (yg_149 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨149, by omega⟩ : ℚ)) (εB := (cut ⟨150, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_149 yg_149 tg_149 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1393144053927 : ℚ) / 500000000000)) (((226118090209 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_150 : Fin 15 → ℕ := fun k => [8933, 127, 23, 13, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_150 : Fin 15 → ℕ := fun k => [9007, 129, 28, 13, 8, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_150 : Fin 15 → ℚ := fun k => [((8815768055336033 : ℚ) / 1000000000000), ((3497312234009 : ℚ) / 31250000000), ((19223098693887 : ℚ) / 1000000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_150 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨150, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨151, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨151, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨150, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_150 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_150 k + 1) (k.val + 1) < (cut ⟨151, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_150 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_150 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_150 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_150 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_150 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_150 ⟨1, by omega⟩ + 1 ≤ xg_150 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_150 k : ℝ) ≤ Chebyshev.theta ((xg_150 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1110
    · exact Work.RHContract.RegionI.thV_30
    · exact Work.RHContract.RegionI.thV_8
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((9007 : ℕ) : ℝ) ≤ (((1393589751703 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1118
  have hSx : (((452236281539 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 8933, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1110
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_150 k := by decide +kernel
  have hT2 : (∑ k, tg_150 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_150 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_150 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1393589751703 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_150 k))
      + ((((452236281539 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_150 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_150 (yg_150 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨150, by omega⟩ : ℚ)) (εB := (cut ⟨151, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_150 yg_150 tg_150 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1393589751703 : ℚ) / 500000000000)) (((452236281539 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_151 : Fin 15 → ℕ := fun k => [9007, 127, 23, 13, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_151 : Fin 15 → ℕ := fun k => [9067, 129, 28, 13, 8, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_151 : Fin 15 → ℚ := fun k => [((888858583776571 : ℚ) / 100000000000), ((3497312234009 : ℚ) / 31250000000), ((19223098693887 : ℚ) / 1000000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_151 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨151, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨152, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨152, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨151, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_151 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_151 k + 1) (k.val + 1) < (cut ⟨152, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_151 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_151 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_151 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_151 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_151 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_151 ⟨1, by omega⟩ + 1 ≤ xg_151 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_151 k : ℝ) ≤ Chebyshev.theta ((xg_151 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1118
    · exact Work.RHContract.RegionI.thV_30
    · exact Work.RHContract.RegionI.thV_8
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((9067 : ℕ) : ℝ) ≤ (((2788064609909 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1126
  have hSx : (((28264773803 : ℚ) / 62500000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 9007, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1118
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_151 k := by decide +kernel
  have hT2 : (∑ k, tg_151 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_151 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_151 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2788064609909 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_151 k))
      + ((((28264773803 : ℚ) / 62500000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_151 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_151 (yg_151 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨151, by omega⟩ : ℚ)) (εB := (cut ⟨152, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_151 yg_151 tg_151 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2788064609909 : ℚ) / 1000000000000)) (((28264773803 : ℚ) / 62500000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_152 : Fin 15 → ℕ := fun k => [9067, 127, 23, 13, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_152 : Fin 15 → ℕ := fun k => [9157, 130, 28, 13, 8, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_152 : Fin 15 → ℚ := fun k => [((1792292050165983 : ℚ) / 200000000000), ((3497312234009 : ℚ) / 31250000000), ((19223098693887 : ℚ) / 1000000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_152 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨152, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨153, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨153, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨152, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_152 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_152 k + 1) (k.val + 1) < (cut ⟨153, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_152 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_152 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_152 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_152 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_152 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_152 ⟨1, by omega⟩ + 1 ≤ xg_152 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_152 k : ℝ) ≤ Chebyshev.theta ((xg_152 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1126
    · exact Work.RHContract.RegionI.thV_30
    · exact Work.RHContract.RegionI.thV_8
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((9157 : ℕ) : ℝ) ≤ (((348617659901 : ℚ) / 125000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1134
  have hSx : (((11305911969 : ℚ) / 25000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 9067, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1126
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_152 k := by decide +kernel
  have hT2 : (∑ k, tg_152 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_152 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_152 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((348617659901 : ℚ) / 125000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_152 k))
      + ((((11305911969 : ℚ) / 25000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_152 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_152 (yg_152 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨152, by omega⟩ : ℚ)) (εB := (cut ⟨153, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_152 yg_152 tg_152 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((348617659901 : ℚ) / 125000000000)) (((11305911969 : ℚ) / 25000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_153 : Fin 15 → ℕ := fun k => [9157, 127, 23, 13, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_153 : Fin 15 → ℕ := fun k => [9221, 130, 28, 13, 8, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_153 : Fin 15 → ℚ := fun k => [((9034411290075479 : ℚ) / 1000000000000), ((3497312234009 : ℚ) / 31250000000), ((19223098693887 : ℚ) / 1000000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_153 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨153, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨154, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨154, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨153, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_153 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_153 k + 1) (k.val + 1) < (cut ⟨154, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_153 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_153 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_153 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_153 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_153 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_153 ⟨1, by omega⟩ + 1 ≤ xg_153 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_153 k : ℝ) ≤ Chebyshev.theta ((xg_153 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1134
    · exact Work.RHContract.RegionI.thV_30
    · exact Work.RHContract.RegionI.thV_8
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((9221 : ℕ) : ℝ) ≤ (((557962335163 : ℚ) / 200000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1142
  have hSx : (((452236574813 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 9157, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1134
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_153 k := by decide +kernel
  have hT2 : (∑ k, tg_153 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_153 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_153 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((557962335163 : ℚ) / 200000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_153 k))
      + ((((452236574813 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_153 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_153 (yg_153 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨153, by omega⟩ : ℚ)) (εB := (cut ⟨154, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_153 yg_153 tg_153 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((557962335163 : ℚ) / 200000000000)) (((452236574813 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_154 : Fin 15 → ℕ := fun k => [9221, 127, 23, 13, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_154 : Fin 15 → ℕ := fun k => [9283, 131, 28, 13, 8, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_154 : Fin 15 → ℚ := fun k => [((9107419766640957 : ℚ) / 1000000000000), ((3497312234009 : ℚ) / 31250000000), ((19223098693887 : ℚ) / 1000000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_154 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨154, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨155, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨155, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨154, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_154 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_154 k + 1) (k.val + 1) < (cut ⟨155, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_154 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_154 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_154 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_154 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_154 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_154 ⟨1, by omega⟩ + 1 ≤ xg_154 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_154 k : ℝ) ≤ Chebyshev.theta ((xg_154 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1142
    · exact Work.RHContract.RegionI.thV_30
    · exact Work.RHContract.RegionI.thV_8
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((9283 : ℕ) : ℝ) ≤ (((2790567835097 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1149
  have hSx : (((226118334749 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 9221, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1142
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_154 k := by decide +kernel
  have hT2 : (∑ k, tg_154 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_154 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_154 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2790567835097 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_154 k))
      + ((((226118334749 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_154 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_154 (yg_154 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨154, by omega⟩ : ℚ)) (εB := (cut ⟨155, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_154 yg_154 tg_154 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2790567835097 : ℚ) / 1000000000000)) (((226118334749 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_155 : Fin 15 → ℕ := fun k => [9283, 131, 23, 13, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_155 : Fin 15 → ℕ := fun k => [9343, 131, 29, 13, 8, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_155 : Fin 15 → ℚ := fun k => [((9171352343609151 : ℚ) / 1000000000000), ((116789188809669 : ℚ) / 1000000000000), ((19223098693887 : ℚ) / 1000000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_155 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨155, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨156, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨156, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨155, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_155 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_155 k + 1) (k.val + 1) < (cut ⟨156, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_155 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_155 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_155 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_155 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_155 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_155 ⟨1, by omega⟩ + 1 ≤ xg_155 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_155 k : ℝ) ≤ Chebyshev.theta ((xg_155 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1149
    · exact Work.RHContract.RegionI.thV_31
    · exact Work.RHContract.RegionI.thV_8
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((9343 : ℕ) : ℝ) ≤ (((348914830007 : ℚ) / 125000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1156
  have hSx : (((452236751169 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 9283, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1149
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_155 k := by decide +kernel
  have hT2 : (∑ k, tg_155 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_155 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_155 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((348914830007 : ℚ) / 125000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_155 k))
      + ((((452236751169 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_155 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_155 (yg_155 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨155, by omega⟩ : ℚ)) (εB := (cut ⟨156, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_155 yg_155 tg_155 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((348914830007 : ℚ) / 125000000000)) (((452236751169 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_156 : Fin 15 → ℕ := fun k => [9343, 131, 29, 13, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_156 : Fin 15 → ℕ := fun k => [9419, 132, 29, 13, 8, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_156 : Fin 15 → ℚ := fun k => [((9235334653970171 : ℚ) / 1000000000000), ((116789188809669 : ℚ) / 1000000000000), ((22590394522833 : ℚ) / 1000000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_156 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨156, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨157, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨157, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨156, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_156 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_156 k + 1) (k.val + 1) < (cut ⟨157, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_156 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_156 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_156 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_156 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_156 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_156 ⟨1, by omega⟩ + 1 ≤ xg_156 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_156 k : ℝ) ≤ Chebyshev.theta ((xg_156 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1156
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((9419 : ℕ) : ℝ) ≤ (((1396085330103 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1164
  have hSx : (((226118415843 : ℚ) / 500000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 9343, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1156
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_156 k := by decide +kernel
  have hT2 : (∑ k, tg_156 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_156 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_156 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1396085330103 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_156 k))
      + ((((226118415843 : ℚ) / 500000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_156 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_156 (yg_156 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨156, by omega⟩ : ℚ)) (εB := (cut ⟨157, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_156 yg_156 tg_156 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1396085330103 : ℚ) / 500000000000)) (((226118415843 : ℚ) / 500000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_157 : Fin 15 → ℕ := fun k => [9419, 131, 29, 13, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_157 : Fin 15 → ℕ := fun k => [9467, 132, 29, 13, 8, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_157 : Fin 15 → ℚ := fun k => [((4654256918478101 : ℚ) / 500000000000), ((116789188809669 : ℚ) / 1000000000000), ((22590394522833 : ℚ) / 1000000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_157 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨157, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨158, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨158, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨157, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_157 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_157 k + 1) (k.val + 1) < (cut ⟨158, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_157 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_157 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_157 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_157 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_157 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_157 ⟨1, by omega⟩ + 1 ≤ xg_157 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_157 k : ℝ) ≤ Chebyshev.theta ((xg_157 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1164
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((9467 : ℕ) : ℝ) ≤ (((21820451611 : ℚ) / 7812500000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1172
  have hSx : (((28264807651 : ℚ) / 62500000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 9419, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1164
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_157 k := by decide +kernel
  have hT2 : (∑ k, tg_157 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_157 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_157 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((21820451611 : ℚ) / 7812500000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_157 k))
      + ((((28264807651 : ℚ) / 62500000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_157 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_157 (yg_157 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨157, by omega⟩ : ℚ)) (εB := (cut ⟨158, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_157 yg_157 tg_157 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((21820451611 : ℚ) / 7812500000)) (((28264807651 : ℚ) / 62500000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_158 : Fin 15 → ℕ := fun k => [9467, 131, 29, 13, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_158 : Fin 15 → ℕ := fun k => [9539, 133, 29, 13, 8, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_158 : Fin 15 → ℚ := fun k => [((4690869452251047 : ℚ) / 500000000000), ((116789188809669 : ℚ) / 1000000000000), ((22590394522833 : ℚ) / 1000000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_158 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨158, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨159, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨159, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨158, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_158 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_158 k + 1) (k.val + 1) < (cut ⟨159, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_158 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_158 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_158 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_158 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_158 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_158 ⟨1, by omega⟩ + 1 ≤ xg_158 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_158 k : ℝ) ≤ Chebyshev.theta ((xg_158 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1172
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((9539 : ℕ) : ℝ) ≤ (((1396929736687 : ℚ) / 500000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1180
  have hSx : (((45223701211 : ℚ) / 100000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 9467, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1172
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_158 k := by decide +kernel
  have hT2 : (∑ k, tg_158 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_158 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_158 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((1396929736687 : ℚ) / 500000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_158 k))
      + ((((45223701211 : ℚ) / 100000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_158 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_158 (yg_158 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨158, by omega⟩ : ℚ)) (εB := (cut ⟨159, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_158 yg_158 tg_158 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((1396929736687 : ℚ) / 500000000000)) (((45223701211 : ℚ) / 100000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

private def xg_159 : Fin 15 → ℕ := fun k => [9539, 131, 29, 13, 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def yg_159 : Fin 15 → ℕ := fun k => [9629, 133, 29, 13, 8, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2].getD k.val 0
private def tg_159 : Fin 15 → ℚ := fun k => [((1891003177630033 : ℚ) / 200000000000), ((116789188809669 : ℚ) / 1000000000000), ((22590394522833 : ℚ) / 1000000000000), ((322186004933 : ℚ) / 31250000000), ((5347107529157 : ℚ) / 1000000000000), ((1700598690311 : ℚ) / 500000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((447939867177 : ℚ) / 250000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000), ((6931471803 : ℚ) / 10000000000)].getD k.val 0

theorem block_159 (ε : ℝ) (hε : 0 < ε)
    (hhi : ε ≤ ((cut ⟨159, by omega⟩ : ℚ) : ℝ))
    (hlo : ((cut ⟨160, by omega⟩ : ℚ) : ℝ) < ε)
    (hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hKtop : Work.RHContract.RegionI.Fhi 2 (15 + 1) < (cut ⟨160, by omega⟩ : ℚ) := by decide +kernel
  have hxle : ∀ k : Fin 15, (cut ⟨159, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo (xg_159 k) (k.val + 1) := by decide +kernel
  have hylo : ∀ k : Fin 15, Work.RHContract.RegionI.Fhi (yg_159 k + 1) (k.val + 1) < (cut ⟨160, by omega⟩ : ℚ) := by decide +kernel
  have hxlo : ∀ k : Fin 15, 2 ≤ xg_159 k := by decide +kernel
  have hxhi : ∀ k : Fin 15, xg_159 k < 2 ^ 20 := by decide +kernel
  have hyhi : ∀ k : Fin 15, yg_159 k + 1 < 2 ^ 20 := by decide +kernel
  have hy1k : ∀ k : Fin 15, 1 ≤ yg_159 k := by decide +kernel
  have hposy : ∀ k : Fin 15, (0 : ℚ) < Work.RHContract.RegionI.logLowQ (((yg_159 k + 1 : ℕ) : ℚ)) := by decide +kernel
  have hK1 : yg_159 ⟨1, by omega⟩ + 1 ≤ xg_159 ⟨0, by omega⟩ := by decide +kernel
  have hθv : ∀ k : Fin 15, (tg_159 k : ℝ) ≤ Chebyshev.theta ((xg_159 k : ℕ) : ℝ) := by
    intro k
    fin_cases k
    · exact Work.RHContract.RegionI.thV_1180
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
  have hLRu : Commons.NumberTheory.Mertens.logRatioSum ((9629 : ℕ) : ℝ) ≤ (((2794693183929 : ℚ) / 1000000000000 : ℚ) : ℝ) := 
    Work.RHContract.RegionI.lrU_1188
  have hSx : (((452237100647 : ℚ) / 1000000000000 : ℚ) : ℝ) ≤ ∑ p ∈ Nat.primesLE 9539, (p : ℝ) ^ (-2 : ℤ) := 
    Work.RHContract.RegionI.s2L_1180
  have hT1 : (1 : ℚ) ≤ ∑ k, tg_159 k := by decide +kernel
  have hT2 : (∑ k, tg_159 k) < 2 ^ 20 := by decide +kernel
  have hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, tg_159 k) := by decide +kernel
  have hT4 : Work.RHContract.RegionI.logLowQ (∑ k, tg_159 k) < 2 ^ 20 := by decide +kernel
  have hmarg : ((2794693183929 : ℚ) / 1000000000000) ≤ (57721 : ℚ) / 100000
      + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, tg_159 k))
      + ((((452237100647 : ℚ) / 1000000000000) : ℚ) - Work.RHContract.RegionI.s2small (yg_159 ⟨1, by omega⟩))
      + Work.RHContract.RegionI.bsmall yg_159 (yg_159 ⟨1, by omega⟩) := by decide +kernel
  exact Work.RHContract.A.RegionI.blockCert (ε := ε) (hε := hε)
    (εT := (cut ⟨159, by omega⟩ : ℚ)) (εB := (cut ⟨160, by omega⟩ : ℚ)) hhi hlo
    15 15 (by norm_num) (by norm_num) hKtop xg_159 yg_159 tg_159 hxle hylo hxlo hxhi hyhi hy1k hposy hK1 hθv 
    (((2794693183929 : ℚ) / 1000000000000)) (((452237100647 : ℚ) / 1000000000000)) hLRu hSx hT1 hT2 hT3 hT4 hmarg

end

end Work.RHContract.A.RegionI
