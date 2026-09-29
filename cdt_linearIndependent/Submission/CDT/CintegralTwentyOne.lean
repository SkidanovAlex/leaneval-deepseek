import Mathlib
import Submission.CDT.CintegralGeneral
import Submission.CDT.L2chi3Cintegral
import Submission.CDT.ZagierH
import Submission.CDT.ZagierHBC
import Submission.Commons.Analysis.Summation.sum_cintegralTwentyOne_core

/-!
# The `(Cintegral)` instance at `n = 21` via the general Beukers expansion

Module `Submission.CDT.CintegralGeneral` proves the **general-`n`** Beukers
expansion

```lean
theorem cintegralJ_eq_sum_W_gen (n : ℕ) : cintegralJ n = ∑' m : ℕ, genW n m
```

so no per-degree *analytic* module is needed any more to close the instance
`CintegralIdentityAt 21`: it suffices to
* identify the parametric summand `genW 21 ·` with the degree-`21` summand
  of the commons creative-telescoping identity
  `Commons.Analysis.Summation.sum_cintegralTwentyOne_core`
  (`genW_twentyone_eq_statement`, a pure expansion of the parametric product
  `genProd 21 m i = ∏_{k≤21}(3m+21+1+3k+i)`, lemma `genProd_twentyone`), and
* apply that commons identity, `squareSum_eq_L2chi3`, and the values of
  `HA_coeff 21`, `HB_coeff 21`.

This *replaces* the per-degree analytic template used for `n ≤ 19` (binomial
series + two Bochner interchanges + monomial integrals), which is now
subsumed by `cintegralJ_eq_sum_W_gen`; it makes adding the next degree cheap
(no 800-line module, no heavy build).
-/

set_option maxHeartbeats 800000

noncomputable section

open scoped BigOperators

namespace Submission.CDT

/-- the parametric product `genProd 21 m i = ∏_{k≤21}(3m+21+1+3k+i)`, expanded -/
lemma genProd_twentyone (m i : ℕ) :
    genProd 21 m i = ((3 * m + 22 + i : ℕ) : ℝ) * ((3 * m + 25 + i : ℕ) : ℝ) * ((3 * m + 28 + i : ℕ) : ℝ) * ((3 * m + 31 + i : ℕ) : ℝ) * ((3 * m + 34 + i : ℕ) : ℝ) * ((3 * m + 37 + i : ℕ) : ℝ) * ((3 * m + 40 + i : ℕ) : ℝ) * ((3 * m + 43 + i : ℕ) : ℝ) * ((3 * m + 46 + i : ℕ) : ℝ) * ((3 * m + 49 + i : ℕ) : ℝ) * ((3 * m + 52 + i : ℕ) : ℝ) * ((3 * m + 55 + i : ℕ) : ℝ) * ((3 * m + 58 + i : ℕ) : ℝ) * ((3 * m + 61 + i : ℕ) : ℝ) * ((3 * m + 64 + i : ℕ) : ℝ) * ((3 * m + 67 + i : ℕ) : ℝ) * ((3 * m + 70 + i : ℕ) : ℝ) * ((3 * m + 73 + i : ℕ) : ℝ) * ((3 * m + 76 + i : ℕ) : ℝ) * ((3 * m + 79 + i : ℕ) : ℝ) * ((3 * m + 82 + i : ℕ) : ℝ) * ((3 * m + 85 + i : ℕ) : ℝ) := by
  unfold genProd
  rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
/-- the degree-`21` instance of the `m`-sum evaluation
`Σₘ genW 21 m = a_21·L(2,χ₋₃) − 2·b_21` -/
theorem genW_twentyone_eq_statement (m : ℕ) :
    genW 21 m = (109418989131512359209 : ℝ) * (Nat.choose (m + 42) 42 : ℝ) *
          (∑ i ∈ Finset.range 44,
            ((-1 : ℝ) ^ i * (Nat.choose 43 i : ℝ)) *
              (534429300590128616689336320000 / (((3 * m + 22 + i : ℕ) : ℝ) * ((3 * m + 25 + i : ℕ) : ℝ) * ((3 * m + 28 + i : ℕ) : ℝ) * ((3 * m + 31 + i : ℕ) : ℝ) * ((3 * m + 34 + i : ℕ) : ℝ) * ((3 * m + 37 + i : ℕ) : ℝ) * ((3 * m + 40 + i : ℕ) : ℝ) * ((3 * m + 43 + i : ℕ) : ℝ) * ((3 * m + 46 + i : ℕ) : ℝ) * ((3 * m + 49 + i : ℕ) : ℝ) * ((3 * m + 52 + i : ℕ) : ℝ) * ((3 * m + 55 + i : ℕ) : ℝ) * ((3 * m + 58 + i : ℕ) : ℝ) * ((3 * m + 61 + i : ℕ) : ℝ) * ((3 * m + 64 + i : ℕ) : ℝ) * ((3 * m + 67 + i : ℕ) : ℝ) * ((3 * m + 70 + i : ℕ) : ℝ) * ((3 * m + 73 + i : ℕ) : ℝ) * ((3 * m + 76 + i : ℕ) : ℝ) * ((3 * m + 79 + i : ℕ) : ℝ) * ((3 * m + 82 + i : ℕ) : ℝ) * ((3 * m + 85 + i : ℕ) : ℝ))) ^ 2) := by
  have hL : genW 21 m = (109418989131512359209 : ℝ) * (Nat.choose (m + 42) 42 : ℝ) *
      (∑ i ∈ Finset.range 44,
        ((-1 : ℝ) ^ i * (Nat.choose 43 i : ℝ)) *
          (534429300590128616689336320000 / genProd 21 m i) ^ 2) := by
    have h9 : ((9 : ℝ) ^ 21) = 109418989131512359209 := by norm_num
    have h3 : ((3 : ℝ) ^ 21) * (Nat.factorial 21 : ℝ) = 534429300590128616689336320000 := by norm_num
    have hr : 2 * 21 + 2 = 44 := by norm_num
    have hb : 2 * 21 = 42 := by norm_num
    have hc : 2 * 21 + 1 = 43 := by norm_num
    unfold genW genCoef genIntTerm'
    rw [hr, hb, hc, h9, h3]
    ring
  rw [hL]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [genProd_twentyone m i]

/-- **the `(Cintegral)` instance at `n = 21`**:
`2129158861755559587·L(2,χ₋₃) − 556481088608425410076556411551509/334520839452800 = J_21`. -/
theorem CintegralIdentityAt_twentyone : CintegralIdentityAt 21 := by
  change L2chi3Real * (HA_coeff 21 : ℝ) - 2 * (HB_coeff 21 : ℝ) = cintegralJ 21
  have hA : HA_coeff 21 = 2129158861755559587 := by native_decide
  have hB : HB_coeff 21 = 556481088608425410076556411551509 / 669041678905600 := by native_decide
  have hJ : cintegralJ 21 = (2129158861755559587 : ℝ) * L2chi3Real - 556481088608425410076556411551509 / 334520839452800 := by
    rw [cintegralJ_eq_sum_W_gen 21]
    rw [show (∑' m : ℕ, genW 21 m) = (∑' m : ℕ, (109418989131512359209 : ℝ) * (Nat.choose (m + 42) 42 : ℝ) *
          (∑ i ∈ Finset.range 44,
            ((-1 : ℝ) ^ i * (Nat.choose 43 i : ℝ)) *
              (534429300590128616689336320000 / (((3 * m + 22 + i : ℕ) : ℝ) * ((3 * m + 25 + i : ℕ) : ℝ) * ((3 * m + 28 + i : ℕ) : ℝ) * ((3 * m + 31 + i : ℕ) : ℝ) * ((3 * m + 34 + i : ℕ) : ℝ) * ((3 * m + 37 + i : ℕ) : ℝ) * ((3 * m + 40 + i : ℕ) : ℝ) * ((3 * m + 43 + i : ℕ) : ℝ) * ((3 * m + 46 + i : ℕ) : ℝ) * ((3 * m + 49 + i : ℕ) : ℝ) * ((3 * m + 52 + i : ℕ) : ℝ) * ((3 * m + 55 + i : ℕ) : ℝ) * ((3 * m + 58 + i : ℕ) : ℝ) * ((3 * m + 61 + i : ℕ) : ℝ) * ((3 * m + 64 + i : ℕ) : ℝ) * ((3 * m + 67 + i : ℕ) : ℝ) * ((3 * m + 70 + i : ℕ) : ℝ) * ((3 * m + 73 + i : ℕ) : ℝ) * ((3 * m + 76 + i : ℕ) : ℝ) * ((3 * m + 79 + i : ℕ) : ℝ) * ((3 * m + 82 + i : ℕ) : ℝ) * ((3 * m + 85 + i : ℕ) : ℝ))) ^ 2)) from
      tsum_congr (fun m => genW_twentyone_eq_statement m)]
    rw [Commons.Analysis.Summation.sum_cintegralTwentyOne_core]
    rw [squareSum_eq_L2chi3]
  rw [hJ]
  norm_num [hA, hB]
  ring

/-- the `(Cintegral)` `n = 21` double-integral evaluation, restated through the
general expansion -/
theorem cintegralJ_twentyone_eq_sum_W : cintegralJ 21 = ∑' m : ℕ, genW 21 m :=
  cintegralJ_eq_sum_W_gen 21

end Submission.CDT
