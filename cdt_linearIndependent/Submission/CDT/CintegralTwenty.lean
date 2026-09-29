import Mathlib
import Submission.CDT.CintegralGeneral
import Submission.CDT.L2chi3Cintegral
import Submission.CDT.ZagierH
import Submission.CDT.ZagierHBC
import Submission.Commons.Analysis.Summation.sum_cintegralTwenty_core

/-!
# The `(Cintegral)` instance at `n = 20` via the general Beukers expansion

Module `Submission.CDT.CintegralGeneral` proves the **general-`n`** Beukers
expansion

```lean
theorem cintegralJ_eq_sum_W_gen (n : ℕ) : cintegralJ n = ∑' m : ℕ, genW n m
```

so no per-degree *analytic* module is needed any more to close the instance
`CintegralIdentityAt 20`: it suffices to
* identify the parametric summand `genW 20 ·` with the degree-`20` summand
  of the commons creative-telescoping identity
  `Commons.Analysis.Summation.sum_cintegralTwenty_core`
  (`genW_twenty_eq_statement`, a pure expansion of the parametric product
  `genProd 20 m i = ∏_{k≤20}(3m+20+1+3k+i)`, lemma `genProd_twenty`), and
* apply that commons identity, `squareSum_eq_L2chi3`, and the values of
  `HA_coeff 20`, `HB_coeff 20`.

This *replaces* the per-degree analytic template used for `n ≤ 19` (binomial
series + two Bochner interchanges + monomial integrals), which is now
subsumed by `cintegralJ_eq_sum_W_gen`; it makes adding the next degree cheap
(no 800-line module, no heavy build).
-/

set_option maxHeartbeats 800000

noncomputable section

open scoped BigOperators

namespace Submission.CDT

/-- the parametric product `genProd 20 m i = ∏_{k≤20}(3m+20+1+3k+i)`, expanded -/
lemma genProd_twenty (m i : ℕ) :
    genProd 20 m i = ((3 * m + 21 + i : ℕ) : ℝ) * ((3 * m + 24 + i : ℕ) : ℝ) * ((3 * m + 27 + i : ℕ) : ℝ) * ((3 * m + 30 + i : ℕ) : ℝ) * ((3 * m + 33 + i : ℕ) : ℝ) * ((3 * m + 36 + i : ℕ) : ℝ) * ((3 * m + 39 + i : ℕ) : ℝ) * ((3 * m + 42 + i : ℕ) : ℝ) * ((3 * m + 45 + i : ℕ) : ℝ) * ((3 * m + 48 + i : ℕ) : ℝ) * ((3 * m + 51 + i : ℕ) : ℝ) * ((3 * m + 54 + i : ℕ) : ℝ) * ((3 * m + 57 + i : ℕ) : ℝ) * ((3 * m + 60 + i : ℕ) : ℝ) * ((3 * m + 63 + i : ℕ) : ℝ) * ((3 * m + 66 + i : ℕ) : ℝ) * ((3 * m + 69 + i : ℕ) : ℝ) * ((3 * m + 72 + i : ℕ) : ℝ) * ((3 * m + 75 + i : ℕ) : ℝ) * ((3 * m + 78 + i : ℕ) : ℝ) * ((3 * m + 81 + i : ℕ) : ℝ) := by
  unfold genProd
  rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_zero, one_mul]

/-- the degree-`20` instance of the `m`-sum evaluation
`Σₘ genW 20 m = a_20·L(2,χ₋₃) − 2·b_20` -/
theorem genW_twenty_eq_statement (m : ℕ) :
    genW 20 m = (12157665459056928801 : ℝ) * (Nat.choose (m + 40) 40 : ℝ) *
          (∑ i ∈ Finset.range 42,
            ((-1 : ℝ) ^ i * (Nat.choose 41 i : ℝ)) *
              (8483004771271882804592640000 / (((3 * m + 21 + i : ℕ) : ℝ) * ((3 * m + 24 + i : ℕ) : ℝ) * ((3 * m + 27 + i : ℕ) : ℝ) * ((3 * m + 30 + i : ℕ) : ℝ) * ((3 * m + 33 + i : ℕ) : ℝ) * ((3 * m + 36 + i : ℕ) : ℝ) * ((3 * m + 39 + i : ℕ) : ℝ) * ((3 * m + 42 + i : ℕ) : ℝ) * ((3 * m + 45 + i : ℕ) : ℝ) * ((3 * m + 48 + i : ℕ) : ℝ) * ((3 * m + 51 + i : ℕ) : ℝ) * ((3 * m + 54 + i : ℕ) : ℝ) * ((3 * m + 57 + i : ℕ) : ℝ) * ((3 * m + 60 + i : ℕ) : ℝ) * ((3 * m + 63 + i : ℕ) : ℝ) * ((3 * m + 66 + i : ℕ) : ℝ) * ((3 * m + 69 + i : ℕ) : ℝ) * ((3 * m + 72 + i : ℕ) : ℝ) * ((3 * m + 75 + i : ℕ) : ℝ) * ((3 * m + 78 + i : ℕ) : ℝ) * ((3 * m + 81 + i : ℕ) : ℝ))) ^ 2) := by
  have hL : genW 20 m = (12157665459056928801 : ℝ) * (Nat.choose (m + 40) 40 : ℝ) *
      (∑ i ∈ Finset.range 42,
        ((-1 : ℝ) ^ i * (Nat.choose 41 i : ℝ)) *
          (8483004771271882804592640000 / genProd 20 m i) ^ 2) := by
    have h9 : ((9 : ℝ) ^ 20) = 12157665459056928801 := by norm_num
    have h3 : ((3 : ℝ) ^ 20) * (Nat.factorial 20 : ℝ) = 8483004771271882804592640000 := by norm_num
    have hr : 2 * 20 + 2 = 42 := by norm_num
    have hb : 2 * 20 = 40 := by norm_num
    have hc : 2 * 20 + 1 = 41 := by norm_num
    unfold genW genCoef genIntTerm'
    rw [hr, hb, hc, h9, h3]
    ring
  rw [hL]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [genProd_twenty m i]

/-- **the `(Cintegral)` instance at `n = 20`**:
`248256043372999089·L(2,χ₋₃) − 64884680871542898537412147933623/334520839452800 = J_20`. -/
theorem CintegralIdentityAt_twenty : CintegralIdentityAt 20 := by
  change L2chi3Real * (HA_coeff 20 : ℝ) - 2 * (HB_coeff 20 : ℝ) = cintegralJ 20
  have hA : HA_coeff 20 = 248256043372999089 := by native_decide
  have hB : HB_coeff 20 = 64884680871542898537412147933623 / 669041678905600 := by native_decide
  have hJ : cintegralJ 20 = (248256043372999089 : ℝ) * L2chi3Real - 64884680871542898537412147933623 / 334520839452800 := by
    rw [cintegralJ_eq_sum_W_gen 20]
    rw [show (∑' m : ℕ, genW 20 m) = (∑' m : ℕ, (12157665459056928801 : ℝ) * (Nat.choose (m + 40) 40 : ℝ) *
          (∑ i ∈ Finset.range 42,
            ((-1 : ℝ) ^ i * (Nat.choose 41 i : ℝ)) *
              (8483004771271882804592640000 / (((3 * m + 21 + i : ℕ) : ℝ) * ((3 * m + 24 + i : ℕ) : ℝ) * ((3 * m + 27 + i : ℕ) : ℝ) * ((3 * m + 30 + i : ℕ) : ℝ) * ((3 * m + 33 + i : ℕ) : ℝ) * ((3 * m + 36 + i : ℕ) : ℝ) * ((3 * m + 39 + i : ℕ) : ℝ) * ((3 * m + 42 + i : ℕ) : ℝ) * ((3 * m + 45 + i : ℕ) : ℝ) * ((3 * m + 48 + i : ℕ) : ℝ) * ((3 * m + 51 + i : ℕ) : ℝ) * ((3 * m + 54 + i : ℕ) : ℝ) * ((3 * m + 57 + i : ℕ) : ℝ) * ((3 * m + 60 + i : ℕ) : ℝ) * ((3 * m + 63 + i : ℕ) : ℝ) * ((3 * m + 66 + i : ℕ) : ℝ) * ((3 * m + 69 + i : ℕ) : ℝ) * ((3 * m + 72 + i : ℕ) : ℝ) * ((3 * m + 75 + i : ℕ) : ℝ) * ((3 * m + 78 + i : ℕ) : ℝ) * ((3 * m + 81 + i : ℕ) : ℝ))) ^ 2)) from
      tsum_congr (fun m => genW_twenty_eq_statement m)]
    rw [Commons.Analysis.Summation.sum_cintegralTwenty_core]
    rw [squareSum_eq_L2chi3]
  rw [hJ]
  norm_num [hA, hB]
  ring

/-- the `(Cintegral)` `n = 20` double-integral evaluation, restated through the
general expansion -/
theorem cintegralJ_twenty_eq_sum_W : cintegralJ 20 = ∑' m : ℕ, genW 20 m :=
  cintegralJ_eq_sum_W_gen 20

end Submission.CDT
