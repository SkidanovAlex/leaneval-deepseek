import Mathlib
import Submission.Work.RHContract.Corpus
import Submission.Work.RHContract.A.ca_margin_lower
import Submission.Work.RHContract.A.psiTail_ge_of_RH
import Submission.Work.RHContract.A.psi_sub_le_of_RH
import Submission.Work.RHContract.A.ca_exp_eq_one_of_gt_xi2
import Submission.Work.RHContract.A.ca_exp_eq_two_of_between
import Submission.Work.RHContract.A.ca_lcmUpto_dvd
import Submission.Work.RHContract.A.regionII.ca_regionII_core

/-!
# Region II of AREA A: Robin's inequality at CA numbers with `30000 ≤ ξ(ε) < 10^8`

This file assembles the target `Work.RHContract.A.robin_ca_regionII` from the margin
computation `Work.RHContract.A.regionII.ca_regionII_core`, which establishes
`γ + log log log N_ε − log(σ(N_ε)/N_ε) ≥ 0` on the region `30000 ≤ ξ(ε) < 10^8`.
The remaining step is the bookkeeping conversion from that inequality to Robin's bound
`σ(N_ε) ≤ e^γ N_ε log log N_ε`.
-/

open scoped ArithmeticFunction.sigma

namespace Work.RHContract.A

/-- The largest prime factor `ξ(ε)` of the colossally abundant number `N_ε` is at most `N_ε`.
Indeed `ξ(ε)` belongs to the support, with exponent `⌊μ(ξ,ε)⌋₊ ≥ 1`. -/
lemma caXi_le_caNumber (ε : ℝ) (hε : 0 < ε) (hξ : 1530 ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.caXi ε ≤ Work.RHPlan.caNumber ε := by
  have hmem : Work.RHPlan.caXi ε ∈ Work.RHPlan.caSupport ε :=
    (mem_caSupport_iff ε hε hξ).mpr ⟨le_refl _, caXi_prime ε hξ⟩
  have ha : 1 ≤ ⌊Work.RHPlan.caMu (Work.RHPlan.caXi ε) ε⌋₊ := (Finset.mem_filter.mp hmem).2
  rw [caNumber_eq_prod_support]
  have h1 : Work.RHPlan.caXi ε ≤ (Work.RHPlan.caXi ε) ^ ⌊Work.RHPlan.caMu (Work.RHPlan.caXi ε) ε⌋₊ :=
    Nat.le_self_pow (by omega) (Work.RHPlan.caXi ε)
  have h2 := Finset.single_le_prod' (f := fun p => p ^ ⌊Work.RHPlan.caMu p ε⌋₊)
      (fun p hp => Nat.one_le_pow _ _ (prime_of_mem_caSupport hp).one_le) hmem
  exact le_trans h1 h2

theorem robin_ca_regionII (h : RiemannHypothesis) (ε : ℝ) (hε : 0 < ε)
    (hlo : 30000 ≤ (Work.RHPlan.caXi ε : ℝ)) (hhi : (Work.RHPlan.caXi ε : ℝ) < (10 : ℝ) ^ 8) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hξ1530 : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ) := by linarith
  -- (1) the margin computation of `regionII`
  have hpos := regionII.ca_regionII_core h ε hε hlo hhi
  -- (2) elementary size facts about `N = caNumber ε`
  have hξnat : 30000 ≤ Work.RHPlan.caXi ε := by exact_mod_cast hlo
  have hξle : Work.RHPlan.caXi ε ≤ Work.RHPlan.caNumber ε := caXi_le_caNumber ε hε hξ1530
  have hN3 : 3 ≤ Work.RHPlan.caNumber ε := by omega
  have hNne : Work.RHPlan.caNumber ε ≠ 0 := by omega
  have hNpos : (0 : ℝ) < ((Work.RHPlan.caNumber ε : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < Work.RHPlan.caNumber ε)
  have hσpos : (0 : ℝ) < (((ArithmeticFunction.sigma 1 (Work.RHPlan.caNumber ε) : ℕ) : ℝ)) := by
    exact_mod_cast ArithmeticFunction.sigma_pos 1 (Work.RHPlan.caNumber ε) hNne
  have hlog3 : (1 : ℝ) < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    exact Real.exp_one_lt_three
  have hlogN1 : (1 : ℝ) < Real.log ((Work.RHPlan.caNumber ε : ℕ) : ℝ) := by
    have h3 : Real.log 3 ≤ Real.log ((Work.RHPlan.caNumber ε : ℕ) : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hN3)
    linarith
  have hloglog_pos : 0 < Real.log (Real.log ((Work.RHPlan.caNumber ε : ℕ) : ℝ)) :=
    Real.log_pos hlogN1
  -- (3) `Δ ≥ 0` implies `σ(N)/N ≤ e^γ log log N`
  have h1 : Real.log (((ArithmeticFunction.sigma 1 (Work.RHPlan.caNumber ε) : ℕ) : ℝ) /
        ((Work.RHPlan.caNumber ε : ℕ) : ℝ))
      ≤ Real.eulerMascheroniConstant
        + Real.log (Real.log (Real.log ((Work.RHPlan.caNumber ε : ℕ) : ℝ))) := by
    linarith
  have hlog_eq : Real.log (Real.exp Real.eulerMascheroniConstant
        * Real.log (Real.log ((Work.RHPlan.caNumber ε : ℕ) : ℝ)))
      = Real.eulerMascheroniConstant
        + Real.log (Real.log (Real.log ((Work.RHPlan.caNumber ε : ℕ) : ℝ))) := by
    rw [Real.log_mul (Real.exp_ne_zero _) (ne_of_gt hloglog_pos), Real.log_exp]
  have h2 : ((ArithmeticFunction.sigma 1 (Work.RHPlan.caNumber ε) : ℕ) : ℝ) /
        ((Work.RHPlan.caNumber ε : ℕ) : ℝ)
      ≤ Real.exp Real.eulerMascheroniConstant
        * Real.log (Real.log ((Work.RHPlan.caNumber ε : ℕ) : ℝ)) :=
    (Real.log_le_log_iff (div_pos hσpos hNpos)
      (mul_pos (Real.exp_pos _) hloglog_pos)).mp (by rw [hlog_eq]; exact h1)
  -- (4) multiply by `N`
  rw [Work.RHPlan.RobinBound]
  have h3 := mul_le_mul_of_nonneg_right h2 hNpos.le
  rw [div_mul_cancel₀ _ (ne_of_gt hNpos)] at h3
  calc ((ArithmeticFunction.sigma 1 (Work.RHPlan.caNumber ε) : ℕ) : ℝ)
      ≤ Real.exp Real.eulerMascheroniConstant
          * Real.log (Real.log ((Work.RHPlan.caNumber ε : ℕ) : ℝ))
          * ((Work.RHPlan.caNumber ε : ℕ) : ℝ) := h3
    _ = Real.exp Real.eulerMascheroniConstant * ((Work.RHPlan.caNumber ε : ℕ) : ℝ)
          * Real.log (Real.log ((Work.RHPlan.caNumber ε : ℕ) : ℝ)) := by ring

end Work.RHContract.A
