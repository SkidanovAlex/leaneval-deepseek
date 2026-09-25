import Mathlib
import Submission.Work.RHContract.A.RegionI.Core

open scoped BigOperators

namespace Work.RHContract.RegionI

noncomputable section

lemma thV_0 : ((((6931471803 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2 : ℕ) : ℝ) := by
  have h2 : ((6931471803 : ℚ) / 10000000000) ≤ Work.RHContract.RegionI.logLowQ (2:ℚ) := by decide +kernel
  have h2R : ((((6931471803 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ (Work.RHContract.RegionI.logLowQ (2:ℚ) : ℝ) := by exact_mod_cast h2
  have h3 : Chebyshev.theta ((2 : ℕ) : ℝ) = Real.log ((2 : ℕ) : ℝ) := by
    rw [Chebyshev.theta_eq_sum_primesLE_log, show Nat.primesLE 2 = {2} by decide +kernel]
    simp
  rw [h3]
  exact le_trans h2R (Work.RHContract.RegionI.logLowQ_le (x := (2:ℚ)) (by norm_num) (by norm_num))
lemma thV_1 : ((((447939867177 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2 < q → q < 3 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3).mp (by decide +kernel))) hgap
  have hprev := thV_0
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((447939867177 : ℚ) / 250000000000) ≤ ((6931471803 : ℚ) / 10000000000) + Work.RHContract.RegionI.logLowQ (3:ℚ) := by decide +kernel
  have hratR : ((((447939867177 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((6931471803 : ℚ) / 10000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2 : ((((1700598690311 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3 < q → q < 5 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5).mp (by decide +kernel))) hgap
  have hprev := thV_1
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1700598690311 : ℚ) / 500000000000) ≤ ((447939867177 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (5:ℚ) := by decide +kernel
  have hratR : ((((1700598690311 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((447939867177 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3 : ((((5347107529157 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5 < q → q < 7 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7).mp (by decide +kernel))) hgap
  have hprev := thV_2
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5347107529157 : ℚ) / 1000000000000) ≤ ((1700598690311 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (7:ℚ) := by decide +kernel
  have hratR : ((((5347107529157 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1700598690311 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_4 : ((((309800112047 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7 < q → q < 11 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11).mp (by decide +kernel))) hgap
  have hprev := thV_3
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((309800112047 : ℚ) / 40000000000) ≤ ((5347107529157 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (11:ℚ) := by decide +kernel
  have hratR : ((((309800112047 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((5347107529157 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_5 : ((((322186004933 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11 < q → q < 13 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13).mp (by decide +kernel))) hgap
  have hprev := thV_4
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((322186004933 : ℚ) / 31250000000) ≤ ((309800112047 : ℚ) / 40000000000) + Work.RHContract.RegionI.logLowQ (13:ℚ) := by decide +kernel
  have hratR : ((((322186004933 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((309800112047 : ℚ) / 40000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_6 : ((((1642895687609 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13 < q → q < 17 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17).mp (by decide +kernel))) hgap
  have hprev := thV_5
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1642895687609 : ℚ) / 125000000000) ≤ ((322186004933 : ℚ) / 31250000000) + Work.RHContract.RegionI.logLowQ (17:ℚ) := by decide +kernel
  have hratR : ((((1642895687609 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((322186004933 : ℚ) / 31250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_7 : ((((8043802239499 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17 < q → q < 19 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19).mp (by decide +kernel))) hgap
  have hprev := thV_6
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8043802239499 : ℚ) / 500000000000) ≤ ((1642895687609 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (19:ℚ) := by decide +kernel
  have hratR : ((((8043802239499 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1642895687609 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_8 : ((((19223098693887 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19 < q → q < 23 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23).mp (by decide +kernel))) hgap
  have hprev := thV_7
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((19223098693887 : ℚ) / 1000000000000) ≤ ((8043802239499 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (23:ℚ) := by decide +kernel
  have hratR : ((((19223098693887 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((8043802239499 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_9 : ((((22590394522833 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23 < q → q < 29 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29).mp (by decide +kernel))) hgap
  have hprev := thV_8
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((22590394522833 : ℚ) / 1000000000000) ≤ ((19223098693887 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (29:ℚ) := by decide +kernel
  have hratR : ((((22590394522833 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((19223098693887 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_10 : ((((13012190863139 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((31 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29 < q → q < 31 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 31).mp (by decide +kernel))) hgap
  have hprev := thV_9
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (31:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13012190863139 : ℚ) / 500000000000) ≤ ((22590394522833 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (31:ℚ) := by decide +kernel
  have hratR : ((((13012190863139 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((22590394522833 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (31:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_11 : ((((14817649818811 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((37 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 31 < q → q < 37 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 37).mp (by decide +kernel))) hgap
  have hprev := thV_10
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (37:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14817649818811 : ℚ) / 500000000000) ≤ ((13012190863139 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (37:ℚ) := by decide +kernel
  have hratR : ((((14817649818811 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((13012190863139 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (37:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_12 : ((((16674435851513 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((41 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 37 < q → q < 41 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 41).mp (by decide +kernel))) hgap
  have hprev := thV_11
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (41:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((16674435851513 : ℚ) / 500000000000) ≤ ((14817649818811 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (41:ℚ) := by decide +kernel
  have hratR : ((((16674435851513 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((14817649818811 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (41:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_13 : ((((37110071817419 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((43 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 41 < q → q < 43 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 43).mp (by decide +kernel))) hgap
  have hprev := thV_12
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (43:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((37110071817419 : ℚ) / 1000000000000) ≤ ((16674435851513 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (43:ℚ) := by decide +kernel
  have hratR : ((((37110071817419 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((16674435851513 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (43:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_14 : ((((40960219417829 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((47 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 43 < q → q < 47 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 47).mp (by decide +kernel))) hgap
  have hprev := thV_13
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (47:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((40960219417829 : ℚ) / 1000000000000) ≤ ((37110071817419 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (47:ℚ) := by decide +kernel
  have hratR : ((((40960219417829 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((37110071817419 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (47:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_15 : ((((44930511330081 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((53 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 47 < q → q < 53 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 53).mp (by decide +kernel))) hgap
  have hprev := thV_14
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (53:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((44930511330081 : ℚ) / 1000000000000) ≤ ((40960219417829 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (53:ℚ) := by decide +kernel
  have hratR : ((((44930511330081 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((40960219417829 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (53:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_16 : ((((24504024386343 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((59 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 53 < q → q < 59 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 59).mp (by decide +kernel))) hgap
  have hprev := thV_15
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (59:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((24504024386343 : ℚ) / 500000000000) ≤ ((44930511330081 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (59:ℚ) := by decide +kernel
  have hratR : ((((24504024386343 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((44930511330081 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (59:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_17 : ((((53118922635559 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((61 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 59 < q → q < 61 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 61).mp (by decide +kernel))) hgap
  have hprev := thV_16
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (61:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((53118922635559 : ℚ) / 1000000000000) ≤ ((24504024386343 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (61:ℚ) := by decide +kernel
  have hratR : ((((53118922635559 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((24504024386343 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (61:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_18 : ((((5732361525339 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((67 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 61 < q → q < 67 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 67).mp (by decide +kernel))) hgap
  have hprev := thV_17
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (67:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5732361525339 : ℚ) / 100000000000) ≤ ((53118922635559 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (67:ℚ) := by decide +kernel
  have hratR : ((((5732361525339 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((53118922635559 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (67:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_19 : ((((61586295128871 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((71 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 67 < q → q < 71 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 71).mp (by decide +kernel))) hgap
  have hprev := thV_18
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (71:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((61586295128871 : ℚ) / 1000000000000) ≤ ((5732361525339 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (71:ℚ) := by decide +kernel
  have hratR : ((((61586295128871 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5732361525339 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (71:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_20 : ((((65876754568459 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((73 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 71 < q → q < 73 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 73).mp (by decide +kernel))) hgap
  have hprev := thV_19
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (73:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((65876754568459 : ℚ) / 1000000000000) ≤ ((61586295128871 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (73:ℚ) := by decide +kernel
  have hratR : ((((65876754568459 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((61586295128871 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (73:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_21 : ((((35123101209683 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((79 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 73 < q → q < 79 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 79).mp (by decide +kernel))) hgap
  have hprev := thV_20
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (79:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((35123101209683 : ℚ) / 500000000000) ≤ ((65876754568459 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (79:ℚ) := by decide +kernel
  have hratR : ((((35123101209683 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((65876754568459 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (79:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_22 : ((((37332521512801 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((83 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 79 < q → q < 83 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 83).mp (by decide +kernel))) hgap
  have hprev := thV_21
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (83:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((37332521512801 : ℚ) / 500000000000) ≤ ((35123101209683 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (83:ℚ) := by decide +kernel
  have hratR : ((((37332521512801 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((35123101209683 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (83:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_23 : ((((39576839696887 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((89 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 83 < q → q < 89 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 89).mp (by decide +kernel))) hgap
  have hprev := thV_22
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (89:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((39576839696887 : ℚ) / 500000000000) ≤ ((37332521512801 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (89:ℚ) := by decide +kernel
  have hratR : ((((39576839696887 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((37332521512801 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (89:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_24 : ((((83728390370717 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((97 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 89 < q → q < 97 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 97).mp (by decide +kernel))) hgap
  have hprev := thV_23
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (97:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((83728390370717 : ℚ) / 1000000000000) ≤ ((39576839696887 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (97:ℚ) := by decide +kernel
  have hratR : ((((83728390370717 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((39576839696887 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (97:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_25 : ((((44171755442999 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((101 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 97 < q → q < 101 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 101).mp (by decide +kernel))) hgap
  have hprev := thV_24
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (101:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((44171755442999 : ℚ) / 500000000000) ≤ ((83728390370717 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (101:ℚ) := by decide +kernel
  have hratR : ((((44171755442999 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((83728390370717 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (101:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_26 : ((((92978239872667 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((103 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 101 < q → q < 103 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 103).mp (by decide +kernel))) hgap
  have hprev := thV_25
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (103:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((92978239872667 : ℚ) / 1000000000000) ≤ ((44171755442999 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (103:ℚ) := by decide +kernel
  have hratR : ((((92978239872667 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((44171755442999 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (103:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_27 : ((((97651068705569 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((107 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 103 < q → q < 107 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 107).mp (by decide +kernel))) hgap
  have hprev := thV_26
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (107:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((97651068705569 : ℚ) / 1000000000000) ≤ ((92978239872667 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (107:ℚ) := by decide +kernel
  have hratR : ((((97651068705569 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((92978239872667 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (107:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_28 : ((((51171208293119 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((109 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 107 < q → q < 109 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 109).mp (by decide +kernel))) hgap
  have hprev := thV_27
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (109:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((51171208293119 : ℚ) / 500000000000) ≤ ((97651068705569 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (109:ℚ) := by decide +kernel
  have hratR : ((((51171208293119 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((97651068705569 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (109:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_29 : ((((10706980440339 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((113 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 109 < q → q < 113 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 113).mp (by decide +kernel))) hgap
  have hprev := thV_28
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (113:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10706980440339 : ℚ) / 100000000000) ≤ ((51171208293119 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (113:ℚ) := by decide +kernel
  have hratR : ((((10706980440339 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((51171208293119 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (113:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_30 : ((((3497312234009 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((127 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 113 < q → q < 127 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 127).mp (by decide +kernel))) hgap
  have hprev := thV_29
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (127:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3497312234009 : ℚ) / 31250000000) ≤ ((10706980440339 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (127:ℚ) := by decide +kernel
  have hratR : ((((3497312234009 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((10706980440339 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (127:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_31 : ((((116789188809669 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((131 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 127 < q → q < 131 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 131).mp (by decide +kernel))) hgap
  have hprev := thV_30
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (131:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((116789188809669 : ℚ) / 1000000000000) ≤ ((3497312234009 : ℚ) / 31250000000) + Work.RHContract.RegionI.logLowQ (131:ℚ) := by decide +kernel
  have hratR : ((((116789188809669 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3497312234009 : ℚ) / 31250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (131:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_32 : ((((121709169733677 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((137 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 131 < q → q < 137 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 137).mp (by decide +kernel))) hgap
  have hprev := thV_31
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (137:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((121709169733677 : ℚ) / 1000000000000) ≤ ((116789188809669 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (137:ℚ) := by decide +kernel
  have hratR : ((((121709169733677 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((116789188809669 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (137:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_33 : ((((31660910916247 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((139 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 137 < q → q < 139 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 139).mp (by decide +kernel))) hgap
  have hprev := thV_32
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (139:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((31660910916247 : ℚ) / 250000000000) ≤ ((121709169733677 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (139:ℚ) := by decide +kernel
  have hratR : ((((31660910916247 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((121709169733677 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (139:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_34 : ((((131647589969113 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((149 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 139 < q → q < 149 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 149).mp (by decide +kernel))) hgap
  have hprev := thV_33
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (149:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((131647589969113 : ℚ) / 1000000000000) ≤ ((31660910916247 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (149:ℚ) := by decide +kernel
  have hratR : ((((131647589969113 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((31660910916247 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (149:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_35 : ((((34166217451027 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((151 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 149 < q → q < 151 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 151).mp (by decide +kernel))) hgap
  have hprev := thV_34
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (151:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((34166217451027 : ℚ) / 250000000000) ≤ ((131647589969113 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (151:ℚ) := by decide +kernel
  have hratR : ((((34166217451027 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((131647589969113 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (151:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_36 : ((((35430278901909 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((157 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 151 < q → q < 157 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 157).mp (by decide +kernel))) hgap
  have hprev := thV_35
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (157:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((35430278901909 : ℚ) / 250000000000) ≤ ((34166217451027 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (157:ℚ) := by decide +kernel
  have hratR : ((((35430278901909 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((34166217451027 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (157:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_37 : ((((146814865806623 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((163 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 157 < q → q < 163 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 163).mp (by decide +kernel))) hgap
  have hprev := thV_36
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (163:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((146814865806623 : ℚ) / 1000000000000) ≤ ((35430278901909 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (163:ℚ) := by decide +kernel
  have hratR : ((((146814865806623 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((35430278901909 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (163:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_38 : ((((7596642980861 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((167 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 163 < q → q < 167 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 167).mp (by decide +kernel))) hgap
  have hprev := thV_37
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (167:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7596642980861 : ℚ) / 50000000000) ≤ ((146814865806623 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (167:ℚ) := by decide +kernel
  have hratR : ((((7596642980861 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((146814865806623 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (167:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_39 : ((((78543075604949 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((173 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 167 < q → q < 173 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 173).mp (by decide +kernel))) hgap
  have hprev := thV_38
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (173:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((78543075604949 : ℚ) / 500000000000) ≤ ((7596642980861 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (173:ℚ) := by decide +kernel
  have hratR : ((((78543075604949 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((7596642980861 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (173:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_40 : ((((162273537013919 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((179 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 173 < q → q < 179 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 179).mp (by decide +kernel))) hgap
  have hprev := thV_39
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (179:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((162273537013919 : ℚ) / 1000000000000) ≤ ((78543075604949 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (179:ℚ) := by decide +kernel
  have hratR : ((((162273537013919 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((78543075604949 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (179:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_41 : ((((33494406808673 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((181 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 179 < q → q < 181 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 181).mp (by decide +kernel))) hgap
  have hprev := thV_40
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (181:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((33494406808673 : ℚ) / 200000000000) ≤ ((162273537013919 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (181:ℚ) := by decide +kernel
  have hratR : ((((33494406808673 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((162273537013919 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (181:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_42 : ((((21590538433699 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((191 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 181 < q → q < 191 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 191).mp (by decide +kernel))) hgap
  have hprev := thV_41
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (191:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((21590538433699 : ℚ) / 125000000000) ≤ ((33494406808673 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (191:ℚ) := by decide +kernel
  have hratR : ((((21590538433699 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((33494406808673 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (191:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_43 : ((((177986997656677 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((193 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 191 < q → q < 193 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 193).mp (by decide +kernel))) hgap
  have hprev := thV_42
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (193:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((177986997656677 : ℚ) / 1000000000000) ≤ ((21590538433699 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (193:ℚ) := by decide +kernel
  have hratR : ((((177986997656677 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((21590538433699 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (193:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_44 : ((((36654040276719 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((197 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 193 < q → q < 197 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 197).mp (by decide +kernel))) hgap
  have hprev := thV_43
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (197:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((36654040276719 : ℚ) / 200000000000) ≤ ((177986997656677 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (197:ℚ) := by decide +kernel
  have hratR : ((((36654040276719 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((177986997656677 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (197:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_45 : ((((188563506206499 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((199 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 197 < q → q < 199 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 199).mp (by decide +kernel))) hgap
  have hprev := thV_44
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (199:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((188563506206499 : ℚ) / 1000000000000) ≤ ((36654040276719 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (199:ℚ) := by decide +kernel
  have hratR : ((((188563506206499 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((36654040276719 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (199:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_46 : ((((38783072867631 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((211 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 199 < q → q < 211 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 211).mp (by decide +kernel))) hgap
  have hprev := thV_45
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (211:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((38783072867631 : ℚ) / 200000000000) ≤ ((188563506206499 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (211:ℚ) := by decide +kernel
  have hratR : ((((38783072867631 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((188563506206499 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (211:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_47 : ((((39864507221559 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((223 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 211 < q → q < 223 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 223).mp (by decide +kernel))) hgap
  have hprev := thV_46
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (223:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((39864507221559 : ℚ) / 200000000000) ≤ ((38783072867631 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (223:ℚ) := by decide +kernel
  have hratR : ((((39864507221559 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((38783072867631 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (223:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_48 : ((((3199179470679 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((227 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 223 < q → q < 227 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 227).mp (by decide +kernel))) hgap
  have hprev := thV_47
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (227:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3199179470679 : ℚ) / 15625000000) ≤ ((39864507221559 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (227:ℚ) := by decide +kernel
  have hratR : ((((3199179470679 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ ((((39864507221559 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (227:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_49 : ((((21018120812519 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((229 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 227 < q → q < 229 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 229).mp (by decide +kernel))) hgap
  have hprev := thV_48
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (229:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((21018120812519 : ℚ) / 100000000000) ≤ ((3199179470679 : ℚ) / 15625000000) + Work.RHContract.RegionI.logLowQ (229:ℚ) := by decide +kernel
  have hratR : ((((21018120812519 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((3199179470679 : ℚ) / 15625000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (229:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_50 : ((((26954030822117 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((233 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 229 < q → q < 233 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 233).mp (by decide +kernel))) hgap
  have hprev := thV_49
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (233:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((26954030822117 : ℚ) / 125000000000) ≤ ((21018120812519 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (233:ℚ) := by decide +kernel
  have hratR : ((((26954030822117 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((21018120812519 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (233:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_51 : ((((221108710127047 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((239 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 233 < q → q < 239 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 239).mp (by decide +kernel))) hgap
  have hprev := thV_50
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (239:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((221108710127047 : ℚ) / 1000000000000) ≤ ((26954030822117 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (239:ℚ) := by decide +kernel
  have hratR : ((((221108710127047 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((26954030822117 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (239:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_52 : ((((113296753529359 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((241 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 239 < q → q < 241 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 241).mp (by decide +kernel))) hgap
  have hprev := thV_51
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (241:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((113296753529359 : ℚ) / 500000000000) ≤ ((221108710127047 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (241:ℚ) := by decide +kernel
  have hratR : ((((113296753529359 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((221108710127047 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (241:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_53 : ((((23211895999603 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((251 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 241 < q → q < 251 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 251).mp (by decide +kernel))) hgap
  have hprev := thV_52
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (251:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((23211895999603 : ℚ) / 100000000000) ≤ ((113296753529359 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (251:ℚ) := by decide +kernel
  have hratR : ((((23211895999603 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((113296753529359 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (251:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_54 : ((((47533607215769 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((257 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 251 < q → q < 257 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 257).mp (by decide +kernel))) hgap
  have hprev := thV_53
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (257:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((47533607215769 : ℚ) / 200000000000) ≤ ((23211895999603 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (257:ℚ) := by decide +kernel
  have hratR : ((((47533607215769 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((23211895999603 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (257:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_55 : ((((243240190108943 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((263 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 257 < q → q < 263 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 263).mp (by decide +kernel))) hgap
  have hprev := thV_54
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (263:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((243240190108943 : ℚ) / 1000000000000) ≤ ((47533607215769 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (263:ℚ) := by decide +kernel
  have hratR : ((((243240190108943 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((47533607215769 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (263:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_56 : ((((49766980297293 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((269 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 263 < q → q < 269 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 269).mp (by decide +kernel))) hgap
  have hprev := thV_55
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (269:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((49766980297293 : ℚ) / 200000000000) ≤ ((243240190108943 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (269:ℚ) := by decide +kernel
  have hratR : ((((49766980297293 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((243240190108943 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (269:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_57 : ((((50887404061053 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((271 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 269 < q → q < 271 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 271).mp (by decide +kernel))) hgap
  have hprev := thV_56
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (271:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((50887404061053 : ℚ) / 200000000000) ≤ ((49766980297293 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (271:ℚ) := by decide +kernel
  have hratR : ((((50887404061053 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((49766980297293 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (271:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_58 : ((((65015259452343 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((277 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 271 < q → q < 277 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 277).mp (by decide +kernel))) hgap
  have hprev := thV_57
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (277:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((65015259452343 : ℚ) / 250000000000) ≤ ((50887404061053 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (277:ℚ) := by decide +kernel
  have hratR : ((((65015259452343 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((50887404061053 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (277:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_59 : ((((132849696238313 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((281 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 277 < q → q < 281 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 281).mp (by decide +kernel))) hgap
  have hprev := thV_58
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (281:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((132849696238313 : ℚ) / 500000000000) ≤ ((65015259452343 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (281:ℚ) := by decide +kernel
  have hratR : ((((132849696238313 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((65015259452343 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (281:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_60 : ((((271344839372189 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((283 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 281 < q → q < 283 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 283).mp (by decide +kernel))) hgap
  have hprev := thV_59
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (283:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((271344839372189 : ℚ) / 1000000000000) ≤ ((132849696238313 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (283:ℚ) := by decide +kernel
  have hratR : ((((271344839372189 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((132849696238313 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (283:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_61 : ((((138512505989563 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((293 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 283 < q → q < 293 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 293).mp (by decide +kernel))) hgap
  have hprev := thV_60
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (293:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((138512505989563 : ℚ) / 500000000000) ≤ ((271344839372189 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (293:ℚ) := by decide +kernel
  have hratR : ((((138512505989563 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((271344839372189 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (293:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_62 : ((((282751859724633 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((307 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 293 < q → q < 307 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 307).mp (by decide +kernel))) hgap
  have hprev := thV_61
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (307:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((282751859724633 : ℚ) / 1000000000000) ≤ ((138512505989563 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (307:ℚ) := by decide +kernel
  have hratR : ((((282751859724633 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((138512505989563 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (307:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_63 : ((((72122913158683 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((311 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 307 < q → q < 311 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 311).mp (by decide +kernel))) hgap
  have hprev := thV_62
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (311:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((72122913158683 : ℚ) / 250000000000) ≤ ((282751859724633 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (311:ℚ) := by decide +kernel
  have hratR : ((((72122913158683 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((282751859724633 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (311:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_64 : ((((36779731977899 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((313 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 311 < q → q < 313 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 313).mp (by decide +kernel))) hgap
  have hprev := thV_63
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (313:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((36779731977899 : ℚ) / 125000000000) ≤ ((72122913158683 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (313:ℚ) := by decide +kernel
  have hratR : ((((36779731977899 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((72122913158683 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (313:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_65 : ((((299996757594989 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((317 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 313 < q → q < 317 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 317).mp (by decide +kernel))) hgap
  have hprev := thV_64
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (317:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((299996757594989 : ℚ) / 1000000000000) ≤ ((36779731977899 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (317:ℚ) := by decide +kernel
  have hratR : ((((299996757594989 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((36779731977899 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (317:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_66 : ((((152899437984143 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((331 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 317 < q → q < 331 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 331).mp (by decide +kernel))) hgap
  have hprev := thV_65
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (331:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((152899437984143 : ℚ) / 500000000000) ≤ ((299996757594989 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (331:ℚ) := by decide +kernel
  have hratR : ((((152899437984143 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((299996757594989 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (331:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_67 : ((((155809479448279 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((337 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 331 < q → q < 337 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 337).mp (by decide +kernel))) hgap
  have hprev := thV_66
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (337:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((155809479448279 : ℚ) / 500000000000) ≤ ((152899437984143 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (337:ℚ) := by decide +kernel
  have hratR : ((((155809479448279 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((152899437984143 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (337:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_68 : ((((12698731346977 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((347 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 337 < q → q < 347 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 347).mp (by decide +kernel))) hgap
  have hprev := thV_67
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (347:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12698731346977 : ℚ) / 40000000000) ≤ ((155809479448279 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (347:ℚ) := by decide +kernel
  have hratR : ((((12698731346977 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((155809479448279 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (347:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_69 : ((((323323355594547 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((349 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 347 < q → q < 349 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 349).mp (by decide +kernel))) hgap
  have hprev := thV_68
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (349:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((323323355594547 : ℚ) / 1000000000000) ≤ ((12698731346977 : ℚ) / 40000000000) + Work.RHContract.RegionI.logLowQ (349:ℚ) := by decide +kernel
  have hratR : ((((323323355594547 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((12698731346977 : ℚ) / 40000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (349:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_70 : ((((1645949118247 : ℚ) / 5000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((353 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 349 < q → q < 353 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 353).mp (by decide +kernel))) hgap
  have hprev := thV_69
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (353:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1645949118247 : ℚ) / 5000000000) ≤ ((323323355594547 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (353:ℚ) := by decide +kernel
  have hratR : ((((1645949118247 : ℚ) / 5000000000) : ℚ) : ℝ) ≤ ((((323323355594547 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (353:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_71 : ((((10471035813619 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((359 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 353 < q → q < 359 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 359).mp (by decide +kernel))) hgap
  have hprev := thV_70
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (359:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10471035813619 : ℚ) / 31250000000) ≤ ((1645949118247 : ℚ) / 5000000000) + Work.RHContract.RegionI.logLowQ (359:ℚ) := by decide +kernel
  have hratR : ((((10471035813619 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((1645949118247 : ℚ) / 5000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (359:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_72 : ((((340978507881783 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((367 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 359 < q → q < 367 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 367).mp (by decide +kernel))) hgap
  have hprev := thV_71
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (367:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((340978507881783 : ℚ) / 1000000000000) ≤ ((10471035813619 : ℚ) / 31250000000) + Work.RHContract.RegionI.logLowQ (367:ℚ) := by decide +kernel
  have hratR : ((((340978507881783 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((10471035813619 : ℚ) / 31250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (367:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_73 : ((((346900086299347 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((373 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 367 < q → q < 373 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 373).mp (by decide +kernel))) hgap
  have hprev := thV_72
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (373:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((346900086299347 : ℚ) / 1000000000000) ≤ ((340978507881783 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (373:ℚ) := by decide +kernel
  have hratR : ((((346900086299347 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((340978507881783 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (373:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_74 : ((((352837622502349 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((379 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 373 < q → q < 379 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 379).mp (by decide +kernel))) hgap
  have hprev := thV_73
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (379:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((352837622502349 : ℚ) / 1000000000000) ≤ ((346900086299347 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (379:ℚ) := by decide +kernel
  have hratR : ((((352837622502349 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((346900086299347 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (379:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_75 : ((((7175713149789 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((383 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 379 < q → q < 383 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 383).mp (by decide +kernel))) hgap
  have hprev := thV_74
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (383:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7175713149789 : ℚ) / 20000000000) ≤ ((352837622502349 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (383:ℚ) := by decide +kernel
  have hratR : ((((7175713149789 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ ((((352837622502349 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (383:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_76 : ((((91187309207747 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((389 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 383 < q → q < 389 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 389).mp (by decide +kernel))) hgap
  have hprev := thV_75
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (389:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((91187309207747 : ℚ) / 250000000000) ≤ ((7175713149789 : ℚ) / 20000000000) + Work.RHContract.RegionI.logLowQ (389:ℚ) := by decide +kernel
  have hratR : ((((91187309207747 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((7175713149789 : ℚ) / 20000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (389:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_77 : ((((74146634621919 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((397 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 389 < q → q < 397 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 397).mp (by decide +kernel))) hgap
  have hprev := thV_76
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (397:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((74146634621919 : ℚ) / 200000000000) ≤ ((91187309207747 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (397:ℚ) := by decide +kernel
  have hratR : ((((74146634621919 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((91187309207747 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (397:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_78 : ((((188363567267411 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((401 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 397 < q → q < 401 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 401).mp (by decide +kernel))) hgap
  have hprev := thV_77
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (401:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((188363567267411 : ℚ) / 500000000000) ≤ ((74146634621919 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (401:ℚ) := by decide +kernel
  have hratR : ((((188363567267411 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((74146634621919 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (401:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_79 : ((((76548169937757 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((409 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 401 < q → q < 409 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 409).mp (by decide +kernel))) hgap
  have hprev := thV_78
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (409:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((76548169937757 : ℚ) / 200000000000) ≤ ((188363567267411 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (409:ℚ) := by decide +kernel
  have hratR : ((((76548169937757 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((188363567267411 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (409:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_80 : ((((388778720606627 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((419 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 409 < q → q < 419 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 419).mp (by decide +kernel))) hgap
  have hprev := thV_79
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (419:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((388778720606627 : ℚ) / 1000000000000) ≤ ((76548169937757 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (419:ℚ) := by decide +kernel
  have hratR : ((((388778720606627 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((76548169937757 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (419:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_81 : ((((394821353438229 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((421 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 419 < q → q < 421 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 421).mp (by decide +kernel))) hgap
  have hprev := thV_80
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (421:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((394821353438229 : ℚ) / 1000000000000) ≤ ((388778720606627 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (421:ℚ) := by decide +kernel
  have hratR : ((((394821353438229 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((388778720606627 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (421:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_82 : ((((400887461526253 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((431 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 421 < q → q < 431 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 431).mp (by decide +kernel))) hgap
  have hprev := thV_81
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (431:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((400887461526253 : ℚ) / 1000000000000) ≤ ((394821353438229 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (431:ℚ) := by decide +kernel
  have hratR : ((((400887461526253 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((394821353438229 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (431:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_83 : ((((16278327970087 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((433 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 431 < q → q < 433 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 433).mp (by decide +kernel))) hgap
  have hprev := thV_82
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (433:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((16278327970087 : ℚ) / 40000000000) ≤ ((400887461526253 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (433:ℚ) := by decide +kernel
  have hratR : ((((16278327970087 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((400887461526253 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (433:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_84 : ((((41304269866317 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((439 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 433 < q → q < 439 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 439).mp (by decide +kernel))) hgap
  have hprev := thV_83
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (439:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((41304269866317 : ℚ) / 100000000000) ≤ ((16278327970087 : ℚ) / 40000000000) + Work.RHContract.RegionI.logLowQ (439:ℚ) := by decide +kernel
  have hratR : ((((41304269866317 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((16278327970087 : ℚ) / 40000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (439:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_85 : ((((83827253686227 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((443 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 439 < q → q < 443 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 443).mp (by decide +kernel))) hgap
  have hprev := thV_84
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (443:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((83827253686227 : ℚ) / 200000000000) ≤ ((41304269866317 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (443:ℚ) := by decide +kernel
  have hratR : ((((83827253686227 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((41304269866317 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (443:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_86 : ((((425243291316797 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((449 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 443 < q → q < 449 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 449).mp (by decide +kernel))) hgap
  have hprev := thV_85
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (449:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((425243291316797 : ℚ) / 1000000000000) ≤ ((83827253686227 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (449:ℚ) := by decide +kernel
  have hratR : ((((425243291316797 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((83827253686227 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (449:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_87 : ((((431367974705611 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((457 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 449 < q → q < 457 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 457).mp (by decide +kernel))) hgap
  have hprev := thV_86
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (457:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((431367974705611 : ℚ) / 1000000000000) ≤ ((425243291316797 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (457:ℚ) := by decide +kernel
  have hratR : ((((431367974705611 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((425243291316797 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (457:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_88 : ((((13671917898329 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((461 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 457 < q → q < 461 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 461).mp (by decide +kernel))) hgap
  have hprev := thV_87
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (461:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13671917898329 : ℚ) / 31250000000) ≤ ((431367974705611 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (461:ℚ) := by decide +kernel
  have hratR : ((((13671917898329 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((431367974705611 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (461:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_89 : ((((221819549899267 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((463 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 461 < q → q < 463 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 463).mp (by decide +kernel))) hgap
  have hprev := thV_88
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (463:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((221819549899267 : ℚ) / 500000000000) ≤ ((13671917898329 : ℚ) / 31250000000) + Work.RHContract.RegionI.logLowQ (463:ℚ) := by decide +kernel
  have hratR : ((((221819549899267 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((13671917898329 : ℚ) / 31250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (463:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_90 : ((((449785429054123 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((467 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 463 < q → q < 467 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 467).mp (by decide +kernel))) hgap
  have hprev := thV_89
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (467:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((449785429054123 : ℚ) / 1000000000000) ≤ ((221819549899267 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (467:ℚ) := by decide +kernel
  have hratR : ((((449785429054123 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((221819549899267 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (467:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_91 : ((((227978564824727 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((479 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 467 < q → q < 479 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 479).mp (by decide +kernel))) hgap
  have hprev := thV_90
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (479:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((227978564824727 : ℚ) / 500000000000) ≤ ((449785429054123 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (479:ℚ) := by decide +kernel
  have hratR : ((((227978564824727 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((449785429054123 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (479:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_92 : ((((462145393770457 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((487 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 479 < q → q < 487 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 487).mp (by decide +kernel))) hgap
  have hprev := thV_91
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (487:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((462145393770457 : ℚ) / 1000000000000) ≤ ((227978564824727 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (487:ℚ) := by decide +kernel
  have hratR : ((((462145393770457 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((227978564824727 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (487:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_93 : ((((468341837896171 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((491 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 487 < q → q < 491 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 491).mp (by decide +kernel))) hgap
  have hprev := thV_92
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (491:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((468341837896171 : ℚ) / 1000000000000) ≤ ((462145393770457 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (491:ℚ) := by decide +kernel
  have hratR : ((((468341837896171 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((462145393770457 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (491:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_94 : ((((237277221994921 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((499 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 491 < q → q < 499 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 499).mp (by decide +kernel))) hgap
  have hprev := thV_93
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (499:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((237277221994921 : ℚ) / 500000000000) ≤ ((468341837896171 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (499:ℚ) := by decide +kernel
  have hratR : ((((237277221994921 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((468341837896171 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (499:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_95 : ((((240387517078931 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((503 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 499 < q → q < 503 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 503).mp (by decide +kernel))) hgap
  have hprev := thV_94
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (503:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((240387517078931 : ℚ) / 500000000000) ≤ ((237277221994921 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (503:ℚ) := by decide +kernel
  have hratR : ((((240387517078931 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((237277221994921 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (503:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_96 : ((((121751870543083 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((509 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 503 < q → q < 509 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 509).mp (by decide +kernel))) hgap
  have hprev := thV_95
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (509:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((121751870543083 : ℚ) / 250000000000) ≤ ((240387517078931 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (509:ℚ) := by decide +kernel
  have hratR : ((((121751870543083 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((240387517078931 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (509:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_97 : ((((98652646442349 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((521 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 509 < q → q < 521 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 521).mp (by decide +kernel))) hgap
  have hprev := thV_96
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (521:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((98652646442349 : ℚ) / 200000000000) ≤ ((121751870543083 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (521:ℚ) := by decide +kernel
  have hratR : ((((98652646442349 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((121751870543083 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (521:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_98 : ((((49952281367347 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((523 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 521 < q → q < 523 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 523).mp (by decide +kernel))) hgap
  have hprev := thV_97
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (523:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((49952281367347 : ℚ) / 100000000000) ≤ ((98652646442349 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (523:ℚ) := by decide +kernel
  have hratR : ((((49952281367347 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((98652646442349 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (523:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_99 : ((((63227029118747 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((541 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 523 < q → q < 541 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 541).mp (by decide +kernel))) hgap
  have hprev := thV_98
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (541:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((63227029118747 : ℚ) / 125000000000) ≤ ((49952281367347 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (541:ℚ) := by decide +kernel
  have hratR : ((((63227029118747 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((49952281367347 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (541:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_100 : ((((256060340875029 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((547 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 541 < q → q < 547 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 547).mp (by decide +kernel))) hgap
  have hprev := thV_99
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (547:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((256060340875029 : ℚ) / 500000000000) ≤ ((63227029118747 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (547:ℚ) := by decide +kernel
  have hratR : ((((256060340875029 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((63227029118747 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (547:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_101 : ((((103688649397529 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((557 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 547 < q → q < 557 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 557).mp (by decide +kernel))) hgap
  have hprev := thV_100
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (557:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((103688649397529 : ℚ) / 200000000000) ≤ ((256060340875029 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (557:ℚ) := by decide +kernel
  have hratR : ((((103688649397529 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((256060340875029 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (557:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_102 : ((((104955305322689 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((563 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 557 < q → q < 563 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 563).mp (by decide +kernel))) hgap
  have hprev := thV_101
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (563:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((104955305322689 : ℚ) / 200000000000) ≤ ((103688649397529 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (563:ℚ) := by decide +kernel
  have hratR : ((((104955305322689 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((103688649397529 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (563:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_103 : ((((531120407045231 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((569 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 563 < q → q < 569 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 569).mp (by decide +kernel))) hgap
  have hprev := thV_102
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (569:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((531120407045231 : ℚ) / 1000000000000) ≤ ((104955305322689 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (569:ℚ) := by decide +kernel
  have hratR : ((((531120407045231 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((104955305322689 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (569:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_104 : ((((537467796252547 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((571 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 569 < q → q < 571 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 571).mp (by decide +kernel))) hgap
  have hprev := thV_103
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (571:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((537467796252547 : ℚ) / 1000000000000) ≤ ((531120407045231 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (571:ℚ) := by decide +kernel
  have hratR : ((((537467796252547 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((531120407045231 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (571:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_105 : ((((108765127703343 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((577 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 571 < q → q < 577 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 577).mp (by decide +kernel))) hgap
  have hprev := thV_104
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (577:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((108765127703343 : ℚ) / 200000000000) ≤ ((537467796252547 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (577:ℚ) := by decide +kernel
  have hratR : ((((108765127703343 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((537467796252547 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (577:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_106 : ((((550200663334203 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((587 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 577 < q → q < 587 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 587).mp (by decide +kernel))) hgap
  have hprev := thV_105
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (587:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((550200663334203 : ℚ) / 1000000000000) ≤ ((108765127703343 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (587:ℚ) := by decide +kernel
  have hratR : ((((550200663334203 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((108765127703343 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (587:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_107 : ((((556585857730861 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((593 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 587 < q → q < 593 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 593).mp (by decide +kernel))) hgap
  have hprev := thV_106
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (593:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((556585857730861 : ℚ) / 1000000000000) ≤ ((550200663334203 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (593:ℚ) := by decide +kernel
  have hratR : ((((556585857730861 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((550200663334203 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (593:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_108 : ((((140745279831659 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((599 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 593 < q → q < 599 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 599).mp (by decide +kernel))) hgap
  have hprev := thV_107
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (599:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((140745279831659 : ℚ) / 250000000000) ≤ ((556585857730861 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (599:ℚ) := by decide +kernel
  have hratR : ((((140745279831659 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((556585857730861 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (599:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_109 : ((((569379714258831 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((601 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 599 < q → q < 601 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 601).mp (by decide +kernel))) hgap
  have hprev := thV_108
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (601:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((569379714258831 : ℚ) / 1000000000000) ≤ ((140745279831659 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (601:ℚ) := by decide +kernel
  have hratR : ((((569379714258831 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((140745279831659 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (601:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_110 : ((((11515764860951 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((607 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 601 < q → q < 607 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 607).mp (by decide +kernel))) hgap
  have hprev := thV_109
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (607:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11515764860951 : ℚ) / 20000000000) ≤ ((569379714258831 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (607:ℚ) := by decide +kernel
  have hratR : ((((11515764860951 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ ((((569379714258831 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (607:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_111 : ((((291103303990573 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((613 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 607 < q → q < 613 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 613).mp (by decide +kernel))) hgap
  have hprev := thV_110
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (613:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((291103303990573 : ℚ) / 500000000000) ≤ ((11515764860951 : ℚ) / 20000000000) + Work.RHContract.RegionI.logLowQ (613:ℚ) := by decide +kernel
  have hratR : ((((291103303990573 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((11515764860951 : ℚ) / 20000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (613:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_112 : ((((588631477002711 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((617 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 613 < q → q < 617 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 617).mp (by decide +kernel))) hgap
  have hprev := thV_111
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (617:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((588631477002711 : ℚ) / 1000000000000) ≤ ((291103303990573 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (617:ℚ) := by decide +kernel
  have hratR : ((((588631477002711 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((291103303990573 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (617:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_113 : ((((18595611946033 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((619 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 617 < q → q < 619 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 619).mp (by decide +kernel))) hgap
  have hprev := thV_112
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (619:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((18595611946033 : ℚ) / 31250000000) ≤ ((588631477002711 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (619:ℚ) := by decide +kernel
  have hratR : ((((18595611946033 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((588631477002711 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (619:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_114 : ((((601506888133257 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((631 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 619 < q → q < 631 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 631).mp (by decide +kernel))) hgap
  have hprev := thV_113
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (631:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((601506888133257 : ℚ) / 1000000000000) ≤ ((18595611946033 : ℚ) / 31250000000) + Work.RHContract.RegionI.logLowQ (631:ℚ) := by decide +kernel
  have hratR : ((((601506888133257 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((18595611946033 : ℚ) / 31250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (631:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_115 : ((((303984958793919 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((641 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 631 < q → q < 641 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 641).mp (by decide +kernel))) hgap
  have hprev := thV_114
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (641:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((303984958793919 : ℚ) / 500000000000) ≤ ((601506888133257 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (641:ℚ) := by decide +kernel
  have hratR : ((((303984958793919 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((601506888133257 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (641:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_116 : ((((76804507788717 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((643 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 641 < q → q < 643 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 643).mp (by decide +kernel))) hgap
  have hprev := thV_115
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (643:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((76804507788717 : ℚ) / 125000000000) ≤ ((303984958793919 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (643:ℚ) := by decide +kernel
  have hratR : ((((76804507788717 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((303984958793919 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (643:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_117 : ((((620908408601897 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((647 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 643 < q → q < 647 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 647).mp (by decide +kernel))) hgap
  have hprev := thV_116
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (647:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((620908408601897 : ℚ) / 1000000000000) ≤ ((76804507788717 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (647:ℚ) := by decide +kernel
  have hratR : ((((620908408601897 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((76804507788717 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (647:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_118 : ((((627389985728833 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((653 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 647 < q → q < 653 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 653).mp (by decide +kernel))) hgap
  have hprev := thV_117
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (653:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((627389985728833 : ℚ) / 1000000000000) ≤ ((620908408601897 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (653:ℚ) := by decide +kernel
  have hratR : ((((627389985728833 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((620908408601897 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (653:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_119 : ((((126776141852199 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((659 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 653 < q → q < 659 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 659).mp (by decide +kernel))) hgap
  have hprev := thV_118
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (659:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((126776141852199 : ℚ) / 200000000000) ≤ ((627389985728833 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (659:ℚ) := by decide +kernel
  have hratR : ((((126776141852199 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((627389985728833 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (659:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_120 : ((((640374463098507 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((661 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 659 < q → q < 661 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 661).mp (by decide +kernel))) hgap
  have hprev := thV_119
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (661:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((640374463098507 : ℚ) / 1000000000000) ≤ ((126776141852199 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (661:ℚ) := by decide +kernel
  have hratR : ((((640374463098507 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((126776141852199 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (661:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_121 : ((((161721552106453 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((673 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 661 < q → q < 673 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 673).mp (by decide +kernel))) hgap
  have hprev := thV_120
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (673:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((161721552106453 : ℚ) / 250000000000) ≤ ((640374463098507 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (673:ℚ) := by decide +kernel
  have hratR : ((((161721552106453 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((640374463098507 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (673:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_122 : ((((319044863133 : ℚ) / 488281250) : ℚ) : ℝ) ≤ Chebyshev.theta ((677 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 673 < q → q < 677 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 677).mp (by decide +kernel))) hgap
  have hprev := thV_121
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (677:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((319044863133 : ℚ) / 488281250) ≤ ((161721552106453 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (677:ℚ) := by decide +kernel
  have hratR : ((((319044863133 : ℚ) / 488281250) : ℚ) : ℝ) ≤ ((((161721552106453 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (677:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_123 : ((((131986074910723 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((683 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 677 < q → q < 683 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 683).mp (by decide +kernel))) hgap
  have hprev := thV_122
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (683:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((131986074910723 : ℚ) / 200000000000) ≤ ((319044863133 : ℚ) / 488281250) + Work.RHContract.RegionI.logLowQ (683:ℚ) := by decide +kernel
  have hratR : ((((131986074910723 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((319044863133 : ℚ) / 488281250) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (683:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_124 : ((((666468514375043 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((691 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 683 < q → q < 691 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 691).mp (by decide +kernel))) hgap
  have hprev := thV_123
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (691:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((666468514375043 : ℚ) / 1000000000000) ≤ ((131986074910723 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (691:ℚ) := by decide +kernel
  have hratR : ((((666468514375043 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((131986074910723 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (691:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_125 : ((((336510511129869 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((701 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 691 < q → q < 701 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 701).mp (by decide +kernel))) hgap
  have hprev := thV_124
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (701:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((336510511129869 : ℚ) / 500000000000) ≤ ((666468514375043 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (701:ℚ) := by decide +kernel
  have hratR : ((((336510511129869 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((666468514375043 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (701:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_126 : ((((67958487778393 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((709 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 701 < q → q < 709 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 709).mp (by decide +kernel))) hgap
  have hprev := thV_125
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (709:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((67958487778393 : ℚ) / 100000000000) ≤ ((336510511129869 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (709:ℚ) := by decide +kernel
  have hratR : ((((67958487778393 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((336510511129869 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (709:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_127 : ((((686162739139311 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((719 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 709 < q → q < 719 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 719).mp (by decide +kernel))) hgap
  have hprev := thV_126
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (719:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((686162739139311 : ℚ) / 1000000000000) ≤ ((67958487778393 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (719:ℚ) := by decide +kernel
  have hratR : ((((686162739139311 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((67958487778393 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (719:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_128 : ((((138550333122901 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((727 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 719 < q → q < 727 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 727).mp (by decide +kernel))) hgap
  have hprev := thV_127
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (727:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((138550333122901 : ℚ) / 200000000000) ≤ ((686162739139311 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (727:ℚ) := by decide +kernel
  have hratR : ((((138550333122901 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((686162739139311 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (727:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_129 : ((((174837202828513 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((733 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 727 < q → q < 733 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 733).mp (by decide +kernel))) hgap
  have hprev := thV_128
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (733:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((174837202828513 : ℚ) / 250000000000) ≤ ((138550333122901 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (733:ℚ) := by decide +kernel
  have hratR : ((((174837202828513 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((138550333122901 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (733:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_130 : ((((35297705461633 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((739 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 733 < q → q < 739 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 739).mp (by decide +kernel))) hgap
  have hprev := thV_129
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (739:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((35297705461633 : ℚ) / 50000000000) ≤ ((174837202828513 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (739:ℚ) := by decide +kernel
  have hratR : ((((35297705461633 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((174837202828513 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (739:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_131 : ((((356282402637519 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((743 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 739 < q → q < 743 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 743).mp (by decide +kernel))) hgap
  have hprev := thV_130
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (743:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((356282402637519 : ℚ) / 500000000000) ≤ ((35297705461633 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (743:ℚ) := by decide +kernel
  have hratR : ((((356282402637519 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((35297705461633 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (743:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_132 : ((((359593105462231 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((751 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 743 < q → q < 751 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 751).mp (by decide +kernel))) hgap
  have hprev := thV_131
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (751:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((359593105462231 : ℚ) / 500000000000) ≤ ((356282402637519 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (751:ℚ) := by decide +kernel
  have hratR : ((((359593105462231 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((356282402637519 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (751:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_133 : ((((725815574175559 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((757 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 751 < q → q < 757 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 757).mp (by decide +kernel))) hgap
  have hprev := thV_132
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (757:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((725815574175559 : ℚ) / 1000000000000) ≤ ((359593105462231 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (757:ℚ) := by decide +kernel
  have hratR : ((((725815574175559 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((359593105462231 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (757:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_134 : ((((732450207531081 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((761 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 757 < q → q < 761 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 761).mp (by decide +kernel))) hgap
  have hprev := thV_133
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (761:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((732450207531081 : ℚ) / 1000000000000) ≤ ((725815574175559 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (761:ℚ) := by decide +kernel
  have hratR : ((((732450207531081 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((725815574175559 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (761:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_135 : ((((739095298498247 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((769 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 761 < q → q < 769 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 769).mp (by decide +kernel))) hgap
  have hprev := thV_134
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (769:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((739095298498247 : ℚ) / 1000000000000) ≤ ((732450207531081 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (769:ℚ) := by decide +kernel
  have hratR : ((((739095298498247 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((732450207531081 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (769:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_136 : ((((372872788772247 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((773 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 769 < q → q < 773 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 773).mp (by decide +kernel))) hgap
  have hprev := thV_135
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (773:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((372872788772247 : ℚ) / 500000000000) ≤ ((739095298498247 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (773:ℚ) := by decide +kernel
  have hratR : ((((372872788772247 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((739095298498247 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (773:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_137 : ((((752413805790571 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((787 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 773 < q → q < 787 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 787).mp (by decide +kernel))) hgap
  have hprev := thV_136
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (787:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((752413805790571 : ℚ) / 1000000000000) ≤ ((372872788772247 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (787:ℚ) := by decide +kernel
  have hratR : ((((752413805790571 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((372872788772247 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (787:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_138 : ((((759094660467021 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((797 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 787 < q → q < 797 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 797).mp (by decide +kernel))) hgap
  have hprev := thV_137
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (797:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((759094660467021 : ℚ) / 1000000000000) ≤ ((752413805790571 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (797:ℚ) := by decide +kernel
  have hratR : ((((759094660467021 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((752413805790571 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (797:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_139 : ((((765790459381739 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((809 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 797 < q → q < 809 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 809).mp (by decide +kernel))) hgap
  have hprev := thV_138
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (809:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((765790459381739 : ℚ) / 1000000000000) ≤ ((759094660467021 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (809:ℚ) := by decide +kernel
  have hratR : ((((765790459381739 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((759094660467021 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (809:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_140 : ((((386244363716757 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((811 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 809 < q → q < 811 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 811).mp (by decide +kernel))) hgap
  have hprev := thV_139
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (811:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((386244363716757 : ℚ) / 500000000000) ≤ ((765790459381739 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (811:ℚ) := by decide +kernel
  have hratR : ((((386244363716757 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((765790459381739 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (811:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_141 : ((((389599625270313 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((821 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 811 < q → q < 821 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 821).mp (by decide +kernel))) hgap
  have hprev := thV_140
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (821:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((389599625270313 : ℚ) / 500000000000) ≤ ((386244363716757 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (821:ℚ) := by decide +kernel
  have hratR : ((((389599625270313 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((386244363716757 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (821:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_142 : ((((785912206738963 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((823 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 821 < q → q < 823 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 823).mp (by decide +kernel))) hgap
  have hprev := thV_141
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (823:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((785912206738963 : ℚ) / 1000000000000) ≤ ((389599625270313 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (823:ℚ) := by decide +kernel
  have hratR : ((((785912206738963 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((389599625270313 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (823:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_143 : ((((792630011431647 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((827 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 823 < q → q < 827 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 827).mp (by decide +kernel))) hgap
  have hprev := thV_142
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (827:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((792630011431647 : ℚ) / 1000000000000) ≤ ((785912206738963 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (827:ℚ) := by decide +kernel
  have hratR : ((((792630011431647 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((785912206738963 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (827:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_144 : ((((399675115792221 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((829 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 827 < q → q < 829 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 829).mp (by decide +kernel))) hgap
  have hprev := thV_143
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (829:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((399675115792221 : ℚ) / 500000000000) ≤ ((792630011431647 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (829:ℚ) := by decide +kernel
  have hratR : ((((399675115792221 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((792630011431647 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (829:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_145 : ((((806082442288569 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((839 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 829 < q → q < 839 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 839).mp (by decide +kernel))) hgap
  have hprev := thV_144
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (839:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((806082442288569 : ℚ) / 1000000000000) ≤ ((399675115792221 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (839:ℚ) := by decide +kernel
  have hratR : ((((806082442288569 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((399675115792221 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (839:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_146 : ((((812831201833721 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((853 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 839 < q → q < 853 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 853).mp (by decide +kernel))) hgap
  have hprev := thV_145
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (853:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((812831201833721 : ℚ) / 1000000000000) ≤ ((806082442288569 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (853:ℚ) := by decide +kernel
  have hratR : ((((812831201833721 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((806082442288569 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (853:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_147 : ((((819584639749979 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((857 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 853 < q → q < 857 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 857).mp (by decide +kernel))) hgap
  have hprev := thV_146
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (857:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((819584639749979 : ℚ) / 1000000000000) ≤ ((812831201833721 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (857:ℚ) := by decide +kernel
  have hratR : ((((819584639749979 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((812831201833721 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (857:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_148 : ((((826340408669623 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((859 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 857 < q → q < 859 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 859).mp (by decide +kernel))) hgap
  have hprev := thV_147
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (859:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((826340408669623 : ℚ) / 1000000000000) ≤ ((819584639749979 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (859:ℚ) := by decide +kernel
  have hratR : ((((826340408669623 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((819584639749979 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (859:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_149 : ((((416550411679183 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((863 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 859 < q → q < 863 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 863).mp (by decide +kernel))) hgap
  have hprev := thV_148
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (863:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((416550411679183 : ℚ) / 500000000000) ≤ ((826340408669623 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (863:ℚ) := by decide +kernel
  have hratR : ((((416550411679183 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((826340408669623 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (863:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_150 : ((((419938665174199 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((877 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 863 < q → q < 877 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 877).mp (by decide +kernel))) hgap
  have hprev := thV_149
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (877:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((419938665174199 : ℚ) / 500000000000) ≤ ((416550411679183 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (877:ℚ) := by decide +kernel
  have hratR : ((((419938665174199 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((416550411679183 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (877:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_151 : ((((423329193985997 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((881 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 877 < q → q < 881 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 881).mp (by decide +kernel))) hgap
  have hprev := thV_150
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (881:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((423329193985997 : ℚ) / 500000000000) ≤ ((419938665174199 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (881:ℚ) := by decide +kernel
  have hratR : ((((423329193985997 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((419938665174199 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (881:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_152 : ((((426720856585129 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((883 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 881 < q → q < 883 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 883).mp (by decide +kernel))) hgap
  have hprev := thV_151
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (883:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((426720856585129 : ℚ) / 500000000000) ≤ ((423329193985997 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (883:ℚ) := by decide +kernel
  have hratR : ((((426720856585129 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((423329193985997 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (883:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_153 : ((((215057389537557 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((887 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 883 < q → q < 887 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 887).mp (by decide +kernel))) hgap
  have hprev := thV_152
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (887:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((215057389537557 : ℚ) / 250000000000) ≤ ((426720856585129 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (887:ℚ) := by decide +kernel
  have hratR : ((((215057389537557 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((426720856585129 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (887:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_154 : ((((867039700598003 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((907 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 887 < q → q < 907 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 907).mp (by decide +kernel))) hgap
  have hprev := thV_153
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (907:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((867039700598003 : ℚ) / 1000000000000) ≤ ((215057389537557 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (907:ℚ) := by decide +kernel
  have hratR : ((((867039700598003 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((215057389537557 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (907:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_155 : ((((873854243492923 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((911 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 907 < q → q < 911 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 911).mp (by decide +kernel))) hgap
  have hprev := thV_154
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (911:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((873854243492923 : ℚ) / 1000000000000) ≤ ((867039700598003 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (911:ℚ) := by decide +kernel
  have hratR : ((((873854243492923 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((867039700598003 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (911:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_156 : ((((880677529612939 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((919 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 911 < q → q < 919 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 919).mp (by decide +kernel))) hgap
  have hprev := thV_155
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (919:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((880677529612939 : ℚ) / 1000000000000) ≤ ((873854243492923 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (919:ℚ) := by decide +kernel
  have hratR : ((((880677529612939 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((873854243492923 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (919:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_157 : ((((887511638349413 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((929 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 919 < q → q < 929 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 929).mp (by decide +kernel))) hgap
  have hprev := thV_156
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (929:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((887511638349413 : ℚ) / 1000000000000) ≤ ((880677529612939 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (929:ℚ) := by decide +kernel
  have hratR : ((((887511638349413 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((880677529612939 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (929:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_158 : ((((894354321629311 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((937 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 929 < q → q < 937 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 937).mp (by decide +kernel))) hgap
  have hprev := thV_157
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (937:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((894354321629311 : ℚ) / 1000000000000) ≤ ((887511638349413 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (937:ℚ) := by decide +kernel
  have hratR : ((((894354321629311 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((887511638349413 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (937:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_159 : ((((225300316191639 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((941 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 937 < q → q < 941 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 941).mp (by decide +kernel))) hgap
  have hprev := thV_158
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (941:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((225300316191639 : ℚ) / 250000000000) ≤ ((894354321629311 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (941:ℚ) := by decide +kernel
  have hratR : ((((225300316191639 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((894354321629311 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (941:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_160 : ((((454027281928701 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((947 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 941 < q → q < 947 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 947).mp (by decide +kernel))) hgap
  have hprev := thV_159
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (947:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((454027281928701 : ℚ) / 500000000000) ≤ ((225300316191639 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (947:ℚ) := by decide +kernel
  have hratR : ((((454027281928701 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((225300316191639 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (947:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_161 : ((((228728544689679 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((953 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 947 < q → q < 953 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 953).mp (by decide +kernel))) hgap
  have hprev := thV_160
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (953:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((228728544689679 : ℚ) / 250000000000) ≤ ((454027281928701 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (953:ℚ) := by decide +kernel
  have hratR : ((((228728544689679 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((454027281928701 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (953:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_162 : ((((921788377251829 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((967 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 953 < q → q < 967 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 967).mp (by decide +kernel))) hgap
  have hprev := thV_161
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (967:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((921788377251829 : ℚ) / 1000000000000) ≤ ((228728544689679 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (967:ℚ) := by decide +kernel
  have hratR : ((((921788377251829 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((228728544689679 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (967:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_163 : ((((46433335185889 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((971 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 967 < q → q < 971 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 971).mp (by decide +kernel))) hgap
  have hprev := thV_162
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (971:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((46433335185889 : ℚ) / 50000000000) ≤ ((921788377251829 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (971:ℚ) := by decide +kernel
  have hratR : ((((46433335185889 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((921788377251829 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (971:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_164 : ((((935551190367483 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((977 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 971 < q → q < 977 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 977).mp (by decide +kernel))) hgap
  have hprev := thV_163
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (977:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((935551190367483 : ℚ) / 1000000000000) ≤ ((46433335185889 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (977:ℚ) := by decide +kernel
  have hratR : ((((935551190367483 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((46433335185889 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (977:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_165 : ((((94244179948529 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((983 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 977 < q → q < 983 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 983).mp (by decide +kernel))) hgap
  have hprev := thV_164
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (983:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((94244179948529 : ℚ) / 100000000000) ≤ ((935551190367483 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (983:ℚ) := by decide +kernel
  have hratR : ((((94244179948529 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((935551190367483 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (983:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_166 : ((((46354517286 : ℚ) / 48828125) : ℚ) : ℝ) ≤ Chebyshev.theta ((991 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 983 < q → q < 991 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 991).mp (by decide +kernel))) hgap
  have hprev := thV_165
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (991:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((46354517286 : ℚ) / 48828125) ≤ ((94244179948529 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (991:ℚ) := by decide +kernel
  have hratR : ((((46354517286 : ℚ) / 48828125) : ℚ) : ℝ) ≤ ((((94244179948529 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (991:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_167 : ((((478122632392451 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((997 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 991 < q → q < 997 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 997).mp (by decide +kernel))) hgap
  have hprev := thV_166
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (997:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((478122632392451 : ℚ) / 500000000000) ≤ ((46354517286 : ℚ) / 48828125) + Work.RHContract.RegionI.logLowQ (997:ℚ) := by decide +kernel
  have hratR : ((((478122632392451 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((46354517286 : ℚ) / 48828125) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (997:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_168 : ((((240790494950729 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1009 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 997 < q → q < 1009 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1009).mp (by decide +kernel))) hgap
  have hprev := thV_167
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1009:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((240790494950729 : ℚ) / 250000000000) ≤ ((478122632392451 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (1009:ℚ) := by decide +kernel
  have hratR : ((((240790494950729 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((478122632392451 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1009:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_169 : ((((38803306052193 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1013 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1009 < q → q < 1013 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1013).mp (by decide +kernel))) hgap
  have hprev := thV_168
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1013:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((38803306052193 : ℚ) / 40000000000) ≤ ((240790494950729 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (1013:ℚ) := by decide +kernel
  have hratR : ((((38803306052193 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((240790494950729 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1013:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_170 : ((((244252307083927 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1019 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1013 < q → q < 1019 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1019).mp (by decide +kernel))) hgap
  have hprev := thV_169
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1019:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((244252307083927 : ℚ) / 250000000000) ≤ ((38803306052193 : ℚ) / 40000000000) + Work.RHContract.RegionI.logLowQ (1019:ℚ) := by decide +kernel
  have hratR : ((((244252307083927 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((38803306052193 : ℚ) / 40000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1019:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_171 : ((((983937766151533 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1021 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1019 < q → q < 1021 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1021).mp (by decide +kernel))) hgap
  have hprev := thV_170
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1021:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((983937766151533 : ℚ) / 1000000000000) ≤ ((244252307083927 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (1021:ℚ) := by decide +kernel
  have hratR : ((((983937766151533 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((244252307083927 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1021:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_172 : ((((19817521012659 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1031 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1021 < q → q < 1031 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1031).mp (by decide +kernel))) hgap
  have hprev := thV_171
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1031:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((19817521012659 : ℚ) / 20000000000) ≤ ((983937766151533 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (1031:ℚ) := by decide +kernel
  have hratR : ((((19817521012659 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ ((((983937766151533 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1031:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_173 : ((((99781627309947 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1033 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1031 < q → q < 1033 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1033).mp (by decide +kernel))) hgap
  have hprev := thV_172
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1033:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((99781627309947 : ℚ) / 100000000000) ≤ ((19817521012659 : ℚ) / 20000000000) + Work.RHContract.RegionI.logLowQ (1033:ℚ) := by decide +kernel
  have hratR : ((((99781627309947 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((19817521012659 : ℚ) / 20000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1033:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_174 : ((((1004762287087969 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1039 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1033 < q → q < 1039 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1039).mp (by decide +kernel))) hgap
  have hprev := thV_173
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1039:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1004762287087969 : ℚ) / 1000000000000) ≤ ((99781627309947 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (1039:ℚ) := by decide +kernel
  have hratR : ((((1004762287087969 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((99781627309947 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1039:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_175 : ((((202343575938753 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1049 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1039 < q → q < 1049 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1049).mp (by decide +kernel))) hgap
  have hprev := thV_174
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1049:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((202343575938753 : ℚ) / 200000000000) ≤ ((1004762287087969 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (1049:ℚ) := by decide +kernel
  have hratR : ((((202343575938753 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((1004762287087969 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1049:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_176 : ((((509337688531021 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1051 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1049 < q → q < 1051 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1051).mp (by decide +kernel))) hgap
  have hprev := thV_175
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1051:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((509337688531021 : ℚ) / 500000000000) ≤ ((202343575938753 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (1051:ℚ) := by decide +kernel
  have hratR : ((((509337688531021 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((202343575938753 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1051:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_177 : ((((128205293024757 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1061 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1051 < q → q < 1061 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1061).mp (by decide +kernel))) hgap
  have hprev := thV_176
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1061:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((128205293024757 : ℚ) / 125000000000) ≤ ((509337688531021 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (1061:ℚ) := by decide +kernel
  have hratR : ((((128205293024757 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((509337688531021 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1061:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_178 : ((((516305597286899 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1063 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1061 < q → q < 1063 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1063).mp (by decide +kernel))) hgap
  have hprev := thV_177
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1063:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((516305597286899 : ℚ) / 500000000000) ≤ ((128205293024757 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (1063:ℚ) := by decide +kernel
  have hratR : ((((516305597286899 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((128205293024757 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1063:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_179 : ((((1039585673482223 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1069 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1063 < q → q < 1069 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1069).mp (by decide +kernel))) hgap
  have hprev := thV_178
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1069:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1039585673482223 : ℚ) / 1000000000000) ≤ ((516305597286899 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (1069:ℚ) := by decide +kernel
  have hratR : ((((1039585673482223 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((516305597286899 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1069:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_180 : ((((130822106295843 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1087 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1069 < q → q < 1087 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1087).mp (by decide +kernel))) hgap
  have hprev := thV_179
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1087:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((130822106295843 : ℚ) / 125000000000) ≤ ((1039585673482223 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (1087:ℚ) := by decide +kernel
  have hratR : ((((130822106295843 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((1039585673482223 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1087:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_181 : ((((1053571700349977 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1091 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1087 < q → q < 1091 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1091).mp (by decide +kernel))) hgap
  have hprev := thV_180
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1091:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1053571700349977 : ℚ) / 1000000000000) ≤ ((130822106295843 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (1091:ℚ) := by decide +kernel
  have hratR : ((((1053571700349977 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((130822106295843 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1091:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_182 : ((((530284190917777 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1093 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1091 < q → q < 1093 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1093).mp (by decide +kernel))) hgap
  have hprev := thV_181
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1093:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((530284190917777 : ℚ) / 500000000000) ≤ ((1053571700349977 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (1093:ℚ) := by decide +kernel
  have hratR : ((((530284190917777 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1053571700349977 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1093:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_183 : ((((1067568716293229 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1097 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1093 < q → q < 1097 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1097).mp (by decide +kernel))) hgap
  have hprev := thV_182
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1097:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1067568716293229 : ℚ) / 1000000000000) ≤ ((530284190917777 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (1097:ℚ) := by decide +kernel
  have hratR : ((((1067568716293229 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((530284190917777 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1097:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_184 : ((((1074574505309883 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1103 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1097 < q → q < 1103 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1103).mp (by decide +kernel))) hgap
  have hprev := thV_183
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1103:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1074574505309883 : ℚ) / 1000000000000) ≤ ((1067568716293229 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (1103:ℚ) := by decide +kernel
  have hratR : ((((1074574505309883 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1067568716293229 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1103:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_185 : ((((1081585719294633 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1109 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1103 < q → q < 1109 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1109).mp (by decide +kernel))) hgap
  have hprev := thV_184
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1109:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1081585719294633 : ℚ) / 1000000000000) ≤ ((1074574505309883 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (1109:ℚ) := by decide +kernel
  have hratR : ((((1081585719294633 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1074574505309883 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1109:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_186 : ((((544302060545551 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1117 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1109 < q → q < 1117 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1117).mp (by decide +kernel))) hgap
  have hprev := thV_185
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1117:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((544302060545551 : ℚ) / 500000000000) ≤ ((1081585719294633 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (1117:ℚ) := by decide +kernel
  have hratR : ((((544302060545551 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1081585719294633 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1117:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_187 : ((((27390697001081 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1123 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1117 < q → q < 1123 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1123).mp (by decide +kernel))) hgap
  have hprev := thV_186
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1123:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((27390697001081 : ℚ) / 25000000000) ≤ ((544302060545551 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (1123:ℚ) := by decide +kernel
  have hratR : ((((27390697001081 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((544302060545551 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1123:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_188 : ((((110265696760479 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1129 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1123 < q → q < 1129 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1129).mp (by decide +kernel))) hgap
  have hprev := thV_187
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1129:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((110265696760479 : ℚ) / 100000000000) ≤ ((27390697001081 : ℚ) / 25000000000) + Work.RHContract.RegionI.logLowQ (1129:ℚ) := by decide +kernel
  have hratR : ((((110265696760479 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((27390697001081 : ℚ) / 25000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1129:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_189 : ((((34678292312841 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1151 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1129 < q → q < 1151 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1151).mp (by decide +kernel))) hgap
  have hprev := thV_188
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1151:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((34678292312841 : ℚ) / 31250000000) ≤ ((110265696760479 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (1151:ℚ) := by decide +kernel
  have hratR : ((((34678292312841 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((110265696760479 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1151:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_190 : ((((1116755476528581 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1153 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1151 < q → q < 1153 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1153).mp (by decide +kernel))) hgap
  have hprev := thV_189
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1153:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1116755476528581 : ℚ) / 1000000000000) ≤ ((34678292312841 : ℚ) / 31250000000) + Work.RHContract.RegionI.logLowQ (1153:ℚ) := by decide +kernel
  have hratR : ((((1116755476528581 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((34678292312841 : ℚ) / 31250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1153:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_191 : ((((2247628469357 : ℚ) / 2000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1163 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1153 < q → q < 1163 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1163).mp (by decide +kernel))) hgap
  have hprev := thV_190
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1163:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2247628469357 : ℚ) / 2000000000) ≤ ((1116755476528581 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (1163:ℚ) := by decide +kernel
  have hratR : ((((2247628469357 : ℚ) / 2000000000) : ℚ) : ℝ) ≤ ((((1116755476528581 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1163:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_192 : ((((565439924019749 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1171 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1163 < q → q < 1171 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1171).mp (by decide +kernel))) hgap
  have hprev := thV_191
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1171:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((565439924019749 : ℚ) / 500000000000) ≤ ((2247628469357 : ℚ) / 2000000000) + Work.RHContract.RegionI.logLowQ (1171:ℚ) := by decide +kernel
  have hratR : ((((565439924019749 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((2247628469357 : ℚ) / 2000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1171:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_193 : ((((227590792970619 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1181 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1171 < q → q < 1181 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1181).mp (by decide +kernel))) hgap
  have hprev := thV_192
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1181:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((227590792970619 : ℚ) / 200000000000) ≤ ((565439924019749 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (1181:ℚ) := by decide +kernel
  have hratR : ((((227590792970619 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((565439924019749 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1181:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_194 : ((((229006629849021 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1187 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1181 < q → q < 1187 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1187).mp (by decide +kernel))) hgap
  have hprev := thV_193
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1187:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((229006629849021 : ℚ) / 200000000000) ≤ ((227590792970619 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (1187:ℚ) := by decide +kernel
  have hratR : ((((229006629849021 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((227590792970619 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1187:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_195 : ((((1152117375664603 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1193 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1187 < q → q < 1193 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1193).mp (by decide +kernel))) hgap
  have hprev := thV_194
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1193:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1152117375664603 : ℚ) / 1000000000000) ≤ ((229006629849021 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (1193:ℚ) := by decide +kernel
  have hratR : ((((1152117375664603 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((229006629849021 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1193:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_196 : ((((1159208285484083 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1201 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1193 < q → q < 1201 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1201).mp (by decide +kernel))) hgap
  have hprev := thV_195
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1201:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1159208285484083 : ℚ) / 1000000000000) ≤ ((1152117375664603 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (1201:ℚ) := by decide +kernel
  have hratR : ((((1159208285484083 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1152117375664603 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1201:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_197 : ((((1166309137390427 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1213 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1201 < q → q < 1213 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1213).mp (by decide +kernel))) hgap
  have hprev := thV_196
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1213:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1166309137390427 : ℚ) / 1000000000000) ≤ ((1159208285484083 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (1213:ℚ) := by decide +kernel
  have hratR : ((((1166309137390427 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1159208285484083 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1213:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_198 : ((((234682656296163 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1217 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1213 < q → q < 1217 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1217).mp (by decide +kernel))) hgap
  have hprev := thV_197
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1217:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((234682656296163 : ℚ) / 200000000000) ≤ ((1166309137390427 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (1217:ℚ) := by decide +kernel
  have hratR : ((((234682656296163 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((1166309137390427 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1217:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_199 : ((((590261171806951 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1223 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1217 < q → q < 1223 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1223).mp (by decide +kernel))) hgap
  have hprev := thV_198
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1223:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((590261171806951 : ℚ) / 500000000000) ≤ ((234682656296163 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (1223:ℚ) := by decide +kernel
  have hratR : ((((590261171806951 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((234682656296163 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1223:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_200 : ((((296909074930217 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1229 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1223 < q → q < 1229 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1229).mp (by decide +kernel))) hgap
  have hprev := thV_199
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1229:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((296909074930217 : ℚ) / 250000000000) ≤ ((590261171806951 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (1229:ℚ) := by decide +kernel
  have hratR : ((((296909074930217 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((590261171806951 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1229:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_201 : ((((1194751881844453 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1231 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1229 < q → q < 1231 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1231).mp (by decide +kernel))) hgap
  have hprev := thV_200
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1231:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1194751881844453 : ℚ) / 1000000000000) ≤ ((296909074930217 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (1231:ℚ) := by decide +kernel
  have hratR : ((((1194751881844453 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((296909074930217 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1231:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_202 : ((((600936163107123 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1237 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1231 < q → q < 1237 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1237).mp (by decide +kernel))) hgap
  have hprev := thV_201
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1237:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((600936163107123 : ℚ) / 500000000000) ≤ ((1194751881844453 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (1237:ℚ) := by decide +kernel
  have hratR : ((((600936163107123 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1194751881844453 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1237:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_203 : ((((302250606180443 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1249 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1237 < q → q < 1249 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1249).mp (by decide +kernel))) hgap
  have hprev := thV_202
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1249:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((302250606180443 : ℚ) / 250000000000) ≤ ((600936163107123 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (1249:ℚ) := by decide +kernel
  have hratR : ((((302250606180443 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((600936163107123 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1249:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_204 : ((((9501097638697 : ℚ) / 7812500000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1259 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1249 < q → q < 1259 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1259).mp (by decide +kernel))) hgap
  have hprev := thV_203
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1259:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9501097638697 : ℚ) / 7812500000) ≤ ((302250606180443 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (1259:ℚ) := by decide +kernel
  have hratR : ((((9501097638697 : ℚ) / 7812500000) : ℚ) : ℝ) ≤ ((((302250606180443 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1259:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_205 : ((((1223292766606649 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1277 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1259 < q → q < 1277 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1277).mp (by decide +kernel))) hgap
  have hprev := thV_204
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1277:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1223292766606649 : ℚ) / 1000000000000) ≤ ((9501097638697 : ℚ) / 7812500000) + Work.RHContract.RegionI.logLowQ (1277:ℚ) := by decide +kernel
  have hratR : ((((1223292766606649 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((9501097638697 : ℚ) / 7812500000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1277:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_206 : ((((307611650101407 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1279 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1277 < q → q < 1279 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1279).mp (by decide +kernel))) hgap
  have hprev := thV_205
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1279:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((307611650101407 : ℚ) / 250000000000) ≤ ((1223292766606649 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (1279:ℚ) := by decide +kernel
  have hratR : ((((307611650101407 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((1223292766606649 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1279:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_207 : ((((309400889191911 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1283 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1279 < q → q < 1283 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1283).mp (by decide +kernel))) hgap
  have hprev := thV_206
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1283:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((309400889191911 : ℚ) / 250000000000) ≤ ((307611650101407 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (1283:ℚ) := by decide +kernel
  have hratR : ((((309400889191911 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((307611650101407 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1283:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_208 : ((((1244765178767983 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1289 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1283 < q → q < 1289 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1289).mp (by decide +kernel))) hgap
  have hprev := thV_207
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1289:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1244765178767983 : ℚ) / 1000000000000) ≤ ((309400889191911 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (1289:ℚ) := by decide +kernel
  have hratR : ((((1244765178767983 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((309400889191911 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1289:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_209 : ((((125192835115623 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1291 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1289 < q → q < 1291 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1291).mp (by decide +kernel))) hgap
  have hprev := thV_208
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1291:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((125192835115623 : ℚ) / 100000000000) ≤ ((1244765178767983 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (1291:ℚ) := by decide +kernel
  have hratR : ((((125192835115623 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((1244765178767983 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1291:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_210 : ((((629548080168973 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1297 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1291 < q → q < 1297 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1297).mp (by decide +kernel))) hgap
  have hprev := thV_209
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1297:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((629548080168973 : ℚ) / 500000000000) ≤ ((125192835115623 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (1297:ℚ) := by decide +kernel
  have hratR : ((((629548080168973 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((125192835115623 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1297:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_211 : ((((1266267048813859 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1301 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1297 < q → q < 1301 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1301).mp (by decide +kernel))) hgap
  have hprev := thV_210
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1301:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1266267048813859 : ℚ) / 1000000000000) ≤ ((629548080168973 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (1301:ℚ) := by decide +kernel
  have hratR : ((((1266267048813859 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((629548080168973 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1301:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_212 : ((((39794983543387 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1303 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1301 < q → q < 1303 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1303).mp (by decide +kernel))) hgap
  have hprev := thV_211
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1303:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((39794983543387 : ℚ) / 31250000000) ≤ ((1266267048813859 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (1303:ℚ) := by decide +kernel
  have hratR : ((((39794983543387 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((1266267048813859 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1303:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_213 : ((((80038435193713 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1307 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1303 < q → q < 1307 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1307).mp (by decide +kernel))) hgap
  have hprev := thV_212
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1307:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((80038435193713 : ℚ) / 62500000000) ≤ ((39794983543387 : ℚ) / 31250000000) + Work.RHContract.RegionI.logLowQ (1307:ℚ) := by decide +kernel
  have hratR : ((((80038435193713 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((39794983543387 : ℚ) / 31250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1307:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_214 : ((((51511983689981 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1319 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1307 < q → q < 1319 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1319).mp (by decide +kernel))) hgap
  have hprev := thV_213
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1319:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((51511983689981 : ℚ) / 40000000000) ≤ ((80038435193713 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (1319:ℚ) := by decide +kernel
  have hratR : ((((51511983689981 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((80038435193713 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1319:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_215 : ((((1294985736551447 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1321 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1319 < q → q < 1321 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1321).mp (by decide +kernel))) hgap
  have hprev := thV_214
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1321:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1294985736551447 : ℚ) / 1000000000000) ≤ ((51511983689981 : ℚ) / 40000000000) + Work.RHContract.RegionI.logLowQ (1321:ℚ) := by decide +kernel
  have hratR : ((((1294985736551447 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((51511983689981 : ℚ) / 40000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1321:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_216 : ((((1302176412583179 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1327 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1321 < q → q < 1327 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1327).mp (by decide +kernel))) hgap
  have hprev := thV_215
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1327:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1302176412583179 : ℚ) / 1000000000000) ≤ ((1294985736551447 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (1327:ℚ) := by decide +kernel
  have hratR : ((((1302176412583179 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1294985736551447 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1327:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_217 : ((((1309392387583231 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1361 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1327 < q → q < 1361 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1361).mp (by decide +kernel))) hgap
  have hprev := thV_216
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1361:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1309392387583231 : ℚ) / 1000000000000) ≤ ((1302176412583179 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (1361:ℚ) := by decide +kernel
  have hratR : ((((1309392387583231 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1302176412583179 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1361:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_218 : ((((263322552283471 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1367 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1361 < q → q < 1367 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1367).mp (by decide +kernel))) hgap
  have hprev := thV_217
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1367:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((263322552283471 : ℚ) / 200000000000) ≤ ((1309392387583231 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (1367:ℚ) := by decide +kernel
  have hratR : ((((263322552283471 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((1309392387583231 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1367:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_219 : ((((1323837514820523 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1373 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1367 < q → q < 1373 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1373).mp (by decide +kernel))) hgap
  have hprev := thV_218
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1373:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1323837514820523 : ℚ) / 1000000000000) ≤ ((263322552283471 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (1373:ℚ) := by decide +kernel
  have hratR : ((((1323837514820523 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((263322552283471 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1373:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_220 : ((((332767019492833 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1381 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1373 < q → q < 1381 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1381).mp (by decide +kernel))) hgap
  have hprev := thV_219
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1381:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((332767019492833 : ℚ) / 250000000000) ≤ ((1323837514820523 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (1381:ℚ) := by decide +kernel
  have hratR : ((((332767019492833 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((1323837514820523 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1381:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_221 : ((((669155795471699 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1399 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1381 < q → q < 1399 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1399).mp (by decide +kernel))) hgap
  have hprev := thV_220
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1399:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((669155795471699 : ℚ) / 500000000000) ≤ ((332767019492833 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (1399:ℚ) := by decide +kernel
  have hratR : ((((669155795471699 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((332767019492833 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1399:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_222 : ((((1345562226452697 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1409 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1399 < q → q < 1409 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1409).mp (by decide +kernel))) hgap
  have hprev := thV_221
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1409:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1345562226452697 : ℚ) / 1000000000000) ≤ ((669155795471699 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (1409:ℚ) := by decide +kernel
  have hratR : ((((1345562226452697 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((669155795471699 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1409:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_223 : ((((1352822749048187 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1423 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1409 < q → q < 1423 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1423).mp (by decide +kernel))) hgap
  have hprev := thV_222
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1423:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1352822749048187 : ℚ) / 1000000000000) ≤ ((1345562226452697 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (1423:ℚ) := by decide +kernel
  have hratR : ((((1352822749048187 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1345562226452697 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1423:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_224 : ((((170010759832883 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1427 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1423 < q → q < 1427 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1427).mp (by decide +kernel))) hgap
  have hprev := thV_223
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1427:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((170010759832883 : ℚ) / 125000000000) ≤ ((1352822749048187 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (1427:ℚ) := by decide +kernel
  have hratR : ((((170010759832883 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((1352822749048187 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1427:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_225 : ((((683675404419197 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1429 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1427 < q → q < 1429 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1429).mp (by decide +kernel))) hgap
  have hprev := thV_224
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1429:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((683675404419197 : ℚ) / 500000000000) ≤ ((170010759832883 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (1429:ℚ) := by decide +kernel
  have hratR : ((((683675404419197 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((170010759832883 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1429:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_226 : ((((687309167131811 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1433 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1429 < q → q < 1433 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1433).mp (by decide +kernel))) hgap
  have hprev := thV_225
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1433:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((687309167131811 : ℚ) / 500000000000) ≤ ((683675404419197 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (1433:ℚ) := by decide +kernel
  have hratR : ((((687309167131811 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((683675404419197 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1433:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_227 : ((((1381890037967909 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1439 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1433 < q → q < 1439 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1439).mp (by decide +kernel))) hgap
  have hprev := thV_226
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1439:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1381890037967909 : ℚ) / 1000000000000) ≤ ((687309167131811 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (1439:ℚ) := by decide +kernel
  have hratR : ((((1381890037967909 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((687309167131811 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1439:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_228 : ((((1389167285691941 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1447 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1439 < q → q < 1447 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1447).mp (by decide +kernel))) hgap
  have hprev := thV_227
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1447:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1389167285691941 : ℚ) / 1000000000000) ≤ ((1381890037967909 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (1447:ℚ) := by decide +kernel
  have hratR : ((((1389167285691941 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1381890037967909 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1447:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_229 : ((((55857891757689 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1451 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1447 < q → q < 1451 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1451).mp (by decide +kernel))) hgap
  have hprev := thV_228
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1451:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((55857891757689 : ℚ) / 40000000000) ≤ ((1389167285691941 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (1451:ℚ) := by decide +kernel
  have hratR : ((((55857891757689 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((1389167285691941 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1451:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_230 : ((((280745735920639 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1453 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1451 < q → q < 1453 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1453).mp (by decide +kernel))) hgap
  have hprev := thV_229
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1453:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((280745735920639 : ℚ) / 200000000000) ≤ ((55857891757689 : ℚ) / 40000000000) + Work.RHContract.RegionI.logLowQ (1453:ℚ) := by decide +kernel
  have hratR : ((((280745735920639 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((55857891757689 : ℚ) / 40000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1453:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_231 : ((((705507093074559 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1459 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1453 < q → q < 1459 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1459).mp (by decide +kernel))) hgap
  have hprev := thV_230
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1459:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((705507093074559 : ℚ) / 500000000000) ≤ ((280745735920639 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (1459:ℚ) := by decide +kernel
  have hratR : ((((705507093074559 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((280745735920639 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1459:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_232 : ((((1418307883867119 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1471 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1459 < q → q < 1471 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1471).mp (by decide +kernel))) hgap
  have hprev := thV_231
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1471:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1418307883867119 : ℚ) / 1000000000000) ≤ ((705507093074559 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (1471:ℚ) := by decide +kernel
  have hratR : ((((1418307883867119 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((705507093074559 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1471:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_233 : ((((1425608356678787 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1481 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1471 < q → q < 1481 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1481).mp (by decide +kernel))) hgap
  have hprev := thV_232
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1481:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1425608356678787 : ℚ) / 1000000000000) ≤ ((1418307883867119 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (1481:ℚ) := by decide +kernel
  have hratR : ((((1425608356678787 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1418307883867119 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1481:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_234 : ((((57316407160733 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1483 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1481 < q → q < 1483 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1483).mp (by decide +kernel))) hgap
  have hprev := thV_233
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1483:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((57316407160733 : ℚ) / 40000000000) ≤ ((1425608356678787 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (1483:ℚ) := by decide +kernel
  have hratR : ((((57316407160733 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((1425608356678787 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1483:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_235 : ((((288042938992437 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1487 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1483 < q → q < 1487 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1487).mp (by decide +kernel))) hgap
  have hprev := thV_234
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1487:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((288042938992437 : ℚ) / 200000000000) ≤ ((57316407160733 : ℚ) / 40000000000) + Work.RHContract.RegionI.logLowQ (1487:ℚ) := by decide +kernel
  have hratR : ((((288042938992437 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((57316407160733 : ℚ) / 40000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1487:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_236 : ((((1447520554992269 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1489 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1487 < q → q < 1489 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1489).mp (by decide +kernel))) hgap
  have hprev := thV_235
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1489:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1447520554992269 : ℚ) / 1000000000000) ≤ ((288042938992437 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (1489:ℚ) := by decide +kernel
  have hratR : ((((1447520554992269 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((288042938992437 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1489:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_237 : ((((181853637223401 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1493 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1489 < q → q < 1493 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1493).mp (by decide +kernel))) hgap
  have hprev := thV_236
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1493:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((181853637223401 : ℚ) / 125000000000) ≤ ((1447520554992269 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (1493:ℚ) := by decide +kernel
  have hratR : ((((181853637223401 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((1447520554992269 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1493:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_238 : ((((1462141651282711 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1499 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1493 < q → q < 1499 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1499).mp (by decide +kernel))) hgap
  have hprev := thV_237
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1499:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1462141651282711 : ℚ) / 1000000000000) ≤ ((181853637223401 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (1499:ℚ) := by decide +kernel
  have hratR : ((((1462141651282711 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((181853637223401 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1499:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_239 : ((((91841386140149 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1511 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1499 < q → q < 1511 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1511).mp (by decide +kernel))) hgap
  have hprev := thV_238
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1511:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((91841386140149 : ℚ) / 62500000000) ≤ ((1462141651282711 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (1511:ℚ) := by decide +kernel
  have hratR : ((((91841386140149 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((1462141651282711 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1511:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_240 : ((((1476790615592679 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1523 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1511 < q → q < 1523 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1523).mp (by decide +kernel))) hgap
  have hprev := thV_239
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1523:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1476790615592679 : ℚ) / 1000000000000) ≤ ((91841386140149 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (1523:ℚ) := by decide +kernel
  have hratR : ((((1476790615592679 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((91841386140149 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1523:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_241 : ((((1484124291985737 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1531 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1523 < q → q < 1531 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1531).mp (by decide +kernel))) hgap
  have hprev := thV_240
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1531:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1484124291985737 : ℚ) / 1000000000000) ≤ ((1476790615592679 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (1531:ℚ) := by decide +kernel
  have hratR : ((((1484124291985737 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1476790615592679 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1531:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_242 : ((((2982931551671 : ℚ) / 2000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1543 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1531 < q → q < 1543 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1543).mp (by decide +kernel))) hgap
  have hprev := thV_241
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1543:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2982931551671 : ℚ) / 2000000000) ≤ ((1484124291985737 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (1543:ℚ) := by decide +kernel
  have hratR : ((((2982931551671 : ℚ) / 2000000000) : ℚ) : ℝ) ≤ ((((1484124291985737 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1543:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_243 : ((((1498811140673317 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1549 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1543 < q → q < 1549 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1549).mp (by decide +kernel))) hgap
  have hprev := thV_242
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1549:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1498811140673317 : ℚ) / 1000000000000) ≤ ((2982931551671 : ℚ) / 2000000000) + Work.RHContract.RegionI.logLowQ (1549:ℚ) := by decide +kernel
  have hratR : ((((1498811140673317 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2982931551671 : ℚ) / 2000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1549:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_244 : ((((753079542246933 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1553 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1549 < q → q < 1553 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1553).mp (by decide +kernel))) hgap
  have hprev := thV_243
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1553:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((753079542246933 : ℚ) / 500000000000) ≤ ((1498811140673317 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (1553:ℚ) := by decide +kernel
  have hratR : ((((753079542246933 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1498811140673317 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1553:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_245 : ((((378377721090081 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1559 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1553 < q → q < 1559 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1559).mp (by decide +kernel))) hgap
  have hprev := thV_244
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1559:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((378377721090081 : ℚ) / 250000000000) ≤ ((753079542246933 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (1559:ℚ) := by decide +kernel
  have hratR : ((((378377721090081 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((753079542246933 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1559:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_246 : ((((19010847532501 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1567 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1559 < q → q < 1567 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1567).mp (by decide +kernel))) hgap
  have hprev := thV_245
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1567:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((19010847532501 : ℚ) / 12500000000) ≤ ((378377721090081 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (1567:ℚ) := by decide +kernel
  have hratR : ((((19010847532501 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ ((((378377721090081 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1567:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_247 : ((((191028408779467 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1571 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1567 < q → q < 1571 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1571).mp (by decide +kernel))) hgap
  have hprev := thV_246
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1571:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((191028408779467 : ℚ) / 125000000000) ≤ ((19010847532501 : ℚ) / 12500000000) + Work.RHContract.RegionI.logLowQ (1571:ℚ) := by decide +kernel
  have hratR : ((((191028408779467 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((19010847532501 : ℚ) / 12500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1571:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_248 : ((((47987244288981 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1579 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1571 < q → q < 1579 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1579).mp (by decide +kernel))) hgap
  have hprev := thV_247
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1579:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((47987244288981 : ℚ) / 31250000000) ≤ ((191028408779467 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (1579:ℚ) := by decide +kernel
  have hratR : ((((47987244288981 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((191028408779467 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1579:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_249 : ((((1542958894304673 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1583 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1579 < q → q < 1583 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1583).mp (by decide +kernel))) hgap
  have hprev := thV_248
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1583:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1542958894304673 : ℚ) / 1000000000000) ≤ ((47987244288981 : ℚ) / 31250000000) + Work.RHContract.RegionI.logLowQ (1583:ℚ) := by decide +kernel
  have hratR : ((((1542958894304673 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((47987244288981 : ℚ) / 31250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1583:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_250 : ((((96895923528143 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1597 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1583 < q → q < 1597 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1597).mp (by decide +kernel))) hgap
  have hprev := thV_249
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1597:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((96895923528143 : ℚ) / 62500000000) ≤ ((1542958894304673 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (1597:ℚ) := by decide +kernel
  have hratR : ((((96895923528143 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((1542958894304673 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1597:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_251 : ((((311542632032137 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1601 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1597 < q → q < 1601 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1601).mp (by decide +kernel))) hgap
  have hprev := thV_250
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1601:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((311542632032137 : ℚ) / 200000000000) ≤ ((96895923528143 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (1601:ℚ) := by decide +kernel
  have hratR : ((((311542632032137 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((96895923528143 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1601:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_252 : ((((1565095284523823 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1607 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1601 < q → q < 1607 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1607).mp (by decide +kernel))) hgap
  have hprev := thV_251
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1607:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1565095284523823 : ℚ) / 1000000000000) ≤ ((311542632032137 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (1607:ℚ) := by decide +kernel
  have hratR : ((((1565095284523823 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((311542632032137 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1607:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_253 : ((((314495730533643 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1609 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1607 < q → q < 1609 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1609).mp (by decide +kernel))) hgap
  have hprev := thV_252
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1609:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((314495730533643 : ℚ) / 200000000000) ≤ ((1565095284523823 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (1609:ℚ) := by decide +kernel
  have hratR : ((((314495730533643 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((1565095284523823 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1609:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_254 : ((((78993225187187 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1613 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1609 < q → q < 1613 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1613).mp (by decide +kernel))) hgap
  have hprev := thV_253
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1613:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((78993225187187 : ℚ) / 50000000000) ≤ ((314495730533643 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (1613:ℚ) := by decide +kernel
  have hratR : ((((78993225187187 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((314495730533643 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1613:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_255 : ((((793627033847409 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1619 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1613 < q → q < 1619 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1619).mp (by decide +kernel))) hgap
  have hprev := thV_254
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1619:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((793627033847409 : ℚ) / 500000000000) ≤ ((78993225187187 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (1619:ℚ) := by decide +kernel
  have hratR : ((((793627033847409 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((78993225187187 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1619:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_256 : ((((797322433106977 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1621 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1619 < q → q < 1621 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1621).mp (by decide +kernel))) hgap
  have hprev := thV_255
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1621:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((797322433106977 : ℚ) / 500000000000) ≤ ((793627033847409 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (1621:ℚ) := by decide +kernel
  have hratR : ((((797322433106977 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((793627033847409 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1621:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_257 : ((((1602039359318573 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1627 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1621 < q → q < 1627 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1627).mp (by decide +kernel))) hgap
  have hprev := thV_256
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1627:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1602039359318573 : ℚ) / 1000000000000) ≤ ((797322433106977 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (1627:ℚ) := by decide +kernel
  have hratR : ((((1602039359318573 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((797322433106977 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1627:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_258 : ((((50294999371667 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1637 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1627 < q → q < 1637 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1637).mp (by decide +kernel))) hgap
  have hprev := thV_257
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1637:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((50294999371667 : ℚ) / 31250000000) ≤ ((1602039359318573 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (1637:ℚ) := by decide +kernel
  have hratR : ((((50294999371667 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((1602039359318573 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1637:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_259 : ((((1616852743908171 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1657 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1637 < q → q < 1657 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1657).mp (by decide +kernel))) hgap
  have hprev := thV_258
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1657:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1616852743908171 : ℚ) / 1000000000000) ≤ ((50294999371667 : ℚ) / 31250000000) + Work.RHContract.RegionI.logLowQ (1657:ℚ) := by decide +kernel
  have hratR : ((((1616852743908171 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((50294999371667 : ℚ) / 31250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1657:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_260 : ((((406067280596191 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1663 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1657 < q → q < 1663 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1663).mp (by decide +kernel))) hgap
  have hprev := thV_259
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1663:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((406067280596191 : ℚ) / 250000000000) ≤ ((1616852743908171 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (1663:ℚ) := by decide +kernel
  have hratR : ((((406067280596191 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((1616852743908171 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1663:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_261 : ((((326337580652983 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1667 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1663 < q → q < 1667 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1667).mp (by decide +kernel))) hgap
  have hprev := thV_260
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1667:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((326337580652983 : ℚ) / 200000000000) ≤ ((406067280596191 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (1667:ℚ) := by decide +kernel
  have hratR : ((((326337580652983 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((406067280596191 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1667:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_262 : ((((1639107883185977 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1669 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1667 < q → q < 1669 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1669).mp (by decide +kernel))) hgap
  have hprev := thV_261
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1669:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1639107883185977 : ℚ) / 1000000000000) ≤ ((326337580652983 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (1669:ℚ) := by decide +kernel
  have hratR : ((((1639107883185977 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((326337580652983 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1669:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_263 : ((((164654214056551 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1693 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1669 < q → q < 1693 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1693).mp (by decide +kernel))) hgap
  have hprev := thV_262
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1693:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((164654214056551 : ℚ) / 100000000000) ≤ ((1639107883185977 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (1693:ℚ) := by decide +kernel
  have hratR : ((((164654214056551 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((1639107883185977 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1693:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_264 : ((((103373672364259 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1697 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1693 < q → q < 1697 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1697).mp (by decide +kernel))) hgap
  have hprev := thV_263
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1697:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((103373672364259 : ℚ) / 62500000000) ≤ ((164654214056551 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (1697:ℚ) := by decide +kernel
  have hratR : ((((103373672364259 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((164654214056551 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1697:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_265 : ((((103838534559201 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1699 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1697 < q → q < 1699 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1699).mp (by decide +kernel))) hgap
  have hprev := thV_264
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1699:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((103838534559201 : ℚ) / 62500000000) ≤ ((103373672364259 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (1699:ℚ) := by decide +kernel
  have hratR : ((((103838534559201 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((103373672364259 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1699:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_266 : ((((417215054156933 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1709 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1699 < q → q < 1709 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1709).mp (by decide +kernel))) hgap
  have hprev := thV_265
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1709:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((417215054156933 : ℚ) / 250000000000) ≤ ((103838534559201 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (1709:ℚ) := by decide +kernel
  have hratR : ((((417215054156933 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((103838534559201 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1709:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_267 : ((((52384714919417 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1721 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1709 < q → q < 1721 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1721).mp (by decide +kernel))) hgap
  have hprev := thV_266
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1721:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((52384714919417 : ℚ) / 31250000000) ≤ ((417215054156933 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (1721:ℚ) := by decide +kernel
  have hratR : ((((52384714919417 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((417215054156933 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1721:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_268 : ((((210470337456909 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1723 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1721 < q → q < 1723 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1723).mp (by decide +kernel))) hgap
  have hprev := thV_267
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1723:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((210470337456909 : ℚ) / 125000000000) ≤ ((52384714919417 : ℚ) / 31250000000) + Work.RHContract.RegionI.logLowQ (1723:ℚ) := by decide +kernel
  have hratR : ((((210470337456909 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((52384714919417 : ℚ) / 31250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1723:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_269 : ((((422805077235597 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1733 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1723 < q → q < 1733 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1733).mp (by decide +kernel))) hgap
  have hprev := thV_268
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1733:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((422805077235597 : ℚ) / 250000000000) ≤ ((210470337456909 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (1733:ℚ) := by decide +kernel
  have hratR : ((((422805077235597 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((210470337456909 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1733:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_270 : ((((424670630969889 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1741 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1733 < q → q < 1741 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1741).mp (by decide +kernel))) hgap
  have hprev := thV_269
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1741:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((424670630969889 : ℚ) / 250000000000) ≤ ((422805077235597 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (1741:ℚ) := by decide +kernel
  have hratR : ((((424670630969889 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((422805077235597 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1741:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_271 : ((((170614817918709 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1747 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1741 < q → q < 1747 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1747).mp (by decide +kernel))) hgap
  have hprev := thV_270
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1747:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((170614817918709 : ℚ) / 100000000000) ≤ ((424670630969889 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (1747:ℚ) := by decide +kernel
  have hratR : ((((170614817918709 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((424670630969889 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1747:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_272 : ((((1713617263069411 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1753 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1747 < q → q < 1753 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1753).mp (by decide +kernel))) hgap
  have hprev := thV_271
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1753:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1713617263069411 : ℚ) / 1000000000000) ≤ ((170614817918709 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (1753:ℚ) := by decide +kernel
  have hratR : ((((1713617263069411 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((170614817918709 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1753:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_273 : ((((1721089763811549 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1759 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1753 < q → q < 1759 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1759).mp (by decide +kernel))) hgap
  have hprev := thV_272
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1759:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1721089763811549 : ℚ) / 1000000000000) ≤ ((1713617263069411 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (1759:ℚ) := by decide +kernel
  have hratR : ((((1721089763811549 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1713617263069411 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1759:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_274 : ((((108035777852319 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1777 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1759 < q → q < 1777 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1777).mp (by decide +kernel))) hgap
  have hprev := thV_273
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1777:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((108035777852319 : ℚ) / 62500000000) ≤ ((1721089763811549 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (1777:ℚ) := by decide +kernel
  have hratR : ((((108035777852319 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((1721089763811549 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1777:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_275 : ((((1736058498252367 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1783 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1777 < q → q < 1783 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1783).mp (by decide +kernel))) hgap
  have hprev := thV_274
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1783:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1736058498252367 : ℚ) / 1000000000000) ≤ ((108035777852319 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (1783:ℚ) := by decide +kernel
  have hratR : ((((1736058498252367 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((108035777852319 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1783:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_276 : ((((871773395882463 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1787 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1783 < q → q < 1787 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1787).mp (by decide +kernel))) hgap
  have hprev := thV_275
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1787:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((871773395882463 : ℚ) / 500000000000) ≤ ((1736058498252367 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (1787:ℚ) := by decide +kernel
  have hratR : ((((871773395882463 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1736058498252367 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1787:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_277 : ((((350207240769167 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1789 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1787 < q → q < 1789 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1789).mp (by decide +kernel))) hgap
  have hprev := thV_276
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1789:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((350207240769167 : ℚ) / 200000000000) ≤ ((871773395882463 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (1789:ℚ) := by decide +kernel
  have hratR : ((((350207240769167 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((871773395882463 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1789:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_278 : ((((1758532301188411 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1801 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1789 < q → q < 1801 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1801).mp (by decide +kernel))) hgap
  have hprev := thV_277
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1801:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1758532301188411 : ℚ) / 1000000000000) ≤ ((350207240769167 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (1801:ℚ) := by decide +kernel
  have hratR : ((((1758532301188411 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((350207240769167 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1801:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_279 : ((((883016967821847 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1811 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1801 < q → q < 1811 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1811).mp (by decide +kernel))) hgap
  have hprev := thV_278
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1811:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((883016967821847 : ℚ) / 500000000000) ≤ ((1758532301188411 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (1811:ℚ) := by decide +kernel
  have hratR : ((((883016967821847 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1758532301188411 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1811:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_280 : ((((1773542174415773 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1823 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1811 < q → q < 1823 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1823).mp (by decide +kernel))) hgap
  have hprev := thV_279
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1823:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1773542174415773 : ℚ) / 1000000000000) ≤ ((883016967821847 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (1823:ℚ) := by decide +kernel
  have hratR : ((((1773542174415773 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((883016967821847 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1823:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_281 : ((((222631848994731 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1831 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1823 < q → q < 1831 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1831).mp (by decide +kernel))) hgap
  have hprev := thV_280
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1831:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((222631848994731 : ℚ) / 125000000000) ≤ ((1773542174415773 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (1831:ℚ) := by decide +kernel
  have hratR : ((((222631848994731 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((1773542174415773 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1831:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_282 : ((((1788576109935447 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1847 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1831 < q → q < 1847 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1847).mp (by decide +kernel))) hgap
  have hprev := thV_281
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1847:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1788576109935447 : ℚ) / 1000000000000) ≤ ((222631848994731 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (1847:ℚ) := by decide +kernel
  have hratR : ((((1788576109935447 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((222631848994731 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1847:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_283 : ((((1796104979189489 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1861 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1847 < q → q < 1861 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1861).mp (by decide +kernel))) hgap
  have hprev := thV_282
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1861:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1796104979189489 : ℚ) / 1000000000000) ≤ ((1788576109935447 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (1861:ℚ) := by decide +kernel
  have hratR : ((((1796104979189489 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1788576109935447 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1861:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_284 : ((((1803637067330431 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1867 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1861 < q → q < 1867 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1867).mp (by decide +kernel))) hgap
  have hprev := thV_283
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1867:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1803637067330431 : ℚ) / 1000000000000) ≤ ((1796104979189489 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (1867:ℚ) := by decide +kernel
  have hratR : ((((1803637067330431 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1796104979189489 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1867:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_285 : ((((362234259130821 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1871 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1867 < q → q < 1871 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1871).mp (by decide +kernel))) hgap
  have hprev := thV_284
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1871:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((362234259130821 : ℚ) / 200000000000) ≤ ((1803637067330431 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (1871:ℚ) := by decide +kernel
  have hratR : ((((362234259130821 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((1803637067330431 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1871:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_286 : ((((1818706592353949 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1873 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1871 < q → q < 1873 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1873).mp (by decide +kernel))) hgap
  have hprev := thV_285
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1873:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1818706592353949 : ℚ) / 1000000000000) ≤ ((362234259130821 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (1873:ℚ) := by decide +kernel
  have hratR : ((((1818706592353949 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((362234259130821 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1873:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_287 : ((((57070125699623 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1877 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1873 < q → q < 1877 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1877).mp (by decide +kernel))) hgap
  have hprev := thV_286
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1877:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((57070125699623 : ℚ) / 31250000000) ≤ ((1818706592353949 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (1877:ℚ) := by decide +kernel
  have hratR : ((((57070125699623 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((1818706592353949 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1877:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_288 : ((((7335130069539 : ℚ) / 4000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1879 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1877 < q → q < 1879 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1879).mp (by decide +kernel))) hgap
  have hprev := thV_287
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1879:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7335130069539 : ℚ) / 4000000000) ≤ ((57070125699623 : ℚ) / 31250000000) + Work.RHContract.RegionI.logLowQ (1879:ℚ) := by decide +kernel
  have hratR : ((((7335130069539 : ℚ) / 4000000000) : ℚ) : ℝ) ≤ ((((57070125699623 : ℚ) / 31250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1879:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_289 : ((((460331580062413 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1889 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1879 < q → q < 1889 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1889).mp (by decide +kernel))) hgap
  have hprev := thV_288
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1889:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((460331580062413 : ℚ) / 250000000000) ≤ ((7335130069539 : ℚ) / 4000000000) + Work.RHContract.RegionI.logLowQ (1889:ℚ) := by decide +kernel
  have hratR : ((((460331580062413 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((7335130069539 : ℚ) / 4000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1889:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_290 : ((((92443822779477 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1901 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1889 < q → q < 1901 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1901).mp (by decide +kernel))) hgap
  have hprev := thV_289
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1901:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((92443822779477 : ℚ) / 50000000000) ≤ ((460331580062413 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (1901:ℚ) := by decide +kernel
  have hratR : ((((92443822779477 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((460331580062413 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1901:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_291 : ((((92821487109627 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1907 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1901 < q → q < 1907 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1907).mp (by decide +kernel))) hgap
  have hprev := thV_290
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1907:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((92821487109627 : ℚ) / 50000000000) ≤ ((92443822779477 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (1907:ℚ) := by decide +kernel
  have hratR : ((((92821487109627 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((92443822779477 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1907:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_292 : ((((93199308507969 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1913 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1907 < q → q < 1913 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1913).mp (by decide +kernel))) hgap
  have hprev := thV_291
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1913:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((93199308507969 : ℚ) / 50000000000) ≤ ((92821487109627 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (1913:ℚ) := by decide +kernel
  have hratR : ((((93199308507969 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((92821487109627 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1913:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_293 : ((((1871551963439209 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1931 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1913 < q → q < 1931 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1931).mp (by decide +kernel))) hgap
  have hprev := thV_292
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1931:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1871551963439209 : ℚ) / 1000000000000) ≤ ((93199308507969 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (1931:ℚ) := by decide +kernel
  have hratR : ((((1871551963439209 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((93199308507969 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1931:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_294 : ((((1879118791915817 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1933 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1931 < q → q < 1933 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1933).mp (by decide +kernel))) hgap
  have hprev := thV_293
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1933:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1879118791915817 : ℚ) / 1000000000000) ≤ ((1871551963439209 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (1933:ℚ) := by decide +kernel
  have hratR : ((((1879118791915817 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1871551963439209 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1933:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_295 : ((((75467754544509 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1949 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1933 < q → q < 1949 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1949).mp (by decide +kernel))) hgap
  have hprev := thV_294
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1949:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((75467754544509 : ℚ) / 40000000000) ≤ ((1879118791915817 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (1949:ℚ) := by decide +kernel
  have hratR : ((((75467754544509 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((1879118791915817 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1949:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_296 : ((((473567490237687 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1951 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1949 < q → q < 1951 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1951).mp (by decide +kernel))) hgap
  have hprev := thV_295
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1951:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((473567490237687 : ℚ) / 250000000000) ≤ ((75467754544509 : ℚ) / 40000000000) + Work.RHContract.RegionI.logLowQ (1951:ℚ) := by decide +kernel
  have hratR : ((((473567490237687 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((75467754544509 : ℚ) / 40000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1951:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_297 : ((((1901857271454171 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1973 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1951 < q → q < 1973 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1973).mp (by decide +kernel))) hgap
  have hprev := thV_296
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1973:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1901857271454171 : ℚ) / 1000000000000) ≤ ((473567490237687 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (1973:ℚ) := by decide +kernel
  have hratR : ((((1901857271454171 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((473567490237687 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1973:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_298 : ((((954723809198587 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1979 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1973 < q → q < 1979 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1979).mp (by decide +kernel))) hgap
  have hprev := thV_297
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1979:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((954723809198587 : ℚ) / 500000000000) ≤ ((1901857271454171 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (1979:ℚ) := by decide +kernel
  have hratR : ((((954723809198587 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1901857271454171 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1979:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_299 : ((((958520999818563 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1987 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1979 < q → q < 1987 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1987).mp (by decide +kernel))) hgap
  have hprev := thV_298
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1987:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((958520999818563 : ℚ) / 500000000000) ≤ ((954723809198587 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (1987:ℚ) := by decide +kernel
  have hratR : ((((958520999818563 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((954723809198587 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1987:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_300 : ((((1924639395954739 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1993 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1987 < q → q < 1993 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1993).mp (by decide +kernel))) hgap
  have hprev := thV_299
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1993:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1924639395954739 : ℚ) / 1000000000000) ≤ ((958520999818563 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (1993:ℚ) := by decide +kernel
  have hratR : ((((1924639395954739 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((958520999818563 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1993:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_301 : ((((386447759457111 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1997 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1993 < q → q < 1997 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1997).mp (by decide +kernel))) hgap
  have hprev := thV_300
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1997:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((386447759457111 : ℚ) / 200000000000) ≤ ((1924639395954739 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (1997:ℚ) := by decide +kernel
  have hratR : ((((386447759457111 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((1924639395954739 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1997:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_302 : ((((387967839923491 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((1999 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1997 < q → q < 1999 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1999).mp (by decide +kernel))) hgap
  have hprev := thV_301
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (1999:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((387967839923491 : ℚ) / 200000000000) ≤ ((386447759457111 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (1999:ℚ) := by decide +kernel
  have hratR : ((((387967839923491 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((386447759457111 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (1999:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_303 : ((((1947441600950521 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2003 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1999 < q → q < 2003 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2003).mp (by decide +kernel))) hgap
  have hprev := thV_302
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2003:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1947441600950521 : ℚ) / 1000000000000) ≤ ((387967839923491 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (2003:ℚ) := by decide +kernel
  have hratR : ((((1947441600950521 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((387967839923491 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2003:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_304 : ((((977523994168847 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2011 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2003 < q → q < 2011 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2011).mp (by decide +kernel))) hgap
  have hprev := thV_303
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2011:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((977523994168847 : ℚ) / 500000000000) ≤ ((1947441600950521 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (2011:ℚ) := by decide +kernel
  have hratR : ((((977523994168847 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1947441600950521 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2011:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_305 : ((((245332169359131 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2017 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2011 < q → q < 2017 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2017).mp (by decide +kernel))) hgap
  have hprev := thV_304
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2017:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((245332169359131 : ℚ) / 125000000000) ≤ ((977523994168847 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (2017:ℚ) := by decide +kernel
  have hratR : ((((245332169359131 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((977523994168847 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2017:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_306 : ((((19702716670169 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2027 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2017 < q → q < 2027 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2027).mp (by decide +kernel))) hgap
  have hprev := thV_305
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2027:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((19702716670169 : ℚ) / 10000000000) ≤ ((245332169359131 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (2027:ℚ) := by decide +kernel
  have hratR : ((((19702716670169 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ ((((245332169359131 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2027:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_307 : ((((988943482677063 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2029 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2027 < q → q < 2029 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2029).mp (by decide +kernel))) hgap
  have hprev := thV_306
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2029:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((988943482677063 : ℚ) / 500000000000) ≤ ((19702716670169 : ℚ) / 10000000000) + Work.RHContract.RegionI.logLowQ (2029:ℚ) := by decide +kernel
  have hratR : ((((988943482677063 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((19702716670169 : ℚ) / 10000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2029:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_308 : ((((1985507180122101 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2039 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2029 < q → q < 2039 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2039).mp (by decide +kernel))) hgap
  have hprev := thV_307
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2039:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1985507180122101 : ℚ) / 1000000000000) ≤ ((988943482677063 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (2039:ℚ) := by decide +kernel
  have hratR : ((((1985507180122101 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((988943482677063 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2039:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_309 : ((((99656711876813 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2053 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2039 < q → q < 2053 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2053).mp (by decide +kernel))) hgap
  have hprev := thV_308
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2053:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((99656711876813 : ℚ) / 50000000000) ≤ ((1985507180122101 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (2053:ℚ) := by decide +kernel
  have hratR : ((((99656711876813 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((1985507180122101 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2053:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_310 : ((((2000766154046471 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2063 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2053 < q → q < 2063 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2063).mp (by decide +kernel))) hgap
  have hprev := thV_309
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2063:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2000766154046471 : ℚ) / 1000000000000) ≤ ((99656711876813 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (2063:ℚ) := by decide +kernel
  have hratR : ((((2000766154046471 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((99656711876813 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2063:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_311 : ((((2008400974721357 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2069 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2063 < q → q < 2069 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2069).mp (by decide +kernel))) hgap
  have hprev := thV_310
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2069:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2008400974721357 : ℚ) / 1000000000000) ≤ ((2000766154046471 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (2069:ℚ) := by decide +kernel
  have hratR : ((((2008400974721357 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2000766154046471 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2069:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_312 : ((((2016041578544891 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2081 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2069 < q → q < 2081 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2081).mp (by decide +kernel))) hgap
  have hprev := thV_311
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2081:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2016041578544891 : ℚ) / 1000000000000) ≤ ((2008400974721357 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (2081:ℚ) := by decide +kernel
  have hratR : ((((2016041578544891 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2008400974721357 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2081:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_313 : ((((505920785745823 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2083 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2081 < q → q < 2083 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2083).mp (by decide +kernel))) hgap
  have hprev := thV_312
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2083:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((505920785745823 : ℚ) / 250000000000) ≤ ((2016041578544891 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (2083:ℚ) := by decide +kernel
  have hratR : ((((505920785745823 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((2016041578544891 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2083:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_314 : ((((2031326625887509 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2087 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2083 < q → q < 2087 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2087).mp (by decide +kernel))) hgap
  have hprev := thV_313
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2087:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2031326625887509 : ℚ) / 1000000000000) ≤ ((505920785745823 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (2087:ℚ) := by decide +kernel
  have hratR : ((((2031326625887509 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((505920785745823 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2087:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_315 : ((((1019485533323103 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2089 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2087 < q → q < 2089 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2089).mp (by decide +kernel))) hgap
  have hprev := thV_314
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2089:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1019485533323103 : ℚ) / 500000000000) ≤ ((2031326625887509 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (2089:ℚ) := by decide +kernel
  have hratR : ((((1019485533323103 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((2031326625887509 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2089:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_316 : ((((2046620282963167 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2099 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2089 < q → q < 2099 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2099).mp (by decide +kernel))) hgap
  have hprev := thV_315
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2099:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2046620282963167 : ℚ) / 1000000000000) ≤ ((1019485533323103 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (2099:ℚ) := by decide +kernel
  have hratR : ((((2046620282963167 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1019485533323103 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2099:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_317 : ((((410855040001631 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2111 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2099 < q → q < 2111 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2111).mp (by decide +kernel))) hgap
  have hprev := thV_316
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2111:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((410855040001631 : ℚ) / 200000000000) ≤ ((2046620282963167 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (2111:ℚ) := by decide +kernel
  have hratR : ((((410855040001631 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((2046620282963167 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2111:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_318 : ((((2061931064022911 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2113 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2111 < q → q < 2113 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2113).mp (by decide +kernel))) hgap
  have hprev := thV_317
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2113:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2061931064022911 : ℚ) / 1000000000000) ≤ ((410855040001631 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (2113:ℚ) := by decide +kernel
  have hratR : ((((2061931064022911 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((410855040001631 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2113:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_319 : ((((413918894336989 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2129 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2113 < q → q < 2129 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2129).mp (by decide +kernel))) hgap
  have hprev := thV_318
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2129:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((413918894336989 : ℚ) / 200000000000) ≤ ((2061931064022911 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (2129:ℚ) := by decide +kernel
  have hratR : ((((413918894336989 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((2061931064022911 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2129:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_320 : ((((259657352289273 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2131 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2129 < q → q < 2131 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2131).mp (by decide +kernel))) hgap
  have hprev := thV_319
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2131:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((259657352289273 : ℚ) / 125000000000) ≤ ((413918894336989 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (2131:ℚ) := by decide +kernel
  have hratR : ((((259657352289273 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((413918894336989 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2131:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_321 : ((((2084925976566643 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2137 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2131 < q → q < 2137 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2137).mp (by decide +kernel))) hgap
  have hprev := thV_320
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2137:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2084925976566643 : ℚ) / 1000000000000) ≤ ((259657352289273 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (2137:ℚ) := by decide +kernel
  have hratR : ((((2084925976566643 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((259657352289273 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2137:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_322 : ((((2092595004852373 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2141 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2137 < q → q < 2141 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2141).mp (by decide +kernel))) hgap
  have hprev := thV_321
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2141:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2092595004852373 : ℚ) / 1000000000000) ≤ ((2084925976566643 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (2141:ℚ) := by decide +kernel
  have hratR : ((((2092595004852373 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2084925976566643 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2141:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_323 : ((((2100264966844987 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2143 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2141 < q → q < 2143 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2143).mp (by decide +kernel))) hgap
  have hprev := thV_322
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2143:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2100264966844987 : ℚ) / 1000000000000) ≤ ((2092595004852373 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (2143:ℚ) := by decide +kernel
  have hratR : ((((2100264966844987 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2092595004852373 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2143:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_324 : ((((2107939584339491 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2153 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2143 < q → q < 2153 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2153).mp (by decide +kernel))) hgap
  have hprev := thV_323
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2153:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2107939584339491 : ℚ) / 1000000000000) ≤ ((2100264966844987 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (2153:ℚ) := by decide +kernel
  have hratR : ((((2107939584339491 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2100264966844987 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2153:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_325 : ((((1057808955346569 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2161 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2153 < q → q < 2161 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2161).mp (by decide +kernel))) hgap
  have hprev := thV_324
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2161:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1057808955346569 : ℚ) / 500000000000) ≤ ((2107939584339491 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (2161:ℚ) := by decide +kernel
  have hratR : ((((1057808955346569 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((2107939584339491 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2161:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_326 : ((((2123304532025223 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2179 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2161 < q → q < 2179 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2179).mp (by decide +kernel))) hgap
  have hprev := thV_325
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2179:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2123304532025223 : ℚ) / 1000000000000) ≤ ((1057808955346569 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (2179:ℚ) := by decide +kernel
  have hratR : ((((2123304532025223 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1057808955346569 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2179:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_327 : ((((426200421473833 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2203 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2179 < q → q < 2203 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2203).mp (by decide +kernel))) hgap
  have hprev := thV_326
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2203:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((426200421473833 : ℚ) / 200000000000) ≤ ((2123304532025223 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (2203:ℚ) := by decide +kernel
  have hratR : ((((426200421473833 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((2123304532025223 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2203:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_328 : ((((1069350748386281 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2207 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2203 < q → q < 2207 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2207).mp (by decide +kernel))) hgap
  have hprev := thV_327
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2207:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1069350748386281 : ℚ) / 500000000000) ≤ ((426200421473833 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (2207:ℚ) := by decide +kernel
  have hratR : ((((1069350748386281 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((426200421473833 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2207:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_329 : ((((2146403601109753 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2213 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2207 < q → q < 2213 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2213).mp (by decide +kernel))) hgap
  have hprev := thV_328
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2213:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2146403601109753 : ℚ) / 1000000000000) ≤ ((1069350748386281 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (2213:ℚ) := by decide +kernel
  have hratR : ((((2146403601109753 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1069350748386281 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2213:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_330 : ((((538527328482697 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2221 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2213 < q → q < 2221 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2221).mp (by decide +kernel))) hgap
  have hprev := thV_329
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2221:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((538527328482697 : ℚ) / 250000000000) ≤ ((2146403601109753 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (2221:ℚ) := by decide +kernel
  have hratR : ((((538527328482697 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((2146403601109753 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2221:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_331 : ((((1080911102444709 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2237 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2221 < q → q < 2237 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2237).mp (by decide +kernel))) hgap
  have hprev := thV_330
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2237:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1080911102444709 : ℚ) / 500000000000) ≤ ((538527328482697 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (2237:ℚ) := by decide +kernel
  have hratR : ((((1080911102444709 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((538527328482697 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2237:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_332 : ((((2169535989503157 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2239 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2237 < q → q < 2239 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2239).mp (by decide +kernel))) hgap
  have hprev := thV_331
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2239:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2169535989503157 : ℚ) / 1000000000000) ≤ ((1080911102444709 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (2239:ℚ) := by decide +kernel
  have hratR : ((((2169535989503157 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1080911102444709 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2239:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_333 : ((((2177251559034817 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2243 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2239 < q → q < 2243 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2243).mp (by decide +kernel))) hgap
  have hprev := thV_332
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2243:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2177251559034817 : ℚ) / 1000000000000) ≤ ((2169535989503157 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (2243:ℚ) := by decide +kernel
  have hratR : ((((2177251559034817 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2169535989503157 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2243:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_334 : ((((68280334027277 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2251 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2243 < q → q < 2251 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2251).mp (by decide +kernel))) hgap
  have hprev := thV_333
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2251:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((68280334027277 : ℚ) / 31250000000) ≤ ((2177251559034817 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (2251:ℚ) := by decide +kernel
  have hratR : ((((68280334027277 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((2177251559034817 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2251:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_335 : ((((17130444543129 : ℚ) / 7812500000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2267 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2251 < q → q < 2267 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2267).mp (by decide +kernel))) hgap
  have hprev := thV_334
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2267:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((17130444543129 : ℚ) / 7812500000) ≤ ((68280334027277 : ℚ) / 31250000000) + Work.RHContract.RegionI.logLowQ (2267:ℚ) := by decide +kernel
  have hratR : ((((17130444543129 : ℚ) / 7812500000) : ℚ) : ℝ) ≤ ((((68280334027277 : ℚ) / 31250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2267:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_336 : ((((17190812468769 : ℚ) / 7812500000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2269 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2267 < q → q < 2269 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2269).mp (by decide +kernel))) hgap
  have hprev := thV_335
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2269:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((17190812468769 : ℚ) / 7812500000) ≤ ((17130444543129 : ℚ) / 7812500000) + Work.RHContract.RegionI.logLowQ (2269:ℚ) := by decide +kernel
  have hratR : ((((17190812468769 : ℚ) / 7812500000) : ℚ) : ℝ) ≤ ((((17130444543129 : ℚ) / 7812500000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2269:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_337 : ((((88326114072937 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2273 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2269 < q → q < 2273 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2273).mp (by decide +kernel))) hgap
  have hprev := thV_336
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2273:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((88326114072937 : ℚ) / 40000000000) ≤ ((17190812468769 : ℚ) / 7812500000) + Work.RHContract.RegionI.logLowQ (2273:ℚ) := by decide +kernel
  have hratR : ((((88326114072937 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((17190812468769 : ℚ) / 7812500000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2273:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_338 : ((((2215885221042849 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2281 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2273 < q → q < 2281 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2281).mp (by decide +kernel))) hgap
  have hprev := thV_337
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2281:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2215885221042849 : ℚ) / 1000000000000) ≤ ((88326114072937 : ℚ) / 40000000000) + Work.RHContract.RegionI.logLowQ (2281:ℚ) := by decide +kernel
  have hratR : ((((2215885221042849 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((88326114072937 : ℚ) / 40000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2281:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_339 : ((((555905054308503 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2287 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2281 < q → q < 2287 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2287).mp (by decide +kernel))) hgap
  have hprev := thV_338
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2287:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((555905054308503 : ℚ) / 250000000000) ≤ ((2215885221042849 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (2287:ℚ) := by decide +kernel
  have hratR : ((((555905054308503 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((2215885221042849 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2287:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_340 : ((((223135783351401 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2293 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2287 < q → q < 2293 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2293).mp (by decide +kernel))) hgap
  have hprev := thV_339
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2293:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((223135783351401 : ℚ) / 100000000000) ≤ ((555905054308503 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (2293:ℚ) := by decide +kernel
  have hratR : ((((223135783351401 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((555905054308503 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2293:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_341 : ((((2239097192713839 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2297 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2293 < q → q < 2297 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2297).mp (by decide +kernel))) hgap
  have hprev := thV_340
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2297:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2239097192713839 : ℚ) / 1000000000000) ≤ ((223135783351401 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (2297:ℚ) := by decide +kernel
  have hratR : ((((2239097192713839 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((223135783351401 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2297:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_342 : ((((1123420881260167 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2309 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2297 < q → q < 2309 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2309).mp (by decide +kernel))) hgap
  have hprev := thV_341
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2309:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1123420881260167 : ℚ) / 500000000000) ≤ ((2239097192713839 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (2309:ℚ) := by decide +kernel
  have hratR : ((((1123420881260167 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((2239097192713839 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2309:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_343 : ((((563646799531937 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2311 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2309 < q → q < 2311 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2311).mp (by decide +kernel))) hgap
  have hprev := thV_342
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2311:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((563646799531937 : ℚ) / 250000000000) ≤ ((1123420881260167 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (2311:ℚ) := by decide +kernel
  have hratR : ((((563646799531937 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((1123420881260167 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2311:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_344 : ((((226234210839691 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2333 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2311 < q → q < 2333 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2333).mp (by decide +kernel))) hgap
  have hprev := thV_343
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2333:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((226234210839691 : ℚ) / 100000000000) ≤ ((563646799531937 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (2333:ℚ) := by decide +kernel
  have hratR : ((((226234210839691 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((563646799531937 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2333:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_345 : ((((1135049793580317 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2339 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2333 < q → q < 2339 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2339).mp (by decide +kernel))) hgap
  have hprev := thV_344
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2339:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1135049793580317 : ℚ) / 500000000000) ≤ ((226234210839691 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (2339:ℚ) := by decide +kernel
  have hratR : ((((1135049793580317 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226234210839691 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2339:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_346 : ((((455571584125053 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2341 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2339 < q → q < 2341 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2341).mp (by decide +kernel))) hgap
  have hprev := thV_345
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2341:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((455571584125053 : ℚ) / 200000000000) ≤ ((1135049793580317 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (2341:ℚ) := by decide +kernel
  have hratR : ((((455571584125053 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((1135049793580317 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2341:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_347 : ((((142851175863641 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2347 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2341 < q → q < 2347 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2347).mp (by decide +kernel))) hgap
  have hprev := thV_346
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2347:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((142851175863641 : ℚ) / 62500000000) ≤ ((455571584125053 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (2347:ℚ) := by decide +kernel
  have hratR : ((((142851175863641 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((455571584125053 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2347:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_348 : ((((8958521132281 : ℚ) / 3906250000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2351 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2347 < q → q < 2351 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2351).mp (by decide +kernel))) hgap
  have hprev := thV_347
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2351:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8958521132281 : ℚ) / 3906250000) ≤ ((142851175863641 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (2351:ℚ) := by decide +kernel
  have hratR : ((((8958521132281 : ℚ) / 3906250000) : ℚ) : ℝ) ≤ ((((142851175863641 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2351:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_349 : ((((575286638691003 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2357 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2351 < q → q < 2357 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2357).mp (by decide +kernel))) hgap
  have hprev := thV_348
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2357:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((575286638691003 : ℚ) / 250000000000) ≤ ((8958521132281 : ℚ) / 3906250000) + Work.RHContract.RegionI.logLowQ (2357:ℚ) := by decide +kernel
  have hratR : ((((575286638691003 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((8958521132281 : ℚ) / 3906250000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2357:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_350 : ((((1154458810923609 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2371 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2357 < q → q < 2371 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2371).mp (by decide +kernel))) hgap
  have hprev := thV_349
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2371:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1154458810923609 : ℚ) / 500000000000) ≤ ((575286638691003 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (2371:ℚ) := by decide +kernel
  have hratR : ((((1154458810923609 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((575286638691003 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2371:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_351 : ((((1158345608155859 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2377 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2371 < q → q < 2377 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2377).mp (by decide +kernel))) hgap
  have hprev := thV_350
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2377:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1158345608155859 : ℚ) / 500000000000) ≤ ((1154458810923609 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (2377:ℚ) := by decide +kernel
  have hratR : ((((1158345608155859 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1154458810923609 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2377:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_352 : ((((464893298431069 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2381 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2377 < q → q < 2381 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2381).mp (by decide +kernel))) hgap
  have hprev := thV_351
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2381:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((464893298431069 : ℚ) / 200000000000) ≤ ((1158345608155859 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (2381:ℚ) := by decide +kernel
  have hratR : ((((464893298431069 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((1158345608155859 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2381:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_353 : ((((145765162976849 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2383 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2381 < q → q < 2383 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2383).mp (by decide +kernel))) hgap
  have hprev := thV_352
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2383:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((145765162976849 : ℚ) / 62500000000) ≤ ((464893298431069 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (2383:ℚ) := by decide +kernel
  have hratR : ((((145765162976849 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((464893298431069 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2383:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_354 : ((((46800424755481 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2389 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2383 < q → q < 2389 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2389).mp (by decide +kernel))) hgap
  have hprev := thV_353
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2389:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((46800424755481 : ℚ) / 20000000000) ≤ ((145765162976849 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (2389:ℚ) := by decide +kernel
  have hratR : ((((46800424755481 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ ((((145765162976849 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2389:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_355 : ((((1173900770429549 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2393 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2389 < q → q < 2393 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2393).mp (by decide +kernel))) hgap
  have hprev := thV_354
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2393:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1173900770429549 : ℚ) / 500000000000) ≤ ((46800424755481 : ℚ) / 20000000000) + Work.RHContract.RegionI.logLowQ (2393:ℚ) := by decide +kernel
  have hratR : ((((1173900770429549 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((46800424755481 : ℚ) / 20000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2393:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_356 : ((((1177792174059539 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2399 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2393 < q → q < 2399 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2399).mp (by decide +kernel))) hgap
  have hprev := thV_355
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2399:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1177792174059539 : ℚ) / 500000000000) ≤ ((1173900770429549 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (2399:ℚ) := by decide +kernel
  have hratR : ((((1177792174059539 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1173900770429549 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2399:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_357 : ((((2363372144994399 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2411 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2399 < q → q < 2411 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2411).mp (by decide +kernel))) hgap
  have hprev := thV_356
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2411:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2363372144994399 : ℚ) / 1000000000000) ≤ ((1177792174059539 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (2411:ℚ) := by decide +kernel
  have hratR : ((((2363372144994399 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1177792174059539 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2411:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_358 : ((((2371162427372243 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2417 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2411 < q → q < 2417 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2417).mp (by decide +kernel))) hgap
  have hprev := thV_357
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2417:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2371162427372243 : ℚ) / 1000000000000) ≤ ((2363372144994399 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (2417:ℚ) := by decide +kernel
  have hratR : ((((2371162427372243 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2363372144994399 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2417:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_359 : ((((11894775945451 : ℚ) / 5000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2423 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2417 < q → q < 2423 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2423).mp (by decide +kernel))) hgap
  have hprev := thV_358
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2423:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11894775945451 : ℚ) / 5000000000) ≤ ((2371162427372243 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (2423:ℚ) := by decide +kernel
  have hratR : ((((11894775945451 : ℚ) / 5000000000) : ℚ) : ℝ) ≤ ((((2371162427372243 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2423:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_360 : ((((477350742428193 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2437 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2423 < q → q < 2437 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2437).mp (by decide +kernel))) hgap
  have hprev := thV_359
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2437:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((477350742428193 : ℚ) / 200000000000) ≤ ((11894775945451 : ℚ) / 5000000000) + Work.RHContract.RegionI.logLowQ (2437:ℚ) := by decide +kernel
  have hratR : ((((477350742428193 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((11894775945451 : ℚ) / 5000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2437:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_361 : ((((1197276937604249 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2441 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2437 < q → q < 2441 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2441).mp (by decide +kernel))) hgap
  have hprev := thV_360
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2441:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1197276937604249 : ℚ) / 500000000000) ≤ ((477350742428193 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (2441:ℚ) := by decide +kernel
  have hratR : ((((1197276937604249 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((477350742428193 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2441:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_362 : ((((2402356493269081 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2447 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2441 < q → q < 2447 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2447).mp (by decide +kernel))) hgap
  have hprev := thV_361
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2447:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2402356493269081 : ℚ) / 1000000000000) ≤ ((1197276937604249 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (2447:ℚ) := by decide +kernel
  have hratR : ((((2402356493269081 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1197276937604249 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2447:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_363 : ((((2410164003308437 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2459 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2447 < q → q < 2459 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2459).mp (by decide +kernel))) hgap
  have hprev := thV_362
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2459:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2410164003308437 : ℚ) / 1000000000000) ≤ ((2402356493269081 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (2459:ℚ) := by decide +kernel
  have hratR : ((((2410164003308437 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2402356493269081 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2459:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_364 : ((((1208987380711053 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2467 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2459 < q → q < 2467 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2467).mp (by decide +kernel))) hgap
  have hprev := thV_363
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2467:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1208987380711053 : ℚ) / 500000000000) ≤ ((2410164003308437 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (2467:ℚ) := by decide +kernel
  have hratR : ((((1208987380711053 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((2410164003308437 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2467:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_365 : ((((151611746792923 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2473 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2467 < q → q < 2473 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2473).mp (by decide +kernel))) hgap
  have hprev := thV_364
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2473:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((151611746792923 : ℚ) / 62500000000) ≤ ((1208987380711053 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (2473:ℚ) := by decide +kernel
  have hratR : ((((151611746792923 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((1208987380711053 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2473:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_366 : ((((2433602752113397 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2477 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2473 < q → q < 2477 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2477).mp (by decide +kernel))) hgap
  have hprev := thV_365
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2477:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2433602752113397 : ℚ) / 1000000000000) ≤ ((151611746792923 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (2477:ℚ) := by decide +kernel
  have hratR : ((((2433602752113397 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((151611746792923 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2477:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_367 : ((((2441427997401969 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2503 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2477 < q → q < 2503 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2503).mp (by decide +kernel))) hgap
  have hprev := thV_366
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2503:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2441427997401969 : ℚ) / 1000000000000) ≤ ((2433602752113397 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (2503:ℚ) := by decide +kernel
  have hratR : ((((2441427997401969 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2433602752113397 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2503:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_368 : ((((2449260408326297 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2521 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2503 < q → q < 2521 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2521).mp (by decide +kernel))) hgap
  have hprev := thV_367
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2521:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2449260408326297 : ℚ) / 1000000000000) ≤ ((2441427997401969 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (2521:ℚ) := by decide +kernel
  have hratR : ((((2449260408326297 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2441427997401969 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2521:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_369 : ((((1228548389041991 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2531 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2521 < q → q < 2531 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2531).mp (by decide +kernel))) hgap
  have hprev := thV_368
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2531:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1228548389041991 : ℚ) / 500000000000) ≤ ((2449260408326297 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (2531:ℚ) := by decide +kernel
  have hratR : ((((1228548389041991 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((2449260408326297 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2531:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_370 : ((((2464936303662827 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2539 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2531 < q → q < 2539 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2539).mp (by decide +kernel))) hgap
  have hprev := thV_369
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2539:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2464936303662827 : ℚ) / 1000000000000) ≤ ((1228548389041991 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (2539:ℚ) := by decide +kernel
  have hratR : ((((2464936303662827 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1228548389041991 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2539:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_371 : ((((2472777403425389 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2543 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2539 < q → q < 2543 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2543).mp (by decide +kernel))) hgap
  have hprev := thV_370
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2543:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2472777403425389 : ℚ) / 1000000000000) ≤ ((2464936303662827 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (2543:ℚ) := by decide +kernel
  have hratR : ((((2472777403425389 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2464936303662827 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2543:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_372 : ((((496124171965381 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2549 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2543 < q → q < 2549 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2549).mp (by decide +kernel))) hgap
  have hprev := thV_371
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2549:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((496124171965381 : ℚ) / 200000000000) ≤ ((2472777403425389 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (2549:ℚ) := by decide +kernel
  have hratR : ((((496124171965381 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((2472777403425389 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2549:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_373 : ((((2488465100542187 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2551 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2549 < q → q < 2551 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2551).mp (by decide +kernel))) hgap
  have hprev := thV_372
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2551:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2488465100542187 : ℚ) / 1000000000000) ≤ ((496124171965381 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (2551:ℚ) := by decide +kernel
  have hratR : ((((2488465100542187 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((496124171965381 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2551:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_374 : ((((1248155845257309 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2557 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2551 < q → q < 2557 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2557).mp (by decide +kernel))) hgap
  have hprev := thV_373
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2557:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1248155845257309 : ℚ) / 500000000000) ≤ ((2488465100542187 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (2557:ℚ) := by decide +kernel
  have hratR : ((((1248155845257309 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((2488465100542187 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2557:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_375 : ((((2504166847517639 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2579 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2557 < q → q < 2579 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2579).mp (by decide +kernel))) hgap
  have hprev := thV_374
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2579:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2504166847517639 : ℚ) / 1000000000000) ≤ ((1248155845257309 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (2579:ℚ) := by decide +kernel
  have hratR : ((((2504166847517639 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1248155845257309 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2579:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_376 : ((((2512026646695341 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2591 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2579 < q → q < 2591 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2591).mp (by decide +kernel))) hgap
  have hprev := thV_375
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2591:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2512026646695341 : ℚ) / 1000000000000) ≤ ((2504166847517639 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (2591:ℚ) := by decide +kernel
  have hratR : ((((2512026646695341 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2504166847517639 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2591:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_377 : ((((125994360873901 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2593 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2591 < q → q < 2593 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2593).mp (by decide +kernel))) hgap
  have hprev := thV_376
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2593:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((125994360873901 : ℚ) / 50000000000) ≤ ((2512026646695341 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (2593:ℚ) := by decide +kernel
  have hratR : ((((125994360873901 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((2512026646695341 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2593:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_378 : ((((2527753939760297 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2609 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2593 < q → q < 2609 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2609).mp (by decide +kernel))) hgap
  have hprev := thV_377
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2609:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2527753939760297 : ℚ) / 1000000000000) ≤ ((125994360873901 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (2609:ℚ) := by decide +kernel
  have hratR : ((((2527753939760297 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((125994360873901 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2609:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_379 : ((((2535623723659967 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2617 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2609 < q → q < 2617 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2617).mp (by decide +kernel))) hgap
  have hprev := thV_378
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2617:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2535623723659967 : ℚ) / 1000000000000) ≤ ((2527753939760297 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (2617:ℚ) := by decide +kernel
  have hratR : ((((2535623723659967 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2527753939760297 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2617:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_380 : ((((2543495034860431 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2621 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2617 < q → q < 2621 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2621).mp (by decide +kernel))) hgap
  have hprev := thV_379
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2621:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2543495034860431 : ℚ) / 1000000000000) ≤ ((2535623723659967 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (2621:ℚ) := by decide +kernel
  have hratR : ((((2543495034860431 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2535623723659967 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2621:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_381 : ((((2551370914017067 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2633 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2621 < q → q < 2633 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2633).mp (by decide +kernel))) hgap
  have hprev := thV_380
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2633:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2551370914017067 : ℚ) / 1000000000000) ≤ ((2543495034860431 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (2633:ℚ) := by decide +kernel
  have hratR : ((((2551370914017067 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2543495034860431 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2633:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_382 : ((((1279626048108217 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2647 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2633 < q → q < 2647 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2647).mp (by decide +kernel))) hgap
  have hprev := thV_381
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2647:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1279626048108217 : ℚ) / 500000000000) ≤ ((2551370914017067 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (2647:ℚ) := by decide +kernel
  have hratR : ((((1279626048108217 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((2551370914017067 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2647:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_383 : ((((1283568524579667 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2657 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2647 < q → q < 2657 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2657).mp (by decide +kernel))) hgap
  have hprev := thV_382
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2657:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1283568524579667 : ℚ) / 500000000000) ≤ ((1279626048108217 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (2657:ℚ) := by decide +kernel
  have hratR : ((((1283568524579667 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1279626048108217 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2657:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_384 : ((((2575022754547717 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2659 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2657 < q → q < 2659 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2659).mp (by decide +kernel))) hgap
  have hprev := thV_383
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2659:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2575022754547717 : ℚ) / 1000000000000) ≤ ((1283568524579667 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (2659:ℚ) := by decide +kernel
  have hratR : ((((2575022754547717 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1283568524579667 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2659:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_385 : ((((2582909963130671 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2663 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2659 < q → q < 2663 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2663).mp (by decide +kernel))) hgap
  have hprev := thV_384
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2663:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2582909963130671 : ℚ) / 1000000000000) ≤ ((2575022754547717 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (2663:ℚ) := by decide +kernel
  have hratR : ((((2582909963130671 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2575022754547717 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2663:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_386 : ((((2590800171340921 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2671 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2663 < q → q < 2671 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2671).mp (by decide +kernel))) hgap
  have hprev := thV_385
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2671:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2590800171340921 : ℚ) / 1000000000000) ≤ ((2582909963130671 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (2671:ℚ) := by decide +kernel
  have hratR : ((((2590800171340921 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2582909963130671 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2671:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_387 : ((((2598692623381581 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2677 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2671 < q → q < 2677 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2677).mp (by decide +kernel))) hgap
  have hprev := thV_386
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2677:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2598692623381581 : ℚ) / 1000000000000) ≤ ((2590800171340921 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (2677:ℚ) := by decide +kernel
  have hratR : ((((2598692623381581 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2590800171340921 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2677:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_388 : ((((2606587314229147 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2683 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2677 < q → q < 2683 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2683).mp (by decide +kernel))) hgap
  have hprev := thV_387
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2683:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2606587314229147 : ℚ) / 1000000000000) ≤ ((2598692623381581 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (2683:ℚ) := by decide +kernel
  have hratR : ((((2606587314229147 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2598692623381581 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2683:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_389 : ((((2614483494834903 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2687 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2683 < q → q < 2687 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2687).mp (by decide +kernel))) hgap
  have hprev := thV_388
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2687:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2614483494834903 : ℚ) / 1000000000000) ≤ ((2606587314229147 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (2687:ℚ) := by decide +kernel
  have hratR : ((((2614483494834903 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2606587314229147 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2687:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_390 : ((((327797552436039 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2689 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2687 < q → q < 2689 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2689).mp (by decide +kernel))) hgap
  have hprev := thV_389
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2689:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((327797552436039 : ℚ) / 125000000000) ≤ ((2614483494834903 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (2689:ℚ) := by decide +kernel
  have hratR : ((((327797552436039 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((2614483494834903 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2689:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_391 : ((((328784853822283 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2693 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2689 < q → q < 2693 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2693).mp (by decide +kernel))) hgap
  have hprev := thV_390
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2693:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((328784853822283 : ℚ) / 125000000000) ≤ ((327797552436039 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (2693:ℚ) := by decide +kernel
  have hratR : ((((328784853822283 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((327797552436039 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2693:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_392 : ((((1319089733594211 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2699 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2693 < q → q < 2699 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2699).mp (by decide +kernel))) hgap
  have hprev := thV_391
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2699:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1319089733594211 : ℚ) / 500000000000) ≤ ((328784853822283 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (2699:ℚ) := by decide +kernel
  have hratR : ((((1319089733594211 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((328784853822283 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2699:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_393 : ((((330760382934397 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2707 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2699 < q → q < 2707 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2707).mp (by decide +kernel))) hgap
  have hprev := thV_392
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2707:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((330760382934397 : ℚ) / 125000000000) ≤ ((1319089733594211 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (2707:ℚ) := by decide +kernel
  have hratR : ((((330760382934397 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((1319089733594211 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2707:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_394 : ((((530797627264363 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2711 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2707 < q → q < 2711 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2711).mp (by decide +kernel))) hgap
  have hprev := thV_393
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2711:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((530797627264363 : ℚ) / 200000000000) ≤ ((330760382934397 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (2711:ℚ) := by decide +kernel
  have hratR : ((((530797627264363 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((330760382934397 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2711:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_395 : ((((1330946973315807 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2713 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2711 < q → q < 2713 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2713).mp (by decide +kernel))) hgap
  have hprev := thV_394
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2713:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1330946973315807 : ℚ) / 500000000000) ≤ ((530797627264363 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (2713:ℚ) := by decide +kernel
  have hratR : ((((1330946973315807 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((530797627264363 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2713:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_396 : ((((2669801966073387 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2719 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2713 < q → q < 2719 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2719).mp (by decide +kernel))) hgap
  have hprev := thV_395
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2719:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2669801966073387 : ℚ) / 1000000000000) ≤ ((1330946973315807 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (2719:ℚ) := by decide +kernel
  have hratR : ((((2669801966073387 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1330946973315807 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2719:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_397 : ((((535542731318247 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2729 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2719 < q → q < 2729 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2729).mp (by decide +kernel))) hgap
  have hprev := thV_396
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2729:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((535542731318247 : ℚ) / 200000000000) ≤ ((2669801966073387 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (2729:ℚ) := by decide +kernel
  have hratR : ((((535542731318247 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((2669801966073387 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2729:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_398 : ((((2685626079709849 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2731 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2729 < q → q < 2731 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2731).mp (by decide +kernel))) hgap
  have hprev := thV_397
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2731:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2685626079709849 : ℚ) / 1000000000000) ≤ ((535542731318247 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (2731:ℚ) := by decide +kernel
  have hratR : ((((2685626079709849 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((535542731318247 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2731:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_399 : ((((673385539450823 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2741 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2731 < q → q < 2741 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2741).mp (by decide +kernel))) hgap
  have hprev := thV_398
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2741:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((673385539450823 : ℚ) / 250000000000) ≤ ((2685626079709849 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (2741:ℚ) := by decide +kernel
  have hratR : ((((673385539450823 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((2685626079709849 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2741:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_400 : ((((2701461150288597 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2749 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2741 < q → q < 2749 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2749).mp (by decide +kernel))) hgap
  have hprev := thV_399
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2749:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2701461150288597 : ℚ) / 1000000000000) ≤ ((673385539450823 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (2749:ℚ) := by decide +kernel
  have hratR : ((((2701461150288597 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((673385539450823 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2749:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_401 : ((((16933634979943 : ℚ) / 6250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2753 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2749 < q → q < 2753 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2753).mp (by decide +kernel))) hgap
  have hprev := thV_400
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2753:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((16933634979943 : ℚ) / 6250000000) ≤ ((2701461150288597 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (2753:ℚ) := by decide +kernel
  have hratR : ((((16933634979943 : ℚ) / 6250000000) : ℚ) : ℝ) ≤ ((((2701461150288597 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2753:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_402 : ((((2717307115767807 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2767 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2753 < q → q < 2767 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2767).mp (by decide +kernel))) hgap
  have hprev := thV_401
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2767:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2717307115767807 : ℚ) / 1000000000000) ≤ ((16933634979943 : ℚ) / 6250000000) + Work.RHContract.RegionI.logLowQ (2767:ℚ) := by decide +kernel
  have hratR : ((((2717307115767807 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((16933634979943 : ℚ) / 6250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2767:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_403 : ((((1362618121126127 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2777 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2767 < q → q < 2777 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2777).mp (by decide +kernel))) hgap
  have hprev := thV_402
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2777:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1362618121126127 : ℚ) / 500000000000) ≤ ((2717307115767807 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (2777:ℚ) := by decide +kernel
  have hratR : ((((1362618121126127 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((2717307115767807 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2777:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_404 : ((((1366584840318511 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2789 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2777 < q → q < 2789 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2789).mp (by decide +kernel))) hgap
  have hprev := thV_403
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2789:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1366584840318511 : ℚ) / 500000000000) ≤ ((1362618121126127 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (2789:ℚ) := by decide +kernel
  have hratR : ((((1366584840318511 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1362618121126127 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2789:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_405 : ((((1370551917933849 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2791 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2789 < q → q < 2791 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2791).mp (by decide +kernel))) hgap
  have hprev := thV_404
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2791:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1370551917933849 : ℚ) / 500000000000) ≤ ((1366584840318511 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (2791:ℚ) := by decide +kernel
  have hratR : ((((1370551917933849 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1366584840318511 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2791:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_406 : ((((68726003463951 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2797 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2791 < q → q < 2797 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2797).mp (by decide +kernel))) hgap
  have hprev := thV_405
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2797:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((68726003463951 : ℚ) / 25000000000) ≤ ((1370551917933849 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (2797:ℚ) := by decide +kernel
  have hratR : ((((68726003463951 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((1370551917933849 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2797:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_407 : ((((68924446758261 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2801 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2797 < q → q < 2801 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2801).mp (by decide +kernel))) hgap
  have hprev := thV_406
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2801:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((68924446758261 : ℚ) / 25000000000) ≤ ((68726003463951 : ℚ) / 25000000000) + Work.RHContract.RegionI.logLowQ (2801:ℚ) := by decide +kernel
  have hratR : ((((68924446758261 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((68726003463951 : ℚ) / 25000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2801:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_408 : ((((552983263175749 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2803 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2801 < q → q < 2803 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2803).mp (by decide +kernel))) hgap
  have hprev := thV_407
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2803:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((552983263175749 : ℚ) / 200000000000) ≤ ((68924446758261 : ℚ) / 25000000000) + Work.RHContract.RegionI.logLowQ (2803:ℚ) := by decide +kernel
  have hratR : ((((552983263175749 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((68924446758261 : ℚ) / 25000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2803:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_409 : ((((2772860453366999 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2819 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2803 < q → q < 2819 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2819).mp (by decide +kernel))) hgap
  have hprev := thV_408
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2819:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2772860453366999 : ℚ) / 1000000000000) ≤ ((552983263175749 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (2819:ℚ) := by decide +kernel
  have hratR : ((((2772860453366999 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((552983263175749 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2819:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_410 : ((((278080954486397 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2833 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2819 < q → q < 2833 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2833).mp (by decide +kernel))) hgap
  have hprev := thV_409
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2833:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((278080954486397 : ℚ) / 100000000000) ≤ ((2772860453366999 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (2833:ℚ) := by decide +kernel
  have hratR : ((((278080954486397 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((2772860453366999 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2833:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_411 : ((((2788760047295919 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2837 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2833 < q → q < 2837 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2837).mp (by decide +kernel))) hgap
  have hprev := thV_410
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2837:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2788760047295919 : ℚ) / 1000000000000) ≤ ((278080954486397 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (2837:ℚ) := by decide +kernel
  have hratR : ((((2788760047295919 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((278080954486397 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2837:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_412 : ((((279671266240471 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2843 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2837 < q → q < 2843 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2843).mp (by decide +kernel))) hgap
  have hprev := thV_411
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2843:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((279671266240471 : ℚ) / 100000000000) ≤ ((2788760047295919 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (2843:ℚ) := by decide +kernel
  have hratR : ((((279671266240471 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((2788760047295919 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2843:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_413 : ((((2804668087490763 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2851 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2843 < q → q < 2851 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2851).mp (by decide +kernel))) hgap
  have hprev := thV_412
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2851:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2804668087490763 : ℚ) / 1000000000000) ≤ ((279671266240471 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (2851:ℚ) := by decide +kernel
  have hratR : ((((2804668087490763 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((279671266240471 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2851:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_414 : ((((1406312807445067 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2857 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2851 < q → q < 2857 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2857).mp (by decide +kernel))) hgap
  have hprev := thV_413
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2857:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1406312807445067 : ℚ) / 500000000000) ≤ ((2804668087490763 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (2857:ℚ) := by decide +kernel
  have hratR : ((((1406312807445067 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((2804668087490763 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2857:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_415 : ((((705146135345081 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2861 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2857 < q → q < 2861 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2861).mp (by decide +kernel))) hgap
  have hprev := thV_414
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2861:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((705146135345081 : ℚ) / 250000000000) ≤ ((1406312807445067 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (2861:ℚ) := by decide +kernel
  have hratR : ((((705146135345081 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((1406312807445067 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2861:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_416 : ((((707137434917019 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2879 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2861 < q → q < 2879 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2879).mp (by decide +kernel))) hgap
  have hprev := thV_415
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2879:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((707137434917019 : ℚ) / 250000000000) ≤ ((705146135345081 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (2879:ℚ) := by decide +kernel
  have hratR : ((((707137434917019 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((705146135345081 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2879:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_417 : ((((2836517712844879 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2887 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2879 < q → q < 2887 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2887).mp (by decide +kernel))) hgap
  have hprev := thV_416
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2887:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2836517712844879 : ℚ) / 1000000000000) ≤ ((707137434917019 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (2887:ℚ) := by decide +kernel
  have hratR : ((((2836517712844879 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((707137434917019 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2887:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_418 : ((((711122285959947 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2897 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2887 < q → q < 2897 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2897).mp (by decide +kernel))) hgap
  have hprev := thV_417
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2897:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((711122285959947 : ℚ) / 250000000000) ≤ ((2836517712844879 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (2897:ℚ) := by decide +kernel
  have hratR : ((((711122285959947 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((2836517712844879 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2897:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_419 : ((((2852462643800953 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2903 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2897 < q → q < 2903 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2903).mp (by decide +kernel))) hgap
  have hprev := thV_418
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2903:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2852462643800953 : ℚ) / 1000000000000) ≤ ((711122285959947 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (2903:ℚ) := by decide +kernel
  have hratR : ((((2852462643800953 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((711122285959947 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2903:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_420 : ((((715109552114147 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2909 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2903 < q → q < 2909 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2909).mp (by decide +kernel))) hgap
  have hprev := thV_419
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2909:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((715109552114147 : ℚ) / 250000000000) ≤ ((2852462643800953 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (2909:ℚ) := by decide +kernel
  have hratR : ((((715109552114147 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((2852462643800953 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2909:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_421 : ((((717104129855899 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2917 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2909 < q → q < 2917 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2917).mp (by decide +kernel))) hgap
  have hprev := thV_420
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2917:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((717104129855899 : ℚ) / 250000000000) ≤ ((715109552114147 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (2917:ℚ) := by decide +kernel
  have hratR : ((((717104129855899 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((715109552114147 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2917:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_422 : ((((719099563176857 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2927 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2917 < q → q < 2927 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2927).mp (by decide +kernel))) hgap
  have hprev := thV_421
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2927:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((719099563176857 : ℚ) / 250000000000) ≤ ((717104129855899 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (2927:ℚ) := by decide +kernel
  have hratR : ((((719099563176857 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((717104129855899 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2927:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_423 : ((((2884384077370987 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2939 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2927 < q → q < 2939 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2939).mp (by decide +kernel))) hgap
  have hprev := thV_422
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2939:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2884384077370987 : ℚ) / 1000000000000) ≤ ((719099563176857 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (2939:ℚ) := by decide +kernel
  have hratR : ((((2884384077370987 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((719099563176857 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2939:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_424 : ((((2892374654249871 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2953 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2939 < q → q < 2953 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2953).mp (by decide +kernel))) hgap
  have hprev := thV_423
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2953:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2892374654249871 : ℚ) / 1000000000000) ≤ ((2884384077370987 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (2953:ℚ) := by decide +kernel
  have hratR : ((((2892374654249871 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2884384077370987 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2953:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_425 : ((((181272911547929 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2957 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2953 < q → q < 2957 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2957).mp (by decide +kernel))) hgap
  have hprev := thV_424
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2957:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((181272911547929 : ℚ) / 62500000000) ≤ ((2892374654249871 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (2957:ℚ) := by decide +kernel
  have hratR : ((((181272911547929 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((2892374654249871 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2957:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_426 : ((((1454180271155789 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2963 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2957 < q → q < 2963 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2963).mp (by decide +kernel))) hgap
  have hprev := thV_425
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2963:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1454180271155789 : ℚ) / 500000000000) ≤ ((181272911547929 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (2963:ℚ) := by decide +kernel
  have hratR : ((((1454180271155789 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((181272911547929 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2963:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_427 : ((((1458178261391741 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2969 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2963 < q → q < 2969 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2969).mp (by decide +kernel))) hgap
  have hprev := thV_426
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2969:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1458178261391741 : ℚ) / 500000000000) ≤ ((1454180271155789 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (2969:ℚ) := by decide +kernel
  have hratR : ((((1458178261391741 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1454180271155789 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2969:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_428 : ((((584870635331217 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2971 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2969 < q → q < 2971 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2971).mp (by decide +kernel))) hgap
  have hprev := thV_427
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2971:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((584870635331217 : ℚ) / 200000000000) ≤ ((1458178261391741 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (2971:ℚ) := by decide +kernel
  have hratR : ((((584870635331217 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((1458178261391741 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2971:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_429 : ((((1466179605415987 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((2999 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2971 < q → q < 2999 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2999).mp (by decide +kernel))) hgap
  have hprev := thV_428
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (2999:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1466179605415987 : ℚ) / 500000000000) ≤ ((584870635331217 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (2999:ℚ) := by decide +kernel
  have hratR : ((((1466179605415987 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((584870635331217 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (2999:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_430 : ((((1470182955837277 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3001 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2999 < q → q < 3001 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3001).mp (by decide +kernel))) hgap
  have hprev := thV_429
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3001:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1470182955837277 : ℚ) / 500000000000) ≤ ((1466179605415987 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (3001:ℚ) := by decide +kernel
  have hratR : ((((1470182955837277 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1466179605415987 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3001:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_431 : ((((184273496200011 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3011 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3001 < q → q < 3011 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3011).mp (by decide +kernel))) hgap
  have hprev := thV_430
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3011:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((184273496200011 : ℚ) / 62500000000) ≤ ((1470182955837277 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (3011:ℚ) := by decide +kernel
  have hratR : ((((184273496200011 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((1470182955837277 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3011:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_432 : ((((2956388620127023 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3019 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3011 < q → q < 3019 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3019).mp (by decide +kernel))) hgap
  have hprev := thV_431
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3019:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2956388620127023 : ℚ) / 1000000000000) ≤ ((184273496200011 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (3019:ℚ) := by decide +kernel
  have hratR : ((((2956388620127023 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((184273496200011 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3019:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_433 : ((((2964402625118943 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3023 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3019 < q → q < 3023 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3023).mp (by decide +kernel))) hgap
  have hprev := thV_432
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3023:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2964402625118943 : ℚ) / 1000000000000) ≤ ((2956388620127023 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (3023:ℚ) := by decide +kernel
  have hratR : ((((2964402625118943 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2956388620127023 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3023:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_434 : ((((2972421250581129 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3037 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3023 < q → q < 3037 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3037).mp (by decide +kernel))) hgap
  have hprev := thV_433
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3037:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2972421250581129 : ℚ) / 1000000000000) ≤ ((2964402625118943 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (3037:ℚ) := by decide +kernel
  have hratR : ((((2972421250581129 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2964402625118943 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3037:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_435 : ((((1490220596132973 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3041 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3037 < q → q < 3041 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3041).mp (by decide +kernel))) hgap
  have hprev := thV_434
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3041:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1490220596132973 : ℚ) / 500000000000) ≤ ((2972421250581129 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (3041:ℚ) := by decide +kernel
  have hratR : ((((1490220596132973 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((2972421250581129 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3041:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_436 : ((((1494231880605037 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3049 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3041 < q → q < 3049 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3049).mp (by decide +kernel))) hgap
  have hprev := thV_435
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3049:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1494231880605037 : ℚ) / 500000000000) ≤ ((1490220596132973 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (3049:ℚ) := by decide +kernel
  have hratR : ((((1494231880605037 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1490220596132973 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3049:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_437 : ((((37456128226827 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3061 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3049 < q → q < 3061 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3061).mp (by decide +kernel))) hgap
  have hprev := thV_436
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3061:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((37456128226827 : ℚ) / 12500000000) ≤ ((1494231880605037 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (3061:ℚ) := by decide +kernel
  have hratR : ((((37456128226827 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ ((((1494231880605037 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3061:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_438 : ((((1502259356653707 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3067 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3061 < q → q < 3067 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3067).mp (by decide +kernel))) hgap
  have hprev := thV_437
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3067:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1502259356653707 : ℚ) / 500000000000) ≤ ((37456128226827 : ℚ) / 12500000000) + Work.RHContract.RegionI.logLowQ (3067:ℚ) := by decide +kernel
  have hratR : ((((1502259356653707 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((37456128226827 : ℚ) / 12500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3067:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_439 : ((((3012551073452479 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3079 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3067 < q → q < 3079 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3079).mp (by decide +kernel))) hgap
  have hprev := thV_438
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3079:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3012551073452479 : ℚ) / 1000000000000) ≤ ((1502259356653707 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (3079:ℚ) := by decide +kernel
  have hratR : ((((3012551073452479 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1502259356653707 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3079:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_440 : ((((604116946375501 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3083 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3079 < q → q < 3083 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3083).mp (by decide +kernel))) hgap
  have hprev := thV_439
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3083:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((604116946375501 : ℚ) / 200000000000) ≤ ((3012551073452479 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (3083:ℚ) := by decide +kernel
  have hratR : ((((604116946375501 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((3012551073452479 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3083:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_441 : ((((757155083641891 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3089 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3083 < q → q < 3089 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3089).mp (by decide +kernel))) hgap
  have hprev := thV_440
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3089:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((757155083641891 : ℚ) / 250000000000) ≤ ((604116946375501 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (3089:ℚ) := by decide +kernel
  have hratR : ((((757155083641891 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((604116946375501 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3089:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_442 : ((((3036662390974763 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3109 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3089 < q → q < 3109 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3109).mp (by decide +kernel))) hgap
  have hprev := thV_441
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3109:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3036662390974763 : ℚ) / 1000000000000) ≤ ((757155083641891 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (3109:ℚ) := by decide +kernel
  have hratR : ((((3036662390974763 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((757155083641891 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3109:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_443 : ((((3044707658688511 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3119 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3109 < q → q < 3119 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3119).mp (by decide +kernel))) hgap
  have hprev := thV_442
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3119:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3044707658688511 : ℚ) / 1000000000000) ≤ ((3036662390974763 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (3119:ℚ) := by decide +kernel
  have hratR : ((((3044707658688511 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3036662390974763 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3119:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_444 : ((((1526376783713961 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3121 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3119 < q → q < 3121 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3121).mp (by decide +kernel))) hgap
  have hprev := thV_443
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3121:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1526376783713961 : ℚ) / 500000000000) ≤ ((3044707658688511 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (3121:ℚ) := by decide +kernel
  have hratR : ((((1526376783713961 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((3044707658688511 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3121:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_445 : ((((3060804589633253 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3137 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3121 < q → q < 3137 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3137).mp (by decide +kernel))) hgap
  have hprev := thV_444
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3137:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3060804589633253 : ℚ) / 1000000000000) ≤ ((1526376783713961 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (3137:ℚ) := by decide +kernel
  have hratR : ((((3060804589633253 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1526376783713961 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3137:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_446 : ((((3068863865853699 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3163 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3137 < q → q < 3163 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3163).mp (by decide +kernel))) hgap
  have hprev := thV_445
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3163:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3068863865853699 : ℚ) / 1000000000000) ≤ ((3060804589633253 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (3163:ℚ) := by decide +kernel
  have hratR : ((((3068863865853699 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3060804589633253 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3163:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_447 : ((((1538462202948689 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3167 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3163 < q → q < 3167 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3167).mp (by decide +kernel))) hgap
  have hprev := thV_446
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3167:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1538462202948689 : ℚ) / 500000000000) ≤ ((3068863865853699 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (3167:ℚ) := by decide +kernel
  have hratR : ((((1538462202948689 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((3068863865853699 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3167:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_448 : ((((3084985577254209 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3169 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3167 < q → q < 3169 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3169).mp (by decide +kernel))) hgap
  have hprev := thV_447
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3169:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3084985577254209 : ℚ) / 1000000000000) ≤ ((1538462202948689 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (3169:ℚ) := by decide +kernel
  have hratR : ((((3084985577254209 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1538462202948689 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3169:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_449 : ((((1546525264071549 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3181 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3169 < q → q < 3181 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3181).mp (by decide +kernel))) hgap
  have hprev := thV_448
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3181:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1546525264071549 : ℚ) / 500000000000) ≤ ((3084985577254209 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (3181:ℚ) := by decide +kernel
  have hratR : ((((1546525264071549 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((3084985577254209 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3181:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_450 : ((((620223472690931 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3187 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3181 < q → q < 3187 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3187).mp (by decide +kernel))) hgap
  have hprev := thV_449
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3187:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((620223472690931 : ℚ) / 200000000000) ≤ ((1546525264071549 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (3187:ℚ) := by decide +kernel
  have hratR : ((((620223472690931 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((1546525264071549 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3187:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_451 : ((((3109185453078073 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3191 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3187 < q → q < 3191 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3191).mp (by decide +kernel))) hgap
  have hprev := thV_450
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3191:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3109185453078073 : ℚ) / 1000000000000) ≤ ((620223472690931 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (3191:ℚ) := by decide +kernel
  have hratR : ((((3109185453078073 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((620223472690931 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3191:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_452 : ((((1558628648112411 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3203 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3191 < q → q < 3203 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3203).mp (by decide +kernel))) hgap
  have hprev := thV_451
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3203:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1558628648112411 : ℚ) / 500000000000) ≤ ((3109185453078073 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (3203:ℚ) := by decide +kernel
  have hratR : ((((1558628648112411 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((3109185453078073 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3203:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_453 : ((((97666594089471 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3209 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3203 < q → q < 3209 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3209).mp (by decide +kernel))) hgap
  have hprev := thV_452
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3209:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((97666594089471 : ℚ) / 31250000000) ≤ ((1558628648112411 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (3209:ℚ) := by decide +kernel
  have hratR : ((((97666594089471 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((1558628648112411 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3209:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_454 : ((((3133407215387451 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3217 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3209 < q → q < 3217 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3217).mp (by decide +kernel))) hgap
  have hprev := thV_453
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3217:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3133407215387451 : ℚ) / 1000000000000) ≤ ((97666594089471 : ℚ) / 31250000000) + Work.RHContract.RegionI.logLowQ (3217:ℚ) := by decide +kernel
  have hratR : ((((3133407215387451 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((97666594089471 : ℚ) / 31250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3217:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_455 : ((((1570742331266961 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3221 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3217 < q → q < 3221 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3221).mp (by decide +kernel))) hgap
  have hprev := thV_454
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3221:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1570742331266961 : ℚ) / 500000000000) ≤ ((3133407215387451 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (3221:ℚ) := by decide +kernel
  have hratR : ((((1570742331266961 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((3133407215387451 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3221:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_456 : ((((157478229515091 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3229 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3221 < q → q < 3229 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3229).mp (by decide +kernel))) hgap
  have hprev := thV_455
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3229:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((157478229515091 : ℚ) / 50000000000) ≤ ((1570742331266961 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (3229:ℚ) := by decide +kernel
  have hratR : ((((157478229515091 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((1570742331266961 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3229:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_457 : ((((24669150845463 : ℚ) / 7812500000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3251 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3229 < q → q < 3251 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3251).mp (by decide +kernel))) hgap
  have hprev := thV_456
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3251:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((24669150845463 : ℚ) / 7812500000) ≤ ((157478229515091 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (3251:ℚ) := by decide +kernel
  have hratR : ((((24669150845463 : ℚ) / 7812500000) : ℚ) : ℝ) ≤ ((((157478229515091 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3251:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_458 : ((((3165738641142877 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3253 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3251 < q → q < 3253 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3253).mp (by decide +kernel))) hgap
  have hprev := thV_457
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3253:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3165738641142877 : ℚ) / 1000000000000) ≤ ((24669150845463 : ℚ) / 7812500000) + Work.RHContract.RegionI.logLowQ (3253:ℚ) := by decide +kernel
  have hratR : ((((3165738641142877 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((24669150845463 : ℚ) / 7812500000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3253:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_459 : ((((3173827202945293 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3257 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3253 < q → q < 3257 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3257).mp (by decide +kernel))) hgap
  have hprev := thV_458
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3257:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3173827202945293 : ℚ) / 1000000000000) ≤ ((3165738641142877 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (3257:ℚ) := by decide +kernel
  have hratR : ((((3173827202945293 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3165738641142877 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3257:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_460 : ((((3181916378621271 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3259 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3257 < q → q < 3259 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3259).mp (by decide +kernel))) hgap
  have hprev := thV_459
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3259:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3181916378621271 : ℚ) / 1000000000000) ≤ ((3173827202945293 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (3259:ℚ) := by decide +kernel
  have hratR : ((((3181916378621271 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3173827202945293 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3259:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_461 : ((((3190009229645949 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3271 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3259 < q → q < 3271 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3271).mp (by decide +kernel))) hgap
  have hprev := thV_460
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3271:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3190009229645949 : ℚ) / 1000000000000) ≤ ((3181916378621271 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (3271:ℚ) := by decide +kernel
  have hratR : ((((3190009229645949 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3181916378621271 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3271:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_462 : ((((1599055302157159 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3299 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3271 < q → q < 3299 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3299).mp (by decide +kernel))) hgap
  have hprev := thV_461
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3299:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1599055302157159 : ℚ) / 500000000000) ≤ ((3190009229645949 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (3299:ℚ) := by decide +kernel
  have hratR : ((((1599055302157159 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((3190009229645949 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3299:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_463 : ((((3206212585043311 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3301 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3299 < q → q < 3301 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3301).mp (by decide +kernel))) hgap
  have hprev := thV_462
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3301:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3206212585043311 : ℚ) / 1000000000000) ≤ ((1599055302157159 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (3301:ℚ) := by decide +kernel
  have hratR : ((((3206212585043311 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1599055302157159 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3301:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_464 : ((((3214316381753433 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3307 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3301 < q → q < 3307 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3307).mp (by decide +kernel))) hgap
  have hprev := thV_463
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3307:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3214316381753433 : ℚ) / 1000000000000) ≤ ((3206212585043311 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (3307:ℚ) := by decide +kernel
  have hratR : ((((3214316381753433 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3206212585043311 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3307:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_465 : ((((3222421991152873 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3313 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3307 < q → q < 3313 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3313).mp (by decide +kernel))) hgap
  have hprev := thV_464
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3313:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3222421991152873 : ℚ) / 1000000000000) ≤ ((3214316381753433 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (3313:ℚ) := by decide +kernel
  have hratR : ((((3222421991152873 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3214316381753433 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3313:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_466 : ((((3230529409961733 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3319 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3313 < q → q < 3319 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3319).mp (by decide +kernel))) hgap
  have hprev := thV_465
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3319:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3230529409961733 : ℚ) / 1000000000000) ≤ ((3222421991152873 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (3319:ℚ) := by decide +kernel
  have hratR : ((((3230529409961733 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3222421991152873 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3319:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_467 : ((((809659508306807 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3323 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3319 < q → q < 3323 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3323).mp (by decide +kernel))) hgap
  have hprev := thV_466
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3323:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((809659508306807 : ℚ) / 250000000000) ≤ ((3230529409961733 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (3323:ℚ) := by decide +kernel
  have hratR : ((((809659508306807 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((3230529409961733 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3323:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_468 : ((((3246748460461943 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3329 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3323 < q → q < 3329 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3329).mp (by decide +kernel))) hgap
  have hprev := thV_467
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3329:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3246748460461943 : ℚ) / 1000000000000) ≤ ((809659508306807 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (3329:ℚ) := by decide +kernel
  have hratR : ((((3246748460461943 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((809659508306807 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3329:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_469 : ((((3254859488297277 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3331 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3329 < q → q < 3331 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3331).mp (by decide +kernel))) hgap
  have hprev := thV_468
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3331:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3254859488297277 : ℚ) / 1000000000000) ≤ ((3246748460461943 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (3331:ℚ) := by decide +kernel
  have hratR : ((((3254859488297277 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3246748460461943 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3331:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_470 : ((((3262974112180837 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3343 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3331 < q → q < 3343 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3343).mp (by decide +kernel))) hgap
  have hprev := thV_469
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3343:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3262974112180837 : ℚ) / 1000000000000) ≤ ((3254859488297277 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (3343:ℚ) := by decide +kernel
  have hratR : ((((3262974112180837 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3254859488297277 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3343:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_471 : ((((817772482969797 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3347 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3343 < q → q < 3347 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3347).mp (by decide +kernel))) hgap
  have hprev := thV_470
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3347:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((817772482969797 : ℚ) / 250000000000) ≤ ((3262974112180837 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (3347:ℚ) := by decide +kernel
  have hratR : ((((817772482969797 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((3262974112180837 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3347:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_472 : ((((163960466523297 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3359 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3347 < q → q < 3359 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3359).mp (by decide +kernel))) hgap
  have hprev := thV_471
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3359:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((163960466523297 : ℚ) / 50000000000) ≤ ((817772482969797 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (3359:ℚ) := by decide +kernel
  have hratR : ((((163960466523297 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((817772482969797 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3359:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_473 : ((((657465864858161 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3361 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3359 < q → q < 3361 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3361).mp (by decide +kernel))) hgap
  have hprev := thV_472
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3361:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((657465864858161 : ℚ) / 200000000000) ≤ ((163960466523297 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (3361:ℚ) := by decide +kernel
  have hratR : ((((657465864858161 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((163960466523297 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3361:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_474 : ((((3295452289003179 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3371 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3361 < q → q < 3371 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3371).mp (by decide +kernel))) hgap
  have hprev := thV_473
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3371:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3295452289003179 : ℚ) / 1000000000000) ≤ ((657465864858161 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (3371:ℚ) := by decide +kernel
  have hratR : ((((3295452289003179 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((657465864858161 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3371:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_475 : ((((3303575846835381 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3373 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3371 < q → q < 3373 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3373).mp (by decide +kernel))) hgap
  have hprev := thV_474
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3373:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3303575846835381 : ℚ) / 1000000000000) ≤ ((3295452289003179 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (3373:ℚ) := by decide +kernel
  have hratR : ((((3303575846835381 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3295452289003179 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3373:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_476 : ((((103490754281379 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3389 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3373 < q → q < 3389 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3389).mp (by decide +kernel))) hgap
  have hprev := thV_475
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3389:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((103490754281379 : ℚ) / 31250000000) ≤ ((3303575846835381 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (3389:ℚ) := by decide +kernel
  have hratR : ((((103490754281379 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((3303575846835381 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3389:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_477 : ((((1659916508571697 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3391 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3389 < q → q < 3391 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3391).mp (by decide +kernel))) hgap
  have hprev := thV_476
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3391:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1659916508571697 : ℚ) / 500000000000) ≤ ((103490754281379 : ℚ) / 31250000000) + Work.RHContract.RegionI.logLowQ (3391:ℚ) := by decide +kernel
  have hratR : ((((1659916508571697 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((103490754281379 : ℚ) / 31250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3391:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_478 : ((((665593320911639 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3407 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3391 < q → q < 3407 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3407).mp (by decide +kernel))) hgap
  have hprev := thV_477
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3407:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((665593320911639 : ℚ) / 200000000000) ≤ ((1659916508571697 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (3407:ℚ) := by decide +kernel
  have hratR : ((((665593320911639 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((1659916508571697 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3407:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_479 : ((((1668050975752121 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3413 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3407 < q → q < 3413 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3413).mp (by decide +kernel))) hgap
  have hprev := thV_478
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3413:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1668050975752121 : ℚ) / 500000000000) ≤ ((665593320911639 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (3413:ℚ) := by decide +kernel
  have hratR : ((((1668050975752121 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((665593320911639 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3413:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_480 : ((((83606078532371 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3433 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3413 < q → q < 3433 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3433).mp (by decide +kernel))) hgap
  have hprev := thV_479
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3433:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((83606078532371 : ℚ) / 25000000000) ≤ ((1668050975752121 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (3433:ℚ) := by decide +kernel
  have hratR : ((((83606078532371 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((1668050975752121 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3433:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_481 : ((((3352388980904917 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3449 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3433 < q → q < 3449 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3449).mp (by decide +kernel))) hgap
  have hprev := thV_480
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3449:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3352388980904917 : ℚ) / 1000000000000) ≤ ((83606078532371 : ℚ) / 25000000000) + Work.RHContract.RegionI.logLowQ (3449:ℚ) := by decide +kernel
  have hratR : ((((3352388980904917 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((83606078532371 : ℚ) / 25000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3449:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_482 : ((((3360537137341979 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3457 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3449 < q → q < 3457 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3457).mp (by decide +kernel))) hgap
  have hprev := thV_481
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3457:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3360537137341979 : ℚ) / 1000000000000) ≤ ((3352388980904917 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (3457:ℚ) := by decide +kernel
  have hratR : ((((3360537137341979 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3352388980904917 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3457:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_483 : ((((1684343225091377 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3461 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3457 < q → q < 3461 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3461).mp (by decide +kernel))) hgap
  have hprev := thV_482
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3461:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1684343225091377 : ℚ) / 500000000000) ≤ ((3360537137341979 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (3461:ℚ) := by decide +kernel
  have hratR : ((((1684343225091377 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((3360537137341979 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3461:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_484 : ((((3376836340724297 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3463 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3461 < q → q < 3463 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3463).mp (by decide +kernel))) hgap
  have hprev := thV_483
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3463:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3376836340724297 : ℚ) / 1000000000000) ≤ ((1684343225091377 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (3463:ℚ) := by decide +kernel
  have hratR : ((((3376836340724297 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1684343225091377 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3463:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_485 : ((((1692493692833561 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3467 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3463 < q → q < 3467 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3467).mp (by decide +kernel))) hgap
  have hprev := thV_484
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3467:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1692493692833561 : ℚ) / 500000000000) ≤ ((3376836340724297 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (3467:ℚ) := by decide +kernel
  have hratR : ((((1692493692833561 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((3376836340724297 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3467:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_486 : ((((26508898494619 : ℚ) / 7812500000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3469 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3467 < q → q < 3469 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3469).mp (by decide +kernel))) hgap
  have hprev := thV_485
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3469:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((26508898494619 : ℚ) / 7812500000) ≤ ((1692493692833561 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (3469:ℚ) := by decide +kernel
  have hratR : ((((26508898494619 : ℚ) / 7812500000) : ℚ) : ℝ) ≤ ((((1692493692833561 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3469:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_487 : ((((3401296950815477 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3491 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3469 < q → q < 3491 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3491).mp (by decide +kernel))) hgap
  have hprev := thV_486
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3491:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3401296950815477 : ℚ) / 1000000000000) ≤ ((26508898494619 : ℚ) / 7812500000) + Work.RHContract.RegionI.logLowQ (3491:ℚ) := by decide +kernel
  have hratR : ((((3401296950815477 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((26508898494619 : ℚ) / 7812500000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3491:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_488 : ((((681891436660997 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3499 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3491 < q → q < 3499 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3499).mp (by decide +kernel))) hgap
  have hprev := thV_487
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3499:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((681891436660997 : ℚ) / 200000000000) ≤ ((3401296950815477 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (3499:ℚ) := by decide +kernel
  have hratR : ((((681891436660997 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((3401296950815477 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3499:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_489 : ((((1708810419739147 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3511 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3499 < q → q < 3511 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3511).mp (by decide +kernel))) hgap
  have hprev := thV_488
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3511:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1708810419739147 : ℚ) / 500000000000) ≤ ((681891436660997 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (3511:ℚ) := by decide +kernel
  have hratR : ((((1708810419739147 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((681891436660997 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3511:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_490 : ((((856446550776977 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3517 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3511 < q → q < 3517 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3517).mp (by decide +kernel))) hgap
  have hprev := thV_489
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3517:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((856446550776977 : ℚ) / 250000000000) ≤ ((1708810419739147 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (3517:ℚ) := by decide +kernel
  have hratR : ((((856446550776977 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((1708810419739147 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3517:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_491 : ((((858488601508821 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3527 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3517 < q → q < 3527 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3527).mp (by decide +kernel))) hgap
  have hprev := thV_490
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3527:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((858488601508821 : ℚ) / 250000000000) ≤ ((856446550776977 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (3527:ℚ) := by decide +kernel
  have hratR : ((((858488601508821 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((856446550776977 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3527:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_492 : ((((3442123175856099 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3529 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3527 < q → q < 3529 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3529).mp (by decide +kernel))) hgap
  have hprev := thV_491
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3529:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3442123175856099 : ℚ) / 1000000000000) ≤ ((858488601508821 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (3529:ℚ) := by decide +kernel
  have hratR : ((((3442123175856099 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((858488601508821 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3529:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_493 : ((((1725146539250299 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3533 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3529 < q → q < 3533 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3533).mp (by decide +kernel))) hgap
  have hprev := thV_492
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3533:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1725146539250299 : ℚ) / 500000000000) ≤ ((3442123175856099 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (3533:ℚ) := by decide +kernel
  have hratR : ((((1725146539250299 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((3442123175856099 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3533:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_494 : ((((864616169494521 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3539 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3533 < q → q < 3539 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3539).mp (by decide +kernel))) hgap
  have hprev := thV_493
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3539:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((864616169494521 : ℚ) / 250000000000) ≤ ((1725146539250299 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (3539:ℚ) := by decide +kernel
  have hratR : ((((864616169494521 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((1725146539250299 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3539:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_495 : ((((433329605303417 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3541 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3539 < q → q < 3541 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3541).mp (by decide +kernel))) hgap
  have hprev := thV_494
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3541:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((433329605303417 : ℚ) / 125000000000) ≤ ((864616169494521 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (3541:ℚ) := by decide +kernel
  have hratR : ((((433329605303417 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((864616169494521 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3541:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_496 : ((((13899242799517 : ℚ) / 4000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3547 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3541 < q → q < 3547 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3547).mp (by decide +kernel))) hgap
  have hprev := thV_495
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3547:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13899242799517 : ℚ) / 4000000000) ≤ ((433329605303417 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (3547:ℚ) := by decide +kernel
  have hratR : ((((13899242799517 : ℚ) / 4000000000) : ℚ) : ℝ) ≤ ((((433329605303417 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3547:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_497 : ((((3482987372648339 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3557 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3547 < q → q < 3557 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3557).mp (by decide +kernel))) hgap
  have hprev := thV_496
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3557:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3482987372648339 : ℚ) / 1000000000000) ≤ ((13899242799517 : ℚ) / 4000000000) + Work.RHContract.RegionI.logLowQ (3557:ℚ) := by decide +kernel
  have hratR : ((((3482987372648339 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((13899242799517 : ℚ) / 4000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3557:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_498 : ((((3491164607530989 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3559 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3557 < q → q < 3559 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3559).mp (by decide +kernel))) hgap
  have hprev := thV_497
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3559:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3491164607530989 : ℚ) / 1000000000000) ≤ ((3482987372648339 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (3559:ℚ) := by decide +kernel
  have hratR : ((((3491164607530989 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3482987372648339 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3559:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_499 : ((((874836302118931 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3571 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3559 < q → q < 3571 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3571).mp (by decide +kernel))) hgap
  have hprev := thV_498
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3571:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((874836302118931 : ℚ) / 250000000000) ≤ ((3491164607530989 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (3571:ℚ) := by decide +kernel
  have hratR : ((((874836302118931 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((3491164607530989 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3571:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_500 : ((((3507528605842863 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3581 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3571 < q → q < 3581 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3581).mp (by decide +kernel))) hgap
  have hprev := thV_499
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3581:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3507528605842863 : ℚ) / 1000000000000) ≤ ((874836302118931 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (3581:ℚ) := by decide +kernel
  have hratR : ((((3507528605842863 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((874836302118931 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3581:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_501 : ((((878928140389327 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3583 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3581 < q → q < 3583 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3583).mp (by decide +kernel))) hgap
  have hprev := thV_500
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3583:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((878928140389327 : ℚ) / 250000000000) ≤ ((3507528605842863 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (3583:ℚ) := by decide +kernel
  have hratR : ((((878928140389327 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((3507528605842863 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3583:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_502 : ((((1761949652170781 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3593 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3583 < q → q < 3593 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3593).mp (by decide +kernel))) hgap
  have hprev := thV_501
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3593:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1761949652170781 : ℚ) / 500000000000) ≤ ((878928140389327 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (3593:ℚ) := by decide +kernel
  have hratR : ((((1761949652170781 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((878928140389327 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3593:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_503 : ((((1766044968009803 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3607 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3593 < q → q < 3607 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3607).mp (by decide +kernel))) hgap
  have hprev := thV_502
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3607:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1766044968009803 : ℚ) / 500000000000) ≤ ((1761949652170781 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (3607:ℚ) := by decide +kernel
  have hratR : ((((1766044968009803 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1761949652170781 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3607:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_504 : ((((1770141114873947 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3613 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3607 < q → q < 3613 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3613).mp (by decide +kernel))) hgap
  have hprev := thV_503
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3613:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1770141114873947 : ℚ) / 500000000000) ≤ ((1766044968009803 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (3613:ℚ) := by decide +kernel
  have hratR : ((((1770141114873947 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1766044968009803 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3613:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_505 : ((((1774237814988493 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3617 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3613 < q → q < 3617 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3617).mp (by decide +kernel))) hgap
  have hprev := thV_504
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3617:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1774237814988493 : ℚ) / 500000000000) ≤ ((1770141114873947 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (3617:ℚ) := by decide +kernel
  have hratR : ((((1774237814988493 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1770141114873947 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3617:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_506 : ((((3556670687665021 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3623 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3617 < q → q < 3623 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3623).mp (by decide +kernel))) hgap
  have hprev := thV_505
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3623:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3556670687665021 : ℚ) / 1000000000000) ≤ ((1774237814988493 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (3623:ℚ) := by decide +kernel
  have hratR : ((((3556670687665021 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1774237814988493 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3623:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_507 : ((((142594718041343 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3631 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3623 < q → q < 3631 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3631).mp (by decide +kernel))) hgap
  have hprev := thV_506
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3631:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((142594718041343 : ℚ) / 40000000000) ≤ ((3556670687665021 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (3631:ℚ) := by decide +kernel
  have hratR : ((((142594718041343 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((3556670687665021 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3631:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_508 : ((((1786533432737851 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3637 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3631 < q → q < 3637 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3637).mp (by decide +kernel))) hgap
  have hprev := thV_507
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3637:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1786533432737851 : ℚ) / 500000000000) ≤ ((142594718041343 : ℚ) / 40000000000) + Work.RHContract.RegionI.logLowQ (3637:ℚ) := by decide +kernel
  have hratR : ((((1786533432737851 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((142594718041343 : ℚ) / 40000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3637:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_509 : ((((3581267428269851 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3643 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3637 < q → q < 3643 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3643).mp (by decide +kernel))) hgap
  have hprev := thV_508
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3643:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3581267428269851 : ℚ) / 1000000000000) ≤ ((1786533432737851 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (3643:ℚ) := by decide +kernel
  have hratR : ((((3581267428269851 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1786533432737851 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3643:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_510 : ((((358947237343201 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3659 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3643 < q → q < 3659 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3659).mp (by decide +kernel))) hgap
  have hprev := thV_509
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3659:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((358947237343201 : ℚ) / 100000000000) ≤ ((3581267428269851 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (3659:ℚ) := by decide +kernel
  have hratR : ((((358947237343201 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((3581267428269851 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3659:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_511 : ((((3597680592812647 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3671 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3659 < q → q < 3671 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3671).mp (by decide +kernel))) hgap
  have hprev := thV_510
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3671:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3597680592812647 : ℚ) / 1000000000000) ≤ ((358947237343201 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (3671:ℚ) := by decide +kernel
  have hratR : ((((3597680592812647 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((358947237343201 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3671:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_512 : ((((3605889356855607 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3673 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3671 < q → q < 3673 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3673).mp (by decide +kernel))) hgap
  have hprev := thV_511
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3673:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3605889356855607 : ℚ) / 1000000000000) ≤ ((3597680592812647 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (3673:ℚ) := by decide +kernel
  have hratR : ((((3605889356855607 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3597680592812647 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3673:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_513 : ((((112940600291689 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3677 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3673 < q → q < 3677 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3677).mp (by decide +kernel))) hgap
  have hprev := thV_512
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3677:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((112940600291689 : ℚ) / 31250000000) ≤ ((3605889356855607 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (3677:ℚ) := by decide +kernel
  have hratR : ((((112940600291689 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((3605889356855607 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3677:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_514 : ((((1811156431017109 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3691 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3677 < q → q < 3691 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3691).mp (by decide +kernel))) hgap
  have hprev := thV_513
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3691:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1811156431017109 : ℚ) / 500000000000) ≤ ((112940600291689 : ℚ) / 31250000000) + Work.RHContract.RegionI.logLowQ (3691:ℚ) := by decide +kernel
  have hratR : ((((1811156431017109 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((112940600291689 : ℚ) / 31250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3691:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_515 : ((((726105627798059 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3697 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3691 < q → q < 3697 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3697).mp (by decide +kernel))) hgap
  have hprev := thV_514
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3697:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((726105627798059 : ℚ) / 200000000000) ≤ ((1811156431017109 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (3697:ℚ) := by decide +kernel
  have hratR : ((((726105627798059 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((1811156431017109 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3697:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_516 : ((((3638744497319821 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3701 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3697 < q → q < 3701 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3701).mp (by decide +kernel))) hgap
  have hprev := thV_515
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3701:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3638744497319821 : ℚ) / 1000000000000) ≤ ((726105627798059 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (3701:ℚ) := by decide +kernel
  have hratR : ((((3638744497319821 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((726105627798059 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3701:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_517 : ((((3646963014894451 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3709 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3701 < q → q < 3709 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3709).mp (by decide +kernel))) hgap
  have hprev := thV_516
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3709:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3646963014894451 : ℚ) / 1000000000000) ≤ ((3638744497319821 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (3709:ℚ) := by decide +kernel
  have hratR : ((((3646963014894451 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3638744497319821 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3709:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_518 : ((((913796056246379 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3719 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3709 < q → q < 3719 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3719).mp (by decide +kernel))) hgap
  have hprev := thV_517
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3719:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((913796056246379 : ℚ) / 250000000000) ≤ ((3646963014894451 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (3719:ℚ) := by decide +kernel
  have hratR : ((((913796056246379 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((3646963014894451 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3719:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_519 : ((((732681516776427 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3727 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3719 < q → q < 3727 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3727).mp (by decide +kernel))) hgap
  have hprev := thV_518
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3727:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((732681516776427 : ℚ) / 200000000000) ≤ ((913796056246379 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (3727:ℚ) := by decide +kernel
  have hratR : ((((732681516776427 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((913796056246379 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3727:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_520 : ((((367163255135819 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3733 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3727 < q → q < 3733 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3733).mp (by decide +kernel))) hgap
  have hprev := thV_519
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3733:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((367163255135819 : ℚ) / 100000000000) ≤ ((732681516776427 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (3733:ℚ) := by decide +kernel
  have hratR : ((((367163255135819 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((732681516776427 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3733:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_521 : ((((3679859124830307 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3739 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3733 < q → q < 3739 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3739).mp (by decide +kernel))) hgap
  have hprev := thV_520
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3739:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3679859124830307 : ℚ) / 1000000000000) ≤ ((367163255135819 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (3739:ℚ) := by decide +kernel
  have hratR : ((((3679859124830307 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((367163255135819 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3739:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_522 : ((((3688091564985917 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3761 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3739 < q → q < 3761 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3761).mp (by decide +kernel))) hgap
  have hprev := thV_521
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3761:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3688091564985917 : ℚ) / 1000000000000) ≤ ((3679859124830307 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (3761:ℚ) := by decide +kernel
  have hratR : ((((3688091564985917 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3679859124830307 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3761:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_523 : ((((3696325599190749 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3767 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3761 < q → q < 3767 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3767).mp (by decide +kernel))) hgap
  have hprev := thV_522
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3767:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3696325599190749 : ℚ) / 1000000000000) ≤ ((3688091564985917 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (3767:ℚ) := by decide +kernel
  have hratR : ((((3696325599190749 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3688091564985917 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3767:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_524 : ((((926140041045289 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3769 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3767 < q → q < 3769 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3769).mp (by decide +kernel))) hgap
  have hprev := thV_523
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3769:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((926140041045289 : ℚ) / 250000000000) ≤ ((3696325599190749 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (3769:ℚ) := by decide +kernel
  have hratR : ((((926140041045289 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((3696325599190749 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3769:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_525 : ((((1856398689440823 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3779 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3769 < q → q < 3779 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3779).mp (by decide +kernel))) hgap
  have hprev := thV_524
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3779:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1856398689440823 : ℚ) / 500000000000) ≤ ((926140041045289 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (3779:ℚ) := by decide +kernel
  have hratR : ((((1856398689440823 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((926140041045289 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3779:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_526 : ((((148841531656819 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3793 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3779 < q → q < 3793 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3793).mp (by decide +kernel))) hgap
  have hprev := thV_525
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3793:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((148841531656819 : ℚ) / 40000000000) ≤ ((1856398689440823 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (3793:ℚ) := by decide +kernel
  have hratR : ((((148841531656819 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((1856398689440823 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3793:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_527 : ((((3729280257977847 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3797 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3793 < q → q < 3797 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3797).mp (by decide +kernel))) hgap
  have hprev := thV_526
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3797:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3729280257977847 : ℚ) / 1000000000000) ≤ ((148841531656819 : ℚ) / 40000000000) + Work.RHContract.RegionI.logLowQ (3797:ℚ) := by decide +kernel
  have hratR : ((((3729280257977847 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((148841531656819 : ℚ) / 40000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3797:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_528 : ((((747504760696583 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3803 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3797 < q → q < 3803 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3803).mp (by decide +kernel))) hgap
  have hprev := thV_527
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3803:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((747504760696583 : ℚ) / 200000000000) ≤ ((3729280257977847 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (3803:ℚ) := by decide +kernel
  have hratR : ((((747504760696583 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((3729280257977847 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3803:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_529 : ((((1872886035463751 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3821 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3803 < q → q < 3821 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3821).mp (by decide +kernel))) hgap
  have hprev := thV_528
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3821:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1872886035463751 : ℚ) / 500000000000) ≤ ((747504760696583 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (3821:ℚ) := by decide +kernel
  have hratR : ((((1872886035463751 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((747504760696583 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3821:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_530 : ((((3754020861658339 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3823 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3821 < q → q < 3823 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3823).mp (by decide +kernel))) hgap
  have hprev := thV_529
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3823:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3754020861658339 : ℚ) / 1000000000000) ≤ ((1872886035463751 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (3823:ℚ) := by decide +kernel
  have hratR : ((((3754020861658339 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1872886035463751 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3823:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_531 : ((((188113613236043 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3833 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3823 < q → q < 3833 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3833).mp (by decide +kernel))) hgap
  have hprev := thV_530
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3833:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((188113613236043 : ℚ) / 50000000000) ≤ ((3754020861658339 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (3833:ℚ) := by decide +kernel
  have hratR : ((((188113613236043 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((3754020861658339 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3833:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_532 : ((((235657957101297 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3847 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3833 < q → q < 3847 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3847).mp (by decide +kernel))) hgap
  have hprev := thV_531
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3847:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((235657957101297 : ℚ) / 62500000000) ≤ ((188113613236043 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (3847:ℚ) := by decide +kernel
  have hratR : ((((235657957101297 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((188113613236043 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3847:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_533 : ((((3778783401751707 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3851 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3847 < q → q < 3851 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3851).mp (by decide +kernel))) hgap
  have hprev := thV_532
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3851:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3778783401751707 : ℚ) / 1000000000000) ≤ ((235657957101297 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (3851:ℚ) := by decide +kernel
  have hratR : ((((3778783401751707 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((235657957101297 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3851:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_534 : ((((3787040009093473 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3853 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3851 < q → q < 3853 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3853).mp (by decide +kernel))) hgap
  have hprev := thV_533
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3853:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3787040009093473 : ℚ) / 1000000000000) ≤ ((3778783401751707 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (3853:ℚ) := by decide +kernel
  have hratR : ((((3787040009093473 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3778783401751707 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3853:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_535 : ((((3795299208453279 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3863 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3853 < q → q < 3863 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3863).mp (by decide +kernel))) hgap
  have hprev := thV_534
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3863:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3795299208453279 : ℚ) / 1000000000000) ≤ ((3787040009093473 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (3863:ℚ) := by decide +kernel
  have hratR : ((((3795299208453279 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3787040009093473 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3863:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_536 : ((((380356202538809 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3877 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3863 < q → q < 3877 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3877).mp (by decide +kernel))) hgap
  have hprev := thV_535
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3877:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((380356202538809 : ℚ) / 100000000000) ≤ ((3795299208453279 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (3877:ℚ) := by decide +kernel
  have hratR : ((((380356202538809 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((3795299208453279 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3877:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_537 : ((((3811825873516599 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3881 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3877 < q → q < 3881 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3881).mp (by decide +kernel))) hgap
  have hprev := thV_536
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3881:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3811825873516599 : ℚ) / 1000000000000) ≤ ((380356202538809 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (3881:ℚ) := by decide +kernel
  have hratR : ((((3811825873516599 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((380356202538809 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3881:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_538 : ((((764018356169579 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3889 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3881 < q → q < 3889 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3889).mp (by decide +kernel))) hgap
  have hprev := thV_537
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3889:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((764018356169579 : ℚ) / 200000000000) ≤ ((3811825873516599 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (3889:ℚ) := by decide +kernel
  have hratR : ((((764018356169579 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((3811825873516599 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3889:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_539 : ((((382836230594009 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3907 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3889 < q → q < 3907 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3907).mp (by decide +kernel))) hgap
  have hprev := thV_538
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3907:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((382836230594009 : ℚ) / 100000000000) ≤ ((764018356169579 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (3907:ℚ) := by decide +kernel
  have hratR : ((((382836230594009 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((764018356169579 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3907:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_540 : ((((1918316927155993 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3911 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3907 < q → q < 3911 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3911).mp (by decide +kernel))) hgap
  have hprev := thV_539
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3911:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1918316927155993 : ℚ) / 500000000000) ≤ ((382836230594009 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (3911:ℚ) := by decide +kernel
  have hratR : ((((1918316927155993 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((382836230594009 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3911:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_541 : ((((480613366955349 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3917 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3911 < q → q < 3917 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3917).mp (by decide +kernel))) hgap
  have hprev := thV_540
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3917:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((480613366955349 : ℚ) / 125000000000) ≤ ((1918316927155993 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (3917:ℚ) := by decide +kernel
  have hratR : ((((480613366955349 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((1918316927155993 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3917:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_542 : ((((963295131859533 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3919 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3917 < q → q < 3919 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3919).mp (by decide +kernel))) hgap
  have hprev := thV_541
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3919:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((963295131859533 : ℚ) / 250000000000) ≤ ((480613366955349 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (3919:ℚ) := by decide +kernel
  have hratR : ((((963295131859533 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((480613366955349 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3919:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_543 : ((((1930727569690741 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3923 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3919 < q → q < 3923 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3923).mp (by decide +kernel))) hgap
  have hprev := thV_542
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3923:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1930727569690741 : ℚ) / 500000000000) ≤ ((963295131859533 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (3923:ℚ) := by decide +kernel
  have hratR : ((((1930727569690741 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((963295131859533 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3923:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_544 : ((((3869731279598181 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3929 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3923 < q → q < 3929 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3929).mp (by decide +kernel))) hgap
  have hprev := thV_543
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3929:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3869731279598181 : ℚ) / 1000000000000) ≤ ((1930727569690741 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (3929:ℚ) := by decide +kernel
  have hratR : ((((3869731279598181 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1930727569690741 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3929:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_545 : ((((3878007928720743 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3931 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3929 < q → q < 3931 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3931).mp (by decide +kernel))) hgap
  have hprev := thV_544
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3931:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3878007928720743 : ℚ) / 1000000000000) ≤ ((3869731279598181 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (3931:ℚ) := by decide +kernel
  have hratR : ((((3878007928720743 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3869731279598181 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3931:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_546 : ((((3886287625851761 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3943 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3931 < q → q < 3943 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3943).mp (by decide +kernel))) hgap
  have hprev := thV_545
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3943:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3886287625851761 : ℚ) / 1000000000000) ≤ ((3878007928720743 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (3943:ℚ) := by decide +kernel
  have hratR : ((((3886287625851761 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3878007928720743 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3943:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_547 : ((((973642084231141 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3947 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3943 < q → q < 3947 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3947).mp (by decide +kernel))) hgap
  have hprev := thV_546
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3947:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((973642084231141 : ℚ) / 250000000000) ≤ ((3886287625851761 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (3947:ℚ) := by decide +kernel
  have hratR : ((((973642084231141 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((3886287625851761 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3947:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_548 : ((((1951427051171109 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3967 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3947 < q → q < 3967 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3967).mp (by decide +kernel))) hgap
  have hprev := thV_547
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3967:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1951427051171109 : ℚ) / 500000000000) ≤ ((973642084231141 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (3967:ℚ) := by decide +kernel
  have hratR : ((((1951427051171109 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((973642084231141 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3967:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_549 : ((((122223293693477 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((3989 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3967 < q → q < 3989 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3989).mp (by decide +kernel))) hgap
  have hprev := thV_548
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (3989:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((122223293693477 : ℚ) / 31250000000) ≤ ((1951427051171109 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (3989:ℚ) := by decide +kernel
  have hratR : ((((122223293693477 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((1951427051171109 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (3989:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_550 : ((((3919439697797261 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4001 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3989 < q → q < 4001 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4001).mp (by decide +kernel))) hgap
  have hprev := thV_549
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4001:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3919439697797261 : ℚ) / 1000000000000) ≤ ((122223293693477 : ℚ) / 31250000000) + Work.RHContract.RegionI.logLowQ (4001:ℚ) := by decide +kernel
  have hratR : ((((3919439697797261 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((122223293693477 : ℚ) / 31250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4001:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_551 : ((((1963867248576697 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4003 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4001 < q → q < 4003 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4003).mp (by decide +kernel))) hgap
  have hprev := thV_550
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4003:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1963867248576697 : ℚ) / 500000000000) ≤ ((3919439697797261 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (4003:ℚ) := by decide +kernel
  have hratR : ((((1963867248576697 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((3919439697797261 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4003:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_552 : ((((393603029526117 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4007 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4003 < q → q < 4007 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4007).mp (by decide +kernel))) hgap
  have hprev := thV_551
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4007:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((393603029526117 : ℚ) / 100000000000) ≤ ((1963867248576697 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (4007:ℚ) := by decide +kernel
  have hratR : ((((393603029526117 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((1963867248576697 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4007:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_553 : ((((3944327589628577 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4013 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4007 < q → q < 4013 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4013).mp (by decide +kernel))) hgap
  have hprev := thV_552
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4013:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3944327589628577 : ℚ) / 1000000000000) ≤ ((393603029526117 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (4013:ℚ) := by decide +kernel
  have hratR : ((((3944327589628577 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((393603029526117 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4013:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_554 : ((((1976313189010083 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4019 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4013 < q → q < 4019 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4019).mp (by decide +kernel))) hgap
  have hprev := thV_553
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4019:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1976313189010083 : ℚ) / 500000000000) ≤ ((3944327589628577 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (4019:ℚ) := by decide +kernel
  have hratR : ((((1976313189010083 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((3944327589628577 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4019:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_555 : ((((3960925663924203 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4021 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4019 < q → q < 4021 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4021).mp (by decide +kernel))) hgap
  have hprev := thV_554
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4021:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3960925663924203 : ℚ) / 1000000000000) ≤ ((1976313189010083 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (4021:ℚ) := by decide +kernel
  have hratR : ((((3960925663924203 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1976313189010083 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4021:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_556 : ((((793845288176439 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4027 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4021 < q → q < 4027 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4027).mp (by decide +kernel))) hgap
  have hprev := thV_555
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4027:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((793845288176439 : ℚ) / 200000000000) ≤ ((3960925663924203 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (4027:ℚ) := by decide +kernel
  have hratR : ((((793845288176439 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((3960925663924203 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4027:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_557 : ((((3977532666095367 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4049 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4027 < q → q < 4049 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4049).mp (by decide +kernel))) hgap
  have hprev := thV_556
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4049:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3977532666095367 : ℚ) / 1000000000000) ≤ ((793845288176439 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (4049:ℚ) := by decide +kernel
  have hratR : ((((3977532666095367 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((793845288176439 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4049:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_558 : ((((398583938513571 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4051 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4049 < q → q < 4051 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4051).mp (by decide +kernel))) hgap
  have hprev := thV_557
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4051:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((398583938513571 : ℚ) / 100000000000) ≤ ((3977532666095367 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (4051:ℚ) := by decide +kernel
  have hratR : ((((398583938513571 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((3977532666095367 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4051:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_559 : ((((3994147584196057 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4057 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4051 < q → q < 4057 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4057).mp (by decide +kernel))) hgap
  have hprev := thV_558
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4057:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3994147584196057 : ℚ) / 1000000000000) ≤ ((398583938513571 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (4057:ℚ) := by decide +kernel
  have hratR : ((((3994147584196057 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((398583938513571 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4057:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_560 : ((((2001229859650423 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4073 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4057 < q → q < 4073 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4073).mp (by decide +kernel))) hgap
  have hprev := thV_559
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4073:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2001229859650423 : ℚ) / 500000000000) ≤ ((3994147584196057 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (4073:ℚ) := by decide +kernel
  have hratR : ((((2001229859650423 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((3994147584196057 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4073:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_561 : ((((501346665804663 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4079 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4073 < q → q < 4079 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4079).mp (by decide +kernel))) hgap
  have hprev := thV_560
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4079:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((501346665804663 : ℚ) / 125000000000) ≤ ((2001229859650423 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (4079:ℚ) := by decide +kernel
  have hratR : ((((501346665804663 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((2001229859650423 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4079:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_562 : ((((4019089871152373 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4091 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4079 < q → q < 4091 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4091).mp (by decide +kernel))) hgap
  have hprev := thV_561
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4091:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4019089871152373 : ℚ) / 1000000000000) ≤ ((501346665804663 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (4091:ℚ) := by decide +kernel
  have hratR : ((((4019089871152373 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((501346665804663 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4091:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_563 : ((((2013703452313003 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4093 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4091 < q → q < 4093 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4093).mp (by decide +kernel))) hgap
  have hprev := thV_562
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4093:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2013703452313003 : ℚ) / 500000000000) ≤ ((4019089871152373 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (4093:ℚ) := by decide +kernel
  have hratR : ((((2013703452313003 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((4019089871152373 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4093:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_564 : ((((403572540294339 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4099 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4093 < q → q < 4099 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4099).mp (by decide +kernel))) hgap
  have hprev := thV_563
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4099:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((403572540294339 : ℚ) / 100000000000) ≤ ((2013703452313003 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (4099:ℚ) := by decide +kernel
  have hratR : ((((403572540294339 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((2013703452313003 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4099:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_565 : ((((63188231633237 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4111 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4099 < q → q < 4111 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4111).mp (by decide +kernel))) hgap
  have hprev := thV_564
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4111:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((63188231633237 : ℚ) / 15625000000) ≤ ((403572540294339 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (4111:ℚ) := by decide +kernel
  have hratR : ((((63188231633237 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ ((((403572540294339 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4111:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_566 : ((((4052372130553801 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4127 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4111 < q → q < 4127 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4127).mp (by decide +kernel))) hgap
  have hprev := thV_565
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4127:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4052372130553801 : ℚ) / 1000000000000) ≤ ((63188231633237 : ℚ) / 15625000000) + Work.RHContract.RegionI.logLowQ (4127:ℚ) := by decide +kernel
  have hratR : ((((4052372130553801 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((63188231633237 : ℚ) / 15625000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4127:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_567 : ((((4060697921076567 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4129 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4127 < q → q < 4129 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4129).mp (by decide +kernel))) hgap
  have hprev := thV_566
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4129:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4060697921076567 : ℚ) / 1000000000000) ≤ ((4052372130553801 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (4129:ℚ) := by decide +kernel
  have hratR : ((((4060697921076567 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4052372130553801 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4129:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_568 : ((((4069024679887959 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4133 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4129 < q → q < 4133 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4133).mp (by decide +kernel))) hgap
  have hprev := thV_567
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4133:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4069024679887959 : ℚ) / 1000000000000) ≤ ((4060697921076567 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (4133:ℚ) := by decide +kernel
  have hratR : ((((4069024679887959 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4060697921076567 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4133:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_569 : ((((1019338222344147 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4139 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4133 < q → q < 4139 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4139).mp (by decide +kernel))) hgap
  have hprev := thV_568
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4139:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1019338222344147 : ℚ) / 250000000000) ≤ ((4069024679887959 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (4139:ℚ) := by decide +kernel
  have hratR : ((((1019338222344147 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((4069024679887959 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4139:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_570 : ((((4085684475617099 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4153 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4139 < q → q < 4153 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4153).mp (by decide +kernel))) hgap
  have hprev := thV_569
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4153:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4085684475617099 : ℚ) / 1000000000000) ≤ ((1019338222344147 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (4153:ℚ) := by decide +kernel
  have hratR : ((((4085684475617099 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1019338222344147 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4153:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_571 : ((((255876064034577 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4157 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4153 < q → q < 4157 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4157).mp (by decide +kernel))) hgap
  have hprev := thV_570
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4157:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((255876064034577 : ℚ) / 62500000000) ≤ ((4085684475617099 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (4157:ℚ) := by decide +kernel
  have hratR : ((((255876064034577 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((4085684475617099 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4157:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_572 : ((((820470010897971 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4159 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4157 < q → q < 4159 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4159).mp (by decide +kernel))) hgap
  have hprev := thV_571
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4159:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((820470010897971 : ℚ) / 200000000000) ≤ ((255876064034577 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (4159:ℚ) := by decide +kernel
  have hratR : ((((820470010897971 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((255876064034577 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4159:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_573 : ((((128458981345351 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4177 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4159 < q → q < 4177 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4177).mp (by decide +kernel))) hgap
  have hprev := thV_572
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4177:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((128458981345351 : ℚ) / 31250000000) ≤ ((820470010897971 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (4177:ℚ) := by decide +kernel
  have hratR : ((((128458981345351 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((820470010897971 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4177:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_574 : ((((2059515240459641 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4201 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4177 < q → q < 4201 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4201).mp (by decide +kernel))) hgap
  have hprev := thV_573
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4201:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2059515240459641 : ℚ) / 500000000000) ≤ ((128458981345351 : ℚ) / 31250000000) + Work.RHContract.RegionI.logLowQ (4201:ℚ) := by decide +kernel
  have hratR : ((((2059515240459641 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((128458981345351 : ℚ) / 31250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4201:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_575 : ((((1031843984086081 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4211 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4201 < q → q < 4211 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4211).mp (by decide +kernel))) hgap
  have hprev := thV_574
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4211:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1031843984086081 : ℚ) / 250000000000) ≤ ((2059515240459641 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (4211:ℚ) := by decide +kernel
  have hratR : ((((1031843984086081 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((2059515240459641 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4211:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_576 : ((((4135722815594951 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4217 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4211 < q → q < 4217 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4217).mp (by decide +kernel))) hgap
  have hprev := thV_575
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4217:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4135722815594951 : ℚ) / 1000000000000) ≤ ((1031843984086081 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (4217:ℚ) := by decide +kernel
  have hratR : ((((4135722815594951 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1031843984086081 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4217:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_577 : ((((828814033800791 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4219 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4217 < q → q < 4219 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4219).mp (by decide +kernel))) hgap
  have hprev := thV_576
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4219:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((828814033800791 : ℚ) / 200000000000) ≤ ((4135722815594951 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (4219:ℚ) := by decide +kernel
  have hratR : ((((828814033800791 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((4135722815594951 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4219:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_578 : ((((1038104972459577 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4229 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4219 < q → q < 4229 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4229).mp (by decide +kernel))) hgap
  have hprev := thV_577
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4229:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1038104972459577 : ℚ) / 250000000000) ≤ ((828814033800791 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (4229:ℚ) := by decide +kernel
  have hratR : ((((1038104972459577 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((828814033800791 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4229:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_579 : ((((1040192520871477 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4231 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4229 < q → q < 4231 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4231).mp (by decide +kernel))) hgap
  have hprev := thV_578
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4231:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1040192520871477 : ℚ) / 250000000000) ≤ ((1038104972459577 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (4231:ℚ) := by decide +kernel
  have hratR : ((((1040192520871477 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((1038104972459577 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4231:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_580 : ((((4169122637852263 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4241 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4231 < q → q < 4241 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4241).mp (by decide +kernel))) hgap
  have hprev := thV_579
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4241:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4169122637852263 : ℚ) / 1000000000000) ≤ ((1040192520871477 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (4241:ℚ) := by decide +kernel
  have hratR : ((((4169122637852263 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1040192520871477 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4241:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_581 : ((((835495132738869 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4243 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4241 < q → q < 4243 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4243).mp (by decide +kernel))) hgap
  have hprev := thV_580
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4243:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((835495132738869 : ℚ) / 200000000000) ≤ ((4169122637852263 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (4243:ℚ) := by decide +kernel
  have hratR : ((((835495132738869 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((4169122637852263 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4243:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_582 : ((((4185831043586479 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4253 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4243 < q → q < 4253 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4253).mp (by decide +kernel))) hgap
  have hprev := thV_581
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4253:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4185831043586479 : ℚ) / 1000000000000) ≤ ((835495132738869 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (4253:ℚ) := by decide +kernel
  have hratR : ((((4185831043586479 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((835495132738869 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4253:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_583 : ((((2097093916626641 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4259 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4253 < q → q < 4259 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4259).mp (by decide +kernel))) hgap
  have hprev := thV_582
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4259:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2097093916626641 : ℚ) / 500000000000) ≤ ((4185831043586479 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (4259:ℚ) := by decide +kernel
  have hratR : ((((2097093916626641 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((4185831043586479 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4259:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_584 : ((((2101272546201831 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4261 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4259 < q → q < 4261 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4261).mp (by decide +kernel))) hgap
  have hprev := thV_583
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4261:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2101272546201831 : ℚ) / 500000000000) ≤ ((2097093916626641 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (4261:ℚ) := by decide +kernel
  have hratR : ((((2101272546201831 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((2097093916626641 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4261:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_585 : ((((526363086958923 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4271 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4261 < q → q < 4271 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4271).mp (by decide +kernel))) hgap
  have hprev := thV_584
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4271:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((526363086958923 : ℚ) / 125000000000) ≤ ((2101272546201831 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (4271:ℚ) := by decide +kernel
  have hratR : ((((526363086958923 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((2101272546201831 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4271:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_586 : ((((1054816191775977 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4273 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4271 < q → q < 4273 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4273).mp (by decide +kernel))) hgap
  have hprev := thV_585
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4273:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1054816191775977 : ℚ) / 250000000000) ≤ ((526363086958923 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (4273:ℚ) := by decide +kernel
  have hratR : ((((1054816191775977 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((526363086958923 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4273:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_587 : ((((1056906794019601 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4283 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4273 < q → q < 4283 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4283).mp (by decide +kernel))) hgap
  have hprev := thV_586
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4283:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1056906794019601 : ℚ) / 250000000000) ≤ ((1054816191775977 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (4283:ℚ) := by decide +kernel
  have hratR : ((((1056906794019601 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((1054816191775977 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4283:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_588 : ((((4235990984959801 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4289 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4283 < q → q < 4289 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4289).mp (by decide +kernel))) hgap
  have hprev := thV_587
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4289:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4235990984959801 : ℚ) / 1000000000000) ≤ ((1056906794019601 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (4289:ℚ) := by decide +kernel
  have hratR : ((((4235990984959801 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1056906794019601 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4289:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_589 : ((((530544582167557 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4297 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4289 < q → q < 4297 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4297).mp (by decide +kernel))) hgap
  have hprev := thV_588
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4297:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((530544582167557 : ℚ) / 125000000000) ≤ ((4235990984959801 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (4297:ℚ) := by decide +kernel
  have hratR : ((((530544582167557 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((4235990984959801 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4297:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_590 : ((((4252729287077561 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4327 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4297 < q → q < 4327 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4327).mp (by decide +kernel))) hgap
  have hprev := thV_589
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4327:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4252729287077561 : ℚ) / 1000000000000) ≤ ((530544582167557 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (4327:ℚ) := by decide +kernel
  have hratR : ((((4252729287077561 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((530544582167557 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4327:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_591 : ((((4261104225218277 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4337 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4327 < q → q < 4337 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4337).mp (by decide +kernel))) hgap
  have hprev := thV_590
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4337:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4261104225218277 : ℚ) / 1000000000000) ≤ ((4252729287077561 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (4337:ℚ) := by decide +kernel
  have hratR : ((((4261104225218277 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4252729287077561 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4337:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_592 : ((((1067369906100239 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4339 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4337 < q → q < 4339 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4339).mp (by decide +kernel))) hgap
  have hprev := thV_591
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4339:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1067369906100239 : ℚ) / 250000000000) ≤ ((4261104225218277 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (4339:ℚ) := by decide +kernel
  have hratR : ((((1067369906100239 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((4261104225218277 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4339:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_593 : ((((2138928662805217 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4349 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4339 < q → q < 4349 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4349).mp (by decide +kernel))) hgap
  have hprev := thV_592
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4349:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2138928662805217 : ℚ) / 500000000000) ≤ ((1067369906100239 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (4349:ℚ) := by decide +kernel
  have hratR : ((((2138928662805217 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1067369906100239 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4349:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_594 : ((((535779608079179 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4357 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4349 < q → q < 4357 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4357).mp (by decide +kernel))) hgap
  have hprev := thV_593
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4357:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((535779608079179 : ℚ) / 125000000000) ≤ ((2138928662805217 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (4357:ℚ) := by decide +kernel
  have hratR : ((((535779608079179 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((2138928662805217 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4357:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_595 : ((((1073654444950859 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4363 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4357 < q → q < 4363 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4363).mp (by decide +kernel))) hgap
  have hprev := thV_594
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4363:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1073654444950859 : ℚ) / 250000000000) ≤ ((535779608079179 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (4363:ℚ) := by decide +kernel
  have hratR : ((((1073654444950859 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((535779608079179 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4363:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_596 : ((((4303000984351729 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4373 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4363 < q → q < 4373 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4373).mp (by decide +kernel))) hgap
  have hprev := thV_595
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4373:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4303000984351729 : ℚ) / 1000000000000) ≤ ((1073654444950859 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (4373:ℚ) := by decide +kernel
  have hratR : ((((4303000984351729 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1073654444950859 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4373:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_597 : ((((4311388296619171 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4391 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4373 < q → q < 4391 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4391).mp (by decide +kernel))) hgap
  have hprev := thV_596
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4391:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4311388296619171 : ℚ) / 1000000000000) ≤ ((4303000984351729 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (4391:ℚ) := by decide +kernel
  have hratR : ((((4311388296619171 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4303000984351729 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4391:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_598 : ((((269986060899077 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4397 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4391 < q → q < 4397 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4397).mp (by decide +kernel))) hgap
  have hprev := thV_597
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4397:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((269986060899077 : ℚ) / 62500000000) ≤ ((4311388296619171 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (4397:ℚ) := by decide +kernel
  have hratR : ((((269986060899077 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((4311388296619171 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4397:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_599 : ((((432816837756747 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4409 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4397 < q → q < 4409 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4409).mp (by decide +kernel))) hgap
  have hprev := thV_598
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4409:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((432816837756747 : ℚ) / 100000000000) ≤ ((269986060899077 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (4409:ℚ) := by decide +kernel
  have hratR : ((((432816837756747 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((269986060899077 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4409:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_600 : ((((135517578086193 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4421 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4409 < q → q < 4421 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4421).mp (by decide +kernel))) hgap
  have hprev := thV_599
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4421:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((135517578086193 : ℚ) / 31250000000) ≤ ((432816837756747 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (4421:ℚ) := by decide +kernel
  have hratR : ((((135517578086193 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((432816837756747 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4421:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_601 : ((((1086239268058231 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4423 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4421 < q → q < 4423 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4423).mp (by decide +kernel))) hgap
  have hprev := thV_600
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4423:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1086239268058231 : ℚ) / 250000000000) ≤ ((135517578086193 : ℚ) / 31250000000) + Work.RHContract.RegionI.logLowQ (4423:ℚ) := by decide +kernel
  have hratR : ((((1086239268058231 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((135517578086193 : ℚ) / 31250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4423:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_602 : ((((544169463385637 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4441 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4423 < q → q < 4441 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4441).mp (by decide +kernel))) hgap
  have hprev := thV_601
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4441:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((544169463385637 : ℚ) / 125000000000) ≤ ((1086239268058231 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (4441:ℚ) := by decide +kernel
  have hratR : ((((544169463385637 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((1086239268058231 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4441:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_603 : ((((4361755692072487 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4447 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4441 < q → q < 4447 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4447).mp (by decide +kernel))) hgap
  have hprev := thV_602
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4447:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4361755692072487 : ℚ) / 1000000000000) ≤ ((544169463385637 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (4447:ℚ) := by decide +kernel
  have hratR : ((((4361755692072487 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((544169463385637 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4447:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_604 : ((((4370156576138383 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4451 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4447 < q → q < 4451 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4451).mp (by decide +kernel))) hgap
  have hprev := thV_603
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4451:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4370156576138383 : ℚ) / 1000000000000) ≤ ((4361755692072487 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (4451:ℚ) := by decide +kernel
  have hratR : ((((4370156576138383 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4361755692072487 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4451:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_605 : ((((437855880730821 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4457 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4451 < q → q < 4457 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4457).mp (by decide +kernel))) hgap
  have hprev := thV_604
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4457:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((437855880730821 : ℚ) / 100000000000) ≤ ((4370156576138383 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (4457:ℚ) := by decide +kernel
  have hratR : ((((437855880730821 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((4370156576138383 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4457:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_606 : ((((4386962383769719 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4463 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4457 < q → q < 4463 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4463).mp (by decide +kernel))) hgap
  have hprev := thV_605
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4463:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4386962383769719 : ℚ) / 1000000000000) ≤ ((437855880730821 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (4463:ℚ) := by decide +kernel
  have hratR : ((((4386962383769719 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((437855880730821 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4463:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_607 : ((((879073997056277 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4481 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4463 < q → q < 4481 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4481).mp (by decide +kernel))) hgap
  have hprev := thV_606
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4481:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((879073997056277 : ℚ) / 200000000000) ≤ ((4386962383769719 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (4481:ℚ) := by decide +kernel
  have hratR : ((((879073997056277 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((4386962383769719 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4481:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_608 : ((((4403778033022421 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4483 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4481 < q → q < 4483 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4483).mp (by decide +kernel))) hgap
  have hprev := thV_607
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4483:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4403778033022421 : ℚ) / 1000000000000) ≤ ((879073997056277 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (4483:ℚ) := by decide +kernel
  have hratR : ((((4403778033022421 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((879073997056277 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4483:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_609 : ((((4412188308928371 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4493 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4483 < q → q < 4493 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4493).mp (by decide +kernel))) hgap
  have hprev := thV_608
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4493:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4412188308928371 : ℚ) / 1000000000000) ≤ ((4403778033022421 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (4493:ℚ) := by decide +kernel
  have hratR : ((((4412188308928371 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4403778033022421 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4493:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_610 : ((((2210300847973971 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4507 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4493 < q → q < 4507 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4507).mp (by decide +kernel))) hgap
  have hprev := thV_609
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4507:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2210300847973971 : ℚ) / 500000000000) ≤ ((4412188308928371 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (4507:ℚ) := by decide +kernel
  have hratR : ((((2210300847973971 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((4412188308928371 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4507:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_611 : ((((4429016413344649 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4513 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4507 < q → q < 4513 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4513).mp (by decide +kernel))) hgap
  have hprev := thV_610
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4513:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4429016413344649 : ℚ) / 1000000000000) ≤ ((2210300847973971 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (4513:ℚ) := by decide +kernel
  have hratR : ((((4429016413344649 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2210300847973971 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4513:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_612 : ((((69334875260581 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4517 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4513 < q → q < 4517 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4517).mp (by decide +kernel))) hgap
  have hprev := thV_611
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4517:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((69334875260581 : ℚ) / 15625000000) ≤ ((4429016413344649 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (4517:ℚ) := by decide +kernel
  have hratR : ((((69334875260581 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ ((((4429016413344649 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4517:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_613 : ((((177833922507339 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4519 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4517 < q → q < 4519 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4519).mp (by decide +kernel))) hgap
  have hprev := thV_612
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4519:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((177833922507339 : ℚ) / 40000000000) ≤ ((69334875260581 : ℚ) / 15625000000) + Work.RHContract.RegionI.logLowQ (4519:ℚ) := by decide +kernel
  have hratR : ((((177833922507339 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((69334875260581 : ℚ) / 15625000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4519:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_614 : ((((4454264993449833 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4523 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4519 < q → q < 4523 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4523).mp (by decide +kernel))) hgap
  have hprev := thV_613
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4523:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4454264993449833 : ℚ) / 1000000000000) ≤ ((177833922507339 : ℚ) / 40000000000) + Work.RHContract.RegionI.logLowQ (4523:ℚ) := by decide +kernel
  have hratR : ((((4454264993449833 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((177833922507339 : ℚ) / 40000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4523:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_615 : ((((2231343608200269 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4547 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4523 < q → q < 4547 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4547).mp (by decide +kernel))) hgap
  have hprev := thV_614
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4547:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2231343608200269 : ℚ) / 500000000000) ≤ ((4454264993449833 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (4547:ℚ) := by decide +kernel
  have hratR : ((((2231343608200269 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((4454264993449833 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4547:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_616 : ((((1117777469776247 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4549 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4547 < q → q < 4549 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4549).mp (by decide +kernel))) hgap
  have hprev := thV_615
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4549:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1117777469776247 : ℚ) / 250000000000) ≤ ((2231343608200269 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (4549:ℚ) := by decide +kernel
  have hratR : ((((1117777469776247 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((2231343608200269 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4549:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_617 : ((((223976758813929 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4561 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4549 < q → q < 4561 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4561).mp (by decide +kernel))) hgap
  have hprev := thV_616
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4561:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((223976758813929 : ℚ) / 50000000000) ≤ ((1117777469776247 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (4561:ℚ) := by decide +kernel
  have hratR : ((((223976758813929 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((1117777469776247 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4561:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_618 : ((((897592357617729 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4567 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4561 < q → q < 4567 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4567).mp (by decide +kernel))) hgap
  have hprev := thV_617
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4567:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((897592357617729 : ℚ) / 200000000000) ≤ ((223976758813929 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (4567:ℚ) := by decide +kernel
  have hratR : ((((897592357617729 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((223976758813929 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4567:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_619 : ((((2248195948585017 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4583 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4567 < q → q < 4583 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4583).mp (by decide +kernel))) hgap
  have hprev := thV_618
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4583:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2248195948585017 : ℚ) / 500000000000) ≤ ((897592357617729 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (4583:ℚ) := by decide +kernel
  have hratR : ((((2248195948585017 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((897592357617729 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4583:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_620 : ((((4504823750311163 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4591 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4583 < q → q < 4591 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4591).mp (by decide +kernel))) hgap
  have hprev := thV_619
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4591:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4504823750311163 : ℚ) / 1000000000000) ≤ ((2248195948585017 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (4591:ℚ) := by decide +kernel
  have hratR : ((((4504823750311163 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2248195948585017 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4591:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_621 : ((((4513256909503849 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4597 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4591 < q → q < 4597 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4597).mp (by decide +kernel))) hgap
  have hprev := thV_620
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4597:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4513256909503849 : ℚ) / 1000000000000) ≤ ((4504823750311163 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (4597:ℚ) := by decide +kernel
  have hratR : ((((4513256909503849 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4504823750311163 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4597:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_622 : ((((2260845686522273 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4603 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4597 < q → q < 4603 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4603).mp (by decide +kernel))) hgap
  have hprev := thV_621
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4603:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2260845686522273 : ℚ) / 500000000000) ≤ ((4513256909503849 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (4603:ℚ) := by decide +kernel
  have hratR : ((((2260845686522273 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((4513256909503849 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4603:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_623 : ((((566266217431537 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4621 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4603 < q → q < 4621 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4621).mp (by decide +kernel))) hgap
  have hprev := thV_622
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4621:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((566266217431537 : ℚ) / 125000000000) ≤ ((2260845686522273 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (4621:ℚ) := by decide +kernel
  have hratR : ((((566266217431537 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((2260845686522273 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4621:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_624 : ((((35457590330731 : ℚ) / 7812500000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4637 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4621 < q → q < 4637 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4637).mp (by decide +kernel))) hgap
  have hprev := thV_623
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4637:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((35457590330731 : ℚ) / 7812500000) ≤ ((566266217431537 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (4637:ℚ) := by decide +kernel
  have hratR : ((((35457590330731 : ℚ) / 7812500000) : ℚ) : ℝ) ≤ ((((566266217431537 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4637:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_625 : ((((355235454409 : ℚ) / 78125000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4639 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4637 < q → q < 4639 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4639).mp (by decide +kernel))) hgap
  have hprev := thV_624
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4639:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((355235454409 : ℚ) / 78125000) ≤ ((35457590330731 : ℚ) / 7812500000) + Work.RHContract.RegionI.logLowQ (4639:ℚ) := by decide +kernel
  have hratR : ((((355235454409 : ℚ) / 78125000) : ℚ) : ℝ) ≤ ((((35457590330731 : ℚ) / 7812500000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4639:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_626 : ((((45554569324201 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4643 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4639 < q → q < 4643 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4643).mp (by decide +kernel))) hgap
  have hprev := thV_625
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4643:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((45554569324201 : ℚ) / 10000000000) ≤ ((355235454409 : ℚ) / 78125000) + Work.RHContract.RegionI.logLowQ (4643:ℚ) := by decide +kernel
  have hratR : ((((45554569324201 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ ((((355235454409 : ℚ) / 78125000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4643:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_627 : ((((4563901339838671 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4649 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4643 < q → q < 4649 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4649).mp (by decide +kernel))) hgap
  have hprev := thV_626
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4649:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4563901339838671 : ℚ) / 1000000000000) ≤ ((45554569324201 : ℚ) / 10000000000) + Work.RHContract.RegionI.logLowQ (4649:ℚ) := by decide +kernel
  have hratR : ((((4563901339838671 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((45554569324201 : ℚ) / 10000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4649:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_628 : ((((182893847094591 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4651 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4649 < q → q < 4651 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4651).mp (by decide +kernel))) hgap
  have hprev := thV_627
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4651:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((182893847094591 : ℚ) / 40000000000) ≤ ((4563901339838671 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (4651:ℚ) := by decide +kernel
  have hratR : ((((182893847094591 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((4563901339838671 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4651:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_629 : ((((2290396152052319 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4657 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4651 < q → q < 4657 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4657).mp (by decide +kernel))) hgap
  have hprev := thV_628
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4657:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2290396152052319 : ℚ) / 500000000000) ≤ ((182893847094591 : ℚ) / 40000000000) + Work.RHContract.RegionI.logLowQ (4657:ℚ) := by decide +kernel
  have hratR : ((((2290396152052319 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((182893847094591 : ℚ) / 40000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4657:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_630 : ((((2294619859199163 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4663 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4657 < q → q < 4663 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4663).mp (by decide +kernel))) hgap
  have hprev := thV_629
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4663:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2294619859199163 : ℚ) / 500000000000) ≤ ((2290396152052319 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (4663:ℚ) := by decide +kernel
  have hratR : ((((2294619859199163 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((2290396152052319 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4663:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_631 : ((((4597689274937907 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4673 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4663 < q → q < 4673 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4673).mp (by decide +kernel))) hgap
  have hprev := thV_630
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4673:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4597689274937907 : ℚ) / 1000000000000) ≤ ((2294619859199163 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (4673:ℚ) := by decide +kernel
  have hratR : ((((4597689274937907 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2294619859199163 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4673:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_632 : ((((4606140114625653 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4679 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4673 < q → q < 4679 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4679).mp (by decide +kernel))) hgap
  have hprev := thV_631
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4679:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4606140114625653 : ℚ) / 1000000000000) ≤ ((4597689274937907 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (4679:ℚ) := by decide +kernel
  have hratR : ((((4606140114625653 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4597689274937907 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4679:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_633 : ((((2307296757840431 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4691 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4679 < q → q < 4691 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4691).mp (by decide +kernel))) hgap
  have hprev := thV_632
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4691:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2307296757840431 : ℚ) / 500000000000) ≤ ((4606140114625653 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (4691:ℚ) := by decide +kernel
  have hratR : ((((2307296757840431 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((4606140114625653 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4691:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_634 : ((((4623049471559687 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4703 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4691 < q → q < 4703 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4703).mp (by decide +kernel))) hgap
  have hprev := thV_633
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4703:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4623049471559687 : ℚ) / 1000000000000) ≤ ((2307296757840431 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (4703:ℚ) := by decide +kernel
  have hratR : ((((4623049471559687 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2307296757840431 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4703:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_635 : ((((4631509247477113 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4721 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4703 < q → q < 4721 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4721).mp (by decide +kernel))) hgap
  have hprev := thV_634
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4721:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4631509247477113 : ℚ) / 1000000000000) ≤ ((4623049471559687 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (4721:ℚ) := by decide +kernel
  have hratR : ((((4631509247477113 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4623049471559687 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4721:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_636 : ((((4639969446943889 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4723 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4721 < q → q < 4723 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4723).mp (by decide +kernel))) hgap
  have hprev := thV_635
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4723:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4639969446943889 : ℚ) / 1000000000000) ≤ ((4631509247477113 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (4723:ℚ) := by decide +kernel
  have hratR : ((((4639969446943889 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4631509247477113 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4723:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_637 : ((((4648430915983413 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4729 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4723 < q → q < 4729 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4729).mp (by decide +kernel))) hgap
  have hprev := thV_636
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4729:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4648430915983413 : ℚ) / 1000000000000) ≤ ((4639969446943889 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (4729:ℚ) := by decide +kernel
  have hratR : ((((4648430915983413 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4639969446943889 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4729:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_638 : ((((4656893230510199 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4733 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4729 < q → q < 4733 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4733).mp (by decide +kernel))) hgap
  have hprev := thV_637
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4733:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4656893230510199 : ℚ) / 1000000000000) ≤ ((4648430915983413 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (4733:ℚ) := by decide +kernel
  have hratR : ((((4656893230510199 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4648430915983413 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4733:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_639 : ((((2332679670454133 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4751 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4733 < q → q < 4751 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4751).mp (by decide +kernel))) hgap
  have hprev := thV_638
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4751:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2332679670454133 : ℚ) / 500000000000) ≤ ((4656893230510199 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (4751:ℚ) := by decide +kernel
  have hratR : ((((2332679670454133 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((4656893230510199 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4751:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_640 : ((((4673827133746267 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4759 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4751 < q → q < 4759 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4759).mp (by decide +kernel))) hgap
  have hprev := thV_639
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4759:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4673827133746267 : ℚ) / 1000000000000) ≤ ((2332679670454133 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (4759:ℚ) := by decide +kernel
  have hratR : ((((4673827133746267 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2332679670454133 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4759:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_641 : ((((4682299956986827 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4783 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4759 < q → q < 4783 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4783).mp (by decide +kernel))) hgap
  have hprev := thV_640
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4783:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4682299956986827 : ℚ) / 1000000000000) ≤ ((4673827133746267 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (4783:ℚ) := by decide +kernel
  have hratR : ((((4682299956986827 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4673827133746267 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4783:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_642 : ((((46907736161731 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4787 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4783 < q → q < 4787 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4787).mp (by decide +kernel))) hgap
  have hprev := thV_641
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4787:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((46907736161731 : ℚ) / 10000000000) ≤ ((4682299956986827 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (4787:ℚ) := by decide +kernel
  have hratR : ((((46907736161731 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ ((((4682299956986827 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4787:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_643 : ((((4699247693070323 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4789 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4787 < q → q < 4789 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4789).mp (by decide +kernel))) hgap
  have hprev := thV_642
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4789:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4699247693070323 : ℚ) / 1000000000000) ≤ ((46907736161731 : ℚ) / 10000000000) + Work.RHContract.RegionI.logLowQ (4789:ℚ) := by decide +kernel
  have hratR : ((((4699247693070323 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((46907736161731 : ℚ) / 10000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4789:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_644 : ((((4707722604866363 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4793 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4789 < q → q < 4793 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4793).mp (by decide +kernel))) hgap
  have hprev := thV_643
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4793:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4707722604866363 : ℚ) / 1000000000000) ≤ ((4699247693070323 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (4793:ℚ) := by decide +kernel
  have hratR : ((((4707722604866363 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4699247693070323 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4793:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_645 : ((((4716198767705101 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4799 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4793 < q → q < 4799 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4799).mp (by decide +kernel))) hgap
  have hprev := thV_644
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4799:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4716198767705101 : ℚ) / 1000000000000) ≤ ((4707722604866363 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (4799:ℚ) := by decide +kernel
  have hratR : ((((4716198767705101 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4707722604866363 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4799:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_646 : ((((295292209200657 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4801 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4799 < q → q < 4801 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4801).mp (by decide +kernel))) hgap
  have hprev := thV_645
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4801:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((295292209200657 : ℚ) / 62500000000) ≤ ((4716198767705101 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (4801:ℚ) := by decide +kernel
  have hratR : ((((295292209200657 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((4716198767705101 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4801:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_647 : ((((946630884615339 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4813 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4801 < q → q < 4813 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4813).mp (by decide +kernel))) hgap
  have hprev := thV_646
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4813:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((946630884615339 : ℚ) / 200000000000) ≤ ((295292209200657 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (4813:ℚ) := by decide +kernel
  have hratR : ((((946630884615339 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((295292209200657 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4813:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_648 : ((((948326865936041 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4817 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4813 < q → q < 4817 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4817).mp (by decide +kernel))) hgap
  have hprev := thV_647
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4817:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((948326865936041 : ℚ) / 200000000000) ≤ ((946630884615339 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (4817:ℚ) := by decide +kernel
  have hratR : ((((948326865936041 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((946630884615339 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4817:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_649 : ((((118752928461041 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4831 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4817 < q → q < 4831 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4831).mp (by decide +kernel))) hgap
  have hprev := thV_648
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4831:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((118752928461041 : ℚ) / 25000000000) ≤ ((948326865936041 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (4831:ℚ) := by decide +kernel
  have hratR : ((((118752928461041 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((948326865936041 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4831:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_650 : ((((2379303068947783 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4861 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4831 < q → q < 4861 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4861).mp (by decide +kernel))) hgap
  have hprev := thV_649
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4861:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2379303068947783 : ℚ) / 500000000000) ≤ ((118752928461041 : ℚ) / 25000000000) + Work.RHContract.RegionI.logLowQ (4861:ℚ) := by decide +kernel
  have hratR : ((((2379303068947783 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((118752928461041 : ℚ) / 25000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4861:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_651 : ((((4767097192426253 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4871 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4861 < q → q < 4871 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4871).mp (by decide +kernel))) hgap
  have hprev := thV_650
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4871:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4767097192426253 : ℚ) / 1000000000000) ≤ ((2379303068947783 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (4871:ℚ) := by decide +kernel
  have hratR : ((((4767097192426253 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2379303068947783 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4871:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_652 : ((((4775589477978843 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4877 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4871 < q → q < 4877 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4877).mp (by decide +kernel))) hgap
  have hprev := thV_651
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4877:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4775589477978843 : ℚ) / 1000000000000) ≤ ((4767097192426253 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (4877:ℚ) := by decide +kernel
  have hratR : ((((4775589477978843 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4767097192426253 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4877:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_653 : ((((2392042110519151 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4889 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4877 < q → q < 4889 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4889).mp (by decide +kernel))) hgap
  have hprev := thV_652
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4889:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2392042110519151 : ℚ) / 500000000000) ≤ ((4775589477978843 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (4889:ℚ) := by decide +kernel
  have hratR : ((((2392042110519151 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((4775589477978843 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4889:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_654 : ((((4792581823576833 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4903 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4889 < q → q < 4903 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4903).mp (by decide +kernel))) hgap
  have hprev := thV_653
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4903:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4792581823576833 : ℚ) / 1000000000000) ≤ ((2392042110519151 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (4903:ℚ) := by decide +kernel
  have hratR : ((((4792581823576833 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2392042110519151 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4903:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_655 : ((((4801080649107771 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4909 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4903 < q → q < 4909 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4909).mp (by decide +kernel))) hgap
  have hprev := thV_654
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4909:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4801080649107771 : ℚ) / 1000000000000) ≤ ((4792581823576833 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (4909:ℚ) := by decide +kernel
  have hratR : ((((4801080649107771 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4792581823576833 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4909:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_656 : ((((2404790754820723 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4919 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4909 < q → q < 4919 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4919).mp (by decide +kernel))) hgap
  have hprev := thV_655
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4919:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2404790754820723 : ℚ) / 500000000000) ≤ ((4801080649107771 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (4919:ℚ) := by decide +kernel
  have hratR : ((((2404790754820723 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((4801080649107771 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4919:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_657 : ((((96361696134491 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4931 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4919 < q → q < 4931 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4931).mp (by decide +kernel))) hgap
  have hprev := thV_656
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4931:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((96361696134491 : ℚ) / 20000000000) ≤ ((2404790754820723 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (4931:ℚ) := by decide +kernel
  have hratR : ((((96361696134491 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ ((((2404790754820723 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4931:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_658 : ((((603323563665333 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4933 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4931 < q → q < 4933 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4933).mp (by decide +kernel))) hgap
  have hprev := thV_657
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4933:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((603323563665333 : ℚ) / 125000000000) ≤ ((96361696134491 : ℚ) / 20000000000) + Work.RHContract.RegionI.logLowQ (4933:ℚ) := by decide +kernel
  have hratR : ((((603323563665333 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((96361696134491 : ℚ) / 20000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4933:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_659 : ((((4835093022457803 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4937 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4933 < q → q < 4937 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4937).mp (by decide +kernel))) hgap
  have hprev := thV_658
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4937:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4835093022457803 : ℚ) / 1000000000000) ≤ ((603323563665333 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (4937:ℚ) := by decide +kernel
  have hratR : ((((4835093022457803 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((603323563665333 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4937:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_660 : ((((484359875016799 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4943 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4937 < q → q < 4943 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4943).mp (by decide +kernel))) hgap
  have hprev := thV_659
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4943:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((484359875016799 : ℚ) / 100000000000) ≤ ((4835093022457803 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (4943:ℚ) := by decide +kernel
  have hratR : ((((484359875016799 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((4835093022457803 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4943:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_661 : ((((606513261877529 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4951 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4943 < q → q < 4951 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4951).mp (by decide +kernel))) hgap
  have hprev := thV_660
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4951:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((606513261877529 : ℚ) / 125000000000) ≤ ((484359875016799 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (4951:ℚ) := by decide +kernel
  have hratR : ((((606513261877529 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((484359875016799 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4951:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_662 : ((((4860614651015133 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4957 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4951 < q → q < 4957 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4957).mp (by decide +kernel))) hgap
  have hprev := thV_661
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4957:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4860614651015133 : ℚ) / 1000000000000) ≤ ((606513261877529 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (4957:ℚ) := by decide +kernel
  have hratR : ((((4860614651015133 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((606513261877529 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4957:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_663 : ((((4869125222327121 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4967 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4957 < q → q < 4967 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4967).mp (by decide +kernel))) hgap
  have hprev := thV_662
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4967:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4869125222327121 : ℚ) / 1000000000000) ≤ ((4860614651015133 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (4967:ℚ) := by decide +kernel
  have hratR : ((((4869125222327121 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4860614651015133 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4967:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_664 : ((((4877636196215603 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4969 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4967 < q → q < 4969 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4969).mp (by decide +kernel))) hgap
  have hprev := thV_663
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4969:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4877636196215603 : ℚ) / 1000000000000) ≤ ((4869125222327121 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (4969:ℚ) := by decide +kernel
  have hratR : ((((4877636196215603 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4869125222327121 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4969:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_665 : ((((2443073987385599 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4973 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4969 < q → q < 4973 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4973).mp (by decide +kernel))) hgap
  have hprev := thV_664
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4973:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2443073987385599 : ℚ) / 500000000000) ≤ ((4877636196215603 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (4973:ℚ) := by decide +kernel
  have hratR : ((((2443073987385599 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((4877636196215603 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4973:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_666 : ((((611832820571703 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4987 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4973 < q → q < 4987 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4987).mp (by decide +kernel))) hgap
  have hprev := thV_665
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4987:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((611832820571703 : ℚ) / 125000000000) ≤ ((2443073987385599 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (4987:ℚ) := by decide +kernel
  have hratR : ((((611832820571703 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((2443073987385599 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4987:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_667 : ((((980635671356201 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4993 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4987 < q → q < 4993 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4993).mp (by decide +kernel))) hgap
  have hprev := thV_666
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4993:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((980635671356201 : ℚ) / 200000000000) ≤ ((611832820571703 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (4993:ℚ) := by decide +kernel
  have hratR : ((((980635671356201 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((611832820571703 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4993:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_668 : ((((4911695349949299 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((4999 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4993 < q → q < 4999 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4999).mp (by decide +kernel))) hgap
  have hprev := thV_667
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (4999:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4911695349949299 : ℚ) / 1000000000000) ≤ ((980635671356201 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (4999:ℚ) := by decide +kernel
  have hratR : ((((4911695349949299 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((980635671356201 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (4999:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_669 : ((((4920213142957667 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5003 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 4999 < q → q < 5003 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5003).mp (by decide +kernel))) hgap
  have hprev := thV_668
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5003:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4920213142957667 : ℚ) / 1000000000000) ≤ ((4911695349949299 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (5003:ℚ) := by decide +kernel
  have hratR : ((((4920213142957667 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4911695349949299 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5003:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_670 : ((((985746426905581 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5009 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5003 < q → q < 5009 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5009).mp (by decide +kernel))) hgap
  have hprev := thV_669
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5009:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((985746426905581 : ℚ) / 200000000000) ≤ ((4920213142957667 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (5009:ℚ) := by decide +kernel
  have hratR : ((((985746426905581 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((4920213142957667 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5009:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_671 : ((((987450305059949 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5011 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5009 < q → q < 5011 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5011).mp (by decide +kernel))) hgap
  have hprev := thV_670
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5011:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((987450305059949 : ℚ) / 200000000000) ≤ ((985746426905581 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (5011:ℚ) := by decide +kernel
  have hratR : ((((987450305059949 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((985746426905581 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5011:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_672 : ((((247288645484633 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5021 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5011 < q → q < 5021 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5021).mp (by decide +kernel))) hgap
  have hprev := thV_671
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5021:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((247288645484633 : ℚ) / 50000000000) ≤ ((987450305059949 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (5021:ℚ) := by decide +kernel
  have hratR : ((((247288645484633 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((987450305059949 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5021:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_673 : ((((495429469233329 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5023 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5021 < q → q < 5023 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5023).mp (by decide +kernel))) hgap
  have hprev := thV_672
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5023:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((495429469233329 : ℚ) / 100000000000) ≤ ((247288645484633 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (5023:ℚ) := by decide +kernel
  have hratR : ((((495429469233329 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((247288645484633 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5023:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_674 : ((((4962819655258851 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5039 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5023 < q → q < 5039 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5039).mp (by decide +kernel))) hgap
  have hprev := thV_673
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5039:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4962819655258851 : ℚ) / 1000000000000) ≤ ((495429469233329 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (5039:ℚ) := by decide +kernel
  have hratR : ((((4962819655258851 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((495429469233329 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5039:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_675 : ((((4971346996778199 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5051 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5039 < q → q < 5051 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5051).mp (by decide +kernel))) hgap
  have hprev := thV_674
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5051:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4971346996778199 : ℚ) / 1000000000000) ≤ ((4962819655258851 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (5051:ℚ) := by decide +kernel
  have hratR : ((((4971346996778199 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4962819655258851 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5051:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_676 : ((((4979875920889371 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5059 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5051 < q → q < 5059 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5059).mp (by decide +kernel))) hgap
  have hprev := thV_675
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5059:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4979875920889371 : ℚ) / 1000000000000) ≤ ((4971346996778199 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (5059:ℚ) := by decide +kernel
  have hratR : ((((4979875920889371 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4971346996778199 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5059:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_677 : ((((4988408396701199 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5077 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5059 < q → q < 5077 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5077).mp (by decide +kernel))) hgap
  have hprev := thV_676
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5077:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4988408396701199 : ℚ) / 1000000000000) ≤ ((4979875920889371 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (5077:ℚ) := by decide +kernel
  have hratR : ((((4988408396701199 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4979875920889371 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5077:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_678 : ((((4996941660069673 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5081 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5077 < q → q < 5081 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5081).mp (by decide +kernel))) hgap
  have hprev := thV_677
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5081:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4996941660069673 : ℚ) / 1000000000000) ≤ ((4988408396701199 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (5081:ℚ) := by decide +kernel
  have hratR : ((((4996941660069673 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4988408396701199 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5081:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_679 : ((((312842256475711 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5087 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5081 < q → q < 5087 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5087).mp (by decide +kernel))) hgap
  have hprev := thV_678
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5087:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((312842256475711 : ℚ) / 62500000000) ≤ ((4996941660069673 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (5087:ℚ) := by decide +kernel
  have hratR : ((((312842256475711 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((4996941660069673 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5087:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_680 : ((((5014012903329311 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5099 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5087 < q → q < 5099 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5099).mp (by decide +kernel))) hgap
  have hprev := thV_679
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5099:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5014012903329311 : ℚ) / 1000000000000) ≤ ((312842256475711 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (5099:ℚ) := by decide +kernel
  have hratR : ((((5014012903329311 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((312842256475711 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5099:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_681 : ((((2511275047602057 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5101 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5099 < q → q < 5101 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5101).mp (by decide +kernel))) hgap
  have hprev := thV_680
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5101:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2511275047602057 : ℚ) / 500000000000) ≤ ((5014012903329311 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (5101:ℚ) := by decide +kernel
  have hratR : ((((2511275047602057 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((5014012903329311 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5101:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_682 : ((((2515544231313821 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5107 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5101 < q → q < 5107 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5107).mp (by decide +kernel))) hgap
  have hprev := thV_681
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5107:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2515544231313821 : ℚ) / 500000000000) ≤ ((2511275047602057 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (5107:ℚ) := by decide +kernel
  have hratR : ((((2515544231313821 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((2511275047602057 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5107:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_683 : ((((2519814002109801 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5113 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5107 < q → q < 5113 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5113).mp (by decide +kernel))) hgap
  have hprev := thV_682
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5113:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2519814002109801 : ℚ) / 500000000000) ≤ ((2515544231313821 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (5113:ℚ) := by decide +kernel
  have hratR : ((((2519814002109801 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((2515544231313821 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5113:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_684 : ((((252408435930147 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5119 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5113 < q → q < 5119 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5119).mp (by decide +kernel))) hgap
  have hprev := thV_683
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5119:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((252408435930147 : ℚ) / 50000000000) ≤ ((2519814002109801 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (5119:ℚ) := by decide +kernel
  have hratR : ((((252408435930147 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((2519814002109801 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5119:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_685 : ((((5056714887899473 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5147 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5119 < q → q < 5147 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5147).mp (by decide +kernel))) hgap
  have hprev := thV_684
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5147:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5056714887899473 : ℚ) / 1000000000000) ≤ ((252408435930147 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (5147:ℚ) := by decide +kernel
  have hratR : ((((5056714887899473 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((252408435930147 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5147:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_686 : ((((5065262222244681 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5153 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5147 < q → q < 5153 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5153).mp (by decide +kernel))) hgap
  have hprev := thV_685
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5153:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5065262222244681 : ℚ) / 1000000000000) ≤ ((5056714887899473 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (5153:ℚ) := by decide +kernel
  have hratR : ((((5065262222244681 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5056714887899473 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5153:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_687 : ((((634226533721231 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5167 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5153 < q → q < 5167 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5167).mp (by decide +kernel))) hgap
  have hprev := thV_686
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5167:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((634226533721231 : ℚ) / 125000000000) ≤ ((5065262222244681 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (5167:ℚ) := by decide +kernel
  have hratR : ((((634226533721231 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((5065262222244681 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5167:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_688 : ((((1270590772784781 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5171 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5167 < q → q < 5171 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5171).mp (by decide +kernel))) hgap
  have hprev := thV_687
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5171:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1270590772784781 : ℚ) / 250000000000) ≤ ((634226533721231 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (5171:ℚ) := by decide +kernel
  have hratR : ((((1270590772784781 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((634226533721231 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5171:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_689 : ((((1272728864600607 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5179 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5171 < q → q < 5179 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5179).mp (by decide +kernel))) hgap
  have hprev := thV_688
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5179:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1272728864600607 : ℚ) / 250000000000) ≤ ((1270590772784781 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (5179:ℚ) := by decide +kernel
  have hratR : ((((1272728864600607 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((1270590772784781 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5179:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_690 : ((((1274867438669669 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5189 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5179 < q → q < 5189 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5189).mp (by decide +kernel))) hgap
  have hprev := thV_689
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5189:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1274867438669669 : ℚ) / 250000000000) ≤ ((1272728864600607 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (5189:ℚ) := by decide +kernel
  have hratR : ((((1274867438669669 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((1272728864600607 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5189:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_691 : ((((1021605118298113 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5197 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5189 < q → q < 5197 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5197).mp (by decide +kernel))) hgap
  have hprev := thV_690
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5197:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1021605118298113 : ℚ) / 200000000000) ≤ ((1274867438669669 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (5197:ℚ) := by decide +kernel
  have hratR : ((((1021605118298113 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((1274867438669669 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5197:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_692 : ((((511658373466519 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5209 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5197 < q → q < 5209 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5209).mp (by decide +kernel))) hgap
  have hprev := thV_691
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5209:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((511658373466519 : ℚ) / 100000000000) ≤ ((1021605118298113 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (5209:ℚ) := by decide +kernel
  have hratR : ((((511658373466519 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((1021605118298113 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5209:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_693 : ((((5125145327440783 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5227 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5209 < q → q < 5227 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5227).mp (by decide +kernel))) hgap
  have hprev := thV_692
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5227:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5125145327440783 : ℚ) / 1000000000000) ≤ ((511658373466519 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (5227:ℚ) := by decide +kernel
  have hratR : ((((5125145327440783 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((511658373466519 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5227:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_694 : ((((2566853842590517 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5231 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5227 < q → q < 5231 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5231).mp (by decide +kernel))) hgap
  have hprev := thV_693
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5231:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2566853842590517 : ℚ) / 500000000000) ≤ ((5125145327440783 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (5231:ℚ) := by decide +kernel
  have hratR : ((((2566853842590517 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((5125145327440783 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5231:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_695 : ((((2571135212592143 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5233 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5231 < q → q < 5233 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5233).mp (by decide +kernel))) hgap
  have hprev := thV_694
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5233:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2571135212592143 : ℚ) / 500000000000) ≤ ((2566853842590517 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (5233:ℚ) := by decide +kernel
  have hratR : ((((2571135212592143 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((2566853842590517 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5233:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_696 : ((((2575416964637723 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5237 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5233 < q → q < 5237 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5237).mp (by decide +kernel))) hgap
  have hprev := thV_695
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5237:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2575416964637723 : ℚ) / 500000000000) ≤ ((2571135212592143 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (5237:ℚ) := by decide +kernel
  have hratR : ((((2575416964637723 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((2571135212592143 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5237:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_697 : ((((5159402005674057 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5261 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5237 < q → q < 5261 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5261).mp (by decide +kernel))) hgap
  have hprev := thV_696
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5261:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5159402005674057 : ℚ) / 1000000000000) ≤ ((2575416964637723 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (5261:ℚ) := by decide +kernel
  have hratR : ((((5159402005674057 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2575416964637723 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5261:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_698 : ((((1291993090102617 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5273 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5261 < q → q < 5273 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5273).mp (by decide +kernel))) hgap
  have hprev := thV_697
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5273:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1291993090102617 : ℚ) / 250000000000) ≤ ((5159402005674057 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (5273:ℚ) := by decide +kernel
  have hratR : ((((1291993090102617 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((5159402005674057 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5273:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_699 : ((((1294135963093043 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5279 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5273 < q → q < 5279 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5279).mp (by decide +kernel))) hgap
  have hprev := thV_698
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5279:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1294135963093043 : ℚ) / 250000000000) ≤ ((1291993090102617 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (5279:ℚ) := by decide +kernel
  have hratR : ((((1294135963093043 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((1291993090102617 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5279:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_700 : ((((5185115723121759 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5281 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5279 < q → q < 5281 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5281).mp (by decide +kernel))) hgap
  have hprev := thV_699
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5281:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5185115723121759 : ℚ) / 1000000000000) ≤ ((1294135963093043 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (5281:ℚ) := by decide +kernel
  have hratR : ((((5185115723121759 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1294135963093043 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5281:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_701 : ((((649211327377523 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5297 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5281 < q → q < 5297 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5297).mp (by decide +kernel))) hgap
  have hprev := thV_700
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5297:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((649211327377523 : ℚ) / 125000000000) ≤ ((5185115723121759 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (5297:ℚ) := by decide +kernel
  have hratR : ((((649211327377523 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((5185115723121759 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5297:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_702 : ((((5202266646994201 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5303 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5297 < q → q < 5303 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5303).mp (by decide +kernel))) hgap
  have hprev := thV_701
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5303:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5202266646994201 : ℚ) / 1000000000000) ≤ ((649211327377523 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (5303:ℚ) := by decide +kernel
  have hratR : ((((5202266646994201 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((649211327377523 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5303:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_703 : ((((1042168761152733 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5309 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5303 < q → q < 5309 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5309).mp (by decide +kernel))) hgap
  have hprev := thV_702
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5309:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1042168761152733 : ℚ) / 200000000000) ≤ ((5202266646994201 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (5309:ℚ) := by decide +kernel
  have hratR : ((((1042168761152733 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((5202266646994201 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5309:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_704 : ((((2609711799046859 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5323 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5309 < q → q < 5323 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5323).mp (by decide +kernel))) hgap
  have hprev := thV_703
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5323:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2609711799046859 : ℚ) / 500000000000) ≤ ((1042168761152733 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (5323:ℚ) := by decide +kernel
  have hratR : ((((2609711799046859 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1042168761152733 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5323:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_705 : ((((5228005267301199 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5333 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5323 < q → q < 5333 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5333).mp (by decide +kernel))) hgap
  have hprev := thV_704
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5333:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5228005267301199 : ℚ) / 1000000000000) ≤ ((2609711799046859 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (5333:ℚ) := by decide +kernel
  have hratR : ((((5228005267301199 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2609711799046859 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5333:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_706 : ((((1309147389558257 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5347 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5333 < q → q < 5347 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5347).mp (by decide +kernel))) hgap
  have hprev := thV_705
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5347:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1309147389558257 : ℚ) / 250000000000) ≤ ((5228005267301199 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (5347:ℚ) := by decide +kernel
  have hratR : ((((1309147389558257 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((5228005267301199 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5347:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_707 : ((((5245174596968219 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5351 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5347 < q → q < 5351 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5351).mp (by decide +kernel))) hgap
  have hprev := thV_706
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5351:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5245174596968219 : ℚ) / 1000000000000) ≤ ((1309147389558257 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (5351:ℚ) := by decide +kernel
  have hratR : ((((5245174596968219 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1309147389558257 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5351:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_708 : ((((5253765226474589 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5381 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5351 < q → q < 5381 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5381).mp (by decide +kernel))) hgap
  have hprev := thV_707
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5381:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5253765226474589 : ℚ) / 1000000000000) ≤ ((5245174596968219 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (5381:ℚ) := by decide +kernel
  have hratR : ((((5253765226474589 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5245174596968219 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5381:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_709 : ((((105247139407883 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5387 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5381 < q → q < 5387 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5387).mp (by decide +kernel))) hgap
  have hprev := thV_708
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5387:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((105247139407883 : ℚ) / 20000000000) ≤ ((5253765226474589 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (5387:ℚ) := by decide +kernel
  have hratR : ((((105247139407883 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ ((((5253765226474589 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5387:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_710 : ((((5270949827486367 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5393 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5387 < q → q < 5393 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5393).mp (by decide +kernel))) hgap
  have hprev := thV_709
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5393:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5270949827486367 : ℚ) / 1000000000000) ≤ ((105247139407883 : ℚ) / 20000000000) + Work.RHContract.RegionI.logLowQ (5393:ℚ) := by decide +kernel
  have hratR : ((((5270949827486367 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((105247139407883 : ℚ) / 20000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5393:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_711 : ((((1055908759302693 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5399 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5393 < q → q < 5399 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5399).mp (by decide +kernel))) hgap
  have hprev := thV_710
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5399:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1055908759302693 : ℚ) / 200000000000) ≤ ((5270949827486367 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (5399:ℚ) := by decide +kernel
  have hratR : ((((1055908759302693 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((5270949827486367 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5399:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_712 : ((((5288139246199727 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5407 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5399 < q → q < 5407 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5407).mp (by decide +kernel))) hgap
  have hprev := thV_711
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5407:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5288139246199727 : ℚ) / 1000000000000) ≤ ((1055908759302693 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (5407:ℚ) := by decide +kernel
  have hratR : ((((5288139246199727 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1055908759302693 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5407:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_713 : ((((1324183951235851 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5413 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5407 < q → q < 5413 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5413).mp (by decide +kernel))) hgap
  have hprev := thV_712
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5413:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1324183951235851 : ℚ) / 250000000000) ≤ ((5288139246199727 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (5413:ℚ) := by decide +kernel
  have hratR : ((((1324183951235851 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((5288139246199727 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5413:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_714 : ((((2652666551187971 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5417 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5413 < q → q < 5417 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5417).mp (by decide +kernel))) hgap
  have hprev := thV_713
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5417:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2652666551187971 : ℚ) / 500000000000) ≤ ((1324183951235851 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (5417:ℚ) := by decide +kernel
  have hratR : ((((2652666551187971 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1324183951235851 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5417:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_715 : ((((1328482692237097 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5419 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5417 < q → q < 5419 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5419).mp (by decide +kernel))) hgap
  have hprev := thV_714
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5419:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1328482692237097 : ℚ) / 250000000000) ≤ ((2652666551187971 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (5419:ℚ) := by decide +kernel
  have hratR : ((((1328482692237097 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((2652666551187971 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5419:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_716 : ((((5322530647503303 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5431 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5419 < q → q < 5431 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5431).mp (by decide +kernel))) hgap
  have hprev := thV_715
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5431:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5322530647503303 : ℚ) / 1000000000000) ≤ ((1328482692237097 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (5431:ℚ) := by decide +kernel
  have hratR : ((((5322530647503303 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1328482692237097 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5431:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_717 : ((((5331131630217329 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5437 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5431 < q → q < 5437 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5437).mp (by decide +kernel))) hgap
  have hprev := thV_716
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5437:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5331131630217329 : ℚ) / 1000000000000) ≤ ((5322530647503303 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (5437:ℚ) := by decide +kernel
  have hratR : ((((5331131630217329 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5322530647503303 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5437:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_718 : ((((1067946669672139 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5441 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5437 < q → q < 5441 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5441).mp (by decide +kernel))) hgap
  have hprev := thV_717
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5441:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1067946669672139 : ℚ) / 200000000000) ≤ ((5331131630217329 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (5441:ℚ) := by decide +kernel
  have hratR : ((((1067946669672139 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((5331131630217329 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5441:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_719 : ((((5348335434016009 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5443 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5441 < q → q < 5443 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5443).mp (by decide +kernel))) hgap
  have hprev := thV_718
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5443:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5348335434016009 : ℚ) / 1000000000000) ≤ ((1067946669672139 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (5443:ℚ) := by decide +kernel
  have hratR : ((((5348335434016009 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1067946669672139 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5443:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_720 : ((((167404331918671 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5449 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5443 < q → q < 5449 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5449).mp (by decide +kernel))) hgap
  have hprev := thV_719
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5449:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((167404331918671 : ℚ) / 31250000000) ≤ ((5348335434016009 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (5449:ℚ) := by decide +kernel
  have hratR : ((((167404331918671 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((5348335434016009 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5449:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_721 : ((((167673307440263 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5471 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5449 < q → q < 5471 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5471).mp (by decide +kernel))) hgap
  have hprev := thV_720
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5471:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((167673307440263 : ℚ) / 31250000000) ≤ ((167404331918671 : ℚ) / 31250000000) + Work.RHContract.RegionI.logLowQ (5471:ℚ) := by decide +kernel
  have hratR : ((((167673307440263 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((167404331918671 : ℚ) / 31250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5471:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_722 : ((((16794231721469 : ℚ) / 3125000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5477 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5471 < q → q < 5477 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5477).mp (by decide +kernel))) hgap
  have hprev := thV_721
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5477:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((16794231721469 : ℚ) / 3125000000) ≤ ((167673307440263 : ℚ) / 31250000000) + Work.RHContract.RegionI.logLowQ (5477:ℚ) := by decide +kernel
  have hratR : ((((16794231721469 : ℚ) / 3125000000) : ℚ) : ℝ) ≤ ((((167673307440263 : ℚ) / 31250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5477:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_723 : ((((5382762828748499 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5479 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5477 < q → q < 5479 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5479).mp (by decide +kernel))) hgap
  have hprev := thV_722
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5479:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5382762828748499 : ℚ) / 1000000000000) ≤ ((16794231721469 : ℚ) / 3125000000) + Work.RHContract.RegionI.logLowQ (5479:ℚ) := by decide +kernel
  have hratR : ((((5382762828748499 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((16794231721469 : ℚ) / 3125000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5479:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_724 : ((((5391372236420783 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5483 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5479 < q → q < 5483 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5483).mp (by decide +kernel))) hgap
  have hprev := thV_723
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5483:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5391372236420783 : ℚ) / 1000000000000) ≤ ((5382762828748499 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (5483:ℚ) := by decide +kernel
  have hratR : ((((5391372236420783 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5382762828748499 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5483:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_725 : ((((5399984921590539 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5501 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5483 < q → q < 5501 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5501).mp (by decide +kernel))) hgap
  have hprev := thV_724
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5501:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5399984921590539 : ℚ) / 1000000000000) ≤ ((5391372236420783 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (5501:ℚ) := by decide +kernel
  have hratR : ((((5399984921590539 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5391372236420783 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5501:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_726 : ((((5408597970264479 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5503 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5501 < q → q < 5503 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5503).mp (by decide +kernel))) hgap
  have hprev := thV_725
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5503:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5408597970264479 : ℚ) / 1000000000000) ≤ ((5399984921590539 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (5503:ℚ) := by decide +kernel
  have hratR : ((((5408597970264479 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5399984921590539 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5503:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_727 : ((((2708605872775311 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5507 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5503 < q → q < 5507 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5507).mp (by decide +kernel))) hgap
  have hprev := thV_726
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5507:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2708605872775311 : ℚ) / 500000000000) ≤ ((5408597970264479 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (5507:ℚ) := by decide +kernel
  have hratR : ((((2708605872775311 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((5408597970264479 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5507:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_728 : ((((2712913848755471 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5519 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5507 < q → q < 5519 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5519).mp (by decide +kernel))) hgap
  have hprev := thV_727
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5519:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2712913848755471 : ℚ) / 500000000000) ≤ ((2708605872775311 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (5519:ℚ) := by decide +kernel
  have hratR : ((((2712913848755471 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((2708605872775311 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5519:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_729 : ((((2717222005895053 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5521 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5519 < q → q < 5521 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5521).mp (by decide +kernel))) hgap
  have hprev := thV_728
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5521:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2717222005895053 : ℚ) / 500000000000) ≤ ((2712913848755471 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (5521:ℚ) := by decide +kernel
  have hratR : ((((2717222005895053 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((2712913848755471 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5521:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_730 : ((((5443061412238819 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5527 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5521 < q → q < 5527 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5527).mp (by decide +kernel))) hgap
  have hprev := thV_729
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5527:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5443061412238819 : ℚ) / 1000000000000) ≤ ((2717222005895053 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (5527:ℚ) := by decide +kernel
  have hratR : ((((5443061412238819 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2717222005895053 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5527:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_731 : ((((2725839768072847 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5531 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5527 < q → q < 5531 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5531).mp (by decide +kernel))) hgap
  have hprev := thV_730
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5531:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2725839768072847 : ℚ) / 500000000000) ≤ ((5443061412238819 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (5531:ℚ) := by decide +kernel
  have hratR : ((((2725839768072847 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((5443061412238819 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5531:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_732 : ((((2730151174907927 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5557 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5531 < q → q < 5557 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5557).mp (by decide +kernel))) hgap
  have hprev := thV_731
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5557:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2730151174907927 : ℚ) / 500000000000) ≤ ((2725839768072847 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (5557:ℚ) := by decide +kernel
  have hratR : ((((2730151174907927 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((2725839768072847 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5557:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_733 : ((((5468926242622809 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5563 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5557 < q → q < 5563 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5563).mp (by decide +kernel))) hgap
  have hprev := thV_732
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5563:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5468926242622809 : ℚ) / 1000000000000) ≤ ((2730151174907927 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (5563:ℚ) := by decide +kernel
  have hratR : ((((5468926242622809 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2730151174907927 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5563:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_734 : ((((5477551213403279 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5569 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5563 < q → q < 5569 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5569).mp (by decide +kernel))) hgap
  have hprev := thV_733
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5569:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5477551213403279 : ℚ) / 1000000000000) ≤ ((5468926242622809 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (5569:ℚ) := by decide +kernel
  have hratR : ((((5477551213403279 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5468926242622809 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5569:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_735 : ((((5486176902187729 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5573 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5569 < q → q < 5573 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5573).mp (by decide +kernel))) hgap
  have hprev := thV_734
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5573:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5486176902187729 : ℚ) / 1000000000000) ≤ ((5477551213403279 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (5573:ℚ) := by decide +kernel
  have hratR : ((((5486176902187729 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5477551213403279 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5573:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_736 : ((((2747402012717699 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5581 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5573 < q → q < 5581 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5581).mp (by decide +kernel))) hgap
  have hprev := thV_735
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5581:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2747402012717699 : ℚ) / 500000000000) ≤ ((5486176902187729 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (5581:ℚ) := by decide +kernel
  have hratR : ((((2747402012717699 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((5486176902187729 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5581:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_737 : ((((1100686587774661 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5591 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5581 < q → q < 5591 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5591).mp (by decide +kernel))) hgap
  have hprev := thV_736
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5591:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1100686587774661 : ℚ) / 200000000000) ≤ ((2747402012717699 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (5591:ℚ) := by decide +kernel
  have hratR : ((((1100686587774661 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((2747402012717699 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5591:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_738 : ((((5512067559478477 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5623 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5591 < q → q < 5623 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5623).mp (by decide +kernel))) hgap
  have hprev := thV_737
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5623:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5512067559478477 : ℚ) / 1000000000000) ≤ ((1100686587774661 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (5623:ℚ) := by decide +kernel
  have hratR : ((((5512067559478477 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1100686587774661 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5623:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_739 : ((((1380176255374791 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5639 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5623 < q → q < 5639 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5639).mp (by decide +kernel))) hgap
  have hprev := thV_738
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5639:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1380176255374791 : ℚ) / 250000000000) ≤ ((5512067559478477 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (5639:ℚ) := by decide +kernel
  have hratR : ((((1380176255374791 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((5512067559478477 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5639:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_740 : ((((691167854766223 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5641 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5639 < q → q < 5641 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5641).mp (by decide +kernel))) hgap
  have hprev := thV_739
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5641:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((691167854766223 : ℚ) / 125000000000) ≤ ((1380176255374791 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (5641:ℚ) := by decide +kernel
  have hratR : ((((691167854766223 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((1380176255374791 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5641:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_741 : ((((5537981717836337 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5647 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5641 < q → q < 5647 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5647).mp (by decide +kernel))) hgap
  have hprev := thV_740
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5647:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5537981717836337 : ℚ) / 1000000000000) ≤ ((691167854766223 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (5647:ℚ) := by decide +kernel
  have hratR : ((((5537981717836337 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((691167854766223 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5647:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_742 : ((((5546621305632847 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5651 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5647 < q → q < 5651 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5651).mp (by decide +kernel))) hgap
  have hprev := thV_741
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5651:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5546621305632847 : ℚ) / 1000000000000) ≤ ((5537981717836337 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (5651:ℚ) := by decide +kernel
  have hratR : ((((5546621305632847 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5537981717836337 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5651:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_743 : ((((2777630623643201 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5653 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5651 < q → q < 5653 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5653).mp (by decide +kernel))) hgap
  have hprev := thV_742
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5653:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2777630623643201 : ℚ) / 500000000000) ≤ ((5546621305632847 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (5653:ℚ) := by decide +kernel
  have hratR : ((((2777630623643201 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((5546621305632847 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5653:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_744 : ((((44511215170229 : ℚ) / 8000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5657 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5653 < q → q < 5657 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5657).mp (by decide +kernel))) hgap
  have hprev := thV_743
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5657:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((44511215170229 : ℚ) / 8000000000) ≤ ((2777630623643201 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (5657:ℚ) := by decide +kernel
  have hratR : ((((44511215170229 : ℚ) / 8000000000) : ℚ) : ℝ) ≤ ((((2777630623643201 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5657:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_745 : ((((696567862344081 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5659 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5657 < q → q < 5659 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5659).mp (by decide +kernel))) hgap
  have hprev := thV_744
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5659:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((696567862344081 : ℚ) / 125000000000) ≤ ((44511215170229 : ℚ) / 8000000000) + Work.RHContract.RegionI.logLowQ (5659:ℚ) := by decide +kernel
  have hratR : ((((696567862344081 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((44511215170229 : ℚ) / 8000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5659:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_746 : ((((1395296416690963 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5669 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5659 < q → q < 5669 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5669).mp (by decide +kernel))) hgap
  have hprev := thV_745
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5669:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1395296416690963 : ℚ) / 250000000000) ≤ ((696567862344081 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (5669:ℚ) := by decide +kernel
  have hratR : ((((1395296416690963 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((696567862344081 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5669:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_747 : ((((5589830901302029 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5683 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5669 < q → q < 5683 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5683).mp (by decide +kernel))) hgap
  have hprev := thV_746
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5683:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5589830901302029 : ℚ) / 1000000000000) ≤ ((1395296416690963 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (5683:ℚ) := by decide +kernel
  have hratR : ((((5589830901302029 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1395296416690963 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5683:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_748 : ((((279923859553183 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5689 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5683 < q → q < 5689 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5689).mp (by decide +kernel))) hgap
  have hprev := thV_747
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5689:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((279923859553183 : ℚ) / 50000000000) ≤ ((5589830901302029 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (5689:ℚ) := by decide +kernel
  have hratR : ((((279923859553183 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((5589830901302029 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5689:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_749 : ((((5607124183689491 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5693 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5689 < q → q < 5693 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5693).mp (by decide +kernel))) hgap
  have hprev := thV_748
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5693:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5607124183689491 : ℚ) / 1000000000000) ≤ ((279923859553183 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (5693:ℚ) := by decide +kernel
  have hratR : ((((5607124183689491 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((279923859553183 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5693:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_750 : ((((5615772580563403 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5701 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5693 < q → q < 5701 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5701).mp (by decide +kernel))) hgap
  have hprev := thV_749
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5701:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5615772580563403 : ℚ) / 1000000000000) ≤ ((5607124183689491 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (5701:ℚ) := by decide +kernel
  have hratR : ((((5615772580563403 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5607124183689491 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5701:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_751 : ((((1406105682494737 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5711 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5701 < q → q < 5711 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5711).mp (by decide +kernel))) hgap
  have hprev := thV_750
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5711:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1406105682494737 : ℚ) / 250000000000) ≤ ((5615772580563403 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (5711:ℚ) := by decide +kernel
  have hratR : ((((1406105682494737 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((5615772580563403 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5711:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_752 : ((((1408268482361773 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5717 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5711 < q → q < 5717 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5717).mp (by decide +kernel))) hgap
  have hprev := thV_751
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5717:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1408268482361773 : ℚ) / 250000000000) ≤ ((1406105682494737 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (5717:ℚ) := by decide +kernel
  have hratR : ((((1408268482361773 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((1406105682494737 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5717:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_753 : ((((2820864310574287 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5737 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5717 < q → q < 5737 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5737).mp (by decide +kernel))) hgap
  have hprev := thV_752
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5737:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2820864310574287 : ℚ) / 500000000000) ≤ ((1408268482361773 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (5737:ℚ) := by decide +kernel
  have hratR : ((((2820864310574287 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1408268482361773 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5737:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_754 : ((((2825192004917811 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5741 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5737 < q → q < 5741 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5741).mp (by decide +kernel))) hgap
  have hprev := thV_753
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5741:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2825192004917811 : ℚ) / 500000000000) ≤ ((2820864310574287 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (5741:ℚ) := by decide +kernel
  have hratR : ((((2825192004917811 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((2820864310574287 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5741:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_755 : ((((2829519873416683 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5743 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5741 < q → q < 5743 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5743).mp (by decide +kernel))) hgap
  have hprev := thV_754
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5743:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2829519873416683 : ℚ) / 500000000000) ≤ ((2825192004917811 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (5743:ℚ) := by decide +kernel
  have hratR : ((((2829519873416683 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((2825192004917811 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5743:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_756 : ((((5667696528035869 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5749 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5743 < q → q < 5749 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5749).mp (by decide +kernel))) hgap
  have hprev := thV_755
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5749:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5667696528035869 : ℚ) / 1000000000000) ≤ ((2829519873416683 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (5749:ℚ) := by decide +kernel
  have hratR : ((((5667696528035869 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2829519873416683 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5749:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_757 : ((((5676358513969067 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5779 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5749 < q → q < 5779 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5779).mp (by decide +kernel))) hgap
  have hprev := thV_756
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5779:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5676358513969067 : ℚ) / 1000000000000) ≤ ((5667696528035869 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (5779:ℚ) := by decide +kernel
  have hratR : ((((5676358513969067 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5667696528035869 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5779:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_758 : ((((1137004238364821 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5783 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5779 < q → q < 5783 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5783).mp (by decide +kernel))) hgap
  have hprev := thV_757
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5783:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1137004238364821 : ℚ) / 200000000000) ≤ ((5676358513969067 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (5783:ℚ) := by decide +kernel
  have hratR : ((((1137004238364821 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((5676358513969067 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5783:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_759 : ((((5693685252088211 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5791 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5783 < q → q < 5791 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5791).mp (by decide +kernel))) hgap
  have hprev := thV_758
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5791:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5693685252088211 : ℚ) / 1000000000000) ≤ ((1137004238364821 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (5791:ℚ) := by decide +kernel
  have hratR : ((((5693685252088211 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1137004238364821 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5791:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_760 : ((((5702351037680557 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5801 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5791 < q → q < 5801 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5801).mp (by decide +kernel))) hgap
  have hprev := thV_759
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5801:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5702351037680557 : ℚ) / 1000000000000) ≤ ((5693685252088211 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (5801:ℚ) := by decide +kernel
  have hratR : ((((5702351037680557 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5693685252088211 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5801:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_761 : ((((5711017857042809 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5807 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5801 < q → q < 5807 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5807).mp (by decide +kernel))) hgap
  have hprev := thV_760
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5807:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5711017857042809 : ℚ) / 1000000000000) ≤ ((5702351037680557 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (5807:ℚ) := by decide +kernel
  have hratR : ((((5711017857042809 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5702351037680557 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5807:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_762 : ((((5719685709107391 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5813 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5807 < q → q < 5813 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5813).mp (by decide +kernel))) hgap
  have hprev := thV_761
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5813:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5719685709107391 : ℚ) / 1000000000000) ≤ ((5711017857042809 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (5813:ℚ) := by decide +kernel
  have hratR : ((((5719685709107391 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5711017857042809 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5813:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_763 : ((((5728354936451543 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5821 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5813 < q → q < 5821 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5821).mp (by decide +kernel))) hgap
  have hprev := thV_762
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5821:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5728354936451543 : ℚ) / 1000000000000) ≤ ((5719685709107391 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (5821:ℚ) := by decide +kernel
  have hratR : ((((5728354936451543 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5719685709107391 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5821:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_764 : ((((2868512597007783 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5827 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5821 < q → q < 5827 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5827).mp (by decide +kernel))) hgap
  have hprev := thV_763
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5827:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2868512597007783 : ℚ) / 500000000000) ≤ ((5728354936451543 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (5827:ℚ) := by decide +kernel
  have hratR : ((((2868512597007783 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((5728354936451543 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5827:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_765 : ((((574569750884073 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5839 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5827 < q → q < 5839 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5839).mp (by decide +kernel))) hgap
  have hprev := thV_764
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5839:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((574569750884073 : ℚ) / 100000000000) ≤ ((2868512597007783 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (5839:ℚ) := by decide +kernel
  have hratR : ((((574569750884073 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((2868512597007783 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5839:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_766 : ((((1150874101696033 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5843 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5839 < q → q < 5843 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5843).mp (by decide +kernel))) hgap
  have hprev := thV_765
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5843:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1150874101696033 : ℚ) / 200000000000) ≤ ((574569750884073 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (5843:ℚ) := by decide +kernel
  have hratR : ((((1150874101696033 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((574569750884073 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5843:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_767 : ((((720380566807811 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5849 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5843 < q → q < 5849 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5849).mp (by decide +kernel))) hgap
  have hprev := thV_766
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5849:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((720380566807811 : ℚ) / 125000000000) ≤ ((1150874101696033 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (5849:ℚ) := by decide +kernel
  have hratR : ((((720380566807811 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((1150874101696033 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5849:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_768 : ((((1442929725581289 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5851 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5849 < q → q < 5851 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5851).mp (by decide +kernel))) hgap
  have hprev := thV_767
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5851:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1442929725581289 : ℚ) / 250000000000) ≤ ((720380566807811 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (5851:ℚ) := by decide +kernel
  have hratR : ((((1442929725581289 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((720380566807811 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5851:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_769 : ((((2890197147564063 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5857 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5851 < q → q < 5857 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5857).mp (by decide +kernel))) hgap
  have hprev := thV_768
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5857:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2890197147564063 : ℚ) / 500000000000) ≤ ((1442929725581289 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (5857:ℚ) := by decide +kernel
  have hratR : ((((2890197147564063 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1442929725581289 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5857:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_770 : ((((5789070370641483 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5861 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5857 < q → q < 5861 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5861).mp (by decide +kernel))) hgap
  have hprev := thV_769
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5861:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5789070370641483 : ℚ) / 1000000000000) ≤ ((2890197147564063 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (5861:ℚ) := by decide +kernel
  have hratR : ((((5789070370641483 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2890197147564063 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5861:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_771 : ((((5797747469347289 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5867 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5861 < q → q < 5867 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5867).mp (by decide +kernel))) hgap
  have hprev := thV_770
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5867:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5797747469347289 : ℚ) / 1000000000000) ≤ ((5789070370641483 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (5867:ℚ) := by decide +kernel
  have hratR : ((((5797747469347289 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5789070370641483 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5867:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_772 : ((((5806424908884727 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5869 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5867 < q → q < 5869 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5869).mp (by decide +kernel))) hgap
  have hprev := thV_771
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5869:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5806424908884727 : ℚ) / 1000000000000) ≤ ((5797747469347289 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (5869:ℚ) := by decide +kernel
  have hratR : ((((5806424908884727 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5797747469347289 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5869:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_773 : ((((5815104050840009 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5879 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5869 < q → q < 5879 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5879).mp (by decide +kernel))) hgap
  have hprev := thV_772
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5879:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5815104050840009 : ℚ) / 1000000000000) ≤ ((5806424908884727 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (5879:ℚ) := by decide +kernel
  have hratR : ((((5815104050840009 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5806424908884727 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5879:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_774 : ((((5823783532931349 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5881 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5879 < q → q < 5881 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5881).mp (by decide +kernel))) hgap
  have hprev := thV_773
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5881:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5823783532931349 : ℚ) / 1000000000000) ≤ ((5815104050840009 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (5881:ℚ) := by decide +kernel
  have hratR : ((((5823783532931349 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5815104050840009 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5881:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_775 : ((((583246573195423 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5897 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5881 < q → q < 5897 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5897).mp (by decide +kernel))) hgap
  have hprev := thV_774
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5897:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((583246573195423 : ℚ) / 100000000000) ≤ ((5823783532931349 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (5897:ℚ) := by decide +kernel
  have hratR : ((((583246573195423 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((5823783532931349 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5897:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_776 : ((((5841148947926351 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5903 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5897 < q → q < 5903 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5903).mp (by decide +kernel))) hgap
  have hprev := thV_775
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5903:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5841148947926351 : ℚ) / 1000000000000) ≤ ((583246573195423 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (5903:ℚ) := by decide +kernel
  have hratR : ((((5841148947926351 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((583246573195423 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5903:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_777 : ((((1462458886569877 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5923 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5903 < q → q < 5923 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5923).mp (by decide +kernel))) hgap
  have hprev := thV_776
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5923:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1462458886569877 : ℚ) / 250000000000) ≤ ((5841148947926351 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (5923:ℚ) := by decide +kernel
  have hratR : ((((1462458886569877 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((5841148947926351 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5923:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_778 : ((((91539419058409 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5927 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5923 < q → q < 5927 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5927).mp (by decide +kernel))) hgap
  have hprev := thV_777
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5927:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((91539419058409 : ℚ) / 15625000000) ≤ ((1462458886569877 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (5927:ℚ) := by decide +kernel
  have hratR : ((((91539419058409 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ ((((1462458886569877 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5927:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_779 : ((((183350378618221 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5939 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5927 < q → q < 5939 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5939).mp (by decide +kernel))) hgap
  have hprev := thV_778
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5939:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((183350378618221 : ℚ) / 31250000000) ≤ ((91539419058409 : ℚ) / 15625000000) + Work.RHContract.RegionI.logLowQ (5939:ℚ) := by decide +kernel
  have hratR : ((((183350378618221 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((91539419058409 : ℚ) / 15625000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5939:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_780 : ((((2937951883176553 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5953 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5939 < q → q < 5953 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5953).mp (by decide +kernel))) hgap
  have hprev := thV_779
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5953:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2937951883176553 : ℚ) / 500000000000) ≤ ((183350378618221 : ℚ) / 31250000000) + Work.RHContract.RegionI.logLowQ (5953:ℚ) := by decide +kernel
  have hratR : ((((2937951883176553 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((183350378618221 : ℚ) / 31250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5953:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_781 : ((((5884600109407031 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5981 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5953 < q → q < 5981 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5981).mp (by decide +kernel))) hgap
  have hprev := thV_780
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5981:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5884600109407031 : ℚ) / 1000000000000) ≤ ((2937951883176553 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (5981:ℚ) := by decide +kernel
  have hratR : ((((5884600109407031 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2937951883176553 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5981:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_782 : ((((5893297455134837 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((5987 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5981 < q → q < 5987 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5987).mp (by decide +kernel))) hgap
  have hprev := thV_781
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (5987:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5893297455134837 : ℚ) / 1000000000000) ≤ ((5884600109407031 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (5987:ℚ) := by decide +kernel
  have hratR : ((((5893297455134837 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5884600109407031 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (5987:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_783 : ((((5901998135866567 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6007 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5987 < q → q < 6007 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6007).mp (by decide +kernel))) hgap
  have hprev := thV_782
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6007:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5901998135866567 : ℚ) / 1000000000000) ≤ ((5893297455134837 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (6007:ℚ) := by decide +kernel
  have hratR : ((((5901998135866567 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5893297455134837 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6007:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_784 : ((((2955349741133243 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6011 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6007 < q → q < 6011 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6011).mp (by decide +kernel))) hgap
  have hprev := thV_783
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6011:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2955349741133243 : ℚ) / 500000000000) ≤ ((5901998135866567 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (6011:ℚ) := by decide +kernel
  have hratR : ((((2955349741133243 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((5901998135866567 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6011:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_785 : ((((184981369334433 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6029 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6011 < q → q < 6029 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6029).mp (by decide +kernel))) hgap
  have hprev := thV_784
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6029:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((184981369334433 : ℚ) / 31250000000) ≤ ((2955349741133243 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (6029:ℚ) := by decide +kernel
  have hratR : ((((184981369334433 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((2955349741133243 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6029:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_786 : ((((5928109481177533 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6037 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6029 < q → q < 6037 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6037).mp (by decide +kernel))) hgap
  have hprev := thV_785
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6037:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5928109481177533 : ℚ) / 1000000000000) ≤ ((184981369334433 : ℚ) / 31250000000) + Work.RHContract.RegionI.logLowQ (6037:ℚ) := by decide +kernel
  have hratR : ((((5928109481177533 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((184981369334433 : ℚ) / 31250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6037:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_787 : ((((237472645481231 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6043 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6037 < q → q < 6043 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6043).mp (by decide +kernel))) hgap
  have hprev := thV_786
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6043:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((237472645481231 : ℚ) / 40000000000) ≤ ((5928109481177533 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (6043:ℚ) := by decide +kernel
  have hratR : ((((237472645481231 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((5928109481177533 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6043:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_788 : ((((743190431823491 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6047 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6043 < q → q < 6047 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6047).mp (by decide +kernel))) hgap
  have hprev := thV_787
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6047:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((743190431823491 : ℚ) / 125000000000) ≤ ((237472645481231 : ℚ) / 40000000000) + Work.RHContract.RegionI.logLowQ (6047:ℚ) := by decide +kernel
  have hratR : ((((743190431823491 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((237472645481231 : ℚ) / 40000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6047:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_789 : ((((59542317638807 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6053 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6047 < q → q < 6053 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6053).mp (by decide +kernel))) hgap
  have hprev := thV_788
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6053:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((59542317638807 : ℚ) / 10000000000) ≤ ((743190431823491 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (6053:ℚ) := by decide +kernel
  have hratR : ((((59542317638807 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ ((((743190431823491 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6053:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_790 : ((((2981471191702761 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6067 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6053 < q → q < 6067 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6067).mp (by decide +kernel))) hgap
  have hprev := thV_789
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6067:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2981471191702761 : ℚ) / 500000000000) ≤ ((59542317638807 : ℚ) / 10000000000) + Work.RHContract.RegionI.logLowQ (6067:ℚ) := by decide +kernel
  have hratR : ((((2981471191702761 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((59542317638807 : ℚ) / 10000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6067:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_791 : ((((59716539913983 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6073 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6067 < q → q < 6073 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6073).mp (by decide +kernel))) hgap
  have hprev := thV_790
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6073:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((59716539913983 : ℚ) / 10000000000) ≤ ((2981471191702761 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (6073:ℚ) := by decide +kernel
  have hratR : ((((59716539913983 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ ((((2981471191702761 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6073:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_792 : ((((5980366586882929 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6079 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6073 < q → q < 6079 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6079).mp (by decide +kernel))) hgap
  have hprev := thV_791
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6079:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5980366586882929 : ℚ) / 1000000000000) ≤ ((59716539913983 : ℚ) / 10000000000) + Work.RHContract.RegionI.logLowQ (6079:ℚ) := by decide +kernel
  have hratR : ((((5980366586882929 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((59716539913983 : ℚ) / 10000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6079:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_793 : ((((2994540413011709 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6089 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6079 < q → q < 6089 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6089).mp (by decide +kernel))) hgap
  have hprev := thV_792
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6089:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2994540413011709 : ℚ) / 500000000000) ≤ ((5980366586882929 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (6089:ℚ) := by decide +kernel
  have hratR : ((((2994540413011709 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((5980366586882929 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6089:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_794 : ((((1199559078714227 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6091 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6089 < q → q < 6091 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6091).mp (by decide +kernel))) hgap
  have hprev := thV_793
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6091:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1199559078714227 : ℚ) / 200000000000) ≤ ((2994540413011709 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (6091:ℚ) := by decide +kernel
  have hratR : ((((1199559078714227 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((2994540413011709 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6091:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_795 : ((((6006511601539167 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6101 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6091 < q → q < 6101 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6101).mp (by decide +kernel))) hgap
  have hprev := thV_794
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6101:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6006511601539167 : ℚ) / 1000000000000) ≤ ((1199559078714227 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (6101:ℚ) := by decide +kernel
  have hratR : ((((6006511601539167 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1199559078714227 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6101:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_796 : ((((1503807443616519 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6113 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6101 < q → q < 6113 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6113).mp (by decide +kernel))) hgap
  have hprev := thV_795
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6113:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1503807443616519 : ℚ) / 250000000000) ≤ ((6006511601539167 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (6113:ℚ) := by decide +kernel
  have hratR : ((((1503807443616519 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((6006511601539167 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6113:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_797 : ((((6023949255223807 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6121 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6113 < q → q < 6121 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6121).mp (by decide +kernel))) hgap
  have hprev := thV_796
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6121:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6023949255223807 : ℚ) / 1000000000000) ≤ ((1503807443616519 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (6121:ℚ) := by decide +kernel
  have hratR : ((((6023949255223807 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1503807443616519 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6121:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_798 : ((((120653407367369 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6131 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6121 < q → q < 6131 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6131).mp (by decide +kernel))) hgap
  have hprev := thV_797
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6131:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((120653407367369 : ℚ) / 20000000000) ≤ ((6023949255223807 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (6131:ℚ) := by decide +kernel
  have hratR : ((((120653407367369 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ ((((6023949255223807 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6131:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_799 : ((((1510347951917739 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6133 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6131 < q → q < 6133 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6133).mp (by decide +kernel))) hgap
  have hprev := thV_798
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6133:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1510347951917739 : ℚ) / 250000000000) ≤ ((120653407367369 : ℚ) / 20000000000) + Work.RHContract.RegionI.logLowQ (6133:ℚ) := by decide +kernel
  have hratR : ((((1510347951917739 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((120653407367369 : ℚ) / 20000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6133:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_800 : ((((6050114876169 : ℚ) / 1000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6143 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6133 < q → q < 6143 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6143).mp (by decide +kernel))) hgap
  have hprev := thV_799
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6143:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6050114876169 : ℚ) / 1000000000) ≤ ((1510347951917739 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (6143:ℚ) := by decide +kernel
  have hratR : ((((6050114876169 : ℚ) / 1000000000) : ℚ) : ℝ) ≤ ((((1510347951917739 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6143:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_801 : ((((6058839246115089 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6151 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6143 < q → q < 6151 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6151).mp (by decide +kernel))) hgap
  have hprev := thV_800
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6151:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6058839246115089 : ℚ) / 1000000000000) ≤ ((6050114876169 : ℚ) / 1000000000) + Work.RHContract.RegionI.logLowQ (6151:ℚ) := by decide +kernel
  have hratR : ((((6058839246115089 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((6050114876169 : ℚ) / 1000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6151:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_802 : ((((6067565565062931 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6163 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6151 < q → q < 6163 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6163).mp (by decide +kernel))) hgap
  have hprev := thV_801
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6163:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6067565565062931 : ℚ) / 1000000000000) ≤ ((6058839246115089 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (6163:ℚ) := by decide +kernel
  have hratR : ((((6067565565062931 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((6058839246115089 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6163:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_803 : ((((1215258701056441 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6173 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6163 < q → q < 6173 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6173).mp (by decide +kernel))) hgap
  have hprev := thV_802
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6173:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1215258701056441 : ℚ) / 200000000000) ≤ ((6067565565062931 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (6173:ℚ) := by decide +kernel
  have hratR : ((((1215258701056441 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((6067565565062931 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6173:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_804 : ((((6085025325862047 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6197 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6173 < q → q < 6197 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6197).mp (by decide +kernel))) hgap
  have hprev := thV_803
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6197:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6085025325862047 : ℚ) / 1000000000000) ≤ ((1215258701056441 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (6197:ℚ) := by decide +kernel
  have hratR : ((((6085025325862047 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1215258701056441 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6197:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_805 : ((((6093757469126629 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6199 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6197 < q → q < 6199 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6199).mp (by decide +kernel))) hgap
  have hprev := thV_804
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6199:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6093757469126629 : ℚ) / 1000000000000) ≤ ((6085025325862047 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (6199:ℚ) := by decide +kernel
  have hratR : ((((6093757469126629 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((6085025325862047 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6199:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_806 : ((((3051245128724241 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6203 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6199 < q → q < 6203 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6203).mp (by decide +kernel))) hgap
  have hprev := thV_805
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6203:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3051245128724241 : ℚ) / 500000000000) ≤ ((6093757469126629 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (6203:ℚ) := by decide +kernel
  have hratR : ((((3051245128724241 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((6093757469126629 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6203:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_807 : ((((6111224334637921 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6211 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6203 < q → q < 6211 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6211).mp (by decide +kernel))) hgap
  have hprev := thV_806
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6211:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6111224334637921 : ℚ) / 1000000000000) ≤ ((3051245128724241 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (6211:ℚ) := by decide +kernel
  have hratR : ((((6111224334637921 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3051245128724241 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6211:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_808 : ((((611995937738907 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6217 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6211 < q → q < 6217 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6217).mp (by decide +kernel))) hgap
  have hprev := thV_807
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6217:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((611995937738907 : ℚ) / 100000000000) ≤ ((6111224334637921 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (6217:ℚ) := by decide +kernel
  have hratR : ((((611995937738907 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((6111224334637921 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6217:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_809 : ((((1225739012666093 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6221 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6217 < q → q < 6221 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6221).mp (by decide +kernel))) hgap
  have hprev := thV_808
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6221:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1225739012666093 : ℚ) / 200000000000) ≤ ((611995937738907 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (6221:ℚ) := by decide +kernel
  have hratR : ((((1225739012666093 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((611995937738907 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6221:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_810 : ((((6137432034412599 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6229 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6221 < q → q < 6229 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6229).mp (by decide +kernel))) hgap
  have hprev := thV_809
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6229:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6137432034412599 : ℚ) / 1000000000000) ≤ ((1225739012666093 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (6229:ℚ) := by decide +kernel
  have hratR : ((((6137432034412599 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1225739012666093 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6229:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_811 : ((((6146171891036973 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6247 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6229 < q → q < 6247 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6247).mp (by decide +kernel))) hgap
  have hprev := thV_810
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6247:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6146171891036973 : ℚ) / 1000000000000) ≤ ((6137432034412599 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (6247:ℚ) := by decide +kernel
  have hratR : ((((6146171891036973 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((6137432034412599 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6247:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_812 : ((((1538728336787463 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6257 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6247 < q → q < 6257 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6257).mp (by decide +kernel))) hgap
  have hprev := thV_811
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6257:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1538728336787463 : ℚ) / 250000000000) ≤ ((6146171891036973 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (6257:ℚ) := by decide +kernel
  have hratR : ((((1538728336787463 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((6146171891036973 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6257:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_813 : ((((3081827880864629 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6263 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6257 < q → q < 6263 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6263).mp (by decide +kernel))) hgap
  have hprev := thV_812
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6263:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3081827880864629 : ℚ) / 500000000000) ≤ ((1538728336787463 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (6263:ℚ) := by decide +kernel
  have hratR : ((((3081827880864629 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1538728336787463 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6263:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_814 : ((((1543099783464353 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6269 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6263 < q → q < 6269 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6269).mp (by decide +kernel))) hgap
  have hprev := thV_813
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6269:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1543099783464353 : ℚ) / 250000000000) ≤ ((3081827880864629 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (6269:ℚ) := by decide +kernel
  have hratR : ((((1543099783464353 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((3081827880864629 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6269:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_815 : ((((1236228564992967 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6271 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6269 < q → q < 6271 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6271).mp (by decide +kernel))) hgap
  have hprev := thV_814
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6271:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1236228564992967 : ℚ) / 200000000000) ≤ ((1543099783464353 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (6271:ℚ) := by decide +kernel
  have hratR : ((((1236228564992967 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((1543099783464353 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6271:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_816 : ((((6189887472400033 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6277 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6271 < q → q < 6277 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6277).mp (by decide +kernel))) hgap
  have hprev := thV_815
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6277:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6189887472400033 : ℚ) / 1000000000000) ≤ ((1236228564992967 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (6277:ℚ) := by decide +kernel
  have hratR : ((((6189887472400033 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1236228564992967 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6277:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_817 : ((((387414606980331 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6287 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6277 < q → q < 6287 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6287).mp (by decide +kernel))) hgap
  have hprev := thV_816
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6287:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((387414606980331 : ℚ) / 62500000000) ≤ ((6189887472400033 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (6287:ℚ) := by decide +kernel
  have hratR : ((((387414606980331 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((6189887472400033 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6287:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_818 : ((((3103690928925899 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6299 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6287 < q → q < 6299 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6299).mp (by decide +kernel))) hgap
  have hprev := thV_817
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6299:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3103690928925899 : ℚ) / 500000000000) ≤ ((387414606980331 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (6299:ℚ) := by decide +kernel
  have hratR : ((((3103690928925899 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((387414606980331 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6299:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_819 : ((((310806516073931 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6301 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6299 < q → q < 6301 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6301).mp (by decide +kernel))) hgap
  have hprev := thV_818
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6301:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((310806516073931 : ℚ) / 50000000000) ≤ ((3103690928925899 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (6301:ℚ) := by decide +kernel
  have hratR : ((((310806516073931 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((3103690928925899 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6301:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_820 : ((((1556220092724271 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6311 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6301 < q → q < 6311 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6311).mp (by decide +kernel))) hgap
  have hprev := thV_819
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6311:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1556220092724271 : ℚ) / 250000000000) ≤ ((310806516073931 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (6311:ℚ) := by decide +kernel
  have hratR : ((((1556220092724271 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((310806516073931 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6311:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_821 : ((((6233631370584863 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6317 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6311 < q → q < 6317 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6317).mp (by decide +kernel))) hgap
  have hprev := thV_820
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6317:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6233631370584863 : ℚ) / 1000000000000) ≤ ((1556220092724271 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (6317:ℚ) := by decide +kernel
  have hratR : ((((6233631370584863 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1556220092724271 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6317:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_822 : ((((3121191659819901 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6323 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6317 < q → q < 6323 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6323).mp (by decide +kernel))) hgap
  have hprev := thV_821
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6323:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3121191659819901 : ℚ) / 500000000000) ≤ ((6233631370584863 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (6323:ℚ) := by decide +kernel
  have hratR : ((((3121191659819901 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((6233631370584863 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6323:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_823 : ((((6251136217161457 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6329 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6323 < q → q < 6329 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6329).mp (by decide +kernel))) hgap
  have hprev := thV_822
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6329:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6251136217161457 : ℚ) / 1000000000000) ≤ ((3121191659819901 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (6329:ℚ) := by decide +kernel
  have hratR : ((((6251136217161457 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3121191659819901 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6329:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_824 : ((((6259890377907661 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6337 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6329 < q → q < 6337 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6337).mp (by decide +kernel))) hgap
  have hprev := thV_823
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6337:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6259890377907661 : ℚ) / 1000000000000) ≤ ((6251136217161457 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (6337:ℚ) := by decide +kernel
  have hratR : ((((6259890377907661 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((6251136217161457 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6337:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_825 : ((((250745819401047 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6343 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6337 < q → q < 6343 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6343).mp (by decide +kernel))) hgap
  have hprev := thV_824
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6343:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((250745819401047 : ℚ) / 40000000000) ≤ ((6259890377907661 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (6343:ℚ) := by decide +kernel
  have hratR : ((((250745819401047 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((6259890377907661 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6343:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_826 : ((((3138701083722161 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6353 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6343 < q → q < 6353 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6353).mp (by decide +kernel))) hgap
  have hprev := thV_825
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6353:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3138701083722161 : ℚ) / 500000000000) ≤ ((250745819401047 : ℚ) / 40000000000) + Work.RHContract.RegionI.logLowQ (6353:ℚ) := by decide +kernel
  have hratR : ((((3138701083722161 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((250745819401047 : ℚ) / 40000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6353:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_827 : ((((628615979385247 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6359 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6353 < q → q < 6359 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6359).mp (by decide +kernel))) hgap
  have hprev := thV_826
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6359:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((628615979385247 : ℚ) / 100000000000) ≤ ((3138701083722161 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (6359:ℚ) := by decide +kernel
  have hratR : ((((628615979385247 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((3138701083722161 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6359:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_828 : ((((6294917734726029 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6361 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6359 < q → q < 6361 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6361).mp (by decide +kernel))) hgap
  have hprev := thV_827
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6361:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6294917734726029 : ℚ) / 1000000000000) ≤ ((628615979385247 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (6361:ℚ) := by decide +kernel
  have hratR : ((((6294917734726029 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((628615979385247 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6361:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_829 : ((((3151838309201463 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6367 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6361 < q → q < 6367 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6367).mp (by decide +kernel))) hgap
  have hprev := thV_828
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6367:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3151838309201463 : ℚ) / 500000000000) ≤ ((6294917734726029 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (6367:ℚ) := by decide +kernel
  have hratR : ((((3151838309201463 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((6294917734726029 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6367:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_830 : ((((78905455549939 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6373 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6367 < q → q < 6373 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6373).mp (by decide +kernel))) hgap
  have hprev := thV_829
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6373:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((78905455549939 : ℚ) / 12500000000) ≤ ((3151838309201463 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (6373:ℚ) := by decide +kernel
  have hratR : ((((78905455549939 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ ((((3151838309201463 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6373:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_831 : ((((3160598605308121 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6379 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6373 < q → q < 6379 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6379).mp (by decide +kernel))) hgap
  have hprev := thV_830
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6379:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3160598605308121 : ℚ) / 500000000000) ≤ ((78905455549939 : ℚ) / 12500000000) + Work.RHContract.RegionI.logLowQ (6379:ℚ) := by decide +kernel
  have hratR : ((((3160598605308121 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((78905455549939 : ℚ) / 12500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6379:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_832 : ((((1582489885913431 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6389 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6379 < q → q < 6389 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6389).mp (by decide +kernel))) hgap
  have hprev := thV_831
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6389:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1582489885913431 : ℚ) / 250000000000) ≤ ((3160598605308121 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (6389:ℚ) := by decide +kernel
  have hratR : ((((1582489885913431 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((3160598605308121 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6389:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_833 : ((((3169361564030027 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6397 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6389 < q → q < 6397 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6397).mp (by decide +kernel))) hgap
  have hprev := thV_832
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6397:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3169361564030027 : ℚ) / 500000000000) ≤ ((1582489885913431 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (6397:ℚ) := by decide +kernel
  have hratR : ((((3169361564030027 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1582489885913431 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6397:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_834 : ((((793436307150591 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6421 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6397 < q → q < 6421 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6421).mp (by decide +kernel))) hgap
  have hprev := thV_833
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6421:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((793436307150591 : ℚ) / 125000000000) ≤ ((3169361564030027 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (6421:ℚ) := by decide +kernel
  have hratR : ((((793436307150591 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((3169361564030027 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6421:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_835 : ((((6356258720346979 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6427 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6421 < q → q < 6427 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6427).mp (by decide +kernel))) hgap
  have hprev := thV_834
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6427:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6356258720346979 : ℚ) / 1000000000000) ≤ ((793436307150591 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (6427:ℚ) := by decide +kernel
  have hratR : ((((6356258720346979 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((793436307150591 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6427:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_836 : ((((636503040070287 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6449 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6427 < q → q < 6449 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6449).mp (by decide +kernel))) hgap
  have hprev := thV_835
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6449:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((636503040070287 : ℚ) / 100000000000) ≤ ((6356258720346979 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (6449:ℚ) := by decide +kernel
  have hratR : ((((636503040070287 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((6356258720346979 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6449:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_837 : ((((3186901195568141 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6451 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6449 < q → q < 6451 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6451).mp (by decide +kernel))) hgap
  have hprev := thV_836
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6451:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3186901195568141 : ℚ) / 500000000000) ≤ ((636503040070287 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (6451:ℚ) := by decide +kernel
  have hratR : ((((3186901195568141 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((636503040070287 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6451:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_838 : ((((3191288583974603 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6469 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6451 < q → q < 6469 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6469).mp (by decide +kernel))) hgap
  have hprev := thV_837
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6469:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3191288583974603 : ℚ) / 500000000000) ≤ ((3186901195568141 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (6469:ℚ) := by decide +kernel
  have hratR : ((((3191288583974603 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((3186901195568141 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6469:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_839 : ((((798919070363079 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6473 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6469 < q → q < 6473 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6473).mp (by decide +kernel))) hgap
  have hprev := thV_838
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6473:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((798919070363079 : ℚ) / 125000000000) ≤ ((3191288583974603 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (6473:ℚ) := by decide +kernel
  have hratR : ((((798919070363079 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((3191288583974603 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6473:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_840 : ((((320006459649997 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6481 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6473 < q → q < 6481 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6481).mp (by decide +kernel))) hgap
  have hprev := thV_839
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6481:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((320006459649997 : ℚ) / 50000000000) ≤ ((798919070363079 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (6481:ℚ) := by decide +kernel
  have hratR : ((((320006459649997 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((798919070363079 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6481:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_841 : ((((3204453682438927 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6491 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6481 < q → q < 6491 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6491).mp (by decide +kernel))) hgap
  have hprev := thV_840
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6491:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3204453682438927 : ℚ) / 500000000000) ≤ ((320006459649997 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (6491:ℚ) := by decide +kernel
  have hratR : ((((3204453682438927 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((320006459649997 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6491:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_842 : ((((6417690147892127 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6521 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6491 < q → q < 6521 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6521).mp (by decide +kernel))) hgap
  have hprev := thV_841
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6521:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6417690147892127 : ℚ) / 1000000000000) ≤ ((3204453682438927 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (6521:ℚ) := by decide +kernel
  have hratR : ((((6417690147892127 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3204453682438927 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6521:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_843 : ((((3213237078480097 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6529 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6521 < q → q < 6529 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6529).mp (by decide +kernel))) hgap
  have hprev := thV_842
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6529:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3213237078480097 : ℚ) / 500000000000) ≤ ((6417690147892127 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (6529:ℚ) := by decide +kernel
  have hratR : ((((3213237078480097 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((6417690147892127 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6529:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_844 : ((((1287052183833103 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6547 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6529 < q → q < 6547 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6547).mp (by decide +kernel))) hgap
  have hprev := thV_843
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6547:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1287052183833103 : ℚ) / 200000000000) ≤ ((3213237078480097 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (6547:ℚ) := by decide +kernel
  have hratR : ((((1287052183833103 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((3213237078480097 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6547:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_845 : ((((6444048292151127 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6551 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6547 < q → q < 6551 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6551).mp (by decide +kernel))) hgap
  have hprev := thV_844
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6551:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6444048292151127 : ℚ) / 1000000000000) ≤ ((1287052183833103 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (6551:ℚ) := by decide +kernel
  have hratR : ((((6444048292151127 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1287052183833103 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6551:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_846 : ((((6452835970387047 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6553 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6551 < q → q < 6553 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6553).mp (by decide +kernel))) hgap
  have hprev := thV_845
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6553:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6452835970387047 : ℚ) / 1000000000000) ≤ ((6444048292151127 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (6553:ℚ) := by decide +kernel
  have hratR : ((((6452835970387047 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((6444048292151127 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6553:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_847 : ((((6461625173478401 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6563 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6553 < q → q < 6563 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6563).mp (by decide +kernel))) hgap
  have hprev := thV_846
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6563:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6461625173478401 : ℚ) / 1000000000000) ≤ ((6452835970387047 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (6563:ℚ) := by decide +kernel
  have hratR : ((((6461625173478401 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((6452835970387047 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6563:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_848 : ((((3235207645184087 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6569 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6563 < q → q < 6569 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6569).mp (by decide +kernel))) hgap
  have hprev := thV_847
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6569:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3235207645184087 : ℚ) / 500000000000) ≤ ((6461625173478401 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (6569:ℚ) := by decide +kernel
  have hratR : ((((3235207645184087 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((6461625173478401 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6569:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_849 : ((((404950356979497 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6571 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6569 < q → q < 6571 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6571).mp (by decide +kernel))) hgap
  have hprev := thV_848
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6571:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((404950356979497 : ℚ) / 62500000000) ≤ ((3235207645184087 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (6571:ℚ) := by decide +kernel
  have hratR : ((((404950356979497 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((3235207645184087 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6571:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_850 : ((((3243998522831067 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6577 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6571 < q → q < 6577 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6577).mp (by decide +kernel))) hgap
  have hprev := thV_849
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6577:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3243998522831067 : ℚ) / 500000000000) ≤ ((404950356979497 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (6577:ℚ) := by decide +kernel
  have hratR : ((((3243998522831067 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((404950356979497 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6577:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_851 : ((((649678898764747 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6581 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6577 < q → q < 6581 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6581).mp (by decide +kernel))) hgap
  have hprev := thV_850
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6581:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((649678898764747 : ℚ) / 100000000000) ≤ ((3243998522831067 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (6581:ℚ) := by decide +kernel
  have hratR : ((((649678898764747 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((3243998522831067 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6581:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_852 : ((((3252791830522867 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6599 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6581 < q → q < 6599 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6599).mp (by decide +kernel))) hgap
  have hprev := thV_851
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6599:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3252791830522867 : ℚ) / 500000000000) ≤ ((649678898764747 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (6599:ℚ) := by decide +kernel
  have hratR : ((((3252791830522867 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((649678898764747 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6599:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_853 : ((((1628594886503661 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6607 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6599 < q → q < 6607 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6607).mp (by decide +kernel))) hgap
  have hprev := thV_852
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6607:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1628594886503661 : ℚ) / 250000000000) ≤ ((3252791830522867 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (6607:ℚ) := by decide +kernel
  have hratR : ((((1628594886503661 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((3252791830522867 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6607:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_854 : ((((6523177245591643 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6619 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6607 < q → q < 6619 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6619).mp (by decide +kernel))) hgap
  have hprev := thV_853
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6619:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6523177245591643 : ℚ) / 1000000000000) ≤ ((1628594886503661 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (6619:ℚ) := by decide +kernel
  have hratR : ((((6523177245591643 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1628594886503661 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6619:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_855 : ((((6531977660921669 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6637 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6619 < q → q < 6637 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6637).mp (by decide +kernel))) hgap
  have hprev := thV_854
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6637:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6531977660921669 : ℚ) / 1000000000000) ≤ ((6523177245591643 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (6637:ℚ) := by decide +kernel
  have hratR : ((((6531977660921669 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((6523177245591643 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6637:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_856 : ((((6540780484078291 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6653 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6637 < q → q < 6653 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6653).mp (by decide +kernel))) hgap
  have hprev := thV_855
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6653:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6540780484078291 : ℚ) / 1000000000000) ≤ ((6531977660921669 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (6653:ℚ) := by decide +kernel
  have hratR : ((((6540780484078291 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((6531977660921669 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6653:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_857 : ((((3274792104338641 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6659 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6653 < q → q < 6659 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6659).mp (by decide +kernel))) hgap
  have hprev := thV_856
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6659:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3274792104338641 : ℚ) / 500000000000) ≤ ((6540780484078291 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (6659:ℚ) := by decide +kernel
  have hratR : ((((3274792104338641 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((6540780484078291 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6659:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_858 : ((((262335529343063 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6661 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6659 < q → q < 6661 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6661).mp (by decide +kernel))) hgap
  have hprev := thV_857
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6661:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((262335529343063 : ℚ) / 40000000000) ≤ ((3274792104338641 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (6661:ℚ) := by decide +kernel
  have hratR : ((((262335529343063 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((3274792104338641 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6661:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_859 : ((((6567194058386359 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6673 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6661 < q → q < 6673 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6673).mp (by decide +kernel))) hgap
  have hprev := thV_858
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6673:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6567194058386359 : ℚ) / 1000000000000) ≤ ((262335529343063 : ℚ) / 40000000000) + Work.RHContract.RegionI.logLowQ (6673:ℚ) := by decide +kernel
  have hratR : ((((6567194058386359 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((262335529343063 : ℚ) / 40000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6673:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_860 : ((((1315200156387593 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6679 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6673 < q → q < 6679 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6679).mp (by decide +kernel))) hgap
  have hprev := thV_859
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6679:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1315200156387593 : ℚ) / 200000000000) ≤ ((6567194058386359 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (6679:ℚ) := by decide +kernel
  have hratR : ((((1315200156387593 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((6567194058386359 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6679:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_861 : ((((1646202250399991 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6689 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6679 < q → q < 6689 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6689).mp (by decide +kernel))) hgap
  have hprev := thV_860
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6689:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1646202250399991 : ℚ) / 250000000000) ≤ ((1315200156387593 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (6689:ℚ) := by decide +kernel
  have hratR : ((((1646202250399991 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((1315200156387593 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6689:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_862 : ((((6593617520215627 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6691 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6689 < q → q < 6691 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6691).mp (by decide +kernel))) hgap
  have hprev := thV_861
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6691:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6593617520215627 : ℚ) / 1000000000000) ≤ ((1646202250399991 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (6691:ℚ) := by decide +kernel
  have hratR : ((((6593617520215627 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1646202250399991 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6691:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_863 : ((((10316293019157 : ℚ) / 1562500000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6701 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6691 < q → q < 6701 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6701).mp (by decide +kernel))) hgap
  have hprev := thV_862
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6701:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10316293019157 : ℚ) / 1562500000) ≤ ((6593617520215627 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (6701:ℚ) := by decide +kernel
  have hratR : ((((10316293019157 : ℚ) / 1562500000) : ℚ) : ℝ) ≤ ((((6593617520215627 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6701:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_864 : ((((3305618921361859 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6703 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6701 < q → q < 6703 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6703).mp (by decide +kernel))) hgap
  have hprev := thV_863
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6703:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3305618921361859 : ℚ) / 500000000000) ≤ ((10316293019157 : ℚ) / 1562500000) + Work.RHContract.RegionI.logLowQ (6703:ℚ) := by decide +kernel
  have hratR : ((((3305618921361859 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((10316293019157 : ℚ) / 1562500000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6703:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_865 : ((((6620049047908161 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6709 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6703 < q → q < 6709 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6709).mp (by decide +kernel))) hgap
  have hprev := thV_864
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6709:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6620049047908161 : ℚ) / 1000000000000) ≤ ((3305618921361859 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (6709:ℚ) := by decide +kernel
  have hratR : ((((6620049047908161 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3305618921361859 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6709:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_866 : ((((6628861742517961 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6719 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6709 < q → q < 6719 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6719).mp (by decide +kernel))) hgap
  have hprev := thV_865
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6719:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6628861742517961 : ℚ) / 1000000000000) ≤ ((6620049047908161 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (6719:ℚ) := by decide +kernel
  have hratR : ((((6628861742517961 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((6620049047908161 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6719:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_867 : ((((3318838259301693 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6733 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6719 < q → q < 6733 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6733).mp (by decide +kernel))) hgap
  have hprev := thV_866
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6733:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3318838259301693 : ℚ) / 500000000000) ≤ ((6628861742517961 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (6733:ℚ) := by decide +kernel
  have hratR : ((((3318838259301693 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((6628861742517961 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6733:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_868 : ((((6646491888601227 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6737 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6733 < q → q < 6737 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6737).mp (by decide +kernel))) hgap
  have hprev := thV_867
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6737:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6646491888601227 : ℚ) / 1000000000000) ≤ ((3318838259301693 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (6737:ℚ) := by decide +kernel
  have hratR : ((((6646491888601227 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3318838259301693 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6737:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_869 : ((((3327655407342599 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6761 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6737 < q → q < 6761 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6761).mp (by decide +kernel))) hgap
  have hprev := thV_868
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6761:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3327655407342599 : ℚ) / 500000000000) ≤ ((6646491888601227 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (6761:ℚ) := by decide +kernel
  have hratR : ((((3327655407342599 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((6646491888601227 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6761:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_870 : ((((6664130036539653 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6763 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6761 < q → q < 6763 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6763).mp (by decide +kernel))) hgap
  have hprev := thV_869
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6763:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6664130036539653 : ℚ) / 1000000000000) ≤ ((3327655407342599 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (6763:ℚ) := by decide +kernel
  have hratR : ((((6664130036539653 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3327655407342599 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6763:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_871 : ((((1668237905353491 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6779 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6763 < q → q < 6779 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6779).mp (by decide +kernel))) hgap
  have hprev := thV_870
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6779:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1668237905353491 : ℚ) / 250000000000) ≤ ((6664130036539653 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (6779:ℚ) := by decide +kernel
  have hratR : ((((1668237905353491 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((6664130036539653 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6779:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_872 : ((((835221687659191 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6781 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6779 < q → q < 6781 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6781).mp (by decide +kernel))) hgap
  have hprev := thV_871
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6781:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((835221687659191 : ℚ) / 125000000000) ≤ ((1668237905353491 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (6781:ℚ) := by decide +kernel
  have hratR : ((((835221687659191 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((1668237905353491 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6781:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_873 : ((((3345298427377761 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6791 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6781 < q → q < 6791 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6791).mp (by decide +kernel))) hgap
  have hprev := thV_872
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6791:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3345298427377761 : ℚ) / 500000000000) ≤ ((835221687659191 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (6791:ℚ) := by decide +kernel
  have hratR : ((((3345298427377761 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((835221687659191 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6791:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_874 : ((((6699420502701593 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6793 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6791 < q → q < 6793 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6793).mp (by decide +kernel))) hgap
  have hprev := thV_873
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6793:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6699420502701593 : ℚ) / 1000000000000) ≤ ((3345298427377761 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (6793:ℚ) := by decide +kernel
  have hratR : ((((6699420502701593 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3345298427377761 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6793:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_875 : ((((3354122810834409 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6803 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6793 < q → q < 6803 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6803).mp (by decide +kernel))) hgap
  have hprev := thV_874
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6803:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3354122810834409 : ℚ) / 500000000000) ≤ ((6699420502701593 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (6803:ℚ) := by decide +kernel
  have hratR : ((((3354122810834409 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((6699420502701593 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6803:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_876 : ((((3358536838101257 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6823 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6803 < q → q < 6823 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6823).mp (by decide +kernel))) hgap
  have hprev := thV_875
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6823:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3358536838101257 : ℚ) / 500000000000) ≤ ((3354122810834409 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (6823:ℚ) := by decide +kernel
  have hratR : ((((3358536838101257 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((3354122810834409 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6823:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_877 : ((((1681475579204203 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6827 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6823 < q → q < 6827 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6827).mp (by decide +kernel))) hgap
  have hprev := thV_876
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6827:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1681475579204203 : ℚ) / 250000000000) ≤ ((3358536838101257 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (6827:ℚ) := by decide +kernel
  have hratR : ((((1681475579204203 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((3358536838101257 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6827:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_878 : ((((6734731250342653 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6829 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6827 < q → q < 6829 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6829).mp (by decide +kernel))) hgap
  have hprev := thV_877
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6829:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6734731250342653 : ℚ) / 1000000000000) ≤ ((1681475579204203 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (6829:ℚ) := by decide +kernel
  have hratR : ((((6734731250342653 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1681475579204203 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6829:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_879 : ((((3371780384717157 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6833 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6829 < q → q < 6833 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6833).mp (by decide +kernel))) hgap
  have hprev := thV_878
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6833:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3371780384717157 : ℚ) / 500000000000) ≤ ((6734731250342653 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (6833:ℚ) := by decide +kernel
  have hratR : ((((3371780384717157 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((6734731250342653 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6833:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_880 : ((((1350478291725991 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6841 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6833 < q → q < 6841 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6841).mp (by decide +kernel))) hgap
  have hprev := thV_879
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6841:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1350478291725991 : ℚ) / 200000000000) ≤ ((3371780384717157 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (6841:ℚ) := by decide +kernel
  have hratR : ((((1350478291725991 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((3371780384717157 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6841:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_881 : ((((169030612098353 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6857 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6841 < q → q < 6857 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6857).mp (by decide +kernel))) hgap
  have hprev := thV_880
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6857:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((169030612098353 : ℚ) / 25000000000) ≤ ((1350478291725991 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (6857:ℚ) := by decide +kernel
  have hratR : ((((169030612098353 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((1350478291725991 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6857:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_882 : ((((6770058383873909 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6863 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6857 < q → q < 6863 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6863).mp (by decide +kernel))) hgap
  have hprev := thV_881
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6863:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6770058383873909 : ℚ) / 1000000000000) ≤ ((169030612098353 : ℚ) / 25000000000) + Work.RHContract.RegionI.logLowQ (6863:ℚ) := by decide +kernel
  have hratR : ((((6770058383873909 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((169030612098353 : ℚ) / 25000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6863:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_883 : ((((6778893157685003 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6869 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6863 < q → q < 6869 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6869).mp (by decide +kernel))) hgap
  have hprev := thV_882
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6869:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6778893157685003 : ℚ) / 1000000000000) ≤ ((6770058383873909 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (6869:ℚ) := by decide +kernel
  have hratR : ((((6778893157685003 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((6770058383873909 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6869:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_884 : ((((3393864111308457 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6871 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6869 < q → q < 6871 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6871).mp (by decide +kernel))) hgap
  have hprev := thV_883
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6871:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3393864111308457 : ℚ) / 500000000000) ≤ ((6778893157685003 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (6871:ℚ) := by decide +kernel
  have hratR : ((((3393864111308457 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((6778893157685003 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6871:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_885 : ((((6796565032496193 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6883 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6871 < q → q < 6883 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6883).mp (by decide +kernel))) hgap
  have hprev := thV_884
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6883:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6796565032496193 : ℚ) / 1000000000000) ≤ ((3393864111308457 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (6883:ℚ) := by decide +kernel
  have hratR : ((((6796565032496193 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3393864111308457 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6883:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_886 : ((((6805404164245619 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6899 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6883 < q → q < 6899 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6899).mp (by decide +kernel))) hgap
  have hprev := thV_885
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6899:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6805404164245619 : ℚ) / 1000000000000) ≤ ((6796565032496193 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (6899:ℚ) := by decide +kernel
  have hratR : ((((6805404164245619 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((6796565032496193 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6899:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_887 : ((((1703561113727897 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6907 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6899 < q → q < 6907 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6907).mp (by decide +kernel))) hgap
  have hprev := thV_886
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6907:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1703561113727897 : ℚ) / 250000000000) ≤ ((6805404164245619 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (6907:ℚ) := by decide +kernel
  have hratR : ((((1703561113727897 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((6805404164245619 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6907:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_888 : ((((85288566556657 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6911 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6907 < q → q < 6911 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6911).mp (by decide +kernel))) hgap
  have hprev := thV_887
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6911:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((85288566556657 : ℚ) / 12500000000) ≤ ((1703561113727897 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (6911:ℚ) := by decide +kernel
  have hratR : ((((85288566556657 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ ((((1703561113727897 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6911:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_889 : ((((6831927061958041 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6917 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6911 < q → q < 6917 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6917).mp (by decide +kernel))) hgap
  have hprev := thV_888
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6917:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6831927061958041 : ℚ) / 1000000000000) ≤ ((85288566556657 : ℚ) / 12500000000) + Work.RHContract.RegionI.logLowQ (6917:ℚ) := by decide +kernel
  have hratR : ((((6831927061958041 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((85288566556657 : ℚ) / 12500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6917:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_890 : ((((3420386563572807 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6947 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6917 < q → q < 6947 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6947).mp (by decide +kernel))) hgap
  have hprev := thV_889
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6947:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3420386563572807 : ℚ) / 500000000000) ≤ ((6831927061958041 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (6947:ℚ) := by decide +kernel
  have hratR : ((((3420386563572807 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((6831927061958041 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6947:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_891 : ((((428101217511613 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6949 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6947 < q → q < 6949 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6949).mp (by decide +kernel))) hgap
  have hprev := thV_890
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6949:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((428101217511613 : ℚ) / 62500000000) ≤ ((3420386563572807 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (6949:ℚ) := by decide +kernel
  have hratR : ((((428101217511613 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((3420386563572807 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6949:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_892 : ((((6858467271247533 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6959 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6949 < q → q < 6959 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6959).mp (by decide +kernel))) hgap
  have hprev := thV_891
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6959:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6858467271247533 : ℚ) / 1000000000000) ≤ ((428101217511613 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (6959:ℚ) := by decide +kernel
  have hratR : ((((6858467271247533 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((428101217511613 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6959:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_893 : ((((3433657674832791 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6961 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6959 < q → q < 6961 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6961).mp (by decide +kernel))) hgap
  have hprev := thV_892
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6961:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3433657674832791 : ℚ) / 500000000000) ≤ ((6858467271247533 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (6961:ℚ) := by decide +kernel
  have hratR : ((((3433657674832791 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((6858467271247533 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6961:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_894 : ((((1719041072414373 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6967 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6961 < q → q < 6967 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6967).mp (by decide +kernel))) hgap
  have hprev := thV_893
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6967:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1719041072414373 : ℚ) / 250000000000) ≤ ((3433657674832791 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (6967:ℚ) := by decide +kernel
  have hratR : ((((1719041072414373 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((3433657674832791 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6967:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_895 : ((((6885013803619859 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6971 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6967 < q → q < 6971 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6971).mp (by decide +kernel))) hgap
  have hprev := thV_894
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6971:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6885013803619859 : ℚ) / 1000000000000) ≤ ((1719041072414373 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (6971:ℚ) := by decide +kernel
  have hratR : ((((6885013803619859 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1719041072414373 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6971:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_896 : ((((3446932088960339 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6977 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6971 < q → q < 6977 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6977).mp (by decide +kernel))) hgap
  have hprev := thV_895
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6977:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3446932088960339 : ℚ) / 500000000000) ≤ ((6885013803619859 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (6977:ℚ) := by decide +kernel
  have hratR : ((((3446932088960339 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((6885013803619859 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6977:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_897 : ((((1725678852955101 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6983 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6977 < q → q < 6983 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6983).mp (by decide +kernel))) hgap
  have hprev := thV_896
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6983:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1725678852955101 : ℚ) / 250000000000) ≤ ((3446932088960339 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (6983:ℚ) := by decide +kernel
  have hratR : ((((1725678852955101 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((3446932088960339 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6983:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_898 : ((((1727891947675949 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6991 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6983 < q → q < 6991 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6991).mp (by decide +kernel))) hgap
  have hprev := thV_897
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6991:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1727891947675949 : ℚ) / 250000000000) ≤ ((1725678852955101 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (6991:ℚ) := by decide +kernel
  have hratR : ((((1727891947675949 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((1725678852955101 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6991:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_899 : ((((3460210513732711 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((6997 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6991 < q → q < 6997 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6997).mp (by decide +kernel))) hgap
  have hprev := thV_898
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (6997:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3460210513732711 : ℚ) / 500000000000) ≤ ((1727891947675949 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (6997:ℚ) := by decide +kernel
  have hratR : ((((3460210513732711 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1727891947675949 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (6997:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)

end

end Work.RHContract.RegionI
