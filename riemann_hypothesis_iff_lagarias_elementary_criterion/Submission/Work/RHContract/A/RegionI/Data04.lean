import Mathlib
import Submission.Work.RHContract.A.RegionI.Data03

open scoped BigOperators

namespace Work.RHContract.RegionI

noncomputable section

lemma thV_2700 : ((((24197343413450167 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24317 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24281 < q → q < 24317 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24317).mp (by decide +kernel))) hgap
  have hprev := thV_2699
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24317:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((24197343413450167 : ℚ) / 1000000000000) ≤ ((24187244482480599 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (24317:ℚ) := by decide +kernel
  have hratR : ((((24197343413450167 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((24187244482480599 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24317:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2701 : ((((24207442837779939 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24329 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24317 < q → q < 24329 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24329).mp (by decide +kernel))) hgap
  have hprev := thV_2700
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24329:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((24207442837779939 : ℚ) / 1000000000000) ≤ ((24197343413450167 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (24329:ℚ) := by decide +kernel
  have hratR : ((((24207442837779939 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((24197343413450167 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24329:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2702 : ((((24217542590881341 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24337 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24329 < q → q < 24337 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24337).mp (by decide +kernel))) hgap
  have hprev := thV_2701
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24337:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((24217542590881341 : ℚ) / 1000000000000) ≤ ((24207442837779939 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (24337:ℚ) := by decide +kernel
  have hratR : ((((24217542590881341 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((24207442837779939 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24337:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2703 : ((((24227643247547779 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24359 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24337 < q → q < 24359 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24359).mp (by decide +kernel))) hgap
  have hprev := thV_2702
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24359:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((24227643247547779 : ℚ) / 1000000000000) ≤ ((24217542590881341 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (24359:ℚ) := by decide +kernel
  have hratR : ((((24227643247547779 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((24217542590881341 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24359:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2704 : ((((969509775868959 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24371 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24359 < q → q < 24371 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24371).mp (by decide +kernel))) hgap
  have hprev := thV_2703
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24371:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((969509775868959 : ℚ) / 40000000000) ≤ ((24227643247547779 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (24371:ℚ) := by decide +kernel
  have hratR : ((((969509775868959 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((24227643247547779 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24371:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2705 : ((((24247845627961553 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24373 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24371 < q → q < 24373 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24373).mp (by decide +kernel))) hgap
  have hprev := thV_2704
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24373:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((24247845627961553 : ℚ) / 1000000000000) ≤ ((969509775868959 : ℚ) / 40000000000) + Work.RHContract.RegionI.logLowQ (24373:ℚ) := by decide +kernel
  have hratR : ((((24247845627961553 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((969509775868959 : ℚ) / 40000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24373:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2706 : ((((151612169408393 : ℚ) / 6250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24379 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24373 < q → q < 24379 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24379).mp (by decide +kernel))) hgap
  have hprev := thV_2705
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24379:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((151612169408393 : ℚ) / 6250000000) ≤ ((24247845627961553 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (24379:ℚ) := by decide +kernel
  have hratR : ((((151612169408393 : ℚ) / 6250000000) : ℚ) : ℝ) ≤ ((((24247845627961553 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24379:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2707 : ((((1213402453741501 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24391 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24379 < q → q < 24391 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24391).mp (by decide +kernel))) hgap
  have hprev := thV_2706
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24391:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1213402453741501 : ℚ) / 50000000000) ≤ ((151612169408393 : ℚ) / 6250000000) + Work.RHContract.RegionI.logLowQ (24391:ℚ) := by decide +kernel
  have hratR : ((((1213402453741501 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((151612169408393 : ℚ) / 6250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24391:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2708 : ((((6069537925020441 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24407 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24391 < q → q < 24407 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24407).mp (by decide +kernel))) hgap
  have hprev := thV_2707
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24407:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6069537925020441 : ℚ) / 250000000000) ≤ ((1213402453741501 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (24407:ℚ) := by decide +kernel
  have hratR : ((((6069537925020441 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((1213402453741501 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24407:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2709 : ((((2428825457113441 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24413 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24407 < q → q < 24413 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24413).mp (by decide +kernel))) hgap
  have hprev := thV_2708
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24413:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2428825457113441 : ℚ) / 100000000000) ≤ ((6069537925020441 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (24413:ℚ) := by decide +kernel
  have hratR : ((((2428825457113441 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((6069537925020441 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24413:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2710 : ((((6074589421981889 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24419 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24413 < q → q < 24419 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24419).mp (by decide +kernel))) hgap
  have hprev := thV_2709
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24419:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6074589421981889 : ℚ) / 250000000000) ≤ ((2428825457113441 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (24419:ℚ) := by decide +kernel
  have hratR : ((((6074589421981889 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((2428825457113441 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24419:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2711 : ((((24308460886620783 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24421 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24419 < q → q < 24421 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24421).mp (by decide +kernel))) hgap
  have hprev := thV_2710
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24421:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((24308460886620783 : ℚ) / 1000000000000) ≤ ((6074589421981889 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (24421:ℚ) := by decide +kernel
  have hratR : ((((24308460886620783 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((6074589421981889 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24421:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2712 : ((((24318564822113061 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24439 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24421 < q → q < 24439 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24439).mp (by decide +kernel))) hgap
  have hprev := thV_2711
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24439:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((24318564822113061 : ℚ) / 1000000000000) ≤ ((24308460886620783 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (24439:ℚ) := by decide +kernel
  have hratR : ((((24318564822113061 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((24308460886620783 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24439:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2713 : ((((4865733784252953 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24443 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24439 < q → q < 24443 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24443).mp (by decide +kernel))) hgap
  have hprev := thV_2712
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24443:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4865733784252953 : ℚ) / 200000000000) ≤ ((24318564822113061 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (24443:ℚ) := by decide +kernel
  have hratR : ((((4865733784252953 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((24318564822113061 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24443:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2714 : ((((608469352088759 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24469 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24443 < q → q < 24469 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24469).mp (by decide +kernel))) hgap
  have hprev := thV_2713
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24469:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((608469352088759 : ℚ) / 25000000000) ≤ ((4865733784252953 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (24469:ℚ) := by decide +kernel
  have hratR : ((((608469352088759 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((4865733784252953 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24469:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2715 : ((((24348879409294743 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24473 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24469 < q → q < 24473 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24473).mp (by decide +kernel))) hgap
  have hprev := thV_2714
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24473:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((24348879409294743 : ℚ) / 1000000000000) ≤ ((608469352088759 : ℚ) / 25000000000) + Work.RHContract.RegionI.logLowQ (24473:ℚ) := by decide +kernel
  have hratR : ((((24348879409294743 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((608469352088759 : ℚ) / 25000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24473:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2716 : ((((3044873132734571 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24481 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24473 < q → q < 24481 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24481).mp (by decide +kernel))) hgap
  have hprev := thV_2715
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24481:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3044873132734571 : ℚ) / 125000000000) ≤ ((24348879409294743 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (24481:ℚ) := by decide +kernel
  have hratR : ((((3044873132734571 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((24348879409294743 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24481:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2717 : ((((12184545724726151 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24499 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24481 < q → q < 24499 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24499).mp (by decide +kernel))) hgap
  have hprev := thV_2716
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24499:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12184545724726151 : ℚ) / 500000000000) ≤ ((3044873132734571 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (24499:ℚ) := by decide +kernel
  have hratR : ((((12184545724726151 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((3044873132734571 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24499:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2718 : ((((12189599122562339 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24509 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24499 < q → q < 24509 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24509).mp (by decide +kernel))) hgap
  have hprev := thV_2717
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24509:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12189599122562339 : ℚ) / 500000000000) ≤ ((12184545724726151 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (24509:ℚ) := by decide +kernel
  have hratR : ((((12189599122562339 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((12184545724726151 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24509:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2719 : ((((48778610734309 : ℚ) / 2000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24517 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24509 < q → q < 24517 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24517).mp (by decide +kernel))) hgap
  have hprev := thV_2718
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24517:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((48778610734309 : ℚ) / 2000000000) ≤ ((12189599122562339 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (24517:ℚ) := by decide +kernel
  have hratR : ((((48778610734309 : ℚ) / 2000000000) : ℚ) : ℝ) ≤ ((((12189599122562339 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24517:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2720 : ((((762481653030669 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24527 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24517 < q → q < 24527 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24527).mp (by decide +kernel))) hgap
  have hprev := thV_2719
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24527:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((762481653030669 : ℚ) / 31250000000) ≤ ((48778610734309 : ℚ) / 2000000000) + Work.RHContract.RegionI.logLowQ (24527:ℚ) := by decide +kernel
  have hratR : ((((762481653030669 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((48778610734309 : ℚ) / 2000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24527:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2721 : ((((1525595041962923 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24533 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24527 < q → q < 24533 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24533).mp (by decide +kernel))) hgap
  have hprev := thV_2720
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24533:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1525595041962923 : ℚ) / 62500000000) ≤ ((762481653030669 : ℚ) / 31250000000) + Work.RHContract.RegionI.logLowQ (24533:ℚ) := by decide +kernel
  have hratR : ((((1525595041962923 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((762481653030669 : ℚ) / 31250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24533:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2722 : ((((24419629016329291 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24547 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24533 < q → q < 24547 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24547).mp (by decide +kernel))) hgap
  have hprev := thV_2721
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24547:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((24419629016329291 : ℚ) / 1000000000000) ≤ ((1525595041962923 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (24547:ℚ) := by decide +kernel
  have hratR : ((((24419629016329291 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1525595041962923 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24547:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2723 : ((((12214868762095621 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24551 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24547 < q → q < 24551 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24551).mp (by decide +kernel))) hgap
  have hprev := thV_2722
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24551:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12214868762095621 : ℚ) / 500000000000) ≤ ((24419629016329291 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (24551:ℚ) := by decide +kernel
  have hratR : ((((12214868762095621 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((24419629016329291 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24551:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2724 : ((((2443984684635233 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24571 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24551 < q → q < 24571 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24571).mp (by decide +kernel))) hgap
  have hprev := thV_2723
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24571:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2443984684635233 : ℚ) / 100000000000) ≤ ((12214868762095621 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (24571:ℚ) := by decide +kernel
  have hratR : ((((2443984684635233 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((12214868762095621 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24571:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2725 : ((((3056244632934659 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24593 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24571 < q → q < 24593 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24593).mp (by decide +kernel))) hgap
  have hprev := thV_2724
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24593:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3056244632934659 : ℚ) / 125000000000) ≤ ((2443984684635233 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (24593:ℚ) := by decide +kernel
  have hratR : ((((3056244632934659 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((2443984684635233 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24593:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2726 : ((((152875425076563 : ℚ) / 6250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24611 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24593 < q → q < 24611 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24611).mp (by decide +kernel))) hgap
  have hprev := thV_2725
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24611:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((152875425076563 : ℚ) / 6250000000) ≤ ((3056244632934659 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (24611:ℚ) := by decide +kernel
  have hratR : ((((152875425076563 : ℚ) / 6250000000) : ℚ) : ℝ) ≤ ((((3056244632934659 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24611:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2727 : ((((6117544862122727 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24623 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24611 < q → q < 24623 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24623).mp (by decide +kernel))) hgap
  have hprev := thV_2726
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24623:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6117544862122727 : ℚ) / 250000000000) ≤ ((152875425076563 : ℚ) / 6250000000) + Work.RHContract.RegionI.logLowQ (24623:ℚ) := by decide +kernel
  have hratR : ((((6117544862122727 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((152875425076563 : ℚ) / 6250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24623:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2728 : ((((6120072802394613 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24631 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24623 < q → q < 24631 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24631).mp (by decide +kernel))) hgap
  have hprev := thV_2727
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24631:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6120072802394613 : ℚ) / 250000000000) ≤ ((6117544862122727 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (24631:ℚ) := by decide +kernel
  have hratR : ((((6120072802394613 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((6117544862122727 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24631:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2729 : ((((3061300513349901 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24659 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24631 < q → q < 24659 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24659).mp (by decide +kernel))) hgap
  have hprev := thV_2728
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24659:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3061300513349901 : ℚ) / 125000000000) ≤ ((6120072802394613 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (24659:ℚ) := by decide +kernel
  have hratR : ((((3061300513349901 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((6120072802394613 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24659:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2730 : ((((24500517490539333 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24671 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24659 < q → q < 24671 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24671).mp (by decide +kernel))) hgap
  have hprev := thV_2729
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24671:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((24500517490539333 : ℚ) / 1000000000000) ≤ ((3061300513349901 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (24671:ℚ) := by decide +kernel
  have hratR : ((((24500517490539333 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3061300513349901 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24671:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2731 : ((((3063828889681301 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24677 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24671 < q → q < 24677 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24677).mp (by decide +kernel))) hgap
  have hprev := thV_2730
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24677:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3063828889681301 : ℚ) / 125000000000) ≤ ((24500517490539333 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (24677:ℚ) := by decide +kernel
  have hratR : ((((3063828889681301 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((24500517490539333 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24677:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2732 : ((((6130186246868329 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24683 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24677 < q → q < 24683 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24683).mp (by decide +kernel))) hgap
  have hprev := thV_2731
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24683:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6130186246868329 : ℚ) / 250000000000) ≤ ((3063828889681301 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (24683:ℚ) := by decide +kernel
  have hratR : ((((6130186246868329 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((3063828889681301 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24683:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2733 : ((((24530859181553423 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24691 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24683 < q → q < 24691 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24691).mp (by decide +kernel))) hgap
  have hprev := thV_2732
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24691:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((24530859181553423 : ℚ) / 1000000000000) ≤ ((6130186246868329 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (24691:ℚ) := by decide +kernel
  have hratR : ((((24530859181553423 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((6130186246868329 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24691:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2734 : ((((24540973618607533 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24697 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24691 < q → q < 24697 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24697).mp (by decide +kernel))) hgap
  have hprev := thV_2733
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24697:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((24540973618607533 : ℚ) / 1000000000000) ≤ ((24530859181553423 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (24697:ℚ) := by decide +kernel
  have hratR : ((((24540973618607533 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((24530859181553423 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24697:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2735 : ((((24551088541432611 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24709 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24697 < q → q < 24709 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24709).mp (by decide +kernel))) hgap
  have hprev := thV_2734
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24709:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((24551088541432611 : ℚ) / 1000000000000) ≤ ((24540973618607533 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (24709:ℚ) := by decide +kernel
  have hratR : ((((24551088541432611 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((24540973618607533 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24709:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2736 : ((((24561204435092279 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24733 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24709 < q → q < 24733 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24733).mp (by decide +kernel))) hgap
  have hprev := thV_2735
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24733:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((24561204435092279 : ℚ) / 1000000000000) ≤ ((24551088541432611 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (24733:ℚ) := by decide +kernel
  have hratR : ((((24561204435092279 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((24551088541432611 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24733:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2737 : ((((24571320975451779 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24749 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24733 < q → q < 24749 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24749).mp (by decide +kernel))) hgap
  have hprev := thV_2736
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24749:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((24571320975451779 : ℚ) / 1000000000000) ≤ ((24561204435092279 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (24749:ℚ) := by decide +kernel
  have hratR : ((((24571320975451779 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((24561204435092279 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24749:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2738 : ((((4916287616266153 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24763 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24749 < q → q < 24763 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24763).mp (by decide +kernel))) hgap
  have hprev := thV_2737
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24763:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4916287616266153 : ℚ) / 200000000000) ≤ ((24571320975451779 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (24763:ℚ) := by decide +kernel
  have hratR : ((((4916287616266153 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((24571320975451779 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24763:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2739 : ((((24591555348728023 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24767 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24763 < q → q < 24767 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24767).mp (by decide +kernel))) hgap
  have hprev := thV_2738
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24767:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((24591555348728023 : ℚ) / 1000000000000) ≤ ((4916287616266153 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (24767:ℚ) := by decide +kernel
  have hratR : ((((24591555348728023 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4916287616266153 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24767:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2740 : ((((24601673181233877 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24781 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24767 < q → q < 24781 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24781).mp (by decide +kernel))) hgap
  have hprev := thV_2739
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24781:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((24601673181233877 : ℚ) / 1000000000000) ≤ ((24591555348728023 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (24781:ℚ) := by decide +kernel
  have hratR : ((((24601673181233877 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((24591555348728023 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24781:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2741 : ((((6152947874466121 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24793 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24781 < q → q < 24793 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24793).mp (by decide +kernel))) hgap
  have hprev := thV_2740
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24793:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6152947874466121 : ℚ) / 250000000000) ≤ ((24601673181233877 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (24793:ℚ) := by decide +kernel
  have hratR : ((((6152947874466121 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((24601673181233877 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24793:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2742 : ((((6155477514117401 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24799 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24793 < q → q < 24799 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24799).mp (by decide +kernel))) hgap
  have hprev := thV_2741
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24799:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6155477514117401 : ℚ) / 250000000000) ≤ ((6152947874466121 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (24799:ℚ) := by decide +kernel
  have hratR : ((((6155477514117401 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((6152947874466121 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24799:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2743 : ((((2463202901823551 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24809 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24799 < q → q < 24809 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24809).mp (by decide +kernel))) hgap
  have hprev := thV_2742
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24809:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2463202901823551 : ℚ) / 100000000000) ≤ ((6155477514117401 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (24809:ℚ) := by decide +kernel
  have hratR : ((((2463202901823551 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((6155477514117401 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24809:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2744 : ((((12321074231789953 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24821 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24809 < q → q < 24821 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24821).mp (by decide +kernel))) hgap
  have hprev := thV_2743
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24821:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12321074231789953 : ℚ) / 500000000000) ≤ ((2463202901823551 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (24821:ℚ) := by decide +kernel
  have hratR : ((((12321074231789953 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((2463202901823551 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24821:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2745 : ((((192595849331009 : ℚ) / 7812500000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24841 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24821 < q → q < 24841 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24841).mp (by decide +kernel))) hgap
  have hprev := thV_2744
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24841:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((192595849331009 : ℚ) / 7812500000) ≤ ((12321074231789953 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (24841:ℚ) := by decide +kernel
  have hratR : ((((192595849331009 : ℚ) / 7812500000) : ℚ) : ℝ) ≤ ((((12321074231789953 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24841:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2746 : ((((24662389206665403 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24847 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24841 < q → q < 24847 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24847).mp (by decide +kernel))) hgap
  have hprev := thV_2745
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24847:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((24662389206665403 : ℚ) / 1000000000000) ≤ ((192595849331009 : ℚ) / 7812500000) + Work.RHContract.RegionI.logLowQ (24847:ℚ) := by decide +kernel
  have hratR : ((((24662389206665403 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((192595849331009 : ℚ) / 7812500000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24847:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2747 : ((((24672509859933927 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24851 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24847 < q → q < 24851 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24851).mp (by decide +kernel))) hgap
  have hprev := thV_2746
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24851:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((24672509859933927 : ℚ) / 1000000000000) ≤ ((24662389206665403 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (24851:ℚ) := by decide +kernel
  have hratR : ((((24672509859933927 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((24662389206665403 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24851:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2748 : ((((24682630835069281 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24859 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24851 < q → q < 24859 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24859).mp (by decide +kernel))) hgap
  have hprev := thV_2747
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24859:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((24682630835069281 : ℚ) / 1000000000000) ≤ ((24672509859933927 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (24859:ℚ) := by decide +kernel
  have hratR : ((((24682630835069281 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((24672509859933927 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24859:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2749 : ((((12346376267013223 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24877 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24859 < q → q < 24877 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24877).mp (by decide +kernel))) hgap
  have hprev := thV_2748
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24877:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12346376267013223 : ℚ) / 500000000000) ≤ ((24682630835069281 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (24877:ℚ) := by decide +kernel
  have hratR : ((((12346376267013223 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((24682630835069281 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24877:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2750 : ((((24702874715240583 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24889 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24877 < q → q < 24889 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24889).mp (by decide +kernel))) hgap
  have hprev := thV_2749
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24889:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((24702874715240583 : ℚ) / 1000000000000) ≤ ((12346376267013223 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (24889:ℚ) := by decide +kernel
  have hratR : ((((24702874715240583 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((12346376267013223 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24889:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2751 : ((((12356498809702193 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24907 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24889 < q → q < 24907 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24907).mp (by decide +kernel))) hgap
  have hprev := thV_2750
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24907:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12356498809702193 : ℚ) / 500000000000) ≤ ((24702874715240583 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (24907:ℚ) := by decide +kernel
  have hratR : ((((12356498809702193 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((24702874715240583 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24907:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2752 : ((((1545195057811323 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24917 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24907 < q → q < 24917 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24917).mp (by decide +kernel))) hgap
  have hprev := thV_2751
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24917:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1545195057811323 : ℚ) / 62500000000) ≤ ((12356498809702193 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (24917:ℚ) := by decide +kernel
  have hratR : ((((1545195057811323 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((12356498809702193 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24917:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2753 : ((((12366622155410607 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24919 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24917 < q → q < 24919 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24919).mp (by decide +kernel))) hgap
  have hprev := thV_2752
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24919:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12366622155410607 : ℚ) / 500000000000) ≤ ((1545195057811323 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (24919:ℚ) := by decide +kernel
  have hratR : ((((12366622155410607 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1545195057811323 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24919:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2754 : ((((24743367857168463 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24923 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24919 < q → q < 24923 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24923).mp (by decide +kernel))) hgap
  have hprev := thV_2753
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24923:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((24743367857168463 : ℚ) / 1000000000000) ≤ ((12366622155410607 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (24923:ℚ) := by decide +kernel
  have hratR : ((((24743367857168463 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((12366622155410607 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24923:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2755 : ((((6188373051416379 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24943 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24923 < q → q < 24943 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24943).mp (by decide +kernel))) hgap
  have hprev := thV_2754
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24943:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6188373051416379 : ℚ) / 250000000000) ≤ ((24743367857168463 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (24943:ℚ) := by decide +kernel
  have hratR : ((((6188373051416379 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((24743367857168463 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24943:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2756 : ((((24763616954996309 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24953 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24943 < q → q < 24953 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24953).mp (by decide +kernel))) hgap
  have hprev := thV_2755
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24953:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((24763616954996309 : ℚ) / 1000000000000) ≤ ((6188373051416379 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (24953:ℚ) := by decide +kernel
  have hratR : ((((24763616954996309 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((6188373051416379 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24953:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2757 : ((((3096717783153069 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24967 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24953 < q → q < 24967 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24967).mp (by decide +kernel))) hgap
  have hprev := thV_2756
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24967:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3096717783153069 : ℚ) / 125000000000) ≤ ((24763616954996309 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (24967:ℚ) := by decide +kernel
  have hratR : ((((3096717783153069 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((24763616954996309 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24967:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2758 : ((((12391933867825721 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24971 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24967 < q → q < 24971 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24971).mp (by decide +kernel))) hgap
  have hprev := thV_2757
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24971:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12391933867825721 : ℚ) / 500000000000) ≤ ((3096717783153069 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (24971:ℚ) := by decide +kernel
  have hratR : ((((12391933867825721 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((3096717783153069 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24971:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2759 : ((((24793993446328193 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24977 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24971 < q → q < 24977 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24977).mp (by decide +kernel))) hgap
  have hprev := thV_2758
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24977:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((24793993446328193 : ℚ) / 1000000000000) ≤ ((12391933867825721 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (24977:ℚ) := by decide +kernel
  have hratR : ((((24793993446328193 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((12391933867825721 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24977:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2760 : ((((12402059618537703 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24979 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24977 < q → q < 24979 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24979).mp (by decide +kernel))) hgap
  have hprev := thV_2759
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24979:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12402059618537703 : ℚ) / 500000000000) ≤ ((24793993446328193 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (24979:ℚ) := by decide +kernel
  have hratR : ((((12402059618537703 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((24793993446328193 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24979:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2761 : ((((6203561357019697 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24989 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24979 < q → q < 24989 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24989).mp (by decide +kernel))) hgap
  have hprev := thV_2760
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24989:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6203561357019697 : ℚ) / 250000000000) ≤ ((12402059618537703 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (24989:ℚ) := by decide +kernel
  have hratR : ((((6203561357019697 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((12402059618537703 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24989:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2762 : ((((4964874515808769 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25013 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24989 < q → q < 25013 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25013).mp (by decide +kernel))) hgap
  have hprev := thV_2761
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25013:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4964874515808769 : ℚ) / 200000000000) ≤ ((6203561357019697 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (25013:ℚ) := by decide +kernel
  have hratR : ((((4964874515808769 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((6203561357019697 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25013:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2763 : ((((24834500449375891 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25031 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25013 < q → q < 25031 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25031).mp (by decide +kernel))) hgap
  have hprev := thV_2762
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25031:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((24834500449375891 : ℚ) / 1000000000000) ≤ ((4964874515808769 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (25031:ℚ) := by decide +kernel
  have hratR : ((((24834500449375891 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4964874515808769 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25031:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2764 : ((((6211157099901417 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25033 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25031 < q → q < 25033 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25033).mp (by decide +kernel))) hgap
  have hprev := thV_2763
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25033:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6211157099901417 : ℚ) / 250000000000) ≤ ((24834500449375891 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (25033:ℚ) := by decide +kernel
  have hratR : ((((6211157099901417 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((24834500449375891 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25033:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2765 : ((((12427378254805879 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25037 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25033 < q → q < 25037 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25037).mp (by decide +kernel))) hgap
  have hprev := thV_2764
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25037:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12427378254805879 : ℚ) / 500000000000) ≤ ((6211157099901417 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (25037:ℚ) := by decide +kernel
  have hratR : ((((12427378254805879 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((6211157099901417 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25037:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2766 : ((((24864885418116713 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25057 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25037 < q → q < 25057 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25057).mp (by decide +kernel))) hgap
  have hprev := thV_2765
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25057:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((24864885418116713 : ℚ) / 1000000000000) ≤ ((12427378254805879 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (25057:ℚ) := by decide +kernel
  have hratR : ((((24864885418116713 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((12427378254805879 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25057:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2767 : ((((4975002992992401 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25073 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25057 < q → q < 25073 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25073).mp (by decide +kernel))) hgap
  have hprev := thV_2766
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25073:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4975002992992401 : ℚ) / 200000000000) ≤ ((24864885418116713 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (25073:ℚ) := by decide +kernel
  have hratR : ((((4975002992992401 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((24864885418116713 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25073:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2768 : ((((24885145070021027 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25087 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25073 < q → q < 25087 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25087).mp (by decide +kernel))) hgap
  have hprev := thV_2767
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25087:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((24885145070021027 : ℚ) / 1000000000000) ≤ ((4975002992992401 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (25087:ℚ) := by decide +kernel
  have hratR : ((((24885145070021027 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4975002992992401 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25087:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2769 : ((((24895275573613451 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25097 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25087 < q → q < 25097 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25097).mp (by decide +kernel))) hgap
  have hprev := thV_2768
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25097:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((24895275573613451 : ℚ) / 1000000000000) ≤ ((24885145070021027 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (25097:ℚ) := by decide +kernel
  have hratR : ((((24895275573613451 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((24885145070021027 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25097:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2770 : ((((24905406634885941 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25111 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25097 < q → q < 25111 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25111).mp (by decide +kernel))) hgap
  have hprev := thV_2769
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25111:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((24905406634885941 : ℚ) / 1000000000000) ≤ ((24895275573613451 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (25111:ℚ) := by decide +kernel
  have hratR : ((((24905406634885941 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((24895275573613451 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25111:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2771 : ((((24915537935069 : ℚ) / 1000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25117 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25111 < q → q < 25117 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25117).mp (by decide +kernel))) hgap
  have hprev := thV_2770
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25117:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((24915537935069 : ℚ) / 1000000000) ≤ ((24905406634885941 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (25117:ℚ) := by decide +kernel
  have hratR : ((((24915537935069 : ℚ) / 1000000000) : ℚ) : ℝ) ≤ ((((24905406634885941 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25117:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2772 : ((((24925669394494067 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25121 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25117 < q → q < 25121 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25121).mp (by decide +kernel))) hgap
  have hprev := thV_2771
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25121:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((24925669394494067 : ℚ) / 1000000000000) ≤ ((24915537935069 : ℚ) / 1000000000) + Work.RHContract.RegionI.logLowQ (25121:ℚ) := by decide +kernel
  have hratR : ((((24925669394494067 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((24915537935069 : ℚ) / 1000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25121:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2773 : ((((24935801092734611 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25127 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25121 < q → q < 25127 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25127).mp (by decide +kernel))) hgap
  have hprev := thV_2772
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25127:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((24935801092734611 : ℚ) / 1000000000000) ≤ ((24925669394494067 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (25127:ℚ) := by decide +kernel
  have hratR : ((((24935801092734611 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((24925669394494067 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25127:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2774 : ((((2494593358661509 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25147 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25127 < q → q < 25147 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25147).mp (by decide +kernel))) hgap
  have hprev := thV_2773
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25147:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2494593358661509 : ℚ) / 100000000000) ≤ ((24935801092734611 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (25147:ℚ) := by decide +kernel
  have hratR : ((((2494593358661509 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((24935801092734611 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25147:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2775 : ((((24956066319064159 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25153 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25147 < q → q < 25153 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25153).mp (by decide +kernel))) hgap
  have hprev := thV_2774
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25153:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((24956066319064159 : ℚ) / 1000000000000) ≤ ((2494593358661509 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (25153:ℚ) := by decide +kernel
  have hratR : ((((24956066319064159 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2494593358661509 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25153:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2776 : ((((24966199449001109 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25163 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25153 < q → q < 25163 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25163).mp (by decide +kernel))) hgap
  have hprev := thV_2775
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25163:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((24966199449001109 : ℚ) / 1000000000000) ≤ ((24956066319064159 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (25163:ℚ) := by decide +kernel
  have hratR : ((((24966199449001109 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((24956066319064159 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25163:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2777 : ((((6244083204338743 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25169 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25163 < q → q < 25169 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25169).mp (by decide +kernel))) hgap
  have hprev := thV_2776
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25169:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6244083204338743 : ℚ) / 250000000000) ≤ ((24966199449001109 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (25169:ℚ) := by decide +kernel
  have hratR : ((((6244083204338743 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((24966199449001109 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25169:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2778 : ((((2498646626516851 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25171 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25169 < q → q < 25171 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25171).mp (by decide +kernel))) hgap
  have hprev := thV_2777
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25171:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2498646626516851 : ℚ) / 100000000000) ≤ ((6244083204338743 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (25171:ℚ) := by decide +kernel
  have hratR : ((((2498646626516851 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((6244083204338743 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25171:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2779 : ((((6249150047401887 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25183 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25171 < q → q < 25183 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25183).mp (by decide +kernel))) hgap
  have hprev := thV_2778
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25183:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6249150047401887 : ℚ) / 250000000000) ≤ ((2498646626516851 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (25183:ℚ) := by decide +kernel
  have hratR : ((((6249150047401887 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((2498646626516851 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25183:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2780 : ((((12503367176137087 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25189 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25183 < q → q < 25189 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25189).mp (by decide +kernel))) hgap
  have hprev := thV_2779
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25189:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12503367176137087 : ℚ) / 500000000000) ≤ ((6249150047401887 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (25189:ℚ) := by decide +kernel
  have hratR : ((((12503367176137087 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((6249150047401887 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25189:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2781 : ((((6254217426307049 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25219 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25189 < q → q < 25219 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25219).mp (by decide +kernel))) hgap
  have hprev := thV_2780
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25219:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6254217426307049 : ℚ) / 250000000000) ≤ ((12503367176137087 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (25219:ℚ) := by decide +kernel
  have hratR : ((((6254217426307049 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((12503367176137087 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25219:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2782 : ((((25027005454630051 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25229 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25219 < q → q < 25229 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25229).mp (by decide +kernel))) hgap
  have hprev := thV_2781
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25229:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((25027005454630051 : ℚ) / 1000000000000) ≤ ((6254217426307049 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (25229:ℚ) := by decide +kernel
  have hratR : ((((25027005454630051 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((6254217426307049 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25229:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2783 : ((((3129642690134631 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25237 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25229 < q → q < 25237 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25237).mp (by decide +kernel))) hgap
  have hprev := thV_2782
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25237:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3129642690134631 : ℚ) / 125000000000) ≤ ((25027005454630051 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (25237:ℚ) := by decide +kernel
  have hratR : ((((3129642690134631 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((25027005454630051 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25237:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2784 : ((((12523638912620977 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25243 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25237 < q → q < 25243 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25243).mp (by decide +kernel))) hgap
  have hprev := thV_2783
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25243:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12523638912620977 : ℚ) / 500000000000) ≤ ((3129642690134631 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (25243:ℚ) := by decide +kernel
  have hratR : ((((12523638912620977 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((3129642690134631 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25243:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2785 : ((((12528707143927039 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25247 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25243 < q → q < 25247 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25247).mp (by decide +kernel))) hgap
  have hprev := thV_2784
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25247:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12528707143927039 : ℚ) / 500000000000) ≤ ((12523638912620977 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (25247:ℚ) := by decide +kernel
  have hratR : ((((12528707143927039 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((12523638912620977 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25247:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2786 : ((((5013510197617993 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25253 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25247 < q → q < 25253 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25253).mp (by decide +kernel))) hgap
  have hprev := thV_2785
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25253:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5013510197617993 : ℚ) / 200000000000) ≤ ((12528707143927039 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (25253:ℚ) := by decide +kernel
  have hratR : ((((5013510197617993 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((12528707143927039 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25253:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2787 : ((((783677750158429 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25261 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25253 < q → q < 25261 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25261).mp (by decide +kernel))) hgap
  have hprev := thV_2786
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25261:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((783677750158429 : ℚ) / 31250000000) ≤ ((5013510197617993 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (25261:ℚ) := by decide +kernel
  have hratR : ((((783677750158429 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((5013510197617993 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25261:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2788 : ((((12543913302132857 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25301 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25261 < q → q < 25301 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25301).mp (by decide +kernel))) hgap
  have hprev := thV_2787
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25301:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12543913302132857 : ℚ) / 500000000000) ≤ ((783677750158429 : ℚ) / 31250000000) + Work.RHContract.RegionI.logLowQ (25301:ℚ) := by decide +kernel
  have hratR : ((((12543913302132857 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((783677750158429 : ℚ) / 31250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25301:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2789 : ((((5019593056501367 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25303 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25301 < q → q < 25303 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25303).mp (by decide +kernel))) hgap
  have hprev := thV_2788
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25303:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5019593056501367 : ℚ) / 200000000000) ≤ ((12543913302132857 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (25303:ℚ) := by decide +kernel
  have hratR : ((((5019593056501367 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((12543913302132857 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25303:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2790 : ((((6277026029704871 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25307 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25303 < q → q < 25307 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25307).mp (by decide +kernel))) hgap
  have hprev := thV_2789
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25307:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6277026029704871 : ℚ) / 250000000000) ≤ ((5019593056501367 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (25307:ℚ) := by decide +kernel
  have hratR : ((((6277026029704871 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((5019593056501367 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25307:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2791 : ((((392472547408727 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25309 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25307 < q → q < 25309 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25309).mp (by decide +kernel))) hgap
  have hprev := thV_2790
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25309:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((392472547408727 : ℚ) / 15625000000) ≤ ((6277026029704871 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (25309:ℚ) := by decide +kernel
  have hratR : ((((392472547408727 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ ((((6277026029704871 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25309:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2792 : ((((25128382423524837 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25321 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25309 < q → q < 25321 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25321).mp (by decide +kernel))) hgap
  have hprev := thV_2791
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25321:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((25128382423524837 : ℚ) / 1000000000000) ≤ ((392472547408727 : ℚ) / 15625000000) + Work.RHContract.RegionI.logLowQ (25321:ℚ) := by decide +kernel
  have hratR : ((((25128382423524837 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((392472547408727 : ℚ) / 15625000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25321:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2793 : ((((5027704504702199 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25339 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25321 < q → q < 25339 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25339).mp (by decide +kernel))) hgap
  have hprev := thV_2792
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25339:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5027704504702199 : ℚ) / 200000000000) ≤ ((25128382423524837 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (25339:ℚ) := by decide +kernel
  have hratR : ((((5027704504702199 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((25128382423524837 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25339:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2794 : ((((628716569533603 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25343 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25339 < q → q < 25343 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25343).mp (by decide +kernel))) hgap
  have hprev := thV_2793
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25343:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((628716569533603 : ℚ) / 25000000000) ≤ ((5027704504702199 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (25343:ℚ) := by decide +kernel
  have hratR : ((((628716569533603 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((5027704504702199 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25343:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2795 : ((((2515880327590099 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25349 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25343 < q → q < 25349 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25349).mp (by decide +kernel))) hgap
  have hprev := thV_2794
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25349:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2515880327590099 : ℚ) / 100000000000) ≤ ((628716569533603 : ℚ) / 25000000000) + Work.RHContract.RegionI.logLowQ (25349:ℚ) := by decide +kernel
  have hratR : ((((2515880327590099 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((628716569533603 : ℚ) / 25000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25349:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2796 : ((((12584472043001187 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25357 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25349 < q → q < 25357 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25357).mp (by decide +kernel))) hgap
  have hprev := thV_2795
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25357:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12584472043001187 : ℚ) / 500000000000) ≤ ((2515880327590099 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (25357:ℚ) := by decide +kernel
  have hratR : ((((12584472043001187 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((2515880327590099 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25357:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2797 : ((((12589542645197217 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25367 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25357 < q → q < 25367 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25367).mp (by decide +kernel))) hgap
  have hprev := thV_2796
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25367:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12589542645197217 : ℚ) / 500000000000) ≤ ((12584472043001187 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (25367:ℚ) := by decide +kernel
  have hratR : ((((12589542645197217 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((12584472043001187 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25367:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2798 : ((((12594613365643149 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25373 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25367 < q → q < 25373 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25373).mp (by decide +kernel))) hgap
  have hprev := thV_2797
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25373:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12594613365643149 : ℚ) / 500000000000) ≤ ((12589542645197217 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (25373:ℚ) := by decide +kernel
  have hratR : ((((12594613365643149 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((12589542645197217 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25373:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2799 : ((((12599684440671083 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25391 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25373 < q → q < 25391 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25391).mp (by decide +kernel))) hgap
  have hprev := thV_2798
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25391:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12599684440671083 : ℚ) / 500000000000) ≤ ((12594613365643149 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (25391:ℚ) := by decide +kernel
  have hratR : ((((12599684440671083 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((12594613365643149 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25391:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2800 : ((((25209511740059481 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25409 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25391 < q → q < 25409 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25409).mp (by decide +kernel))) hgap
  have hprev := thV_2799
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25409:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((25209511740059481 : ℚ) / 1000000000000) ≤ ((12599684440671083 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (25409:ℚ) := by decide +kernel
  have hratR : ((((25209511740059481 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((12599684440671083 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25409:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2801 : ((((12609827338742983 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25411 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25409 < q → q < 25411 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25411).mp (by decide +kernel))) hgap
  have hprev := thV_2800
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25411:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12609827338742983 : ℚ) / 500000000000) ≤ ((25209511740059481 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (25411:ℚ) := by decide +kernel
  have hratR : ((((12609827338742983 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((25209511740059481 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25411:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2802 : ((((5045959617407483 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25423 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25411 < q → q < 25423 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25423).mp (by decide +kernel))) hgap
  have hprev := thV_2801
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25423:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5045959617407483 : ℚ) / 200000000000) ≤ ((12609827338742983 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (25423:ℚ) := by decide +kernel
  have hratR : ((((5045959617407483 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((12609827338742983 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25423:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2803 : ((((25239942125742281 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25439 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25423 < q → q < 25439 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25439).mp (by decide +kernel))) hgap
  have hprev := thV_2802
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25439:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((25239942125742281 : ℚ) / 1000000000000) ≤ ((5045959617407483 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (25439:ℚ) := by decide +kernel
  have hratR : ((((25239942125742281 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5045959617407483 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25439:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2804 : ((((25250086478875479 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25447 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25439 < q → q < 25447 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25447).mp (by decide +kernel))) hgap
  have hprev := thV_2803
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25447:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((25250086478875479 : ℚ) / 1000000000000) ≤ ((25239942125742281 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (25447:ℚ) := by decide +kernel
  have hratR : ((((25250086478875479 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((25239942125742281 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25447:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2805 : ((((25260231067765063 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25453 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25447 < q → q < 25453 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25453).mp (by decide +kernel))) hgap
  have hprev := thV_2804
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25453:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((25260231067765063 : ℚ) / 1000000000000) ≤ ((25250086478875479 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (25453:ℚ) := by decide +kernel
  have hratR : ((((25260231067765063 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((25250086478875479 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25453:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2806 : ((((25270375813794699 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25457 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25453 < q → q < 25457 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25457).mp (by decide +kernel))) hgap
  have hprev := thV_2805
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25457:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((25270375813794699 : ℚ) / 1000000000000) ≤ ((25260231067765063 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (25457:ℚ) := by decide +kernel
  have hratR : ((((25270375813794699 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((25260231067765063 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25457:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2807 : ((((12640260397744061 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25463 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25457 < q → q < 25463 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25463).mp (by decide +kernel))) hgap
  have hprev := thV_2806
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25463:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12640260397744061 : ℚ) / 500000000000) ≤ ((25270375813794699 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (25463:ℚ) := by decide +kernel
  have hratR : ((((12640260397744061 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((25270375813794699 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25463:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2808 : ((((1580666625799363 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25469 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25463 < q → q < 25469 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25469).mp (by decide +kernel))) hgap
  have hprev := thV_2807
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25469:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1580666625799363 : ℚ) / 62500000000) ≤ ((12640260397744061 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (25469:ℚ) := by decide +kernel
  have hratR : ((((1580666625799363 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((12640260397744061 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25469:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2809 : ((((1581300706788453 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25471 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25469 < q → q < 25471 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25471).mp (by decide +kernel))) hgap
  have hprev := thV_2808
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25471:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1581300706788453 : ℚ) / 62500000000) ≤ ((1580666625799363 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (25471:ℚ) := by decide +kernel
  have hratR : ((((1581300706788453 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((1580666625799363 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25471:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2810 : ((((25310958643897017 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25523 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25471 < q → q < 25523 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25523).mp (by decide +kernel))) hgap
  have hprev := thV_2809
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25523:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((25310958643897017 : ℚ) / 1000000000000) ≤ ((1581300706788453 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (25523:ℚ) := by decide +kernel
  have hratR : ((((25310958643897017 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1581300706788453 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25523:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2811 : ((((25321106527553261 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25537 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25523 < q → q < 25537 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25537).mp (by decide +kernel))) hgap
  have hprev := thV_2810
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25537:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((25321106527553261 : ℚ) / 1000000000000) ≤ ((25310958643897017 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (25537:ℚ) := by decide +kernel
  have hratR : ((((25321106527553261 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((25310958643897017 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25537:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2812 : ((((25331254567832709 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25541 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25537 < q → q < 25541 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25541).mp (by decide +kernel))) hgap
  have hprev := thV_2811
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25541:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((25331254567832709 : ℚ) / 1000000000000) ≤ ((25321106527553261 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (25541:ℚ) := by decide +kernel
  have hratR : ((((25331254567832709 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((25321106527553261 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25541:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2813 : ((((12670701695430213 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25561 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25541 < q → q < 25561 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25561).mp (by decide +kernel))) hgap
  have hprev := thV_2812
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25561:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12670701695430213 : ℚ) / 500000000000) ≤ ((25331254567832709 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (25561:ℚ) := by decide +kernel
  have hratR : ((((12670701695430213 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((25331254567832709 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25561:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2814 : ((((25351552839645917 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25577 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25561 < q → q < 25577 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25577).mp (by decide +kernel))) hgap
  have hprev := thV_2813
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25577:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((25351552839645917 : ℚ) / 1000000000000) ≤ ((12670701695430213 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (25577:ℚ) := by decide +kernel
  have hratR : ((((25351552839645917 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((12670701695430213 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25577:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2815 : ((((5072340473324721 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25579 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25577 < q → q < 25579 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25579).mp (by decide +kernel))) hgap
  have hprev := thV_2814
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25579:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5072340473324721 : ℚ) / 200000000000) ≤ ((25351552839645917 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (25579:ℚ) := by decide +kernel
  have hratR : ((((5072340473324721 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((25351552839645917 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25579:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2816 : ((((12685926024983673 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25583 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25579 < q → q < 25583 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25583).mp (by decide +kernel))) hgap
  have hprev := thV_2815
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25583:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12685926024983673 : ℚ) / 500000000000) ≤ ((5072340473324721 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (25583:ℚ) := by decide +kernel
  have hratR : ((((12685926024983673 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((5072340473324721 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25583:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2817 : ((((6345500491953583 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25589 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25583 < q → q < 25589 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25589).mp (by decide +kernel))) hgap
  have hprev := thV_2816
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25589:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6345500491953583 : ℚ) / 250000000000) ≤ ((12685926024983673 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (25589:ℚ) := by decide +kernel
  have hratR : ((((6345500491953583 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((12685926024983673 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25589:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2818 : ((((25392152354502897 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25601 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25589 < q → q < 25601 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25601).mp (by decide +kernel))) hgap
  have hprev := thV_2817
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25601:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((25392152354502897 : ℚ) / 1000000000000) ≤ ((6345500491953583 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (25601:ℚ) := by decide +kernel
  have hratR : ((((25392152354502897 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((6345500491953583 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25601:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2819 : ((((25402302819310359 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25603 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25601 < q → q < 25603 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25603).mp (by decide +kernel))) hgap
  have hprev := thV_2818
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25603:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((25402302819310359 : ℚ) / 1000000000000) ≤ ((25392152354502897 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (25603:ℚ) := by decide +kernel
  have hratR : ((((25402302819310359 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((25392152354502897 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25603:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2820 : ((((25412453518437903 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25609 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25603 < q → q < 25609 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25609).mp (by decide +kernel))) hgap
  have hprev := thV_2819
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25609:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((25412453518437903 : ℚ) / 1000000000000) ≤ ((25402302819310359 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (25609:ℚ) := by decide +kernel
  have hratR : ((((25412453518437903 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((25402302819310359 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25609:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2821 : ((((25422604686040959 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25621 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25609 < q → q < 25621 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25621).mp (by decide +kernel))) hgap
  have hprev := thV_2820
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25621:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((25422604686040959 : ℚ) / 1000000000000) ≤ ((25412453518437903 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (25621:ℚ) := by decide +kernel
  have hratR : ((((25422604686040959 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((25412453518437903 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25621:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2822 : ((((25432756321900159 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25633 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25621 < q → q < 25633 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25633).mp (by decide +kernel))) hgap
  have hprev := thV_2821
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25633:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((25432756321900159 : ℚ) / 1000000000000) ≤ ((25422604686040959 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (25633:ℚ) := by decide +kernel
  have hratR : ((((25432756321900159 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((25422604686040959 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25633:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2823 : ((((25442908191805233 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25639 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25633 < q → q < 25639 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25639).mp (by decide +kernel))) hgap
  have hprev := thV_2822
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25639:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((25442908191805233 : ℚ) / 1000000000000) ≤ ((25432756321900159 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (25639:ℚ) := by decide +kernel
  have hratR : ((((25442908191805233 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((25432756321900159 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25639:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2824 : ((((198852032950863 : ℚ) / 7812500000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25643 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25639 < q → q < 25643 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25643).mp (by decide +kernel))) hgap
  have hprev := thV_2823
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25643:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((198852032950863 : ℚ) / 7812500000) ≤ ((25442908191805233 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (25643:ℚ) := by decide +kernel
  have hratR : ((((198852032950863 : ℚ) / 7812500000) : ℚ) : ℝ) ≤ ((((25442908191805233 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25643:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2825 : ((((1018528511576987 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25657 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25643 < q → q < 25657 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25657).mp (by decide +kernel))) hgap
  have hprev := thV_2824
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25657:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1018528511576987 : ℚ) / 40000000000) ≤ ((198852032950863 : ℚ) / 7812500000) + Work.RHContract.RegionI.logLowQ (25657:ℚ) := by decide +kernel
  have hratR : ((((1018528511576987 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((198852032950863 : ℚ) / 7812500000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25657:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2826 : ((((6368341437705033 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25667 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25657 < q → q < 25667 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25667).mp (by decide +kernel))) hgap
  have hprev := thV_2825
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25667:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6368341437705033 : ℚ) / 250000000000) ≤ ((1018528511576987 : ℚ) / 40000000000) + Work.RHContract.RegionI.logLowQ (25667:ℚ) := by decide +kernel
  have hratR : ((((6368341437705033 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((1018528511576987 : ℚ) / 40000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25667:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2827 : ((((6370879736487867 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25673 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25667 < q → q < 25673 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25673).mp (by decide +kernel))) hgap
  have hprev := thV_2826
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25673:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6370879736487867 : ℚ) / 250000000000) ≤ ((6368341437705033 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (25673:ℚ) := by decide +kernel
  have hratR : ((((6370879736487867 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((6368341437705033 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25673:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2828 : ((((796677261711377 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25679 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25673 < q → q < 25679 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25679).mp (by decide +kernel))) hgap
  have hprev := thV_2827
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25679:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((796677261711377 : ℚ) / 31250000000) ≤ ((6370879736487867 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (25679:ℚ) := by decide +kernel
  have hratR : ((((796677261711377 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((6370879736487867 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25679:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2829 : ((((12751913174310333 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25693 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25679 < q → q < 25693 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25693).mp (by decide +kernel))) hgap
  have hprev := thV_2828
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25693:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12751913174310333 : ℚ) / 500000000000) ≤ ((796677261711377 : ℚ) / 31250000000) + Work.RHContract.RegionI.logLowQ (25693:ℚ) := by decide +kernel
  have hratR : ((((12751913174310333 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((796677261711377 : ℚ) / 31250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25693:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2830 : ((((12756990355806307 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25703 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25693 < q → q < 25703 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25703).mp (by decide +kernel))) hgap
  have hprev := thV_2829
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25703:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12756990355806307 : ℚ) / 500000000000) ≤ ((12751913174310333 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (25703:ℚ) := by decide +kernel
  have hratR : ((((12756990355806307 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((12751913174310333 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25703:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2831 : ((((398814619049059 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25717 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25703 < q → q < 25717 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25717).mp (by decide +kernel))) hgap
  have hprev := thV_2830
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25717:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((398814619049059 : ℚ) / 15625000000) ≤ ((12756990355806307 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (25717:ℚ) := by decide +kernel
  have hratR : ((((398814619049059 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ ((((12756990355806307 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25717:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2832 : ((((25534291148630029 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25733 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25717 < q → q < 25733 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25733).mp (by decide +kernel))) hgap
  have hprev := thV_2831
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25733:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((25534291148630029 : ℚ) / 1000000000000) ≤ ((398814619049059 : ℚ) / 15625000000) + Work.RHContract.RegionI.logLowQ (25733:ℚ) := by decide +kernel
  have hratR : ((((25534291148630029 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((398814619049059 : ℚ) / 15625000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25733:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2833 : ((((3193055873619603 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25741 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25733 < q → q < 25741 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25741).mp (by decide +kernel))) hgap
  have hprev := thV_2832
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25741:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3193055873619603 : ℚ) / 125000000000) ≤ ((25534291148630029 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (25741:ℚ) := by decide +kernel
  have hratR : ((((3193055873619603 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((25534291148630029 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25741:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2834 : ((((5110920612469527 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25747 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25741 < q → q < 25747 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25747).mp (by decide +kernel))) hgap
  have hprev := thV_2833
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25747:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5110920612469527 : ℚ) / 200000000000) ≤ ((3193055873619603 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (25747:ℚ) := by decide +kernel
  have hratR : ((((5110920612469527 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((3193055873619603 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25747:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2835 : ((((798898737553237 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25759 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25747 < q → q < 25759 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25759).mp (by decide +kernel))) hgap
  have hprev := thV_2834
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25759:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((798898737553237 : ℚ) / 31250000000) ≤ ((5110920612469527 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (25759:ℚ) := by decide +kernel
  have hratR : ((((798898737553237 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((5110920612469527 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25759:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2836 : ((((25574916296333009 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25763 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25759 < q → q < 25763 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25763).mp (by decide +kernel))) hgap
  have hprev := thV_2835
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25763:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((25574916296333009 : ℚ) / 1000000000000) ≤ ((798898737553237 : ℚ) / 31250000000) + Work.RHContract.RegionI.logLowQ (25763:ℚ) := by decide +kernel
  have hratR : ((((25574916296333009 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((798898737553237 : ℚ) / 31250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25763:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2837 : ((((1023402932057483 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25771 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25763 < q → q < 25771 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25771).mp (by decide +kernel))) hgap
  have hprev := thV_2836
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25771:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1023402932057483 : ℚ) / 40000000000) ≤ ((25574916296333009 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (25771:ℚ) := by decide +kernel
  have hratR : ((((1023402932057483 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((25574916296333009 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25771:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2838 : ((((12797615579924851 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25793 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25771 < q → q < 25793 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25793).mp (by decide +kernel))) hgap
  have hprev := thV_2837
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25793:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12797615579924851 : ℚ) / 500000000000) ≤ ((1023402932057483 : ℚ) / 40000000000) + Work.RHContract.RegionI.logLowQ (25793:ℚ) := by decide +kernel
  have hratR : ((((12797615579924851 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1023402932057483 : ℚ) / 40000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25793:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2839 : ((((25605389250856531 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25799 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25793 < q → q < 25799 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25799).mp (by decide +kernel))) hgap
  have hprev := thV_2838
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25799:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((25605389250856531 : ℚ) / 1000000000000) ≤ ((12797615579924851 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (25799:ℚ) := by decide +kernel
  have hratR : ((((25605389250856531 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((12797615579924851 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25799:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2840 : ((((1280777370969137 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25801 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25799 < q → q < 25801 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25801).mp (by decide +kernel))) hgap
  have hprev := thV_2839
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25801:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1280777370969137 : ℚ) / 50000000000) ≤ ((25605389250856531 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (25801:ℚ) := by decide +kernel
  have hratR : ((((1280777370969137 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((25605389250856531 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25801:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2841 : ((((6406426571328271 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25819 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25801 < q → q < 25819 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25819).mp (by decide +kernel))) hgap
  have hprev := thV_2840
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25819:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6406426571328271 : ℚ) / 250000000000) ≤ ((1280777370969137 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (25819:ℚ) := by decide +kernel
  have hratR : ((((6406426571328271 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((1280777370969137 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25819:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2842 : ((((12817933001483141 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25841 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25819 < q → q < 25841 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25841).mp (by decide +kernel))) hgap
  have hprev := thV_2841
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25841:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12817933001483141 : ℚ) / 500000000000) ≤ ((6406426571328271 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (25841:ℚ) := by decide +kernel
  have hratR : ((((12817933001483141 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((6406426571328271 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25841:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2843 : ((((5129205190556337 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25847 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25841 < q → q < 25847 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25847).mp (by decide +kernel))) hgap
  have hprev := thV_2842
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25847:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5129205190556337 : ℚ) / 200000000000) ≤ ((12817933001483141 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (25847:ℚ) := by decide +kernel
  have hratR : ((((5129205190556337 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((12817933001483141 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25847:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2844 : ((((12828092989986257 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25849 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25847 < q → q < 25849 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25849).mp (by decide +kernel))) hgap
  have hprev := thV_2843
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25849:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12828092989986257 : ℚ) / 500000000000) ≤ ((5129205190556337 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (25849:ℚ) := by decide +kernel
  have hratR : ((((12828092989986257 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((5129205190556337 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25849:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2845 : ((((6416586675818223 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25867 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25849 < q → q < 25867 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25867).mp (by decide +kernel))) hgap
  have hprev := thV_2844
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25867:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6416586675818223 : ℚ) / 250000000000) ≤ ((12828092989986257 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (25867:ℚ) := by decide +kernel
  have hratR : ((((6416586675818223 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((12828092989986257 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25867:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2846 : ((((25676507658502147 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25873 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25867 < q → q < 25873 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25873).mp (by decide +kernel))) hgap
  have hprev := thV_2845
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25873:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((25676507658502147 : ℚ) / 1000000000000) ≤ ((6416586675818223 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (25873:ℚ) := by decide +kernel
  have hratR : ((((25676507658502147 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((6416586675818223 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25873:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2847 : ((((5137333846389111 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25889 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25873 < q → q < 25889 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25889).mp (by decide +kernel))) hgap
  have hprev := thV_2846
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25889:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5137333846389111 : ℚ) / 200000000000) ≤ ((25676507658502147 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (25889:ℚ) := by decide +kernel
  have hratR : ((((5137333846389111 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((25676507658502147 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25889:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2848 : ((((25696831346013011 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25903 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25889 < q → q < 25903 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25903).mp (by decide +kernel))) hgap
  have hprev := thV_2847
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25903:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((25696831346013011 : ℚ) / 1000000000000) ≤ ((5137333846389111 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (25903:ℚ) := by decide +kernel
  have hratR : ((((25696831346013011 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5137333846389111 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25903:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2849 : ((((6426748461515409 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25913 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25903 < q → q < 25913 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25913).mp (by decide +kernel))) hgap
  have hprev := thV_2848
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25913:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6426748461515409 : ℚ) / 250000000000) ≤ ((25696831346013011 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (25913:ℚ) := by decide +kernel
  have hratR : ((((6426748461515409 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((25696831346013011 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25913:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2850 : ((((25717156577627471 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25919 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25913 < q → q < 25919 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25919).mp (by decide +kernel))) hgap
  have hprev := thV_2849
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25919:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((25717156577627471 : ℚ) / 1000000000000) ≤ ((6426748461515409 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (25919:ℚ) := by decide +kernel
  have hratR : ((((25717156577627471 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((6426748461515409 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25919:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2851 : ((((25727319772066989 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25931 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25919 < q → q < 25931 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25931).mp (by decide +kernel))) hgap
  have hprev := thV_2850
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25931:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((25727319772066989 : ℚ) / 1000000000000) ≤ ((25717156577627471 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (25931:ℚ) := by decide +kernel
  have hratR : ((((25727319772066989 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((25717156577627471 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25931:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2852 : ((((5147496608726259 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25933 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25931 < q → q < 25933 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25933).mp (by decide +kernel))) hgap
  have hprev := thV_2851
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25933:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5147496608726259 : ℚ) / 200000000000) ≤ ((25727319772066989 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (25933:ℚ) := by decide +kernel
  have hratR : ((((5147496608726259 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((25727319772066989 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25933:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2853 : ((((25747646546534281 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25939 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25933 < q → q < 25939 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25939).mp (by decide +kernel))) hgap
  have hprev := thV_2852
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25939:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((25747646546534281 : ℚ) / 1000000000000) ≤ ((5147496608726259 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (25939:ℚ) := by decide +kernel
  have hratR : ((((25747646546534281 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5147496608726259 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25939:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2854 : ((((1609863137727083 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25943 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25939 < q → q < 25943 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25943).mp (by decide +kernel))) hgap
  have hprev := thV_2853
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25943:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1609863137727083 : ℚ) / 62500000000) ≤ ((25747646546534281 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (25943:ℚ) := by decide +kernel
  have hratR : ((((1609863137727083 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((25747646546534281 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25943:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2855 : ((((5153594833810637 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25951 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25943 < q → q < 25951 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25951).mp (by decide +kernel))) hgap
  have hprev := thV_2854
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25951:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5153594833810637 : ℚ) / 200000000000) ≤ ((1609863137727083 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (25951:ℚ) := by decide +kernel
  have hratR : ((((5153594833810637 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((1609863137727083 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25951:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2856 : ((((6444534706961873 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25969 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25951 < q → q < 25969 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25969).mp (by decide +kernel))) hgap
  have hprev := thV_2855
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25969:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6444534706961873 : ℚ) / 250000000000) ≤ ((5153594833810637 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (25969:ℚ) := by decide +kernel
  have hratR : ((((6444534706961873 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((5153594833810637 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25969:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2857 : ((((25788303948624483 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25981 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25969 < q → q < 25981 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25981).mp (by decide +kernel))) hgap
  have hprev := thV_2856
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25981:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((25788303948624483 : ℚ) / 1000000000000) ≤ ((6444534706961873 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (25981:ℚ) := by decide +kernel
  have hratR : ((((25788303948624483 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((6444534706961873 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25981:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2858 : ((((12899234842523287 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25997 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25981 < q → q < 25997 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25997).mp (by decide +kernel))) hgap
  have hprev := thV_2857
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25997:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12899234842523287 : ℚ) / 500000000000) ≤ ((25788303948624483 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (25997:ℚ) := by decide +kernel
  have hratR : ((((12899234842523287 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((25788303948624483 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25997:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2859 : ((((1290431774919883 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((25999 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25997 < q → q < 25999 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25999).mp (by decide +kernel))) hgap
  have hprev := thV_2858
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (25999:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1290431774919883 : ℚ) / 50000000000) ≤ ((12899234842523287 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (25999:ℚ) := by decide +kernel
  have hratR : ((((1290431774919883 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((12899234842523287 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (25999:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2860 : ((((25818801465588983 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26003 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 25999 < q → q < 26003 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26003).mp (by decide +kernel))) hgap
  have hprev := thV_2859
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26003:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((25818801465588983 : ℚ) / 1000000000000) ≤ ((1290431774919883 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (26003:ℚ) := by decide +kernel
  have hratR : ((((25818801465588983 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1290431774919883 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26003:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2861 : ((((6457241992758709 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26017 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26003 < q → q < 26017 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26017).mp (by decide +kernel))) hgap
  have hprev := thV_2860
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26017:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6457241992758709 : ℚ) / 250000000000) ≤ ((25818801465588983 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (26017:ℚ) := by decide +kernel
  have hratR : ((((6457241992758709 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((25818801465588983 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26017:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2862 : ((((51678269260429 : ℚ) / 2000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26021 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26017 < q → q < 26021 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26021).mp (by decide +kernel))) hgap
  have hprev := thV_2861
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26021:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((51678269260429 : ℚ) / 2000000000) ≤ ((6457241992758709 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (26021:ℚ) := by decide +kernel
  have hratR : ((((51678269260429 : ℚ) / 2000000000) : ℚ) : ℝ) ≤ ((((6457241992758709 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26021:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2863 : ((((258493015967909 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26029 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26021 < q → q < 26029 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26029).mp (by decide +kernel))) hgap
  have hprev := thV_2862
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26029:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((258493015967909 : ℚ) / 10000000000) ≤ ((51678269260429 : ℚ) / 2000000000) + Work.RHContract.RegionI.logLowQ (26029:ℚ) := by decide +kernel
  have hratR : ((((258493015967909 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ ((((51678269260429 : ℚ) / 2000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26029:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2864 : ((((25859469024285303 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26041 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26029 < q → q < 26041 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26041).mp (by decide +kernel))) hgap
  have hprev := thV_2863
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26041:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((25859469024285303 : ℚ) / 1000000000000) ≤ ((258493015967909 : ℚ) / 10000000000) + Work.RHContract.RegionI.logLowQ (26041:ℚ) := by decide +kernel
  have hratR : ((((25859469024285303 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((258493015967909 : ℚ) / 10000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26041:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2865 : ((((12934818456242681 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26053 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26041 < q → q < 26053 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26053).mp (by decide +kernel))) hgap
  have hprev := thV_2864
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26053:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12934818456242681 : ℚ) / 500000000000) ≤ ((25859469024285303 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (26053:ℚ) := by decide +kernel
  have hratR : ((((12934818456242681 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((25859469024285303 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26053:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2866 : ((((12939902975760911 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26083 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26053 < q → q < 26083 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26083).mp (by decide +kernel))) hgap
  have hprev := thV_2865
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26083:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12939902975760911 : ℚ) / 500000000000) ≤ ((12934818456242681 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (26083:ℚ) := by decide +kernel
  have hratR : ((((12939902975760911 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((12934818456242681 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26083:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2867 : ((((25889975603796583 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26099 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26083 < q → q < 26099 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26099).mp (by decide +kernel))) hgap
  have hprev := thV_2866
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26099:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((25889975603796583 : ℚ) / 1000000000000) ≤ ((12939902975760911 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (26099:ℚ) := by decide +kernel
  have hratR : ((((25889975603796583 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((12939902975760911 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26099:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2868 : ((((25900145562549529 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26107 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26099 < q → q < 26107 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26107).mp (by decide +kernel))) hgap
  have hprev := thV_2867
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26107:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((25900145562549529 : ℚ) / 1000000000000) ≤ ((25889975603796583 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (26107:ℚ) := by decide +kernel
  have hratR : ((((25900145562549529 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((25889975603796583 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26107:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2869 : ((((25910315674506351 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26111 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26107 < q → q < 26111 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26111).mp (by decide +kernel))) hgap
  have hprev := thV_2868
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26111:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((25910315674506351 : ℚ) / 1000000000000) ≤ ((25900145562549529 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (26111:ℚ) := by decide +kernel
  have hratR : ((((25910315674506351 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((25900145562549529 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26111:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2870 : ((((2592048586305631 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26113 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26111 < q → q < 26113 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26113).mp (by decide +kernel))) hgap
  have hprev := thV_2869
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26113:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2592048586305631 : ℚ) / 100000000000) ≤ ((25910315674506351 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (26113:ℚ) := by decide +kernel
  have hratR : ((((2592048586305631 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((25910315674506351 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26113:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2871 : ((((25930656281350489 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26119 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26113 < q → q < 26119 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26119).mp (by decide +kernel))) hgap
  have hprev := thV_2870
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26119:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((25930656281350489 : ℚ) / 1000000000000) ≤ ((2592048586305631 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (26119:ℚ) := by decide +kernel
  have hratR : ((((25930656281350489 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2592048586305631 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26119:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2872 : ((((25940827541588843 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26141 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26119 < q → q < 26141 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26141).mp (by decide +kernel))) hgap
  have hprev := thV_2871
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26141:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((25940827541588843 : ℚ) / 1000000000000) ≤ ((25930656281350489 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (26141:ℚ) := by decide +kernel
  have hratR : ((((25940827541588843 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((25930656281350489 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26141:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2873 : ((((2595099926077087 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26153 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26141 < q → q < 26153 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26153).mp (by decide +kernel))) hgap
  have hprev := thV_2872
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26153:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2595099926077087 : ℚ) / 100000000000) ≤ ((25940827541588843 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (26153:ℚ) := by decide +kernel
  have hratR : ((((2595099926077087 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((25940827541588843 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26153:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2874 : ((((2596117128579837 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26161 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26153 < q → q < 26161 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26161).mp (by decide +kernel))) hgap
  have hprev := thV_2873
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26161:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2596117128579837 : ℚ) / 100000000000) ≤ ((2595099926077087 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (26161:ℚ) := by decide +kernel
  have hratR : ((((2596117128579837 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((2595099926077087 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26161:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2875 : ((((25971343693001217 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26171 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26161 < q → q < 26171 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26171).mp (by decide +kernel))) hgap
  have hprev := thV_2874
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26171:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((25971343693001217 : ℚ) / 1000000000000) ≤ ((2596117128579837 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (26171:ℚ) := by decide +kernel
  have hratR : ((((25971343693001217 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2596117128579837 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26171:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2876 : ((((1623844770589949 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26177 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26171 < q → q < 26177 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26177).mp (by decide +kernel))) hgap
  have hprev := thV_2875
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26177:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1623844770589949 : ℚ) / 62500000000) ≤ ((25971343693001217 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (26177:ℚ) := by decide +kernel
  have hratR : ((((1623844770589949 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((25971343693001217 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26177:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2877 : ((((12995844597529867 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26183 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26177 < q → q < 26183 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26183).mp (by decide +kernel))) hgap
  have hprev := thV_2876
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26183:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12995844597529867 : ℚ) / 500000000000) ≤ ((1623844770589949 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (26183:ℚ) := by decide +kernel
  have hratR : ((((12995844597529867 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1623844770589949 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26183:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2878 : ((((5200372457962071 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26189 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26183 < q → q < 26189 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26189).mp (by decide +kernel))) hgap
  have hprev := thV_2877
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26189:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5200372457962071 : ℚ) / 200000000000) ≤ ((12995844597529867 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (26189:ℚ) := by decide +kernel
  have hratR : ((((5200372457962071 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((12995844597529867 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26189:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2879 : ((((13006017959496863 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26203 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26189 < q → q < 26203 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26203).mp (by decide +kernel))) hgap
  have hprev := thV_2878
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26203:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13006017959496863 : ℚ) / 500000000000) ≤ ((5200372457962071 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (26203:ℚ) := by decide +kernel
  have hratR : ((((13006017959496863 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((5200372457962071 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26203:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2880 : ((((26022209777132299 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26209 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26203 < q → q < 26209 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26209).mp (by decide +kernel))) hgap
  have hprev := thV_2879
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26209:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((26022209777132299 : ℚ) / 1000000000000) ≤ ((13006017959496863 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (26209:ℚ) := by decide +kernel
  have hratR : ((((26022209777132299 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((13006017959496863 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26209:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2881 : ((((6508096080455531 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26227 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26209 < q → q < 26227 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26227).mp (by decide +kernel))) hgap
  have hprev := thV_2880
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26227:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6508096080455531 : ℚ) / 250000000000) ≤ ((26022209777132299 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (26227:ℚ) := by decide +kernel
  have hratR : ((((6508096080455531 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((26022209777132299 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26227:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2882 : ((((13021279623862869 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26237 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26227 < q → q < 26237 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26237).mp (by decide +kernel))) hgap
  have hprev := thV_2881
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26237:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13021279623862869 : ℚ) / 500000000000) ≤ ((6508096080455531 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (26237:ℚ) := by decide +kernel
  have hratR : ((((13021279623862869 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((6508096080455531 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26237:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2883 : ((((13026367315447077 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26249 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26237 < q → q < 26249 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26249).mp (by decide +kernel))) hgap
  have hprev := thV_2882
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26249:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13026367315447077 : ℚ) / 500000000000) ≤ ((13021279623862869 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (26249:ℚ) := by decide +kernel
  have hratR : ((((13026367315447077 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((13021279623862869 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26249:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2884 : ((((26062910090253047 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26251 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26249 < q → q < 26251 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26251).mp (by decide +kernel))) hgap
  have hprev := thV_2883
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26251:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((26062910090253047 : ℚ) / 1000000000000) ≤ ((13026367315447077 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (26251:ℚ) := by decide +kernel
  have hratR : ((((26062910090253047 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((13026367315447077 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26251:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2885 : ((((2607308593047727 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26261 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26251 < q → q < 26261 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26261).mp (by decide +kernel))) hgap
  have hprev := thV_2884
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26261:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2607308593047727 : ℚ) / 100000000000) ≤ ((26062910090253047 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (26261:ℚ) := by decide +kernel
  have hratR : ((((2607308593047727 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((26062910090253047 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26261:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2886 : ((((5216652369371431 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26263 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26261 < q → q < 26263 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26263).mp (by decide +kernel))) hgap
  have hprev := thV_2885
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26263:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5216652369371431 : ℚ) / 200000000000) ≤ ((2607308593047727 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (26263:ℚ) := by decide +kernel
  have hratR : ((((5216652369371431 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((2607308593047727 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26263:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2887 : ((((3261679739441371 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26267 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26263 < q → q < 26267 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26267).mp (by decide +kernel))) hgap
  have hprev := thV_2886
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26267:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3261679739441371 : ℚ) / 125000000000) ≤ ((5216652369371431 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (26267:ℚ) := by decide +kernel
  have hratR : ((((3261679739441371 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((5216652369371431 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26267:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2888 : ((((6525903743387593 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26293 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26267 < q → q < 26293 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26293).mp (by decide +kernel))) hgap
  have hprev := thV_2887
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26293:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6525903743387593 : ℚ) / 250000000000) ≤ ((3261679739441371 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (26293:ℚ) := by decide +kernel
  have hratR : ((((6525903743387593 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((3261679739441371 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26293:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2889 : ((((26113792183689951 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26297 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26293 < q → q < 26297 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26297).mp (by decide +kernel))) hgap
  have hprev := thV_2888
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26297:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((26113792183689951 : ℚ) / 1000000000000) ≤ ((6525903743387593 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (26297:ℚ) := by decide +kernel
  have hratR : ((((26113792183689951 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((6525903743387593 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26297:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2890 : ((((26123969850051261 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26309 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26297 < q → q < 26309 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26309).mp (by decide +kernel))) hgap
  have hprev := thV_2889
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26309:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((26123969850051261 : ℚ) / 1000000000000) ≤ ((26113792183689951 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (26309:ℚ) := by decide +kernel
  have hratR : ((((26123969850051261 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((26113792183689951 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26309:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2891 : ((((26134147820444801 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26317 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26309 < q → q < 26317 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26317).mp (by decide +kernel))) hgap
  have hprev := thV_2890
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26317:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((26134147820444801 : ℚ) / 1000000000000) ≤ ((26123969850051261 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (26317:ℚ) := by decide +kernel
  have hratR : ((((26134147820444801 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((26123969850051261 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26317:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2892 : ((((130721629714099 : ℚ) / 5000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26321 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26317 < q → q < 26321 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26321).mp (by decide +kernel))) hgap
  have hprev := thV_2891
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26321:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((130721629714099 : ℚ) / 5000000000) ≤ ((26134147820444801 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (26321:ℚ) := by decide +kernel
  have hratR : ((((130721629714099 : ℚ) / 5000000000) : ℚ) : ℝ) ≤ ((((26134147820444801 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26321:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2893 : ((((5230900949765133 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26339 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26321 < q → q < 26339 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26339).mp (by decide +kernel))) hgap
  have hprev := thV_2892
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26339:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5230900949765133 : ℚ) / 200000000000) ≤ ((130721629714099 : ℚ) / 5000000000) + Work.RHContract.RegionI.logLowQ (26339:ℚ) := by decide +kernel
  have hratR : ((((5230900949765133 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((130721629714099 : ℚ) / 5000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26339:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2894 : ((((26164683858517521 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26347 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26339 < q → q < 26347 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26347).mp (by decide +kernel))) hgap
  have hprev := thV_2893
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26347:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((26164683858517521 : ℚ) / 1000000000000) ≤ ((5230900949765133 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (26347:ℚ) := by decide +kernel
  have hratR : ((((26164683858517521 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5230900949765133 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26347:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2895 : ((((1308743167384361 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26357 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26347 < q → q < 26357 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26357).mp (by decide +kernel))) hgap
  have hprev := thV_2894
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26357:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1308743167384361 : ℚ) / 50000000000) ≤ ((26164683858517521 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (26357:ℚ) := by decide +kernel
  have hratR : ((((1308743167384361 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((26164683858517521 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26357:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2896 : ((((2618504336788409 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26371 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26357 < q → q < 26371 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26371).mp (by decide +kernel))) hgap
  have hprev := thV_2895
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26371:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2618504336788409 : ℚ) / 100000000000) ≤ ((1308743167384361 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (26371:ℚ) := by decide +kernel
  have hratR : ((((2618504336788409 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((1308743167384361 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26371:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2897 : ((((13097611997312031 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26387 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26371 < q → q < 26387 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26387).mp (by decide +kernel))) hgap
  have hprev := thV_2896
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26387:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13097611997312031 : ℚ) / 500000000000) ≤ ((2618504336788409 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (26387:ℚ) := by decide +kernel
  have hratR : ((((13097611997312031 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((2618504336788409 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26387:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2898 : ((((26205404848722883 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26393 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26387 < q → q < 26393 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26393).mp (by decide +kernel))) hgap
  have hprev := thV_2897
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26393:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((26205404848722883 : ℚ) / 1000000000000) ≤ ((13097611997312031 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (26393:ℚ) := by decide +kernel
  have hratR : ((((26205404848722883 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((13097611997312031 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26393:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2899 : ((((3276948241266109 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26399 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26393 < q → q < 26399 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26399).mp (by decide +kernel))) hgap
  have hprev := thV_2898
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26399:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3276948241266109 : ℚ) / 125000000000) ≤ ((26205404848722883 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (26399:ℚ) := by decide +kernel
  have hratR : ((((3276948241266109 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((26205404848722883 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26399:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2900 : ((((5245153462906147 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26407 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26399 < q → q < 26407 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26407).mp (by decide +kernel))) hgap
  have hprev := thV_2899
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26407:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5245153462906147 : ℚ) / 200000000000) ≤ ((3276948241266109 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (26407:ℚ) := by decide +kernel
  have hratR : ((((5245153462906147 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((3276948241266109 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26407:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2901 : ((((819873408673387 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26417 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26407 < q → q < 26417 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26417).mp (by decide +kernel))) hgap
  have hprev := thV_2900
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26417:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((819873408673387 : ℚ) / 31250000000) ≤ ((5245153462906147 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (26417:ℚ) := by decide +kernel
  have hratR : ((((819873408673387 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((5245153462906147 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26417:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2902 : ((((5249226213533343 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26423 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26417 < q → q < 26423 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26423).mp (by decide +kernel))) hgap
  have hprev := thV_2901
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26423:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5249226213533343 : ℚ) / 200000000000) ≤ ((819873408673387 : ℚ) / 31250000000) + Work.RHContract.RegionI.logLowQ (26423:ℚ) := by decide +kernel
  have hratR : ((((5249226213533343 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((819873408673387 : ℚ) / 31250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26423:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2903 : ((((26256313360505751 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26431 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26423 < q → q < 26431 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26431).mp (by decide +kernel))) hgap
  have hprev := thV_2902
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26431:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((26256313360505751 : ℚ) / 1000000000000) ≤ ((5249226213533343 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (26431:ℚ) := by decide +kernel
  have hratR : ((((26256313360505751 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5249226213533343 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26431:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2904 : ((((3283311985040649 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26437 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26431 < q → q < 26437 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26437).mp (by decide +kernel))) hgap
  have hprev := thV_2903
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26437:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3283311985040649 : ℚ) / 125000000000) ≤ ((26256313360505751 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (26437:ℚ) := by decide +kernel
  have hratR : ((((3283311985040649 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((26256313360505751 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26437:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2905 : ((((26276678853950941 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26449 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26437 < q → q < 26449 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26449).mp (by decide +kernel))) hgap
  have hprev := thV_2904
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26449:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((26276678853950941 : ℚ) / 1000000000000) ≤ ((3283311985040649 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (26449:ℚ) := by decide +kernel
  have hratR : ((((26276678853950941 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3283311985040649 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26449:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2906 : ((((26286862205591361 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26459 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26449 < q → q < 26459 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26459).mp (by decide +kernel))) hgap
  have hprev := thV_2905
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26459:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((26286862205591361 : ℚ) / 1000000000000) ≤ ((26276678853950941 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (26459:ℚ) := by decide +kernel
  have hratR : ((((26286862205591361 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((26276678853950941 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26459:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2907 : ((((26297046312832709 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26479 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26459 < q → q < 26479 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26479).mp (by decide +kernel))) hgap
  have hprev := thV_2906
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26479:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((26297046312832709 : ℚ) / 1000000000000) ≤ ((26286862205591361 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (26479:ℚ) := by decide +kernel
  have hratR : ((((26297046312832709 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((26286862205591361 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26479:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2908 : ((((1644201924853783 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26489 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26479 < q → q < 26489 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26489).mp (by decide +kernel))) hgap
  have hprev := thV_2907
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26489:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1644201924853783 : ℚ) / 62500000000) ≤ ((26297046312832709 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (26489:ℚ) := by decide +kernel
  have hratR : ((((1644201924853783 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((26297046312832709 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26489:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2909 : ((((26317415584454907 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26497 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26489 < q → q < 26497 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26497).mp (by decide +kernel))) hgap
  have hprev := thV_2908
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26497:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((26317415584454907 : ℚ) / 1000000000000) ≤ ((1644201924853783 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (26497:ℚ) := by decide +kernel
  have hratR : ((((26317415584454907 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1644201924853783 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26497:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2910 : ((((26327600522198379 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26501 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26497 < q → q < 26501 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26501).mp (by decide +kernel))) hgap
  have hprev := thV_2909
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26501:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((26327600522198379 : ℚ) / 1000000000000) ≤ ((26317415584454907 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (26501:ℚ) := by decide +kernel
  have hratR : ((((26327600522198379 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((26317415584454907 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26501:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2911 : ((((26337785912652463 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26513 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26501 < q → q < 26513 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26513).mp (by decide +kernel))) hgap
  have hprev := thV_2910
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26513:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((26337785912652463 : ℚ) / 1000000000000) ≤ ((26327600522198379 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (26513:ℚ) := by decide +kernel
  have hratR : ((((26337785912652463 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((26327600522198379 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26513:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2912 : ((((823374133852407 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26539 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26513 < q → q < 26539 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26539).mp (by decide +kernel))) hgap
  have hprev := thV_2911
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26539:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((823374133852407 : ℚ) / 31250000000) ≤ ((26337785912652463 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (26539:ℚ) := by decide +kernel
  have hratR : ((((823374133852407 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((26337785912652463 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26539:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2913 : ((((6589539832979697 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26557 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26539 < q → q < 26557 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26557).mp (by decide +kernel))) hgap
  have hprev := thV_2912
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26557:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6589539832979697 : ℚ) / 250000000000) ≤ ((823374133852407 : ℚ) / 31250000000) + Work.RHContract.RegionI.logLowQ (26557:ℚ) := by decide +kernel
  have hratR : ((((6589539832979697 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((823374133852407 : ℚ) / 31250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26557:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2914 : ((((3296043316396079 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26561 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26557 < q → q < 26561 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26561).mp (by decide +kernel))) hgap
  have hprev := thV_2913
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26561:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3296043316396079 : ℚ) / 125000000000) ≤ ((6589539832979697 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (26561:ℚ) := by decide +kernel
  have hratR : ((((3296043316396079 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((6589539832979697 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26561:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2915 : ((((26378534182106669 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26573 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26561 < q → q < 26573 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26573).mp (by decide +kernel))) hgap
  have hprev := thV_2914
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26573:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((26378534182106669 : ℚ) / 1000000000000) ≤ ((3296043316396079 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (26573:ℚ) := by decide +kernel
  have hratR : ((((26378534182106669 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3296043316396079 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26573:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2916 : ((((26388722510194683 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26591 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26573 < q → q < 26591 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26591).mp (by decide +kernel))) hgap
  have hprev := thV_2915
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26591:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((26388722510194683 : ℚ) / 1000000000000) ≤ ((26378534182106669 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (26591:ℚ) := by decide +kernel
  have hratR : ((((26388722510194683 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((26378534182106669 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26591:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2917 : ((((13199455531948749 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26597 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26591 < q → q < 26597 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26597).mp (by decide +kernel))) hgap
  have hprev := thV_2916
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26597:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13199455531948749 : ℚ) / 500000000000) ≤ ((26388722510194683 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (26597:ℚ) := by decide +kernel
  have hratR : ((((13199455531948749 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((26388722510194683 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26597:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2918 : ((((1320455037245571 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26627 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26597 < q → q < 26627 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26627).mp (by decide +kernel))) hgap
  have hprev := thV_2917
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26627:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1320455037245571 : ℚ) / 50000000000) ≤ ((13199455531948749 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (26627:ℚ) := by decide +kernel
  have hratR : ((((1320455037245571 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((13199455531948749 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26627:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2919 : ((((3302411331404393 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26633 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26627 < q → q < 26633 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26633).mp (by decide +kernel))) hgap
  have hprev := thV_2918
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26633:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3302411331404393 : ℚ) / 125000000000) ≤ ((1320455037245571 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (26633:ℚ) := by decide +kernel
  have hratR : ((((3302411331404393 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((1320455037245571 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26633:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2920 : ((((206480319202289 : ℚ) / 7812500000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26641 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26633 < q → q < 26641 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26641).mp (by decide +kernel))) hgap
  have hprev := thV_2919
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26641:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((206480319202289 : ℚ) / 7812500000) ≤ ((3302411331404393 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (26641:ℚ) := by decide +kernel
  have hratR : ((((206480319202289 : ℚ) / 7812500000) : ℚ) : ℝ) ≤ ((((3302411331404393 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26641:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2921 : ((((26439671289742253 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26647 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26641 < q → q < 26647 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26647).mp (by decide +kernel))) hgap
  have hprev := thV_2920
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26647:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((26439671289742253 : ℚ) / 1000000000000) ≤ ((206480319202289 : ℚ) / 7812500000) + Work.RHContract.RegionI.logLowQ (26647:ℚ) := by decide +kernel
  have hratR : ((((26439671289742253 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((206480319202289 : ℚ) / 7812500000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26647:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2922 : ((((26449862546859773 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26669 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26647 < q → q < 26669 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26669).mp (by decide +kernel))) hgap
  have hprev := thV_2921
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26669:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((26449862546859773 : ℚ) / 1000000000000) ≤ ((26439671289742253 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (26669:ℚ) := by decide +kernel
  have hratR : ((((26449862546859773 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((26439671289742253 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26669:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2923 : ((((330750678172959 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26681 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26669 < q → q < 26681 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26681).mp (by decide +kernel))) hgap
  have hprev := thV_2922
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26681:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((330750678172959 : ℚ) / 12500000000) ≤ ((26449862546859773 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (26681:ℚ) := by decide +kernel
  have hratR : ((((330750678172959 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ ((((26449862546859773 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26681:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2924 : ((((26470246035770567 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26683 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26681 < q → q < 26683 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26683).mp (by decide +kernel))) hgap
  have hprev := thV_2923
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26683:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((26470246035770567 : ℚ) / 1000000000000) ≤ ((330750678172959 : ℚ) / 12500000000) + Work.RHContract.RegionI.logLowQ (26683:ℚ) := by decide +kernel
  have hratR : ((((26470246035770567 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((330750678172959 : ℚ) / 12500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26683:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2925 : ((((331005474595017 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26687 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26683 < q → q < 26687 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26687).mp (by decide +kernel))) hgap
  have hprev := thV_2924
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26687:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((331005474595017 : ℚ) / 12500000000) ≤ ((26470246035770567 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (26687:ℚ) := by decide +kernel
  have hratR : ((((331005474595017 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ ((((26470246035770567 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26687:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2926 : ((((26490630124235451 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26693 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26687 < q → q < 26693 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26693).mp (by decide +kernel))) hgap
  have hprev := thV_2925
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26693:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((26490630124235451 : ℚ) / 1000000000000) ≤ ((331005474595017 : ℚ) / 12500000000) + Work.RHContract.RegionI.logLowQ (26693:ℚ) := by decide +kernel
  have hratR : ((((26490630124235451 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((331005474595017 : ℚ) / 12500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26693:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2927 : ((((5300164501124463 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26699 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26693 < q → q < 26699 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26699).mp (by decide +kernel))) hgap
  have hprev := thV_2926
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26699:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5300164501124463 : ℚ) / 200000000000) ≤ ((26490630124235451 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (26699:ℚ) := by decide +kernel
  have hratR : ((((5300164501124463 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((26490630124235451 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26699:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2928 : ((((13255507480957773 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26701 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26699 < q → q < 26701 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26701).mp (by decide +kernel))) hgap
  have hprev := thV_2927
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26701:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13255507480957773 : ℚ) / 500000000000) ≤ ((5300164501124463 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (26701:ℚ) := by decide +kernel
  have hratR : ((((13255507480957773 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((5300164501124463 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26701:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2929 : ((((26521207792656471 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26711 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26701 < q → q < 26711 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26711).mp (by decide +kernel))) hgap
  have hprev := thV_2928
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26711:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((26521207792656471 : ℚ) / 1000000000000) ≤ ((13255507480957773 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (26711:ℚ) := by decide +kernel
  have hratR : ((((26521207792656471 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((13255507480957773 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26711:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2930 : ((((829106271820941 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26713 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26711 < q → q < 26713 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26713).mp (by decide +kernel))) hgap
  have hprev := thV_2929
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26713:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((829106271820941 : ℚ) / 31250000000) ≤ ((26521207792656471 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (26713:ℚ) := by decide +kernel
  have hratR : ((((829106271820941 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((26521207792656471 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26713:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2931 : ((((2654159375361237 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26717 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26713 < q → q < 26717 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26717).mp (by decide +kernel))) hgap
  have hprev := thV_2930
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26717:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2654159375361237 : ℚ) / 100000000000) ≤ ((829106271820941 : ℚ) / 31250000000) + Work.RHContract.RegionI.logLowQ (26717:ℚ) := by decide +kernel
  have hratR : ((((2654159375361237 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((829106271820941 : ℚ) / 31250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26717:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2932 : ((((3318973379188191 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26723 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26717 < q → q < 26723 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26723).mp (by decide +kernel))) hgap
  have hprev := thV_2931
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26723:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3318973379188191 : ℚ) / 125000000000) ≤ ((2654159375361237 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (26723:ℚ) := by decide +kernel
  have hratR : ((((3318973379188191 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((2654159375361237 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26723:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2933 : ((((26561980537899173 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26729 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26723 < q → q < 26729 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26729).mp (by decide +kernel))) hgap
  have hprev := thV_2932
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26729:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((26561980537899173 : ℚ) / 1000000000000) ≤ ((3318973379188191 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (26729:ℚ) := by decide +kernel
  have hratR : ((((26561980537899173 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3318973379188191 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26729:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2934 : ((((5314434823423023 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26731 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26729 < q → q < 26731 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26731).mp (by decide +kernel))) hgap
  have hprev := thV_2933
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26731:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5314434823423023 : ℚ) / 200000000000) ≤ ((26561980537899173 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (26731:ℚ) := by decide +kernel
  have hratR : ((((5314434823423023 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((26561980537899173 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26731:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2935 : ((((6645591980191091 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26737 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26731 < q → q < 26737 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26737).mp (by decide +kernel))) hgap
  have hprev := thV_2934
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26737:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6645591980191091 : ℚ) / 250000000000) ≤ ((5314434823423023 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (26737:ℚ) := by decide +kernel
  have hratR : ((((6645591980191091 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((5314434823423023 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26737:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2936 : ((((1329628127345253 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26759 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26737 < q → q < 26759 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26759).mp (by decide +kernel))) hgap
  have hprev := thV_2935
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26759:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1329628127345253 : ℚ) / 50000000000) ≤ ((6645591980191091 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (26759:ℚ) := by decide +kernel
  have hratR : ((((1329628127345253 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((6645591980191091 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26759:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2937 : ((((6650689461372623 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26777 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26759 < q → q < 26777 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26777).mp (by decide +kernel))) hgap
  have hprev := thV_2936
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26777:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6650689461372623 : ℚ) / 250000000000) ≤ ((1329628127345253 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (26777:ℚ) := by decide +kernel
  have hratR : ((((6650689461372623 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((1329628127345253 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26777:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2938 : ((((13306476684061861 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26783 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26777 < q → q < 26783 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26783).mp (by decide +kernel))) hgap
  have hprev := thV_2937
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26783:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13306476684061861 : ℚ) / 500000000000) ≤ ((6650689461372623 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (26783:ℚ) := by decide +kernel
  have hratR : ((((13306476684061861 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((6650689461372623 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26783:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2939 : ((((13311574781299659 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26801 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26783 < q → q < 26801 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26801).mp (by decide +kernel))) hgap
  have hprev := thV_2938
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26801:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13311574781299659 : ℚ) / 500000000000) ≤ ((13306476684061861 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (26801:ℚ) := by decide +kernel
  have hratR : ((((13311574781299659 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((13306476684061861 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26801:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2940 : ((((26633346204719193 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26813 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26801 < q → q < 26813 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26813).mp (by decide +kernel))) hgap
  have hprev := thV_2939
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26813:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((26633346204719193 : ℚ) / 1000000000000) ≤ ((13311574781299659 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (26813:ℚ) := by decide +kernel
  have hratR : ((((26633346204719193 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((13311574781299659 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26813:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2941 : ((((13321771572578651 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26821 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26813 < q → q < 26821 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26821).mp (by decide +kernel))) hgap
  have hprev := thV_2940
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26821:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13321771572578651 : ℚ) / 500000000000) ≤ ((26633346204719193 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (26821:ℚ) := by decide +kernel
  have hratR : ((((13321771572578651 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((26633346204719193 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26821:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2942 : ((((26653740532905963 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26833 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26821 < q → q < 26833 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26833).mp (by decide +kernel))) hgap
  have hprev := thV_2941
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26833:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((26653740532905963 : ℚ) / 1000000000000) ≤ ((13321771572578651 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (26833:ℚ) := by decide +kernel
  have hratR : ((((26653740532905963 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((13321771572578651 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26833:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2943 : ((((26663938144234891 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26839 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26833 < q → q < 26839 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26839).mp (by decide +kernel))) hgap
  have hprev := thV_2942
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26839:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((26663938144234891 : ℚ) / 1000000000000) ≤ ((26653740532905963 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (26839:ℚ) := by decide +kernel
  have hratR : ((((26663938144234891 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((26653740532905963 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26839:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2944 : ((((26674136128086547 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26849 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26839 < q → q < 26849 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26849).mp (by decide +kernel))) hgap
  have hprev := thV_2943
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26849:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((26674136128086547 : ℚ) / 1000000000000) ≤ ((26663938144234891 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (26849:ℚ) := by decide +kernel
  have hratR : ((((26674136128086547 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((26663938144234891 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26849:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2945 : ((((26684334558782373 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26861 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26849 < q → q < 26861 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26861).mp (by decide +kernel))) hgap
  have hprev := thV_2944
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26861:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((26684334558782373 : ℚ) / 1000000000000) ≤ ((26674136128086547 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (26861:ℚ) := by decide +kernel
  have hratR : ((((26684334558782373 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((26674136128086547 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26861:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2946 : ((((26694533063932819 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26863 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26861 < q → q < 26863 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26863).mp (by decide +kernel))) hgap
  have hprev := thV_2945
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26863:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((26694533063932819 : ℚ) / 1000000000000) ≤ ((26684334558782373 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (26863:ℚ) := by decide +kernel
  have hratR : ((((26694533063932819 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((26684334558782373 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26863:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2947 : ((((26704732164520743 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26879 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26863 < q → q < 26879 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26879).mp (by decide +kernel))) hgap
  have hprev := thV_2946
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26879:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((26704732164520743 : ℚ) / 1000000000000) ≤ ((26694533063932819 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (26879:ℚ) := by decide +kernel
  have hratR : ((((26704732164520743 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((26694533063932819 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26879:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2948 : ((((26714931339513429 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26881 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26879 < q → q < 26881 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26881).mp (by decide +kernel))) hgap
  have hprev := thV_2947
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26881:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((26714931339513429 : ℚ) / 1000000000000) ≤ ((26704732164520743 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (26881:ℚ) := by decide +kernel
  have hratR : ((((26714931339513429 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((26704732164520743 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26881:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2949 : ((((26725130886446907 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26891 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26881 < q → q < 26891 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26891).mp (by decide +kernel))) hgap
  have hprev := thV_2948
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26891:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((26725130886446907 : ℚ) / 1000000000000) ≤ ((26714931339513429 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (26891:ℚ) := by decide +kernel
  have hratR : ((((26725130886446907 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((26714931339513429 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26891:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2950 : ((((5347066101550389 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26893 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26891 < q → q < 26893 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26893).mp (by decide +kernel))) hgap
  have hprev := thV_2949
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26893:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5347066101550389 : ℚ) / 200000000000) ≤ ((26725130886446907 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (26893:ℚ) := by decide +kernel
  have hratR : ((((5347066101550389 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((26725130886446907 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26893:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2951 : ((((167159565630199 : ℚ) / 6250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26903 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26893 < q → q < 26903 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26903).mp (by decide +kernel))) hgap
  have hprev := thV_2950
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26903:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((167159565630199 : ℚ) / 6250000000) ≤ ((5347066101550389 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (26903:ℚ) := by decide +kernel
  have hratR : ((((167159565630199 : ℚ) / 6250000000) : ℚ) : ℝ) ≤ ((((5347066101550389 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26903:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2952 : ((((6688932790689593 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26921 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26903 < q → q < 26921 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26921).mp (by decide +kernel))) hgap
  have hprev := thV_2951
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26921:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6688932790689593 : ℚ) / 250000000000) ≤ ((167159565630199 : ℚ) / 6250000000) + Work.RHContract.RegionI.logLowQ (26921:ℚ) := by decide +kernel
  have hratR : ((((6688932790689593 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((167159565630199 : ℚ) / 6250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26921:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2953 : ((((26765932047534407 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26927 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26921 < q → q < 26927 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26927).mp (by decide +kernel))) hgap
  have hprev := thV_2952
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26927:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((26765932047534407 : ℚ) / 1000000000000) ≤ ((6688932790689593 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (26927:ℚ) := by decide +kernel
  have hratR : ((((26765932047534407 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((6688932790689593 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26927:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2954 : ((((13388066837391827 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26947 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26927 < q → q < 26947 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26947).mp (by decide +kernel))) hgap
  have hprev := thV_2953
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26947:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13388066837391827 : ℚ) / 500000000000) ≤ ((26765932047534407 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (26947:ℚ) := by decide +kernel
  have hratR : ((((13388066837391827 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((26765932047534407 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26947:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2955 : ((((13393167725230707 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26951 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26947 < q → q < 26951 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26951).mp (by decide +kernel))) hgap
  have hprev := thV_2954
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26951:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13393167725230707 : ℚ) / 500000000000) ≤ ((13388066837391827 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (26951:ℚ) := by decide +kernel
  have hratR : ((((13393167725230707 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((13388066837391827 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26951:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2956 : ((((2679653730034517 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26953 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26951 < q → q < 26953 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26953).mp (by decide +kernel))) hgap
  have hprev := thV_2955
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26953:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2679653730034517 : ℚ) / 100000000000) ≤ ((13393167725230707 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (26953:ℚ) := by decide +kernel
  have hratR : ((((2679653730034517 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((13393167725230707 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26953:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2957 : ((((670168484320347 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26959 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26953 < q → q < 26959 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26959).mp (by decide +kernel))) hgap
  have hprev := thV_2956
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26959:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((670168484320347 : ℚ) / 25000000000) ≤ ((2679653730034517 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (26959:ℚ) := by decide +kernel
  have hratR : ((((670168484320347 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((2679653730034517 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26959:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2958 : ((((26816942261003807 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26981 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26959 < q → q < 26981 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26981).mp (by decide +kernel))) hgap
  have hprev := thV_2957
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26981:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((26816942261003807 : ℚ) / 1000000000000) ≤ ((670168484320347 : ℚ) / 25000000000) + Work.RHContract.RegionI.logLowQ (26981:ℚ) := by decide +kernel
  have hratR : ((((26816942261003807 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((670168484320347 : ℚ) / 25000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26981:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2959 : ((((26827145371547723 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26987 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26981 < q → q < 26987 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26987).mp (by decide +kernel))) hgap
  have hprev := thV_2958
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26987:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((26827145371547723 : ℚ) / 1000000000000) ≤ ((26816942261003807 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (26987:ℚ) := by decide +kernel
  have hratR : ((((26827145371547723 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((26816942261003807 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26987:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2960 : ((((26837348704396197 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((26993 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26987 < q → q < 26993 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26993).mp (by decide +kernel))) hgap
  have hprev := thV_2959
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (26993:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((26837348704396197 : ℚ) / 1000000000000) ≤ ((26827145371547723 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (26993:ℚ) := by decide +kernel
  have hratR : ((((26837348704396197 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((26827145371547723 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (26993:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2961 : ((((26847552703861983 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27011 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 26993 < q → q < 27011 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27011).mp (by decide +kernel))) hgap
  have hprev := thV_2960
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27011:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((26847552703861983 : ℚ) / 1000000000000) ≤ ((26837348704396197 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (27011:ℚ) := by decide +kernel
  have hratR : ((((26847552703861983 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((26837348704396197 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27011:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2962 : ((((13428878462717413 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27017 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27011 < q → q < 27017 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27017).mp (by decide +kernel))) hgap
  have hprev := thV_2961
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27017:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13428878462717413 : ℚ) / 500000000000) ≤ ((26847552703861983 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (27017:ℚ) := by decide +kernel
  have hratR : ((((13428878462717413 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((26847552703861983 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27017:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2963 : ((((26867961665065703 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27031 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27017 < q → q < 27031 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27031).mp (by decide +kernel))) hgap
  have hprev := thV_2962
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27031:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((26867961665065703 : ℚ) / 1000000000000) ≤ ((13428878462717413 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (27031:ℚ) := by decide +kernel
  have hratR : ((((26867961665065703 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((13428878462717413 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27031:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2964 : ((((6719541712133203 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27043 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27031 < q → q < 27043 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27043).mp (by decide +kernel))) hgap
  have hprev := thV_2963
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27043:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6719541712133203 : ℚ) / 250000000000) ≤ ((26867961665065703 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (27043:ℚ) := by decide +kernel
  have hratR : ((((6719541712133203 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((26867961665065703 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27043:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2965 : ((((26888372623475299 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27059 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27043 < q → q < 27059 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27059).mp (by decide +kernel))) hgap
  have hprev := thV_2964
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27059:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((26888372623475299 : ℚ) / 1000000000000) ≤ ((6719541712133203 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (27059:ℚ) := by decide +kernel
  have hratR : ((((26888372623475299 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((6719541712133203 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27059:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2966 : ((((420290288630119 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27061 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27059 < q → q < 27061 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27061).mp (by decide +kernel))) hgap
  have hprev := thV_2965
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27061:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((420290288630119 : ℚ) / 15625000000) ≤ ((26888372623475299 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (27061:ℚ) := by decide +kernel
  have hratR : ((((420290288630119 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ ((((26888372623475299 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27061:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2967 : ((((26908784542876653 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27067 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27061 < q → q < 27067 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27067).mp (by decide +kernel))) hgap
  have hprev := thV_2966
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27067:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((26908784542876653 : ℚ) / 1000000000000) ≤ ((420290288630119 : ℚ) / 15625000000) + Work.RHContract.RegionI.logLowQ (27067:ℚ) := by decide +kernel
  have hratR : ((((26908784542876653 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((420290288630119 : ℚ) / 15625000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27067:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2968 : ((((26918990835073271 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27073 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27067 < q → q < 27073 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27073).mp (by decide +kernel))) hgap
  have hprev := thV_2967
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27073:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((26918990835073271 : ℚ) / 1000000000000) ≤ ((26908784542876653 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (27073:ℚ) := by decide +kernel
  have hratR : ((((26918990835073271 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((26908784542876653 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27073:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2969 : ((((5385839455001531 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27077 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27073 < q → q < 27077 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27077).mp (by decide +kernel))) hgap
  have hprev := thV_2968
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27077:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5385839455001531 : ℚ) / 200000000000) ≤ ((26918990835073271 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (27077:ℚ) := by decide +kernel
  have hratR : ((((5385839455001531 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((26918990835073271 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27077:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2970 : ((((6734851057963101 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27091 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27077 < q → q < 27091 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27091).mp (by decide +kernel))) hgap
  have hprev := thV_2969
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27091:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6734851057963101 : ℚ) / 250000000000) ≤ ((5385839455001531 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (27091:ℚ) := by decide +kernel
  have hratR : ((((6734851057963101 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((5385839455001531 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27091:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2971 : ((((6737402907887653 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27103 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27091 < q → q < 27103 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27103).mp (by decide +kernel))) hgap
  have hprev := thV_2970
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27103:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6737402907887653 : ℚ) / 250000000000) ≤ ((6734851057963101 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (27103:ℚ) := by decide +kernel
  have hratR : ((((6737402907887653 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((6734851057963101 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27103:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2972 : ((((26959819178823069 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27107 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27103 < q → q < 27107 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27107).mp (by decide +kernel))) hgap
  have hprev := thV_2971
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27107:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((26959819178823069 : ℚ) / 1000000000000) ≤ ((6737402907887653 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (27107:ℚ) := by decide +kernel
  have hratR : ((((26959819178823069 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((6737402907887653 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27107:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2973 : ((((6742506699968621 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27109 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27107 < q → q < 27109 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27109).mp (by decide +kernel))) hgap
  have hprev := thV_2972
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27109:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6742506699968621 : ℚ) / 250000000000) ≤ ((26959819178823069 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (27109:ℚ) := by decide +kernel
  have hratR : ((((6742506699968621 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((26959819178823069 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27109:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2974 : ((((3372529385586461 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27127 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27109 < q → q < 27127 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27127).mp (by decide +kernel))) hgap
  have hprev := thV_2973
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27127:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3372529385586461 : ℚ) / 125000000000) ≤ ((6742506699968621 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (27127:ℚ) := by decide +kernel
  have hratR : ((((3372529385586461 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((6742506699968621 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27127:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2975 : ((((42172568686177 : ℚ) / 1562500000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27143 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27127 < q → q < 27143 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27143).mp (by decide +kernel))) hgap
  have hprev := thV_2974
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27143:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((42172568686177 : ℚ) / 1562500000) ≤ ((3372529385586461 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (27143:ℚ) := by decide +kernel
  have hratR : ((((42172568686177 : ℚ) / 1562500000) : ℚ) : ℝ) ≤ ((((3372529385586461 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27143:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2976 : ((((2700065415904491 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27179 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27143 < q → q < 27179 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27179).mp (by decide +kernel))) hgap
  have hprev := thV_2975
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27179:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2700065415904491 : ℚ) / 100000000000) ≤ ((42172568686177 : ℚ) / 1562500000) + Work.RHContract.RegionI.logLowQ (27179:ℚ) := by decide +kernel
  have hratR : ((((2700065415904491 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((42172568686177 : ℚ) / 1562500000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27179:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2977 : ((((844089525011139 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27191 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27179 < q → q < 27191 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27191).mp (by decide +kernel))) hgap
  have hprev := thV_2976
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27191:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((844089525011139 : ℚ) / 31250000000) ≤ ((2700065415904491 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (27191:ℚ) := by decide +kernel
  have hratR : ((((844089525011139 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((2700065415904491 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27191:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2978 : ((((6755268915576223 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27197 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27191 < q → q < 27197 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27197).mp (by decide +kernel))) hgap
  have hprev := thV_2977
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27197:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6755268915576223 : ℚ) / 250000000000) ≤ ((844089525011139 : ℚ) / 31250000000) + Work.RHContract.RegionI.logLowQ (27197:ℚ) := by decide +kernel
  have hratR : ((((6755268915576223 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((844089525011139 : ℚ) / 31250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27197:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2979 : ((((27031287038883549 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27211 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27197 < q → q < 27211 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27211).mp (by decide +kernel))) hgap
  have hprev := thV_2978
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27211:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((27031287038883549 : ℚ) / 1000000000000) ≤ ((6755268915576223 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (27211:ℚ) := by decide +kernel
  have hratR : ((((27031287038883549 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((6755268915576223 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27211:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2980 : ((((27041499443928779 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27239 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27211 < q → q < 27239 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27239).mp (by decide +kernel))) hgap
  have hprev := thV_2979
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27239:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((27041499443928779 : ℚ) / 1000000000000) ≤ ((27031287038883549 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (27239:ℚ) := by decide +kernel
  have hratR : ((((27041499443928779 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((27031287038883549 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27239:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2981 : ((((3381463990299431 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27241 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27239 < q → q < 27241 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27241).mp (by decide +kernel))) hgap
  have hprev := thV_2980
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27241:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3381463990299431 : ℚ) / 125000000000) ≤ ((27041499443928779 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (27241:ℚ) := by decide +kernel
  have hratR : ((((3381463990299431 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((27041499443928779 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27241:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2982 : ((((27061924841277583 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27253 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27241 < q → q < 27253 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27253).mp (by decide +kernel))) hgap
  have hprev := thV_2981
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27253:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((27061924841277583 : ℚ) / 1000000000000) ≤ ((3381463990299431 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (27253:ℚ) := by decide +kernel
  have hratR : ((((27061924841277583 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3381463990299431 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27253:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2983 : ((((5414427596058947 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27259 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27253 < q → q < 27259 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27259).mp (by decide +kernel))) hgap
  have hprev := thV_2982
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27259:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5414427596058947 : ℚ) / 200000000000) ≤ ((27061924841277583 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (27259:ℚ) := by decide +kernel
  have hratR : ((((5414427596058947 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((27061924841277583 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27259:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2984 : ((((6770587889859149 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27271 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27259 < q → q < 27271 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27271).mp (by decide +kernel))) hgap
  have hprev := thV_2983
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27271:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6770587889859149 : ℚ) / 250000000000) ≤ ((5414427596058947 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (27271:ℚ) := by decide +kernel
  have hratR : ((((6770587889859149 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((5414427596058947 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27271:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2985 : ((((105830333431907 : ℚ) / 3906250000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27277 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27271 < q → q < 27277 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27277).mp (by decide +kernel))) hgap
  have hprev := thV_2984
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27277:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((105830333431907 : ℚ) / 3906250000) ≤ ((6770587889859149 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (27277:ℚ) := by decide +kernel
  have hratR : ((((105830333431907 : ℚ) / 3906250000) : ℚ) : ℝ) ≤ ((((6770587889859149 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27277:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2986 : ((((27102779304332729 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27281 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27277 < q → q < 27281 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27281).mp (by decide +kernel))) hgap
  have hprev := thV_2985
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27281:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((27102779304332729 : ℚ) / 1000000000000) ≤ ((105830333431907 : ℚ) / 3906250000) + Work.RHContract.RegionI.logLowQ (27281:ℚ) := by decide +kernel
  have hratR : ((((27102779304332729 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((105830333431907 : ℚ) / 3906250000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27281:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2987 : ((((1084519732936227 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27283 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27281 < q → q < 27283 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27283).mp (by decide +kernel))) hgap
  have hprev := thV_2986
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27283:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1084519732936227 : ℚ) / 40000000000) ≤ ((27102779304332729 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (27283:ℚ) := by decide +kernel
  have hratR : ((((1084519732936227 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((27102779304332729 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27283:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2988 : ((((27123207928752501 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27299 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27283 < q → q < 27299 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27299).mp (by decide +kernel))) hgap
  have hprev := thV_2987
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27299:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((27123207928752501 : ℚ) / 1000000000000) ≤ ((1084519732936227 : ℚ) / 40000000000) + Work.RHContract.RegionI.logLowQ (27299:ℚ) := by decide +kernel
  have hratR : ((((27123207928752501 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1084519732936227 : ℚ) / 40000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27299:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2989 : ((((13566711816218643 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27329 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27299 < q → q < 27329 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27329).mp (by decide +kernel))) hgap
  have hprev := thV_2988
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27329:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13566711816218643 : ℚ) / 500000000000) ≤ ((27123207928752501 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (27329:ℚ) := by decide +kernel
  have hratR : ((((13566711816218643 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((27123207928752501 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27329:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2990 : ((((27143639628808569 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27337 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27329 < q → q < 27337 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27337).mp (by decide +kernel))) hgap
  have hprev := thV_2989
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27337:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((27143639628808569 : ℚ) / 1000000000000) ≤ ((13566711816218643 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (27337:ℚ) := by decide +kernel
  have hratR : ((((27143639628808569 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((13566711816218643 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27337:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2991 : ((((5430771300545141 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27361 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27337 < q → q < 27361 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27361).mp (by decide +kernel))) hgap
  have hprev := thV_2990
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27361:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5430771300545141 : ℚ) / 200000000000) ≤ ((27143639628808569 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (27361:ℚ) := by decide +kernel
  have hratR : ((((5430771300545141 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((27143639628808569 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27361:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2992 : ((((27164073595909031 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27367 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27361 < q → q < 27367 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27367).mp (by decide +kernel))) hgap
  have hprev := thV_2991
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27367:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((27164073595909031 : ℚ) / 1000000000000) ≤ ((5430771300545141 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (27367:ℚ) := by decide +kernel
  have hratR : ((((27164073595909031 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5430771300545141 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27367:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2993 : ((((13587145892351361 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27397 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27367 < q → q < 27397 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27397).mp (by decide +kernel))) hgap
  have hprev := thV_2992
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27397:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13587145892351361 : ℚ) / 500000000000) ≤ ((27164073595909031 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (27397:ℚ) := by decide +kernel
  have hratR : ((((13587145892351361 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((27164073595909031 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27397:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2994 : ((((27184510338433283 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27407 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27397 < q → q < 27407 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27407).mp (by decide +kernel))) hgap
  have hprev := thV_2993
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27407:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((27184510338433283 : ℚ) / 1000000000000) ≤ ((13587145892351361 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (27407:ℚ) := by decide +kernel
  have hratR : ((((27184510338433283 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((13587145892351361 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27407:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2995 : ((((27194728965135239 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27409 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27407 < q → q < 27409 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27409).mp (by decide +kernel))) hgap
  have hprev := thV_2994
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27409:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((27194728965135239 : ℚ) / 1000000000000) ≤ ((27184510338433283 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (27409:ℚ) := by decide +kernel
  have hratR : ((((27194728965135239 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((27184510338433283 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27409:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2996 : ((((13602474124170123 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27427 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27409 < q → q < 27427 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27427).mp (by decide +kernel))) hgap
  have hprev := thV_2995
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27427:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13602474124170123 : ℚ) / 500000000000) ≤ ((27194728965135239 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (27427:ℚ) := by decide +kernel
  have hratR : ((((13602474124170123 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((27194728965135239 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27427:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2997 : ((((6803791919344077 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27431 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27427 < q → q < 27431 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27431).mp (by decide +kernel))) hgap
  have hprev := thV_2996
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27431:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6803791919344077 : ℚ) / 250000000000) ≤ ((13602474124170123 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (27431:ℚ) := by decide +kernel
  have hratR : ((((6803791919344077 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((13602474124170123 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27431:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2998 : ((((5445077465023817 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27437 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27431 < q → q < 27437 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27437).mp (by decide +kernel))) hgap
  have hprev := thV_2997
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27437:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5445077465023817 : ℚ) / 200000000000) ≤ ((6803791919344077 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (27437:ℚ) := by decide +kernel
  have hratR : ((((5445077465023817 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((6803791919344077 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27437:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2999 : ((((27235607410131847 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27449 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27437 < q → q < 27449 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27449).mp (by decide +kernel))) hgap
  have hprev := thV_2998
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27449:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((27235607410131847 : ℚ) / 1000000000000) ≤ ((5445077465023817 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (27449:ℚ) := by decide +kernel
  have hratR : ((((27235607410131847 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5445077465023817 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27449:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3000 : ((((27245827786551743 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27457 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27449 < q → q < 27457 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27457).mp (by decide +kernel))) hgap
  have hprev := thV_2999
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27457:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((27245827786551743 : ℚ) / 1000000000000) ≤ ((27235607410131847 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (27457:ℚ) := by decide +kernel
  have hratR : ((((27245827786551743 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((27235607410131847 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27457:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3001 : ((((6814012240975919 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27479 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27457 < q → q < 27479 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27479).mp (by decide +kernel))) hgap
  have hprev := thV_3000
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27479:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6814012240975919 : ℚ) / 250000000000) ≤ ((27245827786551743 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (27479:ℚ) := by decide +kernel
  have hratR : ((((6814012240975919 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((27245827786551743 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27479:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3002 : ((((6816567553508953 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27481 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27479 < q → q < 27481 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27481).mp (by decide +kernel))) hgap
  have hprev := thV_3001
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27481:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6816567553508953 : ℚ) / 250000000000) ≤ ((6814012240975919 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (27481:ℚ) := by decide +kernel
  have hratR : ((((6816567553508953 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((6814012240975919 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27481:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3003 : ((((27276491682476783 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27487 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27481 < q → q < 27487 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27487).mp (by decide +kernel))) hgap
  have hprev := thV_3002
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27487:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((27276491682476783 : ℚ) / 1000000000000) ≤ ((6816567553508953 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (27487:ℚ) := by decide +kernel
  have hratR : ((((27276491682476783 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((6816567553508953 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27487:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3004 : ((((27286713950975983 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27509 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27487 < q → q < 27509 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27509).mp (by decide +kernel))) hgap
  have hprev := thV_3003
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27509:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((27286713950975983 : ℚ) / 1000000000000) ≤ ((27276491682476783 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (27509:ℚ) := by decide +kernel
  have hratR : ((((27286713950975983 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((27276491682476783 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27509:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3005 : ((((426514638649883 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27527 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27509 < q → q < 27527 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27527).mp (by decide +kernel))) hgap
  have hprev := thV_3004
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27527:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((426514638649883 : ℚ) / 15625000000) ≤ ((27286713950975983 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (27527:ℚ) := by decide +kernel
  have hratR : ((((426514638649883 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ ((((27286713950975983 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27527:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3006 : ((((27307159868862339 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27529 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27527 < q → q < 27529 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27529).mp (by decide +kernel))) hgap
  have hprev := thV_3005
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27529:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((27307159868862339 : ℚ) / 1000000000000) ≤ ((426514638649883 : ℚ) / 15625000000) + Work.RHContract.RegionI.logLowQ (27529:ℚ) := by decide +kernel
  have hratR : ((((27307159868862339 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((426514638649883 : ℚ) / 15625000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27529:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3007 : ((((13658691613659751 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27539 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27529 < q → q < 27539 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27539).mp (by decide +kernel))) hgap
  have hprev := thV_3006
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27539:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13658691613659751 : ℚ) / 500000000000) ≤ ((27307159868862339 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (27539:ℚ) := by decide +kernel
  have hratR : ((((13658691613659751 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((27307159868862339 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27539:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3008 : ((((13663803329199153 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27541 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27539 < q → q < 27541 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27541).mp (by decide +kernel))) hgap
  have hprev := thV_3007
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27541:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13663803329199153 : ℚ) / 500000000000) ≤ ((13658691613659751 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (27541:ℚ) := by decide +kernel
  have hratR : ((((13663803329199153 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((13658691613659751 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27541:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3009 : ((((27337830452506229 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27551 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27541 < q → q < 27551 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27551).mp (by decide +kernel))) hgap
  have hprev := thV_3008
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27551:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((27337830452506229 : ℚ) / 1000000000000) ≤ ((13663803329199153 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (27551:ℚ) := by decide +kernel
  have hratR : ((((27337830452506229 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((13663803329199153 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27551:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3010 : ((((27348055334911437 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27581 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27551 < q → q < 27581 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27581).mp (by decide +kernel))) hgap
  have hprev := thV_3009
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27581:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((27348055334911437 : ℚ) / 1000000000000) ≤ ((27337830452506229 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (27581:ℚ) := by decide +kernel
  have hratR : ((((27348055334911437 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((27337830452506229 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27581:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3011 : ((((27358280289827703 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27583 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27581 < q → q < 27583 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27583).mp (by decide +kernel))) hgap
  have hprev := thV_3010
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27583:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((27358280289827703 : ℚ) / 1000000000000) ≤ ((27348055334911437 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (27583:ℚ) := by decide +kernel
  have hratR : ((((27358280289827703 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((27348055334911437 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27583:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3012 : ((((27368506259347093 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27611 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27583 < q → q < 27611 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27611).mp (by decide +kernel))) hgap
  have hprev := thV_3011
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27611:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((27368506259347093 : ℚ) / 1000000000000) ≤ ((27358280289827703 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (27611:ℚ) := by decide +kernel
  have hratR : ((((27368506259347093 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((27358280289827703 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27611:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3013 : ((((27378732446147573 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27617 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27611 < q → q < 27617 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27617).mp (by decide +kernel))) hgap
  have hprev := thV_3012
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27617:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((27378732446147573 : ℚ) / 1000000000000) ≤ ((27368506259347093 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (27617:ℚ) := by decide +kernel
  have hratR : ((((27378732446147573 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((27368506259347093 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27617:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3014 : ((((1369447956987687 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27631 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27617 < q → q < 27631 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27631).mp (by decide +kernel))) hgap
  have hprev := thV_3013
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27631:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1369447956987687 : ℚ) / 50000000000) ≤ ((27378732446147573 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (27631:ℚ) := by decide +kernel
  have hratR : ((((1369447956987687 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((27378732446147573 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27631:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3015 : ((((6849796603063017 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27647 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27631 < q → q < 27647 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27647).mp (by decide +kernel))) hgap
  have hprev := thV_3014
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27647:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6849796603063017 : ℚ) / 250000000000) ≤ ((1369447956987687 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (27647:ℚ) := by decide +kernel
  have hratR : ((((6849796603063017 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((1369447956987687 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27647:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3016 : ((((27409413901748589 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27653 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27647 < q → q < 27653 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27653).mp (by decide +kernel))) hgap
  have hprev := thV_3015
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27653:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((27409413901748589 : ℚ) / 1000000000000) ≤ ((6849796603063017 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (27653:ℚ) := by decide +kernel
  have hratR : ((((27409413901748589 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((6849796603063017 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27653:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3017 : ((((1096785684569301 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27673 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27653 < q → q < 27673 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27673).mp (by decide +kernel))) hgap
  have hprev := thV_3016
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27673:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1096785684569301 : ℚ) / 40000000000) ≤ ((27409413901748589 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (27673:ℚ) := by decide +kernel
  have hratR : ((((1096785684569301 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((27409413901748589 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27673:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3018 : ((((13714935452365139 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27689 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27673 < q → q < 27689 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27689).mp (by decide +kernel))) hgap
  have hprev := thV_3017
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27689:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13714935452365139 : ℚ) / 500000000000) ≤ ((1096785684569301 : ℚ) / 40000000000) + Work.RHContract.RegionI.logLowQ (27689:ℚ) := by decide +kernel
  have hratR : ((((13714935452365139 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1096785684569301 : ℚ) / 40000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27689:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3019 : ((((1715006235466017 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27691 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27689 < q → q < 27691 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27691).mp (by decide +kernel))) hgap
  have hprev := thV_3018
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27691:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1715006235466017 : ℚ) / 62500000000) ≤ ((13714935452365139 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (27691:ℚ) := by decide +kernel
  have hratR : ((((1715006235466017 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((13714935452365139 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27691:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3020 : ((((27450328846835693 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27697 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27691 < q → q < 27697 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27697).mp (by decide +kernel))) hgap
  have hprev := thV_3019
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27697:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((27450328846835693 : ℚ) / 1000000000000) ≤ ((1715006235466017 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (27697:ℚ) := by decide +kernel
  have hratR : ((((27450328846835693 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1715006235466017 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27697:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3021 : ((((1373027903531233 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27701 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27697 < q → q < 27701 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27701).mp (by decide +kernel))) hgap
  have hprev := thV_3020
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27701:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1373027903531233 : ℚ) / 50000000000) ≤ ((27450328846835693 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (27701:ℚ) := by decide +kernel
  have hratR : ((((1373027903531233 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((27450328846835693 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27701:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3022 : ((((13735394224469929 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27733 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27701 < q → q < 27733 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27733).mp (by decide +kernel))) hgap
  have hprev := thV_3021
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27733:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13735394224469929 : ℚ) / 500000000000) ≤ ((1373027903531233 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (27733:ℚ) := by decide +kernel
  have hratR : ((((13735394224469929 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1373027903531233 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27733:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3023 : ((((27481018971477159 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27737 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27733 < q → q < 27737 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27737).mp (by decide +kernel))) hgap
  have hprev := thV_3022
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27737:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((27481018971477159 : ℚ) / 1000000000000) ≤ ((13735394224469929 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (27737:ℚ) := by decide +kernel
  have hratR : ((((27481018971477159 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((13735394224469929 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27737:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3024 : ((((1718203097882357 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27739 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27737 < q → q < 27739 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27739).mp (by decide +kernel))) hgap
  have hprev := thV_3023
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27739:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1718203097882357 : ℚ) / 62500000000) ≤ ((27481018971477159 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (27739:ℚ) := by decide +kernel
  have hratR : ((((1718203097882357 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((27481018971477159 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27739:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3025 : ((((13750740152474587 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27743 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27739 < q → q < 27743 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27743).mp (by decide +kernel))) hgap
  have hprev := thV_3024
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27743:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13750740152474587 : ℚ) / 500000000000) ≤ ((1718203097882357 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (27743:ℚ) := by decide +kernel
  have hratR : ((((13750740152474587 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1718203097882357 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27743:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3026 : ((((27511711260028023 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27749 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27743 < q → q < 27749 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27749).mp (by decide +kernel))) hgap
  have hprev := thV_3025
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27749:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((27511711260028023 : ℚ) / 1000000000000) ≤ ((13750740152474587 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (27749:ℚ) := by decide +kernel
  have hratR : ((((27511711260028023 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((13750740152474587 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27749:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3027 : ((((5504388457435789 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27751 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27749 < q → q < 27751 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27751).mp (by decide +kernel))) hgap
  have hprev := thV_3026
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27751:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5504388457435789 : ℚ) / 200000000000) ≤ ((27511711260028023 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (27751:ℚ) := by decide +kernel
  have hratR : ((((5504388457435789 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((27511711260028023 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27751:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3028 : ((((27532173746653251 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27763 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27751 < q → q < 27763 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27763).mp (by decide +kernel))) hgap
  have hprev := thV_3027
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27763:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((27532173746653251 : ℚ) / 1000000000000) ≤ ((5504388457435789 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (27763:ℚ) := by decide +kernel
  have hratR : ((((27532173746653251 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5504388457435789 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27763:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3029 : ((((6885601337548457 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27767 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27763 < q → q < 27767 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27767).mp (by decide +kernel))) hgap
  have hprev := thV_3028
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27767:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6885601337548457 : ℚ) / 250000000000) ≤ ((27532173746653251 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (27767:ℚ) := by decide +kernel
  have hratR : ((((6885601337548457 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((27532173746653251 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27767:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3030 : ((((27552637169794903 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27773 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27767 < q → q < 27773 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27773).mp (by decide +kernel))) hgap
  have hprev := thV_3029
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27773:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((27552637169794903 : ℚ) / 1000000000000) ≤ ((6885601337548457 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (27773:ℚ) := by decide +kernel
  have hratR : ((((27552637169794903 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((6885601337548457 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27773:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3031 : ((((27562869205409803 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27779 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27773 < q → q < 27779 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27779).mp (by decide +kernel))) hgap
  have hprev := thV_3030
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27779:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((27562869205409803 : ℚ) / 1000000000000) ≤ ((27552637169794903 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (27779:ℚ) := by decide +kernel
  have hratR : ((((27562869205409803 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((27552637169794903 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27779:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3032 : ((((27573101672912419 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27791 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27779 < q → q < 27791 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27791).mp (by decide +kernel))) hgap
  have hprev := thV_3031
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27791:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((27573101672912419 : ℚ) / 1000000000000) ≤ ((27562869205409803 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (27791:ℚ) := by decide +kernel
  have hratR : ((((27573101672912419 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((27562869205409803 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27791:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3033 : ((((2758333421237819 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27793 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27791 < q → q < 27793 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27793).mp (by decide +kernel))) hgap
  have hprev := thV_3032
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27793:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2758333421237819 : ℚ) / 100000000000) ≤ ((27573101672912419 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (27793:ℚ) := by decide +kernel
  have hratR : ((((2758333421237819 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((27573101672912419 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27793:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3034 : ((((27593566967702359 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27799 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27793 < q → q < 27799 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27799).mp (by decide +kernel))) hgap
  have hprev := thV_3033
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27799:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((27593566967702359 : ℚ) / 1000000000000) ≤ ((2758333421237819 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (27799:ℚ) := by decide +kernel
  have hratR : ((((27593566967702359 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2758333421237819 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27799:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3035 : ((((5520759973381249 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27803 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27799 < q → q < 27803 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27803).mp (by decide +kernel))) hgap
  have hprev := thV_3034
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27803:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5520759973381249 : ℚ) / 200000000000) ≤ ((27593566967702359 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (27803:ℚ) := by decide +kernel
  have hratR : ((((5520759973381249 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((27593566967702359 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27803:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3036 : ((((13807016490945449 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27809 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27803 < q → q < 27809 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27809).mp (by decide +kernel))) hgap
  have hprev := thV_3035
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27809:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13807016490945449 : ℚ) / 500000000000) ≤ ((5520759973381249 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (27809:ℚ) := by decide +kernel
  have hratR : ((((13807016490945449 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((5520759973381249 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27809:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3037 : ((((1726516649031927 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27817 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27809 < q → q < 27817 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27817).mp (by decide +kernel))) hgap
  have hprev := thV_3036
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27817:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1726516649031927 : ℚ) / 62500000000) ≤ ((13807016490945449 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (27817:ℚ) := by decide +kernel
  have hratR : ((((1726516649031927 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((13807016490945449 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27817:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3038 : ((((5526900000560589 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27823 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27817 < q → q < 27823 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27823).mp (by decide +kernel))) hgap
  have hprev := thV_3037
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27823:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5526900000560589 : ℚ) / 200000000000) ≤ ((1726516649031927 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (27823:ℚ) := by decide +kernel
  have hratR : ((((5526900000560589 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((1726516649031927 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27823:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3039 : ((((13822366882425337 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27827 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27823 < q → q < 27827 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27827).mp (by decide +kernel))) hgap
  have hprev := thV_3038
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27827:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13822366882425337 : ℚ) / 500000000000) ≤ ((5526900000560589 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (27827:ℚ) := by decide +kernel
  have hratR : ((((13822366882425337 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((5526900000560589 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27827:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3040 : ((((27654968245366659 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27847 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27827 < q → q < 27847 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27847).mp (by decide +kernel))) hgap
  have hprev := thV_3039
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27847:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((27654968245366659 : ℚ) / 1000000000000) ≤ ((13822366882425337 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (27847:ℚ) := by decide +kernel
  have hratR : ((((27654968245366659 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((13822366882425337 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27847:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3041 : ((((27665202869514373 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27851 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27847 < q → q < 27851 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27851).mp (by decide +kernel))) hgap
  have hprev := thV_3040
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27851:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((27665202869514373 : ℚ) / 1000000000000) ≤ ((27654968245366659 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (27851:ℚ) := by decide +kernel
  have hratR : ((((27665202869514373 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((27654968245366659 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27851:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3042 : ((((6918859660493459 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27883 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27851 < q → q < 27883 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27883).mp (by decide +kernel))) hgap
  have hprev := thV_3041
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27883:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6918859660493459 : ℚ) / 250000000000) ≤ ((27665202869514373 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (27883:ℚ) := by decide +kernel
  have hratR : ((((6918859660493459 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((27665202869514373 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27883:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3043 : ((((27685674773010469 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27893 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27883 < q → q < 27893 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27893).mp (by decide +kernel))) hgap
  have hprev := thV_3042
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27893:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((27685674773010469 : ℚ) / 1000000000000) ≤ ((6918859660493459 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (27893:ℚ) := by decide +kernel
  have hratR : ((((27685674773010469 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((6918859660493459 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27893:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3044 : ((((2769591119081629 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27901 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27893 < q → q < 27901 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27901).mp (by decide +kernel))) hgap
  have hprev := thV_3043
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27901:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2769591119081629 : ℚ) / 100000000000) ≤ ((27685674773010469 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (27901:ℚ) := by decide +kernel
  have hratR : ((((2769591119081629 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((27685674773010469 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27901:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3045 : ((((27706148181913897 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27917 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27901 < q → q < 27917 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27917).mp (by decide +kernel))) hgap
  have hprev := thV_3044
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27917:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((27706148181913897 : ℚ) / 1000000000000) ≤ ((2769591119081629 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (27917:ℚ) := by decide +kernel
  have hratR : ((((27706148181913897 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2769591119081629 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27917:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3046 : ((((27716385244649873 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27919 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27917 < q → q < 27919 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27919).mp (by decide +kernel))) hgap
  have hprev := thV_3045
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27919:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((27716385244649873 : ℚ) / 1000000000000) ≤ ((27706148181913897 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (27919:ℚ) := by decide +kernel
  have hratR : ((((27716385244649873 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((27706148181913897 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27919:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3047 : ((((3465827886883673 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27941 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27919 < q → q < 27941 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27941).mp (by decide +kernel))) hgap
  have hprev := thV_3046
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27941:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3465827886883673 : ℚ) / 125000000000) ≤ ((27716385244649873 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (27941:ℚ) := by decide +kernel
  have hratR : ((((3465827886883673 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((27716385244649873 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27941:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3048 : ((((27736861017065733 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27943 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27941 < q → q < 27943 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27943).mp (by decide +kernel))) hgap
  have hprev := thV_3047
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27943:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((27736861017065733 : ℚ) / 1000000000000) ≤ ((3465827886883673 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (27943:ℚ) := by decide +kernel
  have hratR : ((((27736861017065733 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3465827886883673 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27943:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3049 : ((((2774709908220039 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27947 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27943 < q → q < 27947 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27947).mp (by decide +kernel))) hgap
  have hprev := thV_3048
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27947:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2774709908220039 : ℚ) / 100000000000) ≤ ((27736861017065733 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (27947:ℚ) := by decide +kernel
  have hratR : ((((2774709908220039 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((27736861017065733 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27947:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3050 : ((((277573373620041 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27953 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27947 < q → q < 27953 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27953).mp (by decide +kernel))) hgap
  have hprev := thV_3049
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27953:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((277573373620041 : ℚ) / 10000000000) ≤ ((2774709908220039 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (27953:ℚ) := by decide +kernel
  have hratR : ((((277573373620041 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ ((((2774709908220039 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27953:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3051 : ((((6941893981990387 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27961 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27953 < q → q < 27961 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27961).mp (by decide +kernel))) hgap
  have hprev := thV_3050
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27961:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6941893981990387 : ℚ) / 250000000000) ≤ ((277573373620041 : ℚ) / 10000000000) + Work.RHContract.RegionI.logLowQ (27961:ℚ) := by decide +kernel
  have hratR : ((((6941893981990387 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((277573373620041 : ℚ) / 10000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27961:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3052 : ((((434028354820009 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27967 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27961 < q → q < 27967 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27967).mp (by decide +kernel))) hgap
  have hprev := thV_3051
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27967:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((434028354820009 : ℚ) / 15625000000) ≤ ((6941893981990387 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (27967:ℚ) := by decide +kernel
  have hratR : ((((434028354820009 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ ((((6941893981990387 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27967:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3053 : ((((27788054060938851 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27983 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27967 < q → q < 27983 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27983).mp (by decide +kernel))) hgap
  have hprev := thV_3052
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27983:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((27788054060938851 : ℚ) / 1000000000000) ≤ ((434028354820009 : ℚ) / 15625000000) + Work.RHContract.RegionI.logLowQ (27983:ℚ) := by decide +kernel
  have hratR : ((((27788054060938851 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((434028354820009 : ℚ) / 15625000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27983:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3054 : ((((27798293913575771 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((27997 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27983 < q → q < 27997 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27997).mp (by decide +kernel))) hgap
  have hprev := thV_3053
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (27997:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((27798293913575771 : ℚ) / 1000000000000) ≤ ((27788054060938851 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (27997:ℚ) := by decide +kernel
  have hratR : ((((27798293913575771 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((27788054060938851 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (27997:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3055 : ((((27808533909074937 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28001 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27997 < q → q < 28001 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28001).mp (by decide +kernel))) hgap
  have hprev := thV_3054
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28001:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((27808533909074937 : ℚ) / 1000000000000) ≤ ((27798293913575771 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (28001:ℚ) := by decide +kernel
  have hratR : ((((27808533909074937 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((27798293913575771 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28001:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3056 : ((((13909387273600879 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28019 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28001 < q → q < 28019 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28019).mp (by decide +kernel))) hgap
  have hprev := thV_3055
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28019:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13909387273600879 : ℚ) / 500000000000) ≤ ((27808533909074937 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (28019:ℚ) := by decide +kernel
  have hratR : ((((13909387273600879 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((27808533909074937 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28019:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3057 : ((((5565803094161673 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28027 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28019 < q → q < 28027 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28027).mp (by decide +kernel))) hgap
  have hprev := thV_3056
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28027:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5565803094161673 : ℚ) / 200000000000) ≤ ((13909387273600879 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (28027:ℚ) := by decide +kernel
  have hratR : ((((5565803094161673 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((13909387273600879 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28027:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3058 : ((((27839256537124309 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28031 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28027 < q → q < 28031 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28031).mp (by decide +kernel))) hgap
  have hprev := thV_3057
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28031:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((27839256537124309 : ℚ) / 1000000000000) ≤ ((5565803094161673 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (28031:ℚ) := by decide +kernel
  have hratR : ((((27839256537124309 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5565803094161673 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28031:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3059 : ((((27849498316681609 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28051 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28031 < q → q < 28051 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28051).mp (by decide +kernel))) hgap
  have hprev := thV_3058
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28051:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((27849498316681609 : ℚ) / 1000000000000) ≤ ((27839256537124309 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (28051:ℚ) := by decide +kernel
  have hratR : ((((27849498316681609 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((27839256537124309 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28051:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3060 : ((((13929870155056077 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28057 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28051 < q → q < 28057 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28057).mp (by decide +kernel))) hgap
  have hprev := thV_3059
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28057:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13929870155056077 : ℚ) / 500000000000) ≤ ((27849498316681609 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (28057:ℚ) := by decide +kernel
  have hratR : ((((13929870155056077 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((27849498316681609 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28057:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3061 : ((((27869982731152013 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28069 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28057 < q → q < 28069 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28069).mp (by decide +kernel))) hgap
  have hprev := thV_3060
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28069:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((27869982731152013 : ℚ) / 1000000000000) ≤ ((13929870155056077 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (28069:ℚ) := by decide +kernel
  have hratR : ((((27869982731152013 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((13929870155056077 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28069:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3062 : ((((5576045115923683 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28081 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28069 < q → q < 28081 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28081).mp (by decide +kernel))) hgap
  have hprev := thV_3061
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28081:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5576045115923683 : ℚ) / 200000000000) ≤ ((27869982731152013 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (28081:ℚ) := by decide +kernel
  have hratR : ((((5576045115923683 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((27869982731152013 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28081:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3063 : ((((27890468641729597 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28087 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28081 < q → q < 28087 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28087).mp (by decide +kernel))) hgap
  have hprev := thV_3062
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28087:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((27890468641729597 : ℚ) / 1000000000000) ≤ ((5576045115923683 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (28087:ℚ) := by decide +kernel
  have hratR : ((((27890468641729597 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5576045115923683 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28087:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3064 : ((((13950356029907007 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28097 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28087 < q → q < 28097 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28097).mp (by decide +kernel))) hgap
  have hprev := thV_3063
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28097:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13950356029907007 : ℚ) / 500000000000) ≤ ((27890468641729597 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (28097:ℚ) := by decide +kernel
  have hratR : ((((13950356029907007 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((27890468641729597 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28097:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3065 : ((((13955477774538937 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28099 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28097 < q → q < 28099 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28099).mp (by decide +kernel))) hgap
  have hprev := thV_3064
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28099:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13955477774538937 : ℚ) / 500000000000) ≤ ((13950356029907007 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (28099:ℚ) := by decide +kernel
  have hratR : ((((13955477774538937 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((13950356029907007 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28099:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3066 : ((((27921199394162973 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28109 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28099 < q → q < 28109 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28109).mp (by decide +kernel))) hgap
  have hprev := thV_3065
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28109:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((27921199394162973 : ℚ) / 1000000000000) ≤ ((13955477774538937 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (28109:ℚ) := by decide +kernel
  have hratR : ((((27921199394162973 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((13955477774538937 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28109:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3067 : ((((2793144331039713 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28111 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28109 < q → q < 28111 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28111).mp (by decide +kernel))) hgap
  have hprev := thV_3066
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28111:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2793144331039713 : ℚ) / 100000000000) ≤ ((27921199394162973 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (28111:ℚ) := by decide +kernel
  have hratR : ((((2793144331039713 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((27921199394162973 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28111:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3068 : ((((27941687653419357 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28123 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28111 < q → q < 28123 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28123).mp (by decide +kernel))) hgap
  have hprev := thV_3067
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28123:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((27941687653419357 : ℚ) / 1000000000000) ≤ ((2793144331039713 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (28123:ℚ) := by decide +kernel
  have hratR : ((((27941687653419357 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2793144331039713 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28123:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3069 : ((((27951932991572633 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28151 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28123 < q → q < 28151 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28151).mp (by decide +kernel))) hgap
  have hprev := thV_3068
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28151:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((27951932991572633 : ℚ) / 1000000000000) ≤ ((27941687653419357 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (28151:ℚ) := by decide +kernel
  have hratR : ((((27951932991572633 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((27941687653419357 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28151:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3070 : ((((13981089377953841 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28163 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28151 < q → q < 28163 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28163).mp (by decide +kernel))) hgap
  have hprev := thV_3069
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28163:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13981089377953841 : ℚ) / 500000000000) ≤ ((27951932991572633 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (28163:ℚ) := by decide +kernel
  have hratR : ((((13981089377953841 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((27951932991572633 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28163:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3071 : ((((13986212579587513 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28181 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28163 < q → q < 28181 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28181).mp (by decide +kernel))) hgap
  have hprev := thV_3070
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28181:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13986212579587513 : ℚ) / 500000000000) ≤ ((13981089377953841 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (28181:ℚ) := by decide +kernel
  have hratR : ((((13986212579587513 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((13981089377953841 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28181:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3072 : ((((13991335816704827 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28183 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28181 < q → q < 28183 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28183).mp (by decide +kernel))) hgap
  have hprev := thV_3071
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28183:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13991335816704827 : ℚ) / 500000000000) ≤ ((13986212579587513 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (28183:ℚ) := by decide +kernel
  have hratR : ((((13991335816704827 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((13986212579587513 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28183:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3073 : ((((5598583749224661 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28201 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28183 < q → q < 28201 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28201).mp (by decide +kernel))) hgap
  have hprev := thV_3072
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28201:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5598583749224661 : ℚ) / 200000000000) ≤ ((13991335816704827 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (28201:ℚ) := by decide +kernel
  have hratR : ((((5598583749224661 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((13991335816704827 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28201:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3074 : ((((437549472083929 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28211 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28201 < q → q < 28211 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28211).mp (by decide +kernel))) hgap
  have hprev := thV_3073
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28211:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((437549472083929 : ℚ) / 15625000000) ≤ ((5598583749224661 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (28211:ℚ) := by decide +kernel
  have hratR : ((((437549472083929 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ ((((5598583749224661 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28211:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3075 : ((((14006706982078367 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28219 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28211 < q → q < 28219 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28219).mp (by decide +kernel))) hgap
  have hprev := thV_3074
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28219:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14006706982078367 : ℚ) / 500000000000) ≤ ((437549472083929 : ℚ) / 15625000000) + Work.RHContract.RegionI.logLowQ (28219:ℚ) := by decide +kernel
  have hratR : ((((14006706982078367 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((437549472083929 : ℚ) / 15625000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28219:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3076 : ((((14011831034625203 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28229 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28219 < q → q < 28229 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28229).mp (by decide +kernel))) hgap
  have hprev := thV_3075
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28229:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14011831034625203 : ℚ) / 500000000000) ≤ ((14006706982078367 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (28229:ℚ) := by decide +kernel
  have hratR : ((((14011831034625203 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((14006706982078367 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28229:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3077 : ((((28033911873279113 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28277 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28229 < q → q < 28277 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28277).mp (by decide +kernel))) hgap
  have hprev := thV_3076
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28277:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((28033911873279113 : ℚ) / 1000000000000) ≤ ((14011831034625203 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (28277:ℚ) := by decide +kernel
  have hratR : ((((28033911873279113 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((14011831034625203 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28277:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3078 : ((((1402208087401709 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28279 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28277 < q → q < 28279 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28279).mp (by decide +kernel))) hgap
  have hprev := thV_3077
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28279:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1402208087401709 : ℚ) / 50000000000) ≤ ((28033911873279113 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (28279:ℚ) := by decide +kernel
  have hratR : ((((1402208087401709 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((28033911873279113 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28279:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3079 : ((((28054411764226961 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28283 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28279 < q → q < 28283 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28283).mp (by decide +kernel))) hgap
  have hprev := thV_3078
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28283:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((28054411764226961 : ℚ) / 1000000000000) ≤ ((1402208087401709 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (28283:ℚ) := by decide +kernel
  have hratR : ((((28054411764226961 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1402208087401709 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28283:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3080 : ((((28064661992538813 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28289 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28283 < q → q < 28289 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28289).mp (by decide +kernel))) hgap
  have hprev := thV_3079
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28289:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((28064661992538813 : ℚ) / 1000000000000) ≤ ((28054411764226961 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (28289:ℚ) := by decide +kernel
  have hratR : ((((28064661992538813 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((28054411764226961 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28289:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3081 : ((((14037456251803059 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28297 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28289 < q → q < 28297 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28297).mp (by decide +kernel))) hgap
  have hprev := thV_3080
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28297:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14037456251803059 : ℚ) / 500000000000) ≤ ((28064661992538813 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (28297:ℚ) := by decide +kernel
  have hratR : ((((14037456251803059 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((28064661992538813 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28297:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3082 : ((((28085163368005347 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28307 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28297 < q → q < 28307 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28307).mp (by decide +kernel))) hgap
  have hprev := thV_3081
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28307:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((28085163368005347 : ℚ) / 1000000000000) ≤ ((14037456251803059 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (28307:ℚ) := by decide +kernel
  have hratR : ((((28085163368005347 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((14037456251803059 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28307:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3083 : ((((14047707151527991 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28309 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28307 < q → q < 28309 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28309).mp (by decide +kernel))) hgap
  have hprev := thV_3082
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28309:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14047707151527991 : ℚ) / 500000000000) ≤ ((28085163368005347 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (28309:ℚ) := by decide +kernel
  have hratR : ((((14047707151527991 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((28085163368005347 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28309:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3084 : ((((3513208198911099 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28319 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28309 < q → q < 28319 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28319).mp (by decide +kernel))) hgap
  have hprev := thV_3083
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28319:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3513208198911099 : ℚ) / 125000000000) ≤ ((14047707151527991 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (28319:ℚ) := by decide +kernel
  have hratR : ((((3513208198911099 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((14047707151527991 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28319:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3085 : ((((28115917938320317 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28349 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28319 < q → q < 28349 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28349).mp (by decide +kernel))) hgap
  have hprev := thV_3084
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28349:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((28115917938320317 : ℚ) / 1000000000000) ≤ ((3513208198911099 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (28349:ℚ) := by decide +kernel
  have hratR : ((((28115917938320317 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3513208198911099 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28349:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3086 : ((((1406308517794929 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28351 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28349 < q → q < 28351 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28351).mp (by decide +kernel))) hgap
  have hprev := thV_3085
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28351:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1406308517794929 : ℚ) / 50000000000) ≤ ((28115917938320317 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (28351:ℚ) := by decide +kernel
  have hratR : ((((1406308517794929 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((28115917938320317 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28351:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3087 : ((((28136424042467813 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28387 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28351 < q → q < 28387 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28387).mp (by decide +kernel))) hgap
  have hprev := thV_3086
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28387:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((28136424042467813 : ℚ) / 1000000000000) ≤ ((1406308517794929 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (28387:ℚ) := by decide +kernel
  have hratR : ((((28136424042467813 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1406308517794929 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28387:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3088 : ((((7036669485094767 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28393 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28387 < q → q < 28393 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28393).mp (by decide +kernel))) hgap
  have hprev := thV_3087
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28393:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7036669485094767 : ℚ) / 250000000000) ≤ ((28136424042467813 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (28393:ℚ) := by decide +kernel
  have hratR : ((((7036669485094767 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((28136424042467813 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28393:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3089 : ((((14078466095213901 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28403 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28393 < q → q < 28403 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28403).mp (by decide +kernel))) hgap
  have hprev := thV_3088
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28403:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14078466095213901 : ℚ) / 500000000000) ≤ ((7036669485094767 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (28403:ℚ) := by decide +kernel
  have hratR : ((((14078466095213901 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((7036669485094767 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28403:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3090 : ((((28167186651699517 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28409 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28403 < q → q < 28409 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28409).mp (by decide +kernel))) hgap
  have hprev := thV_3089
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28409:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((28167186651699517 : ℚ) / 1000000000000) ≤ ((14078466095213901 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (28409:ℚ) := by decide +kernel
  have hratR : ((((28167186651699517 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((14078466095213901 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28409:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3091 : ((((1408872059168449 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28411 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28409 < q → q < 28411 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28411).mp (by decide +kernel))) hgap
  have hprev := thV_3090
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28411:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1408872059168449 : ℚ) / 50000000000) ≤ ((28167186651699517 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (28411:ℚ) := by decide +kernel
  have hratR : ((((1408872059168449 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((28167186651699517 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28411:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3092 : ((((5637539269679051 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28429 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28411 < q → q < 28429 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28429).mp (by decide +kernel))) hgap
  have hprev := thV_3091
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28429:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5637539269679051 : ℚ) / 200000000000) ≤ ((1408872059168449 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (28429:ℚ) := by decide +kernel
  have hratR : ((((5637539269679051 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((1408872059168449 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28429:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3093 : ((((28197951654113029 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28433 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28429 < q → q < 28433 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28433).mp (by decide +kernel))) hgap
  have hprev := thV_3092
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28433:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((28197951654113029 : ℚ) / 1000000000000) ≤ ((5637539269679051 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (28433:ℚ) := by decide +kernel
  have hratR : ((((28197951654113029 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5637539269679051 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28433:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3094 : ((((881506474088467 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28439 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28433 < q → q < 28439 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28439).mp (by decide +kernel))) hgap
  have hprev := thV_3093
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28439:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((881506474088467 : ℚ) / 31250000000) ≤ ((28197951654113029 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (28439:ℚ) := by decide +kernel
  have hratR : ((((881506474088467 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((28197951654113029 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28439:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3095 : ((((3527307871101643 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28447 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28439 < q → q < 28447 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28447).mp (by decide +kernel))) hgap
  have hprev := thV_3094
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28447:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3527307871101643 : ℚ) / 125000000000) ≤ ((881506474088467 : ℚ) / 31250000000) + Work.RHContract.RegionI.logLowQ (28447:ℚ) := by decide +kernel
  have hratR : ((((3527307871101643 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((881506474088467 : ℚ) / 31250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28447:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3096 : ((((3528589916135837 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28463 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28447 < q → q < 28463 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28463).mp (by decide +kernel))) hgap
  have hprev := thV_3095
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28463:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3528589916135837 : ℚ) / 125000000000) ≤ ((3527307871101643 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (28463:ℚ) := by decide +kernel
  have hratR : ((((3528589916135837 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((3527307871101643 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28463:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3097 : ((((5647795236221191 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28477 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28463 < q → q < 28477 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28477).mp (by decide +kernel))) hgap
  have hprev := thV_3096
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28477:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5647795236221191 : ℚ) / 200000000000) ≤ ((3528589916135837 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (28477:ℚ) := by decide +kernel
  have hratR : ((((5647795236221191 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((3528589916135837 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28477:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3098 : ((((28249233594824369 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28493 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28477 < q → q < 28493 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28493).mp (by decide +kernel))) hgap
  have hprev := thV_3097
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28493:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((28249233594824369 : ℚ) / 1000000000000) ≤ ((5647795236221191 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (28493:ℚ) := by decide +kernel
  have hratR : ((((28249233594824369 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5647795236221191 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28493:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3099 : ((((28259491219098651 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28499 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28493 < q → q < 28499 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28499).mp (by decide +kernel))) hgap
  have hprev := thV_3098
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28499:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((28259491219098651 : ℚ) / 1000000000000) ≤ ((28249233594824369 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (28499:ℚ) := by decide +kernel
  have hratR : ((((28259491219098651 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((28249233594824369 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28499:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3100 : ((((14134874667248809 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28513 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28499 < q → q < 28513 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28513).mp (by decide +kernel))) hgap
  have hprev := thV_3099
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28513:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14134874667248809 : ℚ) / 500000000000) ≤ ((28259491219098651 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (28513:ℚ) := by decide +kernel
  have hratR : ((((14134874667248809 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((28259491219098651 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28513:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3101 : ((((28280007590173633 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28517 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28513 < q → q < 28517 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28517).mp (by decide +kernel))) hgap
  have hprev := thV_3100
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28517:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((28280007590173633 : ℚ) / 1000000000000) ≤ ((14134874667248809 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (28517:ℚ) := by decide +kernel
  have hratR : ((((28280007590173633 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((14134874667248809 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28517:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3102 : ((((884070829591871 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28537 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28517 < q → q < 28537 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28537).mp (by decide +kernel))) hgap
  have hprev := thV_3101
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28537:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((884070829591871 : ℚ) / 31250000000) ≤ ((28280007590173633 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (28537:ℚ) := by decide +kernel
  have hratR : ((((884070829591871 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((28280007590173633 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28537:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3103 : ((((3537565705483149 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28541 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28537 < q → q < 28541 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28541).mp (by decide +kernel))) hgap
  have hprev := thV_3102
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28541:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3537565705483149 : ℚ) / 125000000000) ≤ ((884070829591871 : ℚ) / 31250000000) + Work.RHContract.RegionI.logLowQ (28541:ℚ) := by decide +kernel
  have hratR : ((((3537565705483149 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((884070829591871 : ℚ) / 31250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28541:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3104 : ((((14155392475496153 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28547 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28541 < q → q < 28547 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28547).mp (by decide +kernel))) hgap
  have hprev := thV_3103
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28547:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14155392475496153 : ℚ) / 500000000000) ≤ ((3537565705483149 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (28547:ℚ) := by decide +kernel
  have hratR : ((((14155392475496153 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((3537565705483149 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28547:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3105 : ((((28321044328176867 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28549 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28547 < q → q < 28549 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28549).mp (by decide +kernel))) hgap
  have hprev := thV_3104
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28549:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((28321044328176867 : ℚ) / 1000000000000) ≤ ((14155392475496153 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (28549:ℚ) := by decide +kernel
  have hratR : ((((28321044328176867 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((14155392475496153 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28549:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3106 : ((((14165652027787531 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28559 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28549 < q → q < 28559 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28559).mp (by decide +kernel))) hgap
  have hprev := thV_3105
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28559:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14165652027787531 : ℚ) / 500000000000) ≤ ((28321044328176867 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (28559:ℚ) := by decide +kernel
  have hratR : ((((14165652027787531 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((28321044328176867 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28559:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3107 : ((((5668312840613557 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28571 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28559 < q → q < 28571 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28571).mp (by decide +kernel))) hgap
  have hprev := thV_3106
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28571:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5668312840613557 : ℚ) / 200000000000) ≤ ((14165652027787531 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (28571:ℚ) := by decide +kernel
  have hratR : ((((5668312840613557 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((14165652027787531 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28571:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3108 : ((((7087956105139777 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28573 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28571 < q → q < 28573 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28573).mp (by decide +kernel))) hgap
  have hprev := thV_3107
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28573:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7087956105139777 : ℚ) / 250000000000) ≤ ((5668312840613557 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (28573:ℚ) := by decide +kernel
  have hratR : ((((7087956105139777 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((5668312840613557 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28573:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3109 : ((((28362084848016837 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28579 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28573 < q → q < 28579 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28579).mp (by decide +kernel))) hgap
  have hprev := thV_3108
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28579:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((28362084848016837 : ℚ) / 1000000000000) ≤ ((7087956105139777 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (28579:ℚ) := by decide +kernel
  have hratR : ((((28362084848016837 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((7087956105139777 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28579:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3110 : ((((28372345695275167 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28591 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28579 < q → q < 28591 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28591).mp (by decide +kernel))) hgap
  have hprev := thV_3109
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28591:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((28372345695275167 : ℚ) / 1000000000000) ≤ ((28362084848016837 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (28591:ℚ) := by decide +kernel
  have hratR : ((((28372345695275167 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((28362084848016837 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28591:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3111 : ((((1773912922022983 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28597 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28591 < q → q < 28597 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28597).mp (by decide +kernel))) hgap
  have hprev := thV_3110
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28597:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1773912922022983 : ℚ) / 62500000000) ≤ ((28372345695275167 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (28597:ℚ) := by decide +kernel
  have hratR : ((((1773912922022983 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((28372345695275167 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28597:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3112 : ((((56785736038501 : ℚ) / 2000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28603 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28597 < q → q < 28603 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28603).mp (by decide +kernel))) hgap
  have hprev := thV_3111
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28603:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((56785736038501 : ℚ) / 2000000000) ≤ ((1773912922022983 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (28603:ℚ) := by decide +kernel
  have hratR : ((((56785736038501 : ℚ) / 2000000000) : ℚ) : ℝ) ≤ ((((1773912922022983 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28603:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3113 : ((((5680625885193793 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28607 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28603 < q → q < 28607 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28607).mp (by decide +kernel))) hgap
  have hprev := thV_3112
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28607:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5680625885193793 : ℚ) / 200000000000) ≤ ((56785736038501 : ℚ) / 2000000000) + Work.RHContract.RegionI.logLowQ (28607:ℚ) := by decide +kernel
  have hratR : ((((5680625885193793 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((56785736038501 : ℚ) / 2000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28607:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3114 : ((((3551673906509653 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28619 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28607 < q → q < 28619 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28619).mp (by decide +kernel))) hgap
  have hprev := thV_3113
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28619:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3551673906509653 : ℚ) / 125000000000) ≤ ((5680625885193793 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (28619:ℚ) := by decide +kernel
  have hratR : ((((3551673906509653 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((5680625885193793 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28619:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3115 : ((((5684730629613337 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28621 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28619 < q → q < 28621 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28621).mp (by decide +kernel))) hgap
  have hprev := thV_3114
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28621:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5684730629613337 : ℚ) / 200000000000) ≤ ((3551673906509653 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (28621:ℚ) := by decide +kernel
  have hratR : ((((5684730629613337 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((3551673906509653 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28621:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3116 : ((((28433915253670457 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28627 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28621 < q → q < 28627 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28627).mp (by decide +kernel))) hgap
  have hprev := thV_3115
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28627:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((28433915253670457 : ℚ) / 1000000000000) ≤ ((5684730629613337 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (28627:ℚ) := by decide +kernel
  have hratR : ((((28433915253670457 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5684730629613337 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28627:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3117 : ((((3555522187374087 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28631 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28627 < q → q < 28631 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28631).mp (by decide +kernel))) hgap
  have hprev := thV_3116
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28631:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3555522187374087 : ℚ) / 125000000000) ≤ ((28433915253670457 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (28631:ℚ) := by decide +kernel
  have hratR : ((((3555522187374087 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((28433915253670457 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28631:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3118 : ((((889201255104789 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28643 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28631 < q → q < 28643 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28643).mp (by decide +kernel))) hgap
  have hprev := thV_3117
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28643:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((889201255104789 : ℚ) / 31250000000) ≤ ((3555522187374087 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (28643:ℚ) := by decide +kernel
  have hratR : ((((889201255104789 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((3555522187374087 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28643:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3119 : ((((3558087879645891 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28649 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28643 < q → q < 28649 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28649).mp (by decide +kernel))) hgap
  have hprev := thV_3118
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28649:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3558087879645891 : ℚ) / 125000000000) ≤ ((889201255104789 : ℚ) / 31250000000) + Work.RHContract.RegionI.logLowQ (28649:ℚ) := by decide +kernel
  have hratR : ((((3558087879645891 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((889201255104789 : ℚ) / 31250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28649:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3120 : ((((14237483095091943 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28657 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28649 < q → q < 28657 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28657).mp (by decide +kernel))) hgap
  have hprev := thV_3119
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28657:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14237483095091943 : ℚ) / 500000000000) ≤ ((3558087879645891 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (28657:ℚ) := by decide +kernel
  have hratR : ((((14237483095091943 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((3558087879645891 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28657:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3121 : ((((5697045896554571 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28661 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28657 < q → q < 28661 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28661).mp (by decide +kernel))) hgap
  have hprev := thV_3120
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28661:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5697045896554571 : ℚ) / 200000000000) ≤ ((14237483095091943 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (28661:ℚ) := by decide +kernel
  have hratR : ((((5697045896554571 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((14237483095091943 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28661:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3122 : ((((1823711542089 : ℚ) / 64000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28663 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28661 < q → q < 28663 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28663).mp (by decide +kernel))) hgap
  have hprev := thV_3121
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28663:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1823711542089 : ℚ) / 64000000) ≤ ((5697045896554571 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (28663:ℚ) := by decide +kernel
  have hratR : ((((1823711542089 : ℚ) / 64000000) : ℚ) : ℝ) ≤ ((((5697045896554571 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28663:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3123 : ((((28505756416815589 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28669 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28663 < q → q < 28669 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28669).mp (by decide +kernel))) hgap
  have hprev := thV_3122
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28669:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((28505756416815589 : ℚ) / 1000000000000) ≤ ((1823711542089 : ℚ) / 64000000) + Work.RHContract.RegionI.logLowQ (28669:ℚ) := by decide +kernel
  have hratR : ((((28505756416815589 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1823711542089 : ℚ) / 64000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28669:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3124 : ((((14258010308074703 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28687 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28669 < q → q < 28687 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28687).mp (by decide +kernel))) hgap
  have hprev := thV_3123
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28687:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14258010308074703 : ℚ) / 500000000000) ≤ ((28505756416815589 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (28687:ℚ) := by decide +kernel
  have hratR : ((((14258010308074703 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((28505756416815589 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28687:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3125 : ((((14263142582006217 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28697 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28687 < q → q < 28697 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28697).mp (by decide +kernel))) hgap
  have hprev := thV_3124
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28697:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14263142582006217 : ℚ) / 500000000000) ≤ ((14258010308074703 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (28697:ℚ) := by decide +kernel
  have hratR : ((((14263142582006217 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((14258010308074703 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28697:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3126 : ((((3567068740116837 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28703 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28697 < q → q < 28703 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28703).mp (by decide +kernel))) hgap
  have hprev := thV_3125
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28703:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3567068740116837 : ℚ) / 125000000000) ≤ ((14263142582006217 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (28703:ℚ) := by decide +kernel
  have hratR : ((((3567068740116837 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((14263142582006217 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28703:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3127 : ((((14273407478267317 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28711 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28703 < q → q < 28711 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28711).mp (by decide +kernel))) hgap
  have hprev := thV_3126
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28711:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14273407478267317 : ℚ) / 500000000000) ≤ ((3567068740116837 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (28711:ℚ) := by decide +kernel
  have hratR : ((((14273407478267317 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((3567068740116837 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28711:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3128 : ((((14278540205002763 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28723 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28711 < q → q < 28723 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28723).mp (by decide +kernel))) hgap
  have hprev := thV_3127
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28723:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14278540205002763 : ℚ) / 500000000000) ≤ ((14273407478267317 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (28723:ℚ) := by decide +kernel
  have hratR : ((((14278540205002763 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((14273407478267317 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28723:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3129 : ((((446364782380413 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28729 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28723 < q → q < 28729 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28729).mp (by decide +kernel))) hgap
  have hprev := thV_3128
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28729:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((446364782380413 : ℚ) / 15625000000) ≤ ((14278540205002763 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (28729:ℚ) := by decide +kernel
  have hratR : ((((446364782380413 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ ((((14278540205002763 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28729:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3130 : ((((14288806250085511 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28751 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28729 < q → q < 28751 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28751).mp (by decide +kernel))) hgap
  have hprev := thV_3129
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28751:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14288806250085511 : ℚ) / 500000000000) ≤ ((446364782380413 : ℚ) / 15625000000) + Work.RHContract.RegionI.logLowQ (28751:ℚ) := by decide +kernel
  have hratR : ((((14288806250085511 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((446364782380413 : ℚ) / 15625000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28751:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3131 : ((((2858787899755599 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28753 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28751 < q → q < 28753 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28753).mp (by decide +kernel))) hgap
  have hprev := thV_3130
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28753:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2858787899755599 : ℚ) / 100000000000) ≤ ((14288806250085511 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (28753:ℚ) := by decide +kernel
  have hratR : ((((2858787899755599 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((14288806250085511 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28753:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3132 : ((((14299072851796533 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28759 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28753 < q → q < 28759 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28759).mp (by decide +kernel))) hgap
  have hprev := thV_3131
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28759:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14299072851796533 : ℚ) / 500000000000) ≤ ((2858787899755599 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (28759:ℚ) := by decide +kernel
  have hratR : ((((14299072851796533 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((2858787899755599 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28759:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3133 : ((((28608412826803797 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28771 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28759 < q → q < 28771 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28771).mp (by decide +kernel))) hgap
  have hprev := thV_3132
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28771:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((28608412826803797 : ℚ) / 1000000000000) ≤ ((14299072851796533 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (28771:ℚ) := by decide +kernel
  have hratR : ((((28608412826803797 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((14299072851796533 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28771:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3134 : ((((14309340287724439 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28789 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28771 < q → q < 28789 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28789).mp (by decide +kernel))) hgap
  have hprev := thV_3133
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28789:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14309340287724439 : ℚ) / 500000000000) ≤ ((28608412826803797 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (28789:ℚ) := by decide +kernel
  have hratR : ((((14309340287724439 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((28608412826803797 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28789:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3135 : ((((3578618557878283 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28793 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28789 < q → q < 28793 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28793).mp (by decide +kernel))) hgap
  have hprev := thV_3134
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28793:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3578618557878283 : ℚ) / 125000000000) ≤ ((14309340287724439 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (28793:ℚ) := by decide +kernel
  have hratR : ((((3578618557878283 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((14309340287724439 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28793:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3136 : ((((28639216836714771 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28807 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28793 < q → q < 28807 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28807).mp (by decide +kernel))) hgap
  have hprev := thV_3135
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28807:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((28639216836714771 : ℚ) / 1000000000000) ≤ ((3578618557878283 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (28807:ℚ) := by decide +kernel
  have hratR : ((((28639216836714771 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3578618557878283 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28807:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3137 : ((((28649485418664299 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28813 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28807 < q → q < 28813 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28813).mp (by decide +kernel))) hgap
  have hprev := thV_3136
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28813:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((28649485418664299 : ℚ) / 1000000000000) ≤ ((28639216836714771 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (28813:ℚ) := by decide +kernel
  have hratR : ((((28649485418664299 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((28639216836714771 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28813:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3138 : ((((1791234633714401 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28817 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28813 < q → q < 28817 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28817).mp (by decide +kernel))) hgap
  have hprev := thV_3137
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28817:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1791234633714401 : ℚ) / 62500000000) ≤ ((28649485418664299 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (28817:ℚ) := by decide +kernel
  have hratR : ((((1791234633714401 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((28649485418664299 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28817:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3139 : ((((28670023553990573 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28837 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28817 < q → q < 28837 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28837).mp (by decide +kernel))) hgap
  have hprev := thV_3138
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28837:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((28670023553990573 : ℚ) / 1000000000000) ≤ ((1791234633714401 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (28837:ℚ) := by decide +kernel
  have hratR : ((((28670023553990573 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1791234633714401 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28837:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3140 : ((((14340146588297557 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28843 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28837 < q → q < 28843 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28843).mp (by decide +kernel))) hgap
  have hprev := thV_3139
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28843:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14340146588297557 : ℚ) / 500000000000) ≤ ((28670023553990573 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (28843:ℚ) := by decide +kernel
  have hratR : ((((14340146588297557 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((28670023553990573 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28843:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3141 : ((((28690563353773167 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28859 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28843 < q → q < 28859 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28859).mp (by decide +kernel))) hgap
  have hprev := thV_3140
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28859:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((28690563353773167 : ℚ) / 1000000000000) ≤ ((14340146588297557 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (28859:ℚ) := by decide +kernel
  have hratR : ((((28690563353773167 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((14340146588297557 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28859:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3142 : ((((28700833808122687 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28867 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28859 < q → q < 28867 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28867).mp (by decide +kernel))) hgap
  have hprev := thV_3141
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28867:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((28700833808122687 : ℚ) / 1000000000000) ≤ ((28690563353773167 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (28867:ℚ) := by decide +kernel
  have hratR : ((((28700833808122687 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((28690563353773167 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28867:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3143 : ((((28711104401029137 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28871 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28867 < q → q < 28871 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28871).mp (by decide +kernel))) hgap
  have hprev := thV_3142
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28871:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((28711104401029137 : ℚ) / 1000000000000) ≤ ((28700833808122687 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (28871:ℚ) := by decide +kernel
  have hratR : ((((28711104401029137 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((28700833808122687 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28871:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3144 : ((((14360687635495933 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28879 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28871 < q → q < 28879 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28879).mp (by decide +kernel))) hgap
  have hprev := thV_3143
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28879:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14360687635495933 : ℚ) / 500000000000) ≤ ((28711104401029137 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (28879:ℚ) := by decide +kernel
  have hratR : ((((14360687635495933 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((28711104401029137 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28879:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3145 : ((((7182911725615951 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28901 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28879 < q → q < 28901 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28901).mp (by decide +kernel))) hgap
  have hprev := thV_3144
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28901:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7182911725615951 : ℚ) / 250000000000) ≤ ((14360687635495933 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (28901:ℚ) := by decide +kernel
  have hratR : ((((7182911725615951 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((14360687635495933 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28901:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3146 : ((((28741918810704469 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28909 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28901 < q → q < 28909 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28909).mp (by decide +kernel))) hgap
  have hprev := thV_3145
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28909:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((28741918810704469 : ℚ) / 1000000000000) ≤ ((7182911725615951 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (28909:ℚ) := by decide +kernel
  have hratR : ((((28741918810704469 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((7182911725615951 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28909:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3147 : ((((28752191133954651 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28921 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28909 < q → q < 28921 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28921).mp (by decide +kernel))) hgap
  have hprev := thV_3146
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28921:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((28752191133954651 : ℚ) / 1000000000000) ≤ ((28741918810704469 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (28921:ℚ) := by decide +kernel
  have hratR : ((((28752191133954651 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((28741918810704469 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28921:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3148 : ((((14381231832322511 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28927 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28921 < q → q < 28927 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28927).mp (by decide +kernel))) hgap
  have hprev := thV_3147
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28927:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14381231832322511 : ℚ) / 500000000000) ≤ ((28752191133954651 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (28927:ℚ) := by decide +kernel
  have hratR : ((((14381231832322511 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((28752191133954651 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28927:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3149 : ((((28772736402732559 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28933 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28927 < q → q < 28933 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28933).mp (by decide +kernel))) hgap
  have hprev := thV_3148
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28933:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((28772736402732559 : ℚ) / 1000000000000) ≤ ((14381231832322511 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (28933:ℚ) := by decide +kernel
  have hratR : ((((28772736402732559 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((14381231832322511 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28933:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3150 : ((((28783009693669009 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28949 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28933 < q → q < 28949 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28949).mp (by decide +kernel))) hgap
  have hprev := thV_3149
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28949:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((28783009693669009 : ℚ) / 1000000000000) ≤ ((28772736402732559 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (28949:ℚ) := by decide +kernel
  have hratR : ((((28783009693669009 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((28772736402732559 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28949:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3151 : ((((28793283399041659 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28961 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28949 < q → q < 28961 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28961).mp (by decide +kernel))) hgap
  have hprev := thV_3150
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28961:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((28793283399041659 : ℚ) / 1000000000000) ≤ ((28783009693669009 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (28961:ℚ) := by decide +kernel
  have hratR : ((((28793283399041659 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((28783009693669009 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28961:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3152 : ((((14401778862873371 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((28979 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28961 < q → q < 28979 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28979).mp (by decide +kernel))) hgap
  have hprev := thV_3151
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (28979:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14401778862873371 : ℚ) / 500000000000) ≤ ((28793283399041659 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (28979:ℚ) := by decide +kernel
  have hratR : ((((14401778862873371 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((28793283399041659 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (28979:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3153 : ((((28813833087148751 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29009 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28979 < q → q < 29009 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29009).mp (by decide +kernel))) hgap
  have hprev := thV_3152
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29009:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((28813833087148751 : ℚ) / 1000000000000) ≤ ((14401778862873371 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (29009:ℚ) := by decide +kernel
  have hratR : ((((28813833087148751 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((14401778862873371 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29009:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3154 : ((((3603013590536153 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29017 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29009 < q → q < 29017 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29017).mp (by decide +kernel))) hgap
  have hprev := thV_3153
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29017:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3603013590536153 : ℚ) / 125000000000) ≤ ((28813833087148751 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (29017:ℚ) := by decide +kernel
  have hratR : ((((3603013590536153 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((28813833087148751 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29017:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3155 : ((((28834384499270423 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29021 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29017 < q → q < 29021 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29021).mp (by decide +kernel))) hgap
  have hprev := thV_3154
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29021:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((28834384499270423 : ℚ) / 1000000000000) ≤ ((3603013590536153 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (29021:ℚ) := by decide +kernel
  have hratR : ((((28834384499270423 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3603013590536153 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29021:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3156 : ((((1442233017158243 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29023 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29021 < q → q < 29023 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29023).mp (by decide +kernel))) hgap
  have hprev := thV_3155
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29023:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1442233017158243 : ℚ) / 50000000000) ≤ ((28834384499270423 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (29023:ℚ) := by decide +kernel
  have hratR : ((((1442233017158243 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((28834384499270423 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29023:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3157 : ((((3606867040608941 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29027 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29023 < q → q < 29027 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29027).mp (by decide +kernel))) hgap
  have hprev := thV_3156
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29027:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3606867040608941 : ℚ) / 125000000000) ≤ ((1442233017158243 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (29027:ℚ) := by decide +kernel
  have hratR : ((((3606867040608941 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((1442233017158243 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29027:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3158 : ((((28865212513260939 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29033 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29027 < q → q < 29033 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29033).mp (by decide +kernel))) hgap
  have hprev := thV_3157
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29033:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((28865212513260939 : ℚ) / 1000000000000) ≤ ((3606867040608941 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (29033:ℚ) := by decide +kernel
  have hratR : ((((28865212513260939 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3606867040608941 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29033:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3159 : ((((28875489596782269 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29059 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29033 < q → q < 29059 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29059).mp (by decide +kernel))) hgap
  have hprev := thV_3158
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29059:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((28875489596782269 : ℚ) / 1000000000000) ≤ ((28865212513260939 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (29059:ℚ) := by decide +kernel
  have hratR : ((((28875489596782269 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((28865212513260939 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29059:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3160 : ((((3610720852243139 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29063 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29059 < q → q < 29063 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29063).mp (by decide +kernel))) hgap
  have hprev := thV_3159
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29063:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3610720852243139 : ℚ) / 125000000000) ≤ ((28875489596782269 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (29063:ℚ) := by decide +kernel
  have hratR : ((((3610720852243139 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((28875489596782269 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29063:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3161 : ((((1806002782544007 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29077 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29063 < q → q < 29077 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29077).mp (by decide +kernel))) hgap
  have hprev := thV_3160
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29077:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1806002782544007 : ℚ) / 62500000000) ≤ ((3610720852243139 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (29077:ℚ) := by decide +kernel
  have hratR : ((((1806002782544007 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((3610720852243139 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29077:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3162 : ((((28906323048517303 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29101 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29077 < q → q < 29101 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29101).mp (by decide +kernel))) hgap
  have hprev := thV_3161
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29101:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((28906323048517303 : ℚ) / 1000000000000) ≤ ((1806002782544007 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (29101:ℚ) := by decide +kernel
  have hratR : ((((28906323048517303 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1806002782544007 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29101:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3163 : ((((14458301166016323 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29123 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29101 < q → q < 29123 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29123).mp (by decide +kernel))) hgap
  have hprev := thV_3162
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29123:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14458301166016323 : ℚ) / 500000000000) ≤ ((28906323048517303 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (29123:ℚ) := by decide +kernel
  have hratR : ((((14458301166016323 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((28906323048517303 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29123:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3164 : ((((57853763643099 : ℚ) / 2000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29129 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29123 < q → q < 29129 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29129).mp (by decide +kernel))) hgap
  have hprev := thV_3163
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29129:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((57853763643099 : ℚ) / 2000000000) ≤ ((14458301166016323 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (29129:ℚ) := by decide +kernel
  have hratR : ((((57853763643099 : ℚ) / 2000000000) : ℚ) : ℝ) ≤ ((((14458301166016323 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29129:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3165 : ((((5787432275944819 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29131 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29129 < q → q < 29131 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29131).mp (by decide +kernel))) hgap
  have hprev := thV_3164
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29131:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5787432275944819 : ℚ) / 200000000000) ≤ ((57853763643099 : ℚ) / 2000000000) + Work.RHContract.RegionI.logLowQ (29131:ℚ) := by decide +kernel
  have hratR : ((((5787432275944819 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((57853763643099 : ℚ) / 2000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29131:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3166 : ((((5789488228768727 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29137 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29131 < q → q < 29137 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29137).mp (by decide +kernel))) hgap
  have hprev := thV_3165
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29137:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5789488228768727 : ℚ) / 200000000000) ≤ ((5787432275944819 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (29137:ℚ) := by decide +kernel
  have hratR : ((((5789488228768727 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((5787432275944819 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29137:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3167 : ((((14478860625555263 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29147 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29137 < q → q < 29147 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29147).mp (by decide +kernel))) hgap
  have hprev := thV_3166
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29147:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14478860625555263 : ℚ) / 500000000000) ≤ ((5789488228768727 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (29147:ℚ) := by decide +kernel
  have hratR : ((((14478860625555263 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((5789488228768727 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29147:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3168 : ((((28968001564209321 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29153 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29147 < q → q < 29153 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29153).mp (by decide +kernel))) hgap
  have hprev := thV_3167
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29153:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((28968001564209321 : ℚ) / 1000000000000) ≤ ((14478860625555263 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (29153:ℚ) := by decide +kernel
  have hratR : ((((28968001564209321 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((14478860625555263 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29153:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3169 : ((((5795656471483573 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29167 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29153 < q → q < 29167 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29167).mp (by decide +kernel))) hgap
  have hprev := thV_3168
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29167:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5795656471483573 : ℚ) / 200000000000) ≤ ((28968001564209321 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (29167:ℚ) := by decide +kernel
  have hratR : ((((5795656471483573 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((28968001564209321 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29167:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3170 : ((((7247140839079297 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29173 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29167 < q → q < 29173 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29173).mp (by decide +kernel))) hgap
  have hprev := thV_3169
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29173:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7247140839079297 : ℚ) / 250000000000) ≤ ((5795656471483573 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (29173:ℚ) := by decide +kernel
  have hratR : ((((7247140839079297 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((5795656471483573 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29173:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3171 : ((((2899884456086499 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29179 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29173 < q → q < 29179 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29179).mp (by decide +kernel))) hgap
  have hprev := thV_3170
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29179:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2899884456086499 : ℚ) / 100000000000) ≤ ((7247140839079297 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (29179:ℚ) := by decide +kernel
  have hratR : ((((2899884456086499 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((7247140839079297 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29179:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3172 : ((((29009126176582919 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29191 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29179 < q → q < 29191 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29191).mp (by decide +kernel))) hgap
  have hprev := thV_3171
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29191:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((29009126176582919 : ℚ) / 1000000000000) ≤ ((2899884456086499 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (29191:ℚ) := by decide +kernel
  have hratR : ((((29009126176582919 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2899884456086499 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29191:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3173 : ((((1160776325392541 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29201 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29191 < q → q < 29201 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29201).mp (by decide +kernel))) hgap
  have hprev := thV_3172
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29201:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1160776325392541 : ℚ) / 40000000000) ≤ ((29009126176582919 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (29201:ℚ) := by decide +kernel
  have hratR : ((((1160776325392541 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((29009126176582919 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29201:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3174 : ((((29029690298495439 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29207 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29201 < q → q < 29207 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29207).mp (by decide +kernel))) hgap
  have hprev := thV_3173
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29207:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((29029690298495439 : ℚ) / 1000000000000) ≤ ((1160776325392541 : ℚ) / 40000000000) + Work.RHContract.RegionI.logLowQ (29207:ℚ) := by decide +kernel
  have hratR : ((((29029690298495439 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1160776325392541 : ℚ) / 40000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29207:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3175 : ((((907499141582867 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29209 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29207 < q → q < 29209 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29209).mp (by decide +kernel))) hgap
  have hprev := thV_3174
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29209:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((907499141582867 : ℚ) / 31250000000) ≤ ((29029690298495439 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (29209:ℚ) := by decide +kernel
  have hratR : ((((907499141582867 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((29029690298495439 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29209:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3176 : ((((14525127586777979 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29221 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29209 < q → q < 29221 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29221).mp (by decide +kernel))) hgap
  have hprev := thV_3175
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29221:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14525127586777979 : ℚ) / 500000000000) ≤ ((907499141582867 : ℚ) / 31250000000) + Work.RHContract.RegionI.logLowQ (29221:ℚ) := by decide +kernel
  have hratR : ((((14525127586777979 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((907499141582867 : ℚ) / 31250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29221:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3177 : ((((5812107631724253 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29231 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29221 < q → q < 29231 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29231).mp (by decide +kernel))) hgap
  have hprev := thV_3176
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29231:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5812107631724253 : ℚ) / 200000000000) ≤ ((14525127586777979 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (29231:ℚ) := by decide +kernel
  have hratR : ((((5812107631724253 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((14525127586777979 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29231:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3178 : ((((5814164310825081 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29243 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29231 < q → q < 29243 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29243).mp (by decide +kernel))) hgap
  have hprev := thV_3177
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29243:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5814164310825081 : ℚ) / 200000000000) ≤ ((5812107631724253 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (29243:ℚ) := by decide +kernel
  have hratR : ((((5814164310825081 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((5812107631724253 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29243:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3179 : ((((46529768357059 : ℚ) / 1600000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29251 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29243 < q → q < 29251 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29251).mp (by decide +kernel))) hgap
  have hprev := thV_3178
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29251:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((46529768357059 : ℚ) / 1600000000) ≤ ((5814164310825081 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (29251:ℚ) := by decide +kernel
  have hratR : ((((46529768357059 : ℚ) / 1600000000) : ℚ) : ℝ) ≤ ((((5814164310825081 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29251:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3180 : ((((3636423688421583 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29269 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29251 < q → q < 29269 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29269).mp (by decide +kernel))) hgap
  have hprev := thV_3179
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29269:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3636423688421583 : ℚ) / 125000000000) ≤ ((46529768357059 : ℚ) / 1600000000) + Work.RHContract.RegionI.logLowQ (29269:ℚ) := by decide +kernel
  have hratR : ((((3636423688421583 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((46529768357059 : ℚ) / 1600000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29269:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3181 : ((((5820334881275913 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29287 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29269 < q → q < 29287 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29287).mp (by decide +kernel))) hgap
  have hprev := thV_3180
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29287:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5820334881275913 : ℚ) / 200000000000) ≤ ((3636423688421583 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (29287:ℚ) := by decide +kernel
  have hratR : ((((5820334881275913 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((3636423688421583 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29287:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3182 : ((((2911195964677661 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29297 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29287 < q → q < 29297 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29297).mp (by decide +kernel))) hgap
  have hprev := thV_3181
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29297:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2911195964677661 : ℚ) / 100000000000) ≤ ((5820334881275913 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (29297:ℚ) := by decide +kernel
  have hratR : ((((2911195964677661 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((5820334881275913 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29297:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3183 : ((((29122245091951813 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29303 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29297 < q → q < 29303 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29303).mp (by decide +kernel))) hgap
  have hprev := thV_3182
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29303:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((29122245091951813 : ℚ) / 1000000000000) ≤ ((2911195964677661 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (29303:ℚ) := by decide +kernel
  have hratR : ((((29122245091951813 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2911195964677661 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29303:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3184 : ((((5826506162019869 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29311 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29303 < q → q < 29311 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29311).mp (by decide +kernel))) hgap
  have hprev := thV_3183
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29311:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5826506162019869 : ℚ) / 200000000000) ≤ ((29122245091951813 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (29311:ℚ) := by decide +kernel
  have hratR : ((((5826506162019869 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((29122245091951813 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29311:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3185 : ((((5828563414793619 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29327 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29311 < q → q < 29327 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29327).mp (by decide +kernel))) hgap
  have hprev := thV_3184
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29327:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5828563414793619 : ℚ) / 200000000000) ≤ ((5826506162019869 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (29327:ℚ) := by decide +kernel
  have hratR : ((((5828563414793619 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((5826506162019869 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29327:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3186 : ((((29153103542405547 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29333 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29327 < q → q < 29333 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29333).mp (by decide +kernel))) hgap
  have hprev := thV_3185
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29333:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((29153103542405547 : ℚ) / 1000000000000) ≤ ((5828563414793619 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (29333:ℚ) := by decide +kernel
  have hratR : ((((29153103542405547 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5828563414793619 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29333:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3187 : ((((1458169510768493 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29339 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29333 < q → q < 29339 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29339).mp (by decide +kernel))) hgap
  have hprev := thV_3186
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29339:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1458169510768493 : ℚ) / 50000000000) ≤ ((29153103542405547 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (29339:ℚ) := by decide +kernel
  have hratR : ((((1458169510768493 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((29153103542405547 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29339:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3188 : ((((29173677160971601 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29347 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29339 < q → q < 29347 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29347).mp (by decide +kernel))) hgap
  have hprev := thV_3187
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29347:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((29173677160971601 : ℚ) / 1000000000000) ≤ ((1458169510768493 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (29347:ℚ) := by decide +kernel
  have hratR : ((((29173677160971601 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1458169510768493 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29347:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3189 : ((((14591982325812653 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29363 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29347 < q → q < 29363 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29363).mp (by decide +kernel))) hgap
  have hprev := thV_3188
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29363:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14591982325812653 : ℚ) / 500000000000) ≤ ((29173677160971601 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (29363:ℚ) := by decide +kernel
  have hratR : ((((14591982325812653 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((29173677160971601 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29363:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3190 : ((((1459712641158823 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29383 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29363 < q → q < 29383 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29383).mp (by decide +kernel))) hgap
  have hprev := thV_3189
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29383:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1459712641158823 : ℚ) / 50000000000) ≤ ((14591982325812653 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (29383:ℚ) := by decide +kernel
  have hratR : ((((1459712641158823 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((14591982325812653 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29383:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3191 : ((((29204541130851487 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29387 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29383 < q → q < 29387 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29387).mp (by decide +kernel))) hgap
  have hprev := thV_3190
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29387:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((29204541130851487 : ℚ) / 1000000000000) ≤ ((1459712641158823 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (29387:ℚ) := by decide +kernel
  have hratR : ((((29204541130851487 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1459712641158823 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29387:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3192 : ((((29214829506581503 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29389 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29387 < q → q < 29389 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29389).mp (by decide +kernel))) hgap
  have hprev := thV_3191
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29389:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((29214829506581503 : ℚ) / 1000000000000) ≤ ((29204541130851487 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (29389:ℚ) := by decide +kernel
  have hratR : ((((29214829506581503 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((29204541130851487 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29389:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3193 : ((((14612559111258503 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29399 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29389 < q → q < 29399 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29399).mp (by decide +kernel))) hgap
  have hprev := thV_3192
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29399:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14612559111258503 : ℚ) / 500000000000) ≤ ((29214829506581503 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (29399:ℚ) := by decide +kernel
  have hratR : ((((14612559111258503 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((29214829506581503 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29399:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3194 : ((((730885175161993 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29401 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29399 < q → q < 29401 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29401).mp (by decide +kernel))) hgap
  have hprev := thV_3193
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29401:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((730885175161993 : ℚ) / 25000000000) ≤ ((14612559111258503 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (29401:ℚ) := by decide +kernel
  have hratR : ((((730885175161993 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((14612559111258503 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29401:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3195 : ((((2924569613050909 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29411 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29401 < q → q < 29411 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29411).mp (by decide +kernel))) hgap
  have hprev := thV_3194
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29411:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2924569613050909 : ℚ) / 100000000000) ≤ ((730885175161993 : ℚ) / 25000000000) + Work.RHContract.RegionI.logLowQ (29411:ℚ) := by decide +kernel
  have hratR : ((((2924569613050909 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((730885175161993 : ℚ) / 25000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29411:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3196 : ((((5851197132493171 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29423 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29411 < q → q < 29423 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29423).mp (by decide +kernel))) hgap
  have hprev := thV_3195
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29423:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5851197132493171 : ℚ) / 200000000000) ≤ ((2924569613050909 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (29423:ℚ) := by decide +kernel
  have hratR : ((((5851197132493171 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((2924569613050909 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29423:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3197 : ((((7316568849580983 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29429 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29423 < q → q < 29429 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29429).mp (by decide +kernel))) hgap
  have hprev := thV_3196
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29429:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7316568849580983 : ℚ) / 250000000000) ≤ ((5851197132493171 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (29429:ℚ) := by decide +kernel
  have hratR : ((((7316568849580983 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((5851197132493171 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29429:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3198 : ((((29276565405985769 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29437 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29429 < q → q < 29437 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29437).mp (by decide +kernel))) hgap
  have hprev := thV_3197
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29437:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((29276565405985769 : ℚ) / 1000000000000) ≤ ((7316568849580983 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (29437:ℚ) := by decide +kernel
  have hratR : ((((29276565405985769 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((7316568849580983 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29437:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3199 : ((((14643427808725977 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29443 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29437 < q → q < 29443 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29443).mp (by decide +kernel))) hgap
  have hprev := thV_3198
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29443:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14643427808725977 : ℚ) / 500000000000) ≤ ((29276565405985769 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (29443:ℚ) := by decide +kernel
  have hratR : ((((14643427808725977 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((29276565405985769 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29443:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3200 : ((((14648573084249889 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29453 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29443 < q → q < 29453 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29453).mp (by decide +kernel))) hgap
  have hprev := thV_3199
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29453:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14648573084249889 : ℚ) / 500000000000) ≤ ((14643427808725977 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (29453:ℚ) := by decide +kernel
  have hratR : ((((14648573084249889 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((14643427808725977 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29453:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3201 : ((((3663429674795641 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29473 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29453 < q → q < 29473 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29473).mp (by decide +kernel))) hgap
  have hprev := thV_3200
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29473:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3663429674795641 : ℚ) / 125000000000) ≤ ((14648573084249889 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (29473:ℚ) := by decide +kernel
  have hratR : ((((3663429674795641 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((14648573084249889 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29473:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3202 : ((((14658864483733261 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29483 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29473 < q → q < 29483 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29483).mp (by decide +kernel))) hgap
  have hprev := thV_3201
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29483:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14658864483733261 : ℚ) / 500000000000) ≤ ((3663429674795641 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (29483:ℚ) := by decide +kernel
  have hratR : ((((14658864483733261 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((3663429674795641 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29483:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3203 : ((((29328021146902941 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29501 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29483 < q → q < 29501 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29501).mp (by decide +kernel))) hgap
  have hprev := thV_3202
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29501:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((29328021146902941 : ℚ) / 1000000000000) ≤ ((14658864483733261 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (29501:ℚ) := by decide +kernel
  have hratR : ((((29328021146902941 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((14658864483733261 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29501:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3204 : ((((29338314207277277 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29527 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29501 < q → q < 29527 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29527).mp (by decide +kernel))) hgap
  have hprev := thV_3203
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29527:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((29338314207277277 : ℚ) / 1000000000000) ≤ ((29328021146902941 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (29527:ℚ) := by decide +kernel
  have hratR : ((((29338314207277277 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((29328021146902941 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29527:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3205 : ((((29348607403111669 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29531 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29527 < q → q < 29531 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29531).mp (by decide +kernel))) hgap
  have hprev := thV_3204
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29531:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((29348607403111669 : ℚ) / 1000000000000) ≤ ((29338314207277277 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (29531:ℚ) := by decide +kernel
  have hratR : ((((29348607403111669 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((29338314207277277 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29531:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3206 : ((((29358900802101747 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29537 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29531 < q → q < 29537 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29537).mp (by decide +kernel))) hgap
  have hprev := thV_3205
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29537:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((29358900802101747 : ℚ) / 1000000000000) ≤ ((29348607403111669 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (29537:ℚ) := by decide +kernel
  have hratR : ((((29358900802101747 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((29348607403111669 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29537:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3207 : ((((2936919521625163 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29567 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29537 < q → q < 29567 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29567).mp (by decide +kernel))) hgap
  have hprev := thV_3206
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29567:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2936919521625163 : ℚ) / 100000000000) ≤ ((29358900802101747 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (29567:ℚ) := by decide +kernel
  have hratR : ((((2936919521625163 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((29358900802101747 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29567:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3208 : ((((14689744849021103 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29569 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29567 < q → q < 29569 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29569).mp (by decide +kernel))) hgap
  have hprev := thV_3207
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29569:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14689744849021103 : ℚ) / 500000000000) ≤ ((2936919521625163 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (29569:ℚ) := by decide +kernel
  have hratR : ((((14689744849021103 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((2936919521625163 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29569:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3209 : ((((29389784315100443 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29573 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29569 < q → q < 29573 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29573).mp (by decide +kernel))) hgap
  have hprev := thV_3208
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29573:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((29389784315100443 : ℚ) / 1000000000000) ≤ ((14689744849021103 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (29573:ℚ) := by decide +kernel
  have hratR : ((((29389784315100443 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((14689744849021103 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29573:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3210 : ((((29400079202639123 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29581 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29573 < q → q < 29581 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29581).mp (by decide +kernel))) hgap
  have hprev := thV_3209
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29581:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((29400079202639123 : ℚ) / 1000000000000) ≤ ((29389784315100443 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (29581:ℚ) := by decide +kernel
  have hratR : ((((29400079202639123 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((29389784315100443 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29581:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3211 : ((((14705187146495067 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29587 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29581 < q → q < 29587 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29587).mp (by decide +kernel))) hgap
  have hprev := thV_3210
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29587:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14705187146495067 : ℚ) / 500000000000) ≤ ((29400079202639123 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (29587:ℚ) := by decide +kernel
  have hratR : ((((14705187146495067 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((29400079202639123 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29587:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3212 : ((((7355167447210613 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29599 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29587 < q → q < 29599 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29599).mp (by decide +kernel))) hgap
  have hprev := thV_3211
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29599:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7355167447210613 : ℚ) / 250000000000) ≤ ((14705187146495067 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (29599:ℚ) := by decide +kernel
  have hratR : ((((7355167447210613 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((14705187146495067 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29599:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3213 : ((((919717677813491 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29611 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29599 < q → q < 29611 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29611).mp (by decide +kernel))) hgap
  have hprev := thV_3212
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29611:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((919717677813491 : ℚ) / 31250000000) ≤ ((7355167447210613 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (29611:ℚ) := by decide +kernel
  have hratR : ((((919717677813491 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((7355167447210613 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29611:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3214 : ((((7360315549729623 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29629 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29611 < q → q < 29629 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29629).mp (by decide +kernel))) hgap
  have hprev := thV_3213
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29629:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7360315549729623 : ℚ) / 250000000000) ≤ ((919717677813491 : ℚ) / 31250000000) + Work.RHContract.RegionI.logLowQ (29629:ℚ) := by decide +kernel
  have hratR : ((((7360315549729623 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((919717677813491 : ℚ) / 31250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29629:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3215 : ((((29451558842799029 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29633 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29629 < q → q < 29633 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29633).mp (by decide +kernel))) hgap
  have hprev := thV_3214
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29633:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((29451558842799029 : ℚ) / 1000000000000) ≤ ((7360315549729623 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (29633:ℚ) := by decide +kernel
  have hratR : ((((29451558842799029 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((7360315549729623 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29633:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3216 : ((((14730927878306211 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29641 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29633 < q → q < 29641 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29641).mp (by decide +kernel))) hgap
  have hprev := thV_3215
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29641:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14730927878306211 : ℚ) / 500000000000) ≤ ((29451558842799029 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (29641:ℚ) := by decide +kernel
  have hratR : ((((14730927878306211 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((29451558842799029 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29641:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3217 : ((((7368038353091421 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29663 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29641 < q → q < 29663 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29663).mp (by decide +kernel))) hgap
  have hprev := thV_3216
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29663:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7368038353091421 : ℚ) / 250000000000) ≤ ((14730927878306211 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (29663:ℚ) := by decide +kernel
  have hratR : ((((7368038353091421 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((14730927878306211 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29663:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3218 : ((((29482451270370683 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29669 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29663 < q → q < 29669 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29669).mp (by decide +kernel))) hgap
  have hprev := thV_3217
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29669:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((29482451270370683 : ℚ) / 1000000000000) ≤ ((7368038353091421 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (29669:ℚ) := by decide +kernel
  have hratR : ((((29482451270370683 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((7368038353091421 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29669:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3219 : ((((14746374597891919 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29671 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29669 < q → q < 29671 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29671).mp (by decide +kernel))) hgap
  have hprev := thV_3218
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29671:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14746374597891919 : ℚ) / 500000000000) ≤ ((29482451270370683 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (29671:ℚ) := by decide +kernel
  have hratR : ((((14746374597891919 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((29482451270370683 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29671:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3220 : ((((29503047525550539 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29683 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29671 < q → q < 29683 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29683).mp (by decide +kernel))) hgap
  have hprev := thV_3219
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29683:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((29503047525550539 : ℚ) / 1000000000000) ≤ ((14746374597891919 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (29683:ℚ) := by decide +kernel
  have hratR : ((((29503047525550539 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((14746374597891919 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29683:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3221 : ((((29513347000098509 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29717 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29683 < q → q < 29717 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29717).mp (by decide +kernel))) hgap
  have hprev := thV_3220
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29717:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((29513347000098509 : ℚ) / 1000000000000) ≤ ((29503047525550539 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (29717:ℚ) := by decide +kernel
  have hratR : ((((29513347000098509 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((29503047525550539 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29717:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3222 : ((((29523646676530733 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29723 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29717 < q → q < 29723 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29723).mp (by decide +kernel))) hgap
  have hprev := thV_3221
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29723:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((29523646676530733 : ℚ) / 1000000000000) ≤ ((29513347000098509 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (29723:ℚ) := by decide +kernel
  have hratR : ((((29523646676530733 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((29513347000098509 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29723:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3223 : ((((2953394695837129 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29741 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29723 < q → q < 29741 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29741).mp (by decide +kernel))) hgap
  have hprev := thV_3222
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29741:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2953394695837129 : ℚ) / 100000000000) ≤ ((29523646676530733 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (29741:ℚ) := by decide +kernel
  have hratR : ((((2953394695837129 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((29523646676530733 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29741:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3224 : ((((7386061910903469 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29753 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29741 < q → q < 29753 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29753).mp (by decide +kernel))) hgap
  have hprev := thV_3223
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29753:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7386061910903469 : ℚ) / 250000000000) ≤ ((2953394695837129 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (29753:ℚ) := by decide +kernel
  have hratR : ((((7386061910903469 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((2953394695837129 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29753:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3225 : ((((7388637132624117 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29759 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29753 < q → q < 29759 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29759).mp (by decide +kernel))) hgap
  have hprev := thV_3224
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29759:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7388637132624117 : ℚ) / 250000000000) ≤ ((7386061910903469 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (29759:ℚ) := by decide +kernel
  have hratR : ((((7388637132624117 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((7386061910903469 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29759:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3226 : ((((29564849484583361 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29761 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29759 < q → q < 29761 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29761).mp (by decide +kernel))) hgap
  have hprev := thV_3225
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29761:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((29564849484583361 : ℚ) / 1000000000000) ≤ ((7388637132624117 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (29761:ℚ) := by decide +kernel
  have hratR : ((((29564849484583361 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((7388637132624117 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29761:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3227 : ((((14787575689528277 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29789 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29761 < q → q < 29789 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29789).mp (by decide +kernel))) hgap
  have hprev := thV_3226
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29789:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14787575689528277 : ℚ) / 500000000000) ≤ ((29564849484583361 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (29789:ℚ) := by decide +kernel
  have hratR : ((((14787575689528277 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((29564849484583361 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29789:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3228 : ((((14792726871695741 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29803 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29789 < q → q < 29803 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29803).mp (by decide +kernel))) hgap
  have hprev := thV_3227
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29803:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14792726871695741 : ℚ) / 500000000000) ≤ ((14787575689528277 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (29803:ℚ) := by decide +kernel
  have hratR : ((((14792726871695741 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((14787575689528277 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29803:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3229 : ((((14797878322220529 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29819 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29803 < q → q < 29819 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29819).mp (by decide +kernel))) hgap
  have hprev := thV_3228
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29819:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14797878322220529 : ℚ) / 500000000000) ≤ ((14792726871695741 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (29819:ℚ) := by decide +kernel
  have hratR : ((((14797878322220529 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((14792726871695741 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29819:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3230 : ((((14803030007439883 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29833 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29819 < q → q < 29833 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29833).mp (by decide +kernel))) hgap
  have hprev := thV_3229
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29833:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14803030007439883 : ℚ) / 500000000000) ≤ ((14797878322220529 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (29833:ℚ) := by decide +kernel
  have hratR : ((((14803030007439883 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((14797878322220529 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29833:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3231 : ((((29616363519389197 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29837 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29833 < q → q < 29837 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29837).mp (by decide +kernel))) hgap
  have hprev := thV_3230
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29837:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((29616363519389197 : ℚ) / 1000000000000) ≤ ((14803030007439883 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (29837:ℚ) := by decide +kernel
  have hratR : ((((29616363519389197 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((14803030007439883 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29837:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3232 : ((((14813333746502327 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29851 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29837 < q → q < 29851 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29851).mp (by decide +kernel))) hgap
  have hprev := thV_3231
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29851:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14813333746502327 : ℚ) / 500000000000) ≤ ((29616363519389197 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (29851:ℚ) := by decide +kernel
  have hratR : ((((14813333746502327 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((29616363519389197 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29851:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3233 : ((((5927394373707183 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29863 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29851 < q → q < 29863 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29863).mp (by decide +kernel))) hgap
  have hprev := thV_3232
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29863:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5927394373707183 : ℚ) / 200000000000) ≤ ((14813333746502327 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (29863:ℚ) := by decide +kernel
  have hratR : ((((5927394373707183 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((14813333746502327 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29863:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3234 : ((((14823638189001611 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29867 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29863 < q → q < 29867 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29867).mp (by decide +kernel))) hgap
  have hprev := thV_3233
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29867:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14823638189001611 : ℚ) / 500000000000) ≤ ((5927394373707183 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (29867:ℚ) := by decide +kernel
  have hratR : ((((14823638189001611 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((5927394373707183 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29867:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3235 : ((((3707197636042621 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29873 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29867 < q → q < 29873 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29873).mp (by decide +kernel))) hgap
  have hprev := thV_3234
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29873:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3707197636042621 : ℚ) / 125000000000) ≤ ((14823638189001611 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (29873:ℚ) := by decide +kernel
  have hratR : ((((3707197636042621 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((14823638189001611 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29873:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3236 : ((((29667885999508813 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29879 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29873 < q → q < 29879 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29879).mp (by decide +kernel))) hgap
  have hprev := thV_3235
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29879:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((29667885999508813 : ℚ) / 1000000000000) ≤ ((3707197636042621 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (29879:ℚ) := by decide +kernel
  have hratR : ((((29667885999508813 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3707197636042621 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29879:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3237 : ((((14839095488805531 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29881 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29879 < q → q < 29881 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29881).mp (by decide +kernel))) hgap
  have hprev := thV_3236
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29881:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14839095488805531 : ℚ) / 500000000000) ≤ ((29667885999508813 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (29881:ℚ) := by decide +kernel
  have hratR : ((((14839095488805531 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((29667885999508813 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29881:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3238 : ((((463882768121361 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29917 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29881 < q → q < 29917 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29917).mp (by decide +kernel))) hgap
  have hprev := thV_3237
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29917:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((463882768121361 : ℚ) / 15625000000) ≤ ((14839095488805531 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (29917:ℚ) := by decide +kernel
  have hratR : ((((463882768121361 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ ((((14839095488805531 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29917:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3239 : ((((14849401737808727 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29921 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29917 < q → q < 29921 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29921).mp (by decide +kernel))) hgap
  have hprev := thV_3238
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29921:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14849401737808727 : ℚ) / 500000000000) ≤ ((463882768121361 : ℚ) / 15625000000) + Work.RHContract.RegionI.logLowQ (29921:ℚ) := by decide +kernel
  have hratR : ((((14849401737808727 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((463882768121361 : ℚ) / 15625000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29921:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3240 : ((((14854554995987879 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29927 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29921 < q → q < 29927 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29927).mp (by decide +kernel))) hgap
  have hprev := thV_3239
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29927:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14854554995987879 : ℚ) / 500000000000) ≤ ((14849401737808727 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (29927:ℚ) := by decide +kernel
  have hratR : ((((14854554995987879 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((14849401737808727 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29927:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3241 : ((((297194171764037 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29947 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29927 < q → q < 29947 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29947).mp (by decide +kernel))) hgap
  have hprev := thV_3240
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29947:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((297194171764037 : ℚ) / 10000000000) ≤ ((14854554995987879 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (29947:ℚ) := by decide +kernel
  have hratR : ((((297194171764037 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ ((((14854554995987879 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29947:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3242 : ((((29729724761459297 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29959 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29947 < q → q < 29959 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29959).mp (by decide +kernel))) hgap
  have hprev := thV_3241
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29959:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((29729724761459297 : ℚ) / 1000000000000) ≤ ((297194171764037 : ℚ) / 10000000000) + Work.RHContract.RegionI.logLowQ (29959:ℚ) := by decide +kernel
  have hratR : ((((29729724761459297 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((297194171764037 : ℚ) / 10000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29959:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3243 : ((((29740033147289019 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29983 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29959 < q → q < 29983 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29983).mp (by decide +kernel))) hgap
  have hprev := thV_3242
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29983:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((29740033147289019 : ℚ) / 1000000000000) ≤ ((29729724761459297 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (29983:ℚ) := by decide +kernel
  have hratR : ((((29740033147289019 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((29729724761459297 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29983:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3244 : ((((14875170866606059 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((29989 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29983 < q → q < 29989 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29989).mp (by decide +kernel))) hgap
  have hprev := thV_3243
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (29989:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14875170866606059 : ℚ) / 500000000000) ≤ ((29740033147289019 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (29989:ℚ) := by decide +kernel
  have hratR : ((((14875170866606059 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((29740033147289019 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (29989:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3245 : ((((29760651052468583 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((30011 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29989 < q → q < 30011 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 30011).mp (by decide +kernel))) hgap
  have hprev := thV_3244
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (30011:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((29760651052468583 : ℚ) / 1000000000000) ≤ ((14875170866606059 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (30011:ℚ) := by decide +kernel
  have hratR : ((((29760651052468583 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((14875170866606059 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (30011:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3246 : ((((29770960438365059 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((30013 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 30011 < q → q < 30013 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 30013).mp (by decide +kernel))) hgap
  have hprev := thV_3245
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (30013:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((29770960438365059 : ℚ) / 1000000000000) ≤ ((29760651052468583 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (30013:ℚ) := by decide +kernel
  have hratR : ((((29770960438365059 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((29760651052468583 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (30013:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3247 : ((((29781270357221809 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((30029 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 30013 < q → q < 30029 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 30029).mp (by decide +kernel))) hgap
  have hprev := thV_3246
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (30029:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((29781270357221809 : ℚ) / 1000000000000) ≤ ((29770960438365059 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (30029:ℚ) := by decide +kernel
  have hratR : ((((29781270357221809 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((29770960438365059 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (30029:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_3248 : ((((14895790437659769 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((30047 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 30029 < q → q < 30047 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 30047).mp (by decide +kernel))) hgap
  have hprev := thV_3247
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (30047:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14895790437659769 : ℚ) / 500000000000) ≤ ((29781270357221809 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (30047:ℚ) := by decide +kernel
  have hratR : ((((14895790437659769 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((29781270357221809 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (30047:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma lrU_0 : Commons.NumberTheory.Mertens.logRatioSum ((2 : ℕ) : ℝ) ≤ ((((6931471809 : ℚ) / 10000000000) : ℚ) : ℝ) := by
  have h2 : Commons.NumberTheory.Mertens.logRatioSum ((2 : ℕ) : ℝ) = Real.log ((((2:ℚ)/((2:ℚ)-1)) : ℚ)) := by
    unfold Commons.NumberTheory.Mertens.logRatioSum
    rw [Nat.floor_natCast, show Nat.primesLE 2 = {2} by decide +kernel, Finset.sum_singleton]
    congr 1
    push_cast
    norm_num
  rw [h2]
  have h4 : Work.RHContract.RegionI.logUpQ ((((2:ℚ)/((2:ℚ)-1)) : ℚ)) ≤ ((6931471809 : ℚ) / 10000000000) := by decide +kernel
  have h5 : Real.log ((((2:ℚ)/((2:ℚ)-1)) : ℚ)) ≤ ((((6931471809 : ℚ) / 10000000000) : ℚ) : ℝ) :=
    le_trans (Work.RHContract.RegionI.le_logUpQ (x := ((2:ℚ)/((2:ℚ)-1))) (by norm_num) (by norm_num))
      (by exact_mod_cast h4)
  exact h5
lemma lrU_1 : Commons.NumberTheory.Mertens.logRatioSum ((3 : ℕ) : ℝ) ≤ ((((1098612289009 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2 < q → q < 3 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3).mp (by decide +kernel))) hgap
  have hprev := lrU_0
  have hcast : (((3:ℕ):ℝ)/(((3:ℕ):ℝ)-1)) = (((3:ℚ)/((3:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((3:ℚ)/((3:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((3:ℚ)/((3:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((3:ℚ)/((3:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((6931471809 : ℚ) / 10000000000) + Work.RHContract.RegionI.logUpQ (((3:ℚ)/((3:ℚ)-1)) : ℚ) ≤ ((1098612289009 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((6931471809 : ℚ) / 10000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((3:ℚ)/((3:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1098612289009 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_2 : Commons.NumberTheory.Mertens.logRatioSum ((5 : ℕ) : ℝ) ≤ ((((330438960081 : ℚ) / 250000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 3 < q → q < 5 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5).mp (by decide +kernel))) hgap
  have hprev := lrU_1
  have hcast : (((5:ℕ):ℝ)/(((5:ℕ):ℝ)-1)) = (((5:ℚ)/((5:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((5:ℚ)/((5:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((5:ℚ)/((5:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((5:ℚ)/((5:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1098612289009 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((5:ℚ)/((5:ℚ)-1)) : ℚ) ≤ ((330438960081 : ℚ) / 250000000000) := by decide +kernel
  have hratR : ((((1098612289009 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((5:ℚ)/((5:ℚ)-1)) : ℚ) : ℝ) ≤ ((((330438960081 : ℚ) / 250000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3 : Commons.NumberTheory.Mertens.logRatioSum ((7 : ℕ) : ℝ) ≤ ((((184488315019 : ℚ) / 125000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 5 < q → q < 7 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7).mp (by decide +kernel))) hgap
  have hprev := lrU_2
  have hcast : (((7:ℕ):ℝ)/(((7:ℕ):ℝ)-1)) = (((7:ℚ)/((7:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((7:ℚ)/((7:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((7:ℚ)/((7:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((7:ℚ)/((7:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((330438960081 : ℚ) / 250000000000) + Work.RHContract.RegionI.logUpQ (((7:ℚ)/((7:ℚ)-1)) : ℚ) ≤ ((184488315019 : ℚ) / 125000000000) := by decide +kernel
  have hratR : ((((330438960081 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((7:ℚ)/((7:ℚ)-1)) : ℚ) : ℝ) ≤ ((((184488315019 : ℚ) / 125000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_4 : Commons.NumberTheory.Mertens.logRatioSum ((11 : ℕ) : ℝ) ≤ ((((1571216699957 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7 < q → q < 11 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11).mp (by decide +kernel))) hgap
  have hprev := lrU_3
  have hcast : (((11:ℕ):ℝ)/(((11:ℕ):ℝ)-1)) = (((11:ℚ)/((11:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((11:ℚ)/((11:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((11:ℚ)/((11:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((11:ℚ)/((11:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((184488315019 : ℚ) / 125000000000) + Work.RHContract.RegionI.logUpQ (((11:ℚ)/((11:ℚ)-1)) : ℚ) ≤ ((1571216699957 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((184488315019 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((11:ℚ)/((11:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1571216699957 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_5 : Commons.NumberTheory.Mertens.logRatioSum ((13 : ℕ) : ℝ) ≤ ((((1651259407631 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11 < q → q < 13 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13).mp (by decide +kernel))) hgap
  have hprev := lrU_4
  have hcast : (((13:ℕ):ℝ)/(((13:ℕ):ℝ)-1)) = (((13:ℚ)/((13:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((13:ℚ)/((13:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((13:ℚ)/((13:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((13:ℚ)/((13:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1571216699957 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((13:ℚ)/((13:ℚ)-1)) : ℚ) ≤ ((1651259407631 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((1571216699957 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((13:ℚ)/((13:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1651259407631 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_6 : Commons.NumberTheory.Mertens.logRatioSum ((17 : ℕ) : ℝ) ≤ ((((213985503681 : ℚ) / 125000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13 < q → q < 17 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17).mp (by decide +kernel))) hgap
  have hprev := lrU_5
  have hcast : (((17:ℕ):ℝ)/(((17:ℕ):ℝ)-1)) = (((17:ℚ)/((17:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((17:ℚ)/((17:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((17:ℚ)/((17:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((17:ℚ)/((17:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1651259407631 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((17:ℚ)/((17:ℚ)-1)) : ℚ) ≤ ((213985503681 : ℚ) / 125000000000) := by decide +kernel
  have hratR : ((((1651259407631 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((17:ℚ)/((17:ℚ)-1)) : ℚ) : ℝ) ≤ ((((213985503681 : ℚ) / 125000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_7 : Commons.NumberTheory.Mertens.logRatioSum ((19 : ℕ) : ℝ) ≤ ((((1765951250719 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17 < q → q < 19 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19).mp (by decide +kernel))) hgap
  have hprev := lrU_6
  have hcast : (((19:ℕ):ℝ)/(((19:ℕ):ℝ)-1)) = (((19:ℚ)/((19:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((19:ℚ)/((19:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((19:ℚ)/((19:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((19:ℚ)/((19:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((213985503681 : ℚ) / 125000000000) + Work.RHContract.RegionI.logUpQ (((19:ℚ)/((19:ℚ)-1)) : ℚ) ≤ ((1765951250719 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((213985503681 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((19:ℚ)/((19:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1765951250719 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_8 : Commons.NumberTheory.Mertens.logRatioSum ((23 : ℕ) : ℝ) ≤ ((((181040301329 : ℚ) / 100000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19 < q → q < 23 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23).mp (by decide +kernel))) hgap
  have hprev := lrU_7
  have hcast : (((23:ℕ):ℝ)/(((23:ℕ):ℝ)-1)) = (((23:ℚ)/((23:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((23:ℚ)/((23:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((23:ℚ)/((23:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((23:ℚ)/((23:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1765951250719 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((23:ℚ)/((23:ℚ)-1)) : ℚ) ≤ ((181040301329 : ℚ) / 100000000000) := by decide +kernel
  have hratR : ((((1765951250719 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((23:ℚ)/((23:ℚ)-1)) : ℚ) : ℝ) ≤ ((((181040301329 : ℚ) / 100000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_9 : Commons.NumberTheory.Mertens.logRatioSum ((29 : ℕ) : ℝ) ≤ ((((922747166551 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23 < q → q < 29 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29).mp (by decide +kernel))) hgap
  have hprev := lrU_8
  have hcast : (((29:ℕ):ℝ)/(((29:ℕ):ℝ)-1)) = (((29:ℚ)/((29:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29:ℚ)/((29:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29:ℚ)/((29:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29:ℚ)/((29:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((181040301329 : ℚ) / 100000000000) + Work.RHContract.RegionI.logUpQ (((29:ℚ)/((29:ℚ)-1)) : ℚ) ≤ ((922747166551 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((181040301329 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29:ℚ)/((29:ℚ)-1)) : ℚ) : ℝ) ≤ ((((922747166551 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_10 : Commons.NumberTheory.Mertens.logRatioSum ((31 : ℕ) : ℝ) ≤ ((((75131366237 : ℚ) / 40000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29 < q → q < 31 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 31).mp (by decide +kernel))) hgap
  have hprev := lrU_9
  have hcast : (((31:ℕ):ℝ)/(((31:ℕ):ℝ)-1)) = (((31:ℚ)/((31:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((31:ℚ)/((31:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((31:ℚ)/((31:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((31:ℚ)/((31:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((922747166551 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((31:ℚ)/((31:ℚ)-1)) : ℚ) ≤ ((75131366237 : ℚ) / 40000000000) := by decide +kernel
  have hratR : ((((922747166551 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((31:ℚ)/((31:ℚ)-1)) : ℚ) : ℝ) ≤ ((((75131366237 : ℚ) / 40000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_11 : Commons.NumberTheory.Mertens.logRatioSum ((37 : ℕ) : ℝ) ≤ ((((952841565057 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 31 < q → q < 37 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 37).mp (by decide +kernel))) hgap
  have hprev := lrU_10
  have hcast : (((37:ℕ):ℝ)/(((37:ℕ):ℝ)-1)) = (((37:ℚ)/((37:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((37:ℚ)/((37:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((37:ℚ)/((37:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((37:ℚ)/((37:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((75131366237 : ℚ) / 40000000000) + Work.RHContract.RegionI.logUpQ (((37:ℚ)/((37:ℚ)-1)) : ℚ) ≤ ((952841565057 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((75131366237 : ℚ) / 40000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((37:ℚ)/((37:ℚ)-1)) : ℚ) : ℝ) ≤ ((((952841565057 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_12 : Commons.NumberTheory.Mertens.logRatioSum ((41 : ℕ) : ℝ) ≤ ((((386075148541 : ℚ) / 200000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 37 < q → q < 41 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 41).mp (by decide +kernel))) hgap
  have hprev := lrU_11
  have hcast : (((41:ℕ):ℝ)/(((41:ℕ):ℝ)-1)) = (((41:ℚ)/((41:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((41:ℚ)/((41:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((41:ℚ)/((41:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((41:ℚ)/((41:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((952841565057 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((41:ℚ)/((41:ℚ)-1)) : ℚ) ≤ ((386075148541 : ℚ) / 200000000000) := by decide +kernel
  have hratR : ((((952841565057 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((41:ℚ)/((41:ℚ)-1)) : ℚ) : ℝ) ≤ ((((386075148541 : ℚ) / 200000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_13 : Commons.NumberTheory.Mertens.logRatioSum ((43 : ℕ) : ℝ) ≤ ((((488476560029 : ℚ) / 250000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 41 < q → q < 43 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 43).mp (by decide +kernel))) hgap
  have hprev := lrU_12
  have hcast : (((43:ℕ):ℝ)/(((43:ℕ):ℝ)-1)) = (((43:ℚ)/((43:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((43:ℚ)/((43:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((43:ℚ)/((43:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((43:ℚ)/((43:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((386075148541 : ℚ) / 200000000000) + Work.RHContract.RegionI.logUpQ (((43:ℚ)/((43:ℚ)-1)) : ℚ) ≤ ((488476560029 : ℚ) / 250000000000) := by decide +kernel
  have hratR : ((((386075148541 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((43:ℚ)/((43:ℚ)-1)) : ℚ) : ℝ) ≤ ((((488476560029 : ℚ) / 250000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_14 : Commons.NumberTheory.Mertens.logRatioSum ((47 : ℕ) : ℝ) ≤ ((((1975412445337 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 43 < q → q < 47 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 47).mp (by decide +kernel))) hgap
  have hprev := lrU_13
  have hcast : (((47:ℕ):ℝ)/(((47:ℕ):ℝ)-1)) = (((47:ℚ)/((47:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((47:ℚ)/((47:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((47:ℚ)/((47:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((47:ℚ)/((47:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((488476560029 : ℚ) / 250000000000) + Work.RHContract.RegionI.logUpQ (((47:ℚ)/((47:ℚ)-1)) : ℚ) ≤ ((1975412445337 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((488476560029 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((47:ℚ)/((47:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1975412445337 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_15 : Commons.NumberTheory.Mertens.logRatioSum ((53 : ℕ) : ℝ) ≤ ((((498615160077 : ℚ) / 250000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 47 < q → q < 53 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 53).mp (by decide +kernel))) hgap
  have hprev := lrU_14
  have hcast : (((53:ℕ):ℝ)/(((53:ℕ):ℝ)-1)) = (((53:ℚ)/((53:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((53:ℚ)/((53:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((53:ℚ)/((53:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((53:ℚ)/((53:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1975412445337 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((53:ℚ)/((53:ℚ)-1)) : ℚ) ≤ ((498615160077 : ℚ) / 250000000000) := by decide +kernel
  have hratR : ((((1975412445337 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((53:ℚ)/((53:ℚ)-1)) : ℚ) : ℝ) ≤ ((((498615160077 : ℚ) / 250000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_16 : Commons.NumberTheory.Mertens.logRatioSum ((59 : ℕ) : ℝ) ≤ ((((502888768417 : ℚ) / 250000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 53 < q → q < 59 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 59).mp (by decide +kernel))) hgap
  have hprev := lrU_15
  have hcast : (((59:ℕ):ℝ)/(((59:ℕ):ℝ)-1)) = (((59:ℚ)/((59:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((59:ℚ)/((59:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((59:ℚ)/((59:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((59:ℚ)/((59:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((498615160077 : ℚ) / 250000000000) + Work.RHContract.RegionI.logUpQ (((59:ℚ)/((59:ℚ)-1)) : ℚ) ≤ ((502888768417 : ℚ) / 250000000000) := by decide +kernel
  have hratR : ((((498615160077 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((59:ℚ)/((59:ℚ)-1)) : ℚ) : ℝ) ≤ ((((502888768417 : ℚ) / 250000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_17 : Commons.NumberTheory.Mertens.logRatioSum ((61 : ℕ) : ℝ) ≤ ((((101404218781 : ℚ) / 50000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 59 < q → q < 61 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 61).mp (by decide +kernel))) hgap
  have hprev := lrU_16
  have hcast : (((61:ℕ):ℝ)/(((61:ℕ):ℝ)-1)) = (((61:ℚ)/((61:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((61:ℚ)/((61:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((61:ℚ)/((61:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((61:ℚ)/((61:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((502888768417 : ℚ) / 250000000000) + Work.RHContract.RegionI.logUpQ (((61:ℚ)/((61:ℚ)-1)) : ℚ) ≤ ((101404218781 : ℚ) / 50000000000) := by decide +kernel
  have hratR : ((((502888768417 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((61:ℚ)/((61:ℚ)-1)) : ℚ) : ℝ) ≤ ((((101404218781 : ℚ) / 50000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_18 : Commons.NumberTheory.Mertens.logRatioSum ((67 : ℕ) : ℝ) ≤ ((((408624450597 : ℚ) / 200000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 61 < q → q < 67 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 67).mp (by decide +kernel))) hgap
  have hprev := lrU_17
  have hcast : (((67:ℕ):ℝ)/(((67:ℕ):ℝ)-1)) = (((67:ℚ)/((67:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((67:ℚ)/((67:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((67:ℚ)/((67:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((67:ℚ)/((67:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((101404218781 : ℚ) / 50000000000) + Work.RHContract.RegionI.logUpQ (((67:ℚ)/((67:ℚ)-1)) : ℚ) ≤ ((408624450597 : ℚ) / 200000000000) := by decide +kernel
  have hratR : ((((101404218781 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((67:ℚ)/((67:ℚ)-1)) : ℚ) : ℝ) ≤ ((((408624450597 : ℚ) / 200000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_19 : Commons.NumberTheory.Mertens.logRatioSum ((71 : ℕ) : ℝ) ≤ ((((2057306887977 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 67 < q → q < 71 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 71).mp (by decide +kernel))) hgap
  have hprev := lrU_18
  have hcast : (((71:ℕ):ℝ)/(((71:ℕ):ℝ)-1)) = (((71:ℚ)/((71:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((71:ℚ)/((71:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((71:ℚ)/((71:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((71:ℚ)/((71:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((408624450597 : ℚ) / 200000000000) + Work.RHContract.RegionI.logUpQ (((71:ℚ)/((71:ℚ)-1)) : ℚ) ≤ ((2057306887977 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((408624450597 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((71:ℚ)/((71:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2057306887977 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_20 : Commons.NumberTheory.Mertens.logRatioSum ((73 : ℕ) : ℝ) ≤ ((((207110021011 : ℚ) / 100000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 71 < q → q < 73 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 73).mp (by decide +kernel))) hgap
  have hprev := lrU_19
  have hcast : (((73:ℕ):ℝ)/(((73:ℕ):ℝ)-1)) = (((73:ℚ)/((73:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((73:ℚ)/((73:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((73:ℚ)/((73:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((73:ℚ)/((73:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2057306887977 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((73:ℚ)/((73:ℚ)-1)) : ℚ) ≤ ((207110021011 : ℚ) / 100000000000) := by decide +kernel
  have hratR : ((((2057306887977 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((73:ℚ)/((73:ℚ)-1)) : ℚ) : ℝ) ≤ ((((207110021011 : ℚ) / 100000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_21 : Commons.NumberTheory.Mertens.logRatioSum ((79 : ℕ) : ℝ) ≤ ((((130239952243 : ℚ) / 62500000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 73 < q → q < 79 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 79).mp (by decide +kernel))) hgap
  have hprev := lrU_20
  have hcast : (((79:ℕ):ℝ)/(((79:ℕ):ℝ)-1)) = (((79:ℚ)/((79:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((79:ℚ)/((79:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((79:ℚ)/((79:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((79:ℚ)/((79:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((207110021011 : ℚ) / 100000000000) + Work.RHContract.RegionI.logUpQ (((79:ℚ)/((79:ℚ)-1)) : ℚ) ≤ ((130239952243 : ℚ) / 62500000000) := by decide +kernel
  have hratR : ((((207110021011 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((79:ℚ)/((79:ℚ)-1)) : ℚ) : ℝ) ≤ ((((130239952243 : ℚ) / 62500000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_22 : Commons.NumberTheory.Mertens.logRatioSum ((83 : ℕ) : ℝ) ≤ ((((2095960596421 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 79 < q → q < 83 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 83).mp (by decide +kernel))) hgap
  have hprev := lrU_21
  have hcast : (((83:ℕ):ℝ)/(((83:ℕ):ℝ)-1)) = (((83:ℚ)/((83:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((83:ℚ)/((83:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((83:ℚ)/((83:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((83:ℚ)/((83:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((130239952243 : ℚ) / 62500000000) + Work.RHContract.RegionI.logUpQ (((83:ℚ)/((83:ℚ)-1)) : ℚ) ≤ ((2095960596421 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((130239952243 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((83:ℚ)/((83:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2095960596421 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_23 : Commons.NumberTheory.Mertens.logRatioSum ((89 : ℕ) : ℝ) ≤ ((((84290406067 : ℚ) / 40000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 83 < q → q < 89 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 89).mp (by decide +kernel))) hgap
  have hprev := lrU_22
  have hcast : (((89:ℕ):ℝ)/(((89:ℕ):ℝ)-1)) = (((89:ℚ)/((89:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((89:ℚ)/((89:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((89:ℚ)/((89:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((89:ℚ)/((89:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2095960596421 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((89:ℚ)/((89:ℚ)-1)) : ℚ) ≤ ((84290406067 : ℚ) / 40000000000) := by decide +kernel
  have hratR : ((((2095960596421 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((89:ℚ)/((89:ℚ)-1)) : ℚ) : ℝ) ≤ ((((84290406067 : ℚ) / 40000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_24 : Commons.NumberTheory.Mertens.logRatioSum ((97 : ℕ) : ℝ) ≤ ((((2117622938711 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 89 < q → q < 97 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 97).mp (by decide +kernel))) hgap
  have hprev := lrU_23
  have hcast : (((97:ℕ):ℝ)/(((97:ℕ):ℝ)-1)) = (((97:ℚ)/((97:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((97:ℚ)/((97:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((97:ℚ)/((97:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((97:ℚ)/((97:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((84290406067 : ℚ) / 40000000000) + Work.RHContract.RegionI.logUpQ (((97:ℚ)/((97:ℚ)-1)) : ℚ) ≤ ((2117622938711 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((84290406067 : ℚ) / 40000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((97:ℚ)/((97:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2117622938711 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_25 : Commons.NumberTheory.Mertens.logRatioSum ((101 : ℕ) : ℝ) ≤ ((((425514653913 : ℚ) / 200000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 97 < q → q < 101 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 101).mp (by decide +kernel))) hgap
  have hprev := lrU_24
  have hcast : (((101:ℕ):ℝ)/(((101:ℕ):ℝ)-1)) = (((101:ℚ)/((101:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((101:ℚ)/((101:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((101:ℚ)/((101:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((101:ℚ)/((101:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2117622938711 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((101:ℚ)/((101:ℚ)-1)) : ℚ) ≤ ((425514653913 : ℚ) / 200000000000) := by decide +kernel
  have hratR : ((((2117622938711 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((101:ℚ)/((101:ℚ)-1)) : ℚ) : ℝ) ≤ ((((425514653913 : ℚ) / 200000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_26 : Commons.NumberTheory.Mertens.logRatioSum ((103 : ℕ) : ℝ) ≤ ((((2137329444511 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 101 < q → q < 103 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 103).mp (by decide +kernel))) hgap
  have hprev := lrU_25
  have hcast : (((103:ℕ):ℝ)/(((103:ℕ):ℝ)-1)) = (((103:ℚ)/((103:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((103:ℚ)/((103:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((103:ℚ)/((103:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((103:ℚ)/((103:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((425514653913 : ℚ) / 200000000000) + Work.RHContract.RegionI.logUpQ (((103:ℚ)/((103:ℚ)-1)) : ℚ) ≤ ((2137329444511 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((425514653913 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((103:ℚ)/((103:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2137329444511 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_27 : Commons.NumberTheory.Mertens.logRatioSum ((107 : ℕ) : ℝ) ≤ ((((2146719184861 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 103 < q → q < 107 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 107).mp (by decide +kernel))) hgap
  have hprev := lrU_26
  have hcast : (((107:ℕ):ℝ)/(((107:ℕ):ℝ)-1)) = (((107:ℚ)/((107:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((107:ℚ)/((107:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((107:ℚ)/((107:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((107:ℚ)/((107:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2137329444511 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((107:ℚ)/((107:ℚ)-1)) : ℚ) ≤ ((2146719184861 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2137329444511 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((107:ℚ)/((107:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2146719184861 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_28 : Commons.NumberTheory.Mertens.logRatioSum ((109 : ℕ) : ℝ) ≤ ((((1077967919983 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 107 < q → q < 109 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 109).mp (by decide +kernel))) hgap
  have hprev := lrU_27
  have hcast : (((109:ℕ):ℝ)/(((109:ℕ):ℝ)-1)) = (((109:ℚ)/((109:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((109:ℚ)/((109:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((109:ℚ)/((109:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((109:ℚ)/((109:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2146719184861 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((109:ℚ)/((109:ℚ)-1)) : ℚ) ≤ ((1077967919983 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((2146719184861 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((109:ℚ)/((109:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1077967919983 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_29 : Commons.NumberTheory.Mertens.logRatioSum ((113 : ℕ) : ℝ) ≤ ((((270603098423 : ℚ) / 125000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 109 < q → q < 113 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 113).mp (by decide +kernel))) hgap
  have hprev := lrU_28
  have hcast : (((113:ℕ):ℝ)/(((113:ℕ):ℝ)-1)) = (((113:ℚ)/((113:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((113:ℚ)/((113:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((113:ℚ)/((113:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((113:ℚ)/((113:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1077967919983 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((113:ℚ)/((113:ℚ)-1)) : ℚ) ≤ ((270603098423 : ℚ) / 125000000000) := by decide +kernel
  have hratR : ((((1077967919983 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((113:ℚ)/((113:ℚ)-1)) : ℚ) : ℝ) ≤ ((((270603098423 : ℚ) / 125000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_30 : Commons.NumberTheory.Mertens.logRatioSum ((127 : ℕ) : ℝ) ≤ ((((543182491723 : ℚ) / 250000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 113 < q → q < 127 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 127).mp (by decide +kernel))) hgap
  have hprev := lrU_29
  have hcast : (((127:ℕ):ℝ)/(((127:ℕ):ℝ)-1)) = (((127:ℚ)/((127:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((127:ℚ)/((127:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((127:ℚ)/((127:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((127:ℚ)/((127:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((270603098423 : ℚ) / 125000000000) + Work.RHContract.RegionI.logUpQ (((127:ℚ)/((127:ℚ)-1)) : ℚ) ≤ ((543182491723 : ℚ) / 250000000000) := by decide +kernel
  have hratR : ((((270603098423 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((127:ℚ)/((127:ℚ)-1)) : ℚ) : ℝ) ≤ ((((543182491723 : ℚ) / 250000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_31 : Commons.NumberTheory.Mertens.logRatioSum ((131 : ℕ) : ℝ) ≤ ((((1090196419819 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 127 < q → q < 131 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 131).mp (by decide +kernel))) hgap
  have hprev := lrU_30
  have hcast : (((131:ℕ):ℝ)/(((131:ℕ):ℝ)-1)) = (((131:ℚ)/((131:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((131:ℚ)/((131:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((131:ℚ)/((131:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((131:ℚ)/((131:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((543182491723 : ℚ) / 250000000000) + Work.RHContract.RegionI.logUpQ (((131:ℚ)/((131:ℚ)-1)) : ℚ) ≤ ((1090196419819 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((543182491723 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((131:ℚ)/((131:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1090196419819 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_32 : Commons.NumberTheory.Mertens.logRatioSum ((137 : ℕ) : ℝ) ≤ ((((2187718879731 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 131 < q → q < 137 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 137).mp (by decide +kernel))) hgap
  have hprev := lrU_31
  have hcast : (((137:ℕ):ℝ)/(((137:ℕ):ℝ)-1)) = (((137:ℚ)/((137:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((137:ℚ)/((137:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((137:ℚ)/((137:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((137:ℚ)/((137:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1090196419819 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((137:ℚ)/((137:ℚ)-1)) : ℚ) ≤ ((2187718879731 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((1090196419819 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((137:ℚ)/((137:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2187718879731 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_33 : Commons.NumberTheory.Mertens.logRatioSum ((139 : ℕ) : ℝ) ≤ ((((438987825541 : ℚ) / 200000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 137 < q → q < 139 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 139).mp (by decide +kernel))) hgap
  have hprev := lrU_32
  have hcast : (((139:ℕ):ℝ)/(((139:ℕ):ℝ)-1)) = (((139:ℚ)/((139:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((139:ℚ)/((139:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((139:ℚ)/((139:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((139:ℚ)/((139:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2187718879731 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((139:ℚ)/((139:ℚ)-1)) : ℚ) ≤ ((438987825541 : ℚ) / 200000000000) := by decide +kernel
  have hratR : ((((2187718879731 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((139:ℚ)/((139:ℚ)-1)) : ℚ) : ℝ) ≤ ((((438987825541 : ℚ) / 200000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_34 : Commons.NumberTheory.Mertens.logRatioSum ((149 : ℕ) : ℝ) ≤ ((((2201673159887 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 139 < q → q < 149 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 149).mp (by decide +kernel))) hgap
  have hprev := lrU_33
  have hcast : (((149:ℕ):ℝ)/(((149:ℕ):ℝ)-1)) = (((149:ℚ)/((149:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((149:ℚ)/((149:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((149:ℚ)/((149:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((149:ℚ)/((149:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((438987825541 : ℚ) / 200000000000) + Work.RHContract.RegionI.logUpQ (((149:ℚ)/((149:ℚ)-1)) : ℚ) ≤ ((2201673159887 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((438987825541 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((149:ℚ)/((149:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2201673159887 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_35 : Commons.NumberTheory.Mertens.logRatioSum ((151 : ℕ) : ℝ) ≤ ((((1104158851303 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 149 < q → q < 151 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 151).mp (by decide +kernel))) hgap
  have hprev := lrU_34
  have hcast : (((151:ℕ):ℝ)/(((151:ℕ):ℝ)-1)) = (((151:ℚ)/((151:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((151:ℚ)/((151:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((151:ℚ)/((151:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((151:ℚ)/((151:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2201673159887 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((151:ℚ)/((151:ℚ)-1)) : ℚ) ≤ ((1104158851303 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((2201673159887 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((151:ℚ)/((151:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1104158851303 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_36 : Commons.NumberTheory.Mertens.logRatioSum ((157 : ℕ) : ℝ) ≤ ((((442941500141 : ℚ) / 200000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 151 < q → q < 157 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 157).mp (by decide +kernel))) hgap
  have hprev := lrU_35
  have hcast : (((157:ℕ):ℝ)/(((157:ℕ):ℝ)-1)) = (((157:ℚ)/((157:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((157:ℚ)/((157:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((157:ℚ)/((157:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((157:ℚ)/((157:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1104158851303 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((157:ℚ)/((157:ℚ)-1)) : ℚ) ≤ ((442941500141 : ℚ) / 200000000000) := by decide +kernel
  have hratR : ((((1104158851303 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((157:ℚ)/((157:ℚ)-1)) : ℚ) : ℝ) ≤ ((((442941500141 : ℚ) / 200000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_37 : Commons.NumberTheory.Mertens.logRatioSum ((163 : ℕ) : ℝ) ≤ ((((55521534157 : ℚ) / 25000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 157 < q → q < 163 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 163).mp (by decide +kernel))) hgap
  have hprev := lrU_36
  have hcast : (((163:ℕ):ℝ)/(((163:ℕ):ℝ)-1)) = (((163:ℚ)/((163:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((163:ℚ)/((163:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((163:ℚ)/((163:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((163:ℚ)/((163:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((442941500141 : ℚ) / 200000000000) + Work.RHContract.RegionI.logUpQ (((163:ℚ)/((163:ℚ)-1)) : ℚ) ≤ ((55521534157 : ℚ) / 25000000000) := by decide +kernel
  have hratR : ((((442941500141 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((163:ℚ)/((163:ℚ)-1)) : ℚ) : ℝ) ≤ ((((55521534157 : ℚ) / 25000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_38 : Commons.NumberTheory.Mertens.logRatioSum ((167 : ℕ) : ℝ) ≤ ((((2226867390341 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 163 < q → q < 167 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 167).mp (by decide +kernel))) hgap
  have hprev := lrU_37
  have hcast : (((167:ℕ):ℝ)/(((167:ℕ):ℝ)-1)) = (((167:ℚ)/((167:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((167:ℚ)/((167:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((167:ℚ)/((167:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((167:ℚ)/((167:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((55521534157 : ℚ) / 25000000000) + Work.RHContract.RegionI.logUpQ (((167:ℚ)/((167:ℚ)-1)) : ℚ) ≤ ((2226867390341 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((55521534157 : ℚ) / 25000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((167:ℚ)/((167:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2226867390341 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_39 : Commons.NumberTheory.Mertens.logRatioSum ((173 : ℕ) : ℝ) ≤ ((((1116332254013 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 167 < q → q < 173 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 173).mp (by decide +kernel))) hgap
  have hprev := lrU_38
  have hcast : (((173:ℕ):ℝ)/(((173:ℕ):ℝ)-1)) = (((173:ℚ)/((173:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((173:ℚ)/((173:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((173:ℚ)/((173:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((173:ℚ)/((173:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2226867390341 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((173:ℚ)/((173:ℚ)-1)) : ℚ) ≤ ((1116332254013 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((2226867390341 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((173:ℚ)/((173:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1116332254013 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_40 : Commons.NumberTheory.Mertens.logRatioSum ((179 : ℕ) : ℝ) ≤ ((((89530670543 : ℚ) / 40000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 173 < q → q < 179 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 179).mp (by decide +kernel))) hgap
  have hprev := lrU_39
  have hcast : (((179:ℕ):ℝ)/(((179:ℕ):ℝ)-1)) = (((179:ℚ)/((179:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((179:ℚ)/((179:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((179:ℚ)/((179:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((179:ℚ)/((179:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1116332254013 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((179:ℚ)/((179:ℚ)-1)) : ℚ) ≤ ((89530670543 : ℚ) / 40000000000) := by decide +kernel
  have hratR : ((((1116332254013 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((179:ℚ)/((179:ℚ)-1)) : ℚ) : ℝ) ≤ ((((89530670543 : ℚ) / 40000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_41 : Commons.NumberTheory.Mertens.logRatioSum ((181 : ℕ) : ℝ) ≤ ((((2243806943951 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 179 < q → q < 181 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 181).mp (by decide +kernel))) hgap
  have hprev := lrU_40
  have hcast : (((181:ℕ):ℝ)/(((181:ℕ):ℝ)-1)) = (((181:ℚ)/((181:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((181:ℚ)/((181:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((181:ℚ)/((181:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((181:ℚ)/((181:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((89530670543 : ℚ) / 40000000000) + Work.RHContract.RegionI.logUpQ (((181:ℚ)/((181:ℚ)-1)) : ℚ) ≤ ((2243806943951 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((89530670543 : ℚ) / 40000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((181:ℚ)/((181:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2243806943951 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_42 : Commons.NumberTheory.Mertens.logRatioSum ((191 : ℕ) : ℝ) ≤ ((((1124528149919 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 181 < q → q < 191 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 191).mp (by decide +kernel))) hgap
  have hprev := lrU_41
  have hcast : (((191:ℕ):ℝ)/(((191:ℕ):ℝ)-1)) = (((191:ℚ)/((191:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((191:ℚ)/((191:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((191:ℚ)/((191:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((191:ℚ)/((191:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2243806943951 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((191:ℚ)/((191:ℚ)-1)) : ℚ) ≤ ((1124528149919 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((2243806943951 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((191:ℚ)/((191:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1124528149919 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_43 : Commons.NumberTheory.Mertens.logRatioSum ((193 : ℕ) : ℝ) ≤ ((((563562779179 : ℚ) / 250000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 191 < q → q < 193 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 193).mp (by decide +kernel))) hgap
  have hprev := lrU_42
  have hcast : (((193:ℕ):ℝ)/(((193:ℕ):ℝ)-1)) = (((193:ℚ)/((193:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((193:ℚ)/((193:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((193:ℚ)/((193:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((193:ℚ)/((193:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1124528149919 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((193:ℚ)/((193:ℚ)-1)) : ℚ) ≤ ((563562779179 : ℚ) / 250000000000) := by decide +kernel
  have hratR : ((((1124528149919 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((193:ℚ)/((193:ℚ)-1)) : ℚ) : ℝ) ≤ ((((563562779179 : ℚ) / 250000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_44 : Commons.NumberTheory.Mertens.logRatioSum ((197 : ℕ) : ℝ) ≤ ((((141208761639 : ℚ) / 62500000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 193 < q → q < 197 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 197).mp (by decide +kernel))) hgap
  have hprev := lrU_43
  have hcast : (((197:ℕ):ℝ)/(((197:ℕ):ℝ)-1)) = (((197:ℚ)/((197:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((197:ℚ)/((197:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((197:ℚ)/((197:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((197:ℚ)/((197:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((563562779179 : ℚ) / 250000000000) + Work.RHContract.RegionI.logUpQ (((197:ℚ)/((197:ℚ)-1)) : ℚ) ≤ ((141208761639 : ℚ) / 62500000000) := by decide +kernel
  have hratR : ((((563562779179 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((197:ℚ)/((197:ℚ)-1)) : ℚ) : ℝ) ≤ ((((141208761639 : ℚ) / 62500000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_45 : Commons.NumberTheory.Mertens.logRatioSum ((199 : ℕ) : ℝ) ≤ ((((1132188990127 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 197 < q → q < 199 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 199).mp (by decide +kernel))) hgap
  have hprev := lrU_44
  have hcast : (((199:ℕ):ℝ)/(((199:ℕ):ℝ)-1)) = (((199:ℚ)/((199:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((199:ℚ)/((199:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((199:ℚ)/((199:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((199:ℚ)/((199:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((141208761639 : ℚ) / 62500000000) + Work.RHContract.RegionI.logUpQ (((199:ℚ)/((199:ℚ)-1)) : ℚ) ≤ ((1132188990127 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((141208761639 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((199:ℚ)/((199:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1132188990127 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_46 : Commons.NumberTheory.Mertens.logRatioSum ((211 : ℕ) : ℝ) ≤ ((((2269128583013 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 199 < q → q < 211 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 211).mp (by decide +kernel))) hgap
  have hprev := lrU_45
  have hcast : (((211:ℕ):ℝ)/(((211:ℕ):ℝ)-1)) = (((211:ℚ)/((211:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((211:ℚ)/((211:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((211:ℚ)/((211:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((211:ℚ)/((211:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1132188990127 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((211:ℚ)/((211:ℚ)-1)) : ℚ) ≤ ((2269128583013 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((1132188990127 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((211:ℚ)/((211:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2269128583013 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_47 : Commons.NumberTheory.Mertens.logRatioSum ((223 : ℕ) : ℝ) ≤ ((((2273622972601 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 211 < q → q < 223 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 223).mp (by decide +kernel))) hgap
  have hprev := lrU_46
  have hcast : (((223:ℕ):ℝ)/(((223:ℕ):ℝ)-1)) = (((223:ℚ)/((223:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((223:ℚ)/((223:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((223:ℚ)/((223:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((223:ℚ)/((223:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2269128583013 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((223:ℚ)/((223:ℚ)-1)) : ℚ) ≤ ((2273622972601 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2269128583013 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((223:ℚ)/((223:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2273622972601 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_48 : Commons.NumberTheory.Mertens.logRatioSum ((227 : ℕ) : ℝ) ≤ ((((2278037990811 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 223 < q → q < 227 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 227).mp (by decide +kernel))) hgap
  have hprev := lrU_47
  have hcast : (((227:ℕ):ℝ)/(((227:ℕ):ℝ)-1)) = (((227:ℚ)/((227:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((227:ℚ)/((227:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((227:ℚ)/((227:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((227:ℚ)/((227:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2273622972601 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((227:ℚ)/((227:ℚ)-1)) : ℚ) ≤ ((2278037990811 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2273622972601 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((227:ℚ)/((227:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2278037990811 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_49 : Commons.NumberTheory.Mertens.logRatioSum ((229 : ℕ) : ℝ) ≤ ((((2282414365411 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 227 < q → q < 229 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 229).mp (by decide +kernel))) hgap
  have hprev := lrU_48
  have hcast : (((229:ℕ):ℝ)/(((229:ℕ):ℝ)-1)) = (((229:ℚ)/((229:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((229:ℚ)/((229:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((229:ℚ)/((229:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((229:ℚ)/((229:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2278037990811 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((229:ℚ)/((229:ℚ)-1)) : ℚ) ≤ ((2282414365411 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2278037990811 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((229:ℚ)/((229:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2282414365411 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_50 : Commons.NumberTheory.Mertens.logRatioSum ((233 : ℕ) : ℝ) ≤ ((((2286715447311 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 229 < q → q < 233 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 233).mp (by decide +kernel))) hgap
  have hprev := lrU_49
  have hcast : (((233:ℕ):ℝ)/(((233:ℕ):ℝ)-1)) = (((233:ℚ)/((233:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((233:ℚ)/((233:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((233:ℚ)/((233:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((233:ℚ)/((233:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2282414365411 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((233:ℚ)/((233:ℚ)-1)) : ℚ) ≤ ((2286715447311 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2282414365411 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((233:ℚ)/((233:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2286715447311 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_51 : Commons.NumberTheory.Mertens.logRatioSum ((239 : ℕ) : ℝ) ≤ ((((572727081393 : ℚ) / 250000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 233 < q → q < 239 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 239).mp (by decide +kernel))) hgap
  have hprev := lrU_50
  have hcast : (((239:ℕ):ℝ)/(((239:ℕ):ℝ)-1)) = (((239:ℚ)/((239:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((239:ℚ)/((239:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((239:ℚ)/((239:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((239:ℚ)/((239:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2286715447311 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((239:ℚ)/((239:ℚ)-1)) : ℚ) ≤ ((572727081393 : ℚ) / 250000000000) := by decide +kernel
  have hratR : ((((2286715447311 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((239:ℚ)/((239:ℚ)-1)) : ℚ) : ℝ) ≤ ((((572727081393 : ℚ) / 250000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_52 : Commons.NumberTheory.Mertens.logRatioSum ((241 : ℕ) : ℝ) ≤ ((((2295066335721 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 239 < q → q < 241 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 241).mp (by decide +kernel))) hgap
  have hprev := lrU_51
  have hcast : (((241:ℕ):ℝ)/(((241:ℕ):ℝ)-1)) = (((241:ℚ)/((241:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((241:ℚ)/((241:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((241:ℚ)/((241:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((241:ℚ)/((241:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((572727081393 : ℚ) / 250000000000) + Work.RHContract.RegionI.logUpQ (((241:ℚ)/((241:ℚ)-1)) : ℚ) ≤ ((2295066335721 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((572727081393 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((241:ℚ)/((241:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2295066335721 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_53 : Commons.NumberTheory.Mertens.logRatioSum ((251 : ℕ) : ℝ) ≤ ((((2299058356991 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 241 < q → q < 251 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 251).mp (by decide +kernel))) hgap
  have hprev := lrU_52
  have hcast : (((251:ℕ):ℝ)/(((251:ℕ):ℝ)-1)) = (((251:ℚ)/((251:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((251:ℚ)/((251:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((251:ℚ)/((251:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((251:ℚ)/((251:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2295066335721 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((251:ℚ)/((251:ℚ)-1)) : ℚ) ≤ ((2299058356991 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2295066335721 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((251:ℚ)/((251:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2299058356991 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_54 : Commons.NumberTheory.Mertens.logRatioSum ((257 : ℕ) : ℝ) ≤ ((((2302956997407 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 251 < q → q < 257 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 257).mp (by decide +kernel))) hgap
  have hprev := lrU_53
  have hcast : (((257:ℕ):ℝ)/(((257:ℕ):ℝ)-1)) = (((257:ℚ)/((257:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((257:ℚ)/((257:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((257:ℚ)/((257:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((257:ℚ)/((257:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2299058356991 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((257:ℚ)/((257:ℚ)-1)) : ℚ) ≤ ((2302956997407 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2299058356991 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((257:ℚ)/((257:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2302956997407 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_55 : Commons.NumberTheory.Mertens.logRatioSum ((263 : ℕ) : ℝ) ≤ ((((18021613483 : ℚ) / 7812500000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 257 < q → q < 263 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 263).mp (by decide +kernel))) hgap
  have hprev := lrU_54
  have hcast : (((263:ℕ):ℝ)/(((263:ℕ):ℝ)-1)) = (((263:ℚ)/((263:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((263:ℚ)/((263:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((263:ℚ)/((263:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((263:ℚ)/((263:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2302956997407 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((263:ℚ)/((263:ℚ)-1)) : ℚ) ≤ ((18021613483 : ℚ) / 7812500000) := by decide +kernel
  have hratR : ((((2302956997407 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((263:ℚ)/((263:ℚ)-1)) : ℚ) : ℝ) ≤ ((((18021613483 : ℚ) / 7812500000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_56 : Commons.NumberTheory.Mertens.logRatioSum ((269 : ℕ) : ℝ) ≤ ((((462098184983 : ℚ) / 200000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 263 < q → q < 269 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 269).mp (by decide +kernel))) hgap
  have hprev := lrU_55
  have hcast : (((269:ℕ):ℝ)/(((269:ℕ):ℝ)-1)) = (((269:ℚ)/((269:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((269:ℚ)/((269:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((269:ℚ)/((269:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((269:ℚ)/((269:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((18021613483 : ℚ) / 7812500000) + Work.RHContract.RegionI.logUpQ (((269:ℚ)/((269:ℚ)-1)) : ℚ) ≤ ((462098184983 : ℚ) / 200000000000) := by decide +kernel
  have hratR : ((((18021613483 : ℚ) / 7812500000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((269:ℚ)/((269:ℚ)-1)) : ℚ) : ℝ) ≤ ((((462098184983 : ℚ) / 200000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_57 : Commons.NumberTheory.Mertens.logRatioSum ((271 : ℕ) : ℝ) ≤ ((((2314187786797 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 269 < q → q < 271 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 271).mp (by decide +kernel))) hgap
  have hprev := lrU_56
  have hcast : (((271:ℕ):ℝ)/(((271:ℕ):ℝ)-1)) = (((271:ℚ)/((271:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((271:ℚ)/((271:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((271:ℚ)/((271:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((271:ℚ)/((271:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((462098184983 : ℚ) / 200000000000) + Work.RHContract.RegionI.logUpQ (((271:ℚ)/((271:ℚ)-1)) : ℚ) ≤ ((2314187786797 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((462098184983 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((271:ℚ)/((271:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2314187786797 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_58 : Commons.NumberTheory.Mertens.logRatioSum ((277 : ℕ) : ℝ) ≤ ((((579451106817 : ℚ) / 250000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 271 < q → q < 277 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 277).mp (by decide +kernel))) hgap
  have hprev := lrU_57
  have hcast : (((277:ℕ):ℝ)/(((277:ℕ):ℝ)-1)) = (((277:ℚ)/((277:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((277:ℚ)/((277:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((277:ℚ)/((277:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((277:ℚ)/((277:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2314187786797 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((277:ℚ)/((277:ℚ)-1)) : ℚ) ≤ ((579451106817 : ℚ) / 250000000000) := by decide +kernel
  have hratR : ((((2314187786797 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((277:ℚ)/((277:ℚ)-1)) : ℚ) : ℝ) ≤ ((((579451106817 : ℚ) / 250000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_59 : Commons.NumberTheory.Mertens.logRatioSum ((281 : ℕ) : ℝ) ≤ ((((2321369493433 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 277 < q → q < 281 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 281).mp (by decide +kernel))) hgap
  have hprev := lrU_58
  have hcast : (((281:ℕ):ℝ)/(((281:ℕ):ℝ)-1)) = (((281:ℚ)/((281:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((281:ℚ)/((281:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((281:ℚ)/((281:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((281:ℚ)/((281:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((579451106817 : ℚ) / 250000000000) + Work.RHContract.RegionI.logUpQ (((281:ℚ)/((281:ℚ)-1)) : ℚ) ≤ ((2321369493433 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((579451106817 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((281:ℚ)/((281:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2321369493433 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_60 : Commons.NumberTheory.Mertens.logRatioSum ((283 : ℕ) : ℝ) ≤ ((((2324909320139 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 281 < q → q < 283 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 283).mp (by decide +kernel))) hgap
  have hprev := lrU_59
  have hcast : (((283:ℕ):ℝ)/(((283:ℕ):ℝ)-1)) = (((283:ℚ)/((283:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((283:ℚ)/((283:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((283:ℚ)/((283:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((283:ℚ)/((283:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2321369493433 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((283:ℚ)/((283:ℚ)-1)) : ℚ) ≤ ((2324909320139 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2321369493433 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((283:ℚ)/((283:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2324909320139 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_61 : Commons.NumberTheory.Mertens.logRatioSum ((293 : ℕ) : ℝ) ≤ ((((291041015861 : ℚ) / 125000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 283 < q → q < 293 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 293).mp (by decide +kernel))) hgap
  have hprev := lrU_60
  have hcast : (((293:ℕ):ℝ)/(((293:ℕ):ℝ)-1)) = (((293:ℚ)/((293:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((293:ℚ)/((293:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((293:ℚ)/((293:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((293:ℚ)/((293:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2324909320139 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((293:ℚ)/((293:ℚ)-1)) : ℚ) ≤ ((291041015861 : ℚ) / 125000000000) := by decide +kernel
  have hratR : ((((2324909320139 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((293:ℚ)/((293:ℚ)-1)) : ℚ) : ℝ) ≤ ((((291041015861 : ℚ) / 125000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_62 : Commons.NumberTheory.Mertens.logRatioSum ((307 : ℕ) : ℝ) ≤ ((((2331590772523 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 293 < q → q < 307 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 307).mp (by decide +kernel))) hgap
  have hprev := lrU_61
  have hcast : (((307:ℕ):ℝ)/(((307:ℕ):ℝ)-1)) = (((307:ℚ)/((307:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((307:ℚ)/((307:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((307:ℚ)/((307:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((307:ℚ)/((307:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((291041015861 : ℚ) / 125000000000) + Work.RHContract.RegionI.logUpQ (((307:ℚ)/((307:ℚ)-1)) : ℚ) ≤ ((2331590772523 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((291041015861 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((307:ℚ)/((307:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2331590772523 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_63 : Commons.NumberTheory.Mertens.logRatioSum ((311 : ℕ) : ℝ) ≤ ((((291851423403 : ℚ) / 125000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 307 < q → q < 311 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 311).mp (by decide +kernel))) hgap
  have hprev := lrU_62
  have hcast : (((311:ℕ):ℝ)/(((311:ℕ):ℝ)-1)) = (((311:ℚ)/((311:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((311:ℚ)/((311:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((311:ℚ)/((311:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((311:ℚ)/((311:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2331590772523 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((311:ℚ)/((311:ℚ)-1)) : ℚ) ≤ ((291851423403 : ℚ) / 125000000000) := by decide +kernel
  have hratR : ((((2331590772523 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((311:ℚ)/((311:ℚ)-1)) : ℚ) : ℝ) ≤ ((((291851423403 : ℚ) / 125000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_64 : Commons.NumberTheory.Mertens.logRatioSum ((313 : ℕ) : ℝ) ≤ ((((467602277991 : ℚ) / 200000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 311 < q → q < 313 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 313).mp (by decide +kernel))) hgap
  have hprev := lrU_63
  have hcast : (((313:ℕ):ℝ)/(((313:ℕ):ℝ)-1)) = (((313:ℚ)/((313:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((313:ℚ)/((313:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((313:ℚ)/((313:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((313:ℚ)/((313:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((291851423403 : ℚ) / 125000000000) + Work.RHContract.RegionI.logUpQ (((313:ℚ)/((313:ℚ)-1)) : ℚ) ≤ ((467602277991 : ℚ) / 200000000000) := by decide +kernel
  have hratR : ((((291851423403 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((313:ℚ)/((313:ℚ)-1)) : ℚ) : ℝ) ≤ ((((467602277991 : ℚ) / 200000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_65 : Commons.NumberTheory.Mertens.logRatioSum ((317 : ℕ) : ℝ) ≤ ((((1170585475123 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 313 < q → q < 317 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 317).mp (by decide +kernel))) hgap
  have hprev := lrU_64
  have hcast : (((317:ℕ):ℝ)/(((317:ℕ):ℝ)-1)) = (((317:ℚ)/((317:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((317:ℚ)/((317:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((317:ℚ)/((317:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((317:ℚ)/((317:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((467602277991 : ℚ) / 200000000000) + Work.RHContract.RegionI.logUpQ (((317:ℚ)/((317:ℚ)-1)) : ℚ) ≤ ((1170585475123 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((467602277991 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((317:ℚ)/((317:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1170585475123 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_66 : Commons.NumberTheory.Mertens.logRatioSum ((331 : ℕ) : ℝ) ≤ ((((2344196671163 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 317 < q → q < 331 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 331).mp (by decide +kernel))) hgap
  have hprev := lrU_65
  have hcast : (((331:ℕ):ℝ)/(((331:ℕ):ℝ)-1)) = (((331:ℚ)/((331:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((331:ℚ)/((331:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((331:ℚ)/((331:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((331:ℚ)/((331:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1170585475123 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((331:ℚ)/((331:ℚ)-1)) : ℚ) ≤ ((2344196671163 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((1170585475123 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((331:ℚ)/((331:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2344196671163 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_67 : Commons.NumberTheory.Mertens.logRatioSum ((337 : ℕ) : ℝ) ≤ ((((2347168441553 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 331 < q → q < 337 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 337).mp (by decide +kernel))) hgap
  have hprev := lrU_66
  have hcast : (((337:ℕ):ℝ)/(((337:ℕ):ℝ)-1)) = (((337:ℚ)/((337:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((337:ℚ)/((337:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((337:ℚ)/((337:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((337:ℚ)/((337:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2344196671163 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((337:ℚ)/((337:ℚ)-1)) : ℚ) ≤ ((2347168441553 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2344196671163 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((337:ℚ)/((337:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2347168441553 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_68 : Commons.NumberTheory.Mertens.logRatioSum ((347 : ℕ) : ℝ) ≤ ((((2350054446443 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 337 < q → q < 347 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 347).mp (by decide +kernel))) hgap
  have hprev := lrU_67
  have hcast : (((347:ℕ):ℝ)/(((347:ℕ):ℝ)-1)) = (((347:ℚ)/((347:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((347:ℚ)/((347:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((347:ℚ)/((347:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((347:ℚ)/((347:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2347168441553 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((347:ℚ)/((347:ℚ)-1)) : ℚ) ≤ ((2350054446443 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2347168441553 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((347:ℚ)/((347:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2350054446443 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_69 : Commons.NumberTheory.Mertens.logRatioSum ((349 : ℕ) : ℝ) ≤ ((((2352923888871 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 347 < q → q < 349 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 349).mp (by decide +kernel))) hgap
  have hprev := lrU_68
  have hcast : (((349:ℕ):ℝ)/(((349:ℕ):ℝ)-1)) = (((349:ℚ)/((349:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((349:ℚ)/((349:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((349:ℚ)/((349:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((349:ℚ)/((349:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2350054446443 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((349:ℚ)/((349:ℚ)-1)) : ℚ) ≤ ((2352923888871 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2350054446443 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((349:ℚ)/((349:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2352923888871 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_70 : Commons.NumberTheory.Mertens.logRatioSum ((353 : ℕ) : ℝ) ≤ ((((2355760770207 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 349 < q → q < 353 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 353).mp (by decide +kernel))) hgap
  have hprev := lrU_69
  have hcast : (((353:ℕ):ℝ)/(((353:ℕ):ℝ)-1)) = (((353:ℚ)/((353:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((353:ℚ)/((353:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((353:ℚ)/((353:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((353:ℚ)/((353:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2352923888871 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((353:ℚ)/((353:ℚ)-1)) : ℚ) ≤ ((2355760770207 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2352923888871 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((353:ℚ)/((353:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2355760770207 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_71 : Commons.NumberTheory.Mertens.logRatioSum ((359 : ℕ) : ℝ) ≤ ((((471710034459 : ℚ) / 200000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 353 < q → q < 359 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 359).mp (by decide +kernel))) hgap
  have hprev := lrU_70
  have hcast : (((359:ℕ):ℝ)/(((359:ℕ):ℝ)-1)) = (((359:ℚ)/((359:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((359:ℚ)/((359:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((359:ℚ)/((359:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((359:ℚ)/((359:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2355760770207 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((359:ℚ)/((359:ℚ)-1)) : ℚ) ≤ ((471710034459 : ℚ) / 200000000000) := by decide +kernel
  have hratR : ((((2355760770207 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((359:ℚ)/((359:ℚ)-1)) : ℚ) : ℝ) ≤ ((((471710034459 : ℚ) / 200000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_72 : Commons.NumberTheory.Mertens.logRatioSum ((367 : ℕ) : ℝ) ≤ ((((2361278686949 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 359 < q → q < 367 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 367).mp (by decide +kernel))) hgap
  have hprev := lrU_71
  have hcast : (((367:ℕ):ℝ)/(((367:ℕ):ℝ)-1)) = (((367:ℚ)/((367:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((367:ℚ)/((367:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((367:ℚ)/((367:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((367:ℚ)/((367:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((471710034459 : ℚ) / 200000000000) + Work.RHContract.RegionI.logUpQ (((367:ℚ)/((367:ℚ)-1)) : ℚ) ≤ ((2361278686949 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((471710034459 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((367:ℚ)/((367:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2361278686949 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_73 : Commons.NumberTheory.Mertens.logRatioSum ((373 : ℕ) : ℝ) ≤ ((((14774770327 : ℚ) / 6250000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 367 < q → q < 373 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 373).mp (by decide +kernel))) hgap
  have hprev := lrU_72
  have hcast : (((373:ℕ):ℝ)/(((373:ℕ):ℝ)-1)) = (((373:ℚ)/((373:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((373:ℚ)/((373:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((373:ℚ)/((373:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((373:ℚ)/((373:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2361278686949 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((373:ℚ)/((373:ℚ)-1)) : ℚ) ≤ ((14774770327 : ℚ) / 6250000000) := by decide +kernel
  have hratR : ((((2361278686949 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((373:ℚ)/((373:ℚ)-1)) : ℚ) : ℝ) ≤ ((((14774770327 : ℚ) / 6250000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_74 : Commons.NumberTheory.Mertens.logRatioSum ((379 : ℕ) : ℝ) ≤ ((((2366605261783 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 373 < q → q < 379 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 379).mp (by decide +kernel))) hgap
  have hprev := lrU_73
  have hcast : (((379:ℕ):ℝ)/(((379:ℕ):ℝ)-1)) = (((379:ℚ)/((379:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((379:ℚ)/((379:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((379:ℚ)/((379:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((379:ℚ)/((379:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((14774770327 : ℚ) / 6250000000) + Work.RHContract.RegionI.logUpQ (((379:ℚ)/((379:ℚ)-1)) : ℚ) ≤ ((2366605261783 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((14774770327 : ℚ) / 6250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((379:ℚ)/((379:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2366605261783 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_75 : Commons.NumberTheory.Mertens.logRatioSum ((383 : ℕ) : ℝ) ≤ ((((1184609821179 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 379 < q → q < 383 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 383).mp (by decide +kernel))) hgap
  have hprev := lrU_74
  have hcast : (((383:ℕ):ℝ)/(((383:ℕ):ℝ)-1)) = (((383:ℚ)/((383:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((383:ℚ)/((383:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((383:ℚ)/((383:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((383:ℚ)/((383:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2366605261783 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((383:ℚ)/((383:ℚ)-1)) : ℚ) ≤ ((1184609821179 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((2366605261783 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((383:ℚ)/((383:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1184609821179 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_76 : Commons.NumberTheory.Mertens.logRatioSum ((389 : ℕ) : ℝ) ≤ ((((1185896823177 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 383 < q → q < 389 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 389).mp (by decide +kernel))) hgap
  have hprev := lrU_75
  have hcast : (((389:ℕ):ℝ)/(((389:ℕ):ℝ)-1)) = (((389:ℚ)/((389:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((389:ℚ)/((389:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((389:ℚ)/((389:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((389:ℚ)/((389:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1184609821179 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((389:ℚ)/((389:ℚ)-1)) : ℚ) ≤ ((1185896823177 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((1184609821179 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((389:ℚ)/((389:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1185896823177 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_77 : Commons.NumberTheory.Mertens.logRatioSum ((397 : ℕ) : ℝ) ≤ ((((2374315715787 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 389 < q → q < 397 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 397).mp (by decide +kernel))) hgap
  have hprev := lrU_76
  have hcast : (((397:ℕ):ℝ)/(((397:ℕ):ℝ)-1)) = (((397:ℚ)/((397:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((397:ℚ)/((397:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((397:ℚ)/((397:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((397:ℚ)/((397:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1185896823177 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((397:ℚ)/((397:ℚ)-1)) : ℚ) ≤ ((2374315715787 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((1185896823177 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((397:ℚ)/((397:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2374315715787 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_78 : Commons.NumberTheory.Mertens.logRatioSum ((401 : ℕ) : ℝ) ≤ ((((1188406297993 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 397 < q → q < 401 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 401).mp (by decide +kernel))) hgap
  have hprev := lrU_77
  have hcast : (((401:ℕ):ℝ)/(((401:ℕ):ℝ)-1)) = (((401:ℚ)/((401:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((401:ℚ)/((401:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((401:ℚ)/((401:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((401:ℚ)/((401:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2374315715787 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((401:ℚ)/((401:ℚ)-1)) : ℚ) ≤ ((1188406297993 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((2374315715787 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((401:ℚ)/((401:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1188406297993 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_79 : Commons.NumberTheory.Mertens.logRatioSum ((409 : ℕ) : ℝ) ≤ ((((19034084621 : ℚ) / 8000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 401 < q → q < 409 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 409).mp (by decide +kernel))) hgap
  have hprev := lrU_78
  have hcast : (((409:ℕ):ℝ)/(((409:ℕ):ℝ)-1)) = (((409:ℚ)/((409:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((409:ℚ)/((409:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((409:ℚ)/((409:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((409:ℚ)/((409:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1188406297993 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((409:ℚ)/((409:ℚ)-1)) : ℚ) ≤ ((19034084621 : ℚ) / 8000000000) := by decide +kernel
  have hratR : ((((1188406297993 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((409:ℚ)/((409:ℚ)-1)) : ℚ) : ℝ) ≤ ((((19034084621 : ℚ) / 8000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_80 : Commons.NumberTheory.Mertens.logRatioSum ((419 : ℕ) : ℝ) ≤ ((((2381650065023 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 409 < q → q < 419 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 419).mp (by decide +kernel))) hgap
  have hprev := lrU_79
  have hcast : (((419:ℕ):ℝ)/(((419:ℕ):ℝ)-1)) = (((419:ℚ)/((419:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((419:ℚ)/((419:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((419:ℚ)/((419:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((419:ℚ)/((419:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((19034084621 : ℚ) / 8000000000) + Work.RHContract.RegionI.logUpQ (((419:ℚ)/((419:ℚ)-1)) : ℚ) ≤ ((2381650065023 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((19034084621 : ℚ) / 8000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((419:ℚ)/((419:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2381650065023 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_81 : Commons.NumberTheory.Mertens.logRatioSum ((421 : ℕ) : ℝ) ≤ ((((596007046857 : ℚ) / 250000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 419 < q → q < 421 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 421).mp (by decide +kernel))) hgap
  have hprev := lrU_80
  have hcast : (((421:ℕ):ℝ)/(((421:ℕ):ℝ)-1)) = (((421:ℚ)/((421:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((421:ℚ)/((421:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((421:ℚ)/((421:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((421:ℚ)/((421:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2381650065023 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((421:ℚ)/((421:ℚ)-1)) : ℚ) ≤ ((596007046857 : ℚ) / 250000000000) := by decide +kernel
  have hratR : ((((2381650065023 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((421:ℚ)/((421:ℚ)-1)) : ℚ) : ℝ) ≤ ((((596007046857 : ℚ) / 250000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_82 : Commons.NumberTheory.Mertens.logRatioSum ((431 : ℕ) : ℝ) ≤ ((((477270213769 : ℚ) / 200000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 421 < q → q < 431 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 431).mp (by decide +kernel))) hgap
  have hprev := lrU_81
  have hcast : (((431:ℕ):ℝ)/(((431:ℕ):ℝ)-1)) = (((431:ℚ)/((431:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((431:ℚ)/((431:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((431:ℚ)/((431:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((431:ℚ)/((431:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((596007046857 : ℚ) / 250000000000) + Work.RHContract.RegionI.logUpQ (((431:ℚ)/((431:ℚ)-1)) : ℚ) ≤ ((477270213769 : ℚ) / 200000000000) := by decide +kernel
  have hratR : ((((596007046857 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((431:ℚ)/((431:ℚ)-1)) : ℚ) : ℝ) ≤ ((((477270213769 : ℚ) / 200000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_83 : Commons.NumberTheory.Mertens.logRatioSum ((433 : ℕ) : ℝ) ≤ ((((597165802151 : ℚ) / 250000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 431 < q → q < 433 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 433).mp (by decide +kernel))) hgap
  have hprev := lrU_82
  have hcast : (((433:ℕ):ℝ)/(((433:ℕ):ℝ)-1)) = (((433:ℚ)/((433:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((433:ℚ)/((433:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((433:ℚ)/((433:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((433:ℚ)/((433:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((477270213769 : ℚ) / 200000000000) + Work.RHContract.RegionI.logUpQ (((433:ℚ)/((433:ℚ)-1)) : ℚ) ≤ ((597165802151 : ℚ) / 250000000000) := by decide +kernel
  have hratR : ((((477270213769 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((433:ℚ)/((433:ℚ)-1)) : ℚ) : ℝ) ≤ ((((597165802151 : ℚ) / 250000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_84 : Commons.NumberTheory.Mertens.logRatioSum ((439 : ℕ) : ℝ) ≤ ((((2390943711303 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 433 < q → q < 439 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 439).mp (by decide +kernel))) hgap
  have hprev := lrU_83
  have hcast : (((439:ℕ):ℝ)/(((439:ℕ):ℝ)-1)) = (((439:ℚ)/((439:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((439:ℚ)/((439:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((439:ℚ)/((439:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((439:ℚ)/((439:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((597165802151 : ℚ) / 250000000000) + Work.RHContract.RegionI.logUpQ (((439:ℚ)/((439:ℚ)-1)) : ℚ) ≤ ((2390943711303 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((597165802151 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((439:ℚ)/((439:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2390943711303 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_85 : Commons.NumberTheory.Mertens.logRatioSum ((443 : ℕ) : ℝ) ≤ ((((2393203599271 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 439 < q → q < 443 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 443).mp (by decide +kernel))) hgap
  have hprev := lrU_84
  have hcast : (((443:ℕ):ℝ)/(((443:ℕ):ℝ)-1)) = (((443:ℚ)/((443:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((443:ℚ)/((443:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((443:ℚ)/((443:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((443:ℚ)/((443:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2390943711303 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((443:ℚ)/((443:ℚ)-1)) : ℚ) ≤ ((2393203599271 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2390943711303 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((443:ℚ)/((443:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2393203599271 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_86 : Commons.NumberTheory.Mertens.logRatioSum ((449 : ℕ) : ℝ) ≤ ((((2395433254599 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 443 < q → q < 449 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 449).mp (by decide +kernel))) hgap
  have hprev := lrU_85
  have hcast : (((449:ℕ):ℝ)/(((449:ℕ):ℝ)-1)) = (((449:ℚ)/((449:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((449:ℚ)/((449:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((449:ℚ)/((449:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((449:ℚ)/((449:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2393203599271 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((449:ℚ)/((449:ℚ)-1)) : ℚ) ≤ ((2395433254599 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2393203599271 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((449:ℚ)/((449:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2395433254599 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_87 : Commons.NumberTheory.Mertens.logRatioSum ((457 : ℕ) : ℝ) ≤ ((((2397623835979 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 449 < q → q < 457 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 457).mp (by decide +kernel))) hgap
  have hprev := lrU_86
  have hcast : (((457:ℕ):ℝ)/(((457:ℕ):ℝ)-1)) = (((457:ℚ)/((457:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((457:ℚ)/((457:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((457:ℚ)/((457:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((457:ℚ)/((457:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2395433254599 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((457:ℚ)/((457:ℚ)-1)) : ℚ) ≤ ((2397623835979 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2395433254599 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((457:ℚ)/((457:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2397623835979 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_88 : Commons.NumberTheory.Mertens.logRatioSum ((461 : ℕ) : ℝ) ≤ ((((2399795389493 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 457 < q → q < 461 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 461).mp (by decide +kernel))) hgap
  have hprev := lrU_87
  have hcast : (((461:ℕ):ℝ)/(((461:ℕ):ℝ)-1)) = (((461:ℚ)/((461:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((461:ℚ)/((461:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((461:ℚ)/((461:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((461:ℚ)/((461:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2397623835979 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((461:ℚ)/((461:ℚ)-1)) : ℚ) ≤ ((2399795389493 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2397623835979 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((461:ℚ)/((461:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2399795389493 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_89 : Commons.NumberTheory.Mertens.logRatioSum ((463 : ℕ) : ℝ) ≤ ((((1200978776249 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 461 < q → q < 463 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 463).mp (by decide +kernel))) hgap
  have hprev := lrU_88
  have hcast : (((463:ℕ):ℝ)/(((463:ℕ):ℝ)-1)) = (((463:ℚ)/((463:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((463:ℚ)/((463:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((463:ℚ)/((463:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((463:ℚ)/((463:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2399795389493 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((463:ℚ)/((463:ℚ)-1)) : ℚ) ≤ ((1200978776249 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((2399795389493 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((463:ℚ)/((463:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1200978776249 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_90 : Commons.NumberTheory.Mertens.logRatioSum ((467 : ℕ) : ℝ) ≤ ((((1202050588021 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 463 < q → q < 467 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 467).mp (by decide +kernel))) hgap
  have hprev := lrU_89
  have hcast : (((467:ℕ):ℝ)/(((467:ℕ):ℝ)-1)) = (((467:ℚ)/((467:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((467:ℚ)/((467:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((467:ℚ)/((467:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((467:ℚ)/((467:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1200978776249 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((467:ℚ)/((467:ℚ)-1)) : ℚ) ≤ ((1202050588021 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((1200978776249 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((467:ℚ)/((467:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1202050588021 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_91 : Commons.NumberTheory.Mertens.logRatioSum ((479 : ℕ) : ℝ) ≤ ((((1203095520481 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 467 < q → q < 479 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 479).mp (by decide +kernel))) hgap
  have hprev := lrU_90
  have hcast : (((479:ℕ):ℝ)/(((479:ℕ):ℝ)-1)) = (((479:ℚ)/((479:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((479:ℚ)/((479:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((479:ℚ)/((479:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((479:ℚ)/((479:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1202050588021 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((479:ℚ)/((479:ℚ)-1)) : ℚ) ≤ ((1203095520481 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((1202050588021 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((479:ℚ)/((479:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1203095520481 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_92 : Commons.NumberTheory.Mertens.logRatioSum ((487 : ℕ) : ℝ) ≤ ((((481649308029 : ℚ) / 200000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 479 < q → q < 487 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 487).mp (by decide +kernel))) hgap
  have hprev := lrU_91
  have hcast : (((487:ℕ):ℝ)/(((487:ℕ):ℝ)-1)) = (((487:ℚ)/((487:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((487:ℚ)/((487:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((487:ℚ)/((487:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((487:ℚ)/((487:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1203095520481 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((487:ℚ)/((487:ℚ)-1)) : ℚ) ≤ ((481649308029 : ℚ) / 200000000000) := by decide +kernel
  have hratR : ((((1203095520481 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((487:ℚ)/((487:ℚ)-1)) : ℚ) : ℝ) ≤ ((((481649308029 : ℚ) / 200000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_93 : Commons.NumberTheory.Mertens.logRatioSum ((491 : ℕ) : ℝ) ≤ ((((482057055367 : ℚ) / 200000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 487 < q → q < 491 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 491).mp (by decide +kernel))) hgap
  have hprev := lrU_92
  have hcast : (((491:ℕ):ℝ)/(((491:ℕ):ℝ)-1)) = (((491:ℚ)/((491:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((491:ℚ)/((491:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((491:ℚ)/((491:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((491:ℚ)/((491:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((481649308029 : ℚ) / 200000000000) + Work.RHContract.RegionI.logUpQ (((491:ℚ)/((491:ℚ)-1)) : ℚ) ≤ ((482057055367 : ℚ) / 200000000000) := by decide +kernel
  have hratR : ((((481649308029 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((491:ℚ)/((491:ℚ)-1)) : ℚ) : ℝ) ≤ ((((482057055367 : ℚ) / 200000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_94 : Commons.NumberTheory.Mertens.logRatioSum ((499 : ℕ) : ℝ) ≤ ((((1206145647781 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 491 < q → q < 499 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 499).mp (by decide +kernel))) hgap
  have hprev := lrU_93
  have hcast : (((499:ℕ):ℝ)/(((499:ℕ):ℝ)-1)) = (((499:ℚ)/((499:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((499:ℚ)/((499:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((499:ℚ)/((499:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((499:ℚ)/((499:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((482057055367 : ℚ) / 200000000000) + Work.RHContract.RegionI.logUpQ (((499:ℚ)/((499:ℚ)-1)) : ℚ) ≤ ((1206145647781 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((482057055367 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((499:ℚ)/((499:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1206145647781 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_95 : Commons.NumberTheory.Mertens.logRatioSum ((503 : ℕ) : ℝ) ≤ ((((2414281345971 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 499 < q → q < 503 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 503).mp (by decide +kernel))) hgap
  have hprev := lrU_94
  have hcast : (((503:ℕ):ℝ)/(((503:ℕ):ℝ)-1)) = (((503:ℚ)/((503:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((503:ℚ)/((503:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((503:ℚ)/((503:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((503:ℚ)/((503:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1206145647781 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((503:ℚ)/((503:ℚ)-1)) : ℚ) ≤ ((2414281345971 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((1206145647781 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((503:ℚ)/((503:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2414281345971 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_96 : Commons.NumberTheory.Mertens.logRatioSum ((509 : ℕ) : ℝ) ≤ ((((37753873671 : ℚ) / 15625000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 503 < q → q < 509 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 509).mp (by decide +kernel))) hgap
  have hprev := lrU_95
  have hcast : (((509:ℕ):ℝ)/(((509:ℕ):ℝ)-1)) = (((509:ℚ)/((509:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((509:ℚ)/((509:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((509:ℚ)/((509:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((509:ℚ)/((509:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2414281345971 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((509:ℚ)/((509:ℚ)-1)) : ℚ) ≤ ((37753873671 : ℚ) / 15625000000) := by decide +kernel
  have hratR : ((((2414281345971 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((509:ℚ)/((509:ℚ)-1)) : ℚ) : ℝ) ≤ ((((37753873671 : ℚ) / 15625000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_97 : Commons.NumberTheory.Mertens.logRatioSum ((521 : ℕ) : ℝ) ≤ ((((1209084572561 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 509 < q → q < 521 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 521).mp (by decide +kernel))) hgap
  have hprev := lrU_96
  have hcast : (((521:ℕ):ℝ)/(((521:ℕ):ℝ)-1)) = (((521:ℚ)/((521:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((521:ℚ)/((521:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((521:ℚ)/((521:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((521:ℚ)/((521:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((37753873671 : ℚ) / 15625000000) + Work.RHContract.RegionI.logUpQ (((521:ℚ)/((521:ℚ)-1)) : ℚ) ≤ ((1209084572561 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((37753873671 : ℚ) / 15625000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((521:ℚ)/((521:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1209084572561 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_98 : Commons.NumberTheory.Mertens.logRatioSum ((523 : ℕ) : ℝ) ≤ ((((484016604261 : ℚ) / 200000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 521 < q → q < 523 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 523).mp (by decide +kernel))) hgap
  have hprev := lrU_97
  have hcast : (((523:ℕ):ℝ)/(((523:ℕ):ℝ)-1)) = (((523:ℚ)/((523:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((523:ℚ)/((523:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((523:ℚ)/((523:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((523:ℚ)/((523:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1209084572561 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((523:ℚ)/((523:ℚ)-1)) : ℚ) ≤ ((484016604261 : ℚ) / 200000000000) := by decide +kernel
  have hratR : ((((1209084572561 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((523:ℚ)/((523:ℚ)-1)) : ℚ) : ℝ) ≤ ((((484016604261 : ℚ) / 200000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_99 : Commons.NumberTheory.Mertens.logRatioSum ((541 : ℕ) : ℝ) ≤ ((((1210966580297 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 523 < q → q < 541 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 541).mp (by decide +kernel))) hgap
  have hprev := lrU_98
  have hcast : (((541:ℕ):ℝ)/(((541:ℕ):ℝ)-1)) = (((541:ℚ)/((541:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((541:ℚ)/((541:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((541:ℚ)/((541:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((541:ℚ)/((541:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((484016604261 : ℚ) / 200000000000) + Work.RHContract.RegionI.logUpQ (((541:ℚ)/((541:ℚ)-1)) : ℚ) ≤ ((1210966580297 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((484016604261 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((541:ℚ)/((541:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1210966580297 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_100 : Commons.NumberTheory.Mertens.logRatioSum ((547 : ℕ) : ℝ) ≤ ((((302970373409 : ℚ) / 125000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 541 < q → q < 547 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 547).mp (by decide +kernel))) hgap
  have hprev := lrU_99
  have hcast : (((547:ℕ):ℝ)/(((547:ℕ):ℝ)-1)) = (((547:ℚ)/((547:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((547:ℚ)/((547:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((547:ℚ)/((547:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((547:ℚ)/((547:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1210966580297 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((547:ℚ)/((547:ℚ)-1)) : ℚ) ≤ ((302970373409 : ℚ) / 125000000000) := by decide +kernel
  have hratR : ((((1210966580297 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((547:ℚ)/((547:ℚ)-1)) : ℚ) : ℝ) ≤ ((((302970373409 : ℚ) / 125000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_101 : Commons.NumberTheory.Mertens.logRatioSum ((557 : ℕ) : ℝ) ≤ ((((2425559932949 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 547 < q → q < 557 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 557).mp (by decide +kernel))) hgap
  have hprev := lrU_100
  have hcast : (((557:ℕ):ℝ)/(((557:ℕ):ℝ)-1)) = (((557:ℚ)/((557:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((557:ℚ)/((557:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((557:ℚ)/((557:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((557:ℚ)/((557:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((302970373409 : ℚ) / 125000000000) + Work.RHContract.RegionI.logUpQ (((557:ℚ)/((557:ℚ)-1)) : ℚ) ≤ ((2425559932949 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((302970373409 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((557:ℚ)/((557:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2425559932949 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_102 : Commons.NumberTheory.Mertens.logRatioSum ((563 : ℕ) : ℝ) ≤ ((((485467542239 : ℚ) / 200000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 557 < q → q < 563 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 563).mp (by decide +kernel))) hgap
  have hprev := lrU_101
  have hcast : (((563:ℕ):ℝ)/(((563:ℕ):ℝ)-1)) = (((563:ℚ)/((563:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((563:ℚ)/((563:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((563:ℚ)/((563:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((563:ℚ)/((563:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2425559932949 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((563:ℚ)/((563:ℚ)-1)) : ℚ) ≤ ((485467542239 : ℚ) / 200000000000) := by decide +kernel
  have hratR : ((((2425559932949 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((563:ℚ)/((563:ℚ)-1)) : ℚ) : ℝ) ≤ ((((485467542239 : ℚ) / 200000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_103 : Commons.NumberTheory.Mertens.logRatioSum ((569 : ℕ) : ℝ) ≤ ((((2429096726601 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 563 < q → q < 569 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 569).mp (by decide +kernel))) hgap
  have hprev := lrU_102
  have hcast : (((569:ℕ):ℝ)/(((569:ℕ):ℝ)-1)) = (((569:ℚ)/((569:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((569:ℚ)/((569:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((569:ℚ)/((569:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((569:ℚ)/((569:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((485467542239 : ℚ) / 200000000000) + Work.RHContract.RegionI.logUpQ (((569:ℚ)/((569:ℚ)-1)) : ℚ) ≤ ((2429096726601 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((485467542239 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((569:ℚ)/((569:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2429096726601 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_104 : Commons.NumberTheory.Mertens.logRatioSum ((571 : ℕ) : ℝ) ≤ ((((2430849575429 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 569 < q → q < 571 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 571).mp (by decide +kernel))) hgap
  have hprev := lrU_103
  have hcast : (((571:ℕ):ℝ)/(((571:ℕ):ℝ)-1)) = (((571:ℚ)/((571:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((571:ℚ)/((571:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((571:ℚ)/((571:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((571:ℚ)/((571:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2429096726601 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((571:ℚ)/((571:ℚ)-1)) : ℚ) ≤ ((2430849575429 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2429096726601 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((571:ℚ)/((571:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2430849575429 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_105 : Commons.NumberTheory.Mertens.logRatioSum ((577 : ℕ) : ℝ) ≤ ((((1216292090621 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 571 < q → q < 577 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 577).mp (by decide +kernel))) hgap
  have hprev := lrU_104
  have hcast : (((577:ℕ):ℝ)/(((577:ℕ):ℝ)-1)) = (((577:ℚ)/((577:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((577:ℚ)/((577:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((577:ℚ)/((577:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((577:ℚ)/((577:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2430849575429 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((577:ℚ)/((577:ℚ)-1)) : ℚ) ≤ ((1216292090621 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((2430849575429 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((577:ℚ)/((577:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1216292090621 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_106 : Commons.NumberTheory.Mertens.logRatioSum ((587 : ℕ) : ℝ) ≤ ((((1217144605747 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 577 < q → q < 587 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 587).mp (by decide +kernel))) hgap
  have hprev := lrU_105
  have hcast : (((587:ℕ):ℝ)/(((587:ℕ):ℝ)-1)) = (((587:ℚ)/((587:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((587:ℚ)/((587:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((587:ℚ)/((587:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((587:ℚ)/((587:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1216292090621 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((587:ℚ)/((587:ℚ)-1)) : ℚ) ≤ ((1217144605747 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((1216292090621 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((587:ℚ)/((587:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1217144605747 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_107 : Commons.NumberTheory.Mertens.logRatioSum ((593 : ℕ) : ℝ) ≤ ((((304497121951 : ℚ) / 125000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 587 < q → q < 593 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 593).mp (by decide +kernel))) hgap
  have hprev := lrU_106
  have hcast : (((593:ℕ):ℝ)/(((593:ℕ):ℝ)-1)) = (((593:ℚ)/((593:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((593:ℚ)/((593:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((593:ℚ)/((593:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((593:ℚ)/((593:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1217144605747 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((593:ℚ)/((593:ℚ)-1)) : ℚ) ≤ ((304497121951 : ℚ) / 125000000000) := by decide +kernel
  have hratR : ((((1217144605747 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((593:ℚ)/((593:ℚ)-1)) : ℚ) : ℝ) ≤ ((((304497121951 : ℚ) / 125000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_108 : Commons.NumberTheory.Mertens.logRatioSum ((599 : ℕ) : ℝ) ≤ ((((2437647819773 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 593 < q → q < 599 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 599).mp (by decide +kernel))) hgap
  have hprev := lrU_107
  have hcast : (((599:ℕ):ℝ)/(((599:ℕ):ℝ)-1)) = (((599:ℚ)/((599:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((599:ℚ)/((599:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((599:ℚ)/((599:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((599:ℚ)/((599:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((304497121951 : ℚ) / 125000000000) + Work.RHContract.RegionI.logUpQ (((599:ℚ)/((599:ℚ)-1)) : ℚ) ≤ ((2437647819773 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((304497121951 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((599:ℚ)/((599:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2437647819773 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_109 : Commons.NumberTheory.Mertens.logRatioSum ((601 : ℕ) : ℝ) ≤ ((((2439313099093 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 599 < q → q < 601 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 601).mp (by decide +kernel))) hgap
  have hprev := lrU_108
  have hcast : (((601:ℕ):ℝ)/(((601:ℕ):ℝ)-1)) = (((601:ℚ)/((601:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((601:ℚ)/((601:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((601:ℚ)/((601:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((601:ℚ)/((601:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2437647819773 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((601:ℚ)/((601:ℚ)-1)) : ℚ) ≤ ((2439313099093 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2437647819773 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((601:ℚ)/((601:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2439313099093 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_110 : Commons.NumberTheory.Mertens.logRatioSum ((607 : ℕ) : ℝ) ≤ ((((610240476021 : ℚ) / 250000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 601 < q → q < 607 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 607).mp (by decide +kernel))) hgap
  have hprev := lrU_109
  have hcast : (((607:ℕ):ℝ)/(((607:ℕ):ℝ)-1)) = (((607:ℚ)/((607:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((607:ℚ)/((607:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((607:ℚ)/((607:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((607:ℚ)/((607:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2439313099093 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((607:ℚ)/((607:ℚ)-1)) : ℚ) ≤ ((610240476021 : ℚ) / 250000000000) := by decide +kernel
  have hratR : ((((2439313099093 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((607:ℚ)/((607:ℚ)-1)) : ℚ) : ℝ) ≤ ((((610240476021 : ℚ) / 250000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_111 : Commons.NumberTheory.Mertens.logRatioSum ((613 : ℕ) : ℝ) ≤ ((((610648639377 : ℚ) / 250000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 607 < q → q < 613 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 613).mp (by decide +kernel))) hgap
  have hprev := lrU_110
  have hcast : (((613:ℕ):ℝ)/(((613:ℕ):ℝ)-1)) = (((613:ℚ)/((613:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((613:ℚ)/((613:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((613:ℚ)/((613:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((613:ℚ)/((613:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((610240476021 : ℚ) / 250000000000) + Work.RHContract.RegionI.logUpQ (((613:ℚ)/((613:ℚ)-1)) : ℚ) ≤ ((610648639377 : ℚ) / 250000000000) := by decide +kernel
  have hratR : ((((610240476021 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((613:ℚ)/((613:ℚ)-1)) : ℚ) : ℝ) ≤ ((((610648639377 : ℚ) / 250000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_112 : Commons.NumberTheory.Mertens.logRatioSum ((617 : ℕ) : ℝ) ≤ ((((61105415447 : ℚ) / 25000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 613 < q → q < 617 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 617).mp (by decide +kernel))) hgap
  have hprev := lrU_111
  have hcast : (((617:ℕ):ℝ)/(((617:ℕ):ℝ)-1)) = (((617:ℚ)/((617:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((617:ℚ)/((617:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((617:ℚ)/((617:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((617:ℚ)/((617:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((610648639377 : ℚ) / 250000000000) + Work.RHContract.RegionI.logUpQ (((617:ℚ)/((617:ℚ)-1)) : ℚ) ≤ ((61105415447 : ℚ) / 25000000000) := by decide +kernel
  have hratR : ((((610648639377 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((617:ℚ)/((617:ℚ)-1)) : ℚ) : ℝ) ≤ ((((61105415447 : ℚ) / 25000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_113 : Commons.NumberTheory.Mertens.logRatioSum ((619 : ℕ) : ℝ) ≤ ((((2445833433107 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 617 < q → q < 619 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 619).mp (by decide +kernel))) hgap
  have hprev := lrU_112
  have hcast : (((619:ℕ):ℝ)/(((619:ℕ):ℝ)-1)) = (((619:ℚ)/((619:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((619:ℚ)/((619:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((619:ℚ)/((619:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((619:ℚ)/((619:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((61105415447 : ℚ) / 25000000000) + Work.RHContract.RegionI.logUpQ (((619:ℚ)/((619:ℚ)-1)) : ℚ) ≤ ((2445833433107 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((61105415447 : ℚ) / 25000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((619:ℚ)/((619:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2445833433107 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_114 : Commons.NumberTheory.Mertens.logRatioSum ((631 : ℕ) : ℝ) ≤ ((((2447419476263 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 619 < q → q < 631 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 631).mp (by decide +kernel))) hgap
  have hprev := lrU_113
  have hcast : (((631:ℕ):ℝ)/(((631:ℕ):ℝ)-1)) = (((631:ℚ)/((631:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((631:ℚ)/((631:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((631:ℚ)/((631:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((631:ℚ)/((631:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2445833433107 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((631:ℚ)/((631:ℚ)-1)) : ℚ) ≤ ((2447419476263 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2445833433107 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((631:ℚ)/((631:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2447419476263 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_115 : Commons.NumberTheory.Mertens.logRatioSum ((641 : ℕ) : ℝ) ≤ ((((244898075683 : ℚ) / 100000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 631 < q → q < 641 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 641).mp (by decide +kernel))) hgap
  have hprev := lrU_114
  have hcast : (((641:ℕ):ℝ)/(((641:ℕ):ℝ)-1)) = (((641:ℚ)/((641:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((641:ℚ)/((641:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((641:ℚ)/((641:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((641:ℚ)/((641:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2447419476263 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((641:ℚ)/((641:ℚ)-1)) : ℚ) ≤ ((244898075683 : ℚ) / 100000000000) := by decide +kernel
  have hratR : ((((2447419476263 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((641:ℚ)/((641:ℚ)-1)) : ℚ) : ℝ) ≤ ((((244898075683 : ℚ) / 100000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_116 : Commons.NumberTheory.Mertens.logRatioSum ((643 : ℕ) : ℝ) ≤ ((((1225268588689 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 641 < q → q < 643 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 643).mp (by decide +kernel))) hgap
  have hprev := lrU_115
  have hcast : (((643:ℕ):ℝ)/(((643:ℕ):ℝ)-1)) = (((643:ℚ)/((643:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((643:ℚ)/((643:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((643:ℚ)/((643:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((643:ℚ)/((643:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((244898075683 : ℚ) / 100000000000) + Work.RHContract.RegionI.logUpQ (((643:ℚ)/((643:ℚ)-1)) : ℚ) ≤ ((1225268588689 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((244898075683 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((643:ℚ)/((643:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1225268588689 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_117 : Commons.NumberTheory.Mertens.logRatioSum ((647 : ℕ) : ℝ) ≤ ((((2452083968097 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 643 < q → q < 647 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 647).mp (by decide +kernel))) hgap
  have hprev := lrU_116
  have hcast : (((647:ℕ):ℝ)/(((647:ℕ):ℝ)-1)) = (((647:ℚ)/((647:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((647:ℚ)/((647:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((647:ℚ)/((647:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((647:ℚ)/((647:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1225268588689 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((647:ℚ)/((647:ℚ)-1)) : ℚ) ≤ ((2452083968097 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((1225268588689 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((647:ℚ)/((647:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2452083968097 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_118 : Commons.NumberTheory.Mertens.logRatioSum ((653 : ℕ) : ℝ) ≤ ((((2453616535447 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 647 < q → q < 653 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 653).mp (by decide +kernel))) hgap
  have hprev := lrU_117
  have hcast : (((653:ℕ):ℝ)/(((653:ℕ):ℝ)-1)) = (((653:ℚ)/((653:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((653:ℚ)/((653:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((653:ℚ)/((653:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((653:ℚ)/((653:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2452083968097 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((653:ℚ)/((653:ℚ)-1)) : ℚ) ≤ ((2453616535447 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2452083968097 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((653:ℚ)/((653:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2453616535447 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_119 : Commons.NumberTheory.Mertens.logRatioSum ((659 : ℕ) : ℝ) ≤ ((((19641081109 : ℚ) / 8000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 653 < q → q < 659 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 659).mp (by decide +kernel))) hgap
  have hprev := lrU_118
  have hcast : (((659:ℕ):ℝ)/(((659:ℕ):ℝ)-1)) = (((659:ℚ)/((659:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((659:ℚ)/((659:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((659:ℚ)/((659:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((659:ℚ)/((659:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2453616535447 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((659:ℚ)/((659:ℚ)-1)) : ℚ) ≤ ((19641081109 : ℚ) / 8000000000) := by decide +kernel
  have hratR : ((((2453616535447 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((659:ℚ)/((659:ℚ)-1)) : ℚ) : ℝ) ≤ ((((19641081109 : ℚ) / 8000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_120 : Commons.NumberTheory.Mertens.logRatioSum ((661 : ℕ) : ℝ) ≤ ((((2456649143457 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 659 < q → q < 661 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 661).mp (by decide +kernel))) hgap
  have hprev := lrU_119
  have hcast : (((661:ℕ):ℝ)/(((661:ℕ):ℝ)-1)) = (((661:ℚ)/((661:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((661:ℚ)/((661:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((661:ℚ)/((661:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((661:ℚ)/((661:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((19641081109 : ℚ) / 8000000000) + Work.RHContract.RegionI.logUpQ (((661:ℚ)/((661:ℚ)-1)) : ℚ) ≤ ((2456649143457 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((19641081109 : ℚ) / 8000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((661:ℚ)/((661:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2456649143457 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_121 : Commons.NumberTheory.Mertens.logRatioSum ((673 : ℕ) : ℝ) ≤ ((((2458136132579 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 661 < q → q < 673 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 673).mp (by decide +kernel))) hgap
  have hprev := lrU_120
  have hcast : (((673:ℕ):ℝ)/(((673:ℕ):ℝ)-1)) = (((673:ℚ)/((673:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((673:ℚ)/((673:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((673:ℚ)/((673:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((673:ℚ)/((673:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2456649143457 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((673:ℚ)/((673:ℚ)-1)) : ℚ) ≤ ((2458136132579 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2456649143457 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((673:ℚ)/((673:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2458136132579 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_122 : Commons.NumberTheory.Mertens.logRatioSum ((677 : ℕ) : ℝ) ≤ ((((2459614329449 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 673 < q → q < 677 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 677).mp (by decide +kernel))) hgap
  have hprev := lrU_121
  have hcast : (((677:ℕ):ℝ)/(((677:ℕ):ℝ)-1)) = (((677:ℚ)/((677:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((677:ℚ)/((677:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((677:ℚ)/((677:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((677:ℚ)/((677:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2458136132579 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((677:ℚ)/((677:ℚ)-1)) : ℚ) ≤ ((2459614329449 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2458136132579 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((677:ℚ)/((677:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2459614329449 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_123 : Commons.NumberTheory.Mertens.logRatioSum ((683 : ℕ) : ℝ) ≤ ((((2461079531177 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 677 < q → q < 683 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 683).mp (by decide +kernel))) hgap
  have hprev := lrU_122
  have hcast : (((683:ℕ):ℝ)/(((683:ℕ):ℝ)-1)) = (((683:ℚ)/((683:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((683:ℚ)/((683:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((683:ℚ)/((683:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((683:ℚ)/((683:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2459614329449 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((683:ℚ)/((683:ℚ)-1)) : ℚ) ≤ ((2461079531177 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2459614329449 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((683:ℚ)/((683:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2461079531177 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_124 : Commons.NumberTheory.Mertens.logRatioSum ((691 : ℕ) : ℝ) ≤ ((((1231263878677 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 683 < q → q < 691 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 691).mp (by decide +kernel))) hgap
  have hprev := lrU_123
  have hcast : (((691:ℕ):ℝ)/(((691:ℕ):ℝ)-1)) = (((691:ℚ)/((691:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((691:ℚ)/((691:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((691:ℚ)/((691:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((691:ℚ)/((691:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2461079531177 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((691:ℚ)/((691:ℚ)-1)) : ℚ) ≤ ((1231263878677 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((2461079531177 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((691:ℚ)/((691:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1231263878677 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_125 : Commons.NumberTheory.Mertens.logRatioSum ((701 : ℕ) : ℝ) ≤ ((((1231977654673 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 691 < q → q < 701 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 701).mp (by decide +kernel))) hgap
  have hprev := lrU_124
  have hcast : (((701:ℕ):ℝ)/(((701:ℕ):ℝ)-1)) = (((701:ℚ)/((701:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((701:ℚ)/((701:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((701:ℚ)/((701:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((701:ℚ)/((701:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1231263878677 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((701:ℚ)/((701:ℚ)-1)) : ℚ) ≤ ((1231977654673 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((1231263878677 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((701:ℚ)/((701:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1231977654673 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_126 : Commons.NumberTheory.Mertens.logRatioSum ((709 : ℕ) : ℝ) ≤ ((((493073348437 : ℚ) / 200000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 701 < q → q < 709 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 709).mp (by decide +kernel))) hgap
  have hprev := lrU_125
  have hcast : (((709:ℕ):ℝ)/(((709:ℕ):ℝ)-1)) = (((709:ℚ)/((709:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((709:ℚ)/((709:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((709:ℚ)/((709:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((709:ℚ)/((709:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1231977654673 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((709:ℚ)/((709:ℚ)-1)) : ℚ) ≤ ((493073348437 : ℚ) / 200000000000) := by decide +kernel
  have hratR : ((((1231977654673 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((709:ℚ)/((709:ℚ)-1)) : ℚ) : ℝ) ≤ ((((493073348437 : ℚ) / 200000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_127 : Commons.NumberTheory.Mertens.logRatioSum ((719 : ℕ) : ℝ) ≤ ((((1233379265429 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 709 < q → q < 719 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 719).mp (by decide +kernel))) hgap
  have hprev := lrU_126
  have hcast : (((719:ℕ):ℝ)/(((719:ℕ):ℝ)-1)) = (((719:ℚ)/((719:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((719:ℚ)/((719:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((719:ℚ)/((719:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((719:ℚ)/((719:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((493073348437 : ℚ) / 200000000000) + Work.RHContract.RegionI.logUpQ (((719:ℚ)/((719:ℚ)-1)) : ℚ) ≤ ((1233379265429 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((493073348437 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((719:ℚ)/((719:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1233379265429 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_128 : Commons.NumberTheory.Mertens.logRatioSum ((727 : ℕ) : ℝ) ≤ ((((2468134993567 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 719 < q → q < 727 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 727).mp (by decide +kernel))) hgap
  have hprev := lrU_127
  have hcast : (((727:ℕ):ℝ)/(((727:ℕ):ℝ)-1)) = (((727:ℚ)/((727:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((727:ℚ)/((727:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((727:ℚ)/((727:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((727:ℚ)/((727:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1233379265429 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((727:ℚ)/((727:ℚ)-1)) : ℚ) ≤ ((2468134993567 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((1233379265429 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((727:ℚ)/((727:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2468134993567 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_129 : Commons.NumberTheory.Mertens.logRatioSum ((733 : ℕ) : ℝ) ≤ ((((2469500181493 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 727 < q → q < 733 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 733).mp (by decide +kernel))) hgap
  have hprev := lrU_128
  have hcast : (((733:ℕ):ℝ)/(((733:ℕ):ℝ)-1)) = (((733:ℚ)/((733:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((733:ℚ)/((733:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((733:ℚ)/((733:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((733:ℚ)/((733:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2468134993567 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((733:ℚ)/((733:ℚ)-1)) : ℚ) ≤ ((2469500181493 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2468134993567 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((733:ℚ)/((733:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2469500181493 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_130 : Commons.NumberTheory.Mertens.logRatioSum ((739 : ℕ) : ℝ) ≤ ((((2470854277841 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 733 < q → q < 739 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 739).mp (by decide +kernel))) hgap
  have hprev := lrU_129
  have hcast : (((739:ℕ):ℝ)/(((739:ℕ):ℝ)-1)) = (((739:ℚ)/((739:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((739:ℚ)/((739:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((739:ℚ)/((739:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((739:ℚ)/((739:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2469500181493 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((739:ℚ)/((739:ℚ)-1)) : ℚ) ≤ ((2470854277841 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2469500181493 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((739:ℚ)/((739:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2470854277841 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_131 : Commons.NumberTheory.Mertens.logRatioSum ((743 : ℕ) : ℝ) ≤ ((((77256283731 : ℚ) / 31250000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 739 < q → q < 743 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 743).mp (by decide +kernel))) hgap
  have hprev := lrU_130
  have hcast : (((743:ℕ):ℝ)/(((743:ℕ):ℝ)-1)) = (((743:ℚ)/((743:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((743:ℚ)/((743:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((743:ℚ)/((743:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((743:ℚ)/((743:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2470854277841 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((743:ℚ)/((743:ℚ)-1)) : ℚ) ≤ ((77256283731 : ℚ) / 31250000000) := by decide +kernel
  have hratR : ((((2470854277841 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((743:ℚ)/((743:ℚ)-1)) : ℚ) : ℝ) ≤ ((((77256283731 : ℚ) / 31250000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_132 : Commons.NumberTheory.Mertens.logRatioSum ((751 : ℕ) : ℝ) ≤ ((((1236766762313 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 743 < q → q < 751 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 751).mp (by decide +kernel))) hgap
  have hprev := lrU_131
  have hcast : (((751:ℕ):ℝ)/(((751:ℕ):ℝ)-1)) = (((751:ℚ)/((751:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((751:ℚ)/((751:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((751:ℚ)/((751:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((751:ℚ)/((751:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((77256283731 : ℚ) / 31250000000) + Work.RHContract.RegionI.logUpQ (((751:ℚ)/((751:ℚ)-1)) : ℚ) ≤ ((1236766762313 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((77256283731 : ℚ) / 31250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((751:ℚ)/((751:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1236766762313 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_133 : Commons.NumberTheory.Mertens.logRatioSum ((757 : ℕ) : ℝ) ≤ ((((618713850471 : ℚ) / 250000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 751 < q → q < 757 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 757).mp (by decide +kernel))) hgap
  have hprev := lrU_132
  have hcast : (((757:ℕ):ℝ)/(((757:ℕ):ℝ)-1)) = (((757:ℚ)/((757:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((757:ℚ)/((757:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((757:ℚ)/((757:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((757:ℚ)/((757:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1236766762313 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((757:ℚ)/((757:ℚ)-1)) : ℚ) ≤ ((618713850471 : ℚ) / 250000000000) := by decide +kernel
  have hratR : ((((1236766762313 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((757:ℚ)/((757:ℚ)-1)) : ℚ) : ℝ) ≤ ((((618713850471 : ℚ) / 250000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_134 : Commons.NumberTheory.Mertens.logRatioSum ((761 : ℕ) : ℝ) ≤ ((((1238085163233 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 757 < q → q < 761 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 761).mp (by decide +kernel))) hgap
  have hprev := lrU_133
  have hcast : (((761:ℕ):ℝ)/(((761:ℕ):ℝ)-1)) = (((761:ℚ)/((761:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((761:ℚ)/((761:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((761:ℚ)/((761:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((761:ℚ)/((761:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((618713850471 : ℚ) / 250000000000) + Work.RHContract.RegionI.logUpQ (((761:ℚ)/((761:ℚ)-1)) : ℚ) ≤ ((1238085163233 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((618713850471 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((761:ℚ)/((761:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1238085163233 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_135 : Commons.NumberTheory.Mertens.logRatioSum ((769 : ℕ) : ℝ) ≤ ((((309683945353 : ℚ) / 125000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 761 < q → q < 769 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 769).mp (by decide +kernel))) hgap
  have hprev := lrU_134
  have hcast : (((769:ℕ):ℝ)/(((769:ℕ):ℝ)-1)) = (((769:ℚ)/((769:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((769:ℚ)/((769:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((769:ℚ)/((769:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((769:ℚ)/((769:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1238085163233 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((769:ℚ)/((769:ℚ)-1)) : ℚ) ≤ ((309683945353 : ℚ) / 125000000000) := by decide +kernel
  have hratR : ((((1238085163233 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((769:ℚ)/((769:ℚ)-1)) : ℚ) : ℝ) ≤ ((((309683945353 : ℚ) / 125000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_136 : Commons.NumberTheory.Mertens.logRatioSum ((773 : ℕ) : ℝ) ≤ ((((2478766061387 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 769 < q → q < 773 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 773).mp (by decide +kernel))) hgap
  have hprev := lrU_135
  have hcast : (((773:ℕ):ℝ)/(((773:ℕ):ℝ)-1)) = (((773:ℚ)/((773:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((773:ℚ)/((773:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((773:ℚ)/((773:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((773:ℚ)/((773:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((309683945353 : ℚ) / 125000000000) + Work.RHContract.RegionI.logUpQ (((773:ℚ)/((773:ℚ)-1)) : ℚ) ≤ ((2478766061387 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((309683945353 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((773:ℚ)/((773:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2478766061387 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_137 : Commons.NumberTheory.Mertens.logRatioSum ((787 : ℕ) : ℝ) ≤ ((((38750586209 : ℚ) / 15625000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 773 < q → q < 787 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 787).mp (by decide +kernel))) hgap
  have hprev := lrU_136
  have hcast : (((787:ℕ):ℝ)/(((787:ℕ):ℝ)-1)) = (((787:ℚ)/((787:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((787:ℚ)/((787:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((787:ℚ)/((787:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((787:ℚ)/((787:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2478766061387 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((787:ℚ)/((787:ℚ)-1)) : ℚ) ≤ ((38750586209 : ℚ) / 15625000000) := by decide +kernel
  have hratR : ((((2478766061387 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((787:ℚ)/((787:ℚ)-1)) : ℚ) : ℝ) ≤ ((((38750586209 : ℚ) / 15625000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_138 : Commons.NumberTheory.Mertens.logRatioSum ((797 : ℕ) : ℝ) ≤ ((((1240646505161 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 787 < q → q < 797 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 797).mp (by decide +kernel))) hgap
  have hprev := lrU_137
  have hcast : (((797:ℕ):ℝ)/(((797:ℕ):ℝ)-1)) = (((797:ℚ)/((797:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((797:ℚ)/((797:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((797:ℚ)/((797:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((797:ℚ)/((797:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((38750586209 : ℚ) / 15625000000) + Work.RHContract.RegionI.logUpQ (((797:ℚ)/((797:ℚ)-1)) : ℚ) ≤ ((1240646505161 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((38750586209 : ℚ) / 15625000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((797:ℚ)/((797:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1240646505161 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_139 : Commons.NumberTheory.Mertens.logRatioSum ((809 : ℕ) : ℝ) ≤ ((((124126493443 : ℚ) / 50000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 797 < q → q < 809 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 809).mp (by decide +kernel))) hgap
  have hprev := lrU_138
  have hcast : (((809:ℕ):ℝ)/(((809:ℕ):ℝ)-1)) = (((809:ℚ)/((809:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((809:ℚ)/((809:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((809:ℚ)/((809:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((809:ℚ)/((809:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1240646505161 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((809:ℚ)/((809:ℚ)-1)) : ℚ) ≤ ((124126493443 : ℚ) / 50000000000) := by decide +kernel
  have hratR : ((((1240646505161 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((809:ℚ)/((809:ℚ)-1)) : ℚ) : ℝ) ≤ ((((124126493443 : ℚ) / 50000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_140 : Commons.NumberTheory.Mertens.logRatioSum ((811 : ℕ) : ℝ) ≤ ((((2483763675309 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 809 < q → q < 811 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 811).mp (by decide +kernel))) hgap
  have hprev := lrU_139
  have hcast : (((811:ℕ):ℝ)/(((811:ℕ):ℝ)-1)) = (((811:ℚ)/((811:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((811:ℚ)/((811:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((811:ℚ)/((811:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((811:ℚ)/((811:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((124126493443 : ℚ) / 50000000000) + Work.RHContract.RegionI.logUpQ (((811:ℚ)/((811:ℚ)-1)) : ℚ) ≤ ((2483763675309 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((124126493443 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((811:ℚ)/((811:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2483763675309 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_141 : Commons.NumberTheory.Mertens.logRatioSum ((821 : ℕ) : ℝ) ≤ ((((310622805563 : ℚ) / 125000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 811 < q → q < 821 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 821).mp (by decide +kernel))) hgap
  have hprev := lrU_140
  have hcast : (((821:ℕ):ℝ)/(((821:ℕ):ℝ)-1)) = (((821:ℚ)/((821:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((821:ℚ)/((821:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((821:ℚ)/((821:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((821:ℚ)/((821:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2483763675309 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((821:ℚ)/((821:ℚ)-1)) : ℚ) ≤ ((310622805563 : ℚ) / 125000000000) := by decide +kernel
  have hratR : ((((2483763675309 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((821:ℚ)/((821:ℚ)-1)) : ℚ) : ℝ) ≤ ((((310622805563 : ℚ) / 125000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_142 : Commons.NumberTheory.Mertens.logRatioSum ((823 : ℕ) : ℝ) ≤ ((((19889586001 : ℚ) / 8000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 821 < q → q < 823 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 823).mp (by decide +kernel))) hgap
  have hprev := lrU_141
  have hcast : (((823:ℕ):ℝ)/(((823:ℕ):ℝ)-1)) = (((823:ℚ)/((823:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((823:ℚ)/((823:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((823:ℚ)/((823:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((823:ℚ)/((823:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((310622805563 : ℚ) / 125000000000) + Work.RHContract.RegionI.logUpQ (((823:ℚ)/((823:ℚ)-1)) : ℚ) ≤ ((19889586001 : ℚ) / 8000000000) := by decide +kernel
  have hratR : ((((310622805563 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((823:ℚ)/((823:ℚ)-1)) : ℚ) : ℝ) ≤ ((((19889586001 : ℚ) / 8000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_143 : Commons.NumberTheory.Mertens.logRatioSum ((827 : ℕ) : ℝ) ≤ ((((621852042907 : ℚ) / 250000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 823 < q → q < 827 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 827).mp (by decide +kernel))) hgap
  have hprev := lrU_142
  have hcast : (((827:ℕ):ℝ)/(((827:ℕ):ℝ)-1)) = (((827:ℚ)/((827:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((827:ℚ)/((827:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((827:ℚ)/((827:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((827:ℚ)/((827:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((19889586001 : ℚ) / 8000000000) + Work.RHContract.RegionI.logUpQ (((827:ℚ)/((827:ℚ)-1)) : ℚ) ≤ ((621852042907 : ℚ) / 250000000000) := by decide +kernel
  have hratR : ((((19889586001 : ℚ) / 8000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((827:ℚ)/((827:ℚ)-1)) : ℚ) : ℝ) ≤ ((((621852042907 : ℚ) / 250000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_144 : Commons.NumberTheory.Mertens.logRatioSum ((829 : ℕ) : ℝ) ≤ ((((2488615172379 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 827 < q → q < 829 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 829).mp (by decide +kernel))) hgap
  have hprev := lrU_143
  have hcast : (((829:ℕ):ℝ)/(((829:ℕ):ℝ)-1)) = (((829:ℚ)/((829:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((829:ℚ)/((829:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((829:ℚ)/((829:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((829:ℚ)/((829:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((621852042907 : ℚ) / 250000000000) + Work.RHContract.RegionI.logUpQ (((829:ℚ)/((829:ℚ)-1)) : ℚ) ≤ ((2488615172379 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((621852042907 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((829:ℚ)/((829:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2488615172379 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_145 : Commons.NumberTheory.Mertens.logRatioSum ((839 : ℕ) : ℝ) ≤ ((((497961555673 : ℚ) / 200000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 829 < q → q < 839 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 839).mp (by decide +kernel))) hgap
  have hprev := lrU_144
  have hcast : (((839:ℕ):ℝ)/(((839:ℕ):ℝ)-1)) = (((839:ℚ)/((839:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((839:ℚ)/((839:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((839:ℚ)/((839:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((839:ℚ)/((839:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2488615172379 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((839:ℚ)/((839:ℚ)-1)) : ℚ) ≤ ((497961555673 : ℚ) / 200000000000) := by decide +kernel
  have hratR : ((((2488615172379 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((839:ℚ)/((839:ℚ)-1)) : ℚ) : ℝ) ≤ ((((497961555673 : ℚ) / 200000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_146 : Commons.NumberTheory.Mertens.logRatioSum ((853 : ℕ) : ℝ) ≤ ((((622745199757 : ℚ) / 250000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 839 < q → q < 853 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 853).mp (by decide +kernel))) hgap
  have hprev := lrU_145
  have hcast : (((853:ℕ):ℝ)/(((853:ℕ):ℝ)-1)) = (((853:ℚ)/((853:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((853:ℚ)/((853:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((853:ℚ)/((853:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((853:ℚ)/((853:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((497961555673 : ℚ) / 200000000000) + Work.RHContract.RegionI.logUpQ (((853:ℚ)/((853:ℚ)-1)) : ℚ) ≤ ((622745199757 : ℚ) / 250000000000) := by decide +kernel
  have hratR : ((((497961555673 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((853:ℚ)/((853:ℚ)-1)) : ℚ) : ℝ) ≤ ((((622745199757 : ℚ) / 250000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_147 : Commons.NumberTheory.Mertens.logRatioSum ((857 : ℕ) : ℝ) ≤ ((((498429668297 : ℚ) / 200000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 853 < q → q < 857 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 857).mp (by decide +kernel))) hgap
  have hprev := lrU_146
  have hcast : (((857:ℕ):ℝ)/(((857:ℕ):ℝ)-1)) = (((857:ℚ)/((857:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((857:ℚ)/((857:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((857:ℚ)/((857:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((857:ℚ)/((857:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((622745199757 : ℚ) / 250000000000) + Work.RHContract.RegionI.logUpQ (((857:ℚ)/((857:ℚ)-1)) : ℚ) ≤ ((498429668297 : ℚ) / 200000000000) := by decide +kernel
  have hratR : ((((622745199757 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((857:ℚ)/((857:ℚ)-1)) : ℚ) : ℝ) ≤ ((((498429668297 : ℚ) / 200000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_148 : Commons.NumberTheory.Mertens.logRatioSum ((859 : ℕ) : ℝ) ≤ ((((1246656581991 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 857 < q → q < 859 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 859).mp (by decide +kernel))) hgap
  have hprev := lrU_147
  have hcast : (((859:ℕ):ℝ)/(((859:ℕ):ℝ)-1)) = (((859:ℚ)/((859:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((859:ℚ)/((859:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((859:ℚ)/((859:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((859:ℚ)/((859:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((498429668297 : ℚ) / 200000000000) + Work.RHContract.RegionI.logUpQ (((859:ℚ)/((859:ℚ)-1)) : ℚ) ≤ ((1246656581991 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((498429668297 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((859:ℚ)/((859:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1246656581991 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_149 : Commons.NumberTheory.Mertens.logRatioSum ((863 : ℕ) : ℝ) ≤ ((((1247236292201 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 859 < q → q < 863 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 863).mp (by decide +kernel))) hgap
  have hprev := lrU_148
  have hcast : (((863:ℕ):ℝ)/(((863:ℕ):ℝ)-1)) = (((863:ℚ)/((863:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((863:ℚ)/((863:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((863:ℚ)/((863:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((863:ℚ)/((863:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1246656581991 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((863:ℚ)/((863:ℚ)-1)) : ℚ) ≤ ((1247236292201 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((1246656581991 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((863:ℚ)/((863:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1247236292201 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_150 : Commons.NumberTheory.Mertens.logRatioSum ((877 : ℕ) : ℝ) ≤ ((((1247806742919 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 863 < q → q < 877 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 877).mp (by decide +kernel))) hgap
  have hprev := lrU_149
  have hcast : (((877:ℕ):ℝ)/(((877:ℕ):ℝ)-1)) = (((877:ℚ)/((877:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((877:ℚ)/((877:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((877:ℚ)/((877:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((877:ℚ)/((877:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1247236292201 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((877:ℚ)/((877:ℚ)-1)) : ℚ) ≤ ((1247806742919 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((1247236292201 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((877:ℚ)/((877:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1247806742919 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_151 : Commons.NumberTheory.Mertens.logRatioSum ((881 : ℕ) : ℝ) ≤ ((((1248374602151 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 877 < q → q < 881 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 881).mp (by decide +kernel))) hgap
  have hprev := lrU_150
  have hcast : (((881:ℕ):ℝ)/(((881:ℕ):ℝ)-1)) = (((881:ℚ)/((881:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((881:ℚ)/((881:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((881:ℚ)/((881:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((881:ℚ)/((881:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1247806742919 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((881:ℚ)/((881:ℚ)-1)) : ℚ) ≤ ((1248374602151 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((1247806742919 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((881:ℚ)/((881:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1248374602151 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_152 : Commons.NumberTheory.Mertens.logRatioSum ((883 : ℕ) : ℝ) ≤ ((((24978823489 : ℚ) / 10000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 881 < q → q < 883 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 883).mp (by decide +kernel))) hgap
  have hprev := lrU_151
  have hcast : (((883:ℕ):ℝ)/(((883:ℕ):ℝ)-1)) = (((883:ℚ)/((883:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((883:ℚ)/((883:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((883:ℚ)/((883:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((883:ℚ)/((883:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1248374602151 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((883:ℚ)/((883:ℚ)-1)) : ℚ) ≤ ((24978823489 : ℚ) / 10000000000) := by decide +kernel
  have hratR : ((((1248374602151 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((883:ℚ)/((883:ℚ)-1)) : ℚ) : ℝ) ≤ ((((24978823489 : ℚ) / 10000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_153 : Commons.NumberTheory.Mertens.logRatioSum ((887 : ℕ) : ℝ) ≤ ((((499802076121 : ℚ) / 200000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 883 < q → q < 887 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 887).mp (by decide +kernel))) hgap
  have hprev := lrU_152
  have hcast : (((887:ℕ):ℝ)/(((887:ℕ):ℝ)-1)) = (((887:ℚ)/((887:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((887:ℚ)/((887:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((887:ℚ)/((887:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((887:ℚ)/((887:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((24978823489 : ℚ) / 10000000000) + Work.RHContract.RegionI.logUpQ (((887:ℚ)/((887:ℚ)-1)) : ℚ) ≤ ((499802076121 : ℚ) / 200000000000) := by decide +kernel
  have hratR : ((((24978823489 : ℚ) / 10000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((887:ℚ)/((887:ℚ)-1)) : ℚ) : ℝ) ≤ ((((499802076121 : ℚ) / 200000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_154 : Commons.NumberTheory.Mertens.logRatioSum ((907 : ℕ) : ℝ) ≤ ((((1250056762339 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 887 < q → q < 907 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 907).mp (by decide +kernel))) hgap
  have hprev := lrU_153
  have hcast : (((907:ℕ):ℝ)/(((907:ℕ):ℝ)-1)) = (((907:ℚ)/((907:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((907:ℚ)/((907:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((907:ℚ)/((907:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((907:ℚ)/((907:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((499802076121 : ℚ) / 200000000000) + Work.RHContract.RegionI.logUpQ (((907:ℚ)/((907:ℚ)-1)) : ℚ) ≤ ((1250056762339 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((499802076121 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((907:ℚ)/((907:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1250056762339 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_155 : Commons.NumberTheory.Mertens.logRatioSum ((911 : ℕ) : ℝ) ≤ ((((625302955607 : ℚ) / 250000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 907 < q → q < 911 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 911).mp (by decide +kernel))) hgap
  have hprev := lrU_154
  have hcast : (((911:ℕ):ℝ)/(((911:ℕ):ℝ)-1)) = (((911:ℚ)/((911:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((911:ℚ)/((911:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((911:ℚ)/((911:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((911:ℚ)/((911:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1250056762339 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((911:ℚ)/((911:ℚ)-1)) : ℚ) ≤ ((625302955607 : ℚ) / 250000000000) := by decide +kernel
  have hratR : ((((1250056762339 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((911:ℚ)/((911:ℚ)-1)) : ℚ) : ℝ) ≤ ((((625302955607 : ℚ) / 250000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_156 : Commons.NumberTheory.Mertens.logRatioSum ((919 : ℕ) : ℝ) ≤ ((((625575138541 : ℚ) / 250000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 911 < q → q < 919 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 919).mp (by decide +kernel))) hgap
  have hprev := lrU_155
  have hcast : (((919:ℕ):ℝ)/(((919:ℕ):ℝ)-1)) = (((919:ℚ)/((919:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((919:ℚ)/((919:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((919:ℚ)/((919:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((919:ℚ)/((919:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((625302955607 : ℚ) / 250000000000) + Work.RHContract.RegionI.logUpQ (((919:ℚ)/((919:ℚ)-1)) : ℚ) ≤ ((625575138541 : ℚ) / 250000000000) := by decide +kernel
  have hratR : ((((625302955607 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((919:ℚ)/((919:ℚ)-1)) : ℚ) : ℝ) ≤ ((((625575138541 : ℚ) / 250000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_157 : Commons.NumberTheory.Mertens.logRatioSum ((929 : ℕ) : ℝ) ≤ ((((19557637189 : ℚ) / 7812500000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 919 < q → q < 929 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 929).mp (by decide +kernel))) hgap
  have hprev := lrU_156
  have hcast : (((929:ℕ):ℝ)/(((929:ℕ):ℝ)-1)) = (((929:ℚ)/((929:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((929:ℚ)/((929:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((929:ℚ)/((929:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((929:ℚ)/((929:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((625575138541 : ℚ) / 250000000000) + Work.RHContract.RegionI.logUpQ (((929:ℚ)/((929:ℚ)-1)) : ℚ) ≤ ((19557637189 : ℚ) / 7812500000) := by decide +kernel
  have hratR : ((((625575138541 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((929:ℚ)/((929:ℚ)-1)) : ℚ) : ℝ) ≤ ((((19557637189 : ℚ) / 7812500000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_158 : Commons.NumberTheory.Mertens.logRatioSum ((937 : ℕ) : ℝ) ≤ ((((2504445365953 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 929 < q → q < 937 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 937).mp (by decide +kernel))) hgap
  have hprev := lrU_157
  have hcast : (((937:ℕ):ℝ)/(((937:ℕ):ℝ)-1)) = (((937:ℚ)/((937:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((937:ℚ)/((937:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((937:ℚ)/((937:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((937:ℚ)/((937:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((19557637189 : ℚ) / 7812500000) + Work.RHContract.RegionI.logUpQ (((937:ℚ)/((937:ℚ)-1)) : ℚ) ≤ ((2504445365953 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((19557637189 : ℚ) / 7812500000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((937:ℚ)/((937:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2504445365953 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_159 : Commons.NumberTheory.Mertens.logRatioSum ((941 : ℕ) : ℝ) ≤ ((((100220345211 : ℚ) / 40000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 937 < q → q < 941 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 941).mp (by decide +kernel))) hgap
  have hprev := lrU_158
  have hcast : (((941:ℕ):ℝ)/(((941:ℕ):ℝ)-1)) = (((941:ℚ)/((941:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((941:ℚ)/((941:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((941:ℚ)/((941:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((941:ℚ)/((941:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2504445365953 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((941:ℚ)/((941:ℚ)-1)) : ℚ) ≤ ((100220345211 : ℚ) / 40000000000) := by decide +kernel
  have hratR : ((((2504445365953 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((941:ℚ)/((941:ℚ)-1)) : ℚ) : ℝ) ≤ ((((100220345211 : ℚ) / 40000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_160 : Commons.NumberTheory.Mertens.logRatioSum ((947 : ℕ) : ℝ) ≤ ((((250656515441 : ℚ) / 100000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 941 < q → q < 947 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 947).mp (by decide +kernel))) hgap
  have hprev := lrU_159
  have hcast : (((947:ℕ):ℝ)/(((947:ℕ):ℝ)-1)) = (((947:ℚ)/((947:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((947:ℚ)/((947:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((947:ℚ)/((947:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((947:ℚ)/((947:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((100220345211 : ℚ) / 40000000000) + Work.RHContract.RegionI.logUpQ (((947:ℚ)/((947:ℚ)-1)) : ℚ) ≤ ((250656515441 : ℚ) / 100000000000) := by decide +kernel
  have hratR : ((((100220345211 : ℚ) / 40000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((947:ℚ)/((947:ℚ)-1)) : ℚ) : ℝ) ≤ ((((250656515441 : ℚ) / 100000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_161 : Commons.NumberTheory.Mertens.logRatioSum ((953 : ℕ) : ℝ) ≤ ((((2507615023273 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 947 < q → q < 953 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 953).mp (by decide +kernel))) hgap
  have hprev := lrU_160
  have hcast : (((953:ℕ):ℝ)/(((953:ℕ):ℝ)-1)) = (((953:ℚ)/((953:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((953:ℚ)/((953:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((953:ℚ)/((953:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((953:ℚ)/((953:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((250656515441 : ℚ) / 100000000000) + Work.RHContract.RegionI.logUpQ (((953:ℚ)/((953:ℚ)-1)) : ℚ) ≤ ((2507615023273 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((250656515441 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((953:ℚ)/((953:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2507615023273 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_162 : Commons.NumberTheory.Mertens.logRatioSum ((967 : ℕ) : ℝ) ≤ ((((1254324842257 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 953 < q → q < 967 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 967).mp (by decide +kernel))) hgap
  have hprev := lrU_161
  have hcast : (((967:ℕ):ℝ)/(((967:ℕ):ℝ)-1)) = (((967:ℚ)/((967:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((967:ℚ)/((967:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((967:ℚ)/((967:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((967:ℚ)/((967:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2507615023273 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((967:ℚ)/((967:ℚ)-1)) : ℚ) ≤ ((1254324842257 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((2507615023273 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((967:ℚ)/((967:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1254324842257 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_163 : Commons.NumberTheory.Mertens.logRatioSum ((971 : ℕ) : ℝ) ≤ ((((627420020327 : ℚ) / 250000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 967 < q → q < 971 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 971).mp (by decide +kernel))) hgap
  have hprev := lrU_162
  have hcast : (((971:ℕ):ℝ)/(((971:ℕ):ℝ)-1)) = (((971:ℚ)/((971:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((971:ℚ)/((971:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((971:ℚ)/((971:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((971:ℚ)/((971:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1254324842257 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((971:ℚ)/((971:ℚ)-1)) : ℚ) ≤ ((627420020327 : ℚ) / 250000000000) := by decide +kernel
  have hratR : ((((1254324842257 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((971:ℚ)/((971:ℚ)-1)) : ℚ) : ℝ) ≤ ((((627420020327 : ℚ) / 250000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_164 : Commons.NumberTheory.Mertens.logRatioSum ((977 : ℕ) : ℝ) ≤ ((((1255352073469 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 971 < q → q < 977 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 977).mp (by decide +kernel))) hgap
  have hprev := lrU_163
  have hcast : (((977:ℕ):ℝ)/(((977:ℕ):ℝ)-1)) = (((977:ℚ)/((977:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((977:ℚ)/((977:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((977:ℚ)/((977:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((977:ℚ)/((977:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((627420020327 : ℚ) / 250000000000) + Work.RHContract.RegionI.logUpQ (((977:ℚ)/((977:ℚ)-1)) : ℚ) ≤ ((1255352073469 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((627420020327 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((977:ℚ)/((977:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1255352073469 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_165 : Commons.NumberTheory.Mertens.logRatioSum ((983 : ℕ) : ℝ) ≤ ((((2511721958731 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 977 < q → q < 983 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 983).mp (by decide +kernel))) hgap
  have hprev := lrU_164
  have hcast : (((983:ℕ):ℝ)/(((983:ℕ):ℝ)-1)) = (((983:ℚ)/((983:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((983:ℚ)/((983:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((983:ℚ)/((983:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((983:ℚ)/((983:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1255352073469 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((983:ℚ)/((983:ℚ)-1)) : ℚ) ≤ ((2511721958731 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((1255352073469 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((983:ℚ)/((983:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2511721958731 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_166 : Commons.NumberTheory.Mertens.logRatioSum ((991 : ℕ) : ℝ) ≤ ((((2512731549933 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 983 < q → q < 991 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 991).mp (by decide +kernel))) hgap
  have hprev := lrU_165
  have hcast : (((991:ℕ):ℝ)/(((991:ℕ):ℝ)-1)) = (((991:ℚ)/((991:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((991:ℚ)/((991:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((991:ℚ)/((991:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((991:ℚ)/((991:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2511721958731 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((991:ℚ)/((991:ℚ)-1)) : ℚ) ≤ ((2512731549933 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2511721958731 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((991:ℚ)/((991:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2512731549933 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_167 : Commons.NumberTheory.Mertens.logRatioSum ((997 : ℕ) : ℝ) ≤ ((((2513735062311 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 991 < q → q < 997 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 997).mp (by decide +kernel))) hgap
  have hprev := lrU_166
  have hcast : (((997:ℕ):ℝ)/(((997:ℕ):ℝ)-1)) = (((997:ℚ)/((997:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((997:ℚ)/((997:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((997:ℚ)/((997:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((997:ℚ)/((997:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2512731549933 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((997:ℚ)/((997:ℚ)-1)) : ℚ) ≤ ((2513735062311 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2512731549933 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((997:ℚ)/((997:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2513735062311 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_168 : Commons.NumberTheory.Mertens.logRatioSum ((1009 : ℕ) : ℝ) ≤ ((((1257363317017 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 997 < q → q < 1009 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1009).mp (by decide +kernel))) hgap
  have hprev := lrU_167
  have hcast : (((1009:ℕ):ℝ)/(((1009:ℕ):ℝ)-1)) = (((1009:ℚ)/((1009:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1009:ℚ)/((1009:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1009:ℚ)/((1009:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1009:ℚ)/((1009:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2513735062311 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((1009:ℚ)/((1009:ℚ)-1)) : ℚ) ≤ ((1257363317017 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((2513735062311 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1009:ℚ)/((1009:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1257363317017 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_169 : Commons.NumberTheory.Mertens.logRatioSum ((1013 : ℕ) : ℝ) ≤ ((((628928572109 : ℚ) / 250000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1009 < q → q < 1013 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1013).mp (by decide +kernel))) hgap
  have hprev := lrU_168
  have hcast : (((1013:ℕ):ℝ)/(((1013:ℕ):ℝ)-1)) = (((1013:ℚ)/((1013:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1013:ℚ)/((1013:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1013:ℚ)/((1013:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1013:ℚ)/((1013:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1257363317017 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((1013:ℚ)/((1013:ℚ)-1)) : ℚ) ≤ ((628928572109 : ℚ) / 250000000000) := by decide +kernel
  have hratR : ((((1257363317017 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1013:ℚ)/((1013:ℚ)-1)) : ℚ) : ℝ) ≤ ((((628928572109 : ℚ) / 250000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_170 : Commons.NumberTheory.Mertens.logRatioSum ((1019 : ℕ) : ℝ) ≤ ((((2516696124549 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1013 < q → q < 1019 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1019).mp (by decide +kernel))) hgap
  have hprev := lrU_169
  have hcast : (((1019:ℕ):ℝ)/(((1019:ℕ):ℝ)-1)) = (((1019:ℚ)/((1019:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1019:ℚ)/((1019:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1019:ℚ)/((1019:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1019:ℚ)/((1019:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((628928572109 : ℚ) / 250000000000) + Work.RHContract.RegionI.logUpQ (((1019:ℚ)/((1019:ℚ)-1)) : ℚ) ≤ ((2516696124549 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((628928572109 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1019:ℚ)/((1019:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2516696124549 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_171 : Commons.NumberTheory.Mertens.logRatioSum ((1021 : ℕ) : ℝ) ≤ ((((629419009109 : ℚ) / 250000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1019 < q → q < 1021 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1021).mp (by decide +kernel))) hgap
  have hprev := lrU_170
  have hcast : (((1021:ℕ):ℝ)/(((1021:ℕ):ℝ)-1)) = (((1021:ℚ)/((1021:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1021:ℚ)/((1021:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1021:ℚ)/((1021:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1021:ℚ)/((1021:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2516696124549 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((1021:ℚ)/((1021:ℚ)-1)) : ℚ) ≤ ((629419009109 : ℚ) / 250000000000) := by decide +kernel
  have hratR : ((((2516696124549 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1021:ℚ)/((1021:ℚ)-1)) : ℚ) : ℝ) ≤ ((((629419009109 : ℚ) / 250000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_172 : Commons.NumberTheory.Mertens.logRatioSum ((1031 : ℕ) : ℝ) ≤ ((((251864643923 : ℚ) / 100000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1021 < q → q < 1031 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1031).mp (by decide +kernel))) hgap
  have hprev := lrU_171
  have hcast : (((1031:ℕ):ℝ)/(((1031:ℕ):ℝ)-1)) = (((1031:ℚ)/((1031:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1031:ℚ)/((1031:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1031:ℚ)/((1031:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1031:ℚ)/((1031:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((629419009109 : ℚ) / 250000000000) + Work.RHContract.RegionI.logUpQ (((1031:ℚ)/((1031:ℚ)-1)) : ℚ) ≤ ((251864643923 : ℚ) / 100000000000) := by decide +kernel
  have hratR : ((((629419009109 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1031:ℚ)/((1031:ℚ)-1)) : ℚ) : ℝ) ≤ ((((251864643923 : ℚ) / 100000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_173 : Commons.NumberTheory.Mertens.logRatioSum ((1033 : ℕ) : ℝ) ≤ ((((2519614962309 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1031 < q → q < 1033 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1033).mp (by decide +kernel))) hgap
  have hprev := lrU_172
  have hcast : (((1033:ℕ):ℝ)/(((1033:ℕ):ℝ)-1)) = (((1033:ℚ)/((1033:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1033:ℚ)/((1033:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1033:ℚ)/((1033:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1033:ℚ)/((1033:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((251864643923 : ℚ) / 100000000000) + Work.RHContract.RegionI.logUpQ (((1033:ℚ)/((1033:ℚ)-1)) : ℚ) ≤ ((2519614962309 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((251864643923 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1033:ℚ)/((1033:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2519614962309 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_174 : Commons.NumberTheory.Mertens.logRatioSum ((1039 : ℕ) : ℝ) ≤ ((((2520577889683 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1033 < q → q < 1039 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1039).mp (by decide +kernel))) hgap
  have hprev := lrU_173
  have hcast : (((1039:ℕ):ℝ)/(((1039:ℕ):ℝ)-1)) = (((1039:ℚ)/((1039:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1039:ℚ)/((1039:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1039:ℚ)/((1039:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1039:ℚ)/((1039:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2519614962309 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((1039:ℚ)/((1039:ℚ)-1)) : ℚ) ≤ ((2520577889683 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2519614962309 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1039:ℚ)/((1039:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2520577889683 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_175 : Commons.NumberTheory.Mertens.logRatioSum ((1049 : ℕ) : ℝ) ≤ ((((2521531633199 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1039 < q → q < 1049 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1049).mp (by decide +kernel))) hgap
  have hprev := lrU_174
  have hcast : (((1049:ℕ):ℝ)/(((1049:ℕ):ℝ)-1)) = (((1049:ℚ)/((1049:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1049:ℚ)/((1049:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1049:ℚ)/((1049:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1049:ℚ)/((1049:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2520577889683 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((1049:ℚ)/((1049:ℚ)-1)) : ℚ) ≤ ((2521531633199 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2520577889683 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1049:ℚ)/((1049:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2521531633199 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_176 : Commons.NumberTheory.Mertens.logRatioSum ((1051 : ℕ) : ℝ) ≤ ((((100899342437 : ℚ) / 40000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1049 < q → q < 1051 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1051).mp (by decide +kernel))) hgap
  have hprev := lrU_175
  have hcast : (((1051:ℕ):ℝ)/(((1051:ℕ):ℝ)-1)) = (((1051:ℚ)/((1051:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1051:ℚ)/((1051:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1051:ℚ)/((1051:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1051:ℚ)/((1051:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2521531633199 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((1051:ℚ)/((1051:ℚ)-1)) : ℚ) ≤ ((100899342437 : ℚ) / 40000000000) := by decide +kernel
  have hratR : ((((2521531633199 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1051:ℚ)/((1051:ℚ)-1)) : ℚ) : ℝ) ≤ ((((100899342437 : ℚ) / 40000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_177 : Commons.NumberTheory.Mertens.logRatioSum ((1061 : ℕ) : ℝ) ≤ ((((2523426512433 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1051 < q → q < 1061 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1061).mp (by decide +kernel))) hgap
  have hprev := lrU_176
  have hcast : (((1061:ℕ):ℝ)/(((1061:ℕ):ℝ)-1)) = (((1061:ℚ)/((1061:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1061:ℚ)/((1061:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1061:ℚ)/((1061:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1061:ℚ)/((1061:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((100899342437 : ℚ) / 40000000000) + Work.RHContract.RegionI.logUpQ (((1061:ℚ)/((1061:ℚ)-1)) : ℚ) ≤ ((2523426512433 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((100899342437 : ℚ) / 40000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1061:ℚ)/((1061:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2523426512433 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_178 : Commons.NumberTheory.Mertens.logRatioSum ((1063 : ℕ) : ℝ) ≤ ((((1262183844487 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1061 < q → q < 1063 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1063).mp (by decide +kernel))) hgap
  have hprev := lrU_177
  have hcast : (((1063:ℕ):ℝ)/(((1063:ℕ):ℝ)-1)) = (((1063:ℚ)/((1063:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1063:ℚ)/((1063:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1063:ℚ)/((1063:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1063:ℚ)/((1063:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2523426512433 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((1063:ℚ)/((1063:ℚ)-1)) : ℚ) ≤ ((1262183844487 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((2523426512433 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1063:ℚ)/((1063:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1262183844487 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_179 : Commons.NumberTheory.Mertens.logRatioSum ((1069 : ℕ) : ℝ) ≤ ((((2525303580479 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1063 < q → q < 1069 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1069).mp (by decide +kernel))) hgap
  have hprev := lrU_178
  have hcast : (((1069:ℕ):ℝ)/(((1069:ℕ):ℝ)-1)) = (((1069:ℚ)/((1069:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1069:ℚ)/((1069:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1069:ℚ)/((1069:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1069:ℚ)/((1069:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1262183844487 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((1069:ℚ)/((1069:ℚ)-1)) : ℚ) ≤ ((2525303580479 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((1262183844487 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1069:ℚ)/((1069:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2525303580479 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_180 : Commons.NumberTheory.Mertens.logRatioSum ((1087 : ℕ) : ℝ) ≤ ((((2526223967107 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1069 < q → q < 1087 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1087).mp (by decide +kernel))) hgap
  have hprev := lrU_179
  have hcast : (((1087:ℕ):ℝ)/(((1087:ℕ):ℝ)-1)) = (((1087:ℚ)/((1087:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1087:ℚ)/((1087:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1087:ℚ)/((1087:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1087:ℚ)/((1087:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2525303580479 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((1087:ℚ)/((1087:ℚ)-1)) : ℚ) ≤ ((2526223967107 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2525303580479 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1087:ℚ)/((1087:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2526223967107 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_181 : Commons.NumberTheory.Mertens.logRatioSum ((1091 : ℕ) : ℝ) ≤ ((((2527140977717 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1087 < q → q < 1091 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1091).mp (by decide +kernel))) hgap
  have hprev := lrU_180
  have hcast : (((1091:ℕ):ℝ)/(((1091:ℕ):ℝ)-1)) = (((1091:ℚ)/((1091:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1091:ℚ)/((1091:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1091:ℚ)/((1091:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1091:ℚ)/((1091:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2526223967107 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((1091:ℚ)/((1091:ℚ)-1)) : ℚ) ≤ ((2527140977717 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2526223967107 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1091:ℚ)/((1091:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2527140977717 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_182 : Commons.NumberTheory.Mertens.logRatioSum ((1093 : ℕ) : ℝ) ≤ ((((2528056309589 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1091 < q → q < 1093 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1093).mp (by decide +kernel))) hgap
  have hprev := lrU_181
  have hcast : (((1093:ℕ):ℝ)/(((1093:ℕ):ℝ)-1)) = (((1093:ℚ)/((1093:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1093:ℚ)/((1093:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1093:ℚ)/((1093:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1093:ℚ)/((1093:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2527140977717 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((1093:ℚ)/((1093:ℚ)-1)) : ℚ) ≤ ((2528056309589 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2527140977717 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1093:ℚ)/((1093:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2528056309589 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_183 : Commons.NumberTheory.Mertens.logRatioSum ((1097 : ℕ) : ℝ) ≤ ((((2528968302357 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1093 < q → q < 1097 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1097).mp (by decide +kernel))) hgap
  have hprev := lrU_182
  have hcast : (((1097:ℕ):ℝ)/(((1097:ℕ):ℝ)-1)) = (((1097:ℚ)/((1097:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1097:ℚ)/((1097:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1097:ℚ)/((1097:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1097:ℚ)/((1097:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2528056309589 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((1097:ℚ)/((1097:ℚ)-1)) : ℚ) ≤ ((2528968302357 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2528056309589 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1097:ℚ)/((1097:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2528968302357 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_184 : Commons.NumberTheory.Mertens.logRatioSum ((1103 : ℕ) : ℝ) ≤ ((((1264937665949 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1097 < q → q < 1103 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1103).mp (by decide +kernel))) hgap
  have hprev := lrU_183
  have hcast : (((1103:ℕ):ℝ)/(((1103:ℕ):ℝ)-1)) = (((1103:ℚ)/((1103:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1103:ℚ)/((1103:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1103:ℚ)/((1103:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1103:ℚ)/((1103:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2528968302357 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((1103:ℚ)/((1103:ℚ)-1)) : ℚ) ≤ ((1264937665949 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((2528968302357 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1103:ℚ)/((1103:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1264937665949 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_185 : Commons.NumberTheory.Mertens.logRatioSum ((1109 : ℕ) : ℝ) ≤ ((((1265388725971 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1103 < q → q < 1109 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1109).mp (by decide +kernel))) hgap
  have hprev := lrU_184
  have hcast : (((1109:ℕ):ℝ)/(((1109:ℕ):ℝ)-1)) = (((1109:ℚ)/((1109:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1109:ℚ)/((1109:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1109:ℚ)/((1109:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1109:ℚ)/((1109:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1264937665949 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((1109:ℚ)/((1109:ℚ)-1)) : ℚ) ≤ ((1265388725971 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((1264937665949 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1109:ℚ)/((1109:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1265388725971 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_186 : Commons.NumberTheory.Mertens.logRatioSum ((1117 : ℕ) : ℝ) ≤ ((((253167310807 : ℚ) / 100000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1109 < q → q < 1117 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1117).mp (by decide +kernel))) hgap
  have hprev := lrU_185
  have hcast : (((1117:ℕ):ℝ)/(((1117:ℕ):ℝ)-1)) = (((1117:ℚ)/((1117:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1117:ℚ)/((1117:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1117:ℚ)/((1117:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1117:ℚ)/((1117:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1265388725971 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((1117:ℚ)/((1117:ℚ)-1)) : ℚ) ≤ ((253167310807 : ℚ) / 100000000000) := by decide +kernel
  have hratR : ((((1265388725971 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1117:ℚ)/((1117:ℚ)-1)) : ℚ) : ℝ) ≤ ((((253167310807 : ℚ) / 100000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_187 : Commons.NumberTheory.Mertens.logRatioSum ((1123 : ℕ) : ℝ) ≤ ((((1266281988363 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1117 < q → q < 1123 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1123).mp (by decide +kernel))) hgap
  have hprev := lrU_186
  have hcast : (((1123:ℕ):ℝ)/(((1123:ℕ):ℝ)-1)) = (((1123:ℚ)/((1123:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1123:ℚ)/((1123:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1123:ℚ)/((1123:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1123:ℚ)/((1123:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((253167310807 : ℚ) / 100000000000) + Work.RHContract.RegionI.logUpQ (((1123:ℚ)/((1123:ℚ)-1)) : ℚ) ≤ ((1266281988363 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((253167310807 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1123:ℚ)/((1123:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1266281988363 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_188 : Commons.NumberTheory.Mertens.logRatioSum ((1129 : ℕ) : ℝ) ≤ ((((1266725054409 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1123 < q → q < 1129 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1129).mp (by decide +kernel))) hgap
  have hprev := lrU_187
  have hcast : (((1129:ℕ):ℝ)/(((1129:ℕ):ℝ)-1)) = (((1129:ℚ)/((1129:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1129:ℚ)/((1129:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1129:ℚ)/((1129:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1129:ℚ)/((1129:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1266281988363 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((1129:ℚ)/((1129:ℚ)-1)) : ℚ) ≤ ((1266725054409 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((1266281988363 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1129:ℚ)/((1129:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1266725054409 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_189 : Commons.NumberTheory.Mertens.logRatioSum ((1151 : ℕ) : ℝ) ≤ ((((2534319296183 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1129 < q → q < 1151 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1151).mp (by decide +kernel))) hgap
  have hprev := lrU_188
  have hcast : (((1151:ℕ):ℝ)/(((1151:ℕ):ℝ)-1)) = (((1151:ℚ)/((1151:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1151:ℚ)/((1151:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1151:ℚ)/((1151:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1151:ℚ)/((1151:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1266725054409 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((1151:ℚ)/((1151:ℚ)-1)) : ℚ) ≤ ((2534319296183 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((1266725054409 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1151:ℚ)/((1151:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2534319296183 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_190 : Commons.NumberTheory.Mertens.logRatioSum ((1153 : ℕ) : ℝ) ≤ ((((2535186975197 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1151 < q → q < 1153 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1153).mp (by decide +kernel))) hgap
  have hprev := lrU_189
  have hcast : (((1153:ℕ):ℝ)/(((1153:ℕ):ℝ)-1)) = (((1153:ℚ)/((1153:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1153:ℚ)/((1153:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1153:ℚ)/((1153:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1153:ℚ)/((1153:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2534319296183 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((1153:ℚ)/((1153:ℚ)-1)) : ℚ) ≤ ((2535186975197 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2534319296183 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1153:ℚ)/((1153:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2535186975197 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_191 : Commons.NumberTheory.Mertens.logRatioSum ((1163 : ℕ) : ℝ) ≤ ((((79251474697 : ℚ) / 31250000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1153 < q → q < 1163 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1163).mp (by decide +kernel))) hgap
  have hprev := lrU_190
  have hcast : (((1163:ℕ):ℝ)/(((1163:ℕ):ℝ)-1)) = (((1163:ℚ)/((1163:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1163:ℚ)/((1163:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1163:ℚ)/((1163:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1163:ℚ)/((1163:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2535186975197 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((1163:ℚ)/((1163:ℚ)-1)) : ℚ) ≤ ((79251474697 : ℚ) / 31250000000) := by decide +kernel
  have hratR : ((((2535186975197 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1163:ℚ)/((1163:ℚ)-1)) : ℚ) : ℝ) ≤ ((((79251474697 : ℚ) / 31250000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_192 : Commons.NumberTheory.Mertens.logRatioSum ((1171 : ℕ) : ℝ) ≤ ((((253690152611 : ℚ) / 100000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1163 < q → q < 1171 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1171).mp (by decide +kernel))) hgap
  have hprev := lrU_191
  have hcast : (((1171:ℕ):ℝ)/(((1171:ℕ):ℝ)-1)) = (((1171:ℚ)/((1171:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1171:ℚ)/((1171:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1171:ℚ)/((1171:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1171:ℚ)/((1171:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((79251474697 : ℚ) / 31250000000) + Work.RHContract.RegionI.logUpQ (((1171:ℚ)/((1171:ℚ)-1)) : ℚ) ≤ ((253690152611 : ℚ) / 100000000000) := by decide +kernel
  have hratR : ((((79251474697 : ℚ) / 31250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1171:ℚ)/((1171:ℚ)-1)) : ℚ) : ℝ) ≤ ((((253690152611 : ℚ) / 100000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_193 : Commons.NumberTheory.Mertens.logRatioSum ((1181 : ℕ) : ℝ) ≤ ((((158609289053 : ℚ) / 62500000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1171 < q → q < 1181 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1181).mp (by decide +kernel))) hgap
  have hprev := lrU_192
  have hcast : (((1181:ℕ):ℝ)/(((1181:ℕ):ℝ)-1)) = (((1181:ℚ)/((1181:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1181:ℚ)/((1181:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1181:ℚ)/((1181:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1181:ℚ)/((1181:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((253690152611 : ℚ) / 100000000000) + Work.RHContract.RegionI.logUpQ (((1181:ℚ)/((1181:ℚ)-1)) : ℚ) ≤ ((158609289053 : ℚ) / 62500000000) := by decide +kernel
  have hratR : ((((253690152611 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1181:ℚ)/((1181:ℚ)-1)) : ℚ) : ℝ) ≤ ((((158609289053 : ℚ) / 62500000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_194 : Commons.NumberTheory.Mertens.logRatioSum ((1187 : ℕ) : ℝ) ≤ ((((25385914399 : ℚ) / 10000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1181 < q → q < 1187 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1187).mp (by decide +kernel))) hgap
  have hprev := lrU_193
  have hcast : (((1187:ℕ):ℝ)/(((1187:ℕ):ℝ)-1)) = (((1187:ℚ)/((1187:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1187:ℚ)/((1187:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1187:ℚ)/((1187:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1187:ℚ)/((1187:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((158609289053 : ℚ) / 62500000000) + Work.RHContract.RegionI.logUpQ (((1187:ℚ)/((1187:ℚ)-1)) : ℚ) ≤ ((25385914399 : ℚ) / 10000000000) := by decide +kernel
  have hratR : ((((158609289053 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1187:ℚ)/((1187:ℚ)-1)) : ℚ) : ℝ) ≤ ((((25385914399 : ℚ) / 10000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_195 : Commons.NumberTheory.Mertens.logRatioSum ((1193 : ℕ) : ℝ) ≤ ((((2539430014373 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1187 < q → q < 1193 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1193).mp (by decide +kernel))) hgap
  have hprev := lrU_194
  have hcast : (((1193:ℕ):ℝ)/(((1193:ℕ):ℝ)-1)) = (((1193:ℚ)/((1193:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1193:ℚ)/((1193:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1193:ℚ)/((1193:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1193:ℚ)/((1193:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((25385914399 : ℚ) / 10000000000) + Work.RHContract.RegionI.logUpQ (((1193:ℚ)/((1193:ℚ)-1)) : ℚ) ≤ ((2539430014373 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((25385914399 : ℚ) / 10000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1193:ℚ)/((1193:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2539430014373 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_196 : Commons.NumberTheory.Mertens.logRatioSum ((1201 : ℕ) : ℝ) ≤ ((((2540263000677 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1193 < q → q < 1201 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1201).mp (by decide +kernel))) hgap
  have hprev := lrU_195
  have hcast : (((1201:ℕ):ℝ)/(((1201:ℕ):ℝ)-1)) = (((1201:ℚ)/((1201:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1201:ℚ)/((1201:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1201:ℚ)/((1201:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1201:ℚ)/((1201:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2539430014373 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((1201:ℚ)/((1201:ℚ)-1)) : ℚ) ≤ ((2540263000677 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2539430014373 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1201:ℚ)/((1201:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2540263000677 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_197 : Commons.NumberTheory.Mertens.logRatioSum ((1213 : ℕ) : ℝ) ≤ ((((158817983937 : ℚ) / 62500000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1201 < q → q < 1213 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1213).mp (by decide +kernel))) hgap
  have hprev := lrU_196
  have hcast : (((1213:ℕ):ℝ)/(((1213:ℕ):ℝ)-1)) = (((1213:ℚ)/((1213:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1213:ℚ)/((1213:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1213:ℚ)/((1213:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1213:ℚ)/((1213:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2540263000677 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((1213:ℚ)/((1213:ℚ)-1)) : ℚ) ≤ ((158817983937 : ℚ) / 62500000000) := by decide +kernel
  have hratR : ((((2540263000677 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1213:ℚ)/((1213:ℚ)-1)) : ℚ) : ℝ) ≤ ((((158817983937 : ℚ) / 62500000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_198 : Commons.NumberTheory.Mertens.logRatioSum ((1217 : ℕ) : ℝ) ≤ ((((1270954886727 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1213 < q → q < 1217 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1217).mp (by decide +kernel))) hgap
  have hprev := lrU_197
  have hcast : (((1217:ℕ):ℝ)/(((1217:ℕ):ℝ)-1)) = (((1217:ℚ)/((1217:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1217:ℚ)/((1217:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1217:ℚ)/((1217:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1217:ℚ)/((1217:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((158817983937 : ℚ) / 62500000000) + Work.RHContract.RegionI.logUpQ (((1217:ℚ)/((1217:ℚ)-1)) : ℚ) ≤ ((1270954886727 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((158817983937 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1217:ℚ)/((1217:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1270954886727 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_199 : Commons.NumberTheory.Mertens.logRatioSum ((1223 : ℕ) : ℝ) ≤ ((((254272776941 : ℚ) / 100000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1217 < q → q < 1223 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1223).mp (by decide +kernel))) hgap
  have hprev := lrU_198
  have hcast : (((1223:ℕ):ℝ)/(((1223:ℕ):ℝ)-1)) = (((1223:ℚ)/((1223:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1223:ℚ)/((1223:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1223:ℚ)/((1223:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1223:ℚ)/((1223:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1270954886727 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((1223:ℚ)/((1223:ℚ)-1)) : ℚ) ≤ ((254272776941 : ℚ) / 100000000000) := by decide +kernel
  have hratR : ((((1270954886727 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1223:ℚ)/((1223:ℚ)-1)) : ℚ) : ℝ) ≤ ((((254272776941 : ℚ) / 100000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_200 : Commons.NumberTheory.Mertens.logRatioSum ((1229 : ℕ) : ℝ) ≤ ((((2543541770269 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1223 < q → q < 1229 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1229).mp (by decide +kernel))) hgap
  have hprev := lrU_199
  have hcast : (((1229:ℕ):ℝ)/(((1229:ℕ):ℝ)-1)) = (((1229:ℚ)/((1229:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1229:ℚ)/((1229:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1229:ℚ)/((1229:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1229:ℚ)/((1229:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((254272776941 : ℚ) / 100000000000) + Work.RHContract.RegionI.logUpQ (((1229:ℚ)/((1229:ℚ)-1)) : ℚ) ≤ ((2543541770269 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((254272776941 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1229:ℚ)/((1229:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2543541770269 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_201 : Commons.NumberTheory.Mertens.logRatioSum ((1231 : ℕ) : ℝ) ≤ ((((2544354448087 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1229 < q → q < 1231 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1231).mp (by decide +kernel))) hgap
  have hprev := lrU_200
  have hcast : (((1231:ℕ):ℝ)/(((1231:ℕ):ℝ)-1)) = (((1231:ℚ)/((1231:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1231:ℚ)/((1231:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1231:ℚ)/((1231:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1231:ℚ)/((1231:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2543541770269 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((1231:ℚ)/((1231:ℚ)-1)) : ℚ) ≤ ((2544354448087 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2543541770269 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1231:ℚ)/((1231:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2544354448087 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_202 : Commons.NumberTheory.Mertens.logRatioSum ((1237 : ℕ) : ℝ) ≤ ((((1272581591231 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1231 < q → q < 1237 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1237).mp (by decide +kernel))) hgap
  have hprev := lrU_201
  have hcast : (((1237:ℕ):ℝ)/(((1237:ℕ):ℝ)-1)) = (((1237:ℚ)/((1237:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1237:ℚ)/((1237:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1237:ℚ)/((1237:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1237:ℚ)/((1237:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2544354448087 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((1237:ℚ)/((1237:ℚ)-1)) : ℚ) ≤ ((1272581591231 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((2544354448087 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1237:ℚ)/((1237:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1272581591231 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_203 : Commons.NumberTheory.Mertens.logRatioSum ((1249 : ℕ) : ℝ) ≤ ((((2545964143659 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1237 < q → q < 1249 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1249).mp (by decide +kernel))) hgap
  have hprev := lrU_202
  have hcast : (((1249:ℕ):ℝ)/(((1249:ℕ):ℝ)-1)) = (((1249:ℚ)/((1249:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1249:ℚ)/((1249:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1249:ℚ)/((1249:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1249:ℚ)/((1249:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1272581591231 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((1249:ℚ)/((1249:ℚ)-1)) : ℚ) ≤ ((2545964143659 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((1272581591231 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1249:ℚ)/((1249:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2545964143659 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_204 : Commons.NumberTheory.Mertens.logRatioSum ((1259 : ℕ) : ℝ) ≤ ((((2546758740443 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1249 < q → q < 1259 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1259).mp (by decide +kernel))) hgap
  have hprev := lrU_203
  have hcast : (((1259:ℕ):ℝ)/(((1259:ℕ):ℝ)-1)) = (((1259:ℚ)/((1259:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1259:ℚ)/((1259:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1259:ℚ)/((1259:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1259:ℚ)/((1259:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2545964143659 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((1259:ℚ)/((1259:ℚ)-1)) : ℚ) ≤ ((2546758740443 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2545964143659 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1259:ℚ)/((1259:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2546758740443 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_205 : Commons.NumberTheory.Mertens.logRatioSum ((1277 : ℕ) : ℝ) ≤ ((((2547542132571 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1259 < q → q < 1277 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1277).mp (by decide +kernel))) hgap
  have hprev := lrU_204
  have hcast : (((1277:ℕ):ℝ)/(((1277:ℕ):ℝ)-1)) = (((1277:ℚ)/((1277:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1277:ℚ)/((1277:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1277:ℚ)/((1277:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1277:ℚ)/((1277:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2546758740443 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((1277:ℚ)/((1277:ℚ)-1)) : ℚ) ≤ ((2547542132571 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2546758740443 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1277:ℚ)/((1277:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2547542132571 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_206 : Commons.NumberTheory.Mertens.logRatioSum ((1279 : ℕ) : ℝ) ≤ ((((2548324299213 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1277 < q → q < 1279 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1279).mp (by decide +kernel))) hgap
  have hprev := lrU_205
  have hcast : (((1279:ℕ):ℝ)/(((1279:ℕ):ℝ)-1)) = (((1279:ℚ)/((1279:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1279:ℚ)/((1279:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1279:ℚ)/((1279:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1279:ℚ)/((1279:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2547542132571 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((1279:ℚ)/((1279:ℚ)-1)) : ℚ) ≤ ((2548324299213 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2547542132571 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1279:ℚ)/((1279:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2548324299213 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_207 : Commons.NumberTheory.Mertens.logRatioSum ((1283 : ℕ) : ℝ) ≤ ((((2549104026349 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1279 < q → q < 1283 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1283).mp (by decide +kernel))) hgap
  have hprev := lrU_206
  have hcast : (((1283:ℕ):ℝ)/(((1283:ℕ):ℝ)-1)) = (((1283:ℚ)/((1283:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1283:ℚ)/((1283:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1283:ℚ)/((1283:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1283:ℚ)/((1283:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2548324299213 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((1283:ℚ)/((1283:ℚ)-1)) : ℚ) ≤ ((2549104026349 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2548324299213 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1283:ℚ)/((1283:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2549104026349 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_208 : Commons.NumberTheory.Mertens.logRatioSum ((1289 : ℕ) : ℝ) ≤ ((((9960469229 : ℚ) / 3906250000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1283 < q → q < 1289 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1289).mp (by decide +kernel))) hgap
  have hprev := lrU_207
  have hcast : (((1289:ℕ):ℝ)/(((1289:ℕ):ℝ)-1)) = (((1289:ℚ)/((1289:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1289:ℚ)/((1289:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1289:ℚ)/((1289:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1289:ℚ)/((1289:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2549104026349 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((1289:ℚ)/((1289:ℚ)-1)) : ℚ) ≤ ((9960469229 : ℚ) / 3906250000) := by decide +kernel
  have hratR : ((((2549104026349 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1289:ℚ)/((1289:ℚ)-1)) : ℚ) : ℝ) ≤ ((((9960469229 : ℚ) / 3906250000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_209 : Commons.NumberTheory.Mertens.logRatioSum ((1291 : ℕ) : ℝ) ≤ ((((510131003223 : ℚ) / 200000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1289 < q → q < 1291 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1291).mp (by decide +kernel))) hgap
  have hprev := lrU_208
  have hcast : (((1291:ℕ):ℝ)/(((1291:ℕ):ℝ)-1)) = (((1291:ℚ)/((1291:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1291:ℚ)/((1291:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1291:ℚ)/((1291:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1291:ℚ)/((1291:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((9960469229 : ℚ) / 3906250000) + Work.RHContract.RegionI.logUpQ (((1291:ℚ)/((1291:ℚ)-1)) : ℚ) ≤ ((510131003223 : ℚ) / 200000000000) := by decide +kernel
  have hratR : ((((9960469229 : ℚ) / 3906250000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1291:ℚ)/((1291:ℚ)-1)) : ℚ) : ℝ) ≤ ((((510131003223 : ℚ) / 200000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_210 : Commons.NumberTheory.Mertens.logRatioSum ((1297 : ℕ) : ℝ) ≤ ((((7973207261 : ℚ) / 3125000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1291 < q → q < 1297 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1297).mp (by decide +kernel))) hgap
  have hprev := lrU_209
  have hcast : (((1297:ℕ):ℝ)/(((1297:ℕ):ℝ)-1)) = (((1297:ℚ)/((1297:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1297:ℚ)/((1297:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1297:ℚ)/((1297:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1297:ℚ)/((1297:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((510131003223 : ℚ) / 200000000000) + Work.RHContract.RegionI.logUpQ (((1297:ℚ)/((1297:ℚ)-1)) : ℚ) ≤ ((7973207261 : ℚ) / 3125000000) := by decide +kernel
  have hratR : ((((510131003223 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1297:ℚ)/((1297:ℚ)-1)) : ℚ) : ℝ) ≤ ((((7973207261 : ℚ) / 3125000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_211 : Commons.NumberTheory.Mertens.logRatioSum ((1301 : ℕ) : ℝ) ≤ ((((2552195258583 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1297 < q → q < 1301 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1301).mp (by decide +kernel))) hgap
  have hprev := lrU_210
  have hcast : (((1301:ℕ):ℝ)/(((1301:ℕ):ℝ)-1)) = (((1301:ℚ)/((1301:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1301:ℚ)/((1301:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1301:ℚ)/((1301:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1301:ℚ)/((1301:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((7973207261 : ℚ) / 3125000000) + Work.RHContract.RegionI.logUpQ (((1301:ℚ)/((1301:ℚ)-1)) : ℚ) ≤ ((2552195258583 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((7973207261 : ℚ) / 3125000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1301:ℚ)/((1301:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2552195258583 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_212 : Commons.NumberTheory.Mertens.logRatioSum ((1303 : ℕ) : ℝ) ≤ ((((127648150647 : ℚ) / 50000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1301 < q → q < 1303 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1303).mp (by decide +kernel))) hgap
  have hprev := lrU_211
  have hcast : (((1303:ℕ):ℝ)/(((1303:ℕ):ℝ)-1)) = (((1303:ℚ)/((1303:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1303:ℚ)/((1303:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1303:ℚ)/((1303:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1303:ℚ)/((1303:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2552195258583 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((1303:ℚ)/((1303:ℚ)-1)) : ℚ) ≤ ((127648150647 : ℚ) / 50000000000) := by decide +kernel
  have hratR : ((((2552195258583 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1303:ℚ)/((1303:ℚ)-1)) : ℚ) : ℝ) ≤ ((((127648150647 : ℚ) / 50000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_213 : Commons.NumberTheory.Mertens.logRatioSum ((1307 : ℕ) : ℝ) ≤ ((((319216052091 : ℚ) / 125000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1303 < q → q < 1307 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1307).mp (by decide +kernel))) hgap
  have hprev := lrU_212
  have hcast : (((1307:ℕ):ℝ)/(((1307:ℕ):ℝ)-1)) = (((1307:ℚ)/((1307:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1307:ℚ)/((1307:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1307:ℚ)/((1307:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1307:ℚ)/((1307:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((127648150647 : ℚ) / 50000000000) + Work.RHContract.RegionI.logUpQ (((1307:ℚ)/((1307:ℚ)-1)) : ℚ) ≤ ((319216052091 : ℚ) / 125000000000) := by decide +kernel
  have hratR : ((((127648150647 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1307:ℚ)/((1307:ℚ)-1)) : ℚ) : ℝ) ≤ ((((319216052091 : ℚ) / 125000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_214 : Commons.NumberTheory.Mertens.logRatioSum ((1319 : ℕ) : ℝ) ≤ ((((2554486854383 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1307 < q → q < 1319 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1319).mp (by decide +kernel))) hgap
  have hprev := lrU_213
  have hcast : (((1319:ℕ):ℝ)/(((1319:ℕ):ℝ)-1)) = (((1319:ℚ)/((1319:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1319:ℚ)/((1319:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1319:ℚ)/((1319:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1319:ℚ)/((1319:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((319216052091 : ℚ) / 125000000000) + Work.RHContract.RegionI.logUpQ (((1319:ℚ)/((1319:ℚ)-1)) : ℚ) ≤ ((2554486854383 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((319216052091 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1319:ℚ)/((1319:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2554486854383 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_215 : Commons.NumberTheory.Mertens.logRatioSum ((1321 : ℕ) : ℝ) ≤ ((((102209765733 : ℚ) / 40000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1319 < q → q < 1321 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1321).mp (by decide +kernel))) hgap
  have hprev := lrU_214
  have hcast : (((1321:ℕ):ℝ)/(((1321:ℕ):ℝ)-1)) = (((1321:ℚ)/((1321:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1321:ℚ)/((1321:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1321:ℚ)/((1321:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1321:ℚ)/((1321:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2554486854383 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((1321:ℚ)/((1321:ℚ)-1)) : ℚ) ≤ ((102209765733 : ℚ) / 40000000000) := by decide +kernel
  have hratR : ((((2554486854383 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1321:ℚ)/((1321:ℚ)-1)) : ℚ) : ℝ) ≤ ((((102209765733 : ℚ) / 40000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_216 : Commons.NumberTheory.Mertens.logRatioSum ((1327 : ℕ) : ℝ) ≤ ((((19968734429 : ℚ) / 7812500000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1321 < q → q < 1327 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1327).mp (by decide +kernel))) hgap
  have hprev := lrU_215
  have hcast : (((1327:ℕ):ℝ)/(((1327:ℕ):ℝ)-1)) = (((1327:ℚ)/((1327:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1327:ℚ)/((1327:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1327:ℚ)/((1327:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1327:ℚ)/((1327:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((102209765733 : ℚ) / 40000000000) + Work.RHContract.RegionI.logUpQ (((1327:ℚ)/((1327:ℚ)-1)) : ℚ) ≤ ((19968734429 : ℚ) / 7812500000) := by decide +kernel
  have hratR : ((((102209765733 : ℚ) / 40000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1327:ℚ)/((1327:ℚ)-1)) : ℚ) : ℝ) ≤ ((((19968734429 : ℚ) / 7812500000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_217 : Commons.NumberTheory.Mertens.logRatioSum ((1361 : ℕ) : ℝ) ≤ ((((1278366515417 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1327 < q → q < 1361 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1361).mp (by decide +kernel))) hgap
  have hprev := lrU_216
  have hcast : (((1361:ℕ):ℝ)/(((1361:ℕ):ℝ)-1)) = (((1361:ℚ)/((1361:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1361:ℚ)/((1361:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1361:ℚ)/((1361:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1361:ℚ)/((1361:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((19968734429 : ℚ) / 7812500000) + Work.RHContract.RegionI.logUpQ (((1361:ℚ)/((1361:ℚ)-1)) : ℚ) ≤ ((1278366515417 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((19968734429 : ℚ) / 7812500000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1361:ℚ)/((1361:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1278366515417 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_218 : Commons.NumberTheory.Mertens.logRatioSum ((1367 : ℕ) : ℝ) ≤ ((((639366206857 : ℚ) / 250000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1361 < q → q < 1367 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1367).mp (by decide +kernel))) hgap
  have hprev := lrU_217
  have hcast : (((1367:ℕ):ℝ)/(((1367:ℕ):ℝ)-1)) = (((1367:ℚ)/((1367:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1367:ℚ)/((1367:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1367:ℚ)/((1367:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1367:ℚ)/((1367:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1278366515417 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((1367:ℚ)/((1367:ℚ)-1)) : ℚ) ≤ ((639366206857 : ℚ) / 250000000000) := by decide +kernel
  have hratR : ((((1278366515417 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1367:ℚ)/((1367:ℚ)-1)) : ℚ) : ℝ) ≤ ((((639366206857 : ℚ) / 250000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_219 : Commons.NumberTheory.Mertens.logRatioSum ((1373 : ℕ) : ℝ) ≤ ((((2558193424911 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1367 < q → q < 1373 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1373).mp (by decide +kernel))) hgap
  have hprev := lrU_218
  have hcast : (((1373:ℕ):ℝ)/(((1373:ℕ):ℝ)-1)) = (((1373:ℚ)/((1373:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1373:ℚ)/((1373:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1373:ℚ)/((1373:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1373:ℚ)/((1373:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((639366206857 : ℚ) / 250000000000) + Work.RHContract.RegionI.logUpQ (((1373:ℚ)/((1373:ℚ)-1)) : ℚ) ≤ ((2558193424911 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((639366206857 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1373:ℚ)/((1373:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2558193424911 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_220 : Commons.NumberTheory.Mertens.logRatioSum ((1381 : ℕ) : ℝ) ≤ ((((255891780017 : ℚ) / 100000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1373 < q → q < 1381 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1381).mp (by decide +kernel))) hgap
  have hprev := lrU_219
  have hcast : (((1381:ℕ):ℝ)/(((1381:ℕ):ℝ)-1)) = (((1381:ℚ)/((1381:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1381:ℚ)/((1381:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1381:ℚ)/((1381:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1381:ℚ)/((1381:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2558193424911 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((1381:ℚ)/((1381:ℚ)-1)) : ℚ) ≤ ((255891780017 : ℚ) / 100000000000) := by decide +kernel
  have hratR : ((((2558193424911 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1381:ℚ)/((1381:ℚ)-1)) : ℚ) : ℝ) ≤ ((((255891780017 : ℚ) / 100000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_221 : Commons.NumberTheory.Mertens.logRatioSum ((1399 : ℕ) : ℝ) ≤ ((((1279816426021 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1381 < q → q < 1399 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1399).mp (by decide +kernel))) hgap
  have hprev := lrU_220
  have hcast : (((1399:ℕ):ℝ)/(((1399:ℕ):ℝ)-1)) = (((1399:ℚ)/((1399:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1399:ℚ)/((1399:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1399:ℚ)/((1399:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1399:ℚ)/((1399:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((255891780017 : ℚ) / 100000000000) + Work.RHContract.RegionI.logUpQ (((1399:ℚ)/((1399:ℚ)-1)) : ℚ) ≤ ((1279816426021 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((255891780017 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1399:ℚ)/((1399:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1279816426021 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_222 : Commons.NumberTheory.Mertens.logRatioSum ((1409 : ℕ) : ℝ) ≤ ((((2560342827223 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1399 < q → q < 1409 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1409).mp (by decide +kernel))) hgap
  have hprev := lrU_221
  have hcast : (((1409:ℕ):ℝ)/(((1409:ℕ):ℝ)-1)) = (((1409:ℚ)/((1409:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1409:ℚ)/((1409:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1409:ℚ)/((1409:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1409:ℚ)/((1409:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1279816426021 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((1409:ℚ)/((1409:ℚ)-1)) : ℚ) ≤ ((2560342827223 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((1279816426021 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1409:ℚ)/((1409:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2560342827223 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_223 : Commons.NumberTheory.Mertens.logRatioSum ((1423 : ℕ) : ℝ) ≤ ((((51220916299 : ℚ) / 20000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1409 < q → q < 1423 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1423).mp (by decide +kernel))) hgap
  have hprev := lrU_222
  have hcast : (((1423:ℕ):ℝ)/(((1423:ℕ):ℝ)-1)) = (((1423:ℚ)/((1423:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1423:ℚ)/((1423:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1423:ℚ)/((1423:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1423:ℚ)/((1423:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2560342827223 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((1423:ℚ)/((1423:ℚ)-1)) : ℚ) ≤ ((51220916299 : ℚ) / 20000000000) := by decide +kernel
  have hratR : ((((2560342827223 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1423:ℚ)/((1423:ℚ)-1)) : ℚ) : ℝ) ≤ ((((51220916299 : ℚ) / 20000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_224 : Commons.NumberTheory.Mertens.logRatioSum ((1427 : ℕ) : ℝ) ≤ ((((2561746831453 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1423 < q → q < 1427 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1427).mp (by decide +kernel))) hgap
  have hprev := lrU_223
  have hcast : (((1427:ℕ):ℝ)/(((1427:ℕ):ℝ)-1)) = (((1427:ℚ)/((1427:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1427:ℚ)/((1427:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1427:ℚ)/((1427:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1427:ℚ)/((1427:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((51220916299 : ℚ) / 20000000000) + Work.RHContract.RegionI.logUpQ (((1427:ℚ)/((1427:ℚ)-1)) : ℚ) ≤ ((2561746831453 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((51220916299 : ℚ) / 20000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1427:ℚ)/((1427:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2561746831453 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_225 : Commons.NumberTheory.Mertens.logRatioSum ((1429 : ℕ) : ℝ) ≤ ((((640611716621 : ℚ) / 250000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1427 < q → q < 1429 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1429).mp (by decide +kernel))) hgap
  have hprev := lrU_224
  have hcast : (((1429:ℕ):ℝ)/(((1429:ℕ):ℝ)-1)) = (((1429:ℚ)/((1429:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1429:ℚ)/((1429:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1429:ℚ)/((1429:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1429:ℚ)/((1429:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2561746831453 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((1429:ℚ)/((1429:ℚ)-1)) : ℚ) ≤ ((640611716621 : ℚ) / 250000000000) := by decide +kernel
  have hratR : ((((2561746831453 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1429:ℚ)/((1429:ℚ)-1)) : ℚ) : ℝ) ≤ ((((640611716621 : ℚ) / 250000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_226 : Commons.NumberTheory.Mertens.logRatioSum ((1433 : ℕ) : ℝ) ≤ ((((320393118349 : ℚ) / 125000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1429 < q → q < 1433 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1433).mp (by decide +kernel))) hgap
  have hprev := lrU_225
  have hcast : (((1433:ℕ):ℝ)/(((1433:ℕ):ℝ)-1)) = (((1433:ℚ)/((1433:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1433:ℚ)/((1433:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1433:ℚ)/((1433:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1433:ℚ)/((1433:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((640611716621 : ℚ) / 250000000000) + Work.RHContract.RegionI.logUpQ (((1433:ℚ)/((1433:ℚ)-1)) : ℚ) ≤ ((320393118349 : ℚ) / 125000000000) := by decide +kernel
  have hratR : ((((640611716621 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1433:ℚ)/((1433:ℚ)-1)) : ℚ) : ℝ) ≤ ((((320393118349 : ℚ) / 125000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_227 : Commons.NumberTheory.Mertens.logRatioSum ((1439 : ℕ) : ℝ) ≤ ((((2563840115399 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1433 < q → q < 1439 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1439).mp (by decide +kernel))) hgap
  have hprev := lrU_226
  have hcast : (((1439:ℕ):ℝ)/(((1439:ℕ):ℝ)-1)) = (((1439:ℚ)/((1439:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1439:ℚ)/((1439:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1439:ℚ)/((1439:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1439:ℚ)/((1439:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((320393118349 : ℚ) / 125000000000) + Work.RHContract.RegionI.logUpQ (((1439:ℚ)/((1439:ℚ)-1)) : ℚ) ≤ ((2563840115399 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((320393118349 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1439:ℚ)/((1439:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2563840115399 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_228 : Commons.NumberTheory.Mertens.logRatioSum ((1447 : ℕ) : ℝ) ≤ ((((160283214957 : ℚ) / 62500000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1439 < q → q < 1447 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1447).mp (by decide +kernel))) hgap
  have hprev := lrU_227
  have hcast : (((1447:ℕ):ℝ)/(((1447:ℕ):ℝ)-1)) = (((1447:ℚ)/((1447:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1447:ℚ)/((1447:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1447:ℚ)/((1447:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1447:ℚ)/((1447:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2563840115399 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((1447:ℚ)/((1447:ℚ)-1)) : ℚ) ≤ ((160283214957 : ℚ) / 62500000000) := by decide +kernel
  have hratR : ((((2563840115399 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1447:ℚ)/((1447:ℚ)-1)) : ℚ) : ℝ) ≤ ((((160283214957 : ℚ) / 62500000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_229 : Commons.NumberTheory.Mertens.logRatioSum ((1451 : ℕ) : ℝ) ≤ ((((1282610428391 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1447 < q → q < 1451 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1451).mp (by decide +kernel))) hgap
  have hprev := lrU_228
  have hcast : (((1451:ℕ):ℝ)/(((1451:ℕ):ℝ)-1)) = (((1451:ℚ)/((1451:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1451:ℚ)/((1451:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1451:ℚ)/((1451:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1451:ℚ)/((1451:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((160283214957 : ℚ) / 62500000000) + Work.RHContract.RegionI.logUpQ (((1451:ℚ)/((1451:ℚ)-1)) : ℚ) ≤ ((1282610428391 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((160283214957 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1451:ℚ)/((1451:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1282610428391 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_230 : Commons.NumberTheory.Mertens.logRatioSum ((1453 : ℕ) : ℝ) ≤ ((((320738665621 : ℚ) / 125000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1451 < q → q < 1453 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1453).mp (by decide +kernel))) hgap
  have hprev := lrU_229
  have hcast : (((1453:ℕ):ℝ)/(((1453:ℕ):ℝ)-1)) = (((1453:ℚ)/((1453:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1453:ℚ)/((1453:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1453:ℚ)/((1453:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1453:ℚ)/((1453:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1282610428391 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((1453:ℚ)/((1453:ℚ)-1)) : ℚ) ≤ ((320738665621 : ℚ) / 125000000000) := by decide +kernel
  have hratR : ((((1282610428391 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1453:ℚ)/((1453:ℚ)-1)) : ℚ) : ℝ) ≤ ((((320738665621 : ℚ) / 125000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_231 : Commons.NumberTheory.Mertens.logRatioSum ((1459 : ℕ) : ℝ) ≤ ((((2566594960923 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1453 < q → q < 1459 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1459).mp (by decide +kernel))) hgap
  have hprev := lrU_230
  have hcast : (((1459:ℕ):ℝ)/(((1459:ℕ):ℝ)-1)) = (((1459:ℚ)/((1459:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1459:ℚ)/((1459:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1459:ℚ)/((1459:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1459:ℚ)/((1459:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((320738665621 : ℚ) / 125000000000) + Work.RHContract.RegionI.logUpQ (((1459:ℚ)/((1459:ℚ)-1)) : ℚ) ≤ ((2566594960923 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((320738665621 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1459:ℚ)/((1459:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2566594960923 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_232 : Commons.NumberTheory.Mertens.logRatioSum ((1471 : ℕ) : ℝ) ≤ ((((320909375219 : ℚ) / 125000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1459 < q → q < 1471 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1471).mp (by decide +kernel))) hgap
  have hprev := lrU_231
  have hcast : (((1471:ℕ):ℝ)/(((1471:ℕ):ℝ)-1)) = (((1471:ℚ)/((1471:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1471:ℚ)/((1471:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1471:ℚ)/((1471:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1471:ℚ)/((1471:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2566594960923 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((1471:ℚ)/((1471:ℚ)-1)) : ℚ) ≤ ((320909375219 : ℚ) / 125000000000) := by decide +kernel
  have hratR : ((((2566594960923 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1471:ℚ)/((1471:ℚ)-1)) : ℚ) : ℝ) ≤ ((((320909375219 : ℚ) / 125000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_233 : Commons.NumberTheory.Mertens.logRatioSum ((1481 : ℕ) : ℝ) ≤ ((((1283975224631 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1471 < q → q < 1481 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1481).mp (by decide +kernel))) hgap
  have hprev := lrU_232
  have hcast : (((1481:ℕ):ℝ)/(((1481:ℕ):ℝ)-1)) = (((1481:ℚ)/((1481:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1481:ℚ)/((1481:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1481:ℚ)/((1481:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1481:ℚ)/((1481:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((320909375219 : ℚ) / 125000000000) + Work.RHContract.RegionI.logUpQ (((1481:ℚ)/((1481:ℚ)-1)) : ℚ) ≤ ((1283975224631 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((320909375219 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1481:ℚ)/((1481:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1283975224631 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_234 : Commons.NumberTheory.Mertens.logRatioSum ((1483 : ℕ) : ℝ) ≤ ((((321078123193 : ℚ) / 125000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1481 < q → q < 1483 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1483).mp (by decide +kernel))) hgap
  have hprev := lrU_233
  have hcast : (((1483:ℕ):ℝ)/(((1483:ℕ):ℝ)-1)) = (((1483:ℚ)/((1483:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1483:ℚ)/((1483:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1483:ℚ)/((1483:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1483:ℚ)/((1483:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1283975224631 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((1483:ℚ)/((1483:ℚ)-1)) : ℚ) ≤ ((321078123193 : ℚ) / 125000000000) := by decide +kernel
  have hratR : ((((1283975224631 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1483:ℚ)/((1483:ℚ)-1)) : ℚ) : ℝ) ≤ ((((321078123193 : ℚ) / 125000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_235 : Commons.NumberTheory.Mertens.logRatioSum ((1487 : ℕ) : ℝ) ≤ ((((2569297706727 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1483 < q → q < 1487 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1487).mp (by decide +kernel))) hgap
  have hprev := lrU_234
  have hcast : (((1487:ℕ):ℝ)/(((1487:ℕ):ℝ)-1)) = (((1487:ℚ)/((1487:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1487:ℚ)/((1487:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1487:ℚ)/((1487:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1487:ℚ)/((1487:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((321078123193 : ℚ) / 125000000000) + Work.RHContract.RegionI.logUpQ (((1487:ℚ)/((1487:ℚ)-1)) : ℚ) ≤ ((2569297706727 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((321078123193 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1487:ℚ)/((1487:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2569297706727 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_236 : Commons.NumberTheory.Mertens.logRatioSum ((1489 : ℕ) : ℝ) ≤ ((((1284984762009 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1487 < q → q < 1489 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1489).mp (by decide +kernel))) hgap
  have hprev := lrU_235
  have hcast : (((1489:ℕ):ℝ)/(((1489:ℕ):ℝ)-1)) = (((1489:ℚ)/((1489:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1489:ℚ)/((1489:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1489:ℚ)/((1489:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1489:ℚ)/((1489:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2569297706727 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((1489:ℚ)/((1489:ℚ)-1)) : ℚ) ≤ ((1284984762009 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((2569297706727 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1489:ℚ)/((1489:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1284984762009 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_237 : Commons.NumberTheory.Mertens.logRatioSum ((1493 : ℕ) : ℝ) ≤ ((((1285319770397 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1489 < q → q < 1493 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1493).mp (by decide +kernel))) hgap
  have hprev := lrU_236
  have hcast : (((1493:ℕ):ℝ)/(((1493:ℕ):ℝ)-1)) = (((1493:ℚ)/((1493:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1493:ℚ)/((1493:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1493:ℚ)/((1493:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1493:ℚ)/((1493:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1284984762009 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((1493:ℚ)/((1493:ℚ)-1)) : ℚ) ≤ ((1285319770397 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((1284984762009 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1493:ℚ)/((1493:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1285319770397 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_238 : Commons.NumberTheory.Mertens.logRatioSum ((1499 : ℕ) : ℝ) ≤ ((((128565343741 : ℚ) / 50000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1493 < q → q < 1499 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1499).mp (by decide +kernel))) hgap
  have hprev := lrU_237
  have hcast : (((1499:ℕ):ℝ)/(((1499:ℕ):ℝ)-1)) = (((1499:ℚ)/((1499:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1499:ℚ)/((1499:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1499:ℚ)/((1499:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1499:ℚ)/((1499:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1285319770397 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((1499:ℚ)/((1499:ℚ)-1)) : ℚ) ≤ ((128565343741 : ℚ) / 50000000000) := by decide +kernel
  have hratR : ((((1285319770397 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1499:ℚ)/((1499:ℚ)-1)) : ℚ) : ℝ) ≤ ((((128565343741 : ℚ) / 50000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_239 : Commons.NumberTheory.Mertens.logRatioSum ((1511 : ℕ) : ℝ) ≤ ((((642992226821 : ℚ) / 250000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1499 < q → q < 1511 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1511).mp (by decide +kernel))) hgap
  have hprev := lrU_238
  have hcast : (((1511:ℕ):ℝ)/(((1511:ℕ):ℝ)-1)) = (((1511:ℚ)/((1511:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1511:ℚ)/((1511:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1511:ℚ)/((1511:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1511:ℚ)/((1511:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((128565343741 : ℚ) / 50000000000) + Work.RHContract.RegionI.logUpQ (((1511:ℚ)/((1511:ℚ)-1)) : ℚ) ≤ ((642992226821 : ℚ) / 250000000000) := by decide +kernel
  have hratR : ((((128565343741 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1511:ℚ)/((1511:ℚ)-1)) : ℚ) : ℝ) ≤ ((((642992226821 : ℚ) / 250000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_240 : Commons.NumberTheory.Mertens.logRatioSum ((1523 : ℕ) : ℝ) ≤ ((((1286312860879 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1511 < q → q < 1523 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1523).mp (by decide +kernel))) hgap
  have hprev := lrU_239
  have hcast : (((1523:ℕ):ℝ)/(((1523:ℕ):ℝ)-1)) = (((1523:ℚ)/((1523:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1523:ℚ)/((1523:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1523:ℚ)/((1523:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1523:ℚ)/((1523:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((642992226821 : ℚ) / 250000000000) + Work.RHContract.RegionI.logUpQ (((1523:ℚ)/((1523:ℚ)-1)) : ℚ) ≤ ((1286312860879 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((642992226821 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1523:ℚ)/((1523:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1286312860879 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_241 : Commons.NumberTheory.Mertens.logRatioSum ((1531 : ℕ) : ℝ) ≤ ((((257327910303 : ℚ) / 100000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1523 < q → q < 1531 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1531).mp (by decide +kernel))) hgap
  have hprev := lrU_240
  have hcast : (((1531:ℕ):ℝ)/(((1531:ℕ):ℝ)-1)) = (((1531:ℚ)/((1531:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1531:ℚ)/((1531:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1531:ℚ)/((1531:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1531:ℚ)/((1531:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1286312860879 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((1531:ℚ)/((1531:ℚ)-1)) : ℚ) ≤ ((257327910303 : ℚ) / 100000000000) := by decide +kernel
  have hratR : ((((1286312860879 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1531:ℚ)/((1531:ℚ)-1)) : ℚ) : ℝ) ≤ ((((257327910303 : ℚ) / 100000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_242 : Commons.NumberTheory.Mertens.logRatioSum ((1543 : ℕ) : ℝ) ≤ ((((257392740127 : ℚ) / 100000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1531 < q → q < 1543 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1543).mp (by decide +kernel))) hgap
  have hprev := lrU_241
  have hcast : (((1543:ℕ):ℝ)/(((1543:ℕ):ℝ)-1)) = (((1543:ℚ)/((1543:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1543:ℚ)/((1543:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1543:ℚ)/((1543:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1543:ℚ)/((1543:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((257327910303 : ℚ) / 100000000000) + Work.RHContract.RegionI.logUpQ (((1543:ℚ)/((1543:ℚ)-1)) : ℚ) ≤ ((257392740127 : ℚ) / 100000000000) := by decide +kernel
  have hratR : ((((257327910303 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1543:ℚ)/((1543:ℚ)-1)) : ℚ) : ℝ) ≤ ((((257392740127 : ℚ) / 100000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_243 : Commons.NumberTheory.Mertens.logRatioSum ((1549 : ℕ) : ℝ) ≤ ((((1287286593769 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1543 < q → q < 1549 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1549).mp (by decide +kernel))) hgap
  have hprev := lrU_242
  have hcast : (((1549:ℕ):ℝ)/(((1549:ℕ):ℝ)-1)) = (((1549:ℚ)/((1549:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1549:ℚ)/((1549:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1549:ℚ)/((1549:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1549:ℚ)/((1549:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((257392740127 : ℚ) / 100000000000) + Work.RHContract.RegionI.logUpQ (((1549:ℚ)/((1549:ℚ)-1)) : ℚ) ≤ ((1287286593769 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((257392740127 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1549:ℚ)/((1549:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1287286593769 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_244 : Commons.NumberTheory.Mertens.logRatioSum ((1553 : ℕ) : ℝ) ≤ ((((321902163743 : ℚ) / 125000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1549 < q → q < 1553 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1553).mp (by decide +kernel))) hgap
  have hprev := lrU_243
  have hcast : (((1553:ℕ):ℝ)/(((1553:ℕ):ℝ)-1)) = (((1553:ℚ)/((1553:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1553:ℚ)/((1553:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1553:ℚ)/((1553:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1553:ℚ)/((1553:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1287286593769 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((1553:ℚ)/((1553:ℚ)-1)) : ℚ) ≤ ((321902163743 : ℚ) / 125000000000) := by decide +kernel
  have hratR : ((((1287286593769 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1553:ℚ)/((1553:ℚ)-1)) : ℚ) : ℝ) ≤ ((((321902163743 : ℚ) / 125000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_245 : Commons.NumberTheory.Mertens.logRatioSum ((1559 : ℕ) : ℝ) ≤ ((((643964738143 : ℚ) / 250000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1553 < q → q < 1559 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1559).mp (by decide +kernel))) hgap
  have hprev := lrU_244
  have hcast : (((1559:ℕ):ℝ)/(((1559:ℕ):ℝ)-1)) = (((1559:ℚ)/((1559:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1559:ℚ)/((1559:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1559:ℚ)/((1559:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1559:ℚ)/((1559:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((321902163743 : ℚ) / 125000000000) + Work.RHContract.RegionI.logUpQ (((1559:ℚ)/((1559:ℚ)-1)) : ℚ) ≤ ((643964738143 : ℚ) / 250000000000) := by decide +kernel
  have hratR : ((((321902163743 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1559:ℚ)/((1559:ℚ)-1)) : ℚ) : ℝ) ≤ ((((643964738143 : ℚ) / 250000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_246 : Commons.NumberTheory.Mertens.logRatioSum ((1567 : ℕ) : ℝ) ≤ ((((1288248659189 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1559 < q → q < 1567 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1567).mp (by decide +kernel))) hgap
  have hprev := lrU_245
  have hcast : (((1567:ℕ):ℝ)/(((1567:ℕ):ℝ)-1)) = (((1567:ℚ)/((1567:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1567:ℚ)/((1567:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1567:ℚ)/((1567:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1567:ℚ)/((1567:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((643964738143 : ℚ) / 250000000000) + Work.RHContract.RegionI.logUpQ (((1567:ℚ)/((1567:ℚ)-1)) : ℚ) ≤ ((1288248659189 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((643964738143 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1567:ℚ)/((1567:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1288248659189 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_247 : Commons.NumberTheory.Mertens.logRatioSum ((1571 : ℕ) : ℝ) ≤ ((((644283514573 : ℚ) / 250000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1567 < q → q < 1571 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1571).mp (by decide +kernel))) hgap
  have hprev := lrU_246
  have hcast : (((1571:ℕ):ℝ)/(((1571:ℕ):ℝ)-1)) = (((1571:ℚ)/((1571:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1571:ℚ)/((1571:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1571:ℚ)/((1571:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1571:ℚ)/((1571:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1288248659189 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((1571:ℚ)/((1571:ℚ)-1)) : ℚ) ≤ ((644283514573 : ℚ) / 250000000000) := by decide +kernel
  have hratR : ((((1288248659189 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1571:ℚ)/((1571:ℚ)-1)) : ℚ) : ℝ) ≤ ((((644283514573 : ℚ) / 250000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_248 : Commons.NumberTheory.Mertens.logRatioSum ((1579 : ℕ) : ℝ) ≤ ((((1288883785571 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1571 < q → q < 1579 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1579).mp (by decide +kernel))) hgap
  have hprev := lrU_247
  have hcast : (((1579:ℕ):ℝ)/(((1579:ℕ):ℝ)-1)) = (((1579:ℚ)/((1579:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1579:ℚ)/((1579:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1579:ℚ)/((1579:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1579:ℚ)/((1579:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((644283514573 : ℚ) / 250000000000) + Work.RHContract.RegionI.logUpQ (((1579:ℚ)/((1579:ℚ)-1)) : ℚ) ≤ ((1288883785571 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((644283514573 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1579:ℚ)/((1579:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1288883785571 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_249 : Commons.NumberTheory.Mertens.logRatioSum ((1583 : ℕ) : ℝ) ≤ ((((322299935337 : ℚ) / 125000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1579 < q → q < 1583 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1583).mp (by decide +kernel))) hgap
  have hprev := lrU_248
  have hcast : (((1583:ℕ):ℝ)/(((1583:ℕ):ℝ)-1)) = (((1583:ℚ)/((1583:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1583:ℚ)/((1583:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1583:ℚ)/((1583:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1583:ℚ)/((1583:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1288883785571 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((1583:ℚ)/((1583:ℚ)-1)) : ℚ) ≤ ((322299935337 : ℚ) / 125000000000) := by decide +kernel
  have hratR : ((((1288883785571 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1583:ℚ)/((1583:ℚ)-1)) : ℚ) : ℝ) ≤ ((((322299935337 : ℚ) / 125000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_250 : Commons.NumberTheory.Mertens.logRatioSum ((1597 : ℕ) : ℝ) ≤ ((((1289512926451 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1583 < q → q < 1597 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1597).mp (by decide +kernel))) hgap
  have hprev := lrU_249
  have hcast : (((1597:ℕ):ℝ)/(((1597:ℕ):ℝ)-1)) = (((1597:ℚ)/((1597:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1597:ℚ)/((1597:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1597:ℚ)/((1597:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1597:ℚ)/((1597:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((322299935337 : ℚ) / 125000000000) + Work.RHContract.RegionI.logUpQ (((1597:ℚ)/((1597:ℚ)-1)) : ℚ) ≤ ((1289512926451 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((322299935337 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1597:ℚ)/((1597:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1289512926451 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_251 : Commons.NumberTheory.Mertens.logRatioSum ((1601 : ℕ) : ℝ) ≤ ((((2579650657671 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1597 < q → q < 1601 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1601).mp (by decide +kernel))) hgap
  have hprev := lrU_250
  have hcast : (((1601:ℕ):ℝ)/(((1601:ℕ):ℝ)-1)) = (((1601:ℚ)/((1601:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1601:ℚ)/((1601:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1601:ℚ)/((1601:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1601:ℚ)/((1601:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1289512926451 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((1601:ℚ)/((1601:ℚ)-1)) : ℚ) ≤ ((2579650657671 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((1289512926451 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1601:ℚ)/((1601:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2579650657671 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_252 : Commons.NumberTheory.Mertens.logRatioSum ((1607 : ℕ) : ℝ) ≤ ((((1290136564451 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1601 < q → q < 1607 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1607).mp (by decide +kernel))) hgap
  have hprev := lrU_251
  have hcast : (((1607:ℕ):ℝ)/(((1607:ℕ):ℝ)-1)) = (((1607:ℚ)/((1607:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1607:ℚ)/((1607:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1607:ℚ)/((1607:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1607:ℚ)/((1607:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2579650657671 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((1607:ℚ)/((1607:ℚ)-1)) : ℚ) ≤ ((1290136564451 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((2579650657671 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1607:ℚ)/((1607:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1290136564451 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_253 : Commons.NumberTheory.Mertens.logRatioSum ((1609 : ℕ) : ℝ) ≤ ((((645223706539 : ℚ) / 250000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1607 < q → q < 1609 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1609).mp (by decide +kernel))) hgap
  have hprev := lrU_252
  have hcast : (((1609:ℕ):ℝ)/(((1609:ℕ):ℝ)-1)) = (((1609:ℚ)/((1609:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1609:ℚ)/((1609:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1609:ℚ)/((1609:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1609:ℚ)/((1609:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1290136564451 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((1609:ℚ)/((1609:ℚ)-1)) : ℚ) ≤ ((645223706539 : ℚ) / 250000000000) := by decide +kernel
  have hratR : ((((1290136564451 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1609:ℚ)/((1609:ℚ)-1)) : ℚ) : ℝ) ≤ ((((645223706539 : ℚ) / 250000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_254 : Commons.NumberTheory.Mertens.logRatioSum ((1613 : ℕ) : ℝ) ≤ ((((516302996243 : ℚ) / 200000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1609 < q → q < 1613 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1613).mp (by decide +kernel))) hgap
  have hprev := lrU_253
  have hcast : (((1613:ℕ):ℝ)/(((1613:ℕ):ℝ)-1)) = (((1613:ℚ)/((1613:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1613:ℚ)/((1613:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1613:ℚ)/((1613:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1613:ℚ)/((1613:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((645223706539 : ℚ) / 250000000000) + Work.RHContract.RegionI.logUpQ (((1613:ℚ)/((1613:ℚ)-1)) : ℚ) ≤ ((516302996243 : ℚ) / 200000000000) := by decide +kernel
  have hratR : ((((645223706539 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1613:ℚ)/((1613:ℚ)-1)) : ℚ) : ℝ) ≤ ((((516302996243 : ℚ) / 200000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_255 : Commons.NumberTheory.Mertens.logRatioSum ((1619 : ℕ) : ℝ) ≤ ((((103285313491 : ℚ) / 40000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1613 < q → q < 1619 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1619).mp (by decide +kernel))) hgap
  have hprev := lrU_254
  have hcast : (((1619:ℕ):ℝ)/(((1619:ℕ):ℝ)-1)) = (((1619:ℚ)/((1619:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1619:ℚ)/((1619:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1619:ℚ)/((1619:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1619:ℚ)/((1619:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((516302996243 : ℚ) / 200000000000) + Work.RHContract.RegionI.logUpQ (((1619:ℚ)/((1619:ℚ)-1)) : ℚ) ≤ ((103285313491 : ℚ) / 40000000000) := by decide +kernel
  have hratR : ((((516302996243 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1619:ℚ)/((1619:ℚ)-1)) : ℚ) : ℝ) ≤ ((((103285313491 : ℚ) / 40000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_256 : Commons.NumberTheory.Mertens.logRatioSum ((1621 : ℕ) : ℝ) ≤ ((((516549986157 : ℚ) / 200000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1619 < q → q < 1621 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1621).mp (by decide +kernel))) hgap
  have hprev := lrU_255
  have hcast : (((1621:ℕ):ℝ)/(((1621:ℕ):ℝ)-1)) = (((1621:ℚ)/((1621:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1621:ℚ)/((1621:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1621:ℚ)/((1621:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1621:ℚ)/((1621:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((103285313491 : ℚ) / 40000000000) + Work.RHContract.RegionI.logUpQ (((1621:ℚ)/((1621:ℚ)-1)) : ℚ) ≤ ((516549986157 : ℚ) / 200000000000) := by decide +kernel
  have hratR : ((((103285313491 : ℚ) / 40000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1621:ℚ)/((1621:ℚ)-1)) : ℚ) : ℝ) ≤ ((((516549986157 : ℚ) / 200000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_257 : Commons.NumberTheory.Mertens.logRatioSum ((1627 : ℕ) : ℝ) ≤ ((((2583364747897 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1621 < q → q < 1627 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1627).mp (by decide +kernel))) hgap
  have hprev := lrU_256
  have hcast : (((1627:ℕ):ℝ)/(((1627:ℕ):ℝ)-1)) = (((1627:ℚ)/((1627:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1627:ℚ)/((1627:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1627:ℚ)/((1627:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1627:ℚ)/((1627:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((516549986157 : ℚ) / 200000000000) + Work.RHContract.RegionI.logUpQ (((1627:ℚ)/((1627:ℚ)-1)) : ℚ) ≤ ((2583364747897 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((516549986157 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1627:ℚ)/((1627:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2583364747897 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_258 : Commons.NumberTheory.Mertens.logRatioSum ((1637 : ℕ) : ℝ) ≤ ((((1291987904053 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1627 < q → q < 1637 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1637).mp (by decide +kernel))) hgap
  have hprev := lrU_257
  have hcast : (((1637:ℕ):ℝ)/(((1637:ℕ):ℝ)-1)) = (((1637:ℚ)/((1637:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1637:ℚ)/((1637:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1637:ℚ)/((1637:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1637:ℚ)/((1637:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2583364747897 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((1637:ℚ)/((1637:ℚ)-1)) : ℚ) ≤ ((1291987904053 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((2583364747897 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1637:ℚ)/((1637:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1291987904053 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_259 : Commons.NumberTheory.Mertens.logRatioSum ((1657 : ℕ) : ℝ) ≤ ((((646144872647 : ℚ) / 250000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1637 < q → q < 1657 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1657).mp (by decide +kernel))) hgap
  have hprev := lrU_258
  have hcast : (((1657:ℕ):ℝ)/(((1657:ℕ):ℝ)-1)) = (((1657:ℚ)/((1657:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1657:ℚ)/((1657:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1657:ℚ)/((1657:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1657:ℚ)/((1657:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1291987904053 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((1657:ℚ)/((1657:ℚ)-1)) : ℚ) ≤ ((646144872647 : ℚ) / 250000000000) := by decide +kernel
  have hratR : ((((1291987904053 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1657:ℚ)/((1657:ℚ)-1)) : ℚ) : ℝ) ≤ ((((646144872647 : ℚ) / 250000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_260 : Commons.NumberTheory.Mertens.logRatioSum ((1663 : ℕ) : ℝ) ≤ ((((1292590497183 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1657 < q → q < 1663 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1663).mp (by decide +kernel))) hgap
  have hprev := lrU_259
  have hcast : (((1663:ℕ):ℝ)/(((1663:ℕ):ℝ)-1)) = (((1663:ℚ)/((1663:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1663:ℚ)/((1663:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1663:ℚ)/((1663:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1663:ℚ)/((1663:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((646144872647 : ℚ) / 250000000000) + Work.RHContract.RegionI.logUpQ (((1663:ℚ)/((1663:ℚ)-1)) : ℚ) ≤ ((1292590497183 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((646144872647 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1663:ℚ)/((1663:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1292590497183 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_261 : Commons.NumberTheory.Mertens.logRatioSum ((1667 : ℕ) : ℝ) ≤ ((((2585781054391 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1663 < q → q < 1667 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1667).mp (by decide +kernel))) hgap
  have hprev := lrU_260
  have hcast : (((1667:ℕ):ℝ)/(((1667:ℕ):ℝ)-1)) = (((1667:ℚ)/((1667:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1667:ℚ)/((1667:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1667:ℚ)/((1667:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1667:ℚ)/((1667:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1292590497183 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((1667:ℚ)/((1667:ℚ)-1)) : ℚ) ≤ ((2585781054391 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((1292590497183 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1667:ℚ)/((1667:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2585781054391 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_262 : Commons.NumberTheory.Mertens.logRatioSum ((1669 : ℕ) : ℝ) ≤ ((((517276079027 : ℚ) / 200000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1667 < q → q < 1669 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1669).mp (by decide +kernel))) hgap
  have hprev := lrU_261
  have hcast : (((1669:ℕ):ℝ)/(((1669:ℕ):ℝ)-1)) = (((1669:ℚ)/((1669:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1669:ℚ)/((1669:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1669:ℚ)/((1669:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1669:ℚ)/((1669:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2585781054391 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((1669:ℚ)/((1669:ℚ)-1)) : ℚ) ≤ ((517276079027 : ℚ) / 200000000000) := by decide +kernel
  have hratR : ((((2585781054391 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1669:ℚ)/((1669:ℚ)-1)) : ℚ) : ℝ) ≤ ((((517276079027 : ℚ) / 200000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_263 : Commons.NumberTheory.Mertens.logRatioSum ((1693 : ℕ) : ℝ) ≤ ((((1293485618551 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1669 < q → q < 1693 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1693).mp (by decide +kernel))) hgap
  have hprev := lrU_262
  have hcast : (((1693:ℕ):ℝ)/(((1693:ℕ):ℝ)-1)) = (((1693:ℚ)/((1693:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1693:ℚ)/((1693:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1693:ℚ)/((1693:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1693:ℚ)/((1693:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((517276079027 : ℚ) / 200000000000) + Work.RHContract.RegionI.logUpQ (((1693:ℚ)/((1693:ℚ)-1)) : ℚ) ≤ ((1293485618551 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((517276079027 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1693:ℚ)/((1693:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1293485618551 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_264 : Commons.NumberTheory.Mertens.logRatioSum ((1697 : ℕ) : ℝ) ≤ ((((517512137197 : ℚ) / 200000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1693 < q → q < 1697 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1697).mp (by decide +kernel))) hgap
  have hprev := lrU_263
  have hcast : (((1697:ℕ):ℝ)/(((1697:ℕ):ℝ)-1)) = (((1697:ℚ)/((1697:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1697:ℚ)/((1697:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1697:ℚ)/((1697:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1697:ℚ)/((1697:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1293485618551 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((1697:ℚ)/((1697:ℚ)-1)) : ℚ) ≤ ((517512137197 : ℚ) / 200000000000) := by decide +kernel
  have hratR : ((((1293485618551 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1697:ℚ)/((1697:ℚ)-1)) : ℚ) : ℝ) ≤ ((((517512137197 : ℚ) / 200000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_265 : Commons.NumberTheory.Mertens.logRatioSum ((1699 : ℕ) : ℝ) ≤ ((((1294074720393 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1697 < q → q < 1699 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1699).mp (by decide +kernel))) hgap
  have hprev := lrU_264
  have hcast : (((1699:ℕ):ℝ)/(((1699:ℕ):ℝ)-1)) = (((1699:ℚ)/((1699:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1699:ℚ)/((1699:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1699:ℚ)/((1699:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1699:ℚ)/((1699:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((517512137197 : ℚ) / 200000000000) + Work.RHContract.RegionI.logUpQ (((1699:ℚ)/((1699:ℚ)-1)) : ℚ) ≤ ((1294074720393 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((517512137197 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1699:ℚ)/((1699:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1294074720393 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_266 : Commons.NumberTheory.Mertens.logRatioSum ((1709 : ℕ) : ℝ) ≤ ((((1294367374777 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1699 < q → q < 1709 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1709).mp (by decide +kernel))) hgap
  have hprev := lrU_265
  have hcast : (((1709:ℕ):ℝ)/(((1709:ℕ):ℝ)-1)) = (((1709:ℚ)/((1709:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1709:ℚ)/((1709:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1709:ℚ)/((1709:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1709:ℚ)/((1709:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1294074720393 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((1709:ℚ)/((1709:ℚ)-1)) : ℚ) ≤ ((1294367374777 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((1294074720393 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1709:ℚ)/((1709:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1294367374777 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_267 : Commons.NumberTheory.Mertens.logRatioSum ((1721 : ℕ) : ℝ) ≤ ((((2589315975959 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1709 < q → q < 1721 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1721).mp (by decide +kernel))) hgap
  have hprev := lrU_266
  have hcast : (((1721:ℕ):ℝ)/(((1721:ℕ):ℝ)-1)) = (((1721:ℚ)/((1721:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1721:ℚ)/((1721:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1721:ℚ)/((1721:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1721:ℚ)/((1721:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1294367374777 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((1721:ℚ)/((1721:ℚ)-1)) : ℚ) ≤ ((2589315975959 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((1294367374777 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1721:ℚ)/((1721:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2589315975959 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_268 : Commons.NumberTheory.Mertens.logRatioSum ((1723 : ℕ) : ℝ) ≤ ((((1035958611 : ℚ) / 400000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1721 < q → q < 1723 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1723).mp (by decide +kernel))) hgap
  have hprev := lrU_267
  have hcast : (((1723:ℕ):ℝ)/(((1723:ℕ):ℝ)-1)) = (((1723:ℚ)/((1723:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1723:ℚ)/((1723:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1723:ℚ)/((1723:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1723:ℚ)/((1723:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2589315975959 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((1723:ℚ)/((1723:ℚ)-1)) : ℚ) ≤ ((1035958611 : ℚ) / 400000000) := by decide +kernel
  have hratR : ((((2589315975959 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1723:ℚ)/((1723:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1035958611 : ℚ) / 400000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_269 : Commons.NumberTheory.Mertens.logRatioSum ((1733 : ℕ) : ℝ) ≤ ((((1295236864047 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1723 < q → q < 1733 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1733).mp (by decide +kernel))) hgap
  have hprev := lrU_268
  have hcast : (((1733:ℕ):ℝ)/(((1733:ℕ):ℝ)-1)) = (((1733:ℚ)/((1733:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1733:ℚ)/((1733:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1733:ℚ)/((1733:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1733:ℚ)/((1733:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1035958611 : ℚ) / 400000000) + Work.RHContract.RegionI.logUpQ (((1733:ℚ)/((1733:ℚ)-1)) : ℚ) ≤ ((1295236864047 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((1035958611 : ℚ) / 400000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1733:ℚ)/((1733:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1295236864047 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_270 : Commons.NumberTheory.Mertens.logRatioSum ((1741 : ℕ) : ℝ) ≤ ((((1295524137827 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1733 < q → q < 1741 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1741).mp (by decide +kernel))) hgap
  have hprev := lrU_269
  have hcast : (((1741:ℕ):ℝ)/(((1741:ℕ):ℝ)-1)) = (((1741:ℚ)/((1741:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1741:ℚ)/((1741:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1741:ℚ)/((1741:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1741:ℚ)/((1741:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1295236864047 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((1741:ℚ)/((1741:ℚ)-1)) : ℚ) ≤ ((1295524137827 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((1295236864047 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1741:ℚ)/((1741:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1295524137827 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_271 : Commons.NumberTheory.Mertens.logRatioSum ((1747 : ℕ) : ℝ) ≤ ((((2591620849389 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1741 < q → q < 1747 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1747).mp (by decide +kernel))) hgap
  have hprev := lrU_270
  have hcast : (((1747:ℕ):ℝ)/(((1747:ℕ):ℝ)-1)) = (((1747:ℚ)/((1747:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1747:ℚ)/((1747:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1747:ℚ)/((1747:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1747:ℚ)/((1747:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1295524137827 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((1747:ℚ)/((1747:ℚ)-1)) : ℚ) ≤ ((2591620849389 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((1295524137827 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1747:ℚ)/((1747:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2591620849389 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_272 : Commons.NumberTheory.Mertens.logRatioSum ((1753 : ℕ) : ℝ) ≤ ((((1296095731407 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1747 < q → q < 1753 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1753).mp (by decide +kernel))) hgap
  have hprev := lrU_271
  have hcast : (((1753:ℕ):ℝ)/(((1753:ℕ):ℝ)-1)) = (((1753:ℚ)/((1753:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1753:ℚ)/((1753:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1753:ℚ)/((1753:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1753:ℚ)/((1753:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2591620849389 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((1753:ℚ)/((1753:ℚ)-1)) : ℚ) ≤ ((1296095731407 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((2591620849389 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1753:ℚ)/((1753:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1296095731407 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_273 : Commons.NumberTheory.Mertens.logRatioSum ((1759 : ℕ) : ℝ) ≤ ((((2592760129307 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1753 < q → q < 1759 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1759).mp (by decide +kernel))) hgap
  have hprev := lrU_272
  have hcast : (((1759:ℕ):ℝ)/(((1759:ℕ):ℝ)-1)) = (((1759:ℚ)/((1759:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1759:ℚ)/((1759:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1759:ℚ)/((1759:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1759:ℚ)/((1759:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1296095731407 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((1759:ℚ)/((1759:ℚ)-1)) : ℚ) ≤ ((2592760129307 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((1296095731407 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1759:ℚ)/((1759:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2592760129307 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_274 : Commons.NumberTheory.Mertens.logRatioSum ((1777 : ℕ) : ℝ) ≤ ((((259332303391 : ℚ) / 100000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1759 < q → q < 1777 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1777).mp (by decide +kernel))) hgap
  have hprev := lrU_273
  have hcast : (((1777:ℕ):ℝ)/(((1777:ℕ):ℝ)-1)) = (((1777:ℚ)/((1777:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1777:ℚ)/((1777:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1777:ℚ)/((1777:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1777:ℚ)/((1777:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2592760129307 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((1777:ℚ)/((1777:ℚ)-1)) : ℚ) ≤ ((259332303391 : ℚ) / 100000000000) := by decide +kernel
  have hratR : ((((2592760129307 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1777:ℚ)/((1777:ℚ)-1)) : ℚ) : ℝ) ≤ ((((259332303391 : ℚ) / 100000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_275 : Commons.NumberTheory.Mertens.logRatioSum ((1783 : ℕ) : ℝ) ≤ ((((2593884043743 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1777 < q → q < 1783 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1783).mp (by decide +kernel))) hgap
  have hprev := lrU_274
  have hcast : (((1783:ℕ):ℝ)/(((1783:ℕ):ℝ)-1)) = (((1783:ℚ)/((1783:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1783:ℚ)/((1783:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1783:ℚ)/((1783:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1783:ℚ)/((1783:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((259332303391 : ℚ) / 100000000000) + Work.RHContract.RegionI.logUpQ (((1783:ℚ)/((1783:ℚ)-1)) : ℚ) ≤ ((2593884043743 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((259332303391 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1783:ℚ)/((1783:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2593884043743 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_276 : Commons.NumberTheory.Mertens.logRatioSum ((1787 : ℕ) : ℝ) ≤ ((((1297221898733 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1783 < q → q < 1787 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1787).mp (by decide +kernel))) hgap
  have hprev := lrU_275
  have hcast : (((1787:ℕ):ℝ)/(((1787:ℕ):ℝ)-1)) = (((1787:ℚ)/((1787:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1787:ℚ)/((1787:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1787:ℚ)/((1787:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1787:ℚ)/((1787:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2593884043743 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((1787:ℚ)/((1787:ℚ)-1)) : ℚ) ≤ ((1297221898733 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((2593884043743 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1787:ℚ)/((1787:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1297221898733 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_277 : Commons.NumberTheory.Mertens.logRatioSum ((1789 : ℕ) : ℝ) ≤ ((((1297501462621 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1787 < q → q < 1789 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1789).mp (by decide +kernel))) hgap
  have hprev := lrU_276
  have hcast : (((1789:ℕ):ℝ)/(((1789:ℕ):ℝ)-1)) = (((1789:ℚ)/((1789:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1789:ℚ)/((1789:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1789:ℚ)/((1789:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1789:ℚ)/((1789:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1297221898733 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((1789:ℚ)/((1789:ℚ)-1)) : ℚ) ≤ ((1297501462621 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((1297221898733 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1789:ℚ)/((1789:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1297501462621 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_278 : Commons.NumberTheory.Mertens.logRatioSum ((1801 : ℕ) : ℝ) ≤ ((((1297779163267 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1789 < q → q < 1801 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1801).mp (by decide +kernel))) hgap
  have hprev := lrU_277
  have hcast : (((1801:ℕ):ℝ)/(((1801:ℕ):ℝ)-1)) = (((1801:ℚ)/((1801:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1801:ℚ)/((1801:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1801:ℚ)/((1801:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1801:ℚ)/((1801:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1297501462621 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((1801:ℚ)/((1801:ℚ)-1)) : ℚ) ≤ ((1297779163267 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((1297501462621 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1801:ℚ)/((1801:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1297779163267 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_279 : Commons.NumberTheory.Mertens.logRatioSum ((1811 : ℕ) : ℝ) ≤ ((((1298055330079 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1801 < q → q < 1811 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1811).mp (by decide +kernel))) hgap
  have hprev := lrU_278
  have hcast : (((1811:ℕ):ℝ)/(((1811:ℕ):ℝ)-1)) = (((1811:ℚ)/((1811:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1811:ℚ)/((1811:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1811:ℚ)/((1811:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1811:ℚ)/((1811:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1297779163267 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((1811:ℚ)/((1811:ℚ)-1)) : ℚ) ≤ ((1298055330079 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((1297779163267 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1811:ℚ)/((1811:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1298055330079 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_280 : Commons.NumberTheory.Mertens.logRatioSum ((1823 : ℕ) : ℝ) ≤ ((((2596659357017 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1811 < q → q < 1823 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1823).mp (by decide +kernel))) hgap
  have hprev := lrU_279
  have hcast : (((1823:ℕ):ℝ)/(((1823:ℕ):ℝ)-1)) = (((1823:ℚ)/((1823:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1823:ℚ)/((1823:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1823:ℚ)/((1823:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1823:ℚ)/((1823:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1298055330079 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((1823:ℚ)/((1823:ℚ)-1)) : ℚ) ≤ ((2596659357017 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((1298055330079 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1823:ℚ)/((1823:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2596659357017 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_281 : Commons.NumberTheory.Mertens.logRatioSum ((1831 : ℕ) : ℝ) ≤ ((((2597205655857 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1823 < q → q < 1831 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1831).mp (by decide +kernel))) hgap
  have hprev := lrU_280
  have hcast : (((1831:ℕ):ℝ)/(((1831:ℕ):ℝ)-1)) = (((1831:ℚ)/((1831:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1831:ℚ)/((1831:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1831:ℚ)/((1831:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1831:ℚ)/((1831:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2596659357017 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((1831:ℚ)/((1831:ℚ)-1)) : ℚ) ≤ ((2597205655857 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2596659357017 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1831:ℚ)/((1831:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2597205655857 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_282 : Commons.NumberTheory.Mertens.logRatioSum ((1847 : ℕ) : ℝ) ≤ ((((1298873610497 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1831 < q → q < 1847 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1847).mp (by decide +kernel))) hgap
  have hprev := lrU_281
  have hcast : (((1847:ℕ):ℝ)/(((1847:ℕ):ℝ)-1)) = (((1847:ℚ)/((1847:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1847:ℚ)/((1847:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1847:ℚ)/((1847:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1847:ℚ)/((1847:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2597205655857 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((1847:ℚ)/((1847:ℚ)-1)) : ℚ) ≤ ((1298873610497 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((2597205655857 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1847:ℚ)/((1847:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1298873610497 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_283 : Commons.NumberTheory.Mertens.logRatioSum ((1861 : ℕ) : ℝ) ≤ ((((259828471093 : ℚ) / 100000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1847 < q → q < 1861 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1861).mp (by decide +kernel))) hgap
  have hprev := lrU_282
  have hcast : (((1861:ℕ):ℝ)/(((1861:ℕ):ℝ)-1)) = (((1861:ℚ)/((1861:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1861:ℚ)/((1861:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1861:ℚ)/((1861:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1861:ℚ)/((1861:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1298873610497 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((1861:ℚ)/((1861:ℚ)-1)) : ℚ) ≤ ((259828471093 : ℚ) / 100000000000) := by decide +kernel
  have hratR : ((((1298873610497 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1861:ℚ)/((1861:ℚ)-1)) : ℚ) : ℝ) ≤ ((((259828471093 : ℚ) / 100000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_284 : Commons.NumberTheory.Mertens.logRatioSum ((1867 : ℕ) : ℝ) ≤ ((((519764094613 : ℚ) / 200000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1861 < q → q < 1867 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1867).mp (by decide +kernel))) hgap
  have hprev := lrU_283
  have hcast : (((1867:ℕ):ℝ)/(((1867:ℕ):ℝ)-1)) = (((1867:ℚ)/((1867:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1867:ℚ)/((1867:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1867:ℚ)/((1867:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1867:ℚ)/((1867:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((259828471093 : ℚ) / 100000000000) + Work.RHContract.RegionI.logUpQ (((1867:ℚ)/((1867:ℚ)-1)) : ℚ) ≤ ((519764094613 : ℚ) / 200000000000) := by decide +kernel
  have hratR : ((((259828471093 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1867:ℚ)/((1867:ℚ)-1)) : ℚ) : ℝ) ≤ ((((519764094613 : ℚ) / 200000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_285 : Commons.NumberTheory.Mertens.logRatioSum ((1871 : ℕ) : ℝ) ≤ ((((2599355089491 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1867 < q → q < 1871 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1871).mp (by decide +kernel))) hgap
  have hprev := lrU_284
  have hcast : (((1871:ℕ):ℝ)/(((1871:ℕ):ℝ)-1)) = (((1871:ℚ)/((1871:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1871:ℚ)/((1871:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1871:ℚ)/((1871:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1871:ℚ)/((1871:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((519764094613 : ℚ) / 200000000000) + Work.RHContract.RegionI.logUpQ (((1871:ℚ)/((1871:ℚ)-1)) : ℚ) ≤ ((2599355089491 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((519764094613 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1871:ℚ)/((1871:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2599355089491 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_286 : Commons.NumberTheory.Mertens.logRatioSum ((1873 : ℕ) : ℝ) ≤ ((((1299944567449 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1871 < q → q < 1873 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1873).mp (by decide +kernel))) hgap
  have hprev := lrU_285
  have hcast : (((1873:ℕ):ℝ)/(((1873:ℕ):ℝ)-1)) = (((1873:ℚ)/((1873:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1873:ℚ)/((1873:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1873:ℚ)/((1873:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1873:ℚ)/((1873:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2599355089491 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((1873:ℚ)/((1873:ℚ)-1)) : ℚ) ≤ ((1299944567449 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((2599355089491 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1873:ℚ)/((1873:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1299944567449 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_287 : Commons.NumberTheory.Mertens.logRatioSum ((1877 : ℕ) : ℝ) ≤ ((((2600422041919 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1873 < q → q < 1877 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1877).mp (by decide +kernel))) hgap
  have hprev := lrU_286
  have hcast : (((1877:ℕ):ℝ)/(((1877:ℕ):ℝ)-1)) = (((1877:ℚ)/((1877:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1877:ℚ)/((1877:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1877:ℚ)/((1877:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1877:ℚ)/((1877:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1299944567449 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((1877:ℚ)/((1877:ℚ)-1)) : ℚ) ≤ ((2600422041919 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((1299944567449 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1877:ℚ)/((1877:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2600422041919 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_288 : Commons.NumberTheory.Mertens.logRatioSum ((1879 : ℕ) : ℝ) ≤ ((((520190876313 : ℚ) / 200000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1877 < q → q < 1879 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1879).mp (by decide +kernel))) hgap
  have hprev := lrU_287
  have hcast : (((1879:ℕ):ℝ)/(((1879:ℕ):ℝ)-1)) = (((1879:ℚ)/((1879:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1879:ℚ)/((1879:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1879:ℚ)/((1879:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1879:ℚ)/((1879:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2600422041919 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((1879:ℚ)/((1879:ℚ)-1)) : ℚ) ≤ ((520190876313 : ℚ) / 200000000000) := by decide +kernel
  have hratR : ((((2600422041919 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1879:ℚ)/((1879:ℚ)-1)) : ℚ) : ℝ) ≤ ((((520190876313 : ℚ) / 200000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_289 : Commons.NumberTheory.Mertens.logRatioSum ((1889 : ℕ) : ℝ) ≤ ((((1300741951181 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1879 < q → q < 1889 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1889).mp (by decide +kernel))) hgap
  have hprev := lrU_288
  have hcast : (((1889:ℕ):ℝ)/(((1889:ℕ):ℝ)-1)) = (((1889:ℚ)/((1889:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1889:ℚ)/((1889:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1889:ℚ)/((1889:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1889:ℚ)/((1889:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((520190876313 : ℚ) / 200000000000) + Work.RHContract.RegionI.logUpQ (((1889:ℚ)/((1889:ℚ)-1)) : ℚ) ≤ ((1300741951181 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((520190876313 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1889:ℚ)/((1889:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1300741951181 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_290 : Commons.NumberTheory.Mertens.logRatioSum ((1901 : ℕ) : ℝ) ≤ ((((162625629981 : ℚ) / 62500000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1889 < q → q < 1901 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1901).mp (by decide +kernel))) hgap
  have hprev := lrU_289
  have hcast : (((1901:ℕ):ℝ)/(((1901:ℕ):ℝ)-1)) = (((1901:ℚ)/((1901:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1901:ℚ)/((1901:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1901:ℚ)/((1901:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1901:ℚ)/((1901:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1300741951181 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((1901:ℚ)/((1901:ℚ)-1)) : ℚ) ≤ ((162625629981 : ℚ) / 62500000000) := by decide +kernel
  have hratR : ((((1300741951181 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1901:ℚ)/((1901:ℚ)-1)) : ℚ) : ℝ) ≤ ((((162625629981 : ℚ) / 62500000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_291 : Commons.NumberTheory.Mertens.logRatioSum ((1907 : ℕ) : ℝ) ≤ ((((2602534601083 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1901 < q → q < 1907 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1907).mp (by decide +kernel))) hgap
  have hprev := lrU_290
  have hcast : (((1907:ℕ):ℝ)/(((1907:ℕ):ℝ)-1)) = (((1907:ℚ)/((1907:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1907:ℚ)/((1907:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1907:ℚ)/((1907:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1907:ℚ)/((1907:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((162625629981 : ℚ) / 62500000000) + Work.RHContract.RegionI.logUpQ (((1907:ℚ)/((1907:ℚ)-1)) : ℚ) ≤ ((2602534601083 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((162625629981 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1907:ℚ)/((1907:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2602534601083 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_292 : Commons.NumberTheory.Mertens.logRatioSum ((1913 : ℕ) : ℝ) ≤ ((((162691092307 : ℚ) / 62500000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1907 < q → q < 1913 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1913).mp (by decide +kernel))) hgap
  have hprev := lrU_291
  have hcast : (((1913:ℕ):ℝ)/(((1913:ℕ):ℝ)-1)) = (((1913:ℚ)/((1913:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1913:ℚ)/((1913:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1913:ℚ)/((1913:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1913:ℚ)/((1913:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2602534601083 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((1913:ℚ)/((1913:ℚ)-1)) : ℚ) ≤ ((162691092307 : ℚ) / 62500000000) := by decide +kernel
  have hratR : ((((2602534601083 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1913:ℚ)/((1913:ℚ)-1)) : ℚ) : ℝ) ≤ ((((162691092307 : ℚ) / 62500000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_293 : Commons.NumberTheory.Mertens.logRatioSum ((1931 : ℕ) : ℝ) ≤ ((((1301787738721 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1913 < q → q < 1931 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1931).mp (by decide +kernel))) hgap
  have hprev := lrU_292
  have hcast : (((1931:ℕ):ℝ)/(((1931:ℕ):ℝ)-1)) = (((1931:ℚ)/((1931:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1931:ℚ)/((1931:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1931:ℚ)/((1931:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1931:ℚ)/((1931:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((162691092307 : ℚ) / 62500000000) + Work.RHContract.RegionI.logUpQ (((1931:ℚ)/((1931:ℚ)-1)) : ℚ) ≤ ((1301787738721 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((162691092307 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1931:ℚ)/((1931:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1301787738721 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_294 : Commons.NumberTheory.Mertens.logRatioSum ((1933 : ℕ) : ℝ) ≤ ((((1302046470939 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1931 < q → q < 1933 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1933).mp (by decide +kernel))) hgap
  have hprev := lrU_293
  have hcast : (((1933:ℕ):ℝ)/(((1933:ℕ):ℝ)-1)) = (((1933:ℚ)/((1933:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1933:ℚ)/((1933:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1933:ℚ)/((1933:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1933:ℚ)/((1933:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1301787738721 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((1933:ℚ)/((1933:ℚ)-1)) : ℚ) ≤ ((1302046470939 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((1301787738721 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1933:ℚ)/((1933:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1302046470939 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_295 : Commons.NumberTheory.Mertens.logRatioSum ((1949 : ℕ) : ℝ) ≤ ((((20348485603 : ℚ) / 7812500000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1933 < q → q < 1949 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1949).mp (by decide +kernel))) hgap
  have hprev := lrU_294
  have hcast : (((1949:ℕ):ℝ)/(((1949:ℕ):ℝ)-1)) = (((1949:ℚ)/((1949:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1949:ℚ)/((1949:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1949:ℚ)/((1949:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1949:ℚ)/((1949:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1302046470939 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((1949:ℚ)/((1949:ℚ)-1)) : ℚ) ≤ ((20348485603 : ℚ) / 7812500000) := by decide +kernel
  have hratR : ((((1302046470939 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1949:ℚ)/((1949:ℚ)-1)) : ℚ) : ℝ) ≤ ((((20348485603 : ℚ) / 7812500000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_296 : Commons.NumberTheory.Mertens.logRatioSum ((1951 : ℕ) : ℝ) ≤ ((((2084095077 : ℚ) / 800000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1949 < q → q < 1951 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1951).mp (by decide +kernel))) hgap
  have hprev := lrU_295
  have hcast : (((1951:ℕ):ℝ)/(((1951:ℕ):ℝ)-1)) = (((1951:ℚ)/((1951:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1951:ℚ)/((1951:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1951:ℚ)/((1951:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1951:ℚ)/((1951:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((20348485603 : ℚ) / 7812500000) + Work.RHContract.RegionI.logUpQ (((1951:ℚ)/((1951:ℚ)-1)) : ℚ) ≤ ((2084095077 : ℚ) / 800000000) := by decide +kernel
  have hratR : ((((20348485603 : ℚ) / 7812500000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1951:ℚ)/((1951:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2084095077 : ℚ) / 800000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_297 : Commons.NumberTheory.Mertens.logRatioSum ((1973 : ℕ) : ℝ) ≤ ((((2605625817111 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1951 < q → q < 1973 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1973).mp (by decide +kernel))) hgap
  have hprev := lrU_296
  have hcast : (((1973:ℕ):ℝ)/(((1973:ℕ):ℝ)-1)) = (((1973:ℚ)/((1973:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1973:ℚ)/((1973:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1973:ℚ)/((1973:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1973:ℚ)/((1973:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2084095077 : ℚ) / 800000000) + Work.RHContract.RegionI.logUpQ (((1973:ℚ)/((1973:ℚ)-1)) : ℚ) ≤ ((2605625817111 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2084095077 : ℚ) / 800000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1973:ℚ)/((1973:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2605625817111 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_298 : Commons.NumberTheory.Mertens.logRatioSum ((1979 : ℕ) : ℝ) ≤ ((((2606131250531 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1973 < q → q < 1979 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1979).mp (by decide +kernel))) hgap
  have hprev := lrU_297
  have hcast : (((1979:ℕ):ℝ)/(((1979:ℕ):ℝ)-1)) = (((1979:ℚ)/((1979:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1979:ℚ)/((1979:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1979:ℚ)/((1979:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1979:ℚ)/((1979:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2605625817111 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((1979:ℚ)/((1979:ℚ)-1)) : ℚ) ≤ ((2606131250531 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2605625817111 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1979:ℚ)/((1979:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2606131250531 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_299 : Commons.NumberTheory.Mertens.logRatioSum ((1987 : ℕ) : ℝ) ≤ ((((1303317324239 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1979 < q → q < 1987 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1987).mp (by decide +kernel))) hgap
  have hprev := lrU_298
  have hcast : (((1987:ℕ):ℝ)/(((1987:ℕ):ℝ)-1)) = (((1987:ℚ)/((1987:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1987:ℚ)/((1987:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1987:ℚ)/((1987:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1987:ℚ)/((1987:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2606131250531 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((1987:ℚ)/((1987:ℚ)-1)) : ℚ) ≤ ((1303317324239 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((2606131250531 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1987:ℚ)/((1987:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1303317324239 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_300 : Commons.NumberTheory.Mertens.logRatioSum ((1993 : ℕ) : ℝ) ≤ ((((2607136530547 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1987 < q → q < 1993 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1993).mp (by decide +kernel))) hgap
  have hprev := lrU_299
  have hcast : (((1993:ℕ):ℝ)/(((1993:ℕ):ℝ)-1)) = (((1993:ℚ)/((1993:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1993:ℚ)/((1993:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1993:ℚ)/((1993:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1993:ℚ)/((1993:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1303317324239 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((1993:ℚ)/((1993:ℚ)-1)) : ℚ) ≤ ((2607136530547 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((1303317324239 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1993:ℚ)/((1993:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2607136530547 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_301 : Commons.NumberTheory.Mertens.logRatioSum ((1997 : ℕ) : ℝ) ≤ ((((651909351773 : ℚ) / 250000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1993 < q → q < 1997 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1997).mp (by decide +kernel))) hgap
  have hprev := lrU_300
  have hcast : (((1997:ℕ):ℝ)/(((1997:ℕ):ℝ)-1)) = (((1997:ℚ)/((1997:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1997:ℚ)/((1997:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1997:ℚ)/((1997:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1997:ℚ)/((1997:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2607136530547 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((1997:ℚ)/((1997:ℚ)-1)) : ℚ) ≤ ((651909351773 : ℚ) / 250000000000) := by decide +kernel
  have hratR : ((((2607136530547 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1997:ℚ)/((1997:ℚ)-1)) : ℚ) : ℝ) ≤ ((((651909351773 : ℚ) / 250000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_302 : Commons.NumberTheory.Mertens.logRatioSum ((1999 : ℕ) : ℝ) ≤ ((((163008611399 : ℚ) / 62500000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1997 < q → q < 1999 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1999).mp (by decide +kernel))) hgap
  have hprev := lrU_301
  have hcast : (((1999:ℕ):ℝ)/(((1999:ℕ):ℝ)-1)) = (((1999:ℚ)/((1999:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((1999:ℚ)/((1999:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((1999:ℚ)/((1999:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((1999:ℚ)/((1999:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((651909351773 : ℚ) / 250000000000) + Work.RHContract.RegionI.logUpQ (((1999:ℚ)/((1999:ℚ)-1)) : ℚ) ≤ ((163008611399 : ℚ) / 62500000000) := by decide +kernel
  have hratR : ((((651909351773 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((1999:ℚ)/((1999:ℚ)-1)) : ℚ) : ℝ) ≤ ((((163008611399 : ℚ) / 62500000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_303 : Commons.NumberTheory.Mertens.logRatioSum ((2003 : ℕ) : ℝ) ≤ ((((104345486327 : ℚ) / 40000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 1999 < q → q < 2003 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2003).mp (by decide +kernel))) hgap
  have hprev := lrU_302
  have hcast : (((2003:ℕ):ℝ)/(((2003:ℕ):ℝ)-1)) = (((2003:ℚ)/((2003:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((2003:ℚ)/((2003:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((2003:ℚ)/((2003:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((2003:ℚ)/((2003:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((163008611399 : ℚ) / 62500000000) + Work.RHContract.RegionI.logUpQ (((2003:ℚ)/((2003:ℚ)-1)) : ℚ) ≤ ((104345486327 : ℚ) / 40000000000) := by decide +kernel
  have hratR : ((((163008611399 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((2003:ℚ)/((2003:ℚ)-1)) : ℚ) : ℝ) ≤ ((((104345486327 : ℚ) / 40000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_304 : Commons.NumberTheory.Mertens.logRatioSum ((2011 : ℕ) : ℝ) ≤ ((((521826909379 : ℚ) / 200000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2003 < q → q < 2011 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2011).mp (by decide +kernel))) hgap
  have hprev := lrU_303
  have hcast : (((2011:ℕ):ℝ)/(((2011:ℕ):ℝ)-1)) = (((2011:ℚ)/((2011:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((2011:ℚ)/((2011:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((2011:ℚ)/((2011:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((2011:ℚ)/((2011:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((104345486327 : ℚ) / 40000000000) + Work.RHContract.RegionI.logUpQ (((2011:ℚ)/((2011:ℚ)-1)) : ℚ) ≤ ((521826909379 : ℚ) / 200000000000) := by decide +kernel
  have hratR : ((((104345486327 : ℚ) / 40000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((2011:ℚ)/((2011:ℚ)-1)) : ℚ) : ℝ) ≤ ((((521826909379 : ℚ) / 200000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_305 : Commons.NumberTheory.Mertens.logRatioSum ((2017 : ℕ) : ℝ) ≤ ((((1304815227829 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2011 < q → q < 2017 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2017).mp (by decide +kernel))) hgap
  have hprev := lrU_304
  have hcast : (((2017:ℕ):ℝ)/(((2017:ℕ):ℝ)-1)) = (((2017:ℚ)/((2017:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((2017:ℚ)/((2017:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((2017:ℚ)/((2017:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((2017:ℚ)/((2017:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((521826909379 : ℚ) / 200000000000) + Work.RHContract.RegionI.logUpQ (((2017:ℚ)/((2017:ℚ)-1)) : ℚ) ≤ ((1304815227829 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((521826909379 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((2017:ℚ)/((2017:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1304815227829 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_306 : Commons.NumberTheory.Mertens.logRatioSum ((2027 : ℕ) : ℝ) ≤ ((((1305061958651 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2017 < q → q < 2027 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2027).mp (by decide +kernel))) hgap
  have hprev := lrU_305
  have hcast : (((2027:ℕ):ℝ)/(((2027:ℕ):ℝ)-1)) = (((2027:ℚ)/((2027:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((2027:ℚ)/((2027:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((2027:ℚ)/((2027:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((2027:ℚ)/((2027:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1304815227829 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((2027:ℚ)/((2027:ℚ)-1)) : ℚ) ≤ ((1305061958651 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((1304815227829 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((2027:ℚ)/((2027:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1305061958651 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_307 : Commons.NumberTheory.Mertens.logRatioSum ((2029 : ℕ) : ℝ) ≤ ((((2610616892417 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2027 < q → q < 2029 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2029).mp (by decide +kernel))) hgap
  have hprev := lrU_306
  have hcast : (((2029:ℕ):ℝ)/(((2029:ℕ):ℝ)-1)) = (((2029:ℚ)/((2029:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((2029:ℚ)/((2029:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((2029:ℚ)/((2029:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((2029:ℚ)/((2029:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1305061958651 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((2029:ℚ)/((2029:ℚ)-1)) : ℚ) ≤ ((2610616892417 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((1305061958651 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((2029:ℚ)/((2029:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2610616892417 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_308 : Commons.NumberTheory.Mertens.logRatioSum ((2039 : ℕ) : ℝ) ≤ ((((2611107449209 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2029 < q → q < 2039 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2039).mp (by decide +kernel))) hgap
  have hprev := lrU_307
  have hcast : (((2039:ℕ):ℝ)/(((2039:ℕ):ℝ)-1)) = (((2039:ℚ)/((2039:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((2039:ℚ)/((2039:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((2039:ℚ)/((2039:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((2039:ℚ)/((2039:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2610616892417 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((2039:ℚ)/((2039:ℚ)-1)) : ℚ) ≤ ((2611107449209 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2610616892417 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((2039:ℚ)/((2039:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2611107449209 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_309 : Commons.NumberTheory.Mertens.logRatioSum ((2053 : ℕ) : ℝ) ≤ ((((1305797329969 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2039 < q → q < 2053 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2053).mp (by decide +kernel))) hgap
  have hprev := lrU_308
  have hcast : (((2053:ℕ):ℝ)/(((2053:ℕ):ℝ)-1)) = (((2053:ℚ)/((2053:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((2053:ℚ)/((2053:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((2053:ℚ)/((2053:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((2053:ℚ)/((2053:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2611107449209 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((2053:ℚ)/((2053:ℚ)-1)) : ℚ) ≤ ((1305797329969 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((2611107449209 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((2053:ℚ)/((2053:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1305797329969 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_310 : Commons.NumberTheory.Mertens.logRatioSum ((2063 : ℕ) : ℝ) ≤ ((((2612079508433 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2053 < q → q < 2063 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2063).mp (by decide +kernel))) hgap
  have hprev := lrU_309
  have hcast : (((2063:ℕ):ℝ)/(((2063:ℕ):ℝ)-1)) = (((2063:ℚ)/((2063:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((2063:ℚ)/((2063:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((2063:ℚ)/((2063:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((2063:ℚ)/((2063:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1305797329969 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((2063:ℚ)/((2063:ℚ)-1)) : ℚ) ≤ ((2612079508433 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((1305797329969 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((2063:ℚ)/((2063:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2612079508433 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_311 : Commons.NumberTheory.Mertens.logRatioSum ((2069 : ℕ) : ℝ) ≤ ((((2612562950551 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2063 < q → q < 2069 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2069).mp (by decide +kernel))) hgap
  have hprev := lrU_310
  have hcast : (((2069:ℕ):ℝ)/(((2069:ℕ):ℝ)-1)) = (((2069:ℚ)/((2069:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((2069:ℚ)/((2069:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((2069:ℚ)/((2069:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((2069:ℚ)/((2069:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2612079508433 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((2069:ℚ)/((2069:ℚ)-1)) : ℚ) ≤ ((2612562950551 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2612079508433 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((2069:ℚ)/((2069:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2612562950551 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_312 : Commons.NumberTheory.Mertens.logRatioSum ((2081 : ℕ) : ℝ) ≤ ((((10452174417 : ℚ) / 4000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2069 < q → q < 2081 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2081).mp (by decide +kernel))) hgap
  have hprev := lrU_311
  have hcast : (((2081:ℕ):ℝ)/(((2081:ℕ):ℝ)-1)) = (((2081:ℚ)/((2081:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((2081:ℚ)/((2081:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((2081:ℚ)/((2081:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((2081:ℚ)/((2081:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2612562950551 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((2081:ℚ)/((2081:ℚ)-1)) : ℚ) ≤ ((10452174417 : ℚ) / 4000000000) := by decide +kernel
  have hratR : ((((2612562950551 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((2081:ℚ)/((2081:ℚ)-1)) : ℚ) : ℝ) ≤ ((((10452174417 : ℚ) / 4000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_313 : Commons.NumberTheory.Mertens.logRatioSum ((2083 : ℕ) : ℝ) ≤ ((((2613523796337 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2081 < q → q < 2083 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2083).mp (by decide +kernel))) hgap
  have hprev := lrU_312
  have hcast : (((2083:ℕ):ℝ)/(((2083:ℕ):ℝ)-1)) = (((2083:ℚ)/((2083:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((2083:ℚ)/((2083:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((2083:ℚ)/((2083:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((2083:ℚ)/((2083:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((10452174417 : ℚ) / 4000000000) + Work.RHContract.RegionI.logUpQ (((2083:ℚ)/((2083:ℚ)-1)) : ℚ) ≤ ((2613523796337 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((10452174417 : ℚ) / 4000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((2083:ℚ)/((2083:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2613523796337 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_314 : Commons.NumberTheory.Mertens.logRatioSum ((2087 : ℕ) : ℝ) ≤ ((((1307001533927 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2083 < q → q < 2087 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2087).mp (by decide +kernel))) hgap
  have hprev := lrU_313
  have hcast : (((2087:ℕ):ℝ)/(((2087:ℕ):ℝ)-1)) = (((2087:ℚ)/((2087:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((2087:ℚ)/((2087:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((2087:ℚ)/((2087:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((2087:ℚ)/((2087:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2613523796337 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((2087:ℚ)/((2087:ℚ)-1)) : ℚ) ≤ ((1307001533927 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((2613523796337 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((2087:ℚ)/((2087:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1307001533927 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_315 : Commons.NumberTheory.Mertens.logRatioSum ((2089 : ℕ) : ℝ) ≤ ((((2614481880409 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2087 < q → q < 2089 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2089).mp (by decide +kernel))) hgap
  have hprev := lrU_314
  have hcast : (((2089:ℕ):ℝ)/(((2089:ℕ):ℝ)-1)) = (((2089:ℚ)/((2089:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((2089:ℚ)/((2089:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((2089:ℚ)/((2089:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((2089:ℚ)/((2089:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1307001533927 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((2089:ℚ)/((2089:ℚ)-1)) : ℚ) ≤ ((2614481880409 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((1307001533927 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((2089:ℚ)/((2089:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2614481880409 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_316 : Commons.NumberTheory.Mertens.logRatioSum ((2099 : ℕ) : ℝ) ≤ ((((1307479205637 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2089 < q → q < 2099 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2099).mp (by decide +kernel))) hgap
  have hprev := lrU_315
  have hcast : (((2099:ℕ):ℝ)/(((2099:ℕ):ℝ)-1)) = (((2099:ℚ)/((2099:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((2099:ℚ)/((2099:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((2099:ℚ)/((2099:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((2099:ℚ)/((2099:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2614481880409 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((2099:ℚ)/((2099:ℚ)-1)) : ℚ) ≤ ((1307479205637 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((2614481880409 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((2099:ℚ)/((2099:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1307479205637 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_317 : Commons.NumberTheory.Mertens.logRatioSum ((2111 : ℕ) : ℝ) ≤ ((((2615432232653 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2099 < q → q < 2111 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2111).mp (by decide +kernel))) hgap
  have hprev := lrU_316
  have hcast : (((2111:ℕ):ℝ)/(((2111:ℕ):ℝ)-1)) = (((2111:ℚ)/((2111:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((2111:ℚ)/((2111:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((2111:ℚ)/((2111:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((2111:ℚ)/((2111:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1307479205637 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((2111:ℚ)/((2111:ℚ)-1)) : ℚ) ≤ ((2615432232653 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((1307479205637 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((2111:ℚ)/((2111:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2615432232653 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_318 : Commons.NumberTheory.Mertens.logRatioSum ((2113 : ℕ) : ℝ) ≤ ((((2615905605443 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2111 < q → q < 2113 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2113).mp (by decide +kernel))) hgap
  have hprev := lrU_317
  have hcast : (((2113:ℕ):ℝ)/(((2113:ℕ):ℝ)-1)) = (((2113:ℚ)/((2113:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((2113:ℚ)/((2113:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((2113:ℚ)/((2113:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((2113:ℚ)/((2113:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2615432232653 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((2113:ℚ)/((2113:ℚ)-1)) : ℚ) ≤ ((2615905605443 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2615432232653 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((2113:ℚ)/((2113:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2615905605443 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_319 : Commons.NumberTheory.Mertens.logRatioSum ((2129 : ℕ) : ℝ) ≤ ((((20931003359 : ℚ) / 8000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2113 < q → q < 2129 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2129).mp (by decide +kernel))) hgap
  have hprev := lrU_318
  have hcast : (((2129:ℕ):ℝ)/(((2129:ℕ):ℝ)-1)) = (((2129:ℚ)/((2129:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((2129:ℚ)/((2129:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((2129:ℚ)/((2129:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((2129:ℚ)/((2129:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2615905605443 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((2129:ℚ)/((2129:ℚ)-1)) : ℚ) ≤ ((20931003359 : ℚ) / 8000000000) := by decide +kernel
  have hratR : ((((2615905605443 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((2129:ℚ)/((2129:ℚ)-1)) : ℚ) : ℝ) ≤ ((((20931003359 : ℚ) / 8000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_320 : Commons.NumberTheory.Mertens.logRatioSum ((2131 : ℕ) : ℝ) ≤ ((((2616844793271 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2129 < q → q < 2131 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2131).mp (by decide +kernel))) hgap
  have hprev := lrU_319
  have hcast : (((2131:ℕ):ℝ)/(((2131:ℕ):ℝ)-1)) = (((2131:ℚ)/((2131:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((2131:ℚ)/((2131:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((2131:ℚ)/((2131:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((2131:ℚ)/((2131:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((20931003359 : ℚ) / 8000000000) + Work.RHContract.RegionI.logUpQ (((2131:ℚ)/((2131:ℚ)-1)) : ℚ) ≤ ((2616844793271 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((20931003359 : ℚ) / 8000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((2131:ℚ)/((2131:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2616844793271 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_321 : Commons.NumberTheory.Mertens.logRatioSum ((2137 : ℕ) : ℝ) ≤ ((((2617312848511 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2131 < q → q < 2137 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2137).mp (by decide +kernel))) hgap
  have hprev := lrU_320
  have hcast : (((2137:ℕ):ℝ)/(((2137:ℕ):ℝ)-1)) = (((2137:ℚ)/((2137:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((2137:ℚ)/((2137:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((2137:ℚ)/((2137:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((2137:ℚ)/((2137:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2616844793271 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((2137:ℚ)/((2137:ℚ)-1)) : ℚ) ≤ ((2617312848511 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2616844793271 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((2137:ℚ)/((2137:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2617312848511 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_322 : Commons.NumberTheory.Mertens.logRatioSum ((2141 : ℕ) : ℝ) ≤ ((((523556005817 : ℚ) / 200000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2137 < q → q < 2141 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2141).mp (by decide +kernel))) hgap
  have hprev := lrU_321
  have hcast : (((2141:ℕ):ℝ)/(((2141:ℕ):ℝ)-1)) = (((2141:ℚ)/((2141:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((2141:ℚ)/((2141:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((2141:ℚ)/((2141:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((2141:ℚ)/((2141:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2617312848511 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((2141:ℚ)/((2141:ℚ)-1)) : ℚ) ≤ ((523556005817 : ℚ) / 200000000000) := by decide +kernel
  have hratR : ((((2617312848511 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((2141:ℚ)/((2141:ℚ)-1)) : ℚ) : ℝ) ≤ ((((523556005817 : ℚ) / 200000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_323 : Commons.NumberTheory.Mertens.logRatioSum ((2143 : ℕ) : ℝ) ≤ ((((2618246773551 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2141 < q → q < 2143 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2143).mp (by decide +kernel))) hgap
  have hprev := lrU_322
  have hcast : (((2143:ℕ):ℝ)/(((2143:ℕ):ℝ)-1)) = (((2143:ℚ)/((2143:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((2143:ℚ)/((2143:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((2143:ℚ)/((2143:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((2143:ℚ)/((2143:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((523556005817 : ℚ) / 200000000000) + Work.RHContract.RegionI.logUpQ (((2143:ℚ)/((2143:ℚ)-1)) : ℚ) ≤ ((2618246773551 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((523556005817 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((2143:ℚ)/((2143:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2618246773551 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_324 : Commons.NumberTheory.Mertens.logRatioSum ((2153 : ℕ) : ℝ) ≤ ((((1309355674817 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2143 < q → q < 2153 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2153).mp (by decide +kernel))) hgap
  have hprev := lrU_323
  have hcast : (((2153:ℕ):ℝ)/(((2153:ℕ):ℝ)-1)) = (((2153:ℚ)/((2153:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((2153:ℚ)/((2153:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((2153:ℚ)/((2153:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((2153:ℚ)/((2153:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2618246773551 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((2153:ℚ)/((2153:ℚ)-1)) : ℚ) ≤ ((1309355674817 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((2618246773551 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((2153:ℚ)/((2153:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1309355674817 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_325 : Commons.NumberTheory.Mertens.logRatioSum ((2161 : ℕ) : ℝ) ≤ ((((2619174205463 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2153 < q → q < 2161 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2161).mp (by decide +kernel))) hgap
  have hprev := lrU_324
  have hcast : (((2161:ℕ):ℝ)/(((2161:ℕ):ℝ)-1)) = (((2161:ℚ)/((2161:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((2161:ℚ)/((2161:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((2161:ℚ)/((2161:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((2161:ℚ)/((2161:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1309355674817 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((2161:ℚ)/((2161:ℚ)-1)) : ℚ) ≤ ((2619174205463 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((1309355674817 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((2161:ℚ)/((2161:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2619174205463 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_326 : Commons.NumberTheory.Mertens.logRatioSum ((2179 : ℕ) : ℝ) ≤ ((((523926647383 : ℚ) / 200000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2161 < q → q < 2179 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2179).mp (by decide +kernel))) hgap
  have hprev := lrU_325
  have hcast : (((2179:ℕ):ℝ)/(((2179:ℕ):ℝ)-1)) = (((2179:ℚ)/((2179:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((2179:ℚ)/((2179:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((2179:ℚ)/((2179:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((2179:ℚ)/((2179:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2619174205463 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((2179:ℚ)/((2179:ℚ)-1)) : ℚ) ≤ ((523926647383 : ℚ) / 200000000000) := by decide +kernel
  have hratR : ((((2619174205463 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((2179:ℚ)/((2179:ℚ)-1)) : ℚ) : ℝ) ≤ ((((523926647383 : ℚ) / 200000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_327 : Commons.NumberTheory.Mertens.logRatioSum ((2203 : ℕ) : ℝ) ≤ ((((524017453287 : ℚ) / 200000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2179 < q → q < 2203 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2203).mp (by decide +kernel))) hgap
  have hprev := lrU_326
  have hcast : (((2203:ℕ):ℝ)/(((2203:ℕ):ℝ)-1)) = (((2203:ℚ)/((2203:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((2203:ℚ)/((2203:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((2203:ℚ)/((2203:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((2203:ℚ)/((2203:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((523926647383 : ℚ) / 200000000000) + Work.RHContract.RegionI.logUpQ (((2203:ℚ)/((2203:ℚ)-1)) : ℚ) ≤ ((524017453287 : ℚ) / 200000000000) := by decide +kernel
  have hratR : ((((523926647383 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((2203:ℚ)/((2203:ℚ)-1)) : ℚ) : ℝ) ≤ ((((524017453287 : ℚ) / 200000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_328 : Commons.NumberTheory.Mertens.logRatioSum ((2207 : ℕ) : ℝ) ≤ ((((2620540472879 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2203 < q → q < 2207 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2207).mp (by decide +kernel))) hgap
  have hprev := lrU_327
  have hcast : (((2207:ℕ):ℝ)/(((2207:ℕ):ℝ)-1)) = (((2207:ℚ)/((2207:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((2207:ℚ)/((2207:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((2207:ℚ)/((2207:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((2207:ℚ)/((2207:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((524017453287 : ℚ) / 200000000000) + Work.RHContract.RegionI.logUpQ (((2207:ℚ)/((2207:ℚ)-1)) : ℚ) ≤ ((2620540472879 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((524017453287 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((2207:ℚ)/((2207:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2620540472879 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_329 : Commons.NumberTheory.Mertens.logRatioSum ((2213 : ℕ) : ℝ) ≤ ((((163812028143 : ℚ) / 62500000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2207 < q → q < 2213 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2213).mp (by decide +kernel))) hgap
  have hprev := lrU_328
  have hcast : (((2213:ℕ):ℝ)/(((2213:ℕ):ℝ)-1)) = (((2213:ℚ)/((2213:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((2213:ℚ)/((2213:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((2213:ℚ)/((2213:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((2213:ℚ)/((2213:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2620540472879 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((2213:ℚ)/((2213:ℚ)-1)) : ℚ) ≤ ((163812028143 : ℚ) / 62500000000) := by decide +kernel
  have hratR : ((((2620540472879 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((2213:ℚ)/((2213:ℚ)-1)) : ℚ) : ℝ) ≤ ((((163812028143 : ℚ) / 62500000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_330 : Commons.NumberTheory.Mertens.logRatioSum ((2221 : ℕ) : ℝ) ≤ ((((2621442799317 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2213 < q → q < 2221 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2221).mp (by decide +kernel))) hgap
  have hprev := lrU_329
  have hcast : (((2221:ℕ):ℝ)/(((2221:ℕ):ℝ)-1)) = (((2221:ℚ)/((2221:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((2221:ℚ)/((2221:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((2221:ℚ)/((2221:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((2221:ℚ)/((2221:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((163812028143 : ℚ) / 62500000000) + Work.RHContract.RegionI.logUpQ (((2221:ℚ)/((2221:ℚ)-1)) : ℚ) ≤ ((2621442799317 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((163812028143 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((2221:ℚ)/((2221:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2621442799317 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_331 : Commons.NumberTheory.Mertens.logRatioSum ((2237 : ℕ) : ℝ) ≤ ((((2621889926533 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2221 < q → q < 2237 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2237).mp (by decide +kernel))) hgap
  have hprev := lrU_330
  have hcast : (((2237:ℕ):ℝ)/(((2237:ℕ):ℝ)-1)) = (((2237:ℚ)/((2237:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((2237:ℚ)/((2237:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((2237:ℚ)/((2237:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((2237:ℚ)/((2237:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2621442799317 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((2237:ℚ)/((2237:ℚ)-1)) : ℚ) ≤ ((2621889926533 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2621442799317 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((2237:ℚ)/((2237:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2621889926533 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_332 : Commons.NumberTheory.Mertens.logRatioSum ((2239 : ℕ) : ℝ) ≤ ((((131116832713 : ℚ) / 50000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2237 < q → q < 2239 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2239).mp (by decide +kernel))) hgap
  have hprev := lrU_331
  have hcast : (((2239:ℕ):ℝ)/(((2239:ℕ):ℝ)-1)) = (((2239:ℚ)/((2239:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((2239:ℚ)/((2239:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((2239:ℚ)/((2239:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((2239:ℚ)/((2239:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2621889926533 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((2239:ℚ)/((2239:ℚ)-1)) : ℚ) ≤ ((131116832713 : ℚ) / 50000000000) := by decide +kernel
  have hratR : ((((2621889926533 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((2239:ℚ)/((2239:ℚ)-1)) : ℚ) : ℝ) ≤ ((((131116832713 : ℚ) / 50000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_333 : Commons.NumberTheory.Mertens.logRatioSum ((2243 : ℕ) : ℝ) ≤ ((((2622782585149 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2239 < q → q < 2243 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2243).mp (by decide +kernel))) hgap
  have hprev := lrU_332
  have hcast : (((2243:ℕ):ℝ)/(((2243:ℕ):ℝ)-1)) = (((2243:ℚ)/((2243:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((2243:ℚ)/((2243:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((2243:ℚ)/((2243:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((2243:ℚ)/((2243:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((131116832713 : ℚ) / 50000000000) + Work.RHContract.RegionI.logUpQ (((2243:ℚ)/((2243:ℚ)-1)) : ℚ) ≤ ((2622782585149 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((131116832713 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((2243:ℚ)/((2243:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2622782585149 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_334 : Commons.NumberTheory.Mertens.logRatioSum ((2251 : ℕ) : ℝ) ≤ ((((1311613465429 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2243 < q → q < 2251 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2251).mp (by decide +kernel))) hgap
  have hprev := lrU_333
  have hcast : (((2251:ℕ):ℝ)/(((2251:ℕ):ℝ)-1)) = (((2251:ℚ)/((2251:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((2251:ℚ)/((2251:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((2251:ℚ)/((2251:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((2251:ℚ)/((2251:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2622782585149 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((2251:ℚ)/((2251:ℚ)-1)) : ℚ) ≤ ((1311613465429 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((2622782585149 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((2251:ℚ)/((2251:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1311613465429 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_335 : Commons.NumberTheory.Mertens.logRatioSum ((2267 : ℕ) : ℝ) ≤ ((((1311834069889 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2251 < q → q < 2267 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2267).mp (by decide +kernel))) hgap
  have hprev := lrU_334
  have hcast : (((2267:ℕ):ℝ)/(((2267:ℕ):ℝ)-1)) = (((2267:ℚ)/((2267:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((2267:ℚ)/((2267:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((2267:ℚ)/((2267:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((2267:ℚ)/((2267:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1311613465429 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((2267:ℚ)/((2267:ℚ)-1)) : ℚ) ≤ ((1311834069889 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((1311613465429 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((2267:ℚ)/((2267:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1311834069889 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_336 : Commons.NumberTheory.Mertens.logRatioSum ((2269 : ℕ) : ℝ) ≤ ((((2624108959711 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2267 < q → q < 2269 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2269).mp (by decide +kernel))) hgap
  have hprev := lrU_335
  have hcast : (((2269:ℕ):ℝ)/(((2269:ℕ):ℝ)-1)) = (((2269:ℚ)/((2269:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((2269:ℚ)/((2269:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((2269:ℚ)/((2269:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((2269:ℚ)/((2269:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1311834069889 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((2269:ℚ)/((2269:ℚ)-1)) : ℚ) ≤ ((2624108959711 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((1311834069889 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((2269:ℚ)/((2269:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2624108959711 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_337 : Commons.NumberTheory.Mertens.logRatioSum ((2273 : ℕ) : ℝ) ≤ ((((2624549003723 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2269 < q → q < 2273 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2273).mp (by decide +kernel))) hgap
  have hprev := lrU_336
  have hcast : (((2273:ℕ):ℝ)/(((2273:ℕ):ℝ)-1)) = (((2273:ℚ)/((2273:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((2273:ℚ)/((2273:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((2273:ℚ)/((2273:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((2273:ℚ)/((2273:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2624108959711 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((2273:ℚ)/((2273:ℚ)-1)) : ℚ) ≤ ((2624549003723 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2624108959711 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((2273:ℚ)/((2273:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2624549003723 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_338 : Commons.NumberTheory.Mertens.logRatioSum ((2281 : ℕ) : ℝ) ≤ ((((2624987504059 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2273 < q → q < 2281 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2281).mp (by decide +kernel))) hgap
  have hprev := lrU_337
  have hcast : (((2281:ℕ):ℝ)/(((2281:ℕ):ℝ)-1)) = (((2281:ℚ)/((2281:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((2281:ℚ)/((2281:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((2281:ℚ)/((2281:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((2281:ℚ)/((2281:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2624549003723 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((2281:ℚ)/((2281:ℚ)-1)) : ℚ) ≤ ((2624987504059 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2624549003723 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((2281:ℚ)/((2281:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2624987504059 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_339 : Commons.NumberTheory.Mertens.logRatioSum ((2287 : ℕ) : ℝ) ≤ ((((82044526679 : ℚ) / 31250000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2281 < q → q < 2287 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2287).mp (by decide +kernel))) hgap
  have hprev := lrU_338
  have hcast : (((2287:ℕ):ℝ)/(((2287:ℕ):ℝ)-1)) = (((2287:ℚ)/((2287:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((2287:ℚ)/((2287:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((2287:ℚ)/((2287:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((2287:ℚ)/((2287:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2624987504059 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((2287:ℚ)/((2287:ℚ)-1)) : ℚ) ≤ ((82044526679 : ℚ) / 31250000000) := by decide +kernel
  have hratR : ((((2624987504059 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((2287:ℚ)/((2287:ℚ)-1)) : ℚ) : ℝ) ≤ ((((82044526679 : ℚ) / 31250000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_340 : Commons.NumberTheory.Mertens.logRatioSum ((2293 : ℕ) : ℝ) ≤ ((((41029079043 : ℚ) / 15625000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2287 < q → q < 2293 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2293).mp (by decide +kernel))) hgap
  have hprev := lrU_339
  have hcast : (((2293:ℕ):ℝ)/(((2293:ℕ):ℝ)-1)) = (((2293:ℚ)/((2293:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((2293:ℚ)/((2293:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((2293:ℚ)/((2293:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((2293:ℚ)/((2293:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((82044526679 : ℚ) / 31250000000) + Work.RHContract.RegionI.logUpQ (((2293:ℚ)/((2293:ℚ)-1)) : ℚ) ≤ ((41029079043 : ℚ) / 15625000000) := by decide +kernel
  have hratR : ((((82044526679 : ℚ) / 31250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((2293:ℚ)/((2293:ℚ)-1)) : ℚ) : ℝ) ≤ ((((41029079043 : ℚ) / 15625000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_341 : Commons.NumberTheory.Mertens.logRatioSum ((2297 : ℕ) : ℝ) ≤ ((((1313148252001 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2293 < q → q < 2297 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2297).mp (by decide +kernel))) hgap
  have hprev := lrU_340
  have hcast : (((2297:ℕ):ℝ)/(((2297:ℕ):ℝ)-1)) = (((2297:ℚ)/((2297:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((2297:ℚ)/((2297:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((2297:ℚ)/((2297:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((2297:ℚ)/((2297:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((41029079043 : ℚ) / 15625000000) + Work.RHContract.RegionI.logUpQ (((2297:ℚ)/((2297:ℚ)-1)) : ℚ) ≤ ((1313148252001 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((41029079043 : ℚ) / 15625000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((2297:ℚ)/((2297:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1313148252001 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_342 : Commons.NumberTheory.Mertens.logRatioSum ((2309 : ℕ) : ℝ) ≤ ((((2626729685729 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2297 < q → q < 2309 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2309).mp (by decide +kernel))) hgap
  have hprev := lrU_341
  have hcast : (((2309:ℕ):ℝ)/(((2309:ℕ):ℝ)-1)) = (((2309:ℚ)/((2309:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((2309:ℚ)/((2309:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((2309:ℚ)/((2309:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((2309:ℚ)/((2309:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1313148252001 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((2309:ℚ)/((2309:ℚ)-1)) : ℚ) ≤ ((2626729685729 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((1313148252001 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((2309:ℚ)/((2309:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2626729685729 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_343 : Commons.NumberTheory.Mertens.logRatioSum ((2311 : ℕ) : ℝ) ≤ ((((328395311561 : ℚ) / 125000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2309 < q → q < 2311 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2311).mp (by decide +kernel))) hgap
  have hprev := lrU_342
  have hcast : (((2311:ℕ):ℝ)/(((2311:ℕ):ℝ)-1)) = (((2311:ℚ)/((2311:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((2311:ℚ)/((2311:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((2311:ℚ)/((2311:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((2311:ℚ)/((2311:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2626729685729 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((2311:ℚ)/((2311:ℚ)-1)) : ℚ) ≤ ((328395311561 : ℚ) / 125000000000) := by decide +kernel
  have hratR : ((((2626729685729 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((2311:ℚ)/((2311:ℚ)-1)) : ℚ) : ℝ) ≤ ((((328395311561 : ℚ) / 125000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_344 : Commons.NumberTheory.Mertens.logRatioSum ((2333 : ℕ) : ℝ) ≤ ((((32844890213 : ℚ) / 12500000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2311 < q → q < 2333 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2333).mp (by decide +kernel))) hgap
  have hprev := lrU_343
  have hcast : (((2333:ℕ):ℝ)/(((2333:ℕ):ℝ)-1)) = (((2333:ℚ)/((2333:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((2333:ℚ)/((2333:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((2333:ℚ)/((2333:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((2333:ℚ)/((2333:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((328395311561 : ℚ) / 125000000000) + Work.RHContract.RegionI.logUpQ (((2333:ℚ)/((2333:ℚ)-1)) : ℚ) ≤ ((32844890213 : ℚ) / 12500000000) := by decide +kernel
  have hratR : ((((328395311561 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((2333:ℚ)/((2333:ℚ)-1)) : ℚ) : ℝ) ≤ ((((32844890213 : ℚ) / 12500000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_345 : Commons.NumberTheory.Mertens.logRatioSum ((2339 : ℕ) : ℝ) ≤ ((((2628018841593 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2333 < q → q < 2339 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2339).mp (by decide +kernel))) hgap
  have hprev := lrU_344
  have hcast : (((2339:ℕ):ℝ)/(((2339:ℕ):ℝ)-1)) = (((2339:ℚ)/((2339:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((2339:ℚ)/((2339:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((2339:ℚ)/((2339:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((2339:ℚ)/((2339:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((32844890213 : ℚ) / 12500000000) + Work.RHContract.RegionI.logUpQ (((2339:ℚ)/((2339:ℚ)-1)) : ℚ) ≤ ((2628018841593 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((32844890213 : ℚ) / 12500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((2339:ℚ)/((2339:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2628018841593 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_346 : Commons.NumberTheory.Mertens.logRatioSum ((2341 : ℕ) : ℝ) ≤ ((((2628446100733 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2339 < q → q < 2341 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2341).mp (by decide +kernel))) hgap
  have hprev := lrU_345
  have hcast : (((2341:ℕ):ℝ)/(((2341:ℕ):ℝ)-1)) = (((2341:ℚ)/((2341:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((2341:ℚ)/((2341:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((2341:ℚ)/((2341:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((2341:ℚ)/((2341:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2628018841593 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((2341:ℚ)/((2341:ℚ)-1)) : ℚ) ≤ ((2628446100733 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2628018841593 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((2341:ℚ)/((2341:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2628446100733 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_347 : Commons.NumberTheory.Mertens.logRatioSum ((2347 : ℕ) : ℝ) ≤ ((((2628872267371 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2341 < q → q < 2347 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2347).mp (by decide +kernel))) hgap
  have hprev := lrU_346
  have hcast : (((2347:ℕ):ℝ)/(((2347:ℕ):ℝ)-1)) = (((2347:ℚ)/((2347:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((2347:ℚ)/((2347:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((2347:ℚ)/((2347:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((2347:ℚ)/((2347:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2628446100733 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((2347:ℚ)/((2347:ℚ)-1)) : ℚ) ≤ ((2628872267371 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2628446100733 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((2347:ℚ)/((2347:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2628872267371 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_348 : Commons.NumberTheory.Mertens.logRatioSum ((2351 : ℕ) : ℝ) ≤ ((((2629297708773 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2347 < q → q < 2351 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2351).mp (by decide +kernel))) hgap
  have hprev := lrU_347
  have hcast : (((2351:ℕ):ℝ)/(((2351:ℕ):ℝ)-1)) = (((2351:ℚ)/((2351:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((2351:ℚ)/((2351:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((2351:ℚ)/((2351:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((2351:ℚ)/((2351:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2628872267371 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((2351:ℚ)/((2351:ℚ)-1)) : ℚ) ≤ ((2629297708773 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2628872267371 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((2351:ℚ)/((2351:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2629297708773 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_349 : Commons.NumberTheory.Mertens.logRatioSum ((2357 : ℕ) : ℝ) ≤ ((((1314861033469 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2351 < q → q < 2357 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2357).mp (by decide +kernel))) hgap
  have hprev := lrU_348
  have hcast : (((2357:ℕ):ℝ)/(((2357:ℕ):ℝ)-1)) = (((2357:ℚ)/((2357:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((2357:ℚ)/((2357:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((2357:ℚ)/((2357:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((2357:ℚ)/((2357:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2629297708773 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((2357:ℚ)/((2357:ℚ)-1)) : ℚ) ≤ ((1314861033469 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((2629297708773 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((2357:ℚ)/((2357:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1314861033469 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_350 : Commons.NumberTheory.Mertens.logRatioSum ((2371 : ℕ) : ℝ) ≤ ((((21041151351 : ℚ) / 8000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 2357 < q → q < 2371 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2371).mp (by decide +kernel))) hgap
  have hprev := lrU_349
  have hcast : (((2371:ℕ):ℝ)/(((2371:ℕ):ℝ)-1)) = (((2371:ℚ)/((2371:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((2371:ℚ)/((2371:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((2371:ℚ)/((2371:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((2371:ℚ)/((2371:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1314861033469 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((2371:ℚ)/((2371:ℚ)-1)) : ℚ) ≤ ((21041151351 : ℚ) / 8000000000) := by decide +kernel
  have hratR : ((((1314861033469 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((2371:ℚ)/((2371:ℚ)-1)) : ℚ) : ℝ) ≤ ((((21041151351 : ℚ) / 8000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR

end

end Work.RHContract.RegionI
