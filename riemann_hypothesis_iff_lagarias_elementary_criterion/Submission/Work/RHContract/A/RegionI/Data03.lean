import Mathlib
import Submission.Work.RHContract.A.RegionI.Data02

open scoped BigOperators

namespace Work.RHContract.RegionI

noncomputable section

lemma thV_1800 : ((((15297423754361549 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15413 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15401 < q → q < 15413 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15413).mp (by decide +kernel))) hgap
  have hprev := thV_1799
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15413:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((15297423754361549 : ℚ) / 1000000000000) ≤ ((7643890393888391 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (15413:ℚ) := by decide +kernel
  have hratR : ((((15297423754361549 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((7643890393888391 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15413:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1801 : ((((15307067628858181 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15427 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15413 < q → q < 15427 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15427).mp (by decide +kernel))) hgap
  have hprev := thV_1800
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15427:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((15307067628858181 : ℚ) / 1000000000000) ≤ ((15297423754361549 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (15427:ℚ) := by decide +kernel
  have hratR : ((((15307067628858181 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((15297423754361549 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15427:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1802 : ((((15316712280909443 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15439 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15427 < q → q < 15439 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15439).mp (by decide +kernel))) hgap
  have hprev := thV_1801
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15439:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((15316712280909443 : ℚ) / 1000000000000) ≤ ((15307067628858181 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (15439:ℚ) := by decide +kernel
  have hratR : ((((15316712280909443 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((15307067628858181 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15439:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1803 : ((((7663178596005643 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15443 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15439 < q → q < 15443 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15443).mp (by decide +kernel))) hgap
  have hprev := thV_1802
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15443:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7663178596005643 : ℚ) / 500000000000) ≤ ((15316712280909443 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (15443:ℚ) := by decide +kernel
  have hratR : ((((7663178596005643 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((15316712280909443 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15443:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1804 : ((((15336002621013057 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15451 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15443 < q → q < 15451 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15451).mp (by decide +kernel))) hgap
  have hprev := thV_1803
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15451:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((15336002621013057 : ℚ) / 1000000000000) ≤ ((7663178596005643 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (15451:ℚ) := by decide +kernel
  have hratR : ((((15336002621013057 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((7663178596005643 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15451:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1805 : ((((767282434850639 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15461 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15451 < q → q < 15461 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15461).mp (by decide +kernel))) hgap
  have hprev := thV_1804
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15461:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((767282434850639 : ℚ) / 50000000000) ≤ ((15336002621013057 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (15461:ℚ) := by decide +kernel
  have hratR : ((((767282434850639 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((15336002621013057 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15461:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1806 : ((((7677647580505219 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15467 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15461 < q → q < 15467 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15467).mp (by decide +kernel))) hgap
  have hprev := thV_1805
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15467:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7677647580505219 : ℚ) / 500000000000) ≤ ((767282434850639 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (15467:ℚ) := by decide +kernel
  have hratR : ((((7677647580505219 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((767282434850639 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15467:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1807 : ((((3841235503213887 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15473 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15467 < q → q < 15473 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15473).mp (by decide +kernel))) hgap
  have hprev := thV_1806
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15473:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3841235503213887 : ℚ) / 250000000000) ≤ ((7677647580505219 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (15473:ℚ) := by decide +kernel
  have hratR : ((((3841235503213887 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((7677647580505219 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15473:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1808 : ((((3074918031288033 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15493 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15473 < q → q < 15493 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15493).mp (by decide +kernel))) hgap
  have hprev := thV_1807
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15493:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3074918031288033 : ℚ) / 200000000000) ≤ ((3841235503213887 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (15493:ℚ) := by decide +kernel
  have hratR : ((((3074918031288033 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((3841235503213887 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15493:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1809 : ((((15384238558172573 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15497 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15493 < q → q < 15497 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15497).mp (by decide +kernel))) hgap
  have hprev := thV_1808
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15497:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((15384238558172573 : ℚ) / 1000000000000) ≤ ((3074918031288033 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (15497:ℚ) := by decide +kernel
  have hratR : ((((15384238558172573 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3074918031288033 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15497:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1810 : ((((7696943931448909 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15511 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15497 < q → q < 15511 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15511).mp (by decide +kernel))) hgap
  have hprev := thV_1809
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15511:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7696943931448909 : ℚ) / 500000000000) ≤ ((15384238558172573 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (15511:ℚ) := by decide +kernel
  have hratR : ((((7696943931448909 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((15384238558172573 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15511:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1811 : ((((15403538198617419 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15527 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15511 < q → q < 15527 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15527).mp (by decide +kernel))) hgap
  have hprev := thV_1810
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15527:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((15403538198617419 : ℚ) / 1000000000000) ≤ ((7696943931448909 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (15527:ℚ) := by decide +kernel
  have hratR : ((((15403538198617419 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((7696943931448909 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15527:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1812 : ((((3082637887117191 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15541 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15527 < q → q < 15541 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15541).mp (by decide +kernel))) hgap
  have hprev := thV_1811
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15541:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3082637887117191 : ℚ) / 200000000000) ≤ ((15403538198617419 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (15541:ℚ) := by decide +kernel
  have hratR : ((((3082637887117191 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((15403538198617419 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15541:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1813 : ((((15422841315806797 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15551 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15541 < q → q < 15551 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15551).mp (by decide +kernel))) hgap
  have hprev := thV_1812
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15551:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((15422841315806797 : ℚ) / 1000000000000) ≤ ((3082637887117191 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (15551:ℚ) := by decide +kernel
  have hratR : ((((15422841315806797 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3082637887117191 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15551:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1814 : ((((3858123427582933 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15559 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15551 < q → q < 15559 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15559).mp (by decide +kernel))) hgap
  have hprev := thV_1813
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15559:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3858123427582933 : ℚ) / 250000000000) ≤ ((15422841315806797 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (15559:ℚ) := by decide +kernel
  have hratR : ((((3858123427582933 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((15422841315806797 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15559:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1815 : ((((7721073373682521 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15569 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15559 < q → q < 15569 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15569).mp (by decide +kernel))) hgap
  have hprev := thV_1814
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15569:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7721073373682521 : ℚ) / 500000000000) ≤ ((3858123427582933 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (15569:ℚ) := by decide +kernel
  have hratR : ((((7721073373682521 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((3858123427582933 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15569:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1816 : ((((386295013871597 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15581 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15569 < q → q < 15581 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15581).mp (by decide +kernel))) hgap
  have hprev := thV_1815
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15581:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((386295013871597 : ℚ) / 25000000000) ≤ ((7721073373682521 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (15581:ℚ) := by decide +kernel
  have hratR : ((((386295013871597 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((7721073373682521 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15581:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1817 : ((((7730727245357973 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15583 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15581 < q → q < 15583 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15583).mp (by decide +kernel))) hgap
  have hprev := thV_1816
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15583:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7730727245357973 : ℚ) / 500000000000) ≤ ((386295013871597 : ℚ) / 25000000000) + Work.RHContract.RegionI.logLowQ (15583:ℚ) := by decide +kernel
  have hratR : ((((7730727245357973 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((386295013871597 : ℚ) / 25000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15583:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1818 : ((((15471109581006313 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15601 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15583 < q → q < 15601 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15601).mp (by decide +kernel))) hgap
  have hprev := thV_1817
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15601:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((15471109581006313 : ℚ) / 1000000000000) ≤ ((7730727245357973 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (15601:ℚ) := by decide +kernel
  have hratR : ((((15471109581006313 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((7730727245357973 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15601:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1819 : ((((3870191263953369 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15607 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15601 < q → q < 15607 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15607).mp (by decide +kernel))) hgap
  have hprev := thV_1818
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15607:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3870191263953369 : ℚ) / 250000000000) ≤ ((15471109581006313 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (15607:ℚ) := by decide +kernel
  have hratR : ((((3870191263953369 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((15471109581006313 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15607:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1820 : ((((7745210649605477 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15619 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15607 < q → q < 15619 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15619).mp (by decide +kernel))) hgap
  have hprev := thV_1819
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15619:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7745210649605477 : ℚ) / 500000000000) ≤ ((3870191263953369 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (15619:ℚ) := by decide +kernel
  have hratR : ((((7745210649605477 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((3870191263953369 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15619:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1821 : ((((1937509772831177 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15629 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15619 < q → q < 15629 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15629).mp (by decide +kernel))) hgap
  have hprev := thV_1820
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15629:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1937509772831177 : ℚ) / 125000000000) ≤ ((7745210649605477 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (15629:ℚ) := by decide +kernel
  have hratR : ((((1937509772831177 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((7745210649605477 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15629:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1822 : ((((1550973583359671 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15641 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15629 < q → q < 15641 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15641).mp (by decide +kernel))) hgap
  have hprev := thV_1821
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15641:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1550973583359671 : ℚ) / 100000000000) ≤ ((1937509772831177 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (15641:ℚ) := by decide +kernel
  have hratR : ((((1550973583359671 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((1937509772831177 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15641:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1823 : ((((3879848403101223 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15643 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15641 < q → q < 15643 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15643).mp (by decide +kernel))) hgap
  have hprev := thV_1822
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15643:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3879848403101223 : ℚ) / 250000000000) ≤ ((1550973583359671 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (15643:ℚ) := by decide +kernel
  have hratR : ((((3879848403101223 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((1550973583359671 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15643:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1824 : ((((7764525823442907 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15647 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15643 < q → q < 15647 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15647).mp (by decide +kernel))) hgap
  have hprev := thV_1823
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15647:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7764525823442907 : ℚ) / 500000000000) ≤ ((3879848403101223 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (15647:ℚ) := by decide +kernel
  have hratR : ((((7764525823442907 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((3879848403101223 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15647:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1825 : ((((15538709809178597 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15649 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15647 < q → q < 15649 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15649).mp (by decide +kernel))) hgap
  have hprev := thV_1824
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15649:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((15538709809178597 : ℚ) / 1000000000000) ≤ ((7764525823442907 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (15649:ℚ) := by decide +kernel
  have hratR : ((((15538709809178597 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((7764525823442907 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15649:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1826 : ((((3887092184499921 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15661 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15649 < q → q < 15661 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15661).mp (by decide +kernel))) hgap
  have hprev := thV_1825
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15661:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3887092184499921 : ℚ) / 250000000000) ≤ ((15538709809178597 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (15661:ℚ) := by decide +kernel
  have hratR : ((((3887092184499921 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((15538709809178597 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15661:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1827 : ((((7779014024932349 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15667 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15661 < q → q < 15667 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15667).mp (by decide +kernel))) hgap
  have hprev := thV_1826
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15667:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7779014024932349 : ℚ) / 500000000000) ≤ ((3887092184499921 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (15667:ℚ) := by decide +kernel
  have hratR : ((((7779014024932349 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((3887092184499921 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15667:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1828 : ((((15567687617010841 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15671 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15667 < q → q < 15671 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15671).mp (by decide +kernel))) hgap
  have hprev := thV_1827
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15671:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((15567687617010841 : ℚ) / 1000000000000) ≤ ((7779014024932349 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (15671:ℚ) := by decide +kernel
  have hratR : ((((15567687617010841 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((7779014024932349 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15671:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1829 : ((((7788673847261911 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15679 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15671 < q → q < 15679 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15679).mp (by decide +kernel))) hgap
  have hprev := thV_1828
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15679:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7788673847261911 : ℚ) / 500000000000) ≤ ((15567687617010841 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (15679:ℚ) := by decide +kernel
  have hratR : ((((7788673847261911 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((15567687617010841 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15679:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1830 : ((((15587008027122577 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15683 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15679 < q → q < 15683 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15683).mp (by decide +kernel))) hgap
  have hprev := thV_1829
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15683:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((15587008027122577 : ℚ) / 1000000000000) ≤ ((7788673847261911 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (15683:ℚ) := by decide +kernel
  have hratR : ((((15587008027122577 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((7788673847261911 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15683:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1831 : ((((121848993448271 : ℚ) / 7812500000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15727 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15683 < q → q < 15727 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15727).mp (by decide +kernel))) hgap
  have hprev := thV_1830
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15727:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((121848993448271 : ℚ) / 7812500000) ≤ ((15587008027122577 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (15727:ℚ) := by decide +kernel
  have hratR : ((((121848993448271 : ℚ) / 7812500000) : ℚ) : ℝ) ≤ ((((15587008027122577 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15727:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1832 : ((((15606334549942131 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15731 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15727 < q → q < 15731 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15731).mp (by decide +kernel))) hgap
  have hprev := thV_1831
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15731:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((15606334549942131 : ℚ) / 1000000000000) ≤ ((121848993448271 : ℚ) / 7812500000) + Work.RHContract.RegionI.logLowQ (15731:ℚ) := by decide +kernel
  have hratR : ((((15606334549942131 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((121848993448271 : ℚ) / 7812500000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15731:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1833 : ((((975999879102187 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15733 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15731 < q → q < 15733 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15733).mp (by decide +kernel))) hgap
  have hprev := thV_1832
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15733:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((975999879102187 : ℚ) / 62500000000) ≤ ((15606334549942131 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (15733:ℚ) := by decide +kernel
  have hratR : ((((975999879102187 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((15606334549942131 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15733:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1834 : ((((15625661835538213 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15737 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15733 < q → q < 15737 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15737).mp (by decide +kernel))) hgap
  have hprev := thV_1833
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15737:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((15625661835538213 : ℚ) / 1000000000000) ≤ ((975999879102187 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (15737:ℚ) := by decide +kernel
  have hratR : ((((15625661835538213 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((975999879102187 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15737:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1835 : ((((3127065146504477 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15739 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15737 < q → q < 15739 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15739).mp (by decide +kernel))) hgap
  have hprev := thV_1834
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15739:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3127065146504477 : ℚ) / 200000000000) ≤ ((15625661835538213 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (15739:ℚ) := by decide +kernel
  have hratR : ((((3127065146504477 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((15625661835538213 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15739:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1836 : ((((782249513233459 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15749 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15739 < q → q < 15749 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15749).mp (by decide +kernel))) hgap
  have hprev := thV_1835
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15749:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((782249513233459 : ℚ) / 50000000000) ≤ ((3127065146504477 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (15749:ℚ) := by decide +kernel
  have hratR : ((((782249513233459 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((3127065146504477 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15749:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1837 : ((((122301996550617 : ℚ) / 7812500000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15761 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15749 < q → q < 15761 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15761).mp (by decide +kernel))) hgap
  have hprev := thV_1836
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15761:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((122301996550617 : ℚ) / 7812500000) ≤ ((782249513233459 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (15761:ℚ) := by decide +kernel
  have hratR : ((((122301996550617 : ℚ) / 7812500000) : ℚ) : ℝ) ≤ ((((782249513233459 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15761:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1838 : ((((7832160616451417 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15767 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15761 < q → q < 15767 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15767).mp (by decide +kernel))) hgap
  have hprev := thV_1837
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15767:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7832160616451417 : ℚ) / 500000000000) ≤ ((122301996550617 : ℚ) / 7812500000) + Work.RHContract.RegionI.logLowQ (15767:ℚ) := by decide +kernel
  have hratR : ((((7832160616451417 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((122301996550617 : ℚ) / 7812500000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15767:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1839 : ((((7836993643897971 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15773 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15767 < q → q < 15773 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15773).mp (by decide +kernel))) hgap
  have hprev := thV_1838
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15773:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7836993643897971 : ℚ) / 500000000000) ≤ ((7832160616451417 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (15773:ℚ) := by decide +kernel
  have hratR : ((((7836993643897971 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((7832160616451417 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15773:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1840 : ((((7841827114944047 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15787 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15773 < q → q < 15787 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15787).mp (by decide +kernel))) hgap
  have hprev := thV_1839
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15787:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7841827114944047 : ℚ) / 500000000000) ≤ ((7836993643897971 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (15787:ℚ) := by decide +kernel
  have hratR : ((((7841827114944047 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((7836993643897971 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15787:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1841 : ((((15693321425321181 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15791 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15787 < q → q < 15791 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15791).mp (by decide +kernel))) hgap
  have hprev := thV_1840
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15791:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((15693321425321181 : ℚ) / 1000000000000) ≤ ((7841827114944047 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (15791:ℚ) := by decide +kernel
  have hratR : ((((15693321425321181 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((7841827114944047 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15791:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1842 : ((((1570298900064537 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15797 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15791 < q → q < 15797 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15797).mp (by decide +kernel))) hgap
  have hprev := thV_1841
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15797:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1570298900064537 : ℚ) / 100000000000) ≤ ((15693321425321181 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (15797:ℚ) := by decide +kernel
  have hratR : ((((1570298900064537 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((15693321425321181 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15797:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1843 : ((((15712656955716399 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15803 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15797 < q → q < 15803 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15803).mp (by decide +kernel))) hgap
  have hprev := thV_1842
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15803:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((15712656955716399 : ℚ) / 1000000000000) ≤ ((1570298900064537 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (15803:ℚ) := by decide +kernel
  have hratR : ((((15712656955716399 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1570298900064537 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15803:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1844 : ((((3144465058078023 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15809 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15803 < q → q < 15809 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15809).mp (by decide +kernel))) hgap
  have hprev := thV_1843
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15809:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3144465058078023 : ℚ) / 200000000000) ≤ ((15712656955716399 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (15809:ℚ) := by decide +kernel
  have hratR : ((((3144465058078023 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((15712656955716399 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15809:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1845 : ((((15731994130976699 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15817 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15809 < q → q < 15817 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15817).mp (by decide +kernel))) hgap
  have hprev := thV_1844
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15817:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((15731994130976699 : ℚ) / 1000000000000) ≤ ((3144465058078023 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (15817:ℚ) := by decide +kernel
  have hratR : ((((15731994130976699 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3144465058078023 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15817:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1846 : ((((7870831675415019 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15823 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15817 < q → q < 15823 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15823).mp (by decide +kernel))) hgap
  have hprev := thV_1845
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15823:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7870831675415019 : ℚ) / 500000000000) ≤ ((15731994130976699 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (15823:ℚ) := by decide +kernel
  have hratR : ((((7870831675415019 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((15731994130976699 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15823:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1847 : ((((15751334843268157 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15859 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15823 < q → q < 15859 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15859).mp (by decide +kernel))) hgap
  have hprev := thV_1846
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15859:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((15751334843268157 : ℚ) / 1000000000000) ≤ ((7870831675415019 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (15859:ℚ) := by decide +kernel
  have hratR : ((((15751334843268157 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((7870831675415019 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15859:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1848 : ((((3152201494012971 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15877 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15859 < q → q < 15877 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15877).mp (by decide +kernel))) hgap
  have hprev := thV_1847
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15877:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3152201494012971 : ℚ) / 200000000000) ≤ ((15751334843268157 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (15877:ℚ) := by decide +kernel
  have hratR : ((((3152201494012971 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((15751334843268157 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15877:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1849 : ((((7885340174383293 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15881 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15877 < q → q < 15881 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15881).mp (by decide +kernel))) hgap
  have hprev := thV_1848
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15881:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7885340174383293 : ℚ) / 500000000000) ≤ ((3152201494012971 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (15881:ℚ) := by decide +kernel
  have hratR : ((((7885340174383293 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((3152201494012971 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15881:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1850 : ((((7890176802603463 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15887 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15881 < q → q < 15887 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15887).mp (by decide +kernel))) hgap
  have hprev := thV_1849
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15887:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7890176802603463 : ℚ) / 500000000000) ≤ ((7885340174383293 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (15887:ℚ) := by decide +kernel
  have hratR : ((((7890176802603463 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((7885340174383293 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15887:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1851 : ((((3158005397505687 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15889 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15887 < q → q < 15889 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15889).mp (by decide +kernel))) hgap
  have hprev := thV_1850
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15889:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3158005397505687 : ℚ) / 200000000000) ≤ ((7890176802603463 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (15889:ℚ) := by decide +kernel
  have hratR : ((((3158005397505687 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((7890176802603463 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15889:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1852 : ((((987481320300273 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15901 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15889 < q → q < 15901 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15901).mp (by decide +kernel))) hgap
  have hprev := thV_1851
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15901:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((987481320300273 : ℚ) / 62500000000) ≤ ((3158005397505687 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (15901:ℚ) := by decide +kernel
  have hratR : ((((987481320300273 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((3158005397505687 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15901:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1853 : ((((15809375639343887 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15907 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15901 < q → q < 15907 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15907).mp (by decide +kernel))) hgap
  have hprev := thV_1852
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15907:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((15809375639343887 : ℚ) / 1000000000000) ≤ ((987481320300273 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (15907:ℚ) := by decide +kernel
  have hratR : ((((15809375639343887 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((987481320300273 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15907:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1854 : ((((15819050531004717 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15913 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15907 < q → q < 15913 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15913).mp (by decide +kernel))) hgap
  have hprev := thV_1853
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15913:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((15819050531004717 : ℚ) / 1000000000000) ≤ ((15809375639343887 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (15913:ℚ) := by decide +kernel
  have hratR : ((((15819050531004717 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((15809375639343887 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15913:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1855 : ((((3957181449911173 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15919 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15913 < q → q < 15919 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15919).mp (by decide +kernel))) hgap
  have hprev := thV_1854
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15919:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3957181449911173 : ℚ) / 250000000000) ≤ ((15819050531004717 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (15919:ℚ) := by decide +kernel
  have hratR : ((((3957181449911173 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((15819050531004717 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15919:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1856 : ((((15838401319525169 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15923 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15919 < q → q < 15923 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15923).mp (by decide +kernel))) hgap
  have hprev := thV_1855
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15923:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((15838401319525169 : ℚ) / 1000000000000) ≤ ((3957181449911173 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (15923:ℚ) := by decide +kernel
  have hratR : ((((15838401319525169 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3957181449911173 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15923:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1857 : ((((15848077718250649 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15937 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15923 < q → q < 15937 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15937).mp (by decide +kernel))) hgap
  have hprev := thV_1856
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15937:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((15848077718250649 : ℚ) / 1000000000000) ≤ ((15838401319525169 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (15937:ℚ) := by decide +kernel
  have hratR : ((((15848077718250649 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((15838401319525169 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15937:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1858 : ((((3964438874114917 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15959 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15937 < q → q < 15959 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15959).mp (by decide +kernel))) hgap
  have hprev := thV_1857
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15959:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3964438874114917 : ℚ) / 250000000000) ≤ ((15848077718250649 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (15959:ℚ) := by decide +kernel
  have hratR : ((((3964438874114917 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((15848077718250649 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15959:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1859 : ((((3173486805262589 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15971 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15959 < q → q < 15971 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15971).mp (by decide +kernel))) hgap
  have hprev := thV_1858
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15971:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3173486805262589 : ℚ) / 200000000000) ≤ ((3964438874114917 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (15971:ℚ) := by decide +kernel
  have hratR : ((((3173486805262589 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((3964438874114917 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15971:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1860 : ((((3175422536277071 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15973 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15971 < q → q < 15973 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15973).mp (by decide +kernel))) hgap
  have hprev := thV_1859
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15973:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3175422536277071 : ℚ) / 200000000000) ≤ ((3173486805262589 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (15973:ℚ) := by decide +kernel
  have hratR : ((((3175422536277071 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((3173486805262589 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15973:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1861 : ((((3177358492544987 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15991 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15973 < q → q < 15991 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15991).mp (by decide +kernel))) hgap
  have hprev := thV_1860
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15991:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3177358492544987 : ℚ) / 200000000000) ≤ ((3175422536277071 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (15991:ℚ) := by decide +kernel
  have hratR : ((((3177358492544987 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((3175422536277071 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15991:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1862 : ((((1987059108652603 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16001 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15991 < q → q < 16001 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16001).mp (by decide +kernel))) hgap
  have hprev := thV_1861
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16001:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1987059108652603 : ℚ) / 125000000000) ≤ ((3177358492544987 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (16001:ℚ) := by decide +kernel
  have hratR : ((((1987059108652603 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((3177358492544987 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16001:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1863 : ((((15906153650622991 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16007 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16001 < q → q < 16007 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16007).mp (by decide +kernel))) hgap
  have hprev := thV_1862
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16007:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((15906153650622991 : ℚ) / 1000000000000) ≤ ((1987059108652603 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (16007:ℚ) := by decide +kernel
  have hratR : ((((15906153650622991 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1987059108652603 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16007:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1864 : ((((9947397534373 : ℚ) / 625000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16033 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16007 < q → q < 16033 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16033).mp (by decide +kernel))) hgap
  have hprev := thV_1863
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16033:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9947397534373 : ℚ) / 625000000) ≤ ((15906153650622991 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (16033:ℚ) := by decide +kernel
  have hratR : ((((9947397534373 : ℚ) / 625000000) : ℚ) : ℝ) ≤ ((((15906153650622991 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16033:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1865 : ((((1592551995516397 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16057 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16033 < q → q < 16057 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16057).mp (by decide +kernel))) hgap
  have hprev := thV_1864
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16057:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1592551995516397 : ℚ) / 100000000000) ≤ ((9947397534373 : ℚ) / 625000000) + Work.RHContract.RegionI.logLowQ (16057:ℚ) := by decide +kernel
  have hratR : ((((1592551995516397 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((9947397534373 : ℚ) / 625000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16057:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1866 : ((((15935204104412653 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16061 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16057 < q → q < 16061 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16061).mp (by decide +kernel))) hgap
  have hprev := thV_1865
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16061:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((15935204104412653 : ℚ) / 1000000000000) ≤ ((1592551995516397 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (16061:ℚ) := by decide +kernel
  have hratR : ((((15935204104412653 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1592551995516397 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16061:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1867 : ((((15944888378178831 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16063 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16061 < q → q < 16063 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16063).mp (by decide +kernel))) hgap
  have hprev := thV_1866
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16063:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((15944888378178831 : ℚ) / 1000000000000) ≤ ((15935204104412653 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (16063:ℚ) := by decide +kernel
  have hratR : ((((15944888378178831 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((15935204104412653 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16063:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1868 : ((((3190914580186699 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16067 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16063 < q → q < 16067 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16067).mp (by decide +kernel))) hgap
  have hprev := thV_1867
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16067:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3190914580186699 : ℚ) / 200000000000) ≤ ((15944888378178831 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (16067:ℚ) := by decide +kernel
  have hratR : ((((3190914580186699 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((15944888378178831 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16067:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1869 : ((((15964257548159157 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16069 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16067 < q → q < 16069 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16069).mp (by decide +kernel))) hgap
  have hprev := thV_1868
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16069:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((15964257548159157 : ℚ) / 1000000000000) ≤ ((3190914580186699 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (16069:ℚ) := by decide +kernel
  have hratR : ((((15964257548159157 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3190914580186699 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16069:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1870 : ((((7986971222140173 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16073 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16069 < q → q < 16073 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16073).mp (by decide +kernel))) hgap
  have hprev := thV_1869
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16073:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7986971222140173 : ℚ) / 500000000000) ≤ ((15964257548159157 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (16073:ℚ) := by decide +kernel
  have hratR : ((((7986971222140173 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((15964257548159157 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16073:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1871 : ((((15983628211048357 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16087 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16073 < q → q < 16087 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16087).mp (by decide +kernel))) hgap
  have hprev := thV_1870
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16087:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((15983628211048357 : ℚ) / 1000000000000) ≤ ((7986971222140173 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (16087:ℚ) := by decide +kernel
  have hratR : ((((15983628211048357 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((7986971222140173 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16087:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1872 : ((((3998328556608359 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16091 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16087 < q → q < 16091 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16091).mp (by decide +kernel))) hgap
  have hprev := thV_1871
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16091:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3998328556608359 : ℚ) / 250000000000) ≤ ((15983628211048357 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (16091:ℚ) := by decide +kernel
  have hratR : ((((3998328556608359 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((15983628211048357 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16091:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1873 : ((((8001500307314131 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16097 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16091 < q → q < 16097 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16097).mp (by decide +kernel))) hgap
  have hprev := thV_1872
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16097:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8001500307314131 : ℚ) / 500000000000) ≤ ((3998328556608359 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (16097:ℚ) := by decide +kernel
  have hratR : ((((8001500307314131 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((3998328556608359 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16097:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1874 : ((((160126873754939 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16103 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16097 < q → q < 16103 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16103).mp (by decide +kernel))) hgap
  have hprev := thV_1873
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16103:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((160126873754939 : ℚ) / 10000000000) ≤ ((8001500307314131 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (16103:ℚ) := by decide +kernel
  have hratR : ((((160126873754939 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ ((((8001500307314131 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16103:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1875 : ((((16022374633038011 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16111 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16103 < q → q < 16111 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16111).mp (by decide +kernel))) hgap
  have hprev := thV_1874
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16111:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((16022374633038011 : ℚ) / 1000000000000) ≤ ((160126873754939 : ℚ) / 10000000000) + Work.RHContract.RegionI.logLowQ (16111:ℚ) := by decide +kernel
  have hratR : ((((16022374633038011 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((160126873754939 : ℚ) / 10000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16111:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1876 : ((((4008015720799903 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16127 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16111 < q → q < 16127 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16127).mp (by decide +kernel))) hgap
  have hprev := thV_1875
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16127:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4008015720799903 : ℚ) / 250000000000) ≤ ((16022374633038011 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (16127:ℚ) := by decide +kernel
  have hratR : ((((4008015720799903 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((16022374633038011 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16127:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1877 : ((((4010437969294567 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16139 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16127 < q → q < 16139 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16139).mp (by decide +kernel))) hgap
  have hprev := thV_1876
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16139:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4010437969294567 : ℚ) / 250000000000) ≤ ((4008015720799903 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (16139:ℚ) := by decide +kernel
  have hratR : ((((4010437969294567 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((4008015720799903 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16139:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1878 : ((((16051440995072661 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16141 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16139 < q → q < 16141 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16141).mp (by decide +kernel))) hgap
  have hprev := thV_1877
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16141:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((16051440995072661 : ℚ) / 1000000000000) ≤ ((4010437969294567 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (16141:ℚ) := by decide +kernel
  have hratR : ((((16051440995072661 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4010437969294567 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16141:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1879 : ((((8030566355828399 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16183 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16141 < q → q < 16183 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16183).mp (by decide +kernel))) hgap
  have hprev := thV_1878
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16183:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8030566355828399 : ℚ) / 500000000000) ≤ ((16051440995072661 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (16183:ℚ) := by decide +kernel
  have hratR : ((((8030566355828399 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((16051440995072661 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16183:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1880 : ((((2008853084422919 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16187 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16183 < q → q < 16187 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16187).mp (by decide +kernel))) hgap
  have hprev := thV_1879
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16187:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2008853084422919 : ℚ) / 125000000000) ≤ ((8030566355828399 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (16187:ℚ) := by decide +kernel
  have hratR : ((((2008853084422919 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((8030566355828399 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16187:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1881 : ((((8040258381329107 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16189 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16187 < q → q < 16189 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16189).mp (by decide +kernel))) hgap
  have hprev := thV_1880
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16189:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8040258381329107 : ℚ) / 500000000000) ≤ ((2008853084422919 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (16189:ℚ) := by decide +kernel
  have hratR : ((((8040258381329107 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((2008853084422919 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16189:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1882 : ((((4022552274245977 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16193 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16189 < q → q < 16193 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16193).mp (by decide +kernel))) hgap
  have hprev := thV_1881
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16193:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4022552274245977 : ℚ) / 250000000000) ≤ ((8040258381329107 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (16193:ℚ) := by decide +kernel
  have hratR : ((((4022552274245977 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((8040258381329107 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16193:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1883 : ((((2012487864041781 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16217 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16193 < q → q < 16217 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16217).mp (by decide +kernel))) hgap
  have hprev := thV_1882
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16217:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2012487864041781 : ℚ) / 125000000000) ≤ ((4022552274245977 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (16217:ℚ) := by decide +kernel
  have hratR : ((((2012487864041781 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((4022552274245977 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16217:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1884 : ((((16109597097598279 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16223 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16217 < q → q < 16223 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16223).mp (by decide +kernel))) hgap
  have hprev := thV_1883
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16223:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((16109597097598279 : ℚ) / 1000000000000) ≤ ((2012487864041781 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (16223:ℚ) := by decide +kernel
  have hratR : ((((16109597097598279 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2012487864041781 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16223:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1885 : ((((3223858330527843 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16229 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16223 < q → q < 16229 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16229).mp (by decide +kernel))) hgap
  have hprev := thV_1884
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16229:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3223858330527843 : ℚ) / 200000000000) ≤ ((16109597097598279 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (16229:ℚ) := by decide +kernel
  have hratR : ((((3223858330527843 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((16109597097598279 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16229:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1886 : ((((806449316545437 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16231 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16229 < q → q < 16231 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16231).mp (by decide +kernel))) hgap
  have hprev := thV_1885
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16231:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((806449316545437 : ℚ) / 50000000000) ≤ ((3223858330527843 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (16231:ℚ) := by decide +kernel
  have hratR : ((((806449316545437 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((3223858330527843 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16231:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1887 : ((((16138682117552763 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16249 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16231 < q → q < 16249 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16249).mp (by decide +kernel))) hgap
  have hprev := thV_1886
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16249:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((16138682117552763 : ℚ) / 1000000000000) ≤ ((806449316545437 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (16249:ℚ) := by decide +kernel
  have hratR : ((((16138682117552763 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((806449316545437 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16249:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1888 : ((((8074189075167743 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16253 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16249 < q → q < 16253 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16253).mp (by decide +kernel))) hgap
  have hprev := thV_1887
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16253:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8074189075167743 : ℚ) / 500000000000) ≤ ((16138682117552763 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (16253:ℚ) := by decide +kernel
  have hratR : ((((8074189075167743 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((16138682117552763 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16253:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1889 : ((((16158075044126873 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16267 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16253 < q → q < 16267 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16267).mp (by decide +kernel))) hgap
  have hprev := thV_1888
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16267:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((16158075044126873 : ℚ) / 1000000000000) ≤ ((8074189075167743 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (16267:ℚ) := by decide +kernel
  have hratR : ((((16158075044126873 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((8074189075167743 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16267:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1890 : ((((8083886153347577 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16273 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16267 < q → q < 16273 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16273).mp (by decide +kernel))) hgap
  have hprev := thV_1889
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16273:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8083886153347577 : ℚ) / 500000000000) ≤ ((16158075044126873 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (16273:ℚ) := by decide +kernel
  have hratR : ((((8083886153347577 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((16158075044126873 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16273:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1891 : ((((808873564421319 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16301 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16273 < q → q < 16301 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16301).mp (by decide +kernel))) hgap
  have hprev := thV_1890
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16301:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((808873564421319 : ℚ) / 50000000000) ≤ ((8083886153347577 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (16301:ℚ) := by decide +kernel
  have hratR : ((((808873564421319 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((8083886153347577 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16301:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1892 : ((((16187171373775131 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16319 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16301 < q → q < 16319 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16319).mp (by decide +kernel))) hgap
  have hprev := thV_1891
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16319:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((16187171373775131 : ℚ) / 1000000000000) ≤ ((808873564421319 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (16319:ℚ) := by decide +kernel
  have hratR : ((((16187171373775131 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((808873564421319 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16319:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1893 : ((((4049218079162951 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16333 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16319 < q → q < 16333 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16333).mp (by decide +kernel))) hgap
  have hprev := thV_1892
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16333:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4049218079162951 : ℚ) / 250000000000) ≤ ((16187171373775131 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (16333:ℚ) := by decide +kernel
  have hratR : ((((4049218079162951 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((16187171373775131 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16333:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1894 : ((((3241314725363091 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16339 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16333 < q → q < 16339 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16339).mp (by decide +kernel))) hgap
  have hprev := thV_1893
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16339:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3241314725363091 : ℚ) / 200000000000) ≤ ((4049218079162951 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (16339:ℚ) := by decide +kernel
  have hratR : ((((3241314725363091 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((4049218079162951 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16339:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1895 : ((((16216275548824451 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16349 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16339 < q → q < 16349 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16349).mp (by decide +kernel))) hgap
  have hprev := thV_1894
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16349:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((16216275548824451 : ℚ) / 1000000000000) ≤ ((3241314725363091 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (16349:ℚ) := by decide +kernel
  have hratR : ((((16216275548824451 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3241314725363091 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16349:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1896 : ((((8112989102277027 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16361 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16349 < q → q < 16361 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16361).mp (by decide +kernel))) hgap
  have hprev := thV_1895
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16361:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8112989102277027 : ℚ) / 500000000000) ≤ ((16216275548824451 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (16361:ℚ) := by decide +kernel
  have hratR : ((((8112989102277027 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((16216275548824451 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16361:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1897 : ((((16235680982518103 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16363 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16361 < q → q < 16363 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16363).mp (by decide +kernel))) hgap
  have hprev := thV_1896
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16363:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((16235680982518103 : ℚ) / 1000000000000) ≤ ((8112989102277027 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (16363:ℚ) := by decide +kernel
  have hratR : ((((16235680982518103 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((8112989102277027 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16363:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1898 : ((((4061346031773967 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16369 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16363 < q → q < 16369 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16369).mp (by decide +kernel))) hgap
  have hprev := thV_1897
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16369:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4061346031773967 : ℚ) / 250000000000) ≤ ((16235680982518103 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (16369:ℚ) := by decide +kernel
  have hratR : ((((4061346031773967 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((16235680982518103 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16369:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1899 : ((((16255088004498093 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16381 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16369 < q → q < 16381 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16381).mp (by decide +kernel))) hgap
  have hprev := thV_1898
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16381:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((16255088004498093 : ℚ) / 1000000000000) ≤ ((4061346031773967 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (16381:ℚ) := by decide +kernel
  have hratR : ((((16255088004498093 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4061346031773967 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16381:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1900 : ((((16264793711615133 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16411 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16381 < q → q < 16411 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16411).mp (by decide +kernel))) hgap
  have hprev := thV_1899
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16411:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((16264793711615133 : ℚ) / 1000000000000) ≤ ((16255088004498093 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (16411:ℚ) := by decide +kernel
  have hratR : ((((16264793711615133 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((16255088004498093 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16411:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1901 : ((((4068624946068447 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16417 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16411 < q → q < 16417 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16417).mp (by decide +kernel))) hgap
  have hprev := thV_1900
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16417:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4068624946068447 : ℚ) / 250000000000) ≤ ((16264793711615133 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (16417:ℚ) := by decide +kernel
  have hratR : ((((4068624946068447 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((16264793711615133 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16417:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1902 : ((((50888144064227 : ℚ) / 3125000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16421 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16417 < q → q < 16421 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16421).mp (by decide +kernel))) hgap
  have hprev := thV_1901
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16421:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((50888144064227 : ℚ) / 3125000000) ≤ ((4068624946068447 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (16421:ℚ) := by decide +kernel
  have hratR : ((((50888144064227 : ℚ) / 3125000000) : ℚ) : ℝ) ≤ ((((4068624946068447 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16421:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1903 : ((((16293912782150541 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16427 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16421 < q → q < 16427 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16427).mp (by decide +kernel))) hgap
  have hprev := thV_1902
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16427:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((16293912782150541 : ℚ) / 1000000000000) ≤ ((50888144064227 : ℚ) / 3125000000) + Work.RHContract.RegionI.logLowQ (16427:ℚ) := by decide +kernel
  have hratR : ((((16293912782150541 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((50888144064227 : ℚ) / 3125000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16427:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1904 : ((((16303619828934083 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16433 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16427 < q → q < 16433 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16433).mp (by decide +kernel))) hgap
  have hprev := thV_1903
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16433:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((16303619828934083 : ℚ) / 1000000000000) ≤ ((16293912782150541 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (16433:ℚ) := by decide +kernel
  have hratR : ((((16303619828934083 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((16293912782150541 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16433:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1905 : ((((3262665545459837 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16447 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16433 < q → q < 16447 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16447).mp (by decide +kernel))) hgap
  have hprev := thV_1904
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16447:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3262665545459837 : ℚ) / 200000000000) ≤ ((16303619828934083 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (16447:ℚ) := by decide +kernel
  have hratR : ((((3262665545459837 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((16303619828934083 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16447:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1906 : ((((3264607173768033 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16451 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16447 < q → q < 16451 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16451).mp (by decide +kernel))) hgap
  have hprev := thV_1905
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16451:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3264607173768033 : ℚ) / 200000000000) ≤ ((3262665545459837 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (16451:ℚ) := by decide +kernel
  have hratR : ((((3264607173768033 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((3262665545459837 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16451:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1907 : ((((510398254123341 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16453 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16451 < q → q < 16453 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16453).mp (by decide +kernel))) hgap
  have hprev := thV_1906
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16453:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((510398254123341 : ℚ) / 31250000000) ≤ ((3264607173768033 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (16453:ℚ) := by decide +kernel
  have hratR : ((((510398254123341 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((3264607173768033 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16453:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1908 : ((((1634245385269133 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16477 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16453 < q → q < 16477 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16477).mp (by decide +kernel))) hgap
  have hprev := thV_1907
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16477:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1634245385269133 : ℚ) / 100000000000) ≤ ((510398254123341 : ℚ) / 31250000000) + Work.RHContract.RegionI.logLowQ (16477:ℚ) := by decide +kernel
  have hratR : ((((1634245385269133 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((510398254123341 : ℚ) / 31250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16477:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1909 : ((((4088040954042231 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16481 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16477 < q → q < 16481 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16481).mp (by decide +kernel))) hgap
  have hprev := thV_1908
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16481:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4088040954042231 : ℚ) / 250000000000) ≤ ((1634245385269133 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (16481:ℚ) := by decide +kernel
  have hratR : ((((4088040954042231 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((1634245385269133 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16481:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1910 : ((((3272374828727169 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16487 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16481 < q → q < 16487 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16487).mp (by decide +kernel))) hgap
  have hprev := thV_1909
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16487:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3272374828727169 : ℚ) / 200000000000) ≤ ((4088040954042231 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (16487:ℚ) := by decide +kernel
  have hratR : ((((3272374828727169 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((4088040954042231 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16487:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1911 : ((((16371584834959653 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16493 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16487 < q → q < 16493 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16493).mp (by decide +kernel))) hgap
  have hprev := thV_1910
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16493:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((16371584834959653 : ℚ) / 1000000000000) ≤ ((3272374828727169 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (16493:ℚ) := by decide +kernel
  have hratR : ((((16371584834959653 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3272374828727169 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16493:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1912 : ((((2047662137683571 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16519 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16493 < q → q < 16519 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16519).mp (by decide +kernel))) hgap
  have hprev := thV_1911
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16519:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2047662137683571 : ℚ) / 125000000000) ≤ ((16371584834959653 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (16519:ℚ) := by decide +kernel
  have hratR : ((((2047662137683571 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((16371584834959653 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16519:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1913 : ((((8195504986578923 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16529 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16519 < q → q < 16529 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16529).mp (by decide +kernel))) hgap
  have hprev := thV_1912
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16529:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8195504986578923 : ℚ) / 500000000000) ≤ ((2047662137683571 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (16529:ℚ) := by decide +kernel
  have hratR : ((((8195504986578923 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((2047662137683571 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16529:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1914 : ((((8200361966624849 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16547 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16529 < q → q < 16547 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16547).mp (by decide +kernel))) hgap
  have hprev := thV_1913
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16547:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8200361966624849 : ℚ) / 500000000000) ≤ ((8195504986578923 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (16547:ℚ) := by decide +kernel
  have hratR : ((((8200361966624849 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((8195504986578923 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16547:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1915 : ((((8205219127939659 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16553 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16547 < q → q < 16553 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16553).mp (by decide +kernel))) hgap
  have hprev := thV_1914
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16553:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8205219127939659 : ℚ) / 500000000000) ≤ ((8200361966624849 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (16553:ℚ) := by decide +kernel
  have hratR : ((((8205219127939659 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((8200361966624849 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16553:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1916 : ((((4105038265422067 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16561 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16553 < q → q < 16561 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16561).mp (by decide +kernel))) hgap
  have hprev := thV_1915
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16561:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4105038265422067 : ℚ) / 250000000000) ≤ ((8205219127939659 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (16561:ℚ) := by decide +kernel
  have hratR : ((((4105038265422067 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((8205219127939659 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16561:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1917 : ((((16429868229728567 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16567 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16561 < q → q < 16567 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16567).mp (by decide +kernel))) hgap
  have hprev := thV_1916
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16567:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((16429868229728567 : ℚ) / 1000000000000) ≤ ((4105038265422067 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (16567:ℚ) := by decide +kernel
  have hratR : ((((16429868229728567 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4105038265422067 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16567:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1918 : ((((16439583759869051 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16573 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16567 < q → q < 16573 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16573).mp (by decide +kernel))) hgap
  have hprev := thV_1917
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16573:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((16439583759869051 : ℚ) / 1000000000000) ≤ ((16429868229728567 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (16573:ℚ) := by decide +kernel
  have hratR : ((((16439583759869051 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((16429868229728567 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16573:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1919 : ((((16449301098546319 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16603 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16573 < q → q < 16603 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16603).mp (by decide +kernel))) hgap
  have hprev := thV_1918
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16603:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((16449301098546319 : ℚ) / 1000000000000) ≤ ((16439583759869051 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (16603:ℚ) := by decide +kernel
  have hratR : ((((16449301098546319 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((16439583759869051 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16603:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1920 : ((((8229509339057443 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16607 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16603 < q → q < 16607 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16607).mp (by decide +kernel))) hgap
  have hprev := thV_1919
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16607:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8229509339057443 : ℚ) / 500000000000) ≤ ((16449301098546319 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (16607:ℚ) := by decide +kernel
  have hratR : ((((8229509339057443 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((16449301098546319 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16607:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1921 : ((((8234368490004687 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16619 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16607 < q → q < 16619 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16619).mp (by decide +kernel))) hgap
  have hprev := thV_1920
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16619:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8234368490004687 : ℚ) / 500000000000) ≤ ((8229509339057443 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (16619:ℚ) := by decide +kernel
  have hratR : ((((8234368490004687 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((8229509339057443 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16619:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1922 : ((((4119614000927101 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16631 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16619 < q → q < 16631 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16631).mp (by decide +kernel))) hgap
  have hprev := thV_1921
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16631:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4119614000927101 : ℚ) / 250000000000) ≤ ((8234368490004687 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (16631:ℚ) := by decide +kernel
  have hratR : ((((4119614000927101 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((8234368490004687 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16631:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1923 : ((((3297635029531511 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16633 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16631 < q → q < 16633 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16633).mp (by decide +kernel))) hgap
  have hprev := thV_1922
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16633:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3297635029531511 : ℚ) / 200000000000) ≤ ((4119614000927101 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (16633:ℚ) := by decide +kernel
  have hratR : ((((3297635029531511 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((4119614000927101 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16633:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1924 : ((((824894762654373 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16649 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16633 < q → q < 16649 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16649).mp (by decide +kernel))) hgap
  have hprev := thV_1923
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16649:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((824894762654373 : ℚ) / 50000000000) ≤ ((3297635029531511 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (16649:ℚ) := by decide +kernel
  have hratR : ((((824894762654373 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((3297635029531511 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16649:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1925 : ((((3301523095727497 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16651 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16649 < q → q < 16651 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16651).mp (by decide +kernel))) hgap
  have hprev := thV_1924
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16651:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3301523095727497 : ℚ) / 200000000000) ≤ ((824894762654373 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (16651:ℚ) := by decide +kernel
  have hratR : ((((3301523095727497 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((824894762654373 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16651:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1926 : ((((8258668032230661 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16657 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16651 < q → q < 16657 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16657).mp (by decide +kernel))) hgap
  have hprev := thV_1925
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16657:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8258668032230661 : ℚ) / 500000000000) ≤ ((3301523095727497 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (16657:ℚ) := by decide +kernel
  have hratR : ((((8258668032230661 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((3301523095727497 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16657:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1927 : ((((16527056890395611 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16661 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16657 < q → q < 16661 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16661).mp (by decide +kernel))) hgap
  have hprev := thV_1926
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16661:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((16527056890395611 : ℚ) / 1000000000000) ≤ ((8258668032230661 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (16661:ℚ) := by decide +kernel
  have hratR : ((((16527056890395611 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((8258668032230661 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16661:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1928 : ((((4134194609078883 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16673 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16661 < q → q < 16673 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16673).mp (by decide +kernel))) hgap
  have hprev := thV_1927
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16673:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4134194609078883 : ℚ) / 250000000000) ≤ ((16527056890395611 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (16673:ℚ) := by decide +kernel
  have hratR : ((((4134194609078883 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((16527056890395611 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16673:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1929 : ((((16546501061242871 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16691 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16673 < q → q < 16691 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16691).mp (by decide +kernel))) hgap
  have hprev := thV_1928
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16691:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((16546501061242871 : ℚ) / 1000000000000) ≤ ((4134194609078883 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (16691:ℚ) := by decide +kernel
  have hratR : ((((16546501061242871 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4134194609078883 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16691:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1930 : ((((16556223805988087 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16693 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16691 < q → q < 16693 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16693).mp (by decide +kernel))) hgap
  have hprev := thV_1929
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16693:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((16556223805988087 : ℚ) / 1000000000000) ≤ ((16546501061242871 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (16693:ℚ) := by decide +kernel
  have hratR : ((((16556223805988087 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((16546501061242871 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16693:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1931 : ((((828297345505041 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16699 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16693 < q → q < 16699 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16699).mp (by decide +kernel))) hgap
  have hprev := thV_1930
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16699:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((828297345505041 : ℚ) / 50000000000) ≤ ((16556223805988087 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (16699:ℚ) := by decide +kernel
  have hratR : ((((828297345505041 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((16556223805988087 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16699:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1932 : ((((1657567025372017 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16703 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16699 < q → q < 16703 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16703).mp (by decide +kernel))) hgap
  have hprev := thV_1931
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16703:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1657567025372017 : ℚ) / 100000000000) ≤ ((828297345505041 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (16703:ℚ) := by decide +kernel
  have hratR : ((((1657567025372017 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((828297345505041 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16703:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1933 : ((((8292697576367931 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16729 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16703 < q → q < 16729 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16729).mp (by decide +kernel))) hgap
  have hprev := thV_1932
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16729:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8292697576367931 : ℚ) / 500000000000) ≤ ((1657567025372017 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (16729:ℚ) := by decide +kernel
  have hratR : ((((8292697576367931 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1657567025372017 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16729:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1934 : ((((8297560384405819 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16741 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16729 < q → q < 16741 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16741).mp (by decide +kernel))) hgap
  have hprev := thV_1933
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16741:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8297560384405819 : ℚ) / 500000000000) ≤ ((8292697576367931 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (16741:ℚ) := by decide +kernel
  have hratR : ((((8297560384405819 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((8292697576367931 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16741:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1935 : ((((16604846743224733 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16747 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16741 < q → q < 16747 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16747).mp (by decide +kernel))) hgap
  have hprev := thV_1934
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16747:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((16604846743224733 : ℚ) / 1000000000000) ≤ ((8297560384405819 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (16747:ℚ) := by decide +kernel
  have hratR : ((((16604846743224733 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((8297560384405819 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16747:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1936 : ((((8307286716963739 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16759 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16747 < q → q < 16759 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16759).mp (by decide +kernel))) hgap
  have hprev := thV_1935
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16759:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8307286716963739 : ℚ) / 500000000000) ≤ ((16604846743224733 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (16759:ℚ) := by decide +kernel
  have hratR : ((((8307286716963739 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((16604846743224733 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16759:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1937 : ((((1662430036327947 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16763 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16759 < q → q < 16763 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16763).mp (by decide +kernel))) hgap
  have hprev := thV_1936
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16763:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1662430036327947 : ℚ) / 100000000000) ≤ ((8307286716963739 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (16763:ℚ) := by decide +kernel
  have hratR : ((((1662430036327947 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((8307286716963739 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16763:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1938 : ((((16634028723332153 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16787 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16763 < q → q < 16787 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16787).mp (by decide +kernel))) hgap
  have hprev := thV_1937
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16787:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((16634028723332153 : ℚ) / 1000000000000) ≤ ((1662430036327947 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (16787:ℚ) := by decide +kernel
  have hratR : ((((16634028723332153 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1662430036327947 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16787:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1939 : ((((8321879256020773 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16811 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16787 < q → q < 16811 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16811).mp (by decide +kernel))) hgap
  have hprev := thV_1938
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16811:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8321879256020773 : ℚ) / 500000000000) ≤ ((16634028723332153 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (16811:ℚ) := by decide +kernel
  have hratR : ((((8321879256020773 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((16634028723332153 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16811:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1940 : ((((133227912114517 : ℚ) / 8000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16823 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16811 < q → q < 16823 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16823).mp (by decide +kernel))) hgap
  have hprev := thV_1939
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16823:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((133227912114517 : ℚ) / 8000000000) ≤ ((8321879256020773 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (16823:ℚ) := by decide +kernel
  have hratR : ((((133227912114517 : ℚ) / 8000000000) : ℚ) : ℝ) ≤ ((((8321879256020773 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16823:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1941 : ((((8331609936589349 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16829 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16823 < q → q < 16829 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16829).mp (by decide +kernel))) hgap
  have hprev := thV_1940
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16829:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8331609936589349 : ℚ) / 500000000000) ≤ ((133227912114517 : ℚ) / 8000000000) + Work.RHContract.RegionI.logLowQ (16829:ℚ) := by decide +kernel
  have hratR : ((((8331609936589349 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((133227912114517 : ℚ) / 8000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16829:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1942 : ((((2084118856359773 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16831 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16829 < q → q < 16831 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16831).mp (by decide +kernel))) hgap
  have hprev := thV_1941
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16831:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2084118856359773 : ℚ) / 125000000000) ≤ ((8331609936589349 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (16831:ℚ) := by decide +kernel
  have hratR : ((((2084118856359773 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((8331609936589349 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16831:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1943 : ((((16682682541293743 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16843 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16831 < q → q < 16843 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16843).mp (by decide +kernel))) hgap
  have hprev := thV_1942
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16843:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((16682682541293743 : ℚ) / 1000000000000) ≤ ((2084118856359773 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (16843:ℚ) := by decide +kernel
  have hratR : ((((16682682541293743 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2084118856359773 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16843:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1944 : ((((16692415892740709 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16871 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16843 < q → q < 16871 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16871).mp (by decide +kernel))) hgap
  have hprev := thV_1943
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16871:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((16692415892740709 : ℚ) / 1000000000000) ≤ ((16682682541293743 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (16871:ℚ) := by decide +kernel
  have hratR : ((((16692415892740709 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((16682682541293743 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16871:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1945 : ((((8351074859130879 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16879 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16871 < q → q < 16879 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16879).mp (by decide +kernel))) hgap
  have hprev := thV_1944
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16879:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8351074859130879 : ℚ) / 500000000000) ≤ ((16692415892740709 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (16879:ℚ) := by decide +kernel
  have hratR : ((((8351074859130879 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((16692415892740709 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16879:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1946 : ((((3342376756147119 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16883 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16879 < q → q < 16883 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16883).mp (by decide +kernel))) hgap
  have hprev := thV_1945
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16883:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3342376756147119 : ℚ) / 200000000000) ≤ ((8351074859130879 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (16883:ℚ) := by decide +kernel
  have hratR : ((((3342376756147119 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((8351074859130879 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16883:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1947 : ((((16721618198533373 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16889 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16883 < q → q < 16889 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16889).mp (by decide +kernel))) hgap
  have hprev := thV_1946
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16889:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((16721618198533373 : ℚ) / 1000000000000) ≤ ((3342376756147119 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (16889:ℚ) := by decide +kernel
  have hratR : ((((16721618198533373 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3342376756147119 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16889:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1948 : ((((16731353326600491 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16901 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16889 < q → q < 16901 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16901).mp (by decide +kernel))) hgap
  have hprev := thV_1947
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16901:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((16731353326600491 : ℚ) / 1000000000000) ≤ ((16721618198533373 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (16901:ℚ) := by decide +kernel
  have hratR : ((((16731353326600491 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((16721618198533373 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16901:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1949 : ((((16741088572996801 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16903 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16901 < q → q < 16903 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16903).mp (by decide +kernel))) hgap
  have hprev := thV_1948
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16903:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((16741088572996801 : ℚ) / 1000000000000) ≤ ((16731353326600491 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (16903:ℚ) := by decide +kernel
  have hratR : ((((16741088572996801 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((16731353326600491 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16903:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1950 : ((((1675082488372623 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16921 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16903 < q → q < 16921 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16921).mp (by decide +kernel))) hgap
  have hprev := thV_1949
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16921:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1675082488372623 : ℚ) / 100000000000) ≤ ((16741088572996801 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (16921:ℚ) := by decide +kernel
  have hratR : ((((1675082488372623 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((16741088572996801 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16921:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1951 : ((((16760561548981779 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16927 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16921 < q → q < 16927 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16927).mp (by decide +kernel))) hgap
  have hprev := thV_1950
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16927:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((16760561548981779 : ℚ) / 1000000000000) ≤ ((1675082488372623 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (16927:ℚ) := by decide +kernel
  have hratR : ((((16760561548981779 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1675082488372623 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16927:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1952 : ((((16770298450518267 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16931 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16927 < q → q < 16931 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16931).mp (by decide +kernel))) hgap
  have hprev := thV_1951
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16931:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((16770298450518267 : ℚ) / 1000000000000) ≤ ((16760561548981779 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (16931:ℚ) := by decide +kernel
  have hratR : ((((16770298450518267 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((16760561548981779 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16931:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1953 : ((((8390017853185759 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16937 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16931 < q → q < 16937 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16937).mp (by decide +kernel))) hgap
  have hprev := thV_1952
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16937:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8390017853185759 : ℚ) / 500000000000) ≤ ((16770298450518267 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (16937:ℚ) := by decide +kernel
  have hratR : ((((8390017853185759 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((16770298450518267 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16937:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1954 : ((((4197443329104009 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16943 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16937 < q → q < 16943 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16943).mp (by decide +kernel))) hgap
  have hprev := thV_1953
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16943:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4197443329104009 : ℚ) / 250000000000) ≤ ((8390017853185759 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (16943:ℚ) := by decide +kernel
  have hratR : ((((4197443329104009 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((8390017853185759 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16943:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1955 : ((((4199878026548223 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16963 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16943 < q → q < 16963 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16963).mp (by decide +kernel))) hgap
  have hprev := thV_1954
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16963:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4199878026548223 : ℚ) / 250000000000) ≤ ((4197443329104009 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (16963:ℚ) := by decide +kernel
  have hratR : ((((4199878026548223 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((4197443329104009 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16963:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1956 : ((((2101156479844321 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16979 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16963 < q → q < 16979 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16979).mp (by decide +kernel))) hgap
  have hprev := thV_1955
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16979:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2101156479844321 : ℚ) / 125000000000) ≤ ((4199878026548223 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (16979:ℚ) := by decide +kernel
  have hratR : ((((2101156479844321 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((4199878026548223 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16979:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1957 : ((((26910386702563 : ℚ) / 1600000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16981 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16979 < q → q < 16981 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16981).mp (by decide +kernel))) hgap
  have hprev := thV_1956
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16981:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((26910386702563 : ℚ) / 1600000000) ≤ ((2101156479844321 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (16981:ℚ) := by decide +kernel
  have hratR : ((((26910386702563 : ℚ) / 1600000000) : ℚ) : ℝ) ≤ ((((2101156479844321 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16981:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1958 : ((((3365746378544571 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16987 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16981 < q → q < 16987 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16987).mp (by decide +kernel))) hgap
  have hprev := thV_1957
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16987:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3365746378544571 : ℚ) / 200000000000) ≤ ((26910386702563 : ℚ) / 1600000000) + Work.RHContract.RegionI.logLowQ (16987:ℚ) := by decide +kernel
  have hratR : ((((3365746378544571 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((26910386702563 : ℚ) / 1600000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16987:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1959 : ((((16838472449492749 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((16993 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16987 < q → q < 16993 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16993).mp (by decide +kernel))) hgap
  have hprev := thV_1958
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (16993:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((16838472449492749 : ℚ) / 1000000000000) ≤ ((3365746378544571 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (16993:ℚ) := by decide +kernel
  have hratR : ((((16838472449492749 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3365746378544571 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (16993:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1960 : ((((16848214064961719 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17011 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 16993 < q → q < 17011 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17011).mp (by decide +kernel))) hgap
  have hprev := thV_1959
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17011:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((16848214064961719 : ℚ) / 1000000000000) ≤ ((16838472449492749 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (17011:ℚ) := by decide +kernel
  have hratR : ((((16848214064961719 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((16838472449492749 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17011:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1961 : ((((16857956268112887 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17021 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17011 < q → q < 17021 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17021).mp (by decide +kernel))) hgap
  have hprev := thV_1960
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17021:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((16857956268112887 : ℚ) / 1000000000000) ≤ ((16848214064961719 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (17021:ℚ) := by decide +kernel
  have hratR : ((((16857956268112887 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((16848214064961719 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17021:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1962 : ((((4216924705926917 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17027 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17021 < q → q < 17027 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17027).mp (by decide +kernel))) hgap
  have hprev := thV_1961
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17027:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4216924705926917 : ℚ) / 250000000000) ≤ ((16857956268112887 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (17027:ℚ) := by decide +kernel
  have hratR : ((((4216924705926917 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((16857956268112887 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17027:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1963 : ((((3375488299351211 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17029 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17027 < q → q < 17029 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17029).mp (by decide +kernel))) hgap
  have hprev := thV_1962
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17029:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3375488299351211 : ℚ) / 200000000000) ≤ ((4216924705926917 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (17029:ℚ) := by decide +kernel
  have hratR : ((((3375488299351211 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((4216924705926917 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17029:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1964 : ((((4221796101167569 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17033 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17029 < q → q < 17033 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17033).mp (by decide +kernel))) hgap
  have hprev := thV_1963
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17033:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4221796101167569 : ℚ) / 250000000000) ≤ ((3375488299351211 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (17033:ℚ) := by decide +kernel
  have hratR : ((((4221796101167569 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((3375488299351211 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17033:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1965 : ((((2112115972768843 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17041 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17033 < q → q < 17041 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17041).mp (by decide +kernel))) hgap
  have hprev := thV_1964
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17041:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2112115972768843 : ℚ) / 125000000000) ≤ ((4221796101167569 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (17041:ℚ) := by decide +kernel
  have hratR : ((((2112115972768843 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((4221796101167569 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17041:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1966 : ((((3381334302332251 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17047 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17041 < q → q < 17047 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17047).mp (by decide +kernel))) hgap
  have hprev := thV_1965
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17047:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3381334302332251 : ℚ) / 200000000000) ≤ ((2112115972768843 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (17047:ℚ) := by decide +kernel
  have hratR : ((((3381334302332251 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((2112115972768843 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17047:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1967 : ((((2114551949134741 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17053 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17047 < q → q < 17053 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17053).mp (by decide +kernel))) hgap
  have hprev := thV_1966
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17053:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2114551949134741 : ℚ) / 125000000000) ≤ ((3381334302332251 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (17053:ℚ) := by decide +kernel
  have hratR : ((((2114551949134741 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((3381334302332251 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17053:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1968 : ((((16529454180549 : ℚ) / 976562500) : ℚ) : ℝ) ≤ Chebyshev.theta ((17077 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17053 < q → q < 17077 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17077).mp (by decide +kernel))) hgap
  have hprev := thV_1967
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17077:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((16529454180549 : ℚ) / 976562500) ≤ ((2114551949134741 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (17077:ℚ) := by decide +kernel
  have hratR : ((((16529454180549 : ℚ) / 976562500) : ℚ) : ℝ) ≤ ((((2114551949134741 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17077:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1969 : ((((16935907505180493 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17093 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17077 < q → q < 17093 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17093).mp (by decide +kernel))) hgap
  have hprev := thV_1968
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17093:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((16935907505180493 : ℚ) / 1000000000000) ≤ ((16529454180549 : ℚ) / 976562500) + Work.RHContract.RegionI.logLowQ (17093:ℚ) := by decide +kernel
  have hratR : ((((16935907505180493 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((16529454180549 : ℚ) / 976562500) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17093:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1970 : ((((8472827140219051 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17099 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17093 < q → q < 17099 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17099).mp (by decide +kernel))) hgap
  have hprev := thV_1969
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17099:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8472827140219051 : ℚ) / 500000000000) ≤ ((16935907505180493 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (17099:ℚ) := by decide +kernel
  have hratR : ((((8472827140219051 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((16935907505180493 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17099:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1971 : ((((3391080304689983 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17107 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17099 < q → q < 17107 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17107).mp (by decide +kernel))) hgap
  have hprev := thV_1970
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17107:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3391080304689983 : ℚ) / 200000000000) ≤ ((8472827140219051 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (17107:ℚ) := by decide +kernel
  have hratR : ((((3391080304689983 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((8472827140219051 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17107:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1972 : ((((16965149350846971 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17117 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17107 < q → q < 17117 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17117).mp (by decide +kernel))) hgap
  have hprev := thV_1971
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17117:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((16965149350846971 : ℚ) / 1000000000000) ≤ ((3391080304689983 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (17117:ℚ) := by decide +kernel
  have hratR : ((((16965149350846971 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3391080304689983 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17117:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1973 : ((((424372438217783 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17123 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17117 < q → q < 17123 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17123).mp (by decide +kernel))) hgap
  have hprev := thV_1972
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17123:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((424372438217783 : ℚ) / 25000000000) ≤ ((16965149350846971 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (17123:ℚ) := by decide +kernel
  have hratR : ((((424372438217783 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((16965149350846971 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17123:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1974 : ((((16984646523855341 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17137 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17123 < q → q < 17137 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17137).mp (by decide +kernel))) hgap
  have hprev := thV_1973
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17137:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((16984646523855341 : ℚ) / 1000000000000) ≤ ((424372438217783 : ℚ) / 25000000000) + Work.RHContract.RegionI.logLowQ (17137:ℚ) := by decide +kernel
  have hratR : ((((16984646523855341 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((424372438217783 : ℚ) / 25000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17137:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1975 : ((((16994396801947987 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17159 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17137 < q → q < 17159 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17159).mp (by decide +kernel))) hgap
  have hprev := thV_1974
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17159:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((16994396801947987 : ℚ) / 1000000000000) ≤ ((16984646523855341 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (17159:ℚ) := by decide +kernel
  have hratR : ((((16994396801947987 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((16984646523855341 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17159:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1976 : ((((8502073773079809 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17167 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17159 < q → q < 17167 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17167).mp (by decide +kernel))) hgap
  have hprev := thV_1975
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17167:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8502073773079809 : ℚ) / 500000000000) ≤ ((16994396801947987 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (17167:ℚ) := by decide +kernel
  have hratR : ((((8502073773079809 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((16994396801947987 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17167:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1977 : ((((680555968878317 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17183 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17167 < q → q < 17183 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17183).mp (by decide +kernel))) hgap
  have hprev := thV_1976
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17183:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((680555968878317 : ℚ) / 40000000000) ≤ ((8502073773079809 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (17183:ℚ) := by decide +kernel
  have hratR : ((((680555968878317 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((8502073773079809 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17183:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1978 : ((((17023651246877613 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17189 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17183 < q → q < 17189 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17189).mp (by decide +kernel))) hgap
  have hprev := thV_1977
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17189:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((17023651246877613 : ℚ) / 1000000000000) ≤ ((680555968878317 : ℚ) / 40000000000) + Work.RHContract.RegionI.logLowQ (17189:ℚ) := by decide +kernel
  have hratR : ((((17023651246877613 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((680555968878317 : ℚ) / 40000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17189:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1979 : ((((3406680677628803 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17191 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17189 < q → q < 17191 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17191).mp (by decide +kernel))) hgap
  have hprev := thV_1978
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17191:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3406680677628803 : ℚ) / 200000000000) ≤ ((17023651246877613 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (17191:ℚ) := by decide +kernel
  have hratR : ((((3406680677628803 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((17023651246877613 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17191:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1980 : ((((4260789056801643 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17203 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17191 < q → q < 17203 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17203).mp (by decide +kernel))) hgap
  have hprev := thV_1979
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17203:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4260789056801643 : ℚ) / 250000000000) ≤ ((3406680677628803 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (17203:ℚ) := by decide +kernel
  have hratR : ((((4260789056801643 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((3406680677628803 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17203:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1981 : ((((3410581859751937 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17207 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17203 < q → q < 17207 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17207).mp (by decide +kernel))) hgap
  have hprev := thV_1980
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17207:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3410581859751937 : ℚ) / 200000000000) ≤ ((4260789056801643 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (17207:ℚ) := by decide +kernel
  have hratR : ((((3410581859751937 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((4260789056801643 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17207:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1982 : ((((1706266248653781 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17209 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17207 < q → q < 17209 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17209).mp (by decide +kernel))) hgap
  have hprev := thV_1981
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17209:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1706266248653781 : ℚ) / 100000000000) ≤ ((3410581859751937 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (17209:ℚ) := by decide +kernel
  have hratR : ((((1706266248653781 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((3410581859751937 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17209:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1983 : ((((17072416951900313 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17231 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17209 < q → q < 17231 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17231).mp (by decide +kernel))) hgap
  have hprev := thV_1982
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17231:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((17072416951900313 : ℚ) / 1000000000000) ≤ ((1706266248653781 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (17231:ℚ) := by decide +kernel
  have hratR : ((((17072416951900313 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1706266248653781 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17231:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1984 : ((((2135271485179321 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17239 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17231 < q → q < 17239 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17239).mp (by decide +kernel))) hgap
  have hprev := thV_1983
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17239:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2135271485179321 : ℚ) / 125000000000) ≤ ((17072416951900313 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (17239:ℚ) := by decide +kernel
  have hratR : ((((2135271485179321 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((17072416951900313 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17239:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1985 : ((((1068245490910511 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17257 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17239 < q → q < 17257 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17257).mp (by decide +kernel))) hgap
  have hprev := thV_1984
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17257:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1068245490910511 : ℚ) / 62500000000) ≤ ((2135271485179321 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (17257:ℚ) := by decide +kernel
  have hratR : ((((1068245490910511 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((2135271485179321 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17257:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1986 : ((((17101685795978441 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17291 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17257 < q → q < 17291 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17291).mp (by decide +kernel))) hgap
  have hprev := thV_1985
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17291:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((17101685795978441 : ℚ) / 1000000000000) ≤ ((1068245490910511 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (17291:ℚ) := by decide +kernel
  have hratR : ((((17101685795978441 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1068245490910511 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17291:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1987 : ((((17111443853049127 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17293 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17291 < q → q < 17293 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17293).mp (by decide +kernel))) hgap
  have hprev := thV_1986
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17293:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((17111443853049127 : ℚ) / 1000000000000) ≤ ((17101685795978441 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (17293:ℚ) := by decide +kernel
  have hratR : ((((17111443853049127 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((17101685795978441 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17293:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1988 : ((((8560601128510417 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17299 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17293 < q → q < 17299 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17299).mp (by decide +kernel))) hgap
  have hprev := thV_1987
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17299:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8560601128510417 : ℚ) / 500000000000) ≤ ((17111443853049127 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (17299:ℚ) := by decide +kernel
  have hratR : ((((8560601128510417 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((17111443853049127 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17299:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1989 : ((((8565480850487073 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17317 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17299 < q → q < 17317 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17317).mp (by decide +kernel))) hgap
  have hprev := thV_1988
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17317:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8565480850487073 : ℚ) / 500000000000) ≤ ((8560601128510417 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (17317:ℚ) := by decide +kernel
  have hratR : ((((8565480850487073 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((8560601128510417 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17317:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1990 : ((((17140721375887677 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17321 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17317 < q → q < 17321 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17321).mp (by decide +kernel))) hgap
  have hprev := thV_1989
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17321:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((17140721375887677 : ℚ) / 1000000000000) ≤ ((8565480850487073 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (17321:ℚ) := by decide +kernel
  have hratR : ((((17140721375887677 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((8565480850487073 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17321:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1991 : ((((4287620349285387 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17327 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17321 < q → q < 17327 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17327).mp (by decide +kernel))) hgap
  have hprev := thV_1990
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17327:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4287620349285387 : ℚ) / 250000000000) ≤ ((17140721375887677 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (17327:ℚ) := by decide +kernel
  have hratR : ((((4287620349285387 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((17140721375887677 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17327:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1992 : ((((343204835292317 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17333 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17327 < q → q < 17333 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17333).mp (by decide +kernel))) hgap
  have hprev := thV_1991
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17333:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((343204835292317 : ℚ) / 20000000000) ≤ ((4287620349285387 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (17333:ℚ) := by decide +kernel
  have hratR : ((((343204835292317 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ ((((4287620349285387 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17333:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1993 : ((((17170002593531009 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17341 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17333 < q → q < 17341 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17341).mp (by decide +kernel))) hgap
  have hprev := thV_1992
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17341:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((17170002593531009 : ℚ) / 1000000000000) ≤ ((343204835292317 : ℚ) / 20000000000) + Work.RHContract.RegionI.logLowQ (17341:ℚ) := by decide +kernel
  have hratR : ((((17170002593531009 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((343204835292317 : ℚ) / 20000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17341:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1994 : ((((17179763998947971 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17351 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17341 < q → q < 17351 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17351).mp (by decide +kernel))) hgap
  have hprev := thV_1993
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17351:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((17179763998947971 : ℚ) / 1000000000000) ≤ ((17170002593531009 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (17351:ℚ) := by decide +kernel
  have hratR : ((((17179763998947971 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((17170002593531009 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17351:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1995 : ((((21486907331659 : ℚ) / 1250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17359 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17351 < q → q < 17359 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17359).mp (by decide +kernel))) hgap
  have hprev := thV_1994
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17359:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((21486907331659 : ℚ) / 1250000000) ≤ ((17179763998947971 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (17359:ℚ) := by decide +kernel
  have hratR : ((((21486907331659 : ℚ) / 1250000000) : ℚ) : ℝ) ≤ ((((17179763998947971 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17359:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1996 : ((((17199288768095283 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17377 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17359 < q → q < 17377 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17377).mp (by decide +kernel))) hgap
  have hprev := thV_1995
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17377:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((17199288768095283 : ℚ) / 1000000000000) ≤ ((21486907331659 : ℚ) / 1250000000) + Work.RHContract.RegionI.logLowQ (17377:ℚ) := by decide +kernel
  have hratR : ((((17199288768095283 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((21486907331659 : ℚ) / 1250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17377:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1997 : ((((3441810403217553 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17383 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17377 < q → q < 17383 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17383).mp (by decide +kernel))) hgap
  have hprev := thV_1996
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17383:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3441810403217553 : ℚ) / 200000000000) ≤ ((17199288768095283 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (17383:ℚ) := by decide +kernel
  have hratR : ((((3441810403217553 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((17199288768095283 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17383:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1998 : ((((17218815494163653 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17387 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17383 < q → q < 17387 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17387).mp (by decide +kernel))) hgap
  have hprev := thV_1997
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17387:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((17218815494163653 : ℚ) / 1000000000000) ≤ ((3441810403217553 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (17387:ℚ) := by decide +kernel
  have hratR : ((((17218815494163653 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3441810403217553 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17387:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1999 : ((((3445715817452279 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17389 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17387 < q → q < 17389 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17389).mp (by decide +kernel))) hgap
  have hprev := thV_1998
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17389:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3445715817452279 : ℚ) / 200000000000) ≤ ((17218815494163653 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (17389:ℚ) := by decide +kernel
  have hratR : ((((3445715817452279 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((17218815494163653 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17389:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2000 : ((((17238342910363163 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17393 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17389 < q → q < 17393 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17393).mp (by decide +kernel))) hgap
  have hprev := thV_1999
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17393:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((17238342910363163 : ℚ) / 1000000000000) ≤ ((3445715817452279 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (17393:ℚ) := by decide +kernel
  have hratR : ((((17238342910363163 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3445715817452279 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17393:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2001 : ((((17248107193314339 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17401 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17393 < q → q < 17401 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17401).mp (by decide +kernel))) hgap
  have hprev := thV_2000
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17401:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((17248107193314339 : ℚ) / 1000000000000) ≤ ((17238342910363163 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (17401:ℚ) := by decide +kernel
  have hratR : ((((17248107193314339 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((17238342910363163 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17401:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2002 : ((((17257872395330431 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17417 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17401 < q → q < 17417 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17417).mp (by decide +kernel))) hgap
  have hprev := thV_2001
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17417:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((17257872395330431 : ℚ) / 1000000000000) ≤ ((17248107193314339 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (17417:ℚ) := by decide +kernel
  have hratR : ((((17257872395330431 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((17248107193314339 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17417:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2003 : ((((17267637712170269 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17419 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17417 < q → q < 17419 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17419).mp (by decide +kernel))) hgap
  have hprev := thV_2002
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17419:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((17267637712170269 : ℚ) / 1000000000000) ≤ ((17257872395330431 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (17419:ℚ) := by decide +kernel
  have hratR : ((((17267637712170269 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((17257872395330431 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17419:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2004 : ((((4319350929418961 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17431 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17419 < q → q < 17431 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17431).mp (by decide +kernel))) hgap
  have hprev := thV_2003
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17431:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4319350929418961 : ℚ) / 250000000000) ≤ ((17267637712170269 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (17431:ℚ) := by decide +kernel
  have hratR : ((((4319350929418961 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((17267637712170269 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17431:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2005 : ((((8643585205686611 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17443 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17431 < q → q < 17443 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17443).mp (by decide +kernel))) hgap
  have hprev := thV_2004
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17443:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8643585205686611 : ℚ) / 500000000000) ≤ ((4319350929418961 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (17443:ℚ) := by decide +kernel
  have hratR : ((((8643585205686611 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((4319350929418961 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17443:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2006 : ((((864846872449449 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17449 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17443 < q → q < 17449 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17449).mp (by decide +kernel))) hgap
  have hprev := thV_2005
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17449:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((864846872449449 : ℚ) / 50000000000) ≤ ((8643585205686611 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (17449:ℚ) := by decide +kernel
  have hratR : ((((864846872449449 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((8643585205686611 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17449:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2007 : ((((17306705517650769 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17467 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17449 < q → q < 17467 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17467).mp (by decide +kernel))) hgap
  have hprev := thV_2006
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17467:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((17306705517650769 : ℚ) / 1000000000000) ≤ ((864846872449449 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (17467:ℚ) := by decide +kernel
  have hratR : ((((17306705517650769 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((864846872449449 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17467:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2008 : ((((4329118453822401 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17471 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17467 < q → q < 17471 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17471).mp (by decide +kernel))) hgap
  have hprev := thV_2007
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17471:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4329118453822401 : ℚ) / 250000000000) ≤ ((17306705517650769 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (17471:ℚ) := by decide +kernel
  have hratR : ((((4329118453822401 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((17306705517650769 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17471:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2009 : ((((17326242456295731 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17477 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17471 < q → q < 17477 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17477).mp (by decide +kernel))) hgap
  have hprev := thV_2008
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17477:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((17326242456295731 : ℚ) / 1000000000000) ≤ ((4329118453822401 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (17477:ℚ) := by decide +kernel
  have hratR : ((((17326242456295731 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4329118453822401 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17477:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2010 : ((((17336011440551289 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17483 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17477 < q → q < 17483 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17483).mp (by decide +kernel))) hgap
  have hprev := thV_2009
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17483:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((17336011440551289 : ℚ) / 1000000000000) ≤ ((17326242456295731 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (17483:ℚ) := by decide +kernel
  have hratR : ((((17336011440551289 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((17326242456295731 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17483:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2011 : ((((8672890383969249 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17489 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17483 < q → q < 17489 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17489).mp (by decide +kernel))) hgap
  have hprev := thV_2010
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17489:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8672890383969249 : ℚ) / 500000000000) ≤ ((17336011440551289 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (17489:ℚ) := by decide +kernel
  have hratR : ((((8672890383969249 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((17336011440551289 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17489:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2012 : ((((3471110041935353 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17491 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17489 < q → q < 17491 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17491).mp (by decide +kernel))) hgap
  have hprev := thV_2011
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17491:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3471110041935353 : ℚ) / 200000000000) ≤ ((8672890383969249 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (17491:ℚ) := by decide +kernel
  have hratR : ((((3471110041935353 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((8672890383969249 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17491:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2013 : ((((1736531999438977 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17497 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17491 < q → q < 17497 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17497).mp (by decide +kernel))) hgap
  have hprev := thV_2012
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17497:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1736531999438977 : ℚ) / 100000000000) ≤ ((3471110041935353 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (17497:ℚ) := by decide +kernel
  have hratR : ((((1736531999438977 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((3471110041935353 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17497:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2014 : ((((17375090464699557 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17509 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17497 < q → q < 17509 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17509).mp (by decide +kernel))) hgap
  have hprev := thV_2013
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17509:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((17375090464699557 : ℚ) / 1000000000000) ≤ ((1736531999438977 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (17509:ℚ) := by decide +kernel
  have hratR : ((((17375090464699557 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1736531999438977 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17509:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2015 : ((((17384861505981153 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17519 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17509 < q → q < 17519 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17519).mp (by decide +kernel))) hgap
  have hprev := thV_2014
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17519:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((17384861505981153 : ℚ) / 1000000000000) ≤ ((17375090464699557 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (17519:ℚ) := by decide +kernel
  have hratR : ((((17384861505981153 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((17375090464699557 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17519:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2016 : ((((17394633688229271 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17539 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17519 < q → q < 17539 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17539).mp (by decide +kernel))) hgap
  have hprev := thV_2015
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17539:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((17394633688229271 : ℚ) / 1000000000000) ≤ ((17384861505981153 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (17539:ℚ) := by decide +kernel
  have hratR : ((((17394633688229271 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((17384861505981153 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17539:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2017 : ((((17404406554432959 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17551 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17539 < q → q < 17551 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17551).mp (by decide +kernel))) hgap
  have hprev := thV_2016
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17551:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((17404406554432959 : ℚ) / 1000000000000) ≤ ((17394633688229271 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (17551:ℚ) := by decide +kernel
  have hratR : ((((17404406554432959 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((17394633688229271 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17551:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2018 : ((((4353545111423421 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17569 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17551 < q → q < 17569 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17569).mp (by decide +kernel))) hgap
  have hprev := thV_2017
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17569:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4353545111423421 : ℚ) / 250000000000) ≤ ((17404406554432959 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (17569:ℚ) := by decide +kernel
  have hratR : ((((4353545111423421 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((17404406554432959 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17569:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2019 : ((((17423954564602239 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17573 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17569 < q → q < 17573 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17573).mp (by decide +kernel))) hgap
  have hprev := thV_2018
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17573:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((17423954564602239 : ℚ) / 1000000000000) ≤ ((4353545111423421 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (17573:ℚ) := by decide +kernel
  have hratR : ((((17423954564602239 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4353545111423421 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17573:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2020 : ((((17433729024885399 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17579 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17573 < q → q < 17579 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17579).mp (by decide +kernel))) hgap
  have hprev := thV_2019
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17579:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((17433729024885399 : ℚ) / 1000000000000) ≤ ((17423954564602239 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (17579:ℚ) := by decide +kernel
  have hratR : ((((17433729024885399 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((17423954564602239 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17579:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2021 : ((((8721751799467101 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17581 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17579 < q → q < 17581 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17581).mp (by decide +kernel))) hgap
  have hprev := thV_2020
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17581:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8721751799467101 : ℚ) / 500000000000) ≤ ((17433729024885399 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (17581:ℚ) := by decide +kernel
  have hratR : ((((8721751799467101 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((17433729024885399 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17581:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2022 : ((((8726639541321257 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17597 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17581 < q → q < 17597 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17597).mp (by decide +kernel))) hgap
  have hprev := thV_2021
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17597:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8726639541321257 : ℚ) / 500000000000) ≤ ((8721751799467101 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (17597:ℚ) := by decide +kernel
  have hratR : ((((8726639541321257 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((8721751799467101 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17597:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2023 : ((((2182881835000013 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17599 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17597 < q → q < 17599 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17599).mp (by decide +kernel))) hgap
  have hprev := thV_2022
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17599:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2182881835000013 : ℚ) / 125000000000) ≤ ((8726639541321257 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (17599:ℚ) := by decide +kernel
  have hratR : ((((2182881835000013 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((8726639541321257 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17599:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2024 : ((((698913233816417 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17609 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17599 < q → q < 17609 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17609).mp (by decide +kernel))) hgap
  have hprev := thV_2023
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17609:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((698913233816417 : ℚ) / 40000000000) ≤ ((2182881835000013 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (17609:ℚ) := by decide +kernel
  have hratR : ((((698913233816417 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((2182881835000013 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17609:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2025 : ((((349652156111057 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17623 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17609 < q → q < 17623 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17623).mp (by decide +kernel))) hgap
  have hprev := thV_2024
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17623:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((349652156111057 : ℚ) / 20000000000) ≤ ((698913233816417 : ℚ) / 40000000000) + Work.RHContract.RegionI.logLowQ (17623:ℚ) := by decide +kernel
  have hratR : ((((349652156111057 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ ((((698913233816417 : ℚ) / 40000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17623:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2026 : ((((1749238499264563 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17627 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17623 < q → q < 17627 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17627).mp (by decide +kernel))) hgap
  have hprev := thV_2025
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17627:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1749238499264563 : ℚ) / 100000000000) ≤ ((349652156111057 : ℚ) / 20000000000) + Work.RHContract.RegionI.logLowQ (17627:ℚ) := by decide +kernel
  have hratR : ((((1749238499264563 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((349652156111057 : ℚ) / 20000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17627:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2027 : ((((17502163880226293 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17657 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17627 < q → q < 17657 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17657).mp (by decide +kernel))) hgap
  have hprev := thV_2026
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17657:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((17502163880226293 : ℚ) / 1000000000000) ≤ ((1749238499264563 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (17657:ℚ) := by decide +kernel
  have hratR : ((((17502163880226293 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1749238499264563 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17657:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2028 : ((((8755971440535033 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17659 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17657 < q → q < 17659 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17659).mp (by decide +kernel))) hgap
  have hprev := thV_2027
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17659:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8755971440535033 : ℚ) / 500000000000) ≤ ((17502163880226293 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (17659:ℚ) := by decide +kernel
  have hratR : ((((8755971440535033 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((17502163880226293 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17659:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2029 : ((((17521722448037043 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17669 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17659 < q → q < 17669 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17669).mp (by decide +kernel))) hgap
  have hprev := thV_2028
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17669:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((17521722448037043 : ℚ) / 1000000000000) ≤ ((8755971440535033 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (17669:ℚ) := by decide +kernel
  have hratR : ((((17521722448037043 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((8755971440535033 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17669:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2030 : ((((17531502693929081 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17681 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17669 < q → q < 17681 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17681).mp (by decide +kernel))) hgap
  have hprev := thV_2029
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17681:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((17531502693929081 : ℚ) / 1000000000000) ≤ ((17521722448037043 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (17681:ℚ) := by decide +kernel
  have hratR : ((((17531502693929081 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((17521722448037043 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17681:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2031 : ((((274082547702039 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17683 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17681 < q → q < 17683 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17683).mp (by decide +kernel))) hgap
  have hprev := thV_2030
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17683:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((274082547702039 : ℚ) / 15625000000) ≤ ((17531502693929081 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (17683:ℚ) := by decide +kernel
  have hratR : ((((274082547702039 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ ((((17531502693929081 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17683:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2032 : ((((8775532384123731 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17707 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17683 < q → q < 17707 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17707).mp (by decide +kernel))) hgap
  have hprev := thV_2031
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17707:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8775532384123731 : ℚ) / 500000000000) ≤ ((274082547702039 : ℚ) / 15625000000) + Work.RHContract.RegionI.logLowQ (17707:ℚ) := by decide +kernel
  have hratR : ((((8775532384123731 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((274082547702039 : ℚ) / 15625000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17707:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2033 : ((((702433872894243 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17713 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17707 < q → q < 17713 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17713).mp (by decide +kernel))) hgap
  have hprev := thV_2032
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17713:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((702433872894243 : ℚ) / 40000000000) ≤ ((8775532384123731 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (17713:ℚ) := by decide +kernel
  have hratR : ((((702433872894243 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((8775532384123731 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17713:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2034 : ((((8785314889674167 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17729 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17713 < q → q < 17729 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17729).mp (by decide +kernel))) hgap
  have hprev := thV_2033
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17729:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8785314889674167 : ℚ) / 500000000000) ≤ ((702433872894243 : ℚ) / 40000000000) + Work.RHContract.RegionI.logLowQ (17729:ℚ) := by decide +kernel
  have hratR : ((((8785314889674167 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((702433872894243 : ℚ) / 40000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17729:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2035 : ((((175804131874769 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17737 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17729 < q → q < 17737 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17737).mp (by decide +kernel))) hgap
  have hprev := thV_2034
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17737:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((175804131874769 : ℚ) / 10000000000) ≤ ((8785314889674167 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (17737:ℚ) := by decide +kernel
  have hratR : ((((175804131874769 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ ((((8785314889674167 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17737:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2036 : ((((3518039431847959 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17747 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17737 < q → q < 17747 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17747).mp (by decide +kernel))) hgap
  have hprev := thV_2035
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17747:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3518039431847959 : ℚ) / 200000000000) ≤ ((175804131874769 : ℚ) / 10000000000) + Work.RHContract.RegionI.logLowQ (17747:ℚ) := by decide +kernel
  have hratR : ((((3518039431847959 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((175804131874769 : ℚ) / 10000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17747:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2037 : ((((4399995310922861 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17749 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17747 < q → q < 17749 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17749).mp (by decide +kernel))) hgap
  have hprev := thV_2036
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17749:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4399995310922861 : ℚ) / 250000000000) ≤ ((3518039431847959 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (17749:ℚ) := by decide +kernel
  have hratR : ((((4399995310922861 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((3518039431847959 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17749:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2038 : ((((1100610375250567 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17761 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17749 < q → q < 17761 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17761).mp (by decide +kernel))) hgap
  have hprev := thV_2037
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17761:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1100610375250567 : ℚ) / 62500000000) ≤ ((4399995310922861 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (17761:ℚ) := by decide +kernel
  have hratR : ((((1100610375250567 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((4399995310922861 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17761:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2039 : ((((2202444000278647 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17783 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17761 < q → q < 17783 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17783).mp (by decide +kernel))) hgap
  have hprev := thV_2038
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17783:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2202444000278647 : ℚ) / 125000000000) ≤ ((1100610375250567 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (17783:ℚ) := by decide +kernel
  have hratR : ((((2202444000278647 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((1100610375250567 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17783:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2040 : ((((8814669168896631 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17789 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17783 < q → q < 17789 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17789).mp (by decide +kernel))) hgap
  have hprev := thV_2039
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17789:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8814669168896631 : ℚ) / 500000000000) ≤ ((2202444000278647 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (17789:ℚ) := by decide +kernel
  have hratR : ((((8814669168896631 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((2202444000278647 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17789:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2041 : ((((17639124785780057 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17791 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17789 < q → q < 17791 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17791).mp (by decide +kernel))) hgap
  have hprev := thV_2040
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17791:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((17639124785780057 : ℚ) / 1000000000000) ≤ ((8814669168896631 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (17791:ℚ) := by decide +kernel
  have hratR : ((((17639124785780057 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((8814669168896631 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17791:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2042 : ((((17648912132693819 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17807 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17791 < q → q < 17807 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17807).mp (by decide +kernel))) hgap
  have hprev := thV_2041
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17807:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((17648912132693819 : ℚ) / 1000000000000) ≤ ((17639124785780057 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (17807:ℚ) := by decide +kernel
  have hratR : ((((17648912132693819 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((17639124785780057 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17807:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2043 : ((((17658700602131131 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17827 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17807 < q → q < 17827 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17827).mp (by decide +kernel))) hgap
  have hprev := thV_2042
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17827:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((17658700602131131 : ℚ) / 1000000000000) ≤ ((17648912132693819 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (17827:ℚ) := by decide +kernel
  have hratR : ((((17658700602131131 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((17648912132693819 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17827:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2044 : ((((353369792647161 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17837 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17827 < q → q < 17837 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17837).mp (by decide +kernel))) hgap
  have hprev := thV_2043
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17837:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((353369792647161 : ℚ) / 20000000000) ≤ ((17658700602131131 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (17837:ℚ) := by decide +kernel
  have hratR : ((((353369792647161 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ ((((17658700602131131 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17837:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2045 : ((((8839139387352581 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17839 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17837 < q → q < 17839 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17839).mp (by decide +kernel))) hgap
  have hprev := thV_2044
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17839:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8839139387352581 : ℚ) / 500000000000) ≤ ((353369792647161 : ℚ) / 20000000000) + Work.RHContract.RegionI.logLowQ (17839:ℚ) := by decide +kernel
  have hratR : ((((8839139387352581 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((353369792647161 : ℚ) / 20000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17839:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2046 : ((((1768806858950957 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17851 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17839 < q → q < 17851 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17851).mp (by decide +kernel))) hgap
  have hprev := thV_2045
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17851:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1768806858950957 : ℚ) / 100000000000) ≤ ((8839139387352581 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (17851:ℚ) := by decide +kernel
  have hratR : ((((1768806858950957 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((8839139387352581 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17851:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2047 : ((((17697859076319379 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17863 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17851 < q → q < 17863 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17863).mp (by decide +kernel))) hgap
  have hprev := thV_2046
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17863:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((17697859076319379 : ℚ) / 1000000000000) ≤ ((1768806858950957 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (17863:ℚ) := by decide +kernel
  have hratR : ((((17697859076319379 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1768806858950957 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17863:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2048 : ((((8853825285145657 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17881 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17863 < q → q < 17881 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17881).mp (by decide +kernel))) hgap
  have hprev := thV_2047
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17881:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8853825285145657 : ℚ) / 500000000000) ≤ ((17697859076319379 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (17881:ℚ) := by decide +kernel
  have hratR : ((((8853825285145657 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((17697859076319379 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17881:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2049 : ((((4429360655839941 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17891 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17881 < q → q < 17891 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17891).mp (by decide +kernel))) hgap
  have hprev := thV_2048
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17891:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4429360655839941 : ℚ) / 250000000000) ≤ ((8853825285145657 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (17891:ℚ) := by decide +kernel
  have hratR : ((((4429360655839941 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((8853825285145657 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17891:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2050 : ((((4431808836732919 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17903 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17891 < q → q < 17903 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17903).mp (by decide +kernel))) hgap
  have hprev := thV_2049
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17903:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4431808836732919 : ℚ) / 250000000000) ≤ ((4429360655839941 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (17903:ℚ) := by decide +kernel
  have hratR : ((((4431808836732919 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((4429360655839941 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17903:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2051 : ((((17737028405586803 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17909 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17903 < q → q < 17909 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17909).mp (by decide +kernel))) hgap
  have hprev := thV_2050
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17909:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((17737028405586803 : ℚ) / 1000000000000) ≤ ((4431808836732919 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (17909:ℚ) := by decide +kernel
  have hratR : ((((17737028405586803 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4431808836732919 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17909:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2052 : ((((17746821575911389 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17911 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17909 < q → q < 17911 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17911).mp (by decide +kernel))) hgap
  have hprev := thV_2051
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17911:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((17746821575911389 : ℚ) / 1000000000000) ≤ ((17737028405586803 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (17911:ℚ) := by decide +kernel
  have hratR : ((((17746821575911389 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((17737028405586803 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17911:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2053 : ((((17756615304396293 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17921 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17911 < q → q < 17921 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17921).mp (by decide +kernel))) hgap
  have hprev := thV_2052
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17921:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((17756615304396293 : ℚ) / 1000000000000) ≤ ((17746821575911389 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (17921:ℚ) := by decide +kernel
  have hratR : ((((17756615304396293 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((17746821575911389 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17921:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2054 : ((((3553281828895177 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17923 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17921 < q → q < 17923 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17923).mp (by decide +kernel))) hgap
  have hprev := thV_2053
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17923:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3553281828895177 : ℚ) / 200000000000) ≤ ((17756615304396293 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (17923:ℚ) := by decide +kernel
  have hratR : ((((3553281828895177 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((17756615304396293 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17923:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2055 : ((((17776203319264841 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17929 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17923 < q → q < 17929 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17929).mp (by decide +kernel))) hgap
  have hprev := thV_2054
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17929:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((17776203319264841 : ℚ) / 1000000000000) ≤ ((3553281828895177 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (17929:ℚ) := by decide +kernel
  have hratR : ((((17776203319264841 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3553281828895177 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17929:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2056 : ((((177859980516539 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17939 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17929 < q → q < 17939 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17939).mp (by decide +kernel))) hgap
  have hprev := thV_2055
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17939:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((177859980516539 : ℚ) / 10000000000) ≤ ((17776203319264841 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (17939:ℚ) := by decide +kernel
  have hratR : ((((177859980516539 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ ((((17776203319264841 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17939:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2057 : ((((8897896893470151 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17957 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17939 < q → q < 17957 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17957).mp (by decide +kernel))) hgap
  have hprev := thV_2056
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17957:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8897896893470151 : ℚ) / 500000000000) ≤ ((177859980516539 : ℚ) / 10000000000) + Work.RHContract.RegionI.logLowQ (17957:ℚ) := by decide +kernel
  have hratR : ((((8897896893470151 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((177859980516539 : ℚ) / 10000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17957:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2058 : ((((17805589633597681 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17959 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17957 < q → q < 17959 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17959).mp (by decide +kernel))) hgap
  have hprev := thV_2057
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17959:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((17805589633597681 : ℚ) / 1000000000000) ≤ ((8897896893470151 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (17959:ℚ) := by decide +kernel
  have hratR : ((((17805589633597681 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((8897896893470151 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17959:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2059 : ((((17815386148220573 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17971 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17959 < q → q < 17971 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17971).mp (by decide +kernel))) hgap
  have hprev := thV_2058
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17971:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((17815386148220573 : ℚ) / 1000000000000) ≤ ((17805589633597681 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (17971:ℚ) := by decide +kernel
  have hratR : ((((17815386148220573 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((17805589633597681 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17971:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2060 : ((((891259149832949 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17977 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17971 < q → q < 17977 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17977).mp (by decide +kernel))) hgap
  have hprev := thV_2059
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17977:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((891259149832949 : ℚ) / 50000000000) ≤ ((17815386148220573 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (17977:ℚ) := by decide +kernel
  have hratR : ((((891259149832949 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((17815386148220573 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17977:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2061 : ((((4458745016894793 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17981 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17977 < q → q < 17981 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17981).mp (by decide +kernel))) hgap
  have hprev := thV_2060
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17981:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4458745016894793 : ℚ) / 250000000000) ≤ ((891259149832949 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (17981:ℚ) := by decide +kernel
  have hratR : ((((4458745016894793 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((891259149832949 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17981:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2062 : ((((892238873606463 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17987 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17981 < q → q < 17987 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17987).mp (by decide +kernel))) hgap
  have hprev := thV_2061
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17987:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((892238873606463 : ℚ) / 50000000000) ≤ ((4458745016894793 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (17987:ℚ) := by decide +kernel
  have hratR : ((((892238873606463 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((4458745016894793 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17987:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2063 : ((((17854574987864583 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((17989 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17987 < q → q < 17989 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17989).mp (by decide +kernel))) hgap
  have hprev := thV_2062
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (17989:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((17854574987864583 : ℚ) / 1000000000000) ≤ ((892238873606463 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (17989:ℚ) := by decide +kernel
  have hratR : ((((17854574987864583 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((892238873606463 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (17989:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2064 : ((((17864373836859367 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18013 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 17989 < q → q < 18013 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18013).mp (by decide +kernel))) hgap
  have hprev := thV_2063
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18013:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((17864373836859367 : ℚ) / 1000000000000) ≤ ((17854574987864583 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (18013:ℚ) := by decide +kernel
  have hratR : ((((17864373836859367 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((17854574987864583 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18013:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2065 : ((((893708711954009 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18041 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18013 < q → q < 18041 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18041).mp (by decide +kernel))) hgap
  have hprev := thV_2064
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18041:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((893708711954009 : ℚ) / 50000000000) ≤ ((17864373836859367 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (18041:ℚ) := by decide +kernel
  have hratR : ((((893708711954009 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((17864373836859367 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18041:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2066 : ((((17883974752153449 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18043 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18041 < q → q < 18043 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18043).mp (by decide +kernel))) hgap
  have hprev := thV_2065
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18043:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((17883974752153449 : ℚ) / 1000000000000) ≤ ((893708711954009 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (18043:ℚ) := by decide +kernel
  have hratR : ((((17883974752153449 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((893708711954009 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18043:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2067 : ((((17893775486894771 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18047 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18043 < q → q < 18047 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18047).mp (by decide +kernel))) hgap
  have hprev := thV_2066
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18047:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((17893775486894771 : ℚ) / 1000000000000) ≤ ((17883974752153449 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (18047:ℚ) := by decide +kernel
  have hratR : ((((17893775486894771 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((17883974752153449 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18047:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2068 : ((((1118973520778231 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18049 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18047 < q → q < 18049 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18049).mp (by decide +kernel))) hgap
  have hprev := thV_2067
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18049:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1118973520778231 : ℚ) / 62500000000) ≤ ((17893775486894771 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (18049:ℚ) := by decide +kernel
  have hratR : ((((1118973520778231 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((17893775486894771 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18049:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2069 : ((((17913377731902509 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18059 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18049 < q → q < 18059 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18059).mp (by decide +kernel))) hgap
  have hprev := thV_2068
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18059:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((17913377731902509 : ℚ) / 1000000000000) ≤ ((1118973520778231 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (18059:ℚ) := by decide +kernel
  have hratR : ((((17913377731902509 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1118973520778231 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18059:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2070 : ((((17923179242095293 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18061 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18059 < q → q < 18061 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18061).mp (by decide +kernel))) hgap
  have hprev := thV_2069
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18061:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((17923179242095293 : ℚ) / 1000000000000) ≤ ((17913377731902509 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (18061:ℚ) := by decide +kernel
  have hratR : ((((17923179242095293 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((17913377731902509 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18061:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2071 : ((((4483245409445657 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18077 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18061 < q → q < 18077 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18077).mp (by decide +kernel))) hgap
  have hprev := thV_2070
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18077:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4483245409445657 : ℚ) / 250000000000) ≤ ((17923179242095293 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (18077:ℚ) := by decide +kernel
  have hratR : ((((4483245409445657 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((17923179242095293 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18077:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2072 : ((((1794278469707669 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18089 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18077 < q → q < 18089 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18089).mp (by decide +kernel))) hgap
  have hprev := thV_2071
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18089:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1794278469707669 : ℚ) / 100000000000) ≤ ((4483245409445657 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (18089:ℚ) := by decide +kernel
  have hratR : ((((1794278469707669 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((4483245409445657 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18089:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2073 : ((((1795258819853071 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18097 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18089 < q → q < 18097 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18097).mp (by decide +kernel))) hgap
  have hprev := thV_2072
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18097:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1795258819853071 : ℚ) / 100000000000) ≤ ((1794278469707669 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (18097:ℚ) := by decide +kernel
  have hratR : ((((1795258819853071 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((1794278469707669 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18097:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2074 : ((((8981196457458753 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18119 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18097 < q → q < 18119 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18119).mp (by decide +kernel))) hgap
  have hprev := thV_2073
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18119:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8981196457458753 : ℚ) / 500000000000) ≤ ((1795258819853071 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (18119:ℚ) := by decide +kernel
  have hratR : ((((8981196457458753 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1795258819853071 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18119:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2075 : ((((8986098870839789 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18121 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18119 < q → q < 18121 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18121).mp (by decide +kernel))) hgap
  have hprev := thV_2074
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18121:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8986098870839789 : ℚ) / 500000000000) ≤ ((8981196457458753 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (18121:ℚ) := by decide +kernel
  have hratR : ((((8986098870839789 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((8981196457458753 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18121:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2076 : ((((17982002899494401 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18127 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18121 < q → q < 18127 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18127).mp (by decide +kernel))) hgap
  have hprev := thV_2075
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18127:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((17982002899494401 : ℚ) / 1000000000000) ≤ ((8986098870839789 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (18127:ℚ) := by decide +kernel
  have hratR : ((((17982002899494401 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((8986098870839789 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18127:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2077 : ((((17991808277950187 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18131 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18127 < q → q < 18131 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18131).mp (by decide +kernel))) hgap
  have hprev := thV_2076
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18131:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((17991808277950187 : ℚ) / 1000000000000) ≤ ((17982002899494401 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (18131:ℚ) := by decide +kernel
  have hratR : ((((17991808277950187 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((17982002899494401 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18131:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2078 : ((((18001613766708201 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18133 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18131 < q → q < 18133 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18133).mp (by decide +kernel))) hgap
  have hprev := thV_2077
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18133:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((18001613766708201 : ℚ) / 1000000000000) ≤ ((17991808277950187 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (18133:ℚ) := by decide +kernel
  have hratR : ((((18001613766708201 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((17991808277950187 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18133:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2079 : ((((18011419806794931 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18143 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18133 < q → q < 18143 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18143).mp (by decide +kernel))) hgap
  have hprev := thV_2078
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18143:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((18011419806794931 : ℚ) / 1000000000000) ≤ ((18001613766708201 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (18143:ℚ) := by decide +kernel
  have hratR : ((((18011419806794931 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((18001613766708201 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18143:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2080 : ((((2252653272191631 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18149 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18143 < q → q < 18149 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18149).mp (by decide +kernel))) hgap
  have hprev := thV_2079
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18149:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2252653272191631 : ℚ) / 125000000000) ≤ ((18011419806794931 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (18149:ℚ) := by decide +kernel
  have hratR : ((((2252653272191631 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((18011419806794931 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18149:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2081 : ((((18031033649653511 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18169 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18149 < q → q < 18169 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18169).mp (by decide +kernel))) hgap
  have hprev := thV_2080
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18169:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((18031033649653511 : ℚ) / 1000000000000) ≤ ((2252653272191631 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (18169:ℚ) := by decide +kernel
  have hratR : ((((18031033649653511 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2252653272191631 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18169:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2082 : ((((18040841782021591 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18181 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18169 < q → q < 18181 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18181).mp (by decide +kernel))) hgap
  have hprev := thV_2081
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18181:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((18040841782021591 : ℚ) / 1000000000000) ≤ ((18031033649653511 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (18181:ℚ) := by decide +kernel
  have hratR : ((((18040841782021591 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((18031033649653511 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18181:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2083 : ((((18050650464263213 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18191 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18181 < q → q < 18191 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18191).mp (by decide +kernel))) hgap
  have hprev := thV_2082
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18191:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((18050650464263213 : ℚ) / 1000000000000) ≤ ((18040841782021591 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (18191:ℚ) := by decide +kernel
  have hratR : ((((18050650464263213 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((18040841782021591 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18191:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2084 : ((((9030229793093037 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18199 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18191 < q → q < 18199 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18199).mp (by decide +kernel))) hgap
  have hprev := thV_2083
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18199:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9030229793093037 : ℚ) / 500000000000) ≤ ((18050650464263213 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (18199:ℚ) := by decide +kernel
  have hratR : ((((9030229793093037 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((18050650464263213 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18199:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2085 : ((((1807026936726853 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18211 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18199 < q → q < 18211 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18211).mp (by decide +kernel))) hgap
  have hprev := thV_2084
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18211:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1807026936726853 : ℚ) / 100000000000) ≤ ((9030229793093037 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (18211:ℚ) := by decide +kernel
  have hratR : ((((1807026936726853 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((9030229793093037 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18211:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2086 : ((((18080079477767921 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18217 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18211 < q → q < 18217 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18217).mp (by decide +kernel))) hgap
  have hprev := thV_2085
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18217:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((18080079477767921 : ℚ) / 1000000000000) ≤ ((1807026936726853 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (18217:ℚ) := by decide +kernel
  have hratR : ((((18080079477767921 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1807026936726853 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18217:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2087 : ((((18089889917575767 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18223 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18217 < q → q < 18223 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18223).mp (by decide +kernel))) hgap
  have hprev := thV_2086
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18223:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((18089889917575767 : ℚ) / 1000000000000) ≤ ((18080079477767921 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (18223:ℚ) := by decide +kernel
  have hratR : ((((18089889917575767 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((18080079477767921 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18223:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2088 : ((((904985034329183 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18229 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18223 < q → q < 18229 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18229).mp (by decide +kernel))) hgap
  have hprev := thV_2087
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18229:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((904985034329183 : ℚ) / 50000000000) ≤ ((18089889917575767 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (18229:ℚ) := by decide +kernel
  have hratR : ((((904985034329183 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((18089889917575767 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18229:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2089 : ((((18109511674998059 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18233 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18229 < q → q < 18233 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18233).mp (by decide +kernel))) hgap
  have hprev := thV_2088
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18233:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((18109511674998059 : ℚ) / 1000000000000) ≤ ((904985034329183 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (18233:ℚ) := by decide +kernel
  have hratR : ((((18109511674998059 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((904985034329183 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18233:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2090 : ((((18119323650146449 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18251 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18233 < q → q < 18251 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18251).mp (by decide +kernel))) hgap
  have hprev := thV_2089
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18251:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((18119323650146449 : ℚ) / 1000000000000) ≤ ((18109511674998059 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (18251:ℚ) := by decide +kernel
  have hratR : ((((18119323650146449 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((18109511674998059 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18251:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2091 : ((((283267745857373 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18253 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18251 < q → q < 18253 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18253).mp (by decide +kernel))) hgap
  have hprev := thV_2090
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18253:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((283267745857373 : ℚ) / 15625000000) ≤ ((18119323650146449 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (18253:ℚ) := by decide +kernel
  have hratR : ((((283267745857373 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ ((((18119323650146449 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18253:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2092 : ((((9069474019357673 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18257 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18253 < q → q < 18257 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18257).mp (by decide +kernel))) hgap
  have hprev := thV_2091
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18257:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9069474019357673 : ℚ) / 500000000000) ≤ ((283267745857373 : ℚ) / 15625000000) + Work.RHContract.RegionI.logLowQ (18257:ℚ) := by decide +kernel
  have hratR : ((((9069474019357673 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((283267745857373 : ℚ) / 15625000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18257:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2093 : ((((18148760999625043 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18269 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18257 < q → q < 18269 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18269).mp (by decide +kernel))) hgap
  have hprev := thV_2092
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18269:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((18148760999625043 : ℚ) / 1000000000000) ≤ ((9069474019357673 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (18269:ℚ) := by decide +kernel
  have hratR : ((((18148760999625043 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((9069474019357673 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18269:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2094 : ((((9079287472662639 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18287 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18269 < q → q < 18287 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18287).mp (by decide +kernel))) hgap
  have hprev := thV_2093
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18287:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9079287472662639 : ℚ) / 500000000000) ≤ ((18148760999625043 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (18287:ℚ) := by decide +kernel
  have hratR : ((((9079287472662639 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((18148760999625043 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18287:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2095 : ((((18168389000386843 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18289 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18287 < q → q < 18289 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18289).mp (by decide +kernel))) hgap
  have hprev := thV_2094
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18289:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((18168389000386843 : ℚ) / 1000000000000) ≤ ((9079287472662639 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (18289:ℚ) := by decide +kernel
  have hratR : ((((18168389000386843 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((9079287472662639 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18289:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2096 : ((((18178203711365349 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18301 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18289 < q → q < 18301 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18301).mp (by decide +kernel))) hgap
  have hprev := thV_2095
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18301:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((18178203711365349 : ℚ) / 1000000000000) ≤ ((18168389000386843 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (18301:ℚ) := by decide +kernel
  have hratR : ((((18178203711365349 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((18168389000386843 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18301:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2097 : ((((909400937507053 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18307 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18301 < q → q < 18307 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18307).mp (by decide +kernel))) hgap
  have hprev := thV_2096
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18307:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((909400937507053 : ℚ) / 50000000000) ≤ ((18178203711365349 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (18307:ℚ) := by decide +kernel
  have hratR : ((((909400937507053 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((18178203711365349 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18307:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2098 : ((((9098917003694281 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18311 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18307 < q → q < 18311 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18311).mp (by decide +kernel))) hgap
  have hprev := thV_2097
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18311:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9098917003694281 : ℚ) / 500000000000) ≤ ((909400937507053 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (18311:ℚ) := by decide +kernel
  have hratR : ((((9098917003694281 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((909400937507053 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18311:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2099 : ((((18207649373854063 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18313 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18311 < q → q < 18313 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18313).mp (by decide +kernel))) hgap
  have hprev := thV_2098
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18313:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((18207649373854063 : ℚ) / 1000000000000) ≤ ((9098917003694281 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (18313:ℚ) := by decide +kernel
  have hratR : ((((18207649373854063 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((9098917003694281 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18313:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2100 : ((((3643493122726879 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18329 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18313 < q → q < 18329 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18329).mp (by decide +kernel))) hgap
  have hprev := thV_2099
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18329:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3643493122726879 : ℚ) / 200000000000) ≤ ((18207649373854063 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (18329:ℚ) := by decide +kernel
  have hratR : ((((3643493122726879 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((18207649373854063 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18329:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2101 : ((((9113641253950353 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18341 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18329 < q → q < 18341 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18341).mp (by decide +kernel))) hgap
  have hprev := thV_2100
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18341:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9113641253950353 : ℚ) / 500000000000) ≤ ((3643493122726879 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (18341:ℚ) := by decide +kernel
  have hratR : ((((9113641253950353 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((3643493122726879 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18341:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2102 : ((((729484002248997 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18353 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18341 < q → q < 18353 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18353).mp (by decide +kernel))) hgap
  have hprev := thV_2101
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18353:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((729484002248997 : ℚ) / 40000000000) ≤ ((9113641253950353 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (18353:ℚ) := by decide +kernel
  have hratR : ((((729484002248997 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((9113641253950353 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18353:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2103 : ((((9123459183538207 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18367 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18353 < q → q < 18367 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18367).mp (by decide +kernel))) hgap
  have hprev := thV_2102
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18367:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9123459183538207 : ℚ) / 500000000000) ≤ ((729484002248997 : ℚ) / 40000000000) + Work.RHContract.RegionI.logLowQ (18367:ℚ) := by decide +kernel
  have hratR : ((((9123459183538207 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((729484002248997 : ℚ) / 40000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18367:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2104 : ((((18256736895686083 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18371 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18367 < q → q < 18371 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18371).mp (by decide +kernel))) hgap
  have hprev := thV_2103
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18371:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((18256736895686083 : ℚ) / 1000000000000) ≤ ((9123459183538207 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (18371:ℚ) := by decide +kernel
  have hratR : ((((18256736895686083 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((9123459183538207 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18371:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2105 : ((((18266555859669909 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18379 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18371 < q → q < 18379 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18379).mp (by decide +kernel))) hgap
  have hprev := thV_2104
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18379:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((18266555859669909 : ℚ) / 1000000000000) ≤ ((18256736895686083 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (18379:ℚ) := by decide +kernel
  have hratR : ((((18266555859669909 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((18256736895686083 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18379:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2106 : ((((3655275160510619 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18397 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18379 < q → q < 18397 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18397).mp (by decide +kernel))) hgap
  have hprev := thV_2105
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18397:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3655275160510619 : ℚ) / 200000000000) ≤ ((18266555859669909 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (18397:ℚ) := by decide +kernel
  have hratR : ((((3655275160510619 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((18266555859669909 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18397:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2107 : ((((9143097981419701 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18401 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18397 < q → q < 18401 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18401).mp (by decide +kernel))) hgap
  have hprev := thV_2106
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18401:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9143097981419701 : ℚ) / 500000000000) ≤ ((3655275160510619 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (18401:ℚ) := by decide +kernel
  have hratR : ((((9143097981419701 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((3655275160510619 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18401:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2108 : ((((18296016775051629 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18413 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18401 < q → q < 18413 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18413).mp (by decide +kernel))) hgap
  have hprev := thV_2107
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18413:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((18296016775051629 : ℚ) / 1000000000000) ≤ ((9143097981419701 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (18413:ℚ) := by decide +kernel
  have hratR : ((((18296016775051629 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((9143097981419701 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18413:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2109 : ((((4576459586826831 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18427 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18413 < q → q < 18427 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18427).mp (by decide +kernel))) hgap
  have hprev := thV_2108
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18427:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4576459586826831 : ℚ) / 250000000000) ≤ ((18296016775051629 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (18427:ℚ) := by decide +kernel
  have hratR : ((((4576459586826831 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((18296016775051629 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18427:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2110 : ((((915783012255959 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18433 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18427 < q → q < 18433 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18433).mp (by decide +kernel))) hgap
  have hprev := thV_2109
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18433:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((915783012255959 : ℚ) / 50000000000) ≤ ((4576459586826831 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (18433:ℚ) := by decide +kernel
  have hratR : ((((915783012255959 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((4576459586826831 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18433:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2111 : ((((3665096493676249 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18439 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18433 < q → q < 18439 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18439).mp (by decide +kernel))) hgap
  have hprev := thV_2110
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18439:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3665096493676249 : ℚ) / 200000000000) ≤ ((915783012255959 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (18439:ℚ) := by decide +kernel
  have hratR : ((((3665096493676249 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((915783012255959 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18439:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2112 : ((((2291913113568911 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18443 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18439 < q → q < 18443 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18443).mp (by decide +kernel))) hgap
  have hprev := thV_2111
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18443:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2291913113568911 : ℚ) / 125000000000) ≤ ((3665096493676249 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (18443:ℚ) := by decide +kernel
  have hratR : ((((2291913113568911 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((3665096493676249 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18443:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2113 : ((((1834512778239619 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18451 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18443 < q → q < 18451 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18451).mp (by decide +kernel))) hgap
  have hprev := thV_2112
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18451:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1834512778239619 : ℚ) / 100000000000) ≤ ((2291913113568911 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (18451:ℚ) := by decide +kernel
  have hratR : ((((1834512778239619 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((2291913113568911 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18451:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2114 : ((((9177475490686929 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18457 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18451 < q → q < 18457 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18457).mp (by decide +kernel))) hgap
  have hprev := thV_2113
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18457:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9177475490686929 : ℚ) / 500000000000) ≤ ((1834512778239619 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (18457:ℚ) := by decide +kernel
  have hratR : ((((9177475490686929 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1834512778239619 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18457:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2115 : ((((18364774397047989 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18461 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18457 < q → q < 18461 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18461).mp (by decide +kernel))) hgap
  have hprev := thV_2114
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18461:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((18364774397047989 : ℚ) / 1000000000000) ≤ ((9177475490686929 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (18461:ℚ) := by decide +kernel
  have hratR : ((((18364774397047989 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((9177475490686929 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18461:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2116 : ((((3674919779100127 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18481 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18461 < q → q < 18481 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18481).mp (by decide +kernel))) hgap
  have hprev := thV_2115
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18481:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3674919779100127 : ℚ) / 200000000000) ≤ ((18364774397047989 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (18481:ℚ) := by decide +kernel
  have hratR : ((((3674919779100127 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((18364774397047989 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18481:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2117 : ((((114902650269113 : ℚ) / 6250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18493 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18481 < q → q < 18493 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18493).mp (by decide +kernel))) hgap
  have hprev := thV_2116
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18493:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((114902650269113 : ℚ) / 6250000000) ≤ ((3674919779100127 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (18493:ℚ) := by decide +kernel
  have hratR : ((((114902650269113 : ℚ) / 6250000000) : ℚ) : ℝ) ≤ ((((3674919779100127 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18493:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2118 : ((((9197124865607261 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18503 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18493 < q → q < 18503 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18503).mp (by decide +kernel))) hgap
  have hprev := thV_2117
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18503:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9197124865607261 : ℚ) / 500000000000) ≤ ((114902650269113 : ℚ) / 6250000000) + Work.RHContract.RegionI.logLowQ (18503:ℚ) := by decide +kernel
  have hratR : ((((9197124865607261 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((114902650269113 : ℚ) / 6250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18503:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2119 : ((((460101904392973 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18517 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18503 < q → q < 18517 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18517).mp (by decide +kernel))) hgap
  have hprev := thV_2118
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18517:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((460101904392973 : ℚ) / 25000000000) ≤ ((9197124865607261 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (18517:ℚ) := by decide +kernel
  have hratR : ((((460101904392973 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((9197124865607261 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18517:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2120 : ((((18413902836217703 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18521 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18517 < q → q < 18521 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18521).mp (by decide +kernel))) hgap
  have hprev := thV_2119
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18521:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((18413902836217703 : ℚ) / 1000000000000) ≤ ((460101904392973 : ℚ) / 25000000000) + Work.RHContract.RegionI.logLowQ (18521:ℚ) := by decide +kernel
  have hratR : ((((18413902836217703 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((460101904392973 : ℚ) / 25000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18521:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2121 : ((((9211864802348093 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18523 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18521 < q → q < 18523 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18523).mp (by decide +kernel))) hgap
  have hprev := thV_2120
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18523:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9211864802348093 : ℚ) / 500000000000) ≤ ((18413902836217703 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (18523:ℚ) := by decide +kernel
  have hratR : ((((9211864802348093 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((18413902836217703 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18523:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2122 : ((((18433557236592779 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18539 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18523 < q → q < 18539 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18539).mp (by decide +kernel))) hgap
  have hprev := thV_2121
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18539:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((18433557236592779 : ℚ) / 1000000000000) ≤ ((9211864802348093 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (18539:ℚ) := by decide +kernel
  have hratR : ((((18433557236592779 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((9211864802348093 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18539:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2123 : ((((18443384976364237 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18541 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18539 < q → q < 18541 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18541).mp (by decide +kernel))) hgap
  have hprev := thV_2122
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18541:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((18443384976364237 : ℚ) / 1000000000000) ≤ ((18433557236592779 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (18541:ℚ) := by decide +kernel
  have hratR : ((((18443384976364237 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((18433557236592779 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18541:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2124 : ((((1153325835196289 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18553 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18541 < q → q < 18553 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18553).mp (by decide +kernel))) hgap
  have hprev := thV_2123
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18553:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1153325835196289 : ℚ) / 62500000000) ≤ ((18443384976364237 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (18553:ℚ) := by decide +kernel
  have hratR : ((((1153325835196289 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((18443384976364237 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18553:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2125 : ((((9231521682800129 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18583 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18553 < q → q < 18583 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18583).mp (by decide +kernel))) hgap
  have hprev := thV_2124
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18583:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9231521682800129 : ℚ) / 500000000000) ≤ ((1153325835196289 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (18583:ℚ) := by decide +kernel
  have hratR : ((((9231521682800129 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1153325835196289 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18583:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2126 : ((((18472873583287227 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18587 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18583 < q → q < 18587 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18587).mp (by decide +kernel))) hgap
  have hprev := thV_2125
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18587:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((18472873583287227 : ℚ) / 1000000000000) ≤ ((9231521682800129 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (18587:ℚ) := by decide +kernel
  have hratR : ((((18472873583287227 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((9231521682800129 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18587:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2127 : ((((18482704123728367 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18593 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18587 < q → q < 18593 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18593).mp (by decide +kernel))) hgap
  have hprev := thV_2126
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18593:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((18482704123728367 : ℚ) / 1000000000000) ≤ ((18472873583287227 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (18593:ℚ) := by decide +kernel
  have hratR : ((((18482704123728367 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((18472873583287227 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18593:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2128 : ((((18492535954145499 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18617 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18593 < q → q < 18617 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18617).mp (by decide +kernel))) hgap
  have hprev := thV_2127
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18617:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((18492535954145499 : ℚ) / 1000000000000) ≤ ((18482704123728367 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (18617:ℚ) := by decide +kernel
  have hratR : ((((18492535954145499 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((18482704123728367 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18617:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2129 : ((((925118442913647 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18637 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18617 < q → q < 18637 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18637).mp (by decide +kernel))) hgap
  have hprev := thV_2128
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18637:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((925118442913647 : ℚ) / 50000000000) ≤ ((18492535954145499 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (18637:ℚ) := by decide +kernel
  have hratR : ((((925118442913647 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((18492535954145499 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18637:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2130 : ((((9256101524666417 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18661 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18637 < q → q < 18661 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18661).mp (by decide +kernel))) hgap
  have hprev := thV_2129
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18661:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9256101524666417 : ℚ) / 500000000000) ≤ ((925118442913647 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (18661:ℚ) := by decide +kernel
  have hratR : ((((9256101524666417 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((925118442913647 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18661:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2131 : ((((231525472201577 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18671 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18661 < q → q < 18671 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18671).mp (by decide +kernel))) hgap
  have hprev := thV_2130
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18671:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((231525472201577 : ℚ) / 12500000000) ≤ ((9256101524666417 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (18671:ℚ) := by decide +kernel
  have hratR : ((((231525472201577 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ ((((9256101524666417 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18671:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2132 : ((((115824205820623 : ℚ) / 6250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18679 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18671 < q → q < 18679 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18679).mp (by decide +kernel))) hgap
  have hprev := thV_2131
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18679:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((115824205820623 : ℚ) / 6250000000) ≤ ((231525472201577 : ℚ) / 12500000000) + Work.RHContract.RegionI.logLowQ (18679:ℚ) := by decide +kernel
  have hratR : ((((115824205820623 : ℚ) / 6250000000) : ℚ) : ℝ) ≤ ((((231525472201577 : ℚ) / 12500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18679:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2133 : ((((9270854364349803 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18691 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18679 < q → q < 18691 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18691).mp (by decide +kernel))) hgap
  have hprev := thV_2132
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18691:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9270854364349803 : ℚ) / 500000000000) ≤ ((115824205820623 : ℚ) / 6250000000) + Work.RHContract.RegionI.logLowQ (18691:ℚ) := by decide +kernel
  have hratR : ((((9270854364349803 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((115824205820623 : ℚ) / 6250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18691:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2134 : ((((3710309012194663 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18701 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18691 < q → q < 18701 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18701).mp (by decide +kernel))) hgap
  have hprev := thV_2133
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18701:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3710309012194663 : ℚ) / 200000000000) ≤ ((9270854364349803 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (18701:ℚ) := by decide +kernel
  have hratR : ((((3710309012194663 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((9270854364349803 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18701:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2135 : ((((18561382034718153 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18713 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18701 < q → q < 18713 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18713).mp (by decide +kernel))) hgap
  have hprev := thV_2134
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18713:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((18561382034718153 : ℚ) / 1000000000000) ≤ ((3710309012194663 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (18713:ℚ) := by decide +kernel
  have hratR : ((((18561382034718153 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3710309012194663 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18713:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2136 : ((((3714243865808863 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18719 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18713 < q → q < 18719 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18719).mp (by decide +kernel))) hgap
  have hprev := thV_2135
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18719:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3714243865808863 : ℚ) / 200000000000) ≤ ((18561382034718153 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (18719:ℚ) := by decide +kernel
  have hratR : ((((3714243865808863 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((18561382034718153 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18719:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2137 : ((((18581057264224971 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18731 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18719 < q → q < 18731 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18731).mp (by decide +kernel))) hgap
  have hprev := thV_2136
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18731:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((18581057264224971 : ℚ) / 1000000000000) ≤ ((3714243865808863 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (18731:ℚ) := by decide +kernel
  have hratR : ((((18581057264224971 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3714243865808863 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18731:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2138 : ((((1859089583984969 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18743 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18731 < q → q < 18743 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18743).mp (by decide +kernel))) hgap
  have hprev := thV_2137
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18743:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1859089583984969 : ℚ) / 100000000000) ≤ ((18581057264224971 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (18743:ℚ) := by decide +kernel
  have hratR : ((((1859089583984969 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((18581057264224971 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18743:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2139 : ((((18600734735542693 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18749 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18743 < q → q < 18749 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18749).mp (by decide +kernel))) hgap
  have hprev := thV_2138
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18749:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((18600734735542693 : ℚ) / 1000000000000) ≤ ((1859089583984969 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (18749:ℚ) := by decide +kernel
  have hratR : ((((18600734735542693 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1859089583984969 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18749:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2140 : ((((9305287028917057 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18757 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18749 < q → q < 18757 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18757).mp (by decide +kernel))) hgap
  have hprev := thV_2139
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18757:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9305287028917057 : ℚ) / 500000000000) ≤ ((18600734735542693 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (18757:ℚ) := by decide +kernel
  have hratR : ((((9305287028917057 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((18600734735542693 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18757:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2141 : ((((18620414232776799 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18773 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18757 < q → q < 18773 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18773).mp (by decide +kernel))) hgap
  have hprev := thV_2140
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18773:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((18620414232776799 : ℚ) / 1000000000000) ≤ ((9305287028917057 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (18773:ℚ) := by decide +kernel
  have hratR : ((((18620414232776799 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((9305287028917057 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18773:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2142 : ((((18630255153193427 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18787 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18773 < q → q < 18787 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18787).mp (by decide +kernel))) hgap
  have hprev := thV_2141
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18787:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((18630255153193427 : ℚ) / 1000000000000) ≤ ((18620414232776799 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (18787:ℚ) := by decide +kernel
  have hratR : ((((18630255153193427 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((18620414232776799 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18787:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2143 : ((((4660024098232211 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18793 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18787 < q → q < 18793 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18793).mp (by decide +kernel))) hgap
  have hprev := thV_2142
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18793:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4660024098232211 : ℚ) / 250000000000) ≤ ((18630255153193427 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (18793:ℚ) := by decide +kernel
  have hratR : ((((4660024098232211 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((18630255153193427 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18793:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2144 : ((((18649937845486821 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18797 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18793 < q → q < 18797 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18797).mp (by decide +kernel))) hgap
  have hprev := thV_2143
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18797:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((18649937845486821 : ℚ) / 1000000000000) ≤ ((4660024098232211 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (18797:ℚ) := by decide +kernel
  have hratR : ((((18649937845486821 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4660024098232211 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18797:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2145 : ((((18659779617193737 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18803 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18797 < q → q < 18803 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18803).mp (by decide +kernel))) hgap
  have hprev := thV_2144
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18803:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((18659779617193737 : ℚ) / 1000000000000) ≤ ((18649937845486821 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (18803:ℚ) := by decide +kernel
  have hratR : ((((18659779617193737 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((18649937845486821 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18803:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2146 : ((((18669623301658263 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18839 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18803 < q → q < 18839 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18839).mp (by decide +kernel))) hgap
  have hprev := thV_2145
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18839:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((18669623301658263 : ℚ) / 1000000000000) ≤ ((18659779617193737 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (18839:ℚ) := by decide +kernel
  have hratR : ((((18669623301658263 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((18659779617193737 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18839:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2147 : ((((291866688237299 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18859 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18839 < q → q < 18859 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18859).mp (by decide +kernel))) hgap
  have hprev := thV_2146
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18859:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((291866688237299 : ℚ) / 15625000000) ≤ ((18669623301658263 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (18859:ℚ) := by decide +kernel
  have hratR : ((((291866688237299 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ ((((18669623301658263 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18859:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2148 : ((((4672328330706571 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18869 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18859 < q → q < 18869 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18869).mp (by decide +kernel))) hgap
  have hprev := thV_2147
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18869:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4672328330706571 : ℚ) / 250000000000) ≤ ((291866688237299 : ℚ) / 15625000000) + Work.RHContract.RegionI.logLowQ (18869:ℚ) := by decide +kernel
  have hratR : ((((4672328330706571 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((291866688237299 : ℚ) / 15625000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18869:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2149 : ((((18699160187112239 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18899 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18869 < q → q < 18899 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18899).mp (by decide +kernel))) hgap
  have hprev := thV_2148
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18899:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((18699160187112239 : ℚ) / 1000000000000) ≤ ((4672328330706571 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (18899:ℚ) := by decide +kernel
  have hratR : ((((18699160187112239 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4672328330706571 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18899:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2150 : ((((18709007686150927 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18911 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18899 < q → q < 18911 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18911).mp (by decide +kernel))) hgap
  have hprev := thV_2149
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18911:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((18709007686150927 : ℚ) / 1000000000000) ≤ ((18699160187112239 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (18911:ℚ) := by decide +kernel
  have hratR : ((((18709007686150927 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((18699160187112239 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18911:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2151 : ((((1169928455683911 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18913 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18911 < q → q < 18913 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18913).mp (by decide +kernel))) hgap
  have hprev := thV_2150
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18913:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1169928455683911 : ℚ) / 62500000000) ≤ ((18709007686150927 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (18913:ℚ) := by decide +kernel
  have hratR : ((((1169928455683911 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((18709007686150927 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18913:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2152 : ((((9364351553603301 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18917 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18913 < q → q < 18917 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18917).mp (by decide +kernel))) hgap
  have hprev := thV_2151
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18917:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9364351553603301 : ℚ) / 500000000000) ≤ ((1169928455683911 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (18917:ℚ) := by decide +kernel
  have hratR : ((((9364351553603301 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1169928455683911 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18917:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2153 : ((((18738551029190049 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18919 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18917 < q → q < 18919 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18919).mp (by decide +kernel))) hgap
  have hprev := thV_2152
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18919:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((18738551029190049 : ℚ) / 1000000000000) ≤ ((9364351553603301 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (18919:ℚ) := by decide +kernel
  have hratR : ((((18738551029190049 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((9364351553603301 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18919:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2154 : ((((9374200215036521 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18947 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18919 < q → q < 18947 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18947).mp (by decide +kernel))) hgap
  have hprev := thV_2153
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18947:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9374200215036521 : ℚ) / 500000000000) ≤ ((18738551029190049 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (18947:ℚ) := by decide +kernel
  have hratR : ((((9374200215036521 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((18738551029190049 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18947:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2155 : ((((4689562616025301 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18959 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18947 < q → q < 18959 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18959).mp (by decide +kernel))) hgap
  have hprev := thV_2154
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18959:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4689562616025301 : ℚ) / 250000000000) ≤ ((9374200215036521 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (18959:ℚ) := by decide +kernel
  have hratR : ((((4689562616025301 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((9374200215036521 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18959:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2156 : ((((4692025309073107 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18973 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18959 < q → q < 18973 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18973).mp (by decide +kernel))) hgap
  have hprev := thV_2155
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18973:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4692025309073107 : ℚ) / 250000000000) ≤ ((4689562616025301 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (18973:ℚ) := by decide +kernel
  have hratR : ((((4692025309073107 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((4689562616025301 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18973:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2157 : ((((751118092986901 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((18979 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18973 < q → q < 18979 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18979).mp (by decide +kernel))) hgap
  have hprev := thV_2156
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (18979:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((751118092986901 : ℚ) / 40000000000) ≤ ((4692025309073107 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (18979:ℚ) := by decide +kernel
  have hratR : ((((751118092986901 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((4692025309073107 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (18979:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2158 : ((((4696951142889307 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19001 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 18979 < q → q < 19001 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19001).mp (by decide +kernel))) hgap
  have hprev := thV_2157
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19001:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4696951142889307 : ℚ) / 250000000000) ≤ ((751118092986901 : ℚ) / 40000000000) + Work.RHContract.RegionI.logLowQ (19001:ℚ) := by decide +kernel
  have hratR : ((((4696951142889307 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((751118092986901 : ℚ) / 40000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19001:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2159 : ((((9398828619691897 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19009 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19001 < q → q < 19009 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19009).mp (by decide +kernel))) hgap
  have hprev := thV_2158
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19009:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9398828619691897 : ℚ) / 500000000000) ≤ ((4696951142889307 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (19009:ℚ) := by decide +kernel
  have hratR : ((((9398828619691897 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((4696951142889307 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19009:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2160 : ((((1175469382350929 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19013 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19009 < q → q < 19013 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19013).mp (by decide +kernel))) hgap
  have hprev := thV_2159
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19013:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1175469382350929 : ℚ) / 62500000000) ≤ ((9398828619691897 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (19013:ℚ) := by decide +kernel
  have hratR : ((((1175469382350929 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((9398828619691897 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19013:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2161 : ((((18817363942118741 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19031 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19013 < q → q < 19031 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19031).mp (by decide +kernel))) hgap
  have hprev := thV_2160
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19031:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((18817363942118741 : ℚ) / 1000000000000) ≤ ((1175469382350929 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (19031:ℚ) := by decide +kernel
  have hratR : ((((18817363942118741 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1175469382350929 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19031:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2162 : ((((18827218081848007 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19037 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19031 < q → q < 19037 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19037).mp (by decide +kernel))) hgap
  have hprev := thV_2161
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19037:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((18827218081848007 : ℚ) / 1000000000000) ≤ ((18817363942118741 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (19037:ℚ) := by decide +kernel
  have hratR : ((((18827218081848007 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((18817363942118741 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19037:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2163 : ((((18837072956716983 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19051 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19037 < q → q < 19051 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19051).mp (by decide +kernel))) hgap
  have hprev := thV_2162
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19051:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((18837072956716983 : ℚ) / 1000000000000) ≤ ((18827218081848007 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (19051:ℚ) := by decide +kernel
  have hratR : ((((18837072956716983 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((18827218081848007 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19051:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2164 : ((((9423464387986089 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19069 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19051 < q → q < 19069 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19069).mp (by decide +kernel))) hgap
  have hprev := thV_2163
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19069:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9423464387986089 : ℚ) / 500000000000) ≤ ((18837072956716983 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (19069:ℚ) := by decide +kernel
  have hratR : ((((9423464387986089 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((18837072956716983 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19069:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2165 : ((((3771356960993983 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19073 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19069 < q → q < 19073 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19073).mp (by decide +kernel))) hgap
  have hprev := thV_2164
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19073:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3771356960993983 : ℚ) / 200000000000) ≤ ((9423464387986089 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (19073:ℚ) := by decide +kernel
  have hratR : ((((3771356960993983 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((9423464387986089 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19073:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2166 : ((((18866641148499003 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19079 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19073 < q → q < 19079 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19079).mp (by decide +kernel))) hgap
  have hprev := thV_2165
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19079:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((18866641148499003 : ℚ) / 1000000000000) ≤ ((3771356960993983 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (19079:ℚ) := by decide +kernel
  have hratR : ((((18866641148499003 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3771356960993983 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19079:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2167 : ((((9438248798424947 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19081 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19079 < q → q < 19081 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19081).mp (by decide +kernel))) hgap
  have hprev := thV_2166
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19081:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9438248798424947 : ℚ) / 500000000000) ≤ ((18866641148499003 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (19081:ℚ) := by decide +kernel
  have hratR : ((((9438248798424947 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((18866641148499003 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19081:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2168 : ((((4721588589900071 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19087 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19081 < q → q < 19087 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19087).mp (by decide +kernel))) hgap
  have hprev := thV_2167
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19087:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4721588589900071 : ℚ) / 250000000000) ≤ ((9438248798424947 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (19087:ℚ) := by decide +kernel
  have hratR : ((((4721588589900071 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((9438248798424947 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19087:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2169 : ((((18896212902083137 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19121 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19087 < q → q < 19121 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19121).mp (by decide +kernel))) hgap
  have hprev := thV_2168
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19121:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((18896212902083137 : ℚ) / 1000000000000) ≤ ((4721588589900071 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (19121:ℚ) := by decide +kernel
  have hratR : ((((18896212902083137 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4721588589900071 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19121:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2170 : ((((3781214477099307 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19139 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19121 < q → q < 19139 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19139).mp (by decide +kernel))) hgap
  have hprev := thV_2169
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19139:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3781214477099307 : ℚ) / 200000000000) ≤ ((18896212902083137 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (19139:ℚ) := by decide +kernel
  have hratR : ((((3781214477099307 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((18896212902083137 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19139:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2171 : ((((18915931973403141 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19141 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19139 < q → q < 19141 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19141).mp (by decide +kernel))) hgap
  have hprev := thV_2170
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19141:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((18915931973403141 : ℚ) / 1000000000000) ≤ ((3781214477099307 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (19141:ℚ) := by decide +kernel
  have hratR : ((((18915931973403141 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3781214477099307 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19141:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2172 : ((((9462896198431283 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19157 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19141 < q → q < 19157 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19157).mp (by decide +kernel))) hgap
  have hprev := thV_2171
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19157:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9462896198431283 : ℚ) / 500000000000) ≤ ((18915931973403141 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (19157:ℚ) := by decide +kernel
  have hratR : ((((9462896198431283 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((18915931973403141 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19157:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2173 : ((((3787130626694879 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19163 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19157 < q → q < 19163 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19163).mp (by decide +kernel))) hgap
  have hprev := thV_2172
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19163:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3787130626694879 : ℚ) / 200000000000) ≤ ((9462896198431283 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (19163:ℚ) := by decide +kernel
  have hratR : ((((3787130626694879 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((9462896198431283 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19163:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2174 : ((((18945514808955477 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19181 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19163 < q → q < 19181 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19181).mp (by decide +kernel))) hgap
  have hprev := thV_2173
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19181:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((18945514808955477 : ℚ) / 1000000000000) ≤ ((3787130626694879 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (19181:ℚ) := by decide +kernel
  have hratR : ((((18945514808955477 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3787130626694879 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19181:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2175 : ((((9477688294350487 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19183 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19181 < q → q < 19183 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19183).mp (by decide +kernel))) hgap
  have hprev := thV_2174
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19183:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9477688294350487 : ℚ) / 500000000000) ≤ ((18945514808955477 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (19183:ℚ) := by decide +kernel
  have hratR : ((((9477688294350487 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((18945514808955477 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19183:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2176 : ((((18965239618772239 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19207 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19183 < q → q < 19207 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19207).mp (by decide +kernel))) hgap
  have hprev := thV_2175
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19207:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((18965239618772239 : ℚ) / 1000000000000) ≤ ((9477688294350487 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (19207:ℚ) := by decide +kernel
  have hratR : ((((18965239618772239 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((9477688294350487 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19207:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2177 : ((((4743775714269807 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19211 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19207 < q → q < 19211 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19211).mp (by decide +kernel))) hgap
  have hprev := thV_2176
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19211:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4743775714269807 : ℚ) / 250000000000) ≤ ((18965239618772239 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (19211:ℚ) := by decide +kernel
  have hratR : ((((4743775714269807 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((18965239618772239 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19211:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2178 : ((((949248309974391 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19213 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19211 < q → q < 19213 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19213).mp (by decide +kernel))) hgap
  have hprev := thV_2177
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19213:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((949248309974391 : ℚ) / 50000000000) ≤ ((4743775714269807 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (19213:ℚ) := by decide +kernel
  have hratR : ((((949248309974391 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((4743775714269807 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19213:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2179 : ((((3798965970827243 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19219 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19213 < q → q < 19219 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19219).mp (by decide +kernel))) hgap
  have hprev := thV_2178
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19219:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3798965970827243 : ℚ) / 200000000000) ≤ ((949248309974391 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (19219:ℚ) := by decide +kernel
  have hratR : ((((3798965970827243 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((949248309974391 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19219:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2180 : ((((9502347066485943 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19231 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19219 < q → q < 19231 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19231).mp (by decide +kernel))) hgap
  have hprev := thV_2179
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19231:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9502347066485943 : ℚ) / 500000000000) ≤ ((3798965970827243 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (19231:ℚ) := by decide +kernel
  have hratR : ((((9502347066485943 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((3798965970827243 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19231:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2181 : ((((1188409920234697 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19237 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19231 < q → q < 19237 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19237).mp (by decide +kernel))) hgap
  have hprev := thV_2180
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19237:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1188409920234697 : ℚ) / 62500000000) ≤ ((9502347066485943 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (19237:ℚ) := by decide +kernel
  have hratR : ((((1188409920234697 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((9502347066485943 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19237:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2182 : ((((19024423938141827 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19249 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19237 < q → q < 19249 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19249).mp (by decide +kernel))) hgap
  have hprev := thV_2181
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19249:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((19024423938141827 : ℚ) / 1000000000000) ≤ ((1188409920234697 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (19249:ℚ) := by decide +kernel
  have hratR : ((((19024423938141827 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1188409920234697 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19249:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2183 : ((((19034289671901111 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19259 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19249 < q → q < 19259 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19259).mp (by decide +kernel))) hgap
  have hprev := thV_2182
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19259:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((19034289671901111 : ℚ) / 1000000000000) ≤ ((19024423938141827 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (19259:ℚ) := by decide +kernel
  have hratR : ((((19034289671901111 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((19024423938141827 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19259:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2184 : ((((37195616837821 : ℚ) / 1953125000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19267 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19259 < q → q < 19267 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19267).mp (by decide +kernel))) hgap
  have hprev := thV_2183
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19267:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((37195616837821 : ℚ) / 1953125000) ≤ ((19034289671901111 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (19267:ℚ) := by decide +kernel
  have hratR : ((((37195616837821 : ℚ) / 1953125000) : ℚ) : ℝ) ≤ ((((19034289671901111 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19267:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2185 : ((((19054022281392411 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19273 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19267 < q → q < 19273 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19273).mp (by decide +kernel))) hgap
  have hprev := thV_2184
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19273:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((19054022281392411 : ℚ) / 1000000000000) ≤ ((37195616837821 : ℚ) / 1953125000) + Work.RHContract.RegionI.logLowQ (19273:ℚ) := by decide +kernel
  have hratR : ((((19054022281392411 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((37195616837821 : ℚ) / 1953125000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19273:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2186 : ((((4765972392913249 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19289 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19273 < q → q < 19289 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19289).mp (by decide +kernel))) hgap
  have hprev := thV_2185
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19289:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4765972392913249 : ℚ) / 250000000000) ≤ ((19054022281392411 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (19289:ℚ) := by decide +kernel
  have hratR : ((((4765972392913249 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((19054022281392411 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19289:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2187 : ((((9536878741918189 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19301 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19289 < q → q < 19301 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19301).mp (by decide +kernel))) hgap
  have hprev := thV_2186
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19301:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9536878741918189 : ℚ) / 500000000000) ≤ ((4765972392913249 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (19301:ℚ) := by decide +kernel
  have hratR : ((((9536878741918189 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((4765972392913249 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19301:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2188 : ((((19083625810420181 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19309 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19301 < q → q < 19309 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19309).mp (by decide +kernel))) hgap
  have hprev := thV_2187
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19309:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((19083625810420181 : ℚ) / 1000000000000) ≤ ((9536878741918189 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (19309:ℚ) := by decide +kernel
  have hratR : ((((19083625810420181 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((9536878741918189 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19309:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2189 : ((((9546747327381567 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19319 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19309 < q → q < 19319 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19319).mp (by decide +kernel))) hgap
  have hprev := thV_2188
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19319:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9546747327381567 : ℚ) / 500000000000) ≤ ((19083625810420181 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (19319:ℚ) := by decide +kernel
  have hratR : ((((9546747327381567 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((19083625810420181 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19319:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2190 : ((((19103364223518827 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19333 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19319 < q → q < 19333 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19333).mp (by decide +kernel))) hgap
  have hprev := thV_2189
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19333:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((19103364223518827 : ℚ) / 1000000000000) ≤ ((9546747327381567 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (19333:ℚ) := by decide +kernel
  have hratR : ((((19103364223518827 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((9546747327381567 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19333:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2191 : ((((9556617929569137 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19373 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19333 < q → q < 19373 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19373).mp (by decide +kernel))) hgap
  have hprev := thV_2190
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19373:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9556617929569137 : ℚ) / 500000000000) ≤ ((19103364223518827 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (19373:ℚ) := by decide +kernel
  have hratR : ((((9556617929569137 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((19103364223518827 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19373:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2192 : ((((19123107804419161 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19379 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19373 < q → q < 19379 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19379).mp (by decide +kernel))) hgap
  have hprev := thV_2191
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19379:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((19123107804419161 : ℚ) / 1000000000000) ≤ ((9556617929569137 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (19379:ℚ) := by decide +kernel
  have hratR : ((((19123107804419161 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((9556617929569137 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19379:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2193 : ((((9566489926449611 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19381 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19379 < q → q < 19381 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19381).mp (by decide +kernel))) hgap
  have hprev := thV_2192
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19381:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9566489926449611 : ℚ) / 500000000000) ≤ ((19123107804419161 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (19381:ℚ) := by decide +kernel
  have hratR : ((((9566489926449611 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((19123107804419161 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19381:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2194 : ((((19142852210912921 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19387 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19381 < q → q < 19387 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19387).mp (by decide +kernel))) hgap
  have hprev := thV_2193
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19387:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((19142852210912921 : ℚ) / 1000000000000) ≤ ((9566489926449611 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (19387:ℚ) := by decide +kernel
  have hratR : ((((19142852210912921 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((9566489926449611 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19387:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2195 : ((((4788181193807291 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19391 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19387 < q → q < 19391 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19391).mp (by decide +kernel))) hgap
  have hprev := thV_2194
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19391:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4788181193807291 : ℚ) / 250000000000) ≤ ((19142852210912921 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (19391:ℚ) := by decide +kernel
  have hratR : ((((4788181193807291 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((19142852210912921 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19391:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2196 : ((((4790649489549449 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19403 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19391 < q → q < 19403 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19403).mp (by decide +kernel))) hgap
  have hprev := thV_2195
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19403:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4790649489549449 : ℚ) / 250000000000) ≤ ((4788181193807291 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (19403:ℚ) := by decide +kernel
  have hratR : ((((4790649489549449 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((4788181193807291 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19403:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2197 : ((((19172471862444151 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19417 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19403 < q → q < 19417 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19417).mp (by decide +kernel))) hgap
  have hprev := thV_2196
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19417:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((19172471862444151 : ℚ) / 1000000000000) ≤ ((4790649489549449 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (19417:ℚ) := by decide +kernel
  have hratR : ((((19172471862444151 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4790649489549449 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19417:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2198 : ((((19182345972674337 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19421 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19417 < q → q < 19421 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19421).mp (by decide +kernel))) hgap
  have hprev := thV_2197
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19421:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((19182345972674337 : ℚ) / 1000000000000) ≤ ((19172471862444151 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (19421:ℚ) := by decide +kernel
  have hratR : ((((19182345972674337 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((19172471862444151 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19421:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2199 : ((((19192220185880529 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19423 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19421 < q → q < 19423 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19423).mp (by decide +kernel))) hgap
  have hprev := thV_2198
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19423:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((19192220185880529 : ℚ) / 1000000000000) ≤ ((19182345972674337 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (19423:ℚ) := by decide +kernel
  have hratR : ((((19192220185880529 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((19182345972674337 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19423:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2200 : ((((1200130912812933 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19427 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19423 < q → q < 19427 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19427).mp (by decide +kernel))) hgap
  have hprev := thV_2199
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19427:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1200130912812933 : ℚ) / 62500000000) ≤ ((19192220185880529 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (19427:ℚ) := by decide +kernel
  have hratR : ((((1200130912812933 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((19192220185880529 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19427:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2201 : ((((19211969127077531 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19429 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19427 < q → q < 19429 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19429).mp (by decide +kernel))) hgap
  have hprev := thV_2200
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19429:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((19211969127077531 : ℚ) / 1000000000000) ≤ ((1200130912812933 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (19429:ℚ) := by decide +kernel
  have hratR : ((((19211969127077531 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1200130912812933 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19429:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2202 : ((((4805460963751189 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19433 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19429 < q → q < 19433 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19433).mp (by decide +kernel))) hgap
  have hprev := thV_2201
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19433:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4805460963751189 : ℚ) / 250000000000) ≤ ((19211969127077531 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (19433:ℚ) := by decide +kernel
  have hratR : ((((4805460963751189 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((19211969127077531 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19433:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2203 : ((((19231718994518137 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19441 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19433 < q → q < 19441 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19441).mp (by decide +kernel))) hgap
  have hprev := thV_2202
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19441:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((19231718994518137 : ℚ) / 1000000000000) ≤ ((4805460963751189 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (19441:ℚ) := by decide +kernel
  have hratR : ((((19231718994518137 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4805460963751189 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19441:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2204 : ((((9620797221305001 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19447 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19441 < q → q < 19447 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19447).mp (by decide +kernel))) hgap
  have hprev := thV_2203
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19447:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9620797221305001 : ℚ) / 500000000000) ≤ ((19231718994518137 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (19447:ℚ) := by decide +kernel
  have hratR : ((((9620797221305001 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((19231718994518137 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19447:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2205 : ((((9625735202393917 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19457 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19447 < q → q < 19457 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19457).mp (by decide +kernel))) hgap
  have hprev := thV_2204
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19457:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9625735202393917 : ℚ) / 500000000000) ≤ ((9620797221305001 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (19457:ℚ) := by decide +kernel
  have hratR : ((((9625735202393917 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((9620797221305001 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19457:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2206 : ((((19261346675290437 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19463 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19457 < q → q < 19463 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19463).mp (by decide +kernel))) hgap
  have hprev := thV_2205
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19463:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((19261346675290437 : ℚ) / 1000000000000) ≤ ((9625735202393917 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (19463:ℚ) := by decide +kernel
  have hratR : ((((19261346675290437 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((9625735202393917 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19463:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2207 : ((((2408902906752847 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19469 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19463 < q → q < 19469 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19469).mp (by decide +kernel))) hgap
  have hprev := thV_2206
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19469:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2408902906752847 : ℚ) / 125000000000) ≤ ((19261346675290437 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (19469:ℚ) := by decide +kernel
  have hratR : ((((2408902906752847 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((19261346675290437 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19469:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2208 : ((((4820274983869313 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19471 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19469 < q → q < 19471 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19471).mp (by decide +kernel))) hgap
  have hprev := thV_2207
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19471:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4820274983869313 : ℚ) / 250000000000) ≤ ((2408902906752847 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (19471:ℚ) := by decide +kernel
  have hratR : ((((4820274983869313 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((2408902906752847 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19471:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2209 : ((((9645488462517421 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19477 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19471 < q → q < 19477 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19477).mp (by decide +kernel))) hgap
  have hprev := thV_2208
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19477:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9645488462517421 : ℚ) / 500000000000) ≤ ((4820274983869313 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (19477:ℚ) := by decide +kernel
  have hratR : ((((9645488462517421 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((4820274983869313 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19477:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2210 : ((((2412606777825081 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19483 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19477 < q → q < 19483 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19483).mp (by decide +kernel))) hgap
  have hprev := thV_2209
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19483:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2412606777825081 : ℚ) / 125000000000) ≤ ((9645488462517421 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (19483:ℚ) := by decide +kernel
  have hratR : ((((2412606777825081 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((9645488462517421 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19483:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2211 : ((((1931073182807983 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19489 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19483 < q → q < 19489 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19489).mp (by decide +kernel))) hgap
  have hprev := thV_2210
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19489:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1931073182807983 : ℚ) / 100000000000) ≤ ((2412606777825081 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (19489:ℚ) := by decide +kernel
  have hratR : ((((1931073182807983 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((2412606777825081 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19489:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2212 : ((((19320610049101479 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19501 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19489 < q → q < 19501 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19501).mp (by decide +kernel))) hgap
  have hprev := thV_2211
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19501:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((19320610049101479 : ℚ) / 1000000000000) ≤ ((1931073182807983 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (19501:ℚ) := by decide +kernel
  have hratR : ((((19320610049101479 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1931073182807983 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19501:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2213 : ((((9665244288876167 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19507 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19501 < q → q < 19507 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19507).mp (by decide +kernel))) hgap
  have hprev := thV_2212
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19507:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9665244288876167 : ℚ) / 500000000000) ≤ ((19320610049101479 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (19507:ℚ) := by decide +kernel
  have hratR : ((((9665244288876167 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((19320610049101479 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19507:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2214 : ((((19340368335974531 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19531 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19507 < q → q < 19531 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19531).mp (by decide +kernel))) hgap
  have hprev := thV_2213
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19531:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((19340368335974531 : ℚ) / 1000000000000) ≤ ((9665244288876167 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (19531:ℚ) := by decide +kernel
  have hratR : ((((19340368335974531 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((9665244288876167 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19531:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2215 : ((((19350248606072251 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19541 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19531 < q → q < 19541 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19541).mp (by decide +kernel))) hgap
  have hprev := thV_2214
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19541:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((19350248606072251 : ℚ) / 1000000000000) ≤ ((19340368335974531 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (19541:ℚ) := by decide +kernel
  have hratR : ((((19350248606072251 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((19340368335974531 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19541:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2216 : ((((19360128978513641 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19543 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19541 < q → q < 19543 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19543).mp (by decide +kernel))) hgap
  have hprev := thV_2215
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19543:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((19360128978513641 : ℚ) / 1000000000000) ≤ ((19350248606072251 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (19543:ℚ) := by decide +kernel
  have hratR : ((((19360128978513641 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((19350248606072251 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19543:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2217 : ((((2421251232814541 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19553 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19543 < q → q < 19553 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19553).mp (by decide +kernel))) hgap
  have hprev := thV_2216
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19553:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2421251232814541 : ℚ) / 125000000000) ≤ ((19360128978513641 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (19553:ℚ) := by decide +kernel
  have hratR : ((((2421251232814541 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((19360128978513641 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19553:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2218 : ((((9689945526665113 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19559 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19553 < q → q < 19559 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19559).mp (by decide +kernel))) hgap
  have hprev := thV_2217
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19559:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9689945526665113 : ℚ) / 500000000000) ≤ ((2421251232814541 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (19559:ℚ) := by decide +kernel
  have hratR : ((((9689945526665113 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((2421251232814541 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19559:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2219 : ((((19389772857484291 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19571 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19559 < q → q < 19571 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19571).mp (by decide +kernel))) hgap
  have hprev := thV_2218
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19571:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((19389772857484291 : ℚ) / 1000000000000) ≤ ((9689945526665113 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (19571:ℚ) := by decide +kernel
  have hratR : ((((19389772857484291 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((9689945526665113 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19571:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2220 : ((((4849913742041857 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19577 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19571 < q → q < 19577 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19577).mp (by decide +kernel))) hgap
  have hprev := thV_2219
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19577:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4849913742041857 : ℚ) / 250000000000) ≤ ((19389772857484291 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (19577:ℚ) := by decide +kernel
  have hratR : ((((4849913742041857 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((19389772857484291 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19577:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2221 : ((((3881907477057141 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19583 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19577 < q → q < 19583 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19583).mp (by decide +kernel))) hgap
  have hprev := thV_2220
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19583:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3881907477057141 : ℚ) / 200000000000) ≤ ((4849913742041857 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (19583:ℚ) := by decide +kernel
  have hratR : ((((3881907477057141 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((4849913742041857 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19583:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2222 : ((((2427427564631793 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19597 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19583 < q → q < 19597 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19597).mp (by decide +kernel))) hgap
  have hprev := thV_2221
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19597:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2427427564631793 : ℚ) / 125000000000) ≤ ((3881907477057141 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (19597:ℚ) := by decide +kernel
  have hratR : ((((2427427564631793 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((3881907477057141 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19597:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2223 : ((((3885860790989087 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19603 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19597 < q → q < 19603 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19603).mp (by decide +kernel))) hgap
  have hprev := thV_2222
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19603:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3885860790989087 : ℚ) / 200000000000) ≤ ((2427427564631793 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (19603:ℚ) := by decide +kernel
  have hratR : ((((3885860790989087 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((2427427564631793 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19603:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2224 : ((((3887837539773059 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19609 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19603 < q → q < 19609 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19609).mp (by decide +kernel))) hgap
  have hprev := thV_2223
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19609:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3887837539773059 : ℚ) / 200000000000) ≤ ((3885860790989087 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (19609:ℚ) := by decide +kernel
  have hratR : ((((3887837539773059 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((3885860790989087 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19609:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2225 : ((((19449074091118763 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19661 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19609 < q → q < 19661 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19661).mp (by decide +kernel))) hgap
  have hprev := thV_2224
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19661:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((19449074091118763 : ℚ) / 1000000000000) ≤ ((3887837539773059 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (19661:ℚ) := by decide +kernel
  have hratR : ((((19449074091118763 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3887837539773059 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19661:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2226 : ((((19458961500097447 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19681 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19661 < q → q < 19681 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19681).mp (by decide +kernel))) hgap
  have hprev := thV_2225
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19681:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((19458961500097447 : ℚ) / 1000000000000) ≤ ((19449074091118763 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (19681:ℚ) := by decide +kernel
  have hratR : ((((19458961500097447 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((19449074091118763 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19681:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2227 : ((((19468849213892227 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19687 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19681 < q → q < 19687 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19687).mp (by decide +kernel))) hgap
  have hprev := thV_2226
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19687:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((19468849213892227 : ℚ) / 1000000000000) ≤ ((19458961500097447 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (19687:ℚ) := by decide +kernel
  have hratR : ((((19468849213892227 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((19458961500097447 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19687:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2228 : ((((19478737435507453 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19697 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19687 < q → q < 19697 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19697).mp (by decide +kernel))) hgap
  have hprev := thV_2227
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19697:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((19478737435507453 : ℚ) / 1000000000000) ≤ ((19468849213892227 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (19697:ℚ) := by decide +kernel
  have hratR : ((((19478737435507453 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((19468849213892227 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19697:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2229 : ((((1948862575865583 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19699 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19697 < q → q < 19699 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19699).mp (by decide +kernel))) hgap
  have hprev := thV_2228
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19699:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1948862575865583 : ℚ) / 100000000000) ≤ ((19478737435507453 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (19699:ℚ) := by decide +kernel
  have hratR : ((((1948862575865583 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((19478737435507453 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19699:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2230 : ((((19498514589315383 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19709 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19699 < q → q < 19709 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19709).mp (by decide +kernel))) hgap
  have hprev := thV_2229
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19709:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((19498514589315383 : ℚ) / 1000000000000) ≤ ((1948862575865583 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (19709:ℚ) := by decide +kernel
  have hratR : ((((19498514589315383 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1948862575865583 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19709:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2231 : ((((1950840382579851 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19717 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19709 < q → q < 19717 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19717).mp (by decide +kernel))) hgap
  have hprev := thV_2230
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19717:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1950840382579851 : ℚ) / 100000000000) ≤ ((19498514589315383 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (19717:ℚ) := by decide +kernel
  have hratR : ((((1950840382579851 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((19498514589315383 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19717:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2232 : ((((9759146784664807 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19727 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19717 < q → q < 19727 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19727).mp (by decide +kernel))) hgap
  have hprev := thV_2231
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19727:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9759146784664807 : ℚ) / 500000000000) ≤ ((1950840382579851 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (19727:ℚ) := by decide +kernel
  have hratR : ((((9759146784664807 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1950840382579851 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19727:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2233 : ((((19528183920979117 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19739 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19727 < q → q < 19739 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19739).mp (by decide +kernel))) hgap
  have hprev := thV_2232
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19739:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((19528183920979117 : ℚ) / 1000000000000) ≤ ((9759146784664807 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (19739:ℚ) := by decide +kernel
  have hratR : ((((19528183920979117 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((9759146784664807 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19739:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2234 : ((((4884518720094359 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19751 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19739 < q → q < 19751 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19751).mp (by decide +kernel))) hgap
  have hprev := thV_2233
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19751:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4884518720094359 : ℚ) / 250000000000) ≤ ((19528183920979117 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (19751:ℚ) := by decide +kernel
  have hratR : ((((4884518720094359 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((19528183920979117 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19751:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2235 : ((((4886991485257831 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19753 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19751 < q → q < 19753 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19753).mp (by decide +kernel))) hgap
  have hprev := thV_2234
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19753:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4886991485257831 : ℚ) / 250000000000) ≤ ((4884518720094359 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (19753:ℚ) := by decide +kernel
  have hratR : ((((4886991485257831 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((4884518720094359 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19753:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2236 : ((((9778928652695209 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19759 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19753 < q → q < 19759 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19759).mp (by decide +kernel))) hgap
  have hprev := thV_2235
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19759:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9778928652695209 : ℚ) / 500000000000) ≤ ((4886991485257831 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (19759:ℚ) := by decide +kernel
  have hratR : ((((9778928652695209 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((4886991485257831 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19759:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2237 : ((((19567748872168419 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19763 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19759 < q → q < 19763 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19763).mp (by decide +kernel))) hgap
  have hprev := thV_2236
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19763:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((19567748872168419 : ℚ) / 1000000000000) ≤ ((9778928652695209 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (19763:ℚ) := by decide +kernel
  have hratR : ((((19567748872168419 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((9778928652695209 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19763:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2238 : ((((19577641147090101 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19777 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19763 < q → q < 19777 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19777).mp (by decide +kernel))) hgap
  have hprev := thV_2237
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19777:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((19577641147090101 : ℚ) / 1000000000000) ≤ ((19567748872168419 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (19777:ℚ) := by decide +kernel
  have hratR : ((((19577641147090101 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((19567748872168419 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19777:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2239 : ((((9793767115352641 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19793 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19777 < q → q < 19793 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19793).mp (by decide +kernel))) hgap
  have hprev := thV_2238
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19793:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9793767115352641 : ℚ) / 500000000000) ≤ ((19577641147090101 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (19793:ℚ) := by decide +kernel
  have hratR : ((((9793767115352641 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((19577641147090101 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19793:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2240 : ((((195974277184221 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19801 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19793 < q → q < 19801 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19801).mp (by decide +kernel))) hgap
  have hprev := thV_2239
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19801:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((195974277184221 : ℚ) / 10000000000) ≤ ((9793767115352641 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (19801:ℚ) := by decide +kernel
  have hratR : ((((195974277184221 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ ((((9793767115352641 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19801:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2241 : ((((3921464362397071 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19813 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19801 < q → q < 19813 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19813).mp (by decide +kernel))) hgap
  have hprev := thV_2240
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19813:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3921464362397071 : ℚ) / 200000000000) ≤ ((195974277184221 : ℚ) / 10000000000) + Work.RHContract.RegionI.logLowQ (19813:ℚ) := by decide +kernel
  have hratR : ((((3921464362397071 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((195974277184221 : ℚ) / 10000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19813:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2242 : ((((122607601302089 : ℚ) / 6250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19819 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19813 < q → q < 19819 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19819).mp (by decide +kernel))) hgap
  have hprev := thV_2241
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19819:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((122607601302089 : ℚ) / 6250000000) ≤ ((3921464362397071 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (19819:ℚ) := by decide +kernel
  have hratR : ((((122607601302089 : ℚ) / 6250000000) : ℚ) : ℝ) ≤ ((((3921464362397071 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19819:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2243 : ((((3925422342822679 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19841 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19819 < q → q < 19841 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19841).mp (by decide +kernel))) hgap
  have hprev := thV_2242
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19841:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3925422342822679 : ℚ) / 200000000000) ≤ ((122607601302089 : ℚ) / 6250000000) + Work.RHContract.RegionI.logLowQ (19841:ℚ) := by decide +kernel
  have hratR : ((((3925422342822679 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((122607601302089 : ℚ) / 6250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19841:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2244 : ((((19637007320688841 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19843 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19841 < q → q < 19843 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19843).mp (by decide +kernel))) hgap
  have hprev := thV_2243
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19843:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((19637007320688841 : ℚ) / 1000000000000) ≤ ((3925422342822679 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (19843:ℚ) := by decide +kernel
  have hratR : ((((19637007320688841 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3925422342822679 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19843:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2245 : ((((9823451715546699 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19853 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19843 < q → q < 19853 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19853).mp (by decide +kernel))) hgap
  have hprev := thV_2244
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19853:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9823451715546699 : ℚ) / 500000000000) ≤ ((19637007320688841 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (19853:ℚ) := by decide +kernel
  have hratR : ((((9823451715546699 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((19637007320688841 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19853:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2246 : ((((19656799944378557 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19861 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19853 < q → q < 19861 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19861).mp (by decide +kernel))) hgap
  have hprev := thV_2245
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19861:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((19656799944378557 : ℚ) / 1000000000000) ≤ ((9823451715546699 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (19861:ℚ) := by decide +kernel
  have hratR : ((((19656799944378557 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((9823451715546699 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19861:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2247 : ((((3933339351943537 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19867 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19861 < q → q < 19867 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19867).mp (by decide +kernel))) hgap
  have hprev := thV_2246
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19867:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3933339351943537 : ℚ) / 200000000000) ≤ ((19656799944378557 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (19867:ℚ) := by decide +kernel
  have hratR : ((((3933339351943537 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((19656799944378557 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19867:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2248 : ((((19676594681808109 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19889 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19867 < q → q < 19889 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19889).mp (by decide +kernel))) hgap
  have hprev := thV_2247
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19889:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((19676594681808109 : ℚ) / 1000000000000) ≤ ((3933339351943537 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (19889:ℚ) := by decide +kernel
  have hratR : ((((19676594681808109 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3933339351943537 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19889:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2249 : ((((9843246352225787 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19891 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19889 < q → q < 19891 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19891).mp (by decide +kernel))) hgap
  have hprev := thV_2248
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19891:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9843246352225787 : ℚ) / 500000000000) ≤ ((19676594681808109 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (19891:ℚ) := by decide +kernel
  have hratR : ((((9843246352225787 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((19676594681808109 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19891:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2250 : ((((19696391832511693 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19913 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19891 < q → q < 19913 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19913).mp (by decide +kernel))) hgap
  have hprev := thV_2249
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19913:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((19696391832511693 : ℚ) / 1000000000000) ≤ ((9843246352225787 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (19913:ℚ) := by decide +kernel
  have hratR : ((((19696391832511693 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((9843246352225787 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19913:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2251 : ((((19706291261837129 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19919 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19913 < q → q < 19919 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19919).mp (by decide +kernel))) hgap
  have hprev := thV_2250
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19919:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((19706291261837129 : ℚ) / 1000000000000) ≤ ((19696391832511693 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (19919:ℚ) := by decide +kernel
  have hratR : ((((19706291261837129 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((19696391832511693 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19919:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2252 : ((((9858095546354261 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19927 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19919 < q → q < 19927 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19927).mp (by decide +kernel))) hgap
  have hprev := thV_2251
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19927:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9858095546354261 : ℚ) / 500000000000) ≤ ((19706291261837129 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (19927:ℚ) := by decide +kernel
  have hratR : ((((9858095546354261 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((19706291261837129 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19927:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2253 : ((((789043657011429 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19937 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19927 < q → q < 19937 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19937).mp (by decide +kernel))) hgap
  have hprev := thV_2252
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19937:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((789043657011429 : ℚ) / 40000000000) ≤ ((9858095546354261 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (19937:ℚ) := by decide +kernel
  have hratR : ((((789043657011429 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((9858095546354261 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19937:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2254 : ((((9867996179788917 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19949 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19937 < q → q < 19949 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19949).mp (by decide +kernel))) hgap
  have hprev := thV_2253
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19949:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9867996179788917 : ℚ) / 500000000000) ≤ ((789043657011429 : ℚ) / 40000000000) + Work.RHContract.RegionI.logLowQ (19949:ℚ) := by decide +kernel
  have hratR : ((((9867996179788917 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((789043657011429 : ℚ) / 40000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19949:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2255 : ((((3949178779044601 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19961 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19949 < q → q < 19961 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19961).mp (by decide +kernel))) hgap
  have hprev := thV_2254
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19961:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3949178779044601 : ℚ) / 200000000000) ≤ ((9867996179788917 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (19961:ℚ) := by decide +kernel
  have hratR : ((((3949178779044601 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((9867996179788917 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19961:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2256 : ((((9877897765529269 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19963 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19961 < q → q < 19963 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19963).mp (by decide +kernel))) hgap
  have hprev := thV_2255
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19963:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9877897765529269 : ℚ) / 500000000000) ≤ ((3949178779044601 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (19963:ℚ) := by decide +kernel
  have hratR : ((((9877897765529269 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((3949178779044601 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19963:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2257 : ((((19765697667695363 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19973 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19963 < q → q < 19973 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19973).mp (by decide +kernel))) hgap
  have hprev := thV_2256
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19973:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((19765697667695363 : ℚ) / 1000000000000) ≤ ((9877897765529269 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (19973:ℚ) := by decide +kernel
  have hratR : ((((19765697667695363 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((9877897765529269 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19973:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2258 : ((((19775600104692623 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19979 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19973 < q → q < 19979 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19979).mp (by decide +kernel))) hgap
  have hprev := thV_2257
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19979:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((19775600104692623 : ℚ) / 1000000000000) ≤ ((19765697667695363 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (19979:ℚ) := by decide +kernel
  have hratR : ((((19775600104692623 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((19765697667695363 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19979:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2259 : ((((19785503142140239 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19991 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19979 < q → q < 19991 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19991).mp (by decide +kernel))) hgap
  have hprev := thV_2258
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19991:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((19785503142140239 : ℚ) / 1000000000000) ≤ ((19775600104692623 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (19991:ℚ) := by decide +kernel
  have hratR : ((((19785503142140239 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((19775600104692623 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19991:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2260 : ((((19795406279627871 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19993 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19991 < q → q < 19993 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19993).mp (by decide +kernel))) hgap
  have hprev := thV_2259
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19993:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((19795406279627871 : ℚ) / 1000000000000) ≤ ((19785503142140239 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (19993:ℚ) := by decide +kernel
  have hratR : ((((19795406279627871 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((19785503142140239 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19993:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2261 : ((((4951327404291379 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((19997 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19993 < q → q < 19997 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19997).mp (by decide +kernel))) hgap
  have hprev := thV_2260
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (19997:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4951327404291379 : ℚ) / 250000000000) ≤ ((19795406279627871 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (19997:ℚ) := by decide +kernel
  have hratR : ((((4951327404291379 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((19795406279627871 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (19997:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2262 : ((((9907606827281609 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20011 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 19997 < q → q < 20011 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20011).mp (by decide +kernel))) hgap
  have hprev := thV_2261
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20011:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9907606827281609 : ℚ) / 500000000000) ≤ ((4951327404291379 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (20011:ℚ) := by decide +kernel
  have hratR : ((((9907606827281609 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((4951327404291379 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20011:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2263 : ((((15860094553249 : ℚ) / 800000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20021 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20011 < q → q < 20021 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20021).mp (by decide +kernel))) hgap
  have hprev := thV_2262
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20021:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((15860094553249 : ℚ) / 800000000) ≤ ((9907606827281609 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (20021:ℚ) := by decide +kernel
  have hratR : ((((15860094553249 : ℚ) / 800000000) : ℚ) : ℝ) ≤ ((((9907606827281609 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20021:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2264 : ((((19835022828449403 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20023 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20021 < q → q < 20023 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20023).mp (by decide +kernel))) hgap
  have hprev := thV_2263
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20023:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((19835022828449403 : ℚ) / 1000000000000) ≤ ((15860094553249 : ℚ) / 800000000) + Work.RHContract.RegionI.logLowQ (20023:ℚ) := by decide +kernel
  have hratR : ((((19835022828449403 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((15860094553249 : ℚ) / 800000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20023:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2265 : ((((620153992654627 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20029 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20023 < q → q < 20029 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20029).mp (by decide +kernel))) hgap
  have hprev := thV_2264
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20029:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((620153992654627 : ℚ) / 31250000000) ≤ ((19835022828449403 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (20029:ℚ) := by decide +kernel
  have hratR : ((((620153992654627 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((19835022828449403 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20029:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2266 : ((((19854833599740029 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20047 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20029 < q → q < 20047 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20047).mp (by decide +kernel))) hgap
  have hprev := thV_2265
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20047:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((19854833599740029 : ℚ) / 1000000000000) ≤ ((620153992654627 : ℚ) / 31250000000) + Work.RHContract.RegionI.logLowQ (20047:ℚ) := by decide +kernel
  have hratR : ((((19854833599740029 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((620153992654627 : ℚ) / 31250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20047:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2267 : ((((2483092454255399 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20051 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20047 < q → q < 20051 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20051).mp (by decide +kernel))) hgap
  have hprev := thV_2266
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20051:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2483092454255399 : ℚ) / 125000000000) ≤ ((19854833599740029 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (20051:ℚ) := by decide +kernel
  have hratR : ((((2483092454255399 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((19854833599740029 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20051:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2268 : ((((1242165391665077 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20063 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20051 < q → q < 20063 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20063).mp (by decide +kernel))) hgap
  have hprev := thV_2267
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20063:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1242165391665077 : ℚ) / 62500000000) ≤ ((2483092454255399 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (20063:ℚ) := by decide +kernel
  have hratR : ((((1242165391665077 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((2483092454255399 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20063:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2269 : ((((2485569162237969 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20071 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20063 < q → q < 20071 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20071).mp (by decide +kernel))) hgap
  have hprev := thV_2268
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20071:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2485569162237969 : ℚ) / 125000000000) ≤ ((1242165391665077 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (20071:ℚ) := by decide +kernel
  have hratR : ((((2485569162237969 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((1242165391665077 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20071:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2270 : ((((9947230612790337 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20089 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20071 < q → q < 20089 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20089).mp (by decide +kernel))) hgap
  have hprev := thV_2269
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20089:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9947230612790337 : ℚ) / 500000000000) ≤ ((2485569162237969 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (20089:ℚ) := by decide +kernel
  have hratR : ((((9947230612790337 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((2485569162237969 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20089:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2271 : ((((622011554700659 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20101 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20089 < q → q < 20101 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20101).mp (by decide +kernel))) hgap
  have hprev := thV_2270
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20101:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((622011554700659 : ℚ) / 31250000000) ≤ ((9947230612790337 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (20101:ℚ) := by decide +kernel
  have hratR : ((((622011554700659 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((9947230612790337 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20101:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2272 : ((((9957139286854787 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20107 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20101 < q → q < 20107 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20107).mp (by decide +kernel))) hgap
  have hprev := thV_2271
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20107:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9957139286854787 : ℚ) / 500000000000) ≤ ((622011554700659 : ℚ) / 31250000000) + Work.RHContract.RegionI.logLowQ (20107:ℚ) := by decide +kernel
  have hratR : ((((9957139286854787 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((622011554700659 : ℚ) / 31250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20107:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2273 : ((((19924187695357087 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20113 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20107 < q → q < 20113 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20113).mp (by decide +kernel))) hgap
  have hprev := thV_2272
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20113:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((19924187695357087 : ℚ) / 1000000000000) ≤ ((9957139286854787 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (20113:ℚ) := by decide +kernel
  have hratR : ((((19924187695357087 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((9957139286854787 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20113:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2274 : ((((2491762126982647 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20117 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20113 < q → q < 20117 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20117).mp (by decide +kernel))) hgap
  have hprev := thV_2273
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20117:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2491762126982647 : ℚ) / 125000000000) ≤ ((19924187695357087 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (20117:ℚ) := by decide +kernel
  have hratR : ((((2491762126982647 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((19924187695357087 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20117:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2275 : ((((19944006634576003 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20123 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20117 < q → q < 20123 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20123).mp (by decide +kernel))) hgap
  have hprev := thV_2274
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20123:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((19944006634576003 : ℚ) / 1000000000000) ≤ ((2491762126982647 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (20123:ℚ) := by decide +kernel
  have hratR : ((((19944006634576003 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2491762126982647 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20123:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2276 : ((((2494239568926583 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20129 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20123 < q → q < 20129 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20129).mp (by decide +kernel))) hgap
  have hprev := thV_2275
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20129:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2494239568926583 : ℚ) / 125000000000) ≤ ((19944006634576003 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (20129:ℚ) := by decide +kernel
  have hratR : ((((2494239568926583 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((19944006634576003 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20129:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2277 : ((((19963827163521503 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20143 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20129 < q → q < 20143 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20143).mp (by decide +kernel))) hgap
  have hprev := thV_2276
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20143:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((19963827163521503 : ℚ) / 1000000000000) ≤ ((2494239568926583 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (20143:ℚ) := by decide +kernel
  have hratR : ((((19963827163521503 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2494239568926583 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20143:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2278 : ((((19973737974190779 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20147 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20143 < q → q < 20147 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20147).mp (by decide +kernel))) hgap
  have hprev := thV_2277
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20147:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((19973737974190779 : ℚ) / 1000000000000) ≤ ((19963827163521503 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (20147:ℚ) := by decide +kernel
  have hratR : ((((19973737974190779 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((19963827163521503 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20147:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2279 : ((((19983648884125491 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20149 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20147 < q → q < 20149 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20149).mp (by decide +kernel))) hgap
  have hprev := thV_2278
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20149:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((19983648884125491 : ℚ) / 1000000000000) ≤ ((19973737974190779 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (20149:ℚ) := by decide +kernel
  have hratR : ((((19983648884125491 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((19973737974190779 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20149:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2280 : ((((19993560389445981 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20161 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20149 < q → q < 20161 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20161).mp (by decide +kernel))) hgap
  have hprev := thV_2279
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20161:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((19993560389445981 : ℚ) / 1000000000000) ≤ ((19983648884125491 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (20161:ℚ) := by decide +kernel
  have hratR : ((((19993560389445981 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((19983648884125491 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20161:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2281 : ((((2500434061224747 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20173 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20161 < q → q < 20173 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20173).mp (by decide +kernel))) hgap
  have hprev := thV_2280
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20173:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2500434061224747 : ℚ) / 125000000000) ≤ ((19993560389445981 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (20173:ℚ) := by decide +kernel
  have hratR : ((((2500434061224747 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((19993560389445981 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20173:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2282 : ((((20013384788415151 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20177 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20173 < q → q < 20177 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20177).mp (by decide +kernel))) hgap
  have hprev := thV_2281
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20177:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((20013384788415151 : ℚ) / 1000000000000) ≤ ((2500434061224747 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (20177:ℚ) := by decide +kernel
  have hratR : ((((20013384788415151 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2500434061224747 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20177:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2283 : ((((20023297384356411 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20183 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20177 < q → q < 20183 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20183).mp (by decide +kernel))) hgap
  have hprev := thV_2282
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20183:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((20023297384356411 : ℚ) / 1000000000000) ≤ ((20013384788415151 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (20183:ℚ) := by decide +kernel
  have hratR : ((((20023297384356411 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((20013384788415151 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20183:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2284 : ((((10016605435869943 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20201 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20183 < q → q < 20201 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20201).mp (by decide +kernel))) hgap
  have hprev := thV_2283
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20201:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10016605435869943 : ℚ) / 500000000000) ≤ ((20023297384356411 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (20201:ℚ) := by decide +kernel
  have hratR : ((((10016605435869943 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((20023297384356411 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20201:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2285 : ((((10021562624885807 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20219 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20201 < q → q < 20219 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20219).mp (by decide +kernel))) hgap
  have hprev := thV_2284
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20219:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10021562624885807 : ℚ) / 500000000000) ≤ ((10016605435869943 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (20219:ℚ) := by decide +kernel
  have hratR : ((((10021562624885807 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((10016605435869943 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20219:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2286 : ((((5013260055282113 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20231 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20219 < q → q < 20231 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20231).mp (by decide +kernel))) hgap
  have hprev := thV_2285
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20231:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5013260055282113 : ℚ) / 250000000000) ≤ ((10021562624885807 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (20231:ℚ) := by decide +kernel
  have hratR : ((((5013260055282113 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((10021562624885807 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20231:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2287 : ((((20062955291338591 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20233 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20231 < q → q < 20233 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20233).mp (by decide +kernel))) hgap
  have hprev := thV_2286
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20233:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((20062955291338591 : ℚ) / 1000000000000) ≤ ((5013260055282113 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (20233:ℚ) := by decide +kernel
  have hratR : ((((20062955291338591 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5013260055282113 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20233:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2288 : ((((20072871152023551 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20249 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20233 < q → q < 20249 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20249).mp (by decide +kernel))) hgap
  have hprev := thV_2287
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20249:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((20072871152023551 : ℚ) / 1000000000000) ≤ ((20062955291338591 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (20249:ℚ) := by decide +kernel
  have hratR : ((((20072871152023551 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((20062955291338591 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20249:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2289 : ((((20082787605154837 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20261 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20249 < q → q < 20261 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20261).mp (by decide +kernel))) hgap
  have hprev := thV_2288
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20261:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((20082787605154837 : ℚ) / 1000000000000) ≤ ((20072871152023551 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (20261:ℚ) := by decide +kernel
  have hratR : ((((20082787605154837 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((20072871152023551 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20261:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2290 : ((((4018540890611087 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20269 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20261 < q → q < 20269 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20269).mp (by decide +kernel))) hgap
  have hprev := thV_2289
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20269:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4018540890611087 : ℚ) / 200000000000) ≤ ((20082787605154837 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (20269:ℚ) := by decide +kernel
  have hratR : ((((4018540890611087 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((20082787605154837 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20269:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2291 : ((((20102622188617597 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20287 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20269 < q → q < 20287 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20287).mp (by decide +kernel))) hgap
  have hprev := thV_2290
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20287:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((20102622188617597 : ℚ) / 1000000000000) ≤ ((4018540890611087 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (20287:ℚ) := by decide +kernel
  have hratR : ((((20102622188617597 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4018540890611087 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20287:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2292 : ((((4022508083396963 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20297 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20287 < q → q < 20297 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20297).mp (by decide +kernel))) hgap
  have hprev := thV_2291
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20297:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4022508083396963 : ℚ) / 200000000000) ≤ ((20102622188617597 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (20297:ℚ) := by decide +kernel
  have hratR : ((((4022508083396963 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((20102622188617597 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20297:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2293 : ((((10061229962754883 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20323 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20297 < q → q < 20323 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20323).mp (by decide +kernel))) hgap
  have hprev := thV_2292
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20323:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10061229962754883 : ℚ) / 500000000000) ≤ ((4022508083396963 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (20323:ℚ) := by decide +kernel
  have hratR : ((((10061229962754883 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((4022508083396963 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20323:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2294 : ((((4026475926167337 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20327 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20323 < q → q < 20327 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20327).mp (by decide +kernel))) hgap
  have hprev := thV_2293
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20327:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4026475926167337 : ℚ) / 200000000000) ≤ ((10061229962754883 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (20327:ℚ) := by decide +kernel
  have hratR : ((((4026475926167337 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((10061229962754883 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20327:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2295 : ((((5035574907823489 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20333 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20327 < q → q < 20333 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20333).mp (by decide +kernel))) hgap
  have hprev := thV_2294
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20333:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5035574907823489 : ℚ) / 250000000000) ≤ ((4026475926167337 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (20333:ℚ) := by decide +kernel
  have hratR : ((((5035574907823489 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((4026475926167337 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20333:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2296 : ((((20152220025122919 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20341 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20333 < q → q < 20341 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20341).mp (by decide +kernel))) hgap
  have hprev := thV_2295
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20341:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((20152220025122919 : ℚ) / 1000000000000) ≤ ((5035574907823489 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (20341:ℚ) := by decide +kernel
  have hratR : ((((20152220025122919 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5035574907823489 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20341:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2297 : ((((4032428142775827 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20347 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20341 < q → q < 20347 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20347).mp (by decide +kernel))) hgap
  have hprev := thV_2296
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20347:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4032428142775827 : ℚ) / 200000000000) ≤ ((20152220025122919 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (20347:ℚ) := by decide +kernel
  have hratR : ((((4032428142775827 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((20152220025122919 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20347:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2298 : ((((315188464023057 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20353 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20347 < q → q < 20353 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20353).mp (by decide +kernel))) hgap
  have hprev := thV_2297
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20353:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((315188464023057 : ℚ) / 15625000000) ≤ ((4032428142775827 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (20353:ℚ) := by decide +kernel
  have hratR : ((((315188464023057 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ ((((4032428142775827 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20353:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2299 : ((((807279315103363 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20357 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20353 < q → q < 20357 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20357).mp (by decide +kernel))) hgap
  have hprev := thV_2298
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20357:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((807279315103363 : ℚ) / 40000000000) ≤ ((315188464023057 : ℚ) / 15625000000) + Work.RHContract.RegionI.logLowQ (20357:ℚ) := by decide +kernel
  have hratR : ((((807279315103363 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((315188464023057 : ℚ) / 15625000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20357:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2300 : ((((1009595207796699 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20359 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20357 < q → q < 20359 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20359).mp (by decide +kernel))) hgap
  have hprev := thV_2299
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20359:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1009595207796699 : ℚ) / 50000000000) ≤ ((807279315103363 : ℚ) / 40000000000) + Work.RHContract.RegionI.logLowQ (20359:ℚ) := by decide +kernel
  have hratR : ((((1009595207796699 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((807279315103363 : ℚ) / 40000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20359:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2301 : ((((10100912962673277 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20369 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20359 < q → q < 20369 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20369).mp (by decide +kernel))) hgap
  have hprev := thV_2300
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20369:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10100912962673277 : ℚ) / 500000000000) ≤ ((1009595207796699 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (20369:ℚ) := by decide +kernel
  have hratR : ((((10100912962673277 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1009595207796699 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20369:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2302 : ((((20211748676161631 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20389 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20369 < q → q < 20389 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20389).mp (by decide +kernel))) hgap
  have hprev := thV_2301
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20389:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((20211748676161631 : ℚ) / 1000000000000) ≤ ((10100912962673277 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (20389:ℚ) := by decide +kernel
  have hratR : ((((20211748676161631 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((10100912962673277 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20389:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2303 : ((((5055417905785421 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20393 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20389 < q → q < 20393 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20393).mp (by decide +kernel))) hgap
  have hprev := thV_2302
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20393:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5055417905785421 : ℚ) / 250000000000) ≤ ((20211748676161631 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (20393:ℚ) := by decide +kernel
  have hratR : ((((5055417905785421 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((20211748676161631 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20393:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2304 : ((((20231594864297067 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20399 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20393 < q → q < 20399 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20399).mp (by decide +kernel))) hgap
  have hprev := thV_2303
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20399:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((20231594864297067 : ℚ) / 1000000000000) ≤ ((5055417905785421 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (20399:ℚ) := by decide +kernel
  have hratR : ((((20231594864297067 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5055417905785421 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20399:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2305 : ((((2530189812193957 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20407 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20399 < q → q < 20407 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20407).mp (by decide +kernel))) hgap
  have hprev := thV_2304
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20407:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2530189812193957 : ℚ) / 125000000000) ≤ ((20231594864297067 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (20407:ℚ) := by decide +kernel
  have hratR : ((((2530189812193957 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((20231594864297067 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20407:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2306 : ((((2025144232679821 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20411 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20407 < q → q < 20411 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20411).mp (by decide +kernel))) hgap
  have hprev := thV_2305
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20411:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2025144232679821 : ℚ) / 100000000000) ≤ ((2530189812193957 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (20411:ℚ) := by decide +kernel
  have hratR : ((((2025144232679821 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((2530189812193957 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20411:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2307 : ((((2026136713542881 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20431 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20411 < q → q < 20431 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20431).mp (by decide +kernel))) hgap
  have hprev := thV_2306
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20431:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2026136713542881 : ℚ) / 100000000000) ≤ ((2025144232679821 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (20431:ℚ) := by decide +kernel
  have hratR : ((((2026136713542881 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((2025144232679821 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20431:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2308 : ((((2027129243339197 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20441 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20431 < q → q < 20441 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20441).mp (by decide +kernel))) hgap
  have hprev := thV_2307
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20441:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2027129243339197 : ℚ) / 100000000000) ≤ ((2026136713542881 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (20441:ℚ) := by decide +kernel
  have hratR : ((((2027129243339197 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((2026136713542881 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20441:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2309 : ((((4056243565838583 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20443 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20441 < q → q < 20443 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20443).mp (by decide +kernel))) hgap
  have hprev := thV_2308
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20443:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4056243565838583 : ℚ) / 200000000000) ≤ ((2027129243339197 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (20443:ℚ) := by decide +kernel
  have hratR : ((((4056243565838583 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((2027129243339197 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20443:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2310 : ((((5072786221693331 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20477 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20443 < q → q < 20477 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20477).mp (by decide +kernel))) hgap
  have hprev := thV_2309
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20477:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5072786221693331 : ℚ) / 250000000000) ≤ ((4056243565838583 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (20477:ℚ) := by decide +kernel
  have hratR : ((((5072786221693331 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((4056243565838583 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20477:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2311 : ((((20301072042019521 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20479 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20477 < q → q < 20479 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20479).mp (by decide +kernel))) hgap
  have hprev := thV_2310
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20479:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((20301072042019521 : ℚ) / 1000000000000) ≤ ((5072786221693331 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (20479:ℚ) := by decide +kernel
  have hratR : ((((20301072042019521 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5072786221693331 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20479:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2312 : ((((10155499696284341 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20483 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20479 < q → q < 20483 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20483).mp (by decide +kernel))) hgap
  have hprev := thV_2311
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20483:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10155499696284341 : ℚ) / 500000000000) ≤ ((20301072042019521 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (20483:ℚ) := by decide +kernel
  have hratR : ((((10155499696284341 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((20301072042019521 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20483:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2313 : ((((10160463957067649 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20507 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20483 < q → q < 20507 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20507).mp (by decide +kernel))) hgap
  have hprev := thV_2312
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20507:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10160463957067649 : ℚ) / 500000000000) ≤ ((10155499696284341 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (20507:ℚ) := by decide +kernel
  have hratR : ((((10160463957067649 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((10155499696284341 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20507:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2314 : ((((158834816665819 : ℚ) / 7812500000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20509 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20507 < q → q < 20509 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20509).mp (by decide +kernel))) hgap
  have hprev := thV_2313
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20509:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((158834816665819 : ℚ) / 7812500000) ≤ ((10160463957067649 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (20509:ℚ) := by decide +kernel
  have hratR : ((((158834816665819 : ℚ) / 7812500000) : ℚ) : ℝ) ≤ ((((10160463957067649 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20509:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2315 : ((((20340785737252233 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20521 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20509 < q → q < 20521 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20521).mp (by decide +kernel))) hgap
  have hprev := thV_2314
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20521:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((20340785737252233 : ℚ) / 1000000000000) ≤ ((158834816665819 : ℚ) / 7812500000) + Work.RHContract.RegionI.logLowQ (20521:ℚ) := by decide +kernel
  have hratR : ((((20340785737252233 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((158834816665819 : ℚ) / 7812500000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20521:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2316 : ((((20350715525875549 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20533 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20521 < q → q < 20533 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20533).mp (by decide +kernel))) hgap
  have hprev := thV_2315
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20533:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((20350715525875549 : ℚ) / 1000000000000) ≤ ((20340785737252233 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (20533:ℚ) := by decide +kernel
  have hratR : ((((20350715525875549 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((20340785737252233 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20533:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2317 : ((((10180322900700601 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20543 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20533 < q → q < 20543 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20543).mp (by decide +kernel))) hgap
  have hprev := thV_2316
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20543:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10180322900700601 : ℚ) / 500000000000) ≤ ((20350715525875549 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (20543:ℚ) := by decide +kernel
  have hratR : ((((10180322900700601 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((20350715525875549 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20543:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2318 : ((((10185288184477251 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20549 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20543 < q → q < 20549 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20549).mp (by decide +kernel))) hgap
  have hprev := thV_2317
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20549:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10185288184477251 : ℚ) / 500000000000) ≤ ((10180322900700601 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (20549:ℚ) := by decide +kernel
  have hratR : ((((10185288184477251 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((10180322900700601 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20549:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2319 : ((((20380507033831403 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20551 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20549 < q → q < 20551 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20551).mp (by decide +kernel))) hgap
  have hprev := thV_2318
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20551:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((20380507033831403 : ℚ) / 1000000000000) ≤ ((10185288184477251 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (20551:ℚ) := by decide +kernel
  have hratR : ((((20380507033831403 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((10185288184477251 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20551:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2320 : ((((4078087656490217 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20563 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20551 < q → q < 20563 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20563).mp (by decide +kernel))) hgap
  have hprev := thV_2319
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20563:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4078087656490217 : ℚ) / 200000000000) ≤ ((20380507033831403 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (20563:ℚ) := by decide +kernel
  have hratR : ((((4078087656490217 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((20380507033831403 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20563:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2321 : ((((20400370988938651 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20593 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20563 < q → q < 20593 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20593).mp (by decide +kernel))) hgap
  have hprev := thV_2320
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20593:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((20400370988938651 : ℚ) / 1000000000000) ≤ ((4078087656490217 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (20593:ℚ) := by decide +kernel
  have hratR : ((((20400370988938651 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4078087656490217 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20593:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2322 : ((((20410303986744921 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20599 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20593 < q → q < 20599 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20599).mp (by decide +kernel))) hgap
  have hprev := thV_2321
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20599:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((20410303986744921 : ℚ) / 1000000000000) ≤ ((20400370988938651 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (20599:ℚ) := by decide +kernel
  have hratR : ((((20410303986744921 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((20400370988938651 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20599:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2323 : ((((163361900535473 : ℚ) / 8000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20611 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20599 < q → q < 20611 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20611).mp (by decide +kernel))) hgap
  have hprev := thV_2322
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20611:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((163361900535473 : ℚ) / 8000000000) ≤ ((20410303986744921 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (20611:ℚ) := by decide +kernel
  have hratR : ((((163361900535473 : ℚ) / 8000000000) : ℚ) : ℝ) ≤ ((((20410303986744921 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20611:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2324 : ((((5107542980776671 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20627 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20611 < q → q < 20627 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20627).mp (by decide +kernel))) hgap
  have hprev := thV_2323
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20627:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5107542980776671 : ℚ) / 250000000000) ≤ ((163361900535473 : ℚ) / 8000000000) + Work.RHContract.RegionI.logLowQ (20627:ℚ) := by decide +kernel
  have hratR : ((((5107542980776671 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((163361900535473 : ℚ) / 8000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20627:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2325 : ((((10220053430435927 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20639 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20627 < q → q < 20639 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20639).mp (by decide +kernel))) hgap
  have hprev := thV_2324
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20639:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10220053430435927 : ℚ) / 500000000000) ≤ ((5107542980776671 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (20639:ℚ) := by decide +kernel
  have hratR : ((((10220053430435927 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((5107542980776671 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20639:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2326 : ((((20450041895536249 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20641 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20639 < q → q < 20641 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20641).mp (by decide +kernel))) hgap
  have hprev := thV_2325
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20641:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((20450041895536249 : ℚ) / 1000000000000) ≤ ((10220053430435927 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (20641:ℚ) := by decide +kernel
  have hratR : ((((20450041895536249 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((10220053430435927 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20641:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2327 : ((((20459977995472873 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20663 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20641 < q → q < 20663 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20663).mp (by decide +kernel))) hgap
  have hprev := thV_2326
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20663:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((20459977995472873 : ℚ) / 1000000000000) ≤ ((20450041895536249 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (20663:ℚ) := by decide +kernel
  have hratR : ((((20459977995472873 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((20450041895536249 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20663:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2328 : ((((10234957483076293 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20681 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20663 < q → q < 20681 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20681).mp (by decide +kernel))) hgap
  have hprev := thV_2327
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20681:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10234957483076293 : ℚ) / 500000000000) ≤ ((20459977995472873 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (20681:ℚ) := by decide +kernel
  have hratR : ((((10234957483076293 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((20459977995472873 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20681:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2329 : ((((10239926258453379 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20693 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20681 < q → q < 20693 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20693).mp (by decide +kernel))) hgap
  have hprev := thV_2328
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20693:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10239926258453379 : ℚ) / 500000000000) ≤ ((10234957483076293 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (20693:ℚ) := by decide +kernel
  have hratR : ((((10239926258453379 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((10234957483076293 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20693:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2330 : ((((10244895371994729 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20707 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20693 < q → q < 20707 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20707).mp (by decide +kernel))) hgap
  have hprev := thV_2329
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20707:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10244895371994729 : ℚ) / 500000000000) ≤ ((10239926258453379 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (20707:ℚ) := by decide +kernel
  have hratR : ((((10244895371994729 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((10239926258453379 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20707:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2331 : ((((640616545433877 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20717 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20707 < q → q < 20717 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20717).mp (by decide +kernel))) hgap
  have hprev := thV_2330
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20717:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((640616545433877 : ℚ) / 31250000000) ≤ ((10244895371994729 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (20717:ℚ) := by decide +kernel
  have hratR : ((((640616545433877 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((10244895371994729 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20717:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2332 : ((((4101933652062617 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20719 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20717 < q → q < 20719 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20719).mp (by decide +kernel))) hgap
  have hprev := thV_2331
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20719:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4101933652062617 : ℚ) / 200000000000) ≤ ((640616545433877 : ℚ) / 31250000000) + Work.RHContract.RegionI.logLowQ (20719:ℚ) := by decide +kernel
  have hratR : ((((4101933652062617 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((640616545433877 : ℚ) / 31250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20719:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2333 : ((((10259803822876489 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20731 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20719 < q → q < 20731 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20731).mp (by decide +kernel))) hgap
  have hprev := thV_2332
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20731:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10259803822876489 : ℚ) / 500000000000) ≤ ((4101933652062617 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (20731:ℚ) := by decide +kernel
  have hratR : ((((10259803822876489 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((4101933652062617 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20731:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2334 : ((((5132386902467171 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20743 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20731 < q → q < 20743 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20743).mp (by decide +kernel))) hgap
  have hprev := thV_2333
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20743:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5132386902467171 : ℚ) / 250000000000) ≤ ((10259803822876489 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (20743:ℚ) := by decide +kernel
  have hratR : ((((5132386902467171 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((10259803822876489 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20743:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2335 : ((((20539487766801937 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20747 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20743 < q → q < 20747 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20747).mp (by decide +kernel))) hgap
  have hprev := thV_2334
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20747:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((20539487766801937 : ℚ) / 1000000000000) ≤ ((5132386902467171 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (20747:ℚ) := by decide +kernel
  have hratR : ((((20539487766801937 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5132386902467171 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20747:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2336 : ((((2568678502516253 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20749 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20747 < q → q < 20749 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20749).mp (by decide +kernel))) hgap
  have hprev := thV_2335
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20749:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2568678502516253 : ℚ) / 125000000000) ≤ ((20539487766801937 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (20749:ℚ) := by decide +kernel
  have hratR : ((((2568678502516253 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((20539487766801937 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20749:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2337 : ((((10279684233109953 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20753 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20749 < q → q < 20753 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20753).mp (by decide +kernel))) hgap
  have hprev := thV_2336
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20753:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10279684233109953 : ℚ) / 500000000000) ≤ ((2568678502516253 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (20753:ℚ) := by decide +kernel
  have hratR : ((((10279684233109953 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((2568678502516253 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20753:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2338 : ((((20569309201382829 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20759 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20753 < q → q < 20759 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20759).mp (by decide +kernel))) hgap
  have hprev := thV_2337
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20759:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((20569309201382829 : ℚ) / 1000000000000) ≤ ((10279684233109953 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (20759:ℚ) := by decide +kernel
  have hratR : ((((20569309201382829 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((10279684233109953 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20759:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2339 : ((((4115850102888253 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20771 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20759 < q → q < 20771 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20771).mp (by decide +kernel))) hgap
  have hprev := thV_2338
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20771:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4115850102888253 : ℚ) / 200000000000) ≤ ((20569309201382829 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (20771:ℚ) := by decide +kernel
  have hratR : ((((4115850102888253 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((20569309201382829 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20771:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2340 : ((((514729798094579 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20773 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20771 < q → q < 20773 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20773).mp (by decide +kernel))) hgap
  have hprev := thV_2339
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20773:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((514729798094579 : ℚ) / 25000000000) ≤ ((4115850102888253 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (20773:ℚ) := by decide +kernel
  have hratR : ((((514729798094579 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((4115850102888253 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20773:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2341 : ((((20599134103059167 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20789 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20773 < q → q < 20789 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20789).mp (by decide +kernel))) hgap
  have hprev := thV_2340
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20789:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((20599134103059167 : ℚ) / 1000000000000) ≤ ((514729798094579 : ℚ) / 25000000000) + Work.RHContract.RegionI.logLowQ (20789:ℚ) := by decide +kernel
  have hratR : ((((20599134103059167 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((514729798094579 : ℚ) / 25000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20789:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2342 : ((((10304538573901531 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20807 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20789 < q → q < 20807 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20807).mp (by decide +kernel))) hgap
  have hprev := thV_2341
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20807:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10304538573901531 : ℚ) / 500000000000) ≤ ((20599134103059167 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (20807:ℚ) := by decide +kernel
  have hratR : ((((10304538573901531 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((20599134103059167 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20807:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2343 : ((((4123804057732767 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20809 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20807 < q → q < 20809 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20809).mp (by decide +kernel))) hgap
  have hprev := thV_2342
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20809:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4123804057732767 : ℚ) / 200000000000) ≤ ((10304538573901531 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (20809:ℚ) := by decide +kernel
  have hratR : ((((4123804057732767 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((10304538573901531 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20809:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2344 : ((((20628965349924641 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20849 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20809 < q → q < 20849 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20849).mp (by decide +kernel))) hgap
  have hprev := thV_2343
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20849:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((20628965349924641 : ℚ) / 1000000000000) ≤ ((4123804057732767 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (20849:ℚ) := by decide +kernel
  have hratR : ((((20628965349924641 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4123804057732767 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20849:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2345 : ((((10319455397411649 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20857 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20849 < q → q < 20857 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20857).mp (by decide +kernel))) hgap
  have hprev := thV_2344
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20857:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10319455397411649 : ℚ) / 500000000000) ≤ ((20628965349924641 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (20857:ℚ) := by decide +kernel
  have hratR : ((((10319455397411649 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((20628965349924641 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20857:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2346 : ((((5162214251639101 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20873 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20857 < q → q < 20873 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20873).mp (by decide +kernel))) hgap
  have hprev := thV_2345
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20873:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5162214251639101 : ℚ) / 250000000000) ≤ ((10319455397411649 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (20873:ℚ) := by decide +kernel
  have hratR : ((((5162214251639101 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((10319455397411649 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20873:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2347 : ((((10329401752850447 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20879 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20873 < q → q < 20879 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20879).mp (by decide +kernel))) hgap
  have hprev := thV_2346
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20879:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10329401752850447 : ℚ) / 500000000000) ≤ ((5162214251639101 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (20879:ℚ) := by decide +kernel
  have hratR : ((((10329401752850447 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((5162214251639101 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20879:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2348 : ((((2066875038793211 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20887 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20879 < q → q < 20887 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20887).mp (by decide +kernel))) hgap
  have hprev := thV_2347
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20887:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2066875038793211 : ℚ) / 100000000000) ≤ ((10329401752850447 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (20887:ℚ) := by decide +kernel
  have hratR : ((((2066875038793211 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((10329401752850447 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20887:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2349 : ((((413573954976309 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20897 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20887 < q → q < 20897 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20897).mp (by decide +kernel))) hgap
  have hprev := thV_2348
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20897:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((413573954976309 : ℚ) / 20000000000) ≤ ((2066875038793211 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (20897:ℚ) := by decide +kernel
  have hratR : ((((413573954976309 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ ((((2066875038793211 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20897:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2350 : ((((20688645205401729 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20899 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20897 < q → q < 20899 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20899).mp (by decide +kernel))) hgap
  have hprev := thV_2349
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20899:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((20688645205401729 : ℚ) / 1000000000000) ≤ ((413573954976309 : ℚ) / 20000000000) + Work.RHContract.RegionI.logLowQ (20899:ℚ) := by decide +kernel
  have hratR : ((((20688645205401729 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((413573954976309 : ℚ) / 20000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20899:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2351 : ((((20698592853366411 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20903 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20899 < q → q < 20903 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20903).mp (by decide +kernel))) hgap
  have hprev := thV_2350
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20903:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((20698592853366411 : ℚ) / 1000000000000) ≤ ((20688645205401729 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (20903:ℚ) := by decide +kernel
  have hratR : ((((20698592853366411 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((20688645205401729 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20903:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2352 : ((((4141708272416191 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20921 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20903 < q → q < 20921 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20921).mp (by decide +kernel))) hgap
  have hprev := thV_2351
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20921:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4141708272416191 : ℚ) / 200000000000) ≤ ((20698592853366411 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (20921:ℚ) := by decide +kernel
  have hratR : ((((4141708272416191 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((20698592853366411 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20921:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2353 : ((((4143698050622661 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20929 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20921 < q → q < 20929 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20929).mp (by decide +kernel))) hgap
  have hprev := thV_2352
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20929:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4143698050622661 : ℚ) / 200000000000) ≤ ((4141708272416191 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (20929:ℚ) := by decide +kernel
  have hratR : ((((4143698050622661 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((4141708272416191 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20929:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2354 : ((((10364219810918729 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20939 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20929 < q → q < 20939 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20939).mp (by decide +kernel))) hgap
  have hprev := thV_2353
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20939:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10364219810918729 : ℚ) / 500000000000) ≤ ((4143698050622661 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (20939:ℚ) := by decide +kernel
  have hratR : ((((10364219810918729 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((4143698050622661 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20939:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2355 : ((((2592298671568853 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20947 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20939 < q → q < 20947 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20947).mp (by decide +kernel))) hgap
  have hprev := thV_2354
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20947:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2592298671568853 : ℚ) / 125000000000) ≤ ((10364219810918729 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (20947:ℚ) := by decide +kernel
  have hratR : ((((2592298671568853 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((10364219810918729 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20947:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2356 : ((((20748339695974557 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20959 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20947 < q → q < 20959 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20959).mp (by decide +kernel))) hgap
  have hprev := thV_2355
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20959:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((20748339695974557 : ℚ) / 1000000000000) ≤ ((2592298671568853 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (20959:ℚ) := by decide +kernel
  have hratR : ((((20748339695974557 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2592298671568853 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20959:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2357 : ((((20758290210228881 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20963 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20959 < q → q < 20963 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20963).mp (by decide +kernel))) hgap
  have hprev := thV_2356
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20963:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((20758290210228881 : ℚ) / 1000000000000) ≤ ((20748339695974557 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (20963:ℚ) := by decide +kernel
  have hratR : ((((20758290210228881 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((20748339695974557 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20963:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2358 : ((((10384120791385249 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20981 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20963 < q → q < 20981 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20981).mp (by decide +kernel))) hgap
  have hprev := thV_2357
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20981:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10384120791385249 : ℚ) / 500000000000) ≤ ((20758290210228881 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (20981:ℚ) := by decide +kernel
  have hratR : ((((10384120791385249 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((20758290210228881 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20981:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2359 : ((((20778193050631913 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((20983 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20981 < q → q < 20983 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20983).mp (by decide +kernel))) hgap
  have hprev := thV_2358
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (20983:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((20778193050631913 : ℚ) / 1000000000000) ≤ ((10384120791385249 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (20983:ℚ) := by decide +kernel
  have hratR : ((((20778193050631913 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((10384120791385249 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (20983:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2360 : ((((20788145375962893 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21001 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 20983 < q → q < 21001 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21001).mp (by decide +kernel))) hgap
  have hprev := thV_2359
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21001:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((20788145375962893 : ℚ) / 1000000000000) ≤ ((20778193050631913 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (21001:ℚ) := by decide +kernel
  have hratR : ((((20788145375962893 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((20778193050631913 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21001:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2361 : ((((10399049088674171 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21011 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21001 < q → q < 21011 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21011).mp (by decide +kernel))) hgap
  have hprev := thV_2360
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21011:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10399049088674171 : ℚ) / 500000000000) ≤ ((20788145375962893 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (21011:ℚ) := by decide +kernel
  have hratR : ((((10399049088674171 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((20788145375962893 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21011:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2362 : ((((2601006384239687 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21013 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21011 < q → q < 21013 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21013).mp (by decide +kernel))) hgap
  have hprev := thV_2361
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21013:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2601006384239687 : ℚ) / 125000000000) ≤ ((10399049088674171 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (21013:ℚ) := by decide +kernel
  have hratR : ((((2601006384239687 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((10399049088674171 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21013:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2363 : ((((5204501040206721 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21017 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21013 < q → q < 21017 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21017).mp (by decide +kernel))) hgap
  have hprev := thV_2362
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21017:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5204501040206721 : ℚ) / 250000000000) ≤ ((2601006384239687 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (21017:ℚ) := by decide +kernel
  have hratR : ((((5204501040206721 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((2601006384239687 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21017:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2364 : ((((5206989335723201 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21019 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21017 < q → q < 21019 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21019).mp (by decide +kernel))) hgap
  have hprev := thV_2363
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21019:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5206989335723201 : ℚ) / 250000000000) ≤ ((5204501040206721 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (21019:ℚ) := by decide +kernel
  have hratR : ((((5206989335723201 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((5204501040206721 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21019:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2365 : ((((20837910715244629 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21023 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21019 < q → q < 21023 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21023).mp (by decide +kernel))) hgap
  have hprev := thV_2364
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21023:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((20837910715244629 : ℚ) / 1000000000000) ≤ ((5206989335723201 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (21023:ℚ) := by decide +kernel
  have hratR : ((((20837910715244629 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5206989335723201 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21023:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2366 : ((((20847864468059673 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21031 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21023 < q → q < 21031 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21031).mp (by decide +kernel))) hgap
  have hprev := thV_2365
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21031:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((20847864468059673 : ℚ) / 1000000000000) ≤ ((20837910715244629 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (21031:ℚ) := by decide +kernel
  have hratR : ((((20847864468059673 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((20837910715244629 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21031:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2367 : ((((20857819551357213 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21059 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21031 < q → q < 21059 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21059).mp (by decide +kernel))) hgap
  have hprev := thV_2366
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21059:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((20857819551357213 : ℚ) / 1000000000000) ≤ ((20847864468059673 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (21059:ℚ) := by decide +kernel
  have hratR : ((((20857819551357213 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((20847864468059673 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21059:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2368 : ((((4173554945924303 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21061 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21059 < q → q < 21061 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21061).mp (by decide +kernel))) hgap
  have hprev := thV_2367
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21061:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4173554945924303 : ℚ) / 200000000000) ≤ ((20857819551357213 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (21061:ℚ) := by decide +kernel
  have hratR : ((((4173554945924303 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((20857819551357213 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21061:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2369 : ((((10438865096366001 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21067 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21061 < q → q < 21067 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21067).mp (by decide +kernel))) hgap
  have hprev := thV_2368
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21067:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10438865096366001 : ℚ) / 500000000000) ≤ ((4173554945924303 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (21067:ℚ) := by decide +kernel
  have hratR : ((((10438865096366001 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((4173554945924303 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21067:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2370 : ((((10443843349792437 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21089 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21067 < q → q < 21089 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21089).mp (by decide +kernel))) hgap
  have hprev := thV_2369
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21089:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10443843349792437 : ℚ) / 500000000000) ≤ ((10438865096366001 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (21089:ℚ) := by decide +kernel
  have hratR : ((((10443843349792437 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((10438865096366001 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21089:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2371 : ((((1044882188764647 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21101 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21089 < q → q < 21101 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21101).mp (by decide +kernel))) hgap
  have hprev := thV_2370
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21101:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1044882188764647 : ℚ) / 50000000000) ≤ ((10443843349792437 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (21101:ℚ) := by decide +kernel
  have hratR : ((((1044882188764647 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((10443843349792437 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21101:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2372 : ((((20907601135307301 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21107 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21101 < q → q < 21107 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21107).mp (by decide +kernel))) hgap
  have hprev := thV_2371
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21107:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((20907601135307301 : ℚ) / 1000000000000) ≤ ((1044882188764647 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (21107:ℚ) := by decide +kernel
  have hratR : ((((20907601135307301 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1044882188764647 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21107:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2373 : ((((4183511831677769 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21121 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21107 < q → q < 21121 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21121).mp (by decide +kernel))) hgap
  have hprev := thV_2372
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21121:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4183511831677769 : ℚ) / 200000000000) ≤ ((20907601135307301 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (21121:ℚ) := by decide +kernel
  have hratR : ((((4183511831677769 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((20907601135307301 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21121:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2374 : ((((20927518033339821 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21139 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21121 < q → q < 21139 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21139).mp (by decide +kernel))) hgap
  have hprev := thV_2373
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21139:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((20927518033339821 : ℚ) / 1000000000000) ≤ ((4183511831677769 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (21139:ℚ) := by decide +kernel
  have hratR : ((((20927518033339821 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4183511831677769 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21139:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2375 : ((((10468738548748303 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21143 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21139 < q → q < 21143 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21143).mp (by decide +kernel))) hgap
  have hprev := thV_2374
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21143:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10468738548748303 : ℚ) / 500000000000) ≤ ((20927518033339821 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (21143:ℚ) := by decide +kernel
  have hratR : ((((10468738548748303 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((20927518033339821 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21143:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2376 : ((((20947436445394999 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21149 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21143 < q → q < 21149 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21149).mp (by decide +kernel))) hgap
  have hprev := thV_2375
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21149:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((20947436445394999 : ℚ) / 1000000000000) ≤ ((10468738548748303 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (21149:ℚ) := by decide +kernel
  have hratR : ((((20947436445394999 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((10468738548748303 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21149:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2377 : ((((20957396171490343 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21157 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21149 < q → q < 21157 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21157).mp (by decide +kernel))) hgap
  have hprev := thV_2376
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21157:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((20957396171490343 : ℚ) / 1000000000000) ≤ ((20947436445394999 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (21157:ℚ) := by decide +kernel
  have hratR : ((((20957396171490343 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((20947436445394999 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21157:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2378 : ((((5241839045284891 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21163 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21157 < q → q < 21163 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21163).mp (by decide +kernel))) hgap
  have hprev := thV_2377
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21163:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5241839045284891 : ℚ) / 250000000000) ≤ ((20957396171490343 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (21163:ℚ) := by decide +kernel
  have hratR : ((((5241839045284891 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((20957396171490343 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21163:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2379 : ((((10488658237131141 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21169 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21163 < q → q < 21169 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21169).mp (by decide +kernel))) hgap
  have hprev := thV_2378
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21169:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10488658237131141 : ℚ) / 500000000000) ≤ ((5241839045284891 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (21169:ℚ) := by decide +kernel
  have hratR : ((((10488658237131141 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((5241839045284891 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21169:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2380 : ((((2098727723966233 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21179 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21169 < q → q < 21179 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21179).mp (by decide +kernel))) hgap
  have hprev := thV_2379
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21179:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2098727723966233 : ℚ) / 100000000000) ≤ ((10488658237131141 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (21179:ℚ) := by decide +kernel
  have hratR : ((((2098727723966233 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((10488658237131141 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21179:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2381 : ((((4199447676544743 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21187 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21179 < q → q < 21187 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21187).mp (by decide +kernel))) hgap
  have hprev := thV_2380
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21187:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4199447676544743 : ℚ) / 200000000000) ≤ ((2098727723966233 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (21187:ℚ) := by decide +kernel
  have hratR : ((((4199447676544743 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((2098727723966233 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21187:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2382 : ((((2625899964320287 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21191 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21187 < q → q < 21191 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21191).mp (by decide +kernel))) hgap
  have hprev := thV_2381
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21191:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2625899964320287 : ℚ) / 125000000000) ≤ ((4199447676544743 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (21191:ℚ) := by decide +kernel
  have hratR : ((((2625899964320287 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((4199447676544743 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21191:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2383 : ((((21017161140776113 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21193 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21191 < q → q < 21193 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21193).mp (by decide +kernel))) hgap
  have hprev := thV_2382
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21193:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((21017161140776113 : ℚ) / 1000000000000) ≤ ((2625899964320287 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (21193:ℚ) := by decide +kernel
  have hratR : ((((21017161140776113 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2625899964320287 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21193:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2384 : ((((5256780853991623 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21211 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21193 < q → q < 21211 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21211).mp (by decide +kernel))) hgap
  have hprev := thV_2383
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21211:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5256780853991623 : ℚ) / 250000000000) ≤ ((21017161140776113 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (21211:ℚ) := by decide +kernel
  have hratR : ((((5256780853991623 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((21017161140776113 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21211:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2385 : ((((21037086162499263 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21221 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21211 < q → q < 21221 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21221).mp (by decide +kernel))) hgap
  have hprev := thV_2384
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21221:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((21037086162499263 : ℚ) / 1000000000000) ≤ ((5256780853991623 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (21221:ℚ) := by decide +kernel
  have hratR : ((((21037086162499263 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5256780853991623 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21221:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2386 : ((((5261762297932717 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21227 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21221 < q → q < 21227 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21227).mp (by decide +kernel))) hgap
  have hprev := thV_2385
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21227:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5261762297932717 : ℚ) / 250000000000) ≤ ((21037086162499263 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (21227:ℚ) := by decide +kernel
  have hratR : ((((5261762297932717 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((21037086162499263 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21227:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2387 : ((((2632126645339393 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21247 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21227 < q → q < 21247 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21247).mp (by decide +kernel))) hgap
  have hprev := thV_2386
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21247:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2632126645339393 : ℚ) / 125000000000) ≤ ((5261762297932717 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (21247:ℚ) := by decide +kernel
  have hratR : ((((2632126645339393 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((5261762297932717 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21247:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2388 : ((((21066978168604019 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21269 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21247 < q → q < 21269 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21269).mp (by decide +kernel))) hgap
  have hprev := thV_2387
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21269:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((21066978168604019 : ℚ) / 1000000000000) ≤ ((2632126645339393 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (21269:ℚ) := by decide +kernel
  have hratR : ((((21066978168604019 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2632126645339393 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21269:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2389 : ((((21076943550556453 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21277 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21269 < q → q < 21277 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21277).mp (by decide +kernel))) hgap
  have hprev := thV_2388
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21277:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((21076943550556453 : ℚ) / 1000000000000) ≤ ((21066978168604019 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (21277:ℚ) := by decide +kernel
  have hratR : ((((21076943550556453 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((21066978168604019 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21277:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2390 : ((((658965912951993 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21283 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21277 < q → q < 21283 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21283).mp (by decide +kernel))) hgap
  have hprev := thV_2389
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21283:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((658965912951993 : ℚ) / 31250000000) ≤ ((21076943550556453 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (21283:ℚ) := by decide +kernel
  have hratR : ((((658965912951993 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((21076943550556453 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21283:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2391 : ((((10548438143477149 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21313 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21283 < q → q < 21313 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21313).mp (by decide +kernel))) hgap
  have hprev := thV_2390
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21313:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10548438143477149 : ℚ) / 500000000000) ≤ ((658965912951993 : ℚ) / 31250000000) + Work.RHContract.RegionI.logLowQ (21313:ℚ) := by decide +kernel
  have hratR : ((((10548438143477149 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((658965912951993 : ℚ) / 31250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21313:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2392 : ((((21106843547106091 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21317 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21313 < q → q < 21317 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21317).mp (by decide +kernel))) hgap
  have hprev := thV_2391
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21317:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((21106843547106091 : ℚ) / 1000000000000) ≤ ((10548438143477149 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (21317:ℚ) := by decide +kernel
  have hratR : ((((21106843547106091 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((10548438143477149 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21317:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2393 : ((((5279202725268829 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21319 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21317 < q → q < 21319 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21319).mp (by decide +kernel))) hgap
  have hprev := thV_2392
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21319:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5279202725268829 : ℚ) / 250000000000) ≤ ((21106843547106091 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (21319:ℚ) := by decide +kernel
  have hratR : ((((5279202725268829 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((21106843547106091 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21319:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2394 : ((((10563389221326501 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21323 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21319 < q → q < 21323 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21323).mp (by decide +kernel))) hgap
  have hprev := thV_2393
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21323:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10563389221326501 : ℚ) / 500000000000) ≤ ((5279202725268829 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (21323:ℚ) := by decide +kernel
  have hratR : ((((10563389221326501 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((5279202725268829 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21323:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2395 : ((((5284186707008369 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21341 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21323 < q → q < 21341 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21341).mp (by decide +kernel))) hgap
  have hprev := thV_2394
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21341:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5284186707008369 : ℚ) / 250000000000) ≤ ((10563389221326501 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (21341:ℚ) := by decide +kernel
  have hratR : ((((5284186707008369 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((10563389221326501 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21341:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2396 : ((((21146715494523397 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21347 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21341 < q → q < 21347 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21347).mp (by decide +kernel))) hgap
  have hprev := thV_2395
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21347:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((21146715494523397 : ℚ) / 1000000000000) ≤ ((5284186707008369 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (21347:ℚ) := by decide +kernel
  have hratR : ((((21146715494523397 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5284186707008369 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21347:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2397 : ((((21156685565376437 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21377 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21347 < q → q < 21377 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21377).mp (by decide +kernel))) hgap
  have hprev := thV_2396
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21377:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((21156685565376437 : ℚ) / 1000000000000) ≤ ((21146715494523397 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (21377:ℚ) := by decide +kernel
  have hratR : ((((21156685565376437 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((21146715494523397 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21377:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2398 : ((((10583327864891799 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21379 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21377 < q → q < 21379 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21379).mp (by decide +kernel))) hgap
  have hprev := thV_2397
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21379:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10583327864891799 : ℚ) / 500000000000) ≤ ((21156685565376437 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (21379:ℚ) := by decide +kernel
  have hratR : ((((10583327864891799 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((21156685565376437 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21379:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2399 : ((((5294156520318187 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21383 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21379 < q → q < 21383 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21383).mp (by decide +kernel))) hgap
  have hprev := thV_2398
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21383:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5294156520318187 : ℚ) / 250000000000) ≤ ((10583327864891799 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (21383:ℚ) := by decide +kernel
  have hratR : ((((5294156520318187 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((10583327864891799 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21383:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2400 : ((((2118659680682091 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21391 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21383 < q → q < 21391 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21391).mp (by decide +kernel))) hgap
  have hprev := thV_2399
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21391:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2118659680682091 : ℚ) / 100000000000) ≤ ((5294156520318187 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (21391:ℚ) := by decide +kernel
  have hratR : ((((2118659680682091 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((5294156520318187 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21391:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2401 : ((((21196567812821537 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21397 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21391 < q → q < 21397 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21397).mp (by decide +kernel))) hgap
  have hprev := thV_2400
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21397:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((21196567812821537 : ℚ) / 1000000000000) ≤ ((2118659680682091 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (21397:ℚ) := by decide +kernel
  have hratR : ((((21196567812821537 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2118659680682091 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21397:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2402 : ((((21206539005746787 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21401 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21397 < q → q < 21401 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21401).mp (by decide +kernel))) hgap
  have hprev := thV_2401
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21401:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((21206539005746787 : ℚ) / 1000000000000) ≤ ((21196567812821537 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (21401:ℚ) := by decide +kernel
  have hratR : ((((21206539005746787 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((21196567812821537 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21401:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2403 : ((((10608255239496737 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21407 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21401 < q → q < 21407 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21407).mp (by decide +kernel))) hgap
  have hprev := thV_2402
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21407:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10608255239496737 : ℚ) / 500000000000) ≤ ((21206539005746787 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (21407:ℚ) := by decide +kernel
  have hratR : ((((10608255239496737 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((21206539005746787 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21407:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2404 : ((((4245296502529481 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21419 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21407 < q → q < 21419 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21419).mp (by decide +kernel))) hgap
  have hprev := thV_2403
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21419:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4245296502529481 : ℚ) / 200000000000) ≤ ((10608255239496737 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (21419:ℚ) := by decide +kernel
  have hratR : ((((4245296502529481 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((10608255239496737 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21419:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2405 : ((((10618227599856551 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21433 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21419 < q → q < 21433 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21433).mp (by decide +kernel))) hgap
  have hprev := thV_2404
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21433:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10618227599856551 : ℚ) / 500000000000) ≤ ((4245296502529481 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (21433:ℚ) := by decide +kernel
  have hratR : ((((10618227599856551 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((4245296502529481 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21433:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2406 : ((((5311607367965179 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21467 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21433 < q → q < 21467 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21467).mp (by decide +kernel))) hgap
  have hprev := thV_2405
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21467:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5311607367965179 : ℚ) / 250000000000) ≤ ((10618227599856551 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (21467:ℚ) := by decide +kernel
  have hratR : ((((5311607367965179 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((10618227599856551 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21467:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2407 : ((((425128087919191 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21481 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21467 < q → q < 21481 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21481).mp (by decide +kernel))) hgap
  have hprev := thV_2406
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21481:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((425128087919191 : ℚ) / 20000000000) ≤ ((5311607367965179 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (21481:ℚ) := by decide +kernel
  have hratR : ((((425128087919191 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ ((((5311607367965179 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21481:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2408 : ((((5316594899833997 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21487 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21481 < q → q < 21487 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21487).mp (by decide +kernel))) hgap
  have hprev := thV_2407
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21487:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5316594899833997 : ℚ) / 250000000000) ≤ ((425128087919191 : ℚ) / 20000000000) + Work.RHContract.RegionI.logLowQ (21487:ℚ) := by decide +kernel
  have hratR : ((((5316594899833997 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((425128087919191 : ℚ) / 20000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21487:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2409 : ((((21276354988854173 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21491 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21487 < q → q < 21491 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21491).mp (by decide +kernel))) hgap
  have hprev := thV_2408
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21491:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((21276354988854173 : ℚ) / 1000000000000) ≤ ((5316594899833997 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (21491:ℚ) := by decide +kernel
  have hratR : ((((21276354988854173 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5316594899833997 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21491:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2410 : ((((21286330471430241 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21493 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21491 < q → q < 21493 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21493).mp (by decide +kernel))) hgap
  have hprev := thV_2409
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21493:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((21286330471430241 : ℚ) / 1000000000000) ≤ ((21276354988854173 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (21493:ℚ) := by decide +kernel
  have hratR : ((((21286330471430241 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((21276354988854173 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21493:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2411 : ((((21296306233128007 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21499 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21493 < q → q < 21499 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21499).mp (by decide +kernel))) hgap
  have hprev := thV_2410
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21499:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((21296306233128007 : ℚ) / 1000000000000) ≤ ((21286330471430241 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (21499:ℚ) := by decide +kernel
  have hratR : ((((21296306233128007 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((21286330471430241 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21499:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2412 : ((((21306282180863633 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21503 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21499 < q → q < 21503 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21503).mp (by decide +kernel))) hgap
  have hprev := thV_2411
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21503:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((21306282180863633 : ℚ) / 1000000000000) ≤ ((21296306233128007 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (21503:ℚ) := by decide +kernel
  have hratR : ((((21306282180863633 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((21296306233128007 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21503:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2413 : ((((21316258779459347 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21517 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21503 < q → q < 21517 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21517).mp (by decide +kernel))) hgap
  have hprev := thV_2412
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21517:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((21316258779459347 : ℚ) / 1000000000000) ≤ ((21306282180863633 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (21517:ℚ) := by decide +kernel
  have hratR : ((((21316258779459347 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((21306282180863633 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21517:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2414 : ((((4265247112787461 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21521 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21517 < q → q < 21521 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21521).mp (by decide +kernel))) hgap
  have hprev := thV_2413
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21521:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4265247112787461 : ℚ) / 200000000000) ≤ ((21316258779459347 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (21521:ℚ) := by decide +kernel
  have hratR : ((((4265247112787461 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((21316258779459347 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21521:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2415 : ((((21336212441343429 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21523 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21521 < q → q < 21523 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21523).mp (by decide +kernel))) hgap
  have hprev := thV_2414
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21523:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((21336212441343429 : ℚ) / 1000000000000) ≤ ((4265247112787461 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (21523:ℚ) := by decide +kernel
  have hratR : ((((21336212441343429 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4265247112787461 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21523:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2416 : ((((21346189597482251 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21529 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21523 < q → q < 21529 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21529).mp (by decide +kernel))) hgap
  have hprev := thV_2415
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21529:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((21346189597482251 : ℚ) / 1000000000000) ≤ ((21336212441343429 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (21529:ℚ) := by decide +kernel
  have hratR : ((((21346189597482251 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((21336212441343429 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21529:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2417 : ((((4271233610669477 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21557 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21529 < q → q < 21557 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21557).mp (by decide +kernel))) hgap
  have hprev := thV_2416
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21557:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4271233610669477 : ℚ) / 200000000000) ≤ ((21346189597482251 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (21557:ℚ) := by decide +kernel
  have hratR : ((((4271233610669477 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((21346189597482251 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21557:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2418 : ((((21366146601985503 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21559 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21557 < q → q < 21559 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21559).mp (by decide +kernel))) hgap
  have hprev := thV_2417
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21559:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((21366146601985503 : ℚ) / 1000000000000) ≤ ((4271233610669477 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (21559:ℚ) := by decide +kernel
  have hratR : ((((21366146601985503 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4271233610669477 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21559:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2419 : ((((10688062668071887 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21563 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21559 < q → q < 21563 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21563).mp (by decide +kernel))) hgap
  have hprev := thV_2418
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21563:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10688062668071887 : ℚ) / 500000000000) ≤ ((21366146601985503 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (21563:ℚ) := by decide +kernel
  have hratR : ((((10688062668071887 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((21366146601985503 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21563:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2420 : ((((21386104348517757 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21569 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21563 < q → q < 21569 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21569).mp (by decide +kernel))) hgap
  have hprev := thV_2419
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21569:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((21386104348517757 : ℚ) / 1000000000000) ≤ ((10688062668071887 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (21569:ℚ) := by decide +kernel
  have hratR : ((((21386104348517757 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((10688062668071887 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21569:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2421 : ((((21396083731725657 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21577 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21569 < q → q < 21577 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21577).mp (by decide +kernel))) hgap
  have hprev := thV_2420
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21577:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((21396083731725657 : ℚ) / 1000000000000) ≤ ((21386104348517757 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (21577:ℚ) := by decide +kernel
  have hratR : ((((21396083731725657 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((21386104348517757 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21577:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2422 : ((((5351515894570663 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21587 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21577 < q → q < 21587 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21587).mp (by decide +kernel))) hgap
  have hprev := thV_2421
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21587:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5351515894570663 : ℚ) / 250000000000) ≤ ((21396083731725657 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (21587:ℚ) := by decide +kernel
  have hratR : ((((5351515894570663 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((21396083731725657 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21587:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2423 : ((((21416043517483709 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21589 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21587 < q → q < 21589 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21589).mp (by decide +kernel))) hgap
  have hprev := thV_2422
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21589:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((21416043517483709 : ℚ) / 1000000000000) ≤ ((5351515894570663 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (21589:ℚ) := by decide +kernel
  have hratR : ((((21416043517483709 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5351515894570663 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21589:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2424 : ((((10713011959888187 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21599 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21589 < q → q < 21599 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21599).mp (by decide +kernel))) hgap
  have hprev := thV_2423
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21599:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10713011959888187 : ℚ) / 500000000000) ≤ ((21416043517483709 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (21599:ℚ) := by decide +kernel
  have hratR : ((((10713011959888187 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((21416043517483709 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21599:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2425 : ((((21436004414661631 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21601 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21599 < q → q < 21601 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21601).mp (by decide +kernel))) hgap
  have hprev := thV_2424
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21601:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((21436004414661631 : ℚ) / 1000000000000) ≤ ((10713011959888187 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (21601:ℚ) := by decide +kernel
  have hratR : ((((21436004414661631 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((10713011959888187 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21601:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2426 : ((((10722992686190647 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21611 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21601 < q → q < 21611 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21611).mp (by decide +kernel))) hgap
  have hprev := thV_2425
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21611:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10722992686190647 : ℚ) / 500000000000) ≤ ((21436004414661631 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (21611:ℚ) := by decide +kernel
  have hratR : ((((10722992686190647 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((21436004414661631 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21611:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2427 : ((((10727983211321069 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21613 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21611 < q → q < 21613 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21613).mp (by decide +kernel))) hgap
  have hprev := thV_2426
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21613:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10727983211321069 : ℚ) / 500000000000) ≤ ((10722992686190647 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (21613:ℚ) := by decide +kernel
  have hratR : ((((10727983211321069 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((10722992686190647 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21613:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2428 : ((((2683243457244957 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21617 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21613 < q → q < 21617 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21617).mp (by decide +kernel))) hgap
  have hprev := thV_2427
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21617:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2683243457244957 : ℚ) / 125000000000) ≤ ((10727983211321069 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (21617:ℚ) := by decide +kernel
  have hratR : ((((2683243457244957 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((10727983211321069 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21617:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2429 : ((((5368982570027929 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21647 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21617 < q → q < 21647 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21647).mp (by decide +kernel))) hgap
  have hprev := thV_2428
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21647:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5368982570027929 : ℚ) / 250000000000) ≤ ((2683243457244957 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (21647:ℚ) := by decide +kernel
  have hratR : ((((5368982570027929 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((2683243457244957 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21647:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2430 : ((((2685739124331383 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21649 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21647 < q → q < 21649 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21649).mp (by decide +kernel))) hgap
  have hprev := thV_2429
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21649:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2685739124331383 : ℚ) / 125000000000) ≤ ((5368982570027929 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (21649:ℚ) := by decide +kernel
  have hratR : ((((2685739124331383 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((5368982570027929 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21649:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2431 : ((((4299179252666993 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21661 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21649 < q → q < 21661 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21661).mp (by decide +kernel))) hgap
  have hprev := thV_2430
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21661:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4299179252666993 : ℚ) / 200000000000) ≤ ((2685739124331383 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (21661:ℚ) := by decide +kernel
  have hratR : ((((4299179252666993 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((2685739124331383 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21661:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2432 : ((((10752940042928257 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21673 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21661 < q → q < 21673 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21673).mp (by decide +kernel))) hgap
  have hprev := thV_2431
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21673:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10752940042928257 : ℚ) / 500000000000) ≤ ((4299179252666993 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (21673:ℚ) := by decide +kernel
  have hratR : ((((10752940042928257 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((4299179252666993 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21673:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2433 : ((((10757932184837619 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21683 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21673 < q → q < 21683 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21683).mp (by decide +kernel))) hgap
  have hprev := thV_2432
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21683:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10757932184837619 : ℚ) / 500000000000) ≤ ((10752940042928257 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (21683:ℚ) := by decide +kernel
  have hratR : ((((10757932184837619 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((10752940042928257 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21683:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2434 : ((((10762924741646507 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21701 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21683 < q → q < 21701 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21701).mp (by decide +kernel))) hgap
  have hprev := thV_2433
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21701:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10762924741646507 : ℚ) / 500000000000) ≤ ((10757932184837619 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (21701:ℚ) := by decide +kernel
  have hratR : ((((10762924741646507 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((10757932184837619 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21701:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2435 : ((((5383958787431967 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21713 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21701 < q → q < 21713 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21713).mp (by decide +kernel))) hgap
  have hprev := thV_2434
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21713:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5383958787431967 : ℚ) / 250000000000) ≤ ((10762924741646507 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (21713:ℚ) := by decide +kernel
  have hratR : ((((5383958787431967 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((10762924741646507 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21713:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2436 : ((((5386455365182491 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21727 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21713 < q → q < 21727 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21727).mp (by decide +kernel))) hgap
  have hprev := thV_2435
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21727:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5386455365182491 : ℚ) / 250000000000) ≤ ((5383958787431967 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (21727:ℚ) := by decide +kernel
  have hratR : ((((5386455365182491 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((5383958787431967 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21727:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2437 : ((((21555808231882997 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21737 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21727 < q → q < 21737 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21737).mp (by decide +kernel))) hgap
  have hprev := thV_2436
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21737:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((21555808231882997 : ℚ) / 1000000000000) ≤ ((5386455365182491 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (21737:ℚ) := by decide +kernel
  have hratR : ((((21555808231882997 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5386455365182491 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21737:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2438 : ((((10782897547520407 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21739 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21737 < q → q < 21739 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21739).mp (by decide +kernel))) hgap
  have hprev := thV_2437
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21739:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10782897547520407 : ℚ) / 500000000000) ≤ ((21555808231882997 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (21739:ℚ) := by decide +kernel
  have hratR : ((((10782897547520407 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((21555808231882997 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21739:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2439 : ((((10787891255024823 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21751 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21739 < q → q < 21751 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21751).mp (by decide +kernel))) hgap
  have hprev := thV_2438
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21751:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10787891255024823 : ℚ) / 500000000000) ≤ ((10782897547520407 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (21751:ℚ) := by decide +kernel
  have hratR : ((((10787891255024823 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((10782897547520407 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21751:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2440 : ((((337277659388591 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21757 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21751 < q → q < 21757 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21757).mp (by decide +kernel))) hgap
  have hprev := thV_2439
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21757:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((337277659388591 : ℚ) / 15625000000) ≤ ((10787891255024823 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (21757:ℚ) := by decide +kernel
  have hratR : ((((337277659388591 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ ((((10787891255024823 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21757:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2441 : ((((21595758351206599 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21767 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21757 < q → q < 21767 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21767).mp (by decide +kernel))) hgap
  have hprev := thV_2440
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21767:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((21595758351206599 : ℚ) / 1000000000000) ≤ ((337277659388591 : ℚ) / 15625000000) + Work.RHContract.RegionI.logLowQ (21767:ℚ) := by decide +kernel
  have hratR : ((((21595758351206599 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((337277659388591 : ℚ) / 15625000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21767:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2442 : ((((5401436694288003 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21773 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21767 < q → q < 21773 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21773).mp (by decide +kernel))) hgap
  have hprev := thV_2441
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21773:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5401436694288003 : ℚ) / 250000000000) ≤ ((21595758351206599 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (21773:ℚ) := by decide +kernel
  have hratR : ((((5401436694288003 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((21595758351206599 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21773:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2443 : ((((21615735845888999 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21787 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21773 < q → q < 21787 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21787).mp (by decide +kernel))) hgap
  have hprev := thV_2442
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21787:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((21615735845888999 : ℚ) / 1000000000000) ≤ ((5401436694288003 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (21787:ℚ) := by decide +kernel
  have hratR : ((((21615735845888999 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5401436694288003 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21787:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2444 : ((((865029018610461 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21799 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21787 < q → q < 21799 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21799).mp (by decide +kernel))) hgap
  have hprev := thV_2443
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21799:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((865029018610461 : ℚ) / 40000000000) ≤ ((21615735845888999 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (21799:ℚ) := by decide +kernel
  have hratR : ((((865029018610461 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((21615735845888999 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21799:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2445 : ((((21635715268111873 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21803 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21799 < q → q < 21803 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21803).mp (by decide +kernel))) hgap
  have hprev := thV_2444
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21803:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((21635715268111873 : ℚ) / 1000000000000) ≤ ((865029018610461 : ℚ) / 40000000000) + Work.RHContract.RegionI.logLowQ (21803:ℚ) := by decide +kernel
  have hratR : ((((21635715268111873 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((865029018610461 : ℚ) / 40000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21803:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2446 : ((((173165645702957 : ℚ) / 8000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21817 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21803 < q → q < 21817 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21817).mp (by decide +kernel))) hgap
  have hprev := thV_2445
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21817:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((173165645702957 : ℚ) / 8000000000) ≤ ((21635715268111873 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (21817:ℚ) := by decide +kernel
  have hratR : ((((173165645702957 : ℚ) / 8000000000) : ℚ) : ℝ) ≤ ((((21635715268111873 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21817:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2447 : ((((5413924085238459 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21821 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21817 < q → q < 21821 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21821).mp (by decide +kernel))) hgap
  have hprev := thV_2446
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21821:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5413924085238459 : ℚ) / 250000000000) ≤ ((173165645702957 : ℚ) / 8000000000) + Work.RHContract.RegionI.logLowQ (21821:ℚ) := by decide +kernel
  have hratR : ((((5413924085238459 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((173165645702957 : ℚ) / 8000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21821:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2448 : ((((21665687793591461 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21839 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21821 < q → q < 21839 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21839).mp (by decide +kernel))) hgap
  have hprev := thV_2447
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21839:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((21665687793591461 : ℚ) / 1000000000000) ≤ ((5413924085238459 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (21839:ℚ) := by decide +kernel
  have hratR : ((((21665687793591461 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5413924085238459 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21839:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2449 : ((((10837839668902089 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21841 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21839 < q → q < 21841 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21841).mp (by decide +kernel))) hgap
  have hprev := thV_2448
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21841:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10837839668902089 : ℚ) / 500000000000) ≤ ((21665687793591461 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (21841:ℚ) := by decide +kernel
  have hratR : ((((10837839668902089 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((21665687793591461 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21841:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2450 : ((((4337134267953321 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21851 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21841 < q → q < 21851 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21851).mp (by decide +kernel))) hgap
  have hprev := thV_2449
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21851:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4337134267953321 : ℚ) / 200000000000) ≤ ((10837839668902089 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (21851:ℚ) := by decide +kernel
  have hratR : ((((4337134267953321 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((10837839668902089 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21851:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2451 : ((((4339132741555599 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21859 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21851 < q → q < 21859 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21859).mp (by decide +kernel))) hgap
  have hprev := thV_2450
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21859:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4339132741555599 : ℚ) / 200000000000) ≤ ((4337134267953321 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (21859:ℚ) := by decide +kernel
  have hratR : ((((4339132741555599 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((4337134267953321 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21859:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2452 : ((((1356603516172727 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21863 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21859 < q → q < 21863 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21863).mp (by decide +kernel))) hgap
  have hprev := thV_2451
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21863:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1356603516172727 : ℚ) / 62500000000) ≤ ((4339132741555599 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (21863:ℚ) := by decide +kernel
  have hratR : ((((1356603516172727 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((4339132741555599 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21863:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2453 : ((((4343129835119471 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21871 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21863 < q → q < 21871 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21871).mp (by decide +kernel))) hgap
  have hprev := thV_2452
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21871:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4343129835119471 : ℚ) / 200000000000) ≤ ((1356603516172727 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (21871:ℚ) := by decide +kernel
  have hratR : ((((4343129835119471 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((1356603516172727 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21871:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2454 : ((((10862821274776523 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21881 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21871 < q → q < 21881 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21881).mp (by decide +kernel))) hgap
  have hprev := thV_2453
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21881:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10862821274776523 : ℚ) / 500000000000) ≤ ((4343129835119471 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (21881:ℚ) := by decide +kernel
  have hratR : ((((10862821274776523 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((4343129835119471 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21881:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2455 : ((((10867818235889707 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21893 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21881 < q → q < 21893 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21893).mp (by decide +kernel))) hgap
  have hprev := thV_2454
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21893:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10867818235889707 : ℚ) / 500000000000) ≤ ((10862821274776523 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (21893:ℚ) := by decide +kernel
  have hratR : ((((10867818235889707 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((10862821274776523 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21893:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2456 : ((((10872815607924291 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21911 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21893 < q → q < 21911 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21911).mp (by decide +kernel))) hgap
  have hprev := thV_2455
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21911:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10872815607924291 : ℚ) / 500000000000) ≤ ((10867818235889707 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (21911:ℚ) := by decide +kernel
  have hratR : ((((10872815607924291 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((10867818235889707 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21911:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2457 : ((((21755626781085679 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21929 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21911 < q → q < 21929 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21929).mp (by decide +kernel))) hgap
  have hprev := thV_2456
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21929:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((21755626781085679 : ℚ) / 1000000000000) ≤ ((10872815607924291 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (21929:ℚ) := by decide +kernel
  have hratR : ((((21755626781085679 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((10872815607924291 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21929:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2458 : ((((4353124542213993 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21937 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21929 < q → q < 21937 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21937).mp (by decide +kernel))) hgap
  have hprev := thV_2457
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21937:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4353124542213993 : ℚ) / 200000000000) ≤ ((21755626781085679 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (21937:ℚ) := by decide +kernel
  have hratR : ((((4353124542213993 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((21755626781085679 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21937:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2459 : ((((21775618914527361 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21943 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21937 < q → q < 21943 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21943).mp (by decide +kernel))) hgap
  have hprev := thV_2458
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21943:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((21775618914527361 : ℚ) / 1000000000000) ≤ ((4353124542213993 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (21943:ℚ) := by decide +kernel
  have hratR : ((((21775618914527361 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4353124542213993 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21943:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2460 : ((((21785615937955649 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21961 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21943 < q → q < 21961 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21961).mp (by decide +kernel))) hgap
  have hprev := thV_2459
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21961:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((21785615937955649 : ℚ) / 1000000000000) ≤ ((21775618914527361 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (21961:ℚ) := by decide +kernel
  have hratR : ((((21785615937955649 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((21775618914527361 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21961:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2461 : ((((4359122737936587 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21977 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21961 < q → q < 21977 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21977).mp (by decide +kernel))) hgap
  have hprev := thV_2460
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21977:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4359122737936587 : ℚ) / 200000000000) ≤ ((21785615937955649 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (21977:ℚ) := by decide +kernel
  have hratR : ((((4359122737936587 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((21785615937955649 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21977:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2462 : ((((10902806039118513 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21991 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21977 < q → q < 21991 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21991).mp (by decide +kernel))) hgap
  have hprev := thV_2461
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21991:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10902806039118513 : ℚ) / 500000000000) ≤ ((4359122737936587 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (21991:ℚ) := by decide +kernel
  have hratR : ((((10902806039118513 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((4359122737936587 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21991:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2463 : ((((2726951342449099 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((21997 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21991 < q → q < 21997 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21997).mp (by decide +kernel))) hgap
  have hprev := thV_2462
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (21997:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2726951342449099 : ℚ) / 125000000000) ≤ ((10902806039118513 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (21997:ℚ) := by decide +kernel
  have hratR : ((((2726951342449099 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((10902806039118513 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (21997:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2464 : ((((2728201209209479 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22003 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 21997 < q → q < 22003 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22003).mp (by decide +kernel))) hgap
  have hprev := thV_2463
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22003:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2728201209209479 : ℚ) / 125000000000) ≤ ((2726951342449099 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (22003:ℚ) := by decide +kernel
  have hratR : ((((2728201209209479 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((2726951342449099 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22003:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2465 : ((((10917804531069553 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22013 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22003 < q → q < 22013 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22013).mp (by decide +kernel))) hgap
  have hprev := thV_2464
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22013:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10917804531069553 : ℚ) / 500000000000) ≤ ((2728201209209479 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (22013:ℚ) := by decide +kernel
  have hratR : ((((10917804531069553 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((2728201209209479 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22013:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2466 : ((((436912181727761 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22027 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22013 < q → q < 22027 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22027).mp (by decide +kernel))) hgap
  have hprev := thV_2465
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22027:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((436912181727761 : ℚ) / 20000000000) ≤ ((10917804531069553 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (22027:ℚ) := by decide +kernel
  have hratR : ((((436912181727761 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ ((((10917804531069553 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22027:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2467 : ((((21855609292215823 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22031 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22027 < q → q < 22031 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22031).mp (by decide +kernel))) hgap
  have hprev := thV_2466
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22031:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((21855609292215823 : ℚ) / 1000000000000) ≤ ((436912181727761 : ℚ) / 20000000000) + Work.RHContract.RegionI.logLowQ (22031:ℚ) := by decide +kernel
  have hratR : ((((21855609292215823 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((436912181727761 : ℚ) / 20000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22031:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2468 : ((((21865609770350033 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22037 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22031 < q → q < 22037 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22037).mp (by decide +kernel))) hgap
  have hprev := thV_2467
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22037:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((21865609770350033 : ℚ) / 1000000000000) ≤ ((21855609292215823 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (22037:ℚ) := by decide +kernel
  have hratR : ((((21865609770350033 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((21855609292215823 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22037:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2469 : ((((1093780516961829 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22039 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22037 < q → q < 22039 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22039).mp (by decide +kernel))) hgap
  have hprev := thV_2468
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22039:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1093780516961829 : ℚ) / 50000000000) ≤ ((21865609770350033 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (22039:ℚ) := by decide +kernel
  have hratR : ((((1093780516961829 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((21865609770350033 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22039:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2470 : ((((21885611452464261 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22051 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22039 < q → q < 22051 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22051).mp (by decide +kernel))) hgap
  have hprev := thV_2469
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22051:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((21885611452464261 : ℚ) / 1000000000000) ≤ ((1093780516961829 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (22051:ℚ) := by decide +kernel
  have hratR : ((((21885611452464261 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1093780516961829 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22051:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2471 : ((((2189561310973693 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22063 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22051 < q → q < 22063 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22063).mp (by decide +kernel))) hgap
  have hprev := thV_2470
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22063:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2189561310973693 : ℚ) / 100000000000) ≤ ((21885611452464261 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (22063:ℚ) := by decide +kernel
  have hratR : ((((2189561310973693 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((21885611452464261 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22063:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2472 : ((((21905614948292173 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22067 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22063 < q → q < 22067 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22067).mp (by decide +kernel))) hgap
  have hprev := thV_2471
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22067:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((21905614948292173 : ℚ) / 1000000000000) ≤ ((2189561310973693 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (22067:ℚ) := by decide +kernel
  have hratR : ((((21905614948292173 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2189561310973693 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22067:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2473 : ((((10957808529354837 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22073 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22067 < q → q < 22073 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22073).mp (by decide +kernel))) hgap
  have hprev := thV_2472
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22073:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10957808529354837 : ℚ) / 500000000000) ≤ ((21905614948292173 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (22073:ℚ) := by decide +kernel
  have hratR : ((((10957808529354837 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((21905614948292173 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22073:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2474 : ((((4385123888183109 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22079 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22073 < q → q < 22079 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22079).mp (by decide +kernel))) hgap
  have hprev := thV_2473
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22079:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4385123888183109 : ℚ) / 200000000000) ≤ ((10957808529354837 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (22079:ℚ) := by decide +kernel
  have hratR : ((((4385123888183109 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((10957808529354837 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22079:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2475 : ((((21935622366476647 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22091 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22079 < q → q < 22091 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22091).mp (by decide +kernel))) hgap
  have hprev := thV_2474
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22091:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((21935622366476647 : ℚ) / 1000000000000) ≤ ((4385123888183109 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (22091:ℚ) := by decide +kernel
  have hratR : ((((21935622366476647 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4385123888183109 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22091:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2476 : ((((10972812691284129 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22093 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22091 < q → q < 22093 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22093).mp (by decide +kernel))) hgap
  have hprev := thV_2475
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22093:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10972812691284129 : ℚ) / 500000000000) ≤ ((21935622366476647 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (22093:ℚ) := by decide +kernel
  have hratR : ((((10972812691284129 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((21935622366476647 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22093:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2477 : ((((21955629122609043 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22109 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22093 < q → q < 22109 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22109).mp (by decide +kernel))) hgap
  have hprev := thV_2476
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22109:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((21955629122609043 : ℚ) / 1000000000000) ≤ ((10972812691284129 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (22109:ℚ) := by decide +kernel
  have hratR : ((((21955629122609043 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((10972812691284129 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22109:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2478 : ((((4393126590621327 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22111 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22109 < q → q < 22111 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22111).mp (by decide +kernel))) hgap
  have hprev := thV_2477
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22111:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4393126590621327 : ℚ) / 200000000000) ≤ ((21955629122609043 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (22111:ℚ) := by decide +kernel
  have hratR : ((((4393126590621327 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((21955629122609043 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22111:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2479 : ((((4395127465234661 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22123 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22111 < q → q < 22123 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22123).mp (by decide +kernel))) hgap
  have hprev := thV_2478
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22123:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4395127465234661 : ℚ) / 200000000000) ≤ ((4393126590621327 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (22123:ℚ) := by decide +kernel
  have hratR : ((((4395127465234661 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((4393126590621327 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22123:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2480 : ((((21985641970414161 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22129 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22123 < q → q < 22129 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22129).mp (by decide +kernel))) hgap
  have hprev := thV_2479
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22129:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((21985641970414161 : ℚ) / 1000000000000) ≤ ((4395127465234661 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (22129:ℚ) := by decide +kernel
  have hratR : ((((21985641970414161 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4395127465234661 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22129:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2481 : ((((21995646795396963 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22133 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22129 < q → q < 22133 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22133).mp (by decide +kernel))) hgap
  have hprev := thV_2480
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22133:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((21995646795396963 : ℚ) / 1000000000000) ≤ ((21985641970414161 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (22133:ℚ) := by decide +kernel
  have hratR : ((((21995646795396963 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((21985641970414161 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22133:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2482 : ((((22005652252719443 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22147 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22133 < q → q < 22147 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22147).mp (by decide +kernel))) hgap
  have hprev := thV_2481
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22147:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((22005652252719443 : ℚ) / 1000000000000) ≤ ((21995646795396963 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (22147:ℚ) := by decide +kernel
  have hratR : ((((22005652252719443 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((21995646795396963 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22147:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2483 : ((((11007828990461143 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22153 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22147 < q → q < 22153 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22153).mp (by decide +kernel))) hgap
  have hprev := thV_2482
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22153:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11007828990461143 : ℚ) / 500000000000) ≤ ((22005652252719443 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (22153:ℚ) := by decide +kernel
  have hratR : ((((11007828990461143 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((22005652252719443 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22153:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2484 : ((((11012831944835641 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22157 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22153 < q → q < 22157 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22157).mp (by decide +kernel))) hgap
  have hprev := thV_2483
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22157:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11012831944835641 : ℚ) / 500000000000) ≤ ((11007828990461143 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (22157:ℚ) := by decide +kernel
  have hratR : ((((11012831944835641 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((11007828990461143 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22157:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2485 : ((((22035669888681131 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22159 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22157 < q → q < 22159 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22159).mp (by decide +kernel))) hgap
  have hprev := thV_2484
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22159:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((22035669888681131 : ℚ) / 1000000000000) ≤ ((11012831944835641 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (22159:ℚ) := by decide +kernel
  have hratR : ((((22035669888681131 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((11012831944835641 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22159:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2486 : ((((22045676429085083 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22171 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22159 < q → q < 22171 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22171).mp (by decide +kernel))) hgap
  have hprev := thV_2485
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22171:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((22045676429085083 : ℚ) / 1000000000000) ≤ ((22035669888681131 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (22171:ℚ) := by decide +kernel
  have hratR : ((((22045676429085083 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((22035669888681131 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22171:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2487 : ((((2205568378103101 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22189 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22171 < q → q < 22189 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22189).mp (by decide +kernel))) hgap
  have hprev := thV_2486
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22189:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2205568378103101 : ℚ) / 100000000000) ≤ ((22045676429085083 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (22189:ℚ) := by decide +kernel
  have hratR : ((((2205568378103101 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((22045676429085083 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22189:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2488 : ((((22065691313230193 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22193 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22189 < q → q < 22193 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22193).mp (by decide +kernel))) hgap
  have hprev := thV_2487
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22193:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((22065691313230193 : ℚ) / 1000000000000) ≤ ((2205568378103101 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (22193:ℚ) := by decide +kernel
  have hratR : ((((22065691313230193 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2205568378103101 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22193:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2489 : ((((5518925116562061 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22229 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22193 < q → q < 22229 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22229).mp (by decide +kernel))) hgap
  have hprev := thV_2488
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22229:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5518925116562061 : ℚ) / 250000000000) ≤ ((22065691313230193 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (22229:ℚ) := by decide +kernel
  have hratR : ((((5518925116562061 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((22065691313230193 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22229:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2490 : ((((22085710428691647 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22247 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22229 < q → q < 22247 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22247).mp (by decide +kernel))) hgap
  have hprev := thV_2489
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22247:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((22085710428691647 : ℚ) / 1000000000000) ≤ ((5518925116562061 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (22247:ℚ) := by decide +kernel
  have hratR : ((((22085710428691647 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5518925116562061 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22247:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2491 : ((((11047860465194099 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22259 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22247 < q → q < 22259 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22259).mp (by decide +kernel))) hgap
  have hprev := thV_2490
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22259:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11047860465194099 : ℚ) / 500000000000) ≤ ((22085710428691647 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (22259:ℚ) := by decide +kernel
  have hratR : ((((11047860465194099 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((22085710428691647 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22259:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2492 : ((((22105731971047259 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22271 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22259 < q → q < 22271 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22271).mp (by decide +kernel))) hgap
  have hprev := thV_2491
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22271:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((22105731971047259 : ℚ) / 1000000000000) ≤ ((11047860465194099 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (22271:ℚ) := by decide +kernel
  have hratR : ((((22105731971047259 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((11047860465194099 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22271:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2493 : ((((22115743101505171 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22273 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22271 < q → q < 22273 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22273).mp (by decide +kernel))) hgap
  have hprev := thV_2492
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22273:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((22115743101505171 : ℚ) / 1000000000000) ≤ ((22105731971047259 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (22273:ℚ) := by decide +kernel
  have hratR : ((((22115743101505171 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((22105731971047259 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22273:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2494 : ((((5531438602884149 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22277 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22273 < q → q < 22277 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22277).mp (by decide +kernel))) hgap
  have hprev := thV_2493
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22277:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5531438602884149 : ℚ) / 250000000000) ≤ ((22115743101505171 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (22277:ℚ) := by decide +kernel
  have hratR : ((((5531438602884149 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((22115743101505171 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22277:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2495 : ((((22135765811342687 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22279 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22277 < q → q < 22279 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22279).mp (by decide +kernel))) hgap
  have hprev := thV_2494
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22279:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((22135765811342687 : ℚ) / 1000000000000) ≤ ((5531438602884149 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (22279:ℚ) := by decide +kernel
  have hratR : ((((22135765811342687 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5531438602884149 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22279:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2496 : ((((11072888695336967 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22283 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22279 < q → q < 22283 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22283).mp (by decide +kernel))) hgap
  have hprev := thV_2495
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22283:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11072888695336967 : ℚ) / 500000000000) ≤ ((22135765811342687 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (22283:ℚ) := by decide +kernel
  have hratR : ((((11072888695336967 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((22135765811342687 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22283:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2497 : ((((4431157865791767 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22291 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22283 < q → q < 22291 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22291).mp (by decide +kernel))) hgap
  have hprev := thV_2496
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22291:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4431157865791767 : ℚ) / 200000000000) ≤ ((11072888695336967 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (22291:ℚ) := by decide +kernel
  have hratR : ((((4431157865791767 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((11072888695336967 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22291:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2498 : ((((22165801805432743 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22303 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22291 < q → q < 22303 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22303).mp (by decide +kernel))) hgap
  have hprev := thV_2497
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22303:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((22165801805432743 : ℚ) / 1000000000000) ≤ ((4431157865791767 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (22303:ℚ) := by decide +kernel
  have hratR : ((((22165801805432743 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4431157865791767 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22303:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2499 : ((((277197680765483 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22307 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22303 < q → q < 22307 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22307).mp (by decide +kernel))) hgap
  have hprev := thV_2498
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22307:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((277197680765483 : ℚ) / 12500000000) ≤ ((22165801805432743 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (22307:ℚ) := by decide +kernel
  have hratR : ((((277197680765483 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ ((((22165801805432743 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22307:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2500 : ((((69330714779959 : ℚ) / 3125000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22343 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22307 < q → q < 22343 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22343).mp (by decide +kernel))) hgap
  have hprev := thV_2499
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22343:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((69330714779959 : ℚ) / 3125000000) ≤ ((277197680765483 : ℚ) / 12500000000) + Work.RHContract.RegionI.logLowQ (22343:ℚ) := by decide +kernel
  have hratR : ((((69330714779959 : ℚ) / 3125000000) : ℚ) : ℝ) ≤ ((((277197680765483 : ℚ) / 12500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22343:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2501 : ((((173405025519059 : ℚ) / 7812500000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22349 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22343 < q → q < 22349 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22349).mp (by decide +kernel))) hgap
  have hprev := thV_2500
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22349:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((173405025519059 : ℚ) / 7812500000) ≤ ((69330714779959 : ℚ) / 3125000000) + Work.RHContract.RegionI.logLowQ (22349:ℚ) := by decide +kernel
  have hratR : ((((173405025519059 : ℚ) / 7812500000) : ℚ) : ℝ) ≤ ((((69330714779959 : ℚ) / 3125000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22349:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2502 : ((((22205858608373223 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22367 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22349 < q → q < 22367 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22367).mp (by decide +kernel))) hgap
  have hprev := thV_2501
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22367:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((22205858608373223 : ℚ) / 1000000000000) ≤ ((173405025519059 : ℚ) / 7812500000) + Work.RHContract.RegionI.logLowQ (22367:ℚ) := by decide +kernel
  have hratR : ((((22205858608373223 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((173405025519059 : ℚ) / 7812500000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22367:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2503 : ((((22215874039720341 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22369 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22367 < q → q < 22369 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22369).mp (by decide +kernel))) hgap
  have hprev := thV_2502
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22369:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((22215874039720341 : ℚ) / 1000000000000) ≤ ((22205858608373223 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (22369:ℚ) := by decide +kernel
  have hratR : ((((22215874039720341 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((22205858608373223 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22369:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2504 : ((((22225890007380321 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22381 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22369 < q → q < 22381 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22381).mp (by decide +kernel))) hgap
  have hprev := thV_2503
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22381:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((22225890007380321 : ℚ) / 1000000000000) ≤ ((22215874039720341 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (22381:ℚ) := by decide +kernel
  have hratR : ((((22225890007380321 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((22215874039720341 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22381:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2505 : ((((22235906421748073 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22391 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22381 < q → q < 22391 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22391).mp (by decide +kernel))) hgap
  have hprev := thV_2504
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22391:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((22235906421748073 : ℚ) / 1000000000000) ≤ ((22225890007380321 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (22391:ℚ) := by decide +kernel
  have hratR : ((((22235906421748073 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((22225890007380321 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22391:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2506 : ((((347592548500699 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22397 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22391 < q → q < 22397 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22397).mp (by decide +kernel))) hgap
  have hprev := thV_2505
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22397:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((347592548500699 : ℚ) / 15625000000) ≤ ((22235906421748073 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (22397:ℚ) := by decide +kernel
  have hratR : ((((347592548500699 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ ((((22235906421748073 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22397:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2507 : ((((22255940321983959 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22409 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22397 < q → q < 22409 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22409).mp (by decide +kernel))) hgap
  have hprev := thV_2506
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22409:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((22255940321983959 : ℚ) / 1000000000000) ≤ ((347592548500699 : ℚ) / 15625000000) + Work.RHContract.RegionI.logLowQ (22409:ℚ) := by decide +kernel
  have hratR : ((((22255940321983959 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((347592548500699 : ℚ) / 15625000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22409:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2508 : ((((22265958610348333 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22433 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22409 < q → q < 22433 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22433).mp (by decide +kernel))) hgap
  have hprev := thV_2507
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22433:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((22265958610348333 : ℚ) / 1000000000000) ≤ ((22255940321983959 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (22433:ℚ) := by decide +kernel
  have hratR : ((((22265958610348333 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((22255940321983959 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22433:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2509 : ((((22275977255266617 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22441 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22433 < q → q < 22441 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22441).mp (by decide +kernel))) hgap
  have hprev := thV_2508
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22441:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((22275977255266617 : ℚ) / 1000000000000) ≤ ((22265958610348333 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (22441:ℚ) := by decide +kernel
  have hratR : ((((22275977255266617 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((22265958610348333 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22441:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2510 : ((((22285996167516929 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22447 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22441 < q → q < 22447 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22447).mp (by decide +kernel))) hgap
  have hprev := thV_2509
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22447:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((22285996167516929 : ℚ) / 1000000000000) ≤ ((22275977255266617 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (22447:ℚ) := by decide +kernel
  have hratR : ((((22285996167516929 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((22275977255266617 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22447:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2511 : ((((22296015347027821 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22453 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22447 < q → q < 22453 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22453).mp (by decide +kernel))) hgap
  have hprev := thV_2510
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22453:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((22296015347027821 : ℚ) / 1000000000000) ≤ ((22285996167516929 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (22453:ℚ) := by decide +kernel
  have hratR : ((((22296015347027821 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((22285996167516929 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22453:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2512 : ((((22306035238884587 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22469 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22453 < q → q < 22469 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22469).mp (by decide +kernel))) hgap
  have hprev := thV_2511
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22469:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((22306035238884587 : ℚ) / 1000000000000) ≤ ((22296015347027821 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (22469:ℚ) := by decide +kernel
  have hratR : ((((22306035238884587 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((22296015347027821 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22469:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2513 : ((((22316055664667951 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22481 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22469 < q → q < 22481 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22481).mp (by decide +kernel))) hgap
  have hprev := thV_2512
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22481:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((22316055664667951 : ℚ) / 1000000000000) ≤ ((22306035238884587 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (22481:ℚ) := by decide +kernel
  have hratR : ((((22316055664667951 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((22306035238884587 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22481:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2514 : ((((5581519044852843 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22483 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22481 < q → q < 22483 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22483).mp (by decide +kernel))) hgap
  have hprev := thV_2513
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22483:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5581519044852843 : ℚ) / 250000000000) ≤ ((22316055664667951 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (22483:ℚ) := by decide +kernel
  have hratR : ((((5581519044852843 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((22316055664667951 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22483:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2515 : ((((11168048747219691 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22501 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22483 < q → q < 22501 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22501).mp (by decide +kernel))) hgap
  have hprev := thV_2514
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22501:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11168048747219691 : ℚ) / 500000000000) ≤ ((5581519044852843 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (22501:ℚ) := by decide +kernel
  have hratR : ((((11168048747219691 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((5581519044852843 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22501:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2516 : ((((5586529813448339 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22511 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22501 < q → q < 22511 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22511).mp (by decide +kernel))) hgap
  have hprev := thV_2515
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22511:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5586529813448339 : ℚ) / 250000000000) ≤ ((11168048747219691 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (22511:ℚ) := by decide +kernel
  have hratR : ((((5586529813448339 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((11168048747219691 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22511:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2517 : ((((11178070950603711 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22531 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22511 < q → q < 22531 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22531).mp (by decide +kernel))) hgap
  have hprev := thV_2516
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22531:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11178070950603711 : ℚ) / 500000000000) ≤ ((5586529813448339 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (22531:ℚ) := by decide +kernel
  have hratR : ((((11178070950603711 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((5586529813448339 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22531:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2518 : ((((5591541248088991 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22541 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22531 < q → q < 22541 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22541).mp (by decide +kernel))) hgap
  have hprev := thV_2517
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22541:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5591541248088991 : ℚ) / 250000000000) ≤ ((11178070950603711 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (22541:ℚ) := by decide +kernel
  have hratR : ((((5591541248088991 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((11178070950603711 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22541:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2519 : ((((11188094086113889 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22543 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22541 < q → q < 22543 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22543).mp (by decide +kernel))) hgap
  have hprev := thV_2518
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22543:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11188094086113889 : ℚ) / 500000000000) ≤ ((5591541248088991 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (22543:ℚ) := by decide +kernel
  have hratR : ((((11188094086113889 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((5591541248088991 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22543:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2520 : ((((5596552904555547 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22549 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22543 < q → q < 22549 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22549).mp (by decide +kernel))) hgap
  have hprev := thV_2519
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22549:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5596552904555547 : ℚ) / 250000000000) ≤ ((11188094086113889 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (22549:ℚ) := by decide +kernel
  have hratR : ((((5596552904555547 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((11188094086113889 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22549:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2521 : ((((559905896553993 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22567 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22549 < q → q < 22567 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22567).mp (by decide +kernel))) hgap
  have hprev := thV_2520
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22567:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((559905896553993 : ℚ) / 25000000000) ≤ ((5596552904555547 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (22567:ℚ) := by decide +kernel
  have hratR : ((((559905896553993 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((5596552904555547 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22567:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2522 : ((((2800782535416439 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22571 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22567 < q → q < 22571 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22571).mp (by decide +kernel))) hgap
  have hprev := thV_2521
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22571:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2800782535416439 : ℚ) / 125000000000) ≤ ((559905896553993 : ℚ) / 25000000000) + Work.RHContract.RegionI.logLowQ (22571:ℚ) := by decide +kernel
  have hratR : ((((2800782535416439 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((559905896553993 : ℚ) / 25000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22571:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2523 : ((((1401017799569291 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22573 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22571 < q → q < 22573 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22573).mp (by decide +kernel))) hgap
  have hprev := thV_2522
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22573:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1401017799569291 : ℚ) / 62500000000) ≤ ((2800782535416439 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (22573:ℚ) := by decide +kernel
  have hratR : ((((1401017799569291 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((2800782535416439 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22573:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2524 : ((((22426311073346139 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22613 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22573 < q → q < 22613 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22613).mp (by decide +kernel))) hgap
  have hprev := thV_2523
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22613:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((22426311073346139 : ℚ) / 1000000000000) ≤ ((1401017799569291 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (22613:ℚ) := by decide +kernel
  have hratR : ((((22426311073346139 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1401017799569291 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22613:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2525 : ((((22436337618882527 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22619 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22613 < q → q < 22619 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22619).mp (by decide +kernel))) hgap
  have hprev := thV_2524
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22619:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((22436337618882527 : ℚ) / 1000000000000) ≤ ((22426311073346139 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (22619:ℚ) := by decide +kernel
  have hratR : ((((22436337618882527 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((22426311073346139 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22619:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2526 : ((((4489272850567249 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22621 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22619 < q → q < 22621 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22621).mp (by decide +kernel))) hgap
  have hprev := thV_2525
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22621:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4489272850567249 : ℚ) / 200000000000) ≤ ((22436337618882527 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (22621:ℚ) := by decide +kernel
  have hratR : ((((4489272850567249 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((22436337618882527 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22621:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2527 : ((((5614097898461827 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22637 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22621 < q → q < 22637 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22637).mp (by decide +kernel))) hgap
  have hprev := thV_2526
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22637:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5614097898461827 : ℚ) / 250000000000) ≤ ((4489272850567249 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (22637:ℚ) := by decide +kernel
  have hratR : ((((5614097898461827 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((4489272850567249 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22637:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2528 : ((((22466419023205399 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22639 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22637 < q → q < 22639 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22639).mp (by decide +kernel))) hgap
  have hprev := thV_2527
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22639:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((22466419023205399 : ℚ) / 1000000000000) ≤ ((5614097898461827 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (22639:ℚ) := by decide +kernel
  have hratR : ((((22466419023205399 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5614097898461827 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22639:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2529 : ((((5619111657308533 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22643 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22639 < q → q < 22643 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22643).mp (by decide +kernel))) hgap
  have hprev := thV_2528
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22643:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5619111657308533 : ℚ) / 250000000000) ≤ ((22466419023205399 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (22643:ℚ) := by decide +kernel
  have hratR : ((((5619111657308533 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((22466419023205399 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22643:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2530 : ((((22486474588510539 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22651 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22643 < q → q < 22651 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22651).mp (by decide +kernel))) hgap
  have hprev := thV_2529
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22651:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((22486474588510539 : ℚ) / 1000000000000) ≤ ((5619111657308533 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (22651:ℚ) := by decide +kernel
  have hratR : ((((22486474588510539 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5619111657308533 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22651:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2531 : ((((5624125835534567 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22669 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22651 < q → q < 22669 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22669).mp (by decide +kernel))) hgap
  have hprev := thV_2530
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22669:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5624125835534567 : ℚ) / 250000000000) ≤ ((22486474588510539 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (22669:ℚ) := by decide +kernel
  have hratR : ((((5624125835534567 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((22486474588510539 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22669:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2532 : ((((22506532536799787 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22679 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22669 < q → q < 22679 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22679).mp (by decide +kernel))) hgap
  have hprev := thV_2531
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22679:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((22506532536799787 : ℚ) / 1000000000000) ≤ ((5624125835534567 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (22679:ℚ) := by decide +kernel
  have hratR : ((((22506532536799787 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5624125835534567 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22679:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2533 : ((((22516562260445229 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22691 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22679 < q → q < 22691 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22691).mp (by decide +kernel))) hgap
  have hprev := thV_2532
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22691:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((22516562260445229 : ℚ) / 1000000000000) ≤ ((22506532536799787 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (22691:ℚ) := by decide +kernel
  have hratR : ((((22516562260445229 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((22506532536799787 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22691:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2534 : ((((4505318449695547 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22697 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22691 < q → q < 22697 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22697).mp (by decide +kernel))) hgap
  have hprev := thV_2533
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22697:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4505318449695547 : ℚ) / 200000000000) ≤ ((22516562260445229 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (22697:ℚ) := by decide +kernel
  have hratR : ((((4505318449695547 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((22516562260445229 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22697:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2535 : ((((22536622324623731 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22699 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22697 < q → q < 22699 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22699).mp (by decide +kernel))) hgap
  have hprev := thV_2534
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22699:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((22536622324623731 : ℚ) / 1000000000000) ≤ ((4505318449695547 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (22699:ℚ) := by decide +kernel
  have hratR : ((((22536622324623731 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4505318449695547 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22699:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2536 : ((((5636663210305189 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22709 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22699 < q → q < 22709 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22709).mp (by decide +kernel))) hgap
  have hprev := thV_2535
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22709:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5636663210305189 : ℚ) / 250000000000) ≤ ((22536622324623731 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (22709:ℚ) := by decide +kernel
  have hratR : ((((5636663210305189 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((22536622324623731 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22709:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2537 : ((((22556683710038979 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22717 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22709 < q → q < 22717 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22717).mp (by decide +kernel))) hgap
  have hprev := thV_2536
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22717:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((22556683710038979 : ℚ) / 1000000000000) ≤ ((5636663210305189 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (22717:ℚ) := by decide +kernel
  have hratR : ((((22556683710038979 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5636663210305189 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22717:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2538 : ((((2256671475492129 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22721 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22717 < q → q < 22721 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22721).mp (by decide +kernel))) hgap
  have hprev := thV_2537
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22721:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2256671475492129 : ℚ) / 100000000000) ≤ ((22556683710038979 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (22721:ℚ) := by decide +kernel
  have hratR : ((((2256671475492129 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((22556683710038979 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22721:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2539 : ((((2822093257980203 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22727 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22721 < q → q < 22727 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22727).mp (by decide +kernel))) hgap
  have hprev := thV_2538
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22727:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2822093257980203 : ℚ) / 125000000000) ≤ ((2256671475492129 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (22727:ℚ) := by decide +kernel
  have hratR : ((((2822093257980203 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((2256671475492129 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22727:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2540 : ((((5646694475157237 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22739 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22727 < q → q < 22739 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22739).mp (by decide +kernel))) hgap
  have hprev := thV_2539
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22739:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5646694475157237 : ℚ) / 250000000000) ≤ ((2822093257980203 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (22739:ℚ) := by decide +kernel
  have hratR : ((((5646694475157237 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((2822093257980203 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22739:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2541 : ((((1129840491268351 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22741 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22739 < q → q < 22741 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22741).mp (by decide +kernel))) hgap
  have hprev := thV_2540
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22741:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1129840491268351 : ℚ) / 50000000000) ≤ ((5646694475157237 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (22741:ℚ) := by decide +kernel
  have hratR : ((((1129840491268351 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((5646694475157237 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22741:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2542 : ((((22606842189742837 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22751 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22741 < q → q < 22751 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22751).mp (by decide +kernel))) hgap
  have hprev := thV_2541
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22751:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((22606842189742837 : ℚ) / 1000000000000) ≤ ((1129840491268351 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (22751:ℚ) := by decide +kernel
  have hratR : ((((22606842189742837 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1129840491268351 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22751:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2543 : ((((4523375068995971 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22769 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22751 < q → q < 22769 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22769).mp (by decide +kernel))) hgap
  have hprev := thV_2542
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22769:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4523375068995971 : ℚ) / 200000000000) ≤ ((22606842189742837 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (22769:ℚ) := by decide +kernel
  have hratR : ((((4523375068995971 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((22606842189742837 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22769:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2544 : ((((905076354060403 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22777 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22769 < q → q < 22777 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22777).mp (by decide +kernel))) hgap
  have hprev := thV_2543
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22777:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((905076354060403 : ℚ) / 40000000000) ≤ ((4523375068995971 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (22777:ℚ) := by decide +kernel
  have hratR : ((((905076354060403 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((4523375068995971 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22777:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2545 : ((((11318471310714617 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22783 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22777 < q → q < 22783 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22783).mp (by decide +kernel))) hgap
  have hprev := thV_2544
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22783:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11318471310714617 : ℚ) / 500000000000) ≤ ((905076354060403 : ℚ) / 40000000000) + Work.RHContract.RegionI.logLowQ (22783:ℚ) := by decide +kernel
  have hratR : ((((11318471310714617 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((905076354060403 : ℚ) / 40000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22783:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2546 : ((((11323488283451243 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22787 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22783 < q → q < 22787 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22787).mp (by decide +kernel))) hgap
  have hprev := thV_2545
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22787:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11323488283451243 : ℚ) / 500000000000) ≤ ((11318471310714617 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (22787:ℚ) := by decide +kernel
  have hratR : ((((11323488283451243 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((11318471310714617 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22787:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2547 : ((((5664252847421053 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22807 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22787 < q → q < 22807 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22807).mp (by decide +kernel))) hgap
  have hprev := thV_2546
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22807:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5664252847421053 : ℚ) / 250000000000) ≤ ((11323488283451243 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (22807:ℚ) := by decide +kernel
  have hratR : ((((5664252847421053 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((11323488283451243 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22807:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2548 : ((((22667046387835311 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22811 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22807 < q → q < 22811 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22811).mp (by decide +kernel))) hgap
  have hprev := thV_2547
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22811:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((22667046387835311 : ℚ) / 1000000000000) ≤ ((5664252847421053 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (22811:ℚ) := by decide +kernel
  have hratR : ((((22667046387835311 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5664252847421053 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22811:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2549 : ((((22677081648982817 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22817 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22811 < q → q < 22817 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22817).mp (by decide +kernel))) hgap
  have hprev := thV_2548
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22817:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((22677081648982817 : ℚ) / 1000000000000) ≤ ((22667046387835311 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (22817:ℚ) := by decide +kernel
  have hratR : ((((22677081648982817 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((22667046387835311 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22817:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2550 : ((((2268711848665791 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22853 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22817 < q → q < 22853 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22853).mp (by decide +kernel))) hgap
  have hprev := thV_2549
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22853:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2268711848665791 : ℚ) / 100000000000) ≤ ((22677081648982817 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (22853:ℚ) := by decide +kernel
  have hratR : ((((2268711848665791 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((22677081648982817 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22853:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2551 : ((((2269715558684613 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22859 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22853 < q → q < 22859 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22859).mp (by decide +kernel))) hgap
  have hprev := thV_2550
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22859:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2269715558684613 : ℚ) / 100000000000) ≤ ((2268711848665791 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (22859:ℚ) := by decide +kernel
  have hratR : ((((2269715558684613 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((2268711848665791 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22859:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2552 : ((((11353596387261707 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22861 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22859 < q → q < 22861 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22861).mp (by decide +kernel))) hgap
  have hprev := thV_2551
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22861:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11353596387261707 : ℚ) / 500000000000) ≤ ((2269715558684613 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (22861:ℚ) := by decide +kernel
  have hratR : ((((11353596387261707 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((2269715558684613 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22861:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2553 : ((((567930759988281 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22871 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22861 < q → q < 22871 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22871).mp (by decide +kernel))) hgap
  have hprev := thV_2552
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22871:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((567930759988281 : ℚ) / 25000000000) ≤ ((11353596387261707 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (22871:ℚ) := by decide +kernel
  have hratR : ((((567930759988281 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((11353596387261707 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22871:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2554 : ((((1420454267927851 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22877 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22871 < q → q < 22877 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22877).mp (by decide +kernel))) hgap
  have hprev := thV_2553
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22877:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1420454267927851 : ℚ) / 62500000000) ≤ ((567930759988281 : ℚ) / 25000000000) + Work.RHContract.RegionI.logLowQ (22877:ℚ) := by decide +kernel
  have hratR : ((((1420454267927851 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((567930759988281 : ℚ) / 25000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22877:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2555 : ((((22737307222698687 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22901 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22877 < q → q < 22901 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22901).mp (by decide +kernel))) hgap
  have hprev := thV_2554
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22901:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((22737307222698687 : ℚ) / 1000000000000) ≤ ((1420454267927851 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (22901:ℚ) := by decide +kernel
  have hratR : ((((22737307222698687 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1420454267927851 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22901:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2556 : ((((1421709151282171 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22907 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22901 < q → q < 22907 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22907).mp (by decide +kernel))) hgap
  have hprev := thV_2555
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22907:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1421709151282171 : ℚ) / 62500000000) ≤ ((22737307222698687 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (22907:ℚ) := by decide +kernel
  have hratR : ((((1421709151282171 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((22737307222698687 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22907:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2557 : ((((22757386229310991 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22921 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22907 < q → q < 22921 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22921).mp (by decide +kernel))) hgap
  have hprev := thV_2556
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22921:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((22757386229310991 : ℚ) / 1000000000000) ≤ ((1421709151282171 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (22921:ℚ) := by decide +kernel
  have hratR : ((((22757386229310991 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1421709151282171 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22921:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2558 : ((((4553485347182709 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22937 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22921 < q → q < 22937 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22937).mp (by decide +kernel))) hgap
  have hprev := thV_2557
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22937:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4553485347182709 : ℚ) / 200000000000) ≤ ((22757386229310991 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (22937:ℚ) := by decide +kernel
  have hratR : ((((4553485347182709 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((22757386229310991 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22937:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2559 : ((((911098700162719 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22943 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22937 < q → q < 22943 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22943).mp (by decide +kernel))) hgap
  have hprev := thV_2558
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22943:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((911098700162719 : ℚ) / 40000000000) ≤ ((4553485347182709 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (22943:ℚ) := by decide +kernel
  have hratR : ((((911098700162719 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((4553485347182709 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22943:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2560 : ((((22787509056467827 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22961 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22943 < q → q < 22961 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22961).mp (by decide +kernel))) hgap
  have hprev := thV_2559
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22961:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((22787509056467827 : ℚ) / 1000000000000) ≤ ((911098700162719 : ℚ) / 40000000000) + Work.RHContract.RegionI.logLowQ (22961:ℚ) := by decide +kernel
  have hratR : ((((22787509056467827 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((911098700162719 : ℚ) / 40000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22961:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2561 : ((((11398775347984053 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22963 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22961 < q → q < 22963 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22963).mp (by decide +kernel))) hgap
  have hprev := thV_2560
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22963:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11398775347984053 : ℚ) / 500000000000) ≤ ((22787509056467827 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (22963:ℚ) := by decide +kernel
  have hratR : ((((11398775347984053 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((22787509056467827 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22963:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2562 : ((((11403796385428379 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22973 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22963 < q → q < 22973 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22973).mp (by decide +kernel))) hgap
  have hprev := thV_2561
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22973:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11403796385428379 : ℚ) / 500000000000) ≤ ((11398775347984053 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (22973:ℚ) := by decide +kernel
  have hratR : ((((11403796385428379 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((11398775347984053 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22973:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2563 : ((((570440892898847 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((22993 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22973 < q → q < 22993 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22993).mp (by decide +kernel))) hgap
  have hprev := thV_2562
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (22993:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((570440892898847 : ℚ) / 25000000000) ≤ ((11403796385428379 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (22993:ℚ) := by decide +kernel
  have hratR : ((((570440892898847 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((11403796385428379 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (22993:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2564 : ((((5706919773967857 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23003 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 22993 < q → q < 23003 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23003).mp (by decide +kernel))) hgap
  have hprev := thV_2563
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23003:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5706919773967857 : ℚ) / 250000000000) ≤ ((570440892898847 : ℚ) / 25000000000) + Work.RHContract.RegionI.logLowQ (23003:ℚ) := by decide +kernel
  have hratR : ((((5706919773967857 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((570440892898847 : ℚ) / 25000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23003:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2565 : ((((22837722823509239 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23011 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23003 < q → q < 23011 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23011).mp (by decide +kernel))) hgap
  have hprev := thV_2564
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23011:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((22837722823509239 : ℚ) / 1000000000000) ≤ ((5706919773967857 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (23011:ℚ) := by decide +kernel
  have hratR : ((((22837722823509239 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5706919773967857 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23011:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2566 : ((((22847766811857923 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23017 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23011 < q → q < 23017 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23017).mp (by decide +kernel))) hgap
  have hprev := thV_2565
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23017:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((22847766811857923 : ℚ) / 1000000000000) ≤ ((22837722823509239 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (23017:ℚ) := by decide +kernel
  have hratR : ((((22847766811857923 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((22837722823509239 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23017:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2567 : ((((11428905486988051 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23021 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23017 < q → q < 23021 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23021).mp (by decide +kernel))) hgap
  have hprev := thV_2566
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23021:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11428905486988051 : ℚ) / 500000000000) ≤ ((22847766811857923 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (23021:ℚ) := by decide +kernel
  have hratR : ((((11428905486988051 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((22847766811857923 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23021:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2568 : ((((285848192458649 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23027 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23021 < q → q < 23027 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23027).mp (by decide +kernel))) hgap
  have hprev := thV_2567
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23027:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((285848192458649 : ℚ) / 12500000000) ≤ ((11428905486988051 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (23027:ℚ) := by decide +kernel
  have hratR : ((((285848192458649 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ ((((11428905486988051 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23027:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2569 : ((((714934372070579 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23029 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23027 < q → q < 23029 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23029).mp (by decide +kernel))) hgap
  have hprev := thV_2568
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23029:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((714934372070579 : ℚ) / 31250000000) ≤ ((285848192458649 : ℚ) / 12500000000) + Work.RHContract.RegionI.logLowQ (23029:ℚ) := by decide +kernel
  have hratR : ((((714934372070579 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((285848192458649 : ℚ) / 12500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23029:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2570 : ((((11443972424982989 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23039 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23029 < q → q < 23039 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23039).mp (by decide +kernel))) hgap
  have hprev := thV_2569
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23039:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11443972424982989 : ℚ) / 500000000000) ≤ ((714934372070579 : ℚ) / 31250000000) + Work.RHContract.RegionI.logLowQ (23039:ℚ) := by decide +kernel
  have hratR : ((((11443972424982989 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((714934372070579 : ℚ) / 31250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23039:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2571 : ((((2862248735059873 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23041 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23039 < q → q < 23041 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23041).mp (by decide +kernel))) hgap
  have hprev := thV_2570
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23041:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2862248735059873 : ℚ) / 125000000000) ≤ ((11443972424982989 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (23041:ℚ) := by decide +kernel
  have hratR : ((((2862248735059873 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((11443972424982989 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23041:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2572 : ((((2863504428958393 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23053 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23041 < q → q < 23053 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23053).mp (by decide +kernel))) hgap
  have hprev := thV_2571
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23053:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2863504428958393 : ℚ) / 125000000000) ≤ ((2862248735059873 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (23053:ℚ) := by decide +kernel
  have hratR : ((((2863504428958393 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((2862248735059873 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23053:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2573 : ((((22918081156353461 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23057 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23053 < q → q < 23057 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23057).mp (by decide +kernel))) hgap
  have hprev := thV_2572
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23057:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((22918081156353461 : ℚ) / 1000000000000) ≤ ((2863504428958393 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (23057:ℚ) := by decide +kernel
  have hratR : ((((22918081156353461 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2863504428958393 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23057:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2574 : ((((2292812696777757 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23059 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23057 < q → q < 23059 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23059).mp (by decide +kernel))) hgap
  have hprev := thV_2573
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23059:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2292812696777757 : ℚ) / 100000000000) ≤ ((22918081156353461 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (23059:ℚ) := by decide +kernel
  have hratR : ((((2292812696777757 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((22918081156353461 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23059:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2575 : ((((4587634590530939 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23063 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23059 < q → q < 23063 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23063).mp (by decide +kernel))) hgap
  have hprev := thV_2574
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23063:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4587634590530939 : ℚ) / 200000000000) ≤ ((2292812696777757 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (23063:ℚ) := by decide +kernel
  have hratR : ((((4587634590530939 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((2292812696777757 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23063:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2576 : ((((22948219284347621 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23071 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23063 < q → q < 23071 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23071).mp (by decide +kernel))) hgap
  have hprev := thV_2575
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23071:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((22948219284347621 : ℚ) / 1000000000000) ≤ ((4587634590530939 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (23071:ℚ) := by decide +kernel
  have hratR : ((((22948219284347621 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4587634590530939 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23071:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2577 : ((((22958266049391221 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23081 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23071 < q → q < 23081 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23081).mp (by decide +kernel))) hgap
  have hprev := thV_2576
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23081:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((22958266049391221 : ℚ) / 1000000000000) ≤ ((22948219284347621 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (23081:ℚ) := by decide +kernel
  have hratR : ((((22958266049391221 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((22948219284347621 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23081:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2578 : ((((11484156537177557 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23087 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23081 < q → q < 23087 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23087).mp (by decide +kernel))) hgap
  have hprev := thV_2577
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23087:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11484156537177557 : ℚ) / 500000000000) ≤ ((22958266049391221 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (23087:ℚ) := by decide +kernel
  have hratR : ((((11484156537177557 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((22958266049391221 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23087:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2579 : ((((5744590154739251 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23099 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23087 < q → q < 23099 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23099).mp (by decide +kernel))) hgap
  have hprev := thV_2578
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23099:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5744590154739251 : ℚ) / 250000000000) ≤ ((11484156537177557 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (23099:ℚ) := by decide +kernel
  have hratR : ((((5744590154739251 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((11484156537177557 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23099:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2580 : ((((11494204471254973 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23117 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23099 < q → q < 23117 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23117).mp (by decide +kernel))) hgap
  have hprev := thV_2579
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23117:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11494204471254973 : ℚ) / 500000000000) ≤ ((5744590154739251 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (23117:ℚ) := by decide +kernel
  have hratR : ((((11494204471254973 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((5744590154739251 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23117:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2581 : ((((22998457871494493 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23131 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23117 < q → q < 23131 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23131).mp (by decide +kernel))) hgap
  have hprev := thV_2580
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23131:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((22998457871494493 : ℚ) / 1000000000000) ≤ ((11494204471254973 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (23131:ℚ) := by decide +kernel
  have hratR : ((((22998457871494493 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((11494204471254973 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23131:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2582 : ((((23008507319128833 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23143 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23131 < q → q < 23143 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23143).mp (by decide +kernel))) hgap
  have hprev := thV_2581
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23143:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((23008507319128833 : ℚ) / 1000000000000) ≤ ((22998457871494493 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (23143:ℚ) := by decide +kernel
  have hratR : ((((23008507319128833 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((22998457871494493 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23143:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2583 : ((((4603711491575611 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23159 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23143 < q → q < 23159 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23159).mp (by decide +kernel))) hgap
  have hprev := thV_2582
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23159:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4603711491575611 : ℚ) / 200000000000) ≤ ((23008507319128833 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (23159:ℚ) := by decide +kernel
  have hratR : ((((4603711491575611 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((23008507319128833 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23159:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2584 : ((((11514303971002843 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23167 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23159 < q → q < 23167 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23167).mp (by decide +kernel))) hgap
  have hprev := thV_2583
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23167:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11514303971002843 : ℚ) / 500000000000) ≤ ((4603711491575611 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (23167:ℚ) := by decide +kernel
  have hratR : ((((11514303971002843 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((4603711491575611 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23167:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2585 : ((((719958083909027 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23173 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23167 < q → q < 23173 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23173).mp (by decide +kernel))) hgap
  have hprev := thV_2584
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23173:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((719958083909027 : ℚ) / 31250000000) ≤ ((11514303971002843 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (23173:ℚ) := by decide +kernel
  have hratR : ((((719958083909027 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((11514303971002843 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23173:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2586 : ((((23048710118392509 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23189 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23173 < q → q < 23189 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23189).mp (by decide +kernel))) hgap
  have hprev := thV_2585
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23189:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((23048710118392509 : ℚ) / 1000000000000) ≤ ((719958083909027 : ℚ) / 31250000000) + Work.RHContract.RegionI.logLowQ (23189:ℚ) := by decide +kernel
  have hratR : ((((23048710118392509 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((719958083909027 : ℚ) / 31250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23189:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2587 : ((((11529380948313909 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23197 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23189 < q → q < 23197 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23197).mp (by decide +kernel))) hgap
  have hprev := thV_2586
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23197:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11529380948313909 : ℚ) / 500000000000) ≤ ((23048710118392509 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (23197:ℚ) := by decide +kernel
  have hratR : ((((11529380948313909 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((23048710118392509 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23197:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2588 : ((((180225108181909 : ℚ) / 7812500000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23201 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23197 < q → q < 23201 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23201).mp (by decide +kernel))) hgap
  have hprev := thV_2587
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23201:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((180225108181909 : ℚ) / 7812500000) ≤ ((11529380948313909 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (23201:ℚ) := by decide +kernel
  have hratR : ((((180225108181909 : ℚ) / 7812500000) : ℚ) : ℝ) ≤ ((((11529380948313909 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23201:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2589 : ((((360607279439693 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23203 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23201 < q → q < 23203 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23203).mp (by decide +kernel))) hgap
  have hprev := thV_2588
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23203:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((360607279439693 : ℚ) / 15625000000) ≤ ((180225108181909 : ℚ) / 7812500000) + Work.RHContract.RegionI.logLowQ (23203:ℚ) := by decide +kernel
  have hratR : ((((360607279439693 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ ((((180225108181909 : ℚ) / 7812500000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23203:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2590 : ((((923556727182007 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23209 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23203 < q → q < 23209 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23209).mp (by decide +kernel))) hgap
  have hprev := thV_2589
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23209:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((923556727182007 : ℚ) / 40000000000) ≤ ((360607279439693 : ℚ) / 15625000000) + Work.RHContract.RegionI.logLowQ (23209:ℚ) := by decide +kernel
  have hratR : ((((923556727182007 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((360607279439693 : ℚ) / 15625000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23209:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2591 : ((((23098971250220611 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23227 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23209 < q → q < 23227 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23227).mp (by decide +kernel))) hgap
  have hprev := thV_2590
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23227:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((23098971250220611 : ℚ) / 1000000000000) ≤ ((923556727182007 : ℚ) / 40000000000) + Work.RHContract.RegionI.logLowQ (23227:ℚ) := by decide +kernel
  have hratR : ((((23098971250220611 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((923556727182007 : ℚ) / 40000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23227:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2592 : ((((4621805070727563 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23251 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23227 < q → q < 23251 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23251).mp (by decide +kernel))) hgap
  have hprev := thV_2591
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23251:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4621805070727563 : ℚ) / 200000000000) ≤ ((23098971250220611 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (23251:ℚ) := by decide +kernel
  have hratR : ((((4621805070727563 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((23098971250220611 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23251:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2593 : ((((11559540115457881 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23269 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23251 < q → q < 23269 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23269).mp (by decide +kernel))) hgap
  have hprev := thV_2592
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23269:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11559540115457881 : ℚ) / 500000000000) ≤ ((4621805070727563 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (23269:ℚ) := by decide +kernel
  have hratR : ((((11559540115457881 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((4621805070727563 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23269:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2594 : ((((23129135537857719 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23279 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23269 < q → q < 23279 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23279).mp (by decide +kernel))) hgap
  have hprev := thV_2593
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23279:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((23129135537857719 : ℚ) / 1000000000000) ≤ ((11559540115457881 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (23279:ℚ) := by decide +kernel
  have hratR : ((((23129135537857719 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((11559540115457881 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23279:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2595 : ((((23139191360152919 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23291 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23279 < q → q < 23291 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23291).mp (by decide +kernel))) hgap
  have hprev := thV_2594
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23291:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((23139191360152919 : ℚ) / 1000000000000) ≤ ((23129135537857719 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (23291:ℚ) := by decide +kernel
  have hratR : ((((23139191360152919 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((23129135537857719 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23291:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2596 : ((((23149247268314511 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23293 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23291 < q → q < 23293 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23293).mp (by decide +kernel))) hgap
  have hprev := thV_2595
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23293:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((23149247268314511 : ℚ) / 1000000000000) ≤ ((23139191360152919 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (23293:ℚ) := by decide +kernel
  have hratR : ((((23149247268314511 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((23139191360152919 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23293:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2597 : ((((23159303348186771 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23297 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23293 < q → q < 23297 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23297).mp (by decide +kernel))) hgap
  have hprev := thV_2596
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23297:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((23159303348186771 : ℚ) / 1000000000000) ≤ ((23149247268314511 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (23297:ℚ) := by decide +kernel
  have hratR : ((((23159303348186771 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((23149247268314511 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23297:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2598 : ((((5792340007203571 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23311 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23297 < q → q < 23311 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23311).mp (by decide +kernel))) hgap
  have hprev := thV_2597
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23311:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5792340007203571 : ℚ) / 250000000000) ≤ ((23159303348186771 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (23311:ℚ) := by decide +kernel
  have hratR : ((((5792340007203571 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((23159303348186771 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23311:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2599 : ((((5794854284582959 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23321 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23311 < q → q < 23321 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23321).mp (by decide +kernel))) hgap
  have hprev := thV_2598
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23321:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5794854284582959 : ℚ) / 250000000000) ≤ ((5792340007203571 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (23321:ℚ) := by decide +kernel
  have hratR : ((((5794854284582959 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((5792340007203571 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23321:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2600 : ((((4637894901019029 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23327 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23321 < q → q < 23327 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23327).mp (by decide +kernel))) hgap
  have hprev := thV_2599
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23327:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4637894901019029 : ℚ) / 200000000000) ≤ ((5794854284582959 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (23327:ℚ) := by decide +kernel
  have hratR : ((((4637894901019029 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((5794854284582959 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23327:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2601 : ((((5799883032259513 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23333 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23327 < q → q < 23333 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23333).mp (by decide +kernel))) hgap
  have hprev := thV_2600
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23333:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5799883032259513 : ℚ) / 250000000000) ≤ ((4637894901019029 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (23333:ℚ) := by decide +kernel
  have hratR : ((((5799883032259513 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((4637894901019029 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23333:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2602 : ((((23209590010094433 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23339 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23333 < q → q < 23339 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23339).mp (by decide +kernel))) hgap
  have hprev := thV_2601
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23339:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((23209590010094433 : ℚ) / 1000000000000) ≤ ((5799883032259513 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (23339:ℚ) := by decide +kernel
  have hratR : ((((23209590010094433 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5799883032259513 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23339:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2603 : ((((23219648662094831 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23357 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23339 < q → q < 23357 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23357).mp (by decide +kernel))) hgap
  have hprev := thV_2602
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23357:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((23219648662094831 : ℚ) / 1000000000000) ≤ ((23209590010094433 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (23357:ℚ) := by decide +kernel
  have hratR : ((((23219648662094831 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((23209590010094433 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23357:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2604 : ((((23229707827727907 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23369 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23357 < q → q < 23369 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23369).mp (by decide +kernel))) hgap
  have hprev := thV_2603
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23369:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((23229707827727907 : ℚ) / 1000000000000) ≤ ((23219648662094831 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (23369:ℚ) := by decide +kernel
  have hratR : ((((23229707827727907 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((23219648662094831 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23369:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2605 : ((((11619883539470393 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23371 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23369 < q → q < 23371 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23371).mp (by decide +kernel))) hgap
  have hprev := thV_2604
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23371:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11619883539470393 : ℚ) / 500000000000) ≤ ((23229707827727907 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (23371:ℚ) := by decide +kernel
  have hratR : ((((11619883539470393 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((23229707827727907 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23371:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2606 : ((((2906228440937817 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23399 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23371 < q → q < 23399 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23399).mp (by decide +kernel))) hgap
  have hprev := thV_2605
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23399:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2906228440937817 : ℚ) / 125000000000) ≤ ((11619883539470393 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (23399:ℚ) := by decide +kernel
  have hratR : ((((2906228440937817 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((11619883539470393 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23399:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2607 : ((((11629944372516099 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23417 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23399 < q → q < 23417 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23417).mp (by decide +kernel))) hgap
  have hprev := thV_2606
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23417:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11629944372516099 : ℚ) / 500000000000) ≤ ((2906228440937817 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (23417:ℚ) := by decide +kernel
  have hratR : ((((11629944372516099 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((2906228440937817 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23417:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2608 : ((((11634975280119737 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23431 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23417 < q → q < 23431 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23431).mp (by decide +kernel))) hgap
  have hprev := thV_2607
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23431:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11634975280119737 : ℚ) / 500000000000) ≤ ((11629944372516099 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (23431:ℚ) := by decide +kernel
  have hratR : ((((11634975280119737 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((11629944372516099 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23431:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2609 : ((((4656002611613951 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23447 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23431 < q → q < 23447 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23447).mp (by decide +kernel))) hgap
  have hprev := thV_2608
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23447:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4656002611613951 : ℚ) / 200000000000) ≤ ((11634975280119737 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (23447:ℚ) := by decide +kernel
  have hratR : ((((4656002611613951 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((11634975280119737 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23447:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2610 : ((((5822519016890417 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23459 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23447 < q → q < 23459 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23459).mp (by decide +kernel))) hgap
  have hprev := thV_2609
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23459:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5822519016890417 : ℚ) / 250000000000) ≤ ((4656002611613951 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (23459:ℚ) := by decide +kernel
  have hratR : ((((5822519016890417 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((4656002611613951 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23459:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2611 : ((((23300139673661457 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23473 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23459 < q → q < 23473 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23473).mp (by decide +kernel))) hgap
  have hprev := thV_2610
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23473:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((23300139673661457 : ℚ) / 1000000000000) ≤ ((5822519016890417 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (23473:ℚ) := by decide +kernel
  have hratR : ((((23300139673661457 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5822519016890417 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23473:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2612 : ((((11655102150845113 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23497 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23473 < q → q < 23497 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23497).mp (by decide +kernel))) hgap
  have hprev := thV_2611
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23497:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11655102150845113 : ℚ) / 500000000000) ≤ ((23300139673661457 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (23497:ℚ) := by decide +kernel
  have hratR : ((((11655102150845113 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((23300139673661457 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23497:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2613 : ((((5830067360073031 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23509 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23497 < q → q < 23509 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23509).mp (by decide +kernel))) hgap
  have hprev := thV_2612
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23509:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5830067360073031 : ℚ) / 250000000000) ≤ ((11655102150845113 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (23509:ℚ) := by decide +kernel
  have hratR : ((((5830067360073031 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((11655102150845113 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23509:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2614 : ((((291629193928353 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23531 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23509 < q → q < 23531 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23531).mp (by decide +kernel))) hgap
  have hprev := thV_2613
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23531:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((291629193928353 : ℚ) / 12500000000) ≤ ((5830067360073031 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (23531:ℚ) := by decide +kernel
  have hratR : ((((291629193928353 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ ((((5830067360073031 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23531:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2615 : ((((11670200921597321 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23537 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23531 < q → q < 23537 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23537).mp (by decide +kernel))) hgap
  have hprev := thV_2614
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23537:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11670200921597321 : ℚ) / 500000000000) ≤ ((291629193928353 : ℚ) / 12500000000) + Work.RHContract.RegionI.logLowQ (23537:ℚ) := by decide +kernel
  have hratR : ((((11670200921597321 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((291629193928353 : ℚ) / 12500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23537:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2616 : ((((23350468257090031 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23539 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23537 < q → q < 23539 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23539).mp (by decide +kernel))) hgap
  have hprev := thV_2615
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23539:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((23350468257090031 : ℚ) / 1000000000000) ≤ ((11670200921597321 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (23539:ℚ) := by decide +kernel
  have hratR : ((((23350468257090031 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((11670200921597321 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23539:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2617 : ((((23360535095722089 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23549 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23539 < q → q < 23549 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23549).mp (by decide +kernel))) hgap
  have hprev := thV_2616
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23549:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((23360535095722089 : ℚ) / 1000000000000) ≤ ((23350468257090031 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (23549:ℚ) := by decide +kernel
  have hratR : ((((23360535095722089 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((23350468257090031 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23549:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2618 : ((((11685301137006821 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23557 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23549 < q → q < 23557 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23557).mp (by decide +kernel))) hgap
  have hprev := thV_2617
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23557:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11685301137006821 : ℚ) / 500000000000) ≤ ((23360535095722089 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (23557:ℚ) := by decide +kernel
  have hratR : ((((11685301137006821 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((23360535095722089 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23557:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2619 : ((((23380669622091689 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23561 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23557 < q → q < 23561 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23561).mp (by decide +kernel))) hgap
  have hprev := thV_2618
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23561:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((23380669622091689 : ℚ) / 1000000000000) ≤ ((11685301137006821 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (23561:ℚ) := by decide +kernel
  have hratR : ((((23380669622091689 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((11685301137006821 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23561:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2620 : ((((11695368527526087 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23563 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23561 < q → q < 23563 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23563).mp (by decide +kernel))) hgap
  have hprev := thV_2619
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23563:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11695368527526087 : ℚ) / 500000000000) ≤ ((23380669622091689 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (23563:ℚ) := by decide +kernel
  have hratR : ((((11695368527526087 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((23380669622091689 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23563:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2621 : ((((11700402328877961 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23567 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23563 < q → q < 23567 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23567).mp (by decide +kernel))) hgap
  have hprev := thV_2620
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23567:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11700402328877961 : ℚ) / 500000000000) ≤ ((11695368527526087 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (23567:ℚ) := by decide +kernel
  have hratR : ((((11700402328877961 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((11695368527526087 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23567:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2622 : ((((4682174570866859 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23581 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23567 < q → q < 23581 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23581).mp (by decide +kernel))) hgap
  have hprev := thV_2621
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23581:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4682174570866859 : ℚ) / 200000000000) ≤ ((11700402328877961 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (23581:ℚ) := by decide +kernel
  have hratR : ((((4682174570866859 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((11700402328877961 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23581:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2623 : ((((11710470779833751 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23593 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23581 < q → q < 23593 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23593).mp (by decide +kernel))) hgap
  have hprev := thV_2622
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23593:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11710470779833751 : ℚ) / 500000000000) ≤ ((4682174570866859 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (23593:ℚ) := by decide +kernel
  have hratR : ((((11710470779833751 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((4682174570866859 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23593:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2624 : ((((23431010519281097 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23599 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23593 < q → q < 23599 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23599).mp (by decide +kernel))) hgap
  have hprev := thV_2623
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23599:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((23431010519281097 : ℚ) / 1000000000000) ≤ ((11710470779833751 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (23599:ℚ) := by decide +kernel
  have hratR : ((((23431010519281097 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((11710470779833751 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23599:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2625 : ((((5860269912094759 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23603 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23599 < q → q < 23603 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23603).mp (by decide +kernel))) hgap
  have hprev := thV_2624
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23603:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5860269912094759 : ℚ) / 250000000000) ≤ ((23431010519281097 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (23603:ℚ) := by decide +kernel
  have hratR : ((((5860269912094759 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((23431010519281097 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23603:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2626 : ((((5862787257912411 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23609 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23603 < q → q < 23609 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23609).mp (by decide +kernel))) hgap
  have hprev := thV_2625
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23609:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5862787257912411 : ℚ) / 250000000000) ≤ ((5860269912094759 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (23609:ℚ) := by decide +kernel
  have hratR : ((((5862787257912411 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((5860269912094759 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23609:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2627 : ((((11730609503869349 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23623 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23609 < q → q < 23623 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23623).mp (by decide +kernel))) hgap
  have hprev := thV_2626
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23623:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11730609503869349 : ℚ) / 500000000000) ≤ ((5862787257912411 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (23623:ℚ) := by decide +kernel
  have hratR : ((((11730609503869349 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((5862787257912411 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23623:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2628 : ((((11735644576569961 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23627 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23623 < q → q < 23627 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23627).mp (by decide +kernel))) hgap
  have hprev := thV_2627
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23627:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11735644576569961 : ℚ) / 500000000000) ≤ ((11730609503869349 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (23627:ℚ) := by decide +kernel
  have hratR : ((((11735644576569961 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((11730609503869349 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23627:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2629 : ((((11740679691593241 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23629 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23627 < q → q < 23629 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23629).mp (by decide +kernel))) hgap
  have hprev := thV_2628
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23629:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11740679691593241 : ℚ) / 500000000000) ≤ ((11735644576569961 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (23629:ℚ) := by decide +kernel
  have hratR : ((((11740679691593241 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((11735644576569961 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23629:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2630 : ((((23491429782502223 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23633 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23629 < q → q < 23633 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23633).mp (by decide +kernel))) hgap
  have hprev := thV_2629
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23633:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((23491429782502223 : ℚ) / 1000000000000) ≤ ((11740679691593241 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (23633:ℚ) := by decide +kernel
  have hratR : ((((23491429782502223 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((11740679691593241 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23633:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2631 : ((((11750750725212179 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23663 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23633 < q → q < 23663 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23663).mp (by decide +kernel))) hgap
  have hprev := thV_2630
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23663:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11750750725212179 : ℚ) / 500000000000) ≤ ((23491429782502223 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (23663:ℚ) := by decide +kernel
  have hratR : ((((11750750725212179 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((23491429782502223 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23663:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2632 : ((((23511573371874763 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23669 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23663 < q → q < 23669 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23669).mp (by decide +kernel))) hgap
  have hprev := thV_2631
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23669:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((23511573371874763 : ℚ) / 1000000000000) ≤ ((11750750725212179 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (23669:ℚ) := by decide +kernel
  have hratR : ((((23511573371874763 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((11750750725212179 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23669:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2633 : ((((2352164537782031 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23671 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23669 < q → q < 23671 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23671).mp (by decide +kernel))) hgap
  have hprev := thV_2632
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23671:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2352164537782031 : ℚ) / 100000000000) ≤ ((23511573371874763 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (23671:ℚ) := by decide +kernel
  have hratR : ((((2352164537782031 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((23511573371874763 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23671:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2634 : ((((23531717637208453 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23677 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23671 < q → q < 23677 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23677).mp (by decide +kernel))) hgap
  have hprev := thV_2633
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23677:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((23531717637208453 : ℚ) / 1000000000000) ≤ ((2352164537782031 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (23677:ℚ) := by decide +kernel
  have hratR : ((((23531717637208453 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2352164537782031 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23677:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2635 : ((((5885447579714559 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23687 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23677 < q → q < 23687 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23687).mp (by decide +kernel))) hgap
  have hprev := thV_2634
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23687:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5885447579714559 : ℚ) / 250000000000) ≤ ((23531717637208453 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (23687:ℚ) := by decide +kernel
  have hratR : ((((5885447579714559 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((23531717637208453 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23687:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2636 : ((((11775931542469477 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23689 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23687 < q → q < 23689 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23689).mp (by decide +kernel))) hgap
  have hprev := thV_2635
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23689:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11775931542469477 : ℚ) / 500000000000) ≤ ((5885447579714559 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (23689:ℚ) := by decide +kernel
  have hratR : ((((11775931542469477 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((5885447579714559 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23689:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2637 : ((((23561937116629021 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23719 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23689 < q → q < 23719 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23719).mp (by decide +kernel))) hgap
  have hprev := thV_2636
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23719:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((23561937116629021 : ℚ) / 1000000000000) ≤ ((11775931542469477 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (23719:ℚ) := by decide +kernel
  have hratR : ((((23561937116629021 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((11775931542469477 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23719:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2638 : ((((23572012075415657 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23741 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23719 < q → q < 23741 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23741).mp (by decide +kernel))) hgap
  have hprev := thV_2637
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23741:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((23572012075415657 : ℚ) / 1000000000000) ≤ ((23561937116629021 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (23741:ℚ) := by decide +kernel
  have hratR : ((((23572012075415657 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((23561937116629021 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23741:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2639 : ((((4716417423688239 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23743 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23741 < q → q < 23743 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23743).mp (by decide +kernel))) hgap
  have hprev := thV_2638
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23743:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4716417423688239 : ℚ) / 200000000000) ≤ ((23572012075415657 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (23743:ℚ) := by decide +kernel
  have hratR : ((((4716417423688239 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((23572012075415657 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23743:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2640 : ((((94368649319693 : ℚ) / 4000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23747 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23743 < q → q < 23747 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23747).mp (by decide +kernel))) hgap
  have hprev := thV_2639
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23747:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((94368649319693 : ℚ) / 4000000000) ≤ ((4716417423688239 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (23747:ℚ) := by decide +kernel
  have hratR : ((((94368649319693 : ℚ) / 4000000000) : ℚ) : ℝ) ≤ ((((4716417423688239 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23747:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2641 : ((((4720447558807377 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23753 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23747 < q → q < 23753 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23753).mp (by decide +kernel))) hgap
  have hprev := thV_2640
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23753:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4720447558807377 : ℚ) / 200000000000) ≤ ((94368649319693 : ℚ) / 4000000000) + Work.RHContract.RegionI.logLowQ (23753:ℚ) := by decide +kernel
  have hratR : ((((4720447558807377 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((94368649319693 : ℚ) / 4000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23753:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2642 : ((((11806156797446689 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23761 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23753 < q → q < 23761 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23761).mp (by decide +kernel))) hgap
  have hprev := thV_2641
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23761:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11806156797446689 : ℚ) / 500000000000) ≤ ((4720447558807377 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (23761:ℚ) := by decide +kernel
  have hratR : ((((11806156797446689 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((4720447558807377 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23761:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2643 : ((((1181119482411631 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23767 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23761 < q → q < 23767 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23767).mp (by decide +kernel))) hgap
  have hprev := thV_2642
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23767:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1181119482411631 : ℚ) / 50000000000) ≤ ((11806156797446689 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (23767:ℚ) := by decide +kernel
  have hratR : ((((1181119482411631 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((11806156797446689 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23767:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2644 : ((((23632465953990879 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23773 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23767 < q → q < 23773 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23773).mp (by decide +kernel))) hgap
  have hprev := thV_2643
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23773:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((23632465953990879 : ℚ) / 1000000000000) ≤ ((1181119482411631 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (23773:ℚ) := by decide +kernel
  have hratR : ((((23632465953990879 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1181119482411631 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23773:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2645 : ((((4728508586511037 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23789 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23773 < q → q < 23789 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23789).mp (by decide +kernel))) hgap
  have hprev := thV_2644
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23789:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4728508586511037 : ℚ) / 200000000000) ≤ ((23632465953990879 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (23789:ℚ) := by decide +kernel
  have hratR : ((((4728508586511037 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((23632465953990879 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23789:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2646 : ((((23652620415427129 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23801 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23789 < q → q < 23801 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23801).mp (by decide +kernel))) hgap
  have hprev := thV_2645
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23801:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((23652620415427129 : ℚ) / 1000000000000) ≤ ((4728508586511037 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (23801:ℚ) := by decide +kernel
  have hratR : ((((23652620415427129 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4728508586511037 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23801:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2647 : ((((23662698402352513 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23813 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23801 < q → q < 23813 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23813).mp (by decide +kernel))) hgap
  have hprev := thV_2646
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23813:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((23662698402352513 : ℚ) / 1000000000000) ≤ ((23652620415427129 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (23813:ℚ) := by decide +kernel
  have hratR : ((((23662698402352513 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((23652620415427129 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23813:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2648 : ((((23672776641209373 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23819 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23813 < q → q < 23819 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23819).mp (by decide +kernel))) hgap
  have hprev := thV_2647
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23819:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((23672776641209373 : ℚ) / 1000000000000) ≤ ((23662698402352513 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (23819:ℚ) := by decide +kernel
  have hratR : ((((23672776641209373 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((23662698402352513 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23819:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2649 : ((((2960356901984521 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23827 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23819 < q → q < 23827 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23827).mp (by decide +kernel))) hgap
  have hprev := thV_2648
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23827:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2960356901984521 : ℚ) / 125000000000) ≤ ((23672776641209373 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (23827:ℚ) := by decide +kernel
  have hratR : ((((2960356901984521 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((23672776641209373 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23827:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2650 : ((((5923233489601413 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23831 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23827 < q → q < 23831 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23831).mp (by decide +kernel))) hgap
  have hprev := thV_2649
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23831:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5923233489601413 : ℚ) / 250000000000) ≤ ((2960356901984521 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (23831:ℚ) := by decide +kernel
  have hratR : ((((5923233489601413 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((2960356901984521 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23831:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2651 : ((((11851506392427957 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23833 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23831 < q → q < 23833 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23833).mp (by decide +kernel))) hgap
  have hprev := thV_2650
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23833:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11851506392427957 : ℚ) / 500000000000) ≤ ((5923233489601413 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (23833:ℚ) := by decide +kernel
  have hratR : ((((11851506392427957 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((5923233489601413 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23833:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2652 : ((((1482068288612911 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23857 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23833 < q → q < 23857 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23857).mp (by decide +kernel))) hgap
  have hprev := thV_2651
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23857:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1482068288612911 : ℚ) / 62500000000) ≤ ((11851506392427957 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (23857:ℚ) := by decide +kernel
  have hratR : ((((1482068288612911 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((11851506392427957 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23857:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2653 : ((((23723172953627801 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23869 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23857 < q → q < 23869 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23869).mp (by decide +kernel))) hgap
  have hprev := thV_2652
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23869:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((23723172953627801 : ℚ) / 1000000000000) ≤ ((1482068288612911 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (23869:ℚ) := by decide +kernel
  have hratR : ((((23723172953627801 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1482068288612911 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23869:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2654 : ((((1483328341063523 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23873 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23869 < q → q < 23873 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23873).mp (by decide +kernel))) hgap
  have hprev := thV_2653
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23873:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1483328341063523 : ℚ) / 62500000000) ≤ ((23723172953627801 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (23873:ℚ) := by decide +kernel
  have hratR : ((((1483328341063523 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((23723172953627801 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23873:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2655 : ((((23743334211703311 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23879 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23873 < q → q < 23879 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23879).mp (by decide +kernel))) hgap
  have hprev := thV_2654
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23879:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((23743334211703311 : ℚ) / 1000000000000) ≤ ((1483328341063523 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (23879:ℚ) := by decide +kernel
  have hratR : ((((23743334211703311 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1483328341063523 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23879:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2656 : ((((23753415301356551 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23887 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23879 < q → q < 23887 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23887).mp (by decide +kernel))) hgap
  have hprev := thV_2655
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23887:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((23753415301356551 : ℚ) / 1000000000000) ≤ ((23743334211703311 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (23887:ℚ) := by decide +kernel
  have hratR : ((((23753415301356551 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((23743334211703311 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23887:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2657 : ((((11881748321080451 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23893 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23887 < q → q < 23893 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23893).mp (by decide +kernel))) hgap
  have hprev := thV_2656
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23893:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11881748321080451 : ℚ) / 500000000000) ≤ ((23753415301356551 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (23893:ℚ) := by decide +kernel
  have hratR : ((((11881748321080451 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((23753415301356551 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23893:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2658 : ((((11886789117026651 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23899 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23893 < q → q < 23899 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23899).mp (by decide +kernel))) hgap
  have hprev := thV_2657
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23899:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11886789117026651 : ℚ) / 500000000000) ≤ ((11881748321080451 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (23899:ℚ) := by decide +kernel
  have hratR : ((((11886789117026651 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((11881748321080451 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23899:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2659 : ((((4756732048857147 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23909 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23899 < q → q < 23909 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23909).mp (by decide +kernel))) hgap
  have hprev := thV_2658
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23909:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4756732048857147 : ℚ) / 200000000000) ≤ ((11886789117026651 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (23909:ℚ) := by decide +kernel
  have hratR : ((((4756732048857147 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((11886789117026651 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23909:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2660 : ((((11896871169082589 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23911 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23909 < q → q < 23911 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23911).mp (by decide +kernel))) hgap
  have hprev := thV_2659
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23911:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11896871169082589 : ℚ) / 500000000000) ≤ ((4756732048857147 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (23911:ℚ) := by decide +kernel
  have hratR : ((((11896871169082589 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((4756732048857147 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23911:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2661 : ((((23803824682943677 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23917 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23911 < q → q < 23917 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23917).mp (by decide +kernel))) hgap
  have hprev := thV_2660
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23917:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((23803824682943677 : ℚ) / 1000000000000) ≤ ((11896871169082589 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (23917:ℚ) := by decide +kernel
  have hratR : ((((23803824682943677 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((11896871169082589 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23917:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2662 : ((((23813907529331517 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23929 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23917 < q → q < 23929 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23929).mp (by decide +kernel))) hgap
  have hprev := thV_2661
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23929:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((23813907529331517 : ℚ) / 1000000000000) ≤ ((23803824682943677 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (23929:ℚ) := by decide +kernel
  have hratR : ((((23813907529331517 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((23803824682943677 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23929:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2663 : ((((11911995772581793 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23957 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23929 < q → q < 23957 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23957).mp (by decide +kernel))) hgap
  have hprev := thV_2662
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23957:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11911995772581793 : ℚ) / 500000000000) ≤ ((23813907529331517 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (23957:ℚ) := by decide +kernel
  have hratR : ((((11911995772581793 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((23813907529331517 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23957:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2664 : ((((595851903630133 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23971 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23957 < q → q < 23971 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23971).mp (by decide +kernel))) hgap
  have hprev := thV_2663
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23971:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((595851903630133 : ℚ) / 25000000000) ≤ ((11911995772581793 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (23971:ℚ) := by decide +kernel
  have hratR : ((((595851903630133 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((11911995772581793 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23971:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2665 : ((((11922080497759091 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23977 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23971 < q → q < 23977 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23977).mp (by decide +kernel))) hgap
  have hprev := thV_2664
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23977:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11922080497759091 : ℚ) / 500000000000) ≤ ((595851903630133 : ℚ) / 25000000000) + Work.RHContract.RegionI.logLowQ (23977:ℚ) := by decide +kernel
  have hratR : ((((11922080497759091 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((595851903630133 : ℚ) / 25000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23977:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2666 : ((((2981780751580459 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23981 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23977 < q → q < 23981 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23981).mp (by decide +kernel))) hgap
  have hprev := thV_2665
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23981:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2981780751580459 : ℚ) / 125000000000) ≤ ((11922080497759091 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (23981:ℚ) := by decide +kernel
  have hratR : ((((2981780751580459 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((11922080497759091 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23981:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2667 : ((((23864331530040153 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((23993 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23981 < q → q < 23993 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23993).mp (by decide +kernel))) hgap
  have hprev := thV_2666
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (23993:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((23864331530040153 : ℚ) / 1000000000000) ≤ ((2981780751580459 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (23993:ℚ) := by decide +kernel
  have hratR : ((((23864331530040153 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2981780751580459 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (23993:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2668 : ((((11937208690405821 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24001 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 23993 < q → q < 24001 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24001).mp (by decide +kernel))) hgap
  have hprev := thV_2667
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24001:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11937208690405821 : ℚ) / 500000000000) ≤ ((23864331530040153 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (24001:ℚ) := by decide +kernel
  have hratR : ((((11937208690405821 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((23864331530040153 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24001:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2669 : ((((23884503481541473 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24007 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24001 < q → q < 24007 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24007).mp (by decide +kernel))) hgap
  have hprev := thV_2668
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24007:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((23884503481541473 : ℚ) / 1000000000000) ≤ ((11937208690405821 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (24007:ℚ) := by decide +kernel
  have hratR : ((((23884503481541473 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((11937208690405821 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24007:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2670 : ((((23894590082000627 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24019 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24007 < q → q < 24019 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24019).mp (by decide +kernel))) hgap
  have hprev := thV_2669
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24019:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((23894590082000627 : ℚ) / 1000000000000) ≤ ((23884503481541473 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (24019:ℚ) := by decide +kernel
  have hratR : ((((23894590082000627 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((23884503481541473 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24019:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2671 : ((((11952338424490371 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24023 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24019 < q → q < 24023 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24023).mp (by decide +kernel))) hgap
  have hprev := thV_2670
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24023:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11952338424490371 : ℚ) / 500000000000) ≤ ((23894590082000627 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (24023:ℚ) := by decide +kernel
  have hratR : ((((11952338424490371 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((23894590082000627 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24023:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2672 : ((((23914763865690319 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24029 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24023 < q → q < 24029 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24029).mp (by decide +kernel))) hgap
  have hprev := thV_2671
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24029:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((23914763865690319 : ℚ) / 1000000000000) ≤ ((11952338424490371 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (24029:ℚ) := by decide +kernel
  have hratR : ((((23914763865690319 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((11952338424490371 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24029:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2673 : ((((5981212866214889 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24043 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24029 < q → q < 24043 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24043).mp (by decide +kernel))) hgap
  have hprev := thV_2672
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24043:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5981212866214889 : ℚ) / 250000000000) ≤ ((23914763865690319 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (24043:ℚ) := by decide +kernel
  have hratR : ((((5981212866214889 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((23914763865690319 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24043:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2674 : ((((1495933707096909 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24049 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24043 < q → q < 24049 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24049).mp (by decide +kernel))) hgap
  have hprev := thV_2673
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24049:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1495933707096909 : ℚ) / 62500000000) ≤ ((5981212866214889 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (24049:ℚ) := by decide +kernel
  have hratR : ((((1495933707096909 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((5981212866214889 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24049:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2675 : ((((23945027661098329 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24061 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24049 < q → q < 24061 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24061).mp (by decide +kernel))) hgap
  have hprev := thV_2674
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24061:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((23945027661098329 : ℚ) / 1000000000000) ≤ ((1495933707096909 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (24061:ℚ) := by decide +kernel
  have hratR : ((((23945027661098329 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1495933707096909 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24061:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2676 : ((((1497194776510631 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24071 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24061 < q → q < 24071 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24071).mp (by decide +kernel))) hgap
  have hprev := thV_2675
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24071:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1497194776510631 : ℚ) / 62500000000) ≤ ((23945027661098329 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (24071:ℚ) := by decide +kernel
  have hratR : ((((1497194776510631 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((23945027661098329 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24071:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2677 : ((((119826027182367 : ℚ) / 5000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24077 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24071 < q → q < 24077 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24077).mp (by decide +kernel))) hgap
  have hprev := thV_2676
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24077:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((119826027182367 : ℚ) / 5000000000) ≤ ((1497194776510631 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (24077:ℚ) := by decide +kernel
  have hratR : ((((119826027182367 : ℚ) / 5000000000) : ℚ) : ℝ) ≤ ((((1497194776510631 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24077:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2678 : ((((23975294697946141 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24083 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24077 < q → q < 24083 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24083).mp (by decide +kernel))) hgap
  have hprev := thV_2677
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24083:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((23975294697946141 : ℚ) / 1000000000000) ≤ ((119826027182367 : ℚ) / 5000000000) + Work.RHContract.RegionI.logLowQ (24083:ℚ) := by decide +kernel
  have hratR : ((((23975294697946141 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((119826027182367 : ℚ) / 5000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24083:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2679 : ((((23985384291548249 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24091 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24083 < q → q < 24091 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24091).mp (by decide +kernel))) hgap
  have hprev := thV_2678
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24091:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((23985384291548249 : ℚ) / 1000000000000) ≤ ((23975294697946141 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (24091:ℚ) := by decide +kernel
  have hratR : ((((23985384291548249 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((23975294697946141 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24091:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2680 : ((((5998868533543753 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24097 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24091 < q → q < 24097 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24097).mp (by decide +kernel))) hgap
  have hprev := thV_2679
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24097:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5998868533543753 : ℚ) / 250000000000) ≤ ((23985384291548249 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (24097:ℚ) := by decide +kernel
  have hratR : ((((5998868533543753 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((23985384291548249 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24097:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2681 : ((((1500347764110277 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24103 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24097 < q → q < 24103 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24103).mp (by decide +kernel))) hgap
  have hprev := thV_2680
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24103:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1500347764110277 : ℚ) / 62500000000) ≤ ((5998868533543753 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (24103:ℚ) := by decide +kernel
  have hratR : ((((1500347764110277 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((5998868533543753 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24103:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2682 : ((((375244601301477 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24107 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24103 < q → q < 24107 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24107).mp (by decide +kernel))) hgap
  have hprev := thV_2681
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24107:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((375244601301477 : ℚ) / 15625000000) ≤ ((1500347764110277 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (24107:ℚ) := by decide +kernel
  have hratR : ((((375244601301477 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ ((((1500347764110277 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24107:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2683 : ((((12012872411892319 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24109 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24107 < q → q < 24109 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24109).mp (by decide +kernel))) hgap
  have hprev := thV_2682
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24109:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12012872411892319 : ℚ) / 500000000000) ≤ ((375244601301477 : ℚ) / 15625000000) + Work.RHContract.RegionI.logLowQ (24109:ℚ) := by decide +kernel
  have hratR : ((((12012872411892319 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((375244601301477 : ℚ) / 15625000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24109:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2684 : ((((2403583533017413 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24113 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24109 < q → q < 24113 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24113).mp (by decide +kernel))) hgap
  have hprev := thV_2683
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24113:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2403583533017413 : ℚ) / 100000000000) ≤ ((12012872411892319 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (24113:ℚ) := by decide +kernel
  have hratR : ((((2403583533017413 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((12012872411892319 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24113:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2685 : ((((12022963084139921 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24121 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24113 < q → q < 24121 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24121).mp (by decide +kernel))) hgap
  have hprev := thV_2684
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24121:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12022963084139921 : ℚ) / 500000000000) ≤ ((2403583533017413 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (24121:ℚ) := by decide +kernel
  have hratR : ((((12022963084139921 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((2403583533017413 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24121:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2686 : ((((12028008751876829 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24133 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24121 < q → q < 24133 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24133).mp (by decide +kernel))) hgap
  have hprev := thV_2685
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24133:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12028008751876829 : ℚ) / 500000000000) ≤ ((12022963084139921 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (24133:ℚ) := by decide +kernel
  have hratR : ((((12028008751876829 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((12022963084139921 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24133:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2687 : ((((4813221800992377 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24137 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24133 < q → q < 24137 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24137).mp (by decide +kernel))) hgap
  have hprev := thV_2686
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24137:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4813221800992377 : ℚ) / 200000000000) ≤ ((12028008751876829 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (24137:ℚ) := by decide +kernel
  have hratR : ((((4813221800992377 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((12028008751876829 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24137:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2688 : ((((1504762567876521 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24151 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24137 < q → q < 24151 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24151).mp (by decide +kernel))) hgap
  have hprev := thV_2687
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24151:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1504762567876521 : ℚ) / 62500000000) ≤ ((4813221800992377 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (24151:ℚ) := by decide +kernel
  have hratR : ((((1504762567876521 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((4813221800992377 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24151:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2689 : ((((12043146956059967 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24169 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24151 < q → q < 24169 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24169).mp (by decide +kernel))) hgap
  have hprev := thV_2688
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24169:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12043146956059967 : ℚ) / 500000000000) ≤ ((1504762567876521 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (24169:ℚ) := by decide +kernel
  have hratR : ((((12043146956059967 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1504762567876521 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24169:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2690 : ((((4819277430376623 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24179 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24169 < q → q < 24179 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24179).mp (by decide +kernel))) hgap
  have hprev := thV_2689
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24179:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4819277430376623 : ℚ) / 200000000000) ≤ ((12043146956059967 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (24179:ℚ) := by decide +kernel
  have hratR : ((((4819277430376623 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((12043146956059967 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24179:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2691 : ((((12053240237179641 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24181 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24179 < q → q < 24181 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24181).mp (by decide +kernel))) hgap
  have hprev := thV_2690
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24181:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12053240237179641 : ℚ) / 500000000000) ≤ ((4819277430376623 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (24181:ℚ) := by decide +kernel
  have hratR : ((((12053240237179641 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((4819277430376623 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24181:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2692 : ((((602914361457329 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24197 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24181 < q → q < 24197 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24197).mp (by decide +kernel))) hgap
  have hprev := thV_2691
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24197:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((602914361457329 : ℚ) / 25000000000) ≤ ((12053240237179641 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (24197:ℚ) := by decide +kernel
  have hratR : ((((602914361457329 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((12053240237179641 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24197:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2693 : ((((6031667172540231 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24203 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24197 < q → q < 24203 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24203).mp (by decide +kernel))) hgap
  have hprev := thV_2692
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24203:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6031667172540231 : ℚ) / 250000000000) ≤ ((602914361457329 : ℚ) / 25000000000) + Work.RHContract.RegionI.logLowQ (24203:ℚ) := by decide +kernel
  have hratR : ((((6031667172540231 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((602914361457329 : ℚ) / 25000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24203:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2694 : ((((4827352749606259 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24223 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24203 < q → q < 24223 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24223).mp (by decide +kernel))) hgap
  have hprev := thV_2693
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24223:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4827352749606259 : ℚ) / 200000000000) ≤ ((6031667172540231 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (24223:ℚ) := by decide +kernel
  have hratR : ((((4827352749606259 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((6031667172540231 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24223:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2695 : ((((24146859053569463 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24229 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24223 < q → q < 24229 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24229).mp (by decide +kernel))) hgap
  have hprev := thV_2694
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24229:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((24146859053569463 : ℚ) / 1000000000000) ≤ ((4827352749606259 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (24229:ℚ) := by decide +kernel
  have hratR : ((((24146859053569463 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4827352749606259 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24229:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2696 : ((((2415695477175103 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24239 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24229 < q → q < 24239 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24239).mp (by decide +kernel))) hgap
  have hprev := thV_2695
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24239:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2415695477175103 : ℚ) / 100000000000) ≤ ((24146859053569463 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (24239:ℚ) := by decide +kernel
  have hratR : ((((2415695477175103 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((24146859053569463 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24239:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2697 : ((((24167050819924763 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24247 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24239 < q → q < 24247 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24247).mp (by decide +kernel))) hgap
  have hprev := thV_2696
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24247:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((24167050819924763 : ℚ) / 1000000000000) ≤ ((2415695477175103 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (24247:ℚ) := by decide +kernel
  have hratR : ((((24167050819924763 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2415695477175103 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24247:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2698 : ((((3022143379131719 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24251 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24247 < q → q < 24251 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24251).mp (by decide +kernel))) hgap
  have hprev := thV_2697
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24251:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3022143379131719 : ℚ) / 125000000000) ≤ ((24167050819924763 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (24251:ℚ) := by decide +kernel
  have hratR : ((((3022143379131719 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((24167050819924763 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24251:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_2699 : ((((24187244482480599 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((24281 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 24251 < q → q < 24281 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24281).mp (by decide +kernel))) hgap
  have hprev := thV_2698
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (24281:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((24187244482480599 : ℚ) / 1000000000000) ≤ ((3022143379131719 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (24281:ℚ) := by decide +kernel
  have hratR : ((((24187244482480599 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3022143379131719 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (24281:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)

end

end Work.RHContract.RegionI
