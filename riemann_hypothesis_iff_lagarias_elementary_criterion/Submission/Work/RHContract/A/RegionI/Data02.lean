import Mathlib
import Submission.Work.RHContract.A.RegionI.Data01

open scoped BigOperators

namespace Work.RHContract.RegionI

noncomputable section

lemma thV_900 : ((((6929274835737279 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7001 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 6997 < q → q < 7001 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7001).mp (by decide +kernel))) hgap
  have hprev := thV_899
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7001:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6929274835737279 : ℚ) / 1000000000000) ≤ ((3460210513732711 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (7001:ℚ) := by decide +kernel
  have hratR : ((((6929274835737279 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3460210513732711 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7001:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_901 : ((((867266294572837 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7013 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7001 < q → q < 7013 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7013).mp (by decide +kernel))) hgap
  have hprev := thV_900
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7013:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((867266294572837 : ℚ) / 125000000000) ≤ ((6929274835737279 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (7013:ℚ) := by decide +kernel
  have hratR : ((((867266294572837 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((6929274835737279 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7013:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_902 : ((((6946986732616307 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7019 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7013 < q → q < 7019 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7019).mp (by decide +kernel))) hgap
  have hprev := thV_901
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7019:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6946986732616307 : ℚ) / 1000000000000) ≤ ((867266294572837 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (7019:ℚ) := by decide +kernel
  have hratR : ((((6946986732616307 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((867266294572837 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7019:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_903 : ((((6955844247764379 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7027 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7019 < q → q < 7027 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7027).mp (by decide +kernel))) hgap
  have hprev := thV_902
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7027:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6955844247764379 : ℚ) / 1000000000000) ≤ ((6946986732616307 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (7027:ℚ) := by decide +kernel
  have hratR : ((((6955844247764379 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((6946986732616307 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7027:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_904 : ((((6964703469154867 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7039 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7027 < q → q < 7039 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7039).mp (by decide +kernel))) hgap
  have hprev := thV_903
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7039:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6964703469154867 : ℚ) / 1000000000000) ≤ ((6955844247764379 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (7039:ℚ) := by decide +kernel
  have hratR : ((((6964703469154867 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((6955844247764379 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7039:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_905 : ((((6973563258646493 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7043 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7039 < q → q < 7043 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7043).mp (by decide +kernel))) hgap
  have hprev := thV_904
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7043:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6973563258646493 : ℚ) / 1000000000000) ≤ ((6964703469154867 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (7043:ℚ) := by decide +kernel
  have hratR : ((((6973563258646493 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((6964703469154867 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7043:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_906 : ((((3491212516977187 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7057 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7043 < q → q < 7057 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7057).mp (by decide +kernel))) hgap
  have hprev := thV_905
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7057:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3491212516977187 : ℚ) / 500000000000) ≤ ((6973563258646493 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (7057:ℚ) := by decide +kernel
  have hratR : ((((3491212516977187 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((6973563258646493 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7057:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_907 : ((((279651540330297 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7069 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7057 < q → q < 7069 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7069).mp (by decide +kernel))) hgap
  have hprev := thV_906
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7069:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((279651540330297 : ℚ) / 40000000000) ≤ ((3491212516977187 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (7069:ℚ) := by decide +kernel
  have hratR : ((((279651540330297 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((3491212516977187 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7069:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_908 : ((((7000153396188079 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7079 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7069 < q → q < 7079 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7079).mp (by decide +kernel))) hgap
  have hprev := thV_907
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7079:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7000153396188079 : ℚ) / 1000000000000) ≤ ((279651540330297 : ℚ) / 40000000000) + Work.RHContract.RegionI.logLowQ (7079:ℚ) := by decide +kernel
  have hratR : ((((7000153396188079 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((279651540330297 : ℚ) / 40000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7079:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_909 : ((((7009021668693957 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7103 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7079 < q → q < 7103 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7103).mp (by decide +kernel))) hgap
  have hprev := thV_908
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7103:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7009021668693957 : ℚ) / 1000000000000) ≤ ((7000153396188079 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (7103:ℚ) := by decide +kernel
  have hratR : ((((7009021668693957 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((7000153396188079 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7103:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_910 : ((((7017890785556767 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7109 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7103 < q → q < 7109 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7109).mp (by decide +kernel))) hgap
  have hprev := thV_909
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7109:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7017890785556767 : ℚ) / 1000000000000) ≤ ((7009021668693957 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (7109:ℚ) := by decide +kernel
  have hratR : ((((7017890785556767 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((7009021668693957 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7109:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_911 : ((((7026761588997629 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7121 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7109 < q → q < 7121 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7121).mp (by decide +kernel))) hgap
  have hprev := thV_910
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7121:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7026761588997629 : ℚ) / 1000000000000) ≤ ((7017890785556767 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (7121:ℚ) := by decide +kernel
  have hratR : ((((7026761588997629 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((7017890785556767 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7121:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_912 : ((((7035633234662011 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7127 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7121 < q → q < 7127 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7127).mp (by decide +kernel))) hgap
  have hprev := thV_911
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7127:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7035633234662011 : ℚ) / 1000000000000) ≤ ((7026761588997629 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (7127:ℚ) := by decide +kernel
  have hratR : ((((7035633234662011 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((7026761588997629 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7127:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_913 : ((((7044505160910009 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7129 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7127 < q → q < 7129 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7129).mp (by decide +kernel))) hgap
  have hprev := thV_912
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7129:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7044505160910009 : ℚ) / 1000000000000) ≤ ((7035633234662011 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (7129:ℚ) := by decide +kernel
  have hratR : ((((7044505160910009 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((7035633234662011 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7129:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_914 : ((((3526690084196469 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7151 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7129 < q → q < 7151 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7151).mp (by decide +kernel))) hgap
  have hprev := thV_913
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7151:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3526690084196469 : ℚ) / 500000000000) ≤ ((7044505160910009 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (7151:ℚ) := by decide +kernel
  have hratR : ((((3526690084196469 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((7044505160910009 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7151:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_915 : ((((3531128146987607 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7159 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7151 < q → q < 7159 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7159).mp (by decide +kernel))) hgap
  have hprev := thV_914
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7159:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3531128146987607 : ℚ) / 500000000000) ≤ ((3526690084196469 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (7159:ℚ) := by decide +kernel
  have hratR : ((((3531128146987607 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((3526690084196469 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7159:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_916 : ((((1767783732679881 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7177 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7159 < q → q < 7177 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7177).mp (by decide +kernel))) hgap
  have hprev := thV_915
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7177:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1767783732679881 : ℚ) / 250000000000) ≤ ((3531128146987607 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (7177:ℚ) := by decide +kernel
  have hratR : ((((1767783732679881 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((3531128146987607 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7177:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_917 : ((((7080014959833873 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7187 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7177 < q → q < 7187 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7187).mp (by decide +kernel))) hgap
  have hprev := thV_916
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7187:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7080014959833873 : ℚ) / 1000000000000) ≤ ((1767783732679881 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (7187:ℚ) := by decide +kernel
  have hratR : ((((7080014959833873 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1767783732679881 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7187:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_918 : ((((7088895823440621 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7193 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7187 < q → q < 7193 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7193).mp (by decide +kernel))) hgap
  have hprev := thV_917
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7193:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7088895823440621 : ℚ) / 1000000000000) ≤ ((7080014959833873 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (7193:ℚ) := by decide +kernel
  have hratR : ((((7088895823440621 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((7080014959833873 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7193:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_919 : ((((3548889315746213 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7207 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7193 < q → q < 7207 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7207).mp (by decide +kernel))) hgap
  have hprev := thV_918
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7207:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3548889315746213 : ℚ) / 500000000000) ≤ ((7088895823440621 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (7207:ℚ) := by decide +kernel
  have hratR : ((((3548889315746213 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((7088895823440621 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7207:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_920 : ((((7106661994406223 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7211 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7207 < q → q < 7211 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7211).mp (by decide +kernel))) hgap
  have hprev := thV_919
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7211:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7106661994406223 : ℚ) / 1000000000000) ≤ ((3548889315746213 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (7211:ℚ) := by decide +kernel
  have hratR : ((((7106661994406223 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3548889315746213 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7211:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_921 : ((((7115545634635607 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7213 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7211 < q → q < 7213 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7213).mp (by decide +kernel))) hgap
  have hprev := thV_920
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7213:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7115545634635607 : ℚ) / 1000000000000) ≤ ((7106661994406223 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (7213:ℚ) := by decide +kernel
  have hratR : ((((7115545634635607 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((7106661994406223 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7213:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_922 : ((((3562215053175313 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7219 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7213 < q → q < 7219 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7219).mp (by decide +kernel))) hgap
  have hprev := thV_921
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7219:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3562215053175313 : ℚ) / 500000000000) ≤ ((7115545634635607 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (7219:ℚ) := by decide +kernel
  have hratR : ((((3562215053175313 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((7115545634635607 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7219:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_923 : ((((3566657981170253 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7229 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7219 < q → q < 7229 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7229).mp (by decide +kernel))) hgap
  have hprev := thV_922
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7229:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3566657981170253 : ℚ) / 500000000000) ≤ ((3562215053175313 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (7229:ℚ) := by decide +kernel
  have hratR : ((((3566657981170253 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((3562215053175313 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7229:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_924 : ((((1785550731093063 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7237 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7229 < q → q < 7237 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7237).mp (by decide +kernel))) hgap
  have hprev := thV_923
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7237:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1785550731093063 : ℚ) / 250000000000) ≤ ((3566657981170253 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (7237:ℚ) := by decide +kernel
  have hratR : ((((1785550731093063 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((3566657981170253 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7237:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_925 : ((((7151090715133327 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7243 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7237 < q → q < 7243 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7243).mp (by decide +kernel))) hgap
  have hprev := thV_924
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7243:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7151090715133327 : ℚ) / 1000000000000) ≤ ((1785550731093063 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (7243:ℚ) := by decide +kernel
  have hratR : ((((7151090715133327 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1785550731093063 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7243:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_926 : ((((1789994764499829 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7247 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7243 < q → q < 7247 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7247).mp (by decide +kernel))) hgap
  have hprev := thV_925
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7247:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1789994764499829 : ℚ) / 250000000000) ≤ ((7151090715133327 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (7247:ℚ) := by decide +kernel
  have hratR : ((((1789994764499829 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((7151090715133327 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7247:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_927 : ((((179221705711289 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7253 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7247 < q → q < 7253 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7253).mp (by decide +kernel))) hgap
  have hprev := thV_926
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7253:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((179221705711289 : ℚ) / 25000000000) ≤ ((1789994764499829 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (7253:ℚ) := by decide +kernel
  have hratR : ((((179221705711289 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((1789994764499829 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7253:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_928 : ((((3588880763296329 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7283 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7253 < q → q < 7283 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7283).mp (by decide +kernel))) hgap
  have hprev := thV_927
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7283:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3588880763296329 : ℚ) / 500000000000) ≤ ((179221705711289 : ℚ) / 25000000000) + Work.RHContract.RegionI.logLowQ (7283:ℚ) := by decide +kernel
  have hratR : ((((3588880763296329 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((179221705711289 : ℚ) / 25000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7283:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_929 : ((((898332093146663 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7297 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7283 < q → q < 7297 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7297).mp (by decide +kernel))) hgap
  have hprev := thV_928
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7297:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((898332093146663 : ℚ) / 125000000000) ≤ ((3588880763296329 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (7297:ℚ) := by decide +kernel
  have hratR : ((((898332093146663 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((3588880763296329 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7297:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_930 : ((((287822133329679 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7307 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7297 < q → q < 7307 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7307).mp (by decide +kernel))) hgap
  have hprev := thV_929
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7307:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((287822133329679 : ℚ) / 40000000000) ≤ ((898332093146663 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (7307:ℚ) := by decide +kernel
  have hratR : ((((287822133329679 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((898332093146663 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7307:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_931 : ((((900556274372917 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7309 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7307 < q → q < 7309 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7309).mp (by decide +kernel))) hgap
  have hprev := thV_930
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7309:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((900556274372917 : ℚ) / 125000000000) ≤ ((287822133329679 : ℚ) / 40000000000) + Work.RHContract.RegionI.logLowQ (7309:ℚ) := by decide +kernel
  have hratR : ((((900556274372917 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((287822133329679 : ℚ) / 40000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7309:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_932 : ((((7213348697189863 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7321 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7309 < q → q < 7321 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7321).mp (by decide +kernel))) hgap
  have hprev := thV_931
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7321:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7213348697189863 : ℚ) / 1000000000000) ≤ ((900556274372917 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (7321:ℚ) := by decide +kernel
  have hratR : ((((7213348697189863 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((900556274372917 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7321:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_933 : ((((7222248564397967 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7331 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7321 < q → q < 7331 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7331).mp (by decide +kernel))) hgap
  have hprev := thV_932
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7331:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7222248564397967 : ℚ) / 1000000000000) ≤ ((7213348697189863 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (7331:ℚ) := by decide +kernel
  have hratR : ((((7222248564397967 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((7213348697189863 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7331:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_934 : ((((7231148704382941 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7333 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7331 < q → q < 7333 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7333).mp (by decide +kernel))) hgap
  have hprev := thV_933
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7333:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7231148704382941 : ℚ) / 1000000000000) ≤ ((7222248564397967 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (7333:ℚ) := by decide +kernel
  have hratR : ((((7231148704382941 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((7222248564397967 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7333:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_935 : ((((144801020478167 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7349 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7333 < q → q < 7349 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7349).mp (by decide +kernel))) hgap
  have hprev := thV_934
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7349:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((144801020478167 : ℚ) / 20000000000) ≤ ((7231148704382941 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (7349:ℚ) := by decide +kernel
  have hratR : ((((144801020478167 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ ((((7231148704382941 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7349:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_936 : ((((1812238403885651 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7351 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7349 < q → q < 7351 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7351).mp (by decide +kernel))) hgap
  have hprev := thV_935
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7351:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1812238403885651 : ℚ) / 250000000000) ≤ ((144801020478167 : ℚ) / 20000000000) + Work.RHContract.RegionI.logLowQ (7351:ℚ) := by decide +kernel
  have hratR : ((((1812238403885651 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((144801020478167 : ℚ) / 20000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7351:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_937 : ((((7257858652830251 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7369 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7351 < q → q < 7369 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7369).mp (by decide +kernel))) hgap
  have hprev := thV_936
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7369:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7257858652830251 : ℚ) / 1000000000000) ≤ ((1812238403885651 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (7369:ℚ) := by decide +kernel
  have hratR : ((((7257858652830251 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1812238403885651 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7369:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_938 : ((((454172933857043 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7393 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7369 < q → q < 7393 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7393).mp (by decide +kernel))) hgap
  have hprev := thV_937
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7393:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((454172933857043 : ℚ) / 62500000000) ≤ ((7257858652830251 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (7393:ℚ) := by decide +kernel
  have hratR : ((((454172933857043 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((7257858652830251 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7393:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_939 : ((((22736492694911 : ℚ) / 3125000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7411 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7393 < q → q < 7411 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7411).mp (by decide +kernel))) hgap
  have hprev := thV_938
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7411:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((22736492694911 : ℚ) / 3125000000) ≤ ((454172933857043 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (7411:ℚ) := by decide +kernel
  have hratR : ((((22736492694911 : ℚ) / 3125000000) : ℚ) : ℝ) ≤ ((((454172933857043 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7411:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_940 : ((((7284589192310137 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7417 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7411 < q → q < 7417 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7417).mp (by decide +kernel))) hgap
  have hprev := thV_939
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7417:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7284589192310137 : ℚ) / 1000000000000) ≤ ((22736492694911 : ℚ) / 3125000000) + Work.RHContract.RegionI.logLowQ (7417:ℚ) := by decide +kernel
  have hratR : ((((7284589192310137 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((22736492694911 : ℚ) / 3125000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7417:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_941 : ((((3646751438565871 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7433 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7417 < q → q < 7433 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7433).mp (by decide +kernel))) hgap
  have hprev := thV_940
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7433:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3646751438565871 : ℚ) / 500000000000) ≤ ((7284589192310137 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (7433:ℚ) := by decide +kernel
  have hratR : ((((3646751438565871 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((7284589192310137 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7433:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_942 : ((((912802372582397 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7451 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7433 < q → q < 7451 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7451).mp (by decide +kernel))) hgap
  have hprev := thV_941
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7451:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((912802372582397 : ℚ) / 125000000000) ≤ ((3646751438565871 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (7451:ℚ) := by decide +kernel
  have hratR : ((((912802372582397 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((3646751438565871 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7451:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_943 : ((((18278339722809 : ℚ) / 2500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7457 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7451 < q → q < 7457 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7457).mp (by decide +kernel))) hgap
  have hprev := thV_942
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7457:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((18278339722809 : ℚ) / 2500000000) ≤ ((912802372582397 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (7457:ℚ) := by decide +kernel
  have hratR : ((((18278339722809 : ℚ) / 2500000000) : ℚ) : ℝ) ≤ ((((912802372582397 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7457:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_944 : ((((1464050613151287 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7459 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7457 < q → q < 7459 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7459).mp (by decide +kernel))) hgap
  have hprev := thV_943
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7459:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1464050613151287 : ℚ) / 200000000000) ≤ ((18278339722809 : ℚ) / 2500000000) + Work.RHContract.RegionI.logLowQ (7459:ℚ) := by decide +kernel
  have hratR : ((((1464050613151287 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((18278339722809 : ℚ) / 2500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7459:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_945 : ((((1465834530534863 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7477 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7459 < q → q < 7477 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7477).mp (by decide +kernel))) hgap
  have hprev := thV_944
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7477:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1465834530534863 : ℚ) / 200000000000) ≤ ((1464050613151287 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (7477:ℚ) := by decide +kernel
  have hratR : ((((1465834530534863 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((1464050613151287 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7477:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_946 : ((((1834523193605767 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7481 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7477 < q → q < 7481 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7481).mp (by decide +kernel))) hgap
  have hprev := thV_945
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7481:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1834523193605767 : ℚ) / 250000000000) ≤ ((1465834530534863 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (7481:ℚ) := by decide +kernel
  have hratR : ((((1834523193605767 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((1465834530534863 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7481:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_947 : ((((7347013697882179 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7487 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7481 < q → q < 7487 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7487).mp (by decide +kernel))) hgap
  have hprev := thV_946
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7487:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7347013697882179 : ℚ) / 1000000000000) ≤ ((1834523193605767 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (7487:ℚ) := by decide +kernel
  have hratR : ((((7347013697882179 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1834523193605767 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7487:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_948 : ((((7355934888435309 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7489 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7487 < q → q < 7489 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7489).mp (by decide +kernel))) hgap
  have hprev := thV_947
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7489:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7355934888435309 : ℚ) / 1000000000000) ≤ ((7347013697882179 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (7489:ℚ) := by decide +kernel
  have hratR : ((((7355934888435309 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((7347013697882179 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7489:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_949 : ((((7364857413389491 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7499 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7489 < q → q < 7499 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7499).mp (by decide +kernel))) hgap
  have hprev := thV_948
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7499:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7364857413389491 : ℚ) / 1000000000000) ≤ ((7355934888435309 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (7499:ℚ) := by decide +kernel
  have hratR : ((((7364857413389491 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((7355934888435309 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7499:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_950 : ((((921722625572993 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7507 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7499 < q → q < 7507 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7507).mp (by decide +kernel))) hgap
  have hprev := thV_949
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7507:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((921722625572993 : ℚ) / 125000000000) ≤ ((7364857413389491 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (7507:ℚ) := by decide +kernel
  have hratR : ((((921722625572993 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((7364857413389491 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7507:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_951 : ((((3691352963491001 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7517 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7507 < q → q < 7517 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7517).mp (by decide +kernel))) hgap
  have hprev := thV_950
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7517:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3691352963491001 : ℚ) / 500000000000) ≤ ((921722625572993 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (7517:ℚ) := by decide +kernel
  have hratR : ((((3691352963491001 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((921722625572993 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7517:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_952 : ((((3695815823626221 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7523 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7517 < q → q < 7523 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7523).mp (by decide +kernel))) hgap
  have hprev := thV_951
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7523:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3695815823626221 : ℚ) / 500000000000) ≤ ((3691352963491001 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (7523:ℚ) := by decide +kernel
  have hratR : ((((3695815823626221 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((3691352963491001 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7523:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_953 : ((((1850139541189793 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7529 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7523 < q → q < 7529 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7529).mp (by decide +kernel))) hgap
  have hprev := thV_952
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7529:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1850139541189793 : ℚ) / 250000000000) ≤ ((3695815823626221 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (7529:ℚ) := by decide +kernel
  have hratR : ((((1850139541189793 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((3695815823626221 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7529:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_954 : ((((926185718032487 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7537 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7529 < q → q < 7537 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7537).mp (by decide +kernel))) hgap
  have hprev := thV_953
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7537:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((926185718032487 : ℚ) / 125000000000) ≤ ((1850139541189793 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (7537:ℚ) := by decide +kernel
  have hratR : ((((926185718032487 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((1850139541189793 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7537:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_955 : ((((7418413854334979 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7541 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7537 < q → q < 7541 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7541).mp (by decide +kernel))) hgap
  have hprev := thV_954
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7541:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7418413854334979 : ℚ) / 1000000000000) ≤ ((926185718032487 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (7541:ℚ) := by decide +kernel
  have hratR : ((((7418413854334979 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((926185718032487 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7541:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_956 : ((((464208922484009 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7547 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7541 < q → q < 7547 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7547).mp (by decide +kernel))) hgap
  have hprev := thV_955
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7547:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((464208922484009 : ℚ) / 62500000000) ≤ ((7418413854334979 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (7547:ℚ) := by decide +kernel
  have hratR : ((((464208922484009 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((7418413854334979 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7547:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_957 : ((((1859067982531041 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7549 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7547 < q → q < 7549 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7549).mp (by decide +kernel))) hgap
  have hprev := thV_956
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7549:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1859067982531041 : ℚ) / 250000000000) ≤ ((464208922484009 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (7549:ℚ) := by decide +kernel
  have hratR : ((((1859067982531041 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((464208922484009 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7549:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_958 : ((((232662575759573 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7559 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7549 < q → q < 7559 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7559).mp (by decide +kernel))) hgap
  have hprev := thV_957
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7559:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((232662575759573 : ℚ) / 31250000000) ≤ ((1859067982531041 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (7559:ℚ) := by decide +kernel
  have hratR : ((((232662575759573 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((1859067982531041 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7559:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_959 : ((((3727066591519387 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7561 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7559 < q → q < 7561 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7561).mp (by decide +kernel))) hgap
  have hprev := thV_958
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7561:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3727066591519387 : ℚ) / 500000000000) ≤ ((232662575759573 : ℚ) / 31250000000) + Work.RHContract.RegionI.logLowQ (7561:ℚ) := by decide +kernel
  have hratR : ((((3727066591519387 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((232662575759573 : ℚ) / 31250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7561:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_960 : ((((233220797737649 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7573 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7561 < q → q < 7573 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7573).mp (by decide +kernel))) hgap
  have hprev := thV_959
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7573:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((233220797737649 : ℚ) / 31250000000) ≤ ((3727066591519387 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (7573:ℚ) := by decide +kernel
  have hratR : ((((233220797737649 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((3727066591519387 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7573:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_961 : ((((373599920011179 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7577 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7573 < q → q < 7577 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7577).mp (by decide +kernel))) hgap
  have hprev := thV_960
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7577:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((373599920011179 : ℚ) / 50000000000) ≤ ((233220797737649 : ℚ) / 31250000000) + Work.RHContract.RegionI.logLowQ (7577:ℚ) := by decide +kernel
  have hratR : ((((373599920011179 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((233220797737649 : ℚ) / 31250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7577:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_962 : ((((7480932064399161 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7583 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7577 < q → q < 7583 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7583).mp (by decide +kernel))) hgap
  have hprev := thV_961
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7583:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7480932064399161 : ℚ) / 1000000000000) ≤ ((373599920011179 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (7583:ℚ) := by decide +kernel
  have hratR : ((((7480932064399161 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((373599920011179 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7583:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_963 : ((((1497973303901089 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7589 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7583 < q → q < 7589 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7589).mp (by decide +kernel))) hgap
  have hprev := thV_962
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7589:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1497973303901089 : ℚ) / 200000000000) ≤ ((7480932064399161 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (7589:ℚ) := by decide +kernel
  have hratR : ((((1497973303901089 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((7480932064399161 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7589:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_964 : ((((3749400619058171 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7591 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7589 < q → q < 7591 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7591).mp (by decide +kernel))) hgap
  have hprev := thV_963
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7591:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3749400619058171 : ℚ) / 500000000000) ≤ ((1497973303901089 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (7591:ℚ) := by decide +kernel
  have hratR : ((((3749400619058171 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1497973303901089 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7591:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_965 : ((((7507737536298451 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7603 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7591 < q → q < 7603 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7603).mp (by decide +kernel))) hgap
  have hprev := thV_964
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7603:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7507737536298451 : ℚ) / 1000000000000) ≤ ((3749400619058171 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (7603:ℚ) := by decide +kernel
  have hratR : ((((7507737536298451 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3749400619058171 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7603:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_966 : ((((939584295056291 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7607 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7603 < q → q < 7607 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7607).mp (by decide +kernel))) hgap
  have hprev := thV_965
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7607:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((939584295056291 : ℚ) / 125000000000) ≤ ((7507737536298451 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (7607:ℚ) := by decide +kernel
  have hratR : ((((939584295056291 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((7507737536298451 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7607:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_967 : ((((3762806511660437 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7621 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7607 < q → q < 7621 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7621).mp (by decide +kernel))) hgap
  have hprev := thV_966
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7621:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3762806511660437 : ℚ) / 500000000000) ≤ ((939584295056291 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (7621:ℚ) := by decide +kernel
  have hratR : ((((3762806511660437 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((939584295056291 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7621:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_968 : ((((470909627831331 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7639 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7621 < q → q < 7639 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7639).mp (by decide +kernel))) hgap
  have hprev := thV_967
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7639:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((470909627831331 : ℚ) / 62500000000) ≤ ((3762806511660437 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (7639:ℚ) := by decide +kernel
  have hratR : ((((470909627831331 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((3762806511660437 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7639:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_969 : ((((7543495590773419 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7643 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7639 < q → q < 7643 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7643).mp (by decide +kernel))) hgap
  have hprev := thV_968
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7643:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7543495590773419 : ℚ) / 1000000000000) ≤ ((470909627831331 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (7643:ℚ) := by decide +kernel
  have hratR : ((((7543495590773419 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((470909627831331 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7643:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_970 : ((((7552437920969621 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7649 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7643 < q → q < 7649 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7649).mp (by decide +kernel))) hgap
  have hprev := thV_969
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7649:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7552437920969621 : ℚ) / 1000000000000) ≤ ((7543495590773419 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (7649:ℚ) := by decide +kernel
  have hratR : ((((7552437920969621 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((7543495590773419 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7649:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_971 : ((((3780691431237133 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7669 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7649 < q → q < 7669 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7669).mp (by decide +kernel))) hgap
  have hprev := thV_970
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7669:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3780691431237133 : ℚ) / 500000000000) ≤ ((7552437920969621 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (7669:ℚ) := by decide +kernel
  have hratR : ((((3780691431237133 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((7552437920969621 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7669:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_972 : ((((1892582081355831 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7673 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7669 < q → q < 7673 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7673).mp (by decide +kernel))) hgap
  have hprev := thV_971
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7673:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1892582081355831 : ℚ) / 250000000000) ≤ ((3780691431237133 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (7673:ℚ) := by decide +kernel
  have hratR : ((((1892582081355831 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((3780691431237133 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7673:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_973 : ((((7579274830446203 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7681 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7673 < q → q < 7681 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7681).mp (by decide +kernel))) hgap
  have hprev := thV_972
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7681:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7579274830446203 : ℚ) / 1000000000000) ≤ ((1892582081355831 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (7681:ℚ) := by decide +kernel
  have hratR : ((((7579274830446203 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1892582081355831 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7681:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_974 : ((((474263882269527 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7687 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7681 < q → q < 7687 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7687).mp (by decide +kernel))) hgap
  have hprev := thV_973
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7687:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((474263882269527 : ℚ) / 62500000000) ≤ ((7579274830446203 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (7687:ℚ) := by decide +kernel
  have hratR : ((((474263882269527 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((7579274830446203 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7687:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_975 : ((((7597169922402369 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7691 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7687 < q → q < 7691 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7691).mp (by decide +kernel))) hgap
  have hprev := thV_974
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7691:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7597169922402369 : ℚ) / 1000000000000) ≤ ((474263882269527 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (7691:ℚ) := by decide +kernel
  have hratR : ((((7597169922402369 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((474263882269527 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7691:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_976 : ((((7606118768128527 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7699 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7691 < q → q < 7699 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7699).mp (by decide +kernel))) hgap
  have hprev := thV_975
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7699:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7606118768128527 : ℚ) / 1000000000000) ≤ ((7597169922402369 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (7699:ℚ) := by decide +kernel
  have hratR : ((((7606118768128527 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((7597169922402369 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7699:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_977 : ((((95188351665847 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7703 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7699 < q → q < 7703 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7703).mp (by decide +kernel))) hgap
  have hprev := thV_976
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7703:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((95188351665847 : ℚ) / 12500000000) ≤ ((7606118768128527 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (7703:ℚ) := by decide +kernel
  have hratR : ((((95188351665847 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ ((((7606118768128527 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7703:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_978 : ((((3812009657115549 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7717 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7703 < q → q < 7717 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7717).mp (by decide +kernel))) hgap
  have hprev := thV_977
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7717:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3812009657115549 : ℚ) / 500000000000) ≤ ((95188351665847 : ℚ) / 12500000000) + Work.RHContract.RegionI.logLowQ (7717:ℚ) := by decide +kernel
  have hratR : ((((3812009657115549 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((95188351665847 : ℚ) / 12500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7717:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_979 : ((((7632971272396547 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7723 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7717 < q → q < 7723 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7723).mp (by decide +kernel))) hgap
  have hprev := thV_978
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7723:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7632971272396547 : ℚ) / 1000000000000) ≤ ((3812009657115549 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (7723:ℚ) := by decide +kernel
  have hratR : ((((7632971272396547 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3812009657115549 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7723:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_980 : ((((7641923748361361 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7727 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7723 < q → q < 7727 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7727).mp (by decide +kernel))) hgap
  have hprev := thV_979
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7727:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7641923748361361 : ℚ) / 1000000000000) ≤ ((7632971272396547 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (7727:ℚ) := by decide +kernel
  have hratR : ((((7641923748361361 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((7632971272396547 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7727:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_981 : ((((3825439017257723 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7741 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7727 < q → q < 7741 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7741).mp (by decide +kernel))) hgap
  have hprev := thV_980
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7741:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3825439017257723 : ℚ) / 500000000000) ≤ ((7641923748361361 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (7741:ℚ) := by decide +kernel
  have hratR : ((((3825439017257723 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((7641923748361361 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7741:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_982 : ((((1531966773931309 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7753 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7741 < q → q < 7753 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7753).mp (by decide +kernel))) hgap
  have hprev := thV_981
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7753:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1531966773931309 : ℚ) / 200000000000) ≤ ((3825439017257723 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (7753:ℚ) := by decide +kernel
  have hratR : ((((1531966773931309 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((3825439017257723 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7753:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_983 : ((((1917197555148479 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7757 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7753 < q → q < 7757 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7757).mp (by decide +kernel))) hgap
  have hprev := thV_982
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7757:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1917197555148479 : ℚ) / 250000000000) ≤ ((1531966773931309 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (7757:ℚ) := by decide +kernel
  have hratR : ((((1917197555148479 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((1531966773931309 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7757:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_984 : ((((767774682932969 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7759 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7757 < q → q < 7759 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7759).mp (by decide +kernel))) hgap
  have hprev := thV_983
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7759:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((767774682932969 : ℚ) / 100000000000) ≤ ((1917197555148479 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (7759:ℚ) := by decide +kernel
  have hratR : ((((767774682932969 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((1917197555148479 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7759:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_985 : ((((768670729708749 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7789 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7759 < q → q < 7789 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7789).mp (by decide +kernel))) hgap
  have hprev := thV_984
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7789:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((768670729708749 : ℚ) / 100000000000) ≤ ((767774682932969 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (7789:ℚ) := by decide +kernel
  have hratR : ((((768670729708749 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((767774682932969 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7789:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_986 : ((((3847834139129107 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7793 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7789 < q → q < 7793 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7793).mp (by decide +kernel))) hgap
  have hprev := thV_985
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7793:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3847834139129107 : ℚ) / 500000000000) ≤ ((768670729708749 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (7793:ℚ) := by decide +kernel
  have hratR : ((((3847834139129107 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((768670729708749 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7793:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_987 : ((((3852316167191657 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7817 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7793 < q → q < 7817 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7817).mp (by decide +kernel))) hgap
  have hprev := thV_986
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7817:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3852316167191657 : ℚ) / 500000000000) ≤ ((3847834139129107 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (7817:ℚ) := by decide +kernel
  have hratR : ((((3852316167191657 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((3847834139129107 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7817:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_988 : ((((7713597157771879 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7823 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7817 < q → q < 7823 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7823).mp (by decide +kernel))) hgap
  have hprev := thV_987
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7823:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7713597157771879 : ℚ) / 1000000000000) ≤ ((3852316167191657 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (7823:ℚ) := by decide +kernel
  have hratR : ((((7713597157771879 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3852316167191657 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7823:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_989 : ((((7722562747835667 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7829 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7823 < q → q < 7829 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7829).mp (by decide +kernel))) hgap
  have hprev := thV_988
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7829:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7722562747835667 : ℚ) / 1000000000000) ≤ ((7713597157771879 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (7829:ℚ) := by decide +kernel
  have hratR : ((((7722562747835667 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((7713597157771879 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7829:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_990 : ((((3865764934744389 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7841 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7829 < q → q < 7841 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7841).mp (by decide +kernel))) hgap
  have hprev := thV_989
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7841:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3865764934744389 : ℚ) / 500000000000) ≤ ((7722562747835667 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (7841:ℚ) := by decide +kernel
  have hratR : ((((3865764934744389 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((7722562747835667 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7841:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_991 : ((((7740498520389033 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7853 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7841 < q → q < 7853 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7853).mp (by decide +kernel))) hgap
  have hprev := thV_990
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7853:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7740498520389033 : ℚ) / 1000000000000) ≤ ((3865764934744389 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (7853:ℚ) := by decide +kernel
  have hratR : ((((7740498520389033 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3865764934744389 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7853:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_992 : ((((3874734476230121 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7867 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7853 < q → q < 7867 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7867).mp (by decide +kernel))) hgap
  have hprev := thV_991
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7867:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3874734476230121 : ℚ) / 500000000000) ≤ ((7740498520389033 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (7867:ℚ) := by decide +kernel
  have hratR : ((((3874734476230121 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((7740498520389033 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7867:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_993 : ((((7758440146920307 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7873 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7867 < q → q < 7873 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7873).mp (by decide +kernel))) hgap
  have hprev := thV_992
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7873:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7758440146920307 : ℚ) / 1000000000000) ≤ ((3874734476230121 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (7873:ℚ) := by decide +kernel
  have hratR : ((((7758440146920307 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3874734476230121 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7873:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_994 : ((((776741184931689 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7877 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7873 < q → q < 7877 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7877).mp (by decide +kernel))) hgap
  have hprev := thV_993
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7877:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((776741184931689 : ℚ) / 100000000000) ≤ ((7758440146920307 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (7877:ℚ) := by decide +kernel
  have hratR : ((((776741184931689 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((7758440146920307 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7877:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_995 : ((((972047975698127 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7879 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7877 < q → q < 7879 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7879).mp (by decide +kernel))) hgap
  have hprev := thV_994
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7879:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((972047975698127 : ℚ) / 125000000000) ≤ ((776741184931689 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (7879:ℚ) := by decide +kernel
  have hratR : ((((972047975698127 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((776741184931689 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7879:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_996 : ((((1946339067350739 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7883 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7879 < q → q < 7883 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7883).mp (by decide +kernel))) hgap
  have hprev := thV_995
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7883:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1946339067350739 : ℚ) / 250000000000) ≤ ((972047975698127 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (7883:ℚ) := by decide +kernel
  have hratR : ((((1946339067350739 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((972047975698127 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7883:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_997 : ((((7794331014012559 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7901 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7883 < q → q < 7901 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7901).mp (by decide +kernel))) hgap
  have hprev := thV_996
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7901:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7794331014012559 : ℚ) / 1000000000000) ≤ ((1946339067350739 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (7901:ℚ) := by decide +kernel
  have hratR : ((((7794331014012559 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1946339067350739 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7901:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_998 : ((((780330651773151 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7907 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7901 < q → q < 7907 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7907).mp (by decide +kernel))) hgap
  have hprev := thV_997
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7907:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((780330651773151 : ℚ) / 100000000000) ≤ ((7794331014012559 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (7907:ℚ) := by decide +kernel
  have hratR : ((((780330651773151 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((7794331014012559 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7907:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_999 : ((((7812283537942601 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7919 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7907 < q → q < 7919 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7919).mp (by decide +kernel))) hgap
  have hprev := thV_998
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7919:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7812283537942601 : ℚ) / 1000000000000) ≤ ((780330651773151 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (7919:ℚ) := by decide +kernel
  have hratR : ((((7812283537942601 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((780330651773151 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7919:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1000 : ((((3910630783936159 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7927 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7919 < q → q < 7927 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7927).mp (by decide +kernel))) hgap
  have hprev := thV_999
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7927:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3910630783936159 : ℚ) / 500000000000) ≤ ((7812283537942601 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (7927:ℚ) := by decide +kernel
  have hratR : ((((3910630783936159 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((7812283537942601 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7927:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1001 : ((((3132096141769 : ℚ) / 400000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7933 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7927 < q → q < 7933 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7933).mp (by decide +kernel))) hgap
  have hprev := thV_1000
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7933:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3132096141769 : ℚ) / 400000000) ≤ ((3910630783936159 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (7933:ℚ) := by decide +kernel
  have hratR : ((((3132096141769 : ℚ) / 400000000) : ℚ) : ℝ) ≤ ((((3910630783936159 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7933:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1002 : ((((7839219645068471 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7937 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7933 < q → q < 7937 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7937).mp (by decide +kernel))) hgap
  have hprev := thV_1001
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7937:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7839219645068471 : ℚ) / 1000000000000) ≤ ((3132096141769 : ℚ) / 400000000) + Work.RHContract.RegionI.logLowQ (7937:ℚ) := by decide +kernel
  have hratR : ((((7839219645068471 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3132096141769 : ℚ) / 400000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7937:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1003 : ((((1962050111619731 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7949 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7937 < q → q < 7949 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7949).mp (by decide +kernel))) hgap
  have hprev := thV_1002
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7949:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1962050111619731 : ℚ) / 250000000000) ≤ ((7839219645068471 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (7949:ℚ) := by decide +kernel
  have hratR : ((((1962050111619731 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((7839219645068471 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7949:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1004 : ((((3928590749730853 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7951 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7949 < q → q < 7951 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7951).mp (by decide +kernel))) hgap
  have hprev := thV_1003
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7951:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3928590749730853 : ℚ) / 500000000000) ≤ ((1962050111619731 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (7951:ℚ) := by decide +kernel
  have hratR : ((((3928590749730853 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1962050111619731 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7951:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1005 : ((((1966541015137711 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7963 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7951 < q → q < 7963 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7963).mp (by decide +kernel))) hgap
  have hprev := thV_1004
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7963:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1966541015137711 : ℚ) / 250000000000) ≤ ((3928590749730853 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (7963:ℚ) := by decide +kernel
  have hratR : ((((1966541015137711 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((3928590749730853 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7963:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1006 : ((((157503007639707 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((7993 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7963 < q → q < 7993 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7993).mp (by decide +kernel))) hgap
  have hprev := thV_1005
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (7993:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((157503007639707 : ℚ) / 20000000000) ≤ ((1966541015137711 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (7993:ℚ) := by decide +kernel
  have hratR : ((((157503007639707 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ ((((1966541015137711 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (7993:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1007 : ((((3942069351585277 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8009 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 7993 < q → q < 8009 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8009).mp (by decide +kernel))) hgap
  have hprev := thV_1006
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8009:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3942069351585277 : ℚ) / 500000000000) ≤ ((157503007639707 : ℚ) / 20000000000) + Work.RHContract.RegionI.logLowQ (8009:ℚ) := by decide +kernel
  have hratR : ((((3942069351585277 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((157503007639707 : ℚ) / 20000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8009:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1008 : ((((7893127274043649 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8011 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8009 < q → q < 8011 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8011).mp (by decide +kernel))) hgap
  have hprev := thV_1007
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8011:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7893127274043649 : ℚ) / 1000000000000) ≤ ((3942069351585277 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (8011:ℚ) := by decide +kernel
  have hratR : ((((7893127274043649 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3942069351585277 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8011:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1009 : ((((1975529148401643 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8017 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8011 < q → q < 8017 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8017).mp (by decide +kernel))) hgap
  have hprev := thV_1008
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8017:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1975529148401643 : ℚ) / 250000000000) ≤ ((7893127274043649 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (8017:ℚ) := by decide +kernel
  have hratR : ((((1975529148401643 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((7893127274043649 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8017:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1010 : ((((395555432678989 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8039 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8017 < q → q < 8039 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8039).mp (by decide +kernel))) hgap
  have hprev := thV_1009
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8039:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((395555432678989 : ℚ) / 50000000000) ≤ ((1975529148401643 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (8039:ℚ) := by decide +kernel
  have hratR : ((((395555432678989 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((1975529148401643 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8039:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1011 : ((((990012806693557 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8053 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8039 < q → q < 8053 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8053).mp (by decide +kernel))) hgap
  have hprev := thV_1010
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8053:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((990012806693557 : ℚ) / 125000000000) ≤ ((395555432678989 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (8053:ℚ) := by decide +kernel
  have hratR : ((((990012806693557 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((395555432678989 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8053:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1012 : ((((7929096998303661 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8059 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8053 < q → q < 8059 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8059).mp (by decide +kernel))) hgap
  have hprev := thV_1011
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8059:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7929096998303661 : ℚ) / 1000000000000) ≤ ((990012806693557 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (8059:ℚ) := by decide +kernel
  have hratR : ((((7929096998303661 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((990012806693557 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8059:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1013 : ((((793809278313839 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8069 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8059 < q → q < 8069 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8069).mp (by decide +kernel))) hgap
  have hprev := thV_1012
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8069:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((793809278313839 : ℚ) / 100000000000) ≤ ((7929096998303661 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (8069:ℚ) := by decide +kernel
  have hratR : ((((793809278313839 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((7929096998303661 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8069:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1014 : ((((248346564188797 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8081 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8069 < q → q < 8081 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8081).mp (by decide +kernel))) hgap
  have hprev := thV_1013
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8081:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((248346564188797 : ℚ) / 31250000000) ≤ ((793809278313839 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (8081:ℚ) := by decide +kernel
  have hratR : ((((248346564188797 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((793809278313839 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8081:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1015 : ((((198902201678787 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8087 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8081 < q → q < 8087 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8087).mp (by decide +kernel))) hgap
  have hprev := thV_1014
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8087:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((198902201678787 : ℚ) / 25000000000) ≤ ((248346564188797 : ℚ) / 31250000000) + Work.RHContract.RegionI.logLowQ (8087:ℚ) := by decide +kernel
  have hratR : ((((198902201678787 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((248346564188797 : ℚ) / 31250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8087:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1016 : ((((3982543163770689 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8089 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8087 < q → q < 8089 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8089).mp (by decide +kernel))) hgap
  have hprev := thV_1015
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8089:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3982543163770689 : ℚ) / 500000000000) ≤ ((198902201678787 : ℚ) / 25000000000) + Work.RHContract.RegionI.logLowQ (8089:ℚ) := by decide +kernel
  have hratR : ((((3982543163770689 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((198902201678787 : ℚ) / 25000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8089:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1017 : ((((3987042541153877 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8093 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8089 < q → q < 8093 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8093).mp (by decide +kernel))) hgap
  have hprev := thV_1016
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8093:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3987042541153877 : ℚ) / 500000000000) ≤ ((3982543163770689 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (8093:ℚ) := by decide +kernel
  have hratR : ((((3987042541153877 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((3982543163770689 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8093:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1018 : ((((1596616965018893 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8101 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8093 < q → q < 8101 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8101).mp (by decide +kernel))) hgap
  have hprev := thV_1017
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8101:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1596616965018893 : ℚ) / 200000000000) ≤ ((3987042541153877 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (8101:ℚ) := by decide +kernel
  have hratR : ((((1596616965018893 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((3987042541153877 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8101:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1019 : ((((999010725191927 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8111 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8101 < q → q < 8111 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8111).mp (by decide +kernel))) hgap
  have hprev := thV_1018
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8111:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((999010725191927 : ℚ) / 125000000000) ≤ ((1596616965018893 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (8111:ℚ) := by decide +kernel
  have hratR : ((((999010725191927 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((1596616965018893 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8111:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1020 : ((((8001087517439057 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8117 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8111 < q → q < 8117 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8117).mp (by decide +kernel))) hgap
  have hprev := thV_1019
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8117:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8001087517439057 : ℚ) / 1000000000000) ≤ ((999010725191927 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (8117:ℚ) := by decide +kernel
  have hratR : ((((8001087517439057 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((999010725191927 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8117:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1021 : ((((2002522493064747 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8123 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8117 < q → q < 8123 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8123).mp (by decide +kernel))) hgap
  have hprev := thV_1020
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8123:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2002522493064747 : ℚ) / 250000000000) ≤ ((8001087517439057 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (8123:ℚ) := by decide +kernel
  have hratR : ((((2002522493064747 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((8001087517439057 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8123:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1022 : ((((8019095377296179 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8147 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8123 < q → q < 8147 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8147).mp (by decide +kernel))) hgap
  have hprev := thV_1021
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8147:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8019095377296179 : ℚ) / 1000000000000) ≤ ((2002522493064747 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (8147:ℚ) := by decide +kernel
  have hratR : ((((8019095377296179 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2002522493064747 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8147:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1023 : ((((250878203102579 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8161 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8147 < q → q < 8161 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8161).mp (by decide +kernel))) hgap
  have hprev := thV_1022
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8161:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((250878203102579 : ℚ) / 31250000000) ≤ ((8019095377296179 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (8161:ℚ) := by decide +kernel
  have hratR : ((((250878203102579 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((8019095377296179 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8161:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1024 : ((((4018555178101383 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8167 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8161 < q → q < 8167 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8167).mp (by decide +kernel))) hgap
  have hprev := thV_1023
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8167:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4018555178101383 : ℚ) / 500000000000) ≤ ((250878203102579 : ℚ) / 31250000000) + Work.RHContract.RegionI.logLowQ (8167:ℚ) := by decide +kernel
  have hratR : ((((4018555178101383 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((250878203102579 : ℚ) / 31250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8167:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1025 : ((((8046118702779031 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8171 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8167 < q → q < 8171 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8171).mp (by decide +kernel))) hgap
  have hprev := thV_1024
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8171:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8046118702779031 : ℚ) / 1000000000000) ≤ ((4018555178101383 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (8171:ℚ) := by decide +kernel
  have hratR : ((((8046118702779031 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4018555178101383 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8171:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1026 : ((((4027564013974323 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8179 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8171 < q → q < 8179 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8179).mp (by decide +kernel))) hgap
  have hprev := thV_1025
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8179:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4027564013974323 : ℚ) / 500000000000) ≤ ((8046118702779031 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (8179:ℚ) := by decide +kernel
  have hratR : ((((4027564013974323 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((8046118702779031 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8179:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1027 : ((((4032069409607521 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8191 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8179 < q → q < 8191 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8191).mp (by decide +kernel))) hgap
  have hprev := thV_1026
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8191:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4032069409607521 : ℚ) / 500000000000) ≤ ((4027564013974323 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (8191:ℚ) := by decide +kernel
  have hratR : ((((4032069409607521 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((4027564013974323 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8191:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1028 : ((((807315180560401 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8209 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8191 < q → q < 8209 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8209).mp (by decide +kernel))) hgap
  have hprev := thV_1027
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8209:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((807315180560401 : ℚ) / 100000000000) ≤ ((4032069409607521 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (8209:ℚ) := by decide +kernel
  have hratR : ((((807315180560401 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((4032069409607521 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8209:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1029 : ((((8082166009426779 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8219 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8209 < q → q < 8219 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8219).mp (by decide +kernel))) hgap
  have hprev := thV_1028
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8219:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8082166009426779 : ℚ) / 1000000000000) ≤ ((807315180560401 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (8219:ℚ) := by decide +kernel
  have hratR : ((((8082166009426779 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((807315180560401 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8219:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1030 : ((((8091180456558551 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8221 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8219 < q → q < 8221 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8221).mp (by decide +kernel))) hgap
  have hprev := thV_1029
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8221:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8091180456558551 : ℚ) / 1000000000000) ≤ ((8082166009426779 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (8221:ℚ) := by decide +kernel
  have hratR : ((((8091180456558551 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((8082166009426779 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8221:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1031 : ((((506262257459259 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8231 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8221 < q → q < 8231 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8231).mp (by decide +kernel))) hgap
  have hprev := thV_1030
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8231:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((506262257459259 : ℚ) / 62500000000) ≤ ((8091180456558551 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (8231:ℚ) := by decide +kernel
  have hratR : ((((506262257459259 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((8091180456558551 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8231:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1032 : ((((8109212025092063 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8233 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8231 < q → q < 8233 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8233).mp (by decide +kernel))) hgap
  have hprev := thV_1031
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8233:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8109212025092063 : ℚ) / 1000000000000) ≤ ((506262257459259 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (8233:ℚ) := by decide +kernel
  have hratR : ((((8109212025092063 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((506262257459259 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8233:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1033 : ((((1014778552070953 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8237 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8233 < q → q < 8237 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8237).mp (by decide +kernel))) hgap
  have hprev := thV_1032
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8237:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1014778552070953 : ℚ) / 125000000000) ≤ ((8109212025092063 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (8237:ℚ) := by decide +kernel
  have hratR : ((((1014778552070953 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((8109212025092063 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8237:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1034 : ((((8127245536198557 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8243 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8237 < q → q < 8243 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8243).mp (by decide +kernel))) hgap
  have hprev := thV_1033
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8243:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8127245536198557 : ℚ) / 1000000000000) ≤ ((1014778552070953 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (8243:ℚ) := by decide +kernel
  have hratR : ((((8127245536198557 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1014778552070953 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8243:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1035 : ((((4068132539595939 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8263 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8243 < q → q < 8263 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8263).mp (by decide +kernel))) hgap
  have hprev := thV_1034
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8263:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4068132539595939 : ℚ) / 500000000000) ≤ ((8127245536198557 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (8263:ℚ) := by decide +kernel
  have hratR : ((((4068132539595939 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((8127245536198557 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8263:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1036 : ((((407264267402511 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8269 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8263 < q → q < 8269 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8269).mp (by decide +kernel))) hgap
  have hprev := thV_1035
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8269:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((407264267402511 : ℚ) / 50000000000) ≤ ((4068132539595939 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (8269:ℚ) := by decide +kernel
  have hratR : ((((407264267402511 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((4068132539595939 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8269:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1037 : ((((815430610052603 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8273 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8269 < q → q < 8273 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8273).mp (by decide +kernel))) hgap
  have hprev := thV_1036
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8273:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((815430610052603 : ℚ) / 100000000000) ≤ ((407264267402511 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (8273:ℚ) := by decide +kernel
  have hratR : ((((815430610052603 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((407264267402511 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8273:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1038 : ((((8163328543823499 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8287 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8273 < q → q < 8287 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8287).mp (by decide +kernel))) hgap
  have hprev := thV_1037
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8287:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8163328543823499 : ℚ) / 1000000000000) ≤ ((815430610052603 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (8287:ℚ) := by decide +kernel
  have hratR : ((((8163328543823499 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((815430610052603 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8287:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1039 : ((((1634470293937647 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8291 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8287 < q → q < 8291 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8291).mp (by decide +kernel))) hgap
  have hprev := thV_1038
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8291:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1634470293937647 : ℚ) / 200000000000) ≤ ((8163328543823499 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (8291:ℚ) := by decide +kernel
  have hratR : ((((1634470293937647 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((8163328543823499 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8291:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1040 : ((((4090687318374653 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8293 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8291 < q → q < 8293 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8293).mp (by decide +kernel))) hgap
  have hprev := thV_1039
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8293:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4090687318374653 : ℚ) / 500000000000) ≤ ((1634470293937647 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (8293:ℚ) := by decide +kernel
  have hratR : ((((4090687318374653 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1634470293937647 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8293:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1041 : ((((819039828602859 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8297 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8293 < q → q < 8297 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8297).mp (by decide +kernel))) hgap
  have hprev := thV_1040
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8297:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((819039828602859 : ℚ) / 100000000000) ≤ ((4090687318374653 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (8297:ℚ) := by decide +kernel
  have hratR : ((((819039828602859 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((4090687318374653 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8297:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1042 : ((((8199423621242763 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8311 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8297 < q → q < 8311 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8311).mp (by decide +kernel))) hgap
  have hprev := thV_1041
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8311:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8199423621242763 : ℚ) / 1000000000000) ≤ ((819039828602859 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (8311:ℚ) := by decide +kernel
  have hratR : ((((8199423621242763 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((819039828602859 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8311:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1043 : ((((2052112419532813 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8317 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8311 < q → q < 8317 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8317).mp (by decide +kernel))) hgap
  have hprev := thV_1042
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8317:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2052112419532813 : ℚ) / 250000000000) ≤ ((8199423621242763 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (8317:ℚ) := by decide +kernel
  have hratR : ((((2052112419532813 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((8199423621242763 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8317:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1044 : ((((64199040443811 : ℚ) / 7812500000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8329 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8317 < q → q < 8329 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8329).mp (by decide +kernel))) hgap
  have hprev := thV_1043
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8329:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((64199040443811 : ℚ) / 7812500000) ≤ ((2052112419532813 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (8329:ℚ) := by decide +kernel
  have hratR : ((((64199040443811 : ℚ) / 7812500000) : ℚ) : ℝ) ≤ ((((2052112419532813 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8329:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1045 : ((((514156722052449 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8353 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8329 < q → q < 8353 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8353).mp (by decide +kernel))) hgap
  have hprev := thV_1044
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8353:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((514156722052449 : ℚ) / 62500000000) ≤ ((64199040443811 : ℚ) / 7812500000) + Work.RHContract.RegionI.logLowQ (8353:ℚ) := by decide +kernel
  have hratR : ((((514156722052449 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((64199040443811 : ℚ) / 7812500000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8353:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1046 : ((((4117769562664593 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8363 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8353 < q → q < 8363 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8363).mp (by decide +kernel))) hgap
  have hprev := thV_1045
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8363:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4117769562664593 : ℚ) / 500000000000) ≤ ((514156722052449 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (8363:ℚ) := by decide +kernel
  have hratR : ((((4117769562664593 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((514156722052449 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8363:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1047 : ((((8244571415007839 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8369 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8363 < q → q < 8369 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8369).mp (by decide +kernel))) hgap
  have hprev := thV_1046
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8369:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8244571415007839 : ℚ) / 1000000000000) ≤ ((4117769562664593 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (8369:ℚ) := by decide +kernel
  have hratR : ((((8244571415007839 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4117769562664593 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8369:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1048 : ((((8253604660138613 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8377 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8369 < q → q < 8377 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8377).mp (by decide +kernel))) hgap
  have hprev := thV_1047
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8377:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8253604660138613 : ℚ) / 1000000000000) ≤ ((8244571415007839 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (8377:ℚ) := by decide +kernel
  have hratR : ((((8253604660138613 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((8244571415007839 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8377:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1049 : ((((4131319549151109 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8387 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8377 < q → q < 8387 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8387).mp (by decide +kernel))) hgap
  have hprev := thV_1048
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8387:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4131319549151109 : ℚ) / 500000000000) ≤ ((8253604660138613 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (8387:ℚ) := by decide +kernel
  have hratR : ((((4131319549151109 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((8253604660138613 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8387:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1050 : ((((1654334754980337 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8389 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8387 < q → q < 8389 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8389).mp (by decide +kernel))) hgap
  have hprev := thV_1049
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8389:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1654334754980337 : ℚ) / 200000000000) ≤ ((4131319549151109 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (8389:ℚ) := by decide +kernel
  have hratR : ((((1654334754980337 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((4131319549151109 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8389:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1051 : ((((8280712021233643 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8419 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8389 < q → q < 8419 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8419).mp (by decide +kernel))) hgap
  have hprev := thV_1050
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8419:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8280712021233643 : ℚ) / 1000000000000) ≤ ((1654334754980337 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (8419:ℚ) := by decide +kernel
  have hratR : ((((8280712021233643 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1654334754980337 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8419:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1052 : ((((8289750742568579 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8423 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8419 < q → q < 8423 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8423).mp (by decide +kernel))) hgap
  have hprev := thV_1051
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8423:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8289750742568579 : ℚ) / 1000000000000) ≤ ((8280712021233643 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (8423:ℚ) := by decide +kernel
  have hratR : ((((8289750742568579 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((8280712021233643 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8423:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1053 : ((((8298790175985197 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8429 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8423 < q → q < 8429 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8429).mp (by decide +kernel))) hgap
  have hprev := thV_1052
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8429:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8298790175985197 : ℚ) / 1000000000000) ≤ ((8289750742568579 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (8429:ℚ) := by decide +kernel
  have hratR : ((((8298790175985197 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((8289750742568579 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8429:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1054 : ((((415391492332487 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8431 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8429 < q → q < 8431 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8431).mp (by decide +kernel))) hgap
  have hprev := thV_1053
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8431:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((415391492332487 : ℚ) / 50000000000) ≤ ((8298790175985197 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (8431:ℚ) := by decide +kernel
  have hratR : ((((415391492332487 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((8298790175985197 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8431:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1055 : ((((831687093962103 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8443 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8431 < q → q < 8443 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8443).mp (by decide +kernel))) hgap
  have hprev := thV_1054
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8443:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((831687093962103 : ℚ) / 100000000000) ≤ ((415391492332487 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (8443:ℚ) := by decide +kernel
  have hratR : ((((831687093962103 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((415391492332487 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8443:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1056 : ((((4162956253122689 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8447 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8443 < q → q < 8447 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8447).mp (by decide +kernel))) hgap
  have hprev := thV_1055
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8447:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4162956253122689 : ℚ) / 500000000000) ≤ ((831687093962103 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (8447:ℚ) := by decide +kernel
  have hratR : ((((4162956253122689 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((831687093962103 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8447:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1057 : ((((8334955728890923 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8461 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8447 < q → q < 8461 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8461).mp (by decide +kernel))) hgap
  have hprev := thV_1056
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8461:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8334955728890923 : ℚ) / 1000000000000) ≤ ((4162956253122689 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (8461:ℚ) := by decide +kernel
  have hratR : ((((8334955728890923 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4162956253122689 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8461:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1058 : ((((1668799932084237 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8467 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8461 < q → q < 8467 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8467).mp (by decide +kernel))) hgap
  have hprev := thV_1057
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8467:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1668799932084237 : ℚ) / 200000000000) ≤ ((8334955728890923 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (8467:ℚ) := by decide +kernel
  have hratR : ((((1668799932084237 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((8334955728890923 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8467:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1059 : ((((8353047599500423 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8501 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8467 < q → q < 8501 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8501).mp (by decide +kernel))) hgap
  have hprev := thV_1058
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8501:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8353047599500423 : ℚ) / 1000000000000) ≤ ((1668799932084237 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (8501:ℚ) := by decide +kernel
  have hratR : ((((8353047599500423 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1668799932084237 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8501:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1060 : ((((8362096949182927 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8513 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8501 < q → q < 8513 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8513).mp (by decide +kernel))) hgap
  have hprev := thV_1059
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8513:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8362096949182927 : ℚ) / 1000000000000) ≤ ((8353047599500423 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (8513:ℚ) := by decide +kernel
  have hratR : ((((8362096949182927 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((8353047599500423 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8513:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1061 : ((((66969177905307 : ℚ) / 8000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8521 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8513 < q → q < 8521 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8521).mp (by decide +kernel))) hgap
  have hprev := thV_1060
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8521:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((66969177905307 : ℚ) / 8000000000) ≤ ((8362096949182927 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (8521:ℚ) := by decide +kernel
  have hratR : ((((66969177905307 : ℚ) / 8000000000) : ℚ) : ℝ) ≤ ((((8362096949182927 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8521:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1062 : ((((8380198231038737 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8527 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8521 < q → q < 8527 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8527).mp (by decide +kernel))) hgap
  have hprev := thV_1061
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8527:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8380198231038737 : ℚ) / 1000000000000) ≤ ((66969177905307 : ℚ) / 8000000000) + Work.RHContract.RegionI.logLowQ (8527:ℚ) := by decide +kernel
  have hratR : ((((8380198231038737 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((66969177905307 : ℚ) / 8000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8527:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1063 : ((((524328149748273 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8537 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8527 < q → q < 8537 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8537).mp (by decide +kernel))) hgap
  have hprev := thV_1062
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8537:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((524328149748273 : ℚ) / 62500000000) ≤ ((8380198231038737 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (8537:ℚ) := by decide +kernel
  have hratR : ((((524328149748273 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((8380198231038737 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8537:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1064 : ((((16402935146783 : ℚ) / 1953125000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8539 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8537 < q → q < 8539 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8539).mp (by decide +kernel))) hgap
  have hprev := thV_1063
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8539:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((16402935146783 : ℚ) / 1953125000) ≤ ((524328149748273 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (8539:ℚ) := by decide +kernel
  have hratR : ((((16402935146783 : ℚ) / 1953125000) : ℚ) : ℝ) ≤ ((((524328149748273 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8539:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1065 : ((((2101838915665667 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8543 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8539 < q → q < 8543 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8543).mp (by decide +kernel))) hgap
  have hprev := thV_1064
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8543:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2101838915665667 : ℚ) / 250000000000) ≤ ((16402935146783 : ℚ) / 1953125000) + Work.RHContract.RegionI.logLowQ (8543:ℚ) := by decide +kernel
  have hratR : ((((2101838915665667 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((16402935146783 : ℚ) / 1953125000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8543:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1066 : ((((4208205434267157 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8563 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8543 < q → q < 8563 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8563).mp (by decide +kernel))) hgap
  have hprev := thV_1065
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8563:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4208205434267157 : ℚ) / 500000000000) ≤ ((2101838915665667 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (8563:ℚ) := by decide +kernel
  have hratR : ((((4208205434267157 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((2101838915665667 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8563:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1067 : ((((8425467241539613 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8573 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8563 < q → q < 8573 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8573).mp (by decide +kernel))) hgap
  have hprev := thV_1066
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8573:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8425467241539613 : ℚ) / 1000000000000) ≤ ((4208205434267157 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (8573:ℚ) := by decide +kernel
  have hratR : ((((8425467241539613 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4208205434267157 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8573:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1068 : ((((210863113681801 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8581 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8573 < q → q < 8581 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8581).mp (by decide +kernel))) hgap
  have hprev := thV_1067
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8581:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((210863113681801 : ℚ) / 25000000000) ≤ ((8425467241539613 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (8581:ℚ) := by decide +kernel
  have hratR : ((((210863113681801 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((8425467241539613 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8581:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1069 : ((((1688716743170567 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8597 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8581 < q → q < 8597 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8597).mp (by decide +kernel))) hgap
  have hprev := thV_1068
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8597:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1688716743170567 : ℚ) / 200000000000) ≤ ((210863113681801 : ℚ) / 25000000000) + Work.RHContract.RegionI.logLowQ (8597:ℚ) := by decide +kernel
  have hratR : ((((1688716743170567 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((210863113681801 : ℚ) / 25000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8597:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1070 : ((((4226321558522933 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8599 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8597 < q → q < 8599 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8599).mp (by decide +kernel))) hgap
  have hprev := thV_1069
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8599:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4226321558522933 : ℚ) / 500000000000) ≤ ((1688716743170567 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (8599:ℚ) := by decide +kernel
  have hratR : ((((4226321558522933 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1688716743170567 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8599:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1071 : ((((1057712960061143 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8609 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8599 < q → q < 8609 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8609).mp (by decide +kernel))) hgap
  have hprev := thV_1070
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8609:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1057712960061143 : ℚ) / 125000000000) ≤ ((4226321558522933 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (8609:ℚ) := by decide +kernel
  have hratR : ((((1057712960061143 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((4226321558522933 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8609:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1072 : ((((8470765868816717 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8623 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8609 < q → q < 8623 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8623).mp (by decide +kernel))) hgap
  have hprev := thV_1071
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8623:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8470765868816717 : ℚ) / 1000000000000) ≤ ((1057712960061143 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (8623:ℚ) := by decide +kernel
  have hratR : ((((8470765868816717 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1057712960061143 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8623:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1073 : ((((4239914260456207 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8627 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8623 < q → q < 8627 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8627).mp (by decide +kernel))) hgap
  have hprev := thV_1072
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8627:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4239914260456207 : ℚ) / 500000000000) ≤ ((8470765868816717 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (8627:ℚ) := by decide +kernel
  have hratR : ((((4239914260456207 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((8470765868816717 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8627:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1074 : ((((8488891404811543 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8629 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8627 < q → q < 8629 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8629).mp (by decide +kernel))) hgap
  have hprev := thV_1073
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8629:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8488891404811543 : ℚ) / 1000000000000) ≤ ((4239914260456207 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (8629:ℚ) := by decide +kernel
  have hratR : ((((8488891404811543 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4239914260456207 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8629:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1075 : ((((1699591135680801 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8641 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8629 < q → q < 8641 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8641).mp (by decide +kernel))) hgap
  have hprev := thV_1074
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8641:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1699591135680801 : ℚ) / 200000000000) ≤ ((8488891404811543 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (8641:ℚ) := by decide +kernel
  have hratR : ((((1699591135680801 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((8488891404811543 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8641:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1076 : ((((4253510323059793 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8647 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8641 < q → q < 8647 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8647).mp (by decide +kernel))) hgap
  have hprev := thV_1075
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8647:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4253510323059793 : ℚ) / 500000000000) ≤ ((1699591135680801 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (8647:ℚ) := by decide +kernel
  have hratR : ((((4253510323059793 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1699591135680801 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8647:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1077 : ((((532255466404881 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8663 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8647 < q → q < 8663 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8663).mp (by decide +kernel))) hgap
  have hprev := thV_1076
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8663:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((532255466404881 : ℚ) / 62500000000) ≤ ((4253510323059793 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (8663:ℚ) := by decide +kernel
  have hratR : ((((532255466404881 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((4253510323059793 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8663:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1078 : ((((1705030994239517 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8669 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8663 < q → q < 8669 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8669).mp (by decide +kernel))) hgap
  have hprev := thV_1077
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8669:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1705030994239517 : ℚ) / 200000000000) ≤ ((532255466404881 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (8669:ℚ) := by decide +kernel
  have hratR : ((((1705030994239517 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((532255466404881 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8669:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1079 : ((((8534223402319999 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8677 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8669 < q → q < 8677 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8677).mp (by decide +kernel))) hgap
  have hprev := thV_1078
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8677:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8534223402319999 : ℚ) / 1000000000000) ≤ ((1705030994239517 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (8677:ℚ) := by decide +kernel
  have hratR : ((((8534223402319999 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1705030994239517 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8677:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1080 : ((((8543292294325011 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8681 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8677 < q → q < 8681 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8681).mp (by decide +kernel))) hgap
  have hprev := thV_1079
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8681:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8543292294325011 : ℚ) / 1000000000000) ≤ ((8534223402319999 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (8681:ℚ) := by decide +kernel
  have hratR : ((((8543292294325011 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((8534223402319999 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8681:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1081 : ((((855236210745847 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8689 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8681 < q → q < 8689 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8689).mp (by decide +kernel))) hgap
  have hprev := thV_1080
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8689:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((855236210745847 : ℚ) / 100000000000) ≤ ((8543292294325011 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (8689:ℚ) := by decide +kernel
  have hratR : ((((855236210745847 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((8543292294325011 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8689:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1082 : ((((8561432380838169 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8693 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8689 < q → q < 8693 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8693).mp (by decide +kernel))) hgap
  have hprev := thV_1081
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8693:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8561432380838169 : ℚ) / 1000000000000) ≤ ((855236210745847 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (8693:ℚ) := by decide +kernel
  have hratR : ((((8561432380838169 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((855236210745847 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8693:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1083 : ((((8570503344190297 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8699 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8693 < q → q < 8699 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8699).mp (by decide +kernel))) hgap
  have hprev := thV_1082
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8699:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8570503344190297 : ℚ) / 1000000000000) ≤ ((8561432380838169 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (8699:ℚ) := by decide +kernel
  have hratR : ((((8570503344190297 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((8561432380838169 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8699:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1084 : ((((4289787613382873 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8707 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8699 < q → q < 8707 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8707).mp (by decide +kernel))) hgap
  have hprev := thV_1083
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8707:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4289787613382873 : ℚ) / 500000000000) ≤ ((8570503344190297 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (8707:ℚ) := by decide +kernel
  have hratR : ((((4289787613382873 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((8570503344190297 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8707:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1085 : ((((8588647798204597 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8713 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8707 < q → q < 8713 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8713).mp (by decide +kernel))) hgap
  have hprev := thV_1084
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8713:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8588647798204597 : ℚ) / 1000000000000) ≤ ((4289787613382873 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (8713:ℚ) := by decide +kernel
  have hratR : ((((8588647798204597 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4289787613382873 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8713:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1086 : ((((1719544211606529 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8719 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8713 < q → q < 8719 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8719).mp (by decide +kernel))) hgap
  have hprev := thV_1085
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8719:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1719544211606529 : ℚ) / 200000000000) ≤ ((8588647798204597 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (8719:ℚ) := by decide +kernel
  have hratR : ((((1719544211606529 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((8588647798204597 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8719:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1087 : ((((2151698923304769 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8731 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8719 < q → q < 8731 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8731).mp (by decide +kernel))) hgap
  have hprev := thV_1086
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8731:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2151698923304769 : ℚ) / 250000000000) ≤ ((1719544211606529 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (8731:ℚ) := by decide +kernel
  have hratR : ((((2151698923304769 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((1719544211606529 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8731:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1088 : ((((4307935507687997 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8737 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8731 < q → q < 8737 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8737).mp (by decide +kernel))) hgap
  have hprev := thV_1087
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8737:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4307935507687997 : ℚ) / 500000000000) ≤ ((2151698923304769 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (8737:ℚ) := by decide +kernel
  have hratR : ((((4307935507687997 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((2151698923304769 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8737:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1089 : ((((1724989359050239 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8741 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8737 < q → q < 8741 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8741).mp (by decide +kernel))) hgap
  have hprev := thV_1088
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8741:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1724989359050239 : ℚ) / 200000000000) ≤ ((4307935507687997 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (8741:ℚ) := by decide +kernel
  have hratR : ((((1724989359050239 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((4307935507687997 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8741:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1090 : ((((1726804652262247 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8747 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8741 < q → q < 8747 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8747).mp (by decide +kernel))) hgap
  have hprev := thV_1089
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8747:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1726804652262247 : ℚ) / 200000000000) ≤ ((1724989359050239 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (8747:ℚ) := by decide +kernel
  have hratR : ((((1726804652262247 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((1724989359050239 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8747:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1091 : ((((2160775103271397 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8753 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8747 < q → q < 8753 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8753).mp (by decide +kernel))) hgap
  have hprev := thV_1090
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8753:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2160775103271397 : ℚ) / 250000000000) ≤ ((1726804652262247 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (8753:ℚ) := by decide +kernel
  have hratR : ((((2160775103271397 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((1726804652262247 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8753:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1092 : ((((69217427827319 : ℚ) / 8000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8761 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8753 < q → q < 8761 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8761).mp (by decide +kernel))) hgap
  have hprev := thV_1091
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8761:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((69217427827319 : ℚ) / 8000000000) ≤ ((2160775103271397 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (8761:ℚ) := by decide +kernel
  have hratR : ((((69217427827319 : ℚ) / 8000000000) : ℚ) : ℝ) ≤ ((((2160775103271397 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8761:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1093 : ((((8661258596196421 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8779 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8761 < q → q < 8779 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8779).mp (by decide +kernel))) hgap
  have hprev := thV_1092
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8779:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8661258596196421 : ℚ) / 1000000000000) ≤ ((69217427827319 : ℚ) / 8000000000) + Work.RHContract.RegionI.logLowQ (8779:ℚ) := by decide +kernel
  have hratR : ((((8661258596196421 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((69217427827319 : ℚ) / 8000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8779:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1094 : ((((4335169584753479 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8783 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8779 < q → q < 8783 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8783).mp (by decide +kernel))) hgap
  have hprev := thV_1093
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8783:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4335169584753479 : ℚ) / 500000000000) ≤ ((8661258596196421 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (8783:ℚ) := by decide +kernel
  have hratR : ((((4335169584753479 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((8661258596196421 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8783:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1095 : ((((8679422017355039 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8803 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8783 < q → q < 8803 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8803).mp (by decide +kernel))) hgap
  have hprev := thV_1094
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8803:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8679422017355039 : ℚ) / 1000000000000) ≤ ((4335169584753479 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (8803:ℚ) := by decide +kernel
  have hratR : ((((8679422017355039 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4335169584753479 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8803:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1096 : ((((1737701063898093 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8807 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8803 < q → q < 8807 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8807).mp (by decide +kernel))) hgap
  have hprev := thV_1095
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8807:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1737701063898093 : ℚ) / 200000000000) ≤ ((8679422017355039 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (8807:ℚ) := by decide +kernel
  have hratR : ((((1737701063898093 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((8679422017355039 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8807:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1097 : ((((8697589983250973 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8819 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8807 < q → q < 8819 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8819).mp (by decide +kernel))) hgap
  have hprev := thV_1096
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8819:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8697589983250973 : ℚ) / 1000000000000) ≤ ((1737701063898093 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (8819:ℚ) := by decide +kernel
  have hratR : ((((8697589983250973 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1737701063898093 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8819:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1098 : ((((2176668718442213 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8821 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8819 < q → q < 8821 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8821).mp (by decide +kernel))) hgap
  have hprev := thV_1097
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8821:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2176668718442213 : ℚ) / 250000000000) ≤ ((8697589983250973 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (8821:ℚ) := by decide +kernel
  have hratR : ((((2176668718442213 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((8697589983250973 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8821:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1099 : ((((8715760897302941 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8831 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8821 < q → q < 8831 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8831).mp (by decide +kernel))) hgap
  have hprev := thV_1098
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8831:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8715760897302941 : ℚ) / 1000000000000) ≤ ((2176668718442213 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (8831:ℚ) := by decide +kernel
  have hratR : ((((8715760897302941 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2176668718442213 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8831:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1100 : ((((8724847600031079 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8837 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8831 < q → q < 8837 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8837).mp (by decide +kernel))) hgap
  have hprev := thV_1099
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8837:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8724847600031079 : ℚ) / 1000000000000) ≤ ((8715760897302941 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (8837:ℚ) := by decide +kernel
  have hratR : ((((8724847600031079 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((8715760897302941 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8837:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1101 : ((((218348363226369 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8839 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8837 < q → q < 8839 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8839).mp (by decide +kernel))) hgap
  have hprev := thV_1100
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8839:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((218348363226369 : ℚ) / 25000000000) ≤ ((8724847600031079 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (8839:ℚ) := by decide +kernel
  have hratR : ((((218348363226369 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((8724847600031079 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8839:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1102 : ((((1092877823598581 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8849 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8839 < q → q < 8849 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8849).mp (by decide +kernel))) hgap
  have hprev := thV_1101
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8849:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1092877823598581 : ℚ) / 125000000000) ≤ ((218348363226369 : ℚ) / 25000000000) + Work.RHContract.RegionI.logLowQ (8849:ℚ) := by decide +kernel
  have hratR : ((((1092877823598581 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((218348363226369 : ℚ) / 25000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8849:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1103 : ((((2188028000922329 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8861 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8849 < q → q < 8861 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8861).mp (by decide +kernel))) hgap
  have hprev := thV_1102
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8861:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2188028000922329 : ℚ) / 250000000000) ≤ ((1092877823598581 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (8861:ℚ) := by decide +kernel
  have hratR : ((((2188028000922329 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((1092877823598581 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8861:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1104 : ((((350448065770907 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8863 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8861 < q → q < 8863 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8863).mp (by decide +kernel))) hgap
  have hprev := thV_1103
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8863:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((350448065770907 : ℚ) / 40000000000) ≤ ((2188028000922329 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (8863:ℚ) := by decide +kernel
  have hratR : ((((350448065770907 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((2188028000922329 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8863:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1105 : ((((350811669442747 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8867 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8863 < q → q < 8867 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8867).mp (by decide +kernel))) hgap
  have hprev := thV_1104
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8867:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((350811669442747 : ℚ) / 40000000000) ≤ ((350448065770907 : ℚ) / 40000000000) + Work.RHContract.RegionI.logLowQ (8867:ℚ) := by decide +kernel
  have hratR : ((((350811669442747 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((350448065770907 : ℚ) / 40000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8867:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1106 : ((((4389692040439517 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8887 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8867 < q → q < 8887 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8887).mp (by decide +kernel))) hgap
  have hprev := thV_1105
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8887:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4389692040439517 : ℚ) / 500000000000) ≤ ((350811669442747 : ℚ) / 40000000000) + Work.RHContract.RegionI.logLowQ (8887:ℚ) := by decide +kernel
  have hratR : ((((4389692040439517 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((350811669442747 : ℚ) / 40000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8887:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1107 : ((((4394238550302527 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8893 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8887 < q → q < 8893 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8893).mp (by decide +kernel))) hgap
  have hprev := thV_1106
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8893:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4394238550302527 : ℚ) / 500000000000) ≤ ((4389692040439517 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (8893:ℚ) := by decide +kernel
  have hratR : ((((4394238550302527 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((4389692040439517 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8893:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1108 : ((((4398786744046787 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8923 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8893 < q → q < 8923 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8923).mp (by decide +kernel))) hgap
  have hprev := thV_1107
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8923:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4398786744046787 : ℚ) / 500000000000) ≤ ((4394238550302527 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (8923:ℚ) := by decide +kernel
  have hratR : ((((4398786744046787 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((4394238550302527 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8923:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1109 : ((((8806670547775711 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8929 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8923 < q → q < 8929 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8929).mp (by decide +kernel))) hgap
  have hprev := thV_1108
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8929:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8806670547775711 : ℚ) / 1000000000000) ≤ ((4398786744046787 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (8929:ℚ) := by decide +kernel
  have hratR : ((((8806670547775711 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4398786744046787 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8929:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1110 : ((((8815768055336033 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8933 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8929 < q → q < 8933 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8933).mp (by decide +kernel))) hgap
  have hprev := thV_1109
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8933:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8815768055336033 : ℚ) / 1000000000000) ≤ ((8806670547775711 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (8933:ℚ) := by decide +kernel
  have hratR : ((((8815768055336033 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((8806670547775711 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8933:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1111 : ((((8824866458051389 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8941 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8933 < q → q < 8941 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8941).mp (by decide +kernel))) hgap
  have hprev := thV_1110
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8941:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8824866458051389 : ℚ) / 1000000000000) ≤ ((8815768055336033 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (8941:ℚ) := by decide +kernel
  have hratR : ((((8824866458051389 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((8815768055336033 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8941:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1112 : ((((110424574732311 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8951 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8941 < q → q < 8951 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8951).mp (by decide +kernel))) hgap
  have hprev := thV_1111
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8951:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((110424574732311 : ℚ) / 12500000000) ≤ ((8824866458051389 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (8951:ℚ) := by decide +kernel
  have hratR : ((((110424574732311 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ ((((8824866458051389 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8951:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1113 : ((((4421533419426429 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8963 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8951 < q → q < 8963 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8963).mp (by decide +kernel))) hgap
  have hprev := thV_1112
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8963:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4421533419426429 : ℚ) / 500000000000) ≤ ((110424574732311 : ℚ) / 12500000000) + Work.RHContract.RegionI.logLowQ (8963:ℚ) := by decide +kernel
  have hratR : ((((4421533419426429 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((110424574732311 : ℚ) / 12500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8963:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1114 : ((((2213042092078899 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8969 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8963 < q → q < 8969 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8969).mp (by decide +kernel))) hgap
  have hprev := thV_1113
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8969:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2213042092078899 : ℚ) / 250000000000) ≤ ((4421533419426429 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (8969:ℚ) := by decide +kernel
  have hratR : ((((2213042092078899 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((4421533419426429 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8969:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1115 : ((((354450804829751 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8971 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8969 < q → q < 8971 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8971).mp (by decide +kernel))) hgap
  have hprev := thV_1114
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8971:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((354450804829751 : ℚ) / 40000000000) ≤ ((2213042092078899 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (8971:ℚ) := by decide +kernel
  have hratR : ((((354450804829751 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((2213042092078899 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8971:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1116 : ((((8870374989479429 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((8999 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8971 < q → q < 8999 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8999).mp (by decide +kernel))) hgap
  have hprev := thV_1115
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (8999:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8870374989479429 : ℚ) / 1000000000000) ≤ ((354450804829751 : ℚ) / 40000000000) + Work.RHContract.RegionI.logLowQ (8999:ℚ) := by decide +kernel
  have hratR : ((((8870374989479429 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((354450804829751 : ℚ) / 40000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (8999:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1117 : ((((4439740040218653 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9001 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 8999 < q → q < 9001 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9001).mp (by decide +kernel))) hgap
  have hprev := thV_1116
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9001:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4439740040218653 : ℚ) / 500000000000) ≤ ((8870374989479429 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (9001:ℚ) := by decide +kernel
  have hratR : ((((4439740040218653 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((8870374989479429 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9001:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1118 : ((((888858583776571 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9007 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9001 < q → q < 9007 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9007).mp (by decide +kernel))) hgap
  have hprev := thV_1117
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9007:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((888858583776571 : ℚ) / 100000000000) ≤ ((4439740040218653 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (9007:ℚ) := by decide +kernel
  have hratR : ((((888858583776571 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((4439740040218653 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9007:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1119 : ((((1779538407818913 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9011 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9007 < q → q < 9011 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9011).mp (by decide +kernel))) hgap
  have hprev := thV_1118
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9011:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1779538407818913 : ℚ) / 200000000000) ≤ ((888858583776571 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (9011:ℚ) := by decide +kernel
  have hratR : ((((1779538407818913 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((888858583776571 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9011:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1120 : ((((4453399231174871 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9013 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9011 < q → q < 9013 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9013).mp (by decide +kernel))) hgap
  have hprev := thV_1119
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9013:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4453399231174871 : ℚ) / 500000000000) ≤ ((1779538407818913 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (9013:ℚ) := by decide +kernel
  have hratR : ((((4453399231174871 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1779538407818913 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9013:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1121 : ((((891590665924467 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9029 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9013 < q → q < 9029 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9029).mp (by decide +kernel))) hgap
  have hprev := thV_1120
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9029:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((891590665924467 : ℚ) / 100000000000) ≤ ((4453399231174871 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (9029:ℚ) := by decide +kernel
  have hratR : ((((891590665924467 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((4453399231174871 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9029:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1122 : ((((2231254046077007 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9041 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9029 < q → q < 9041 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9041).mp (by decide +kernel))) hgap
  have hprev := thV_1121
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9041:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2231254046077007 : ℚ) / 250000000000) ≤ ((891590665924467 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (9041:ℚ) := by decide +kernel
  have hratR : ((((2231254046077007 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((891590665924467 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9041:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1123 : ((((8934125930561389 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9043 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9041 < q → q < 9043 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9043).mp (by decide +kernel))) hgap
  have hprev := thV_1122
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9043:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8934125930561389 : ℚ) / 1000000000000) ≤ ((2231254046077007 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (9043:ℚ) := by decide +kernel
  have hratR : ((((8934125930561389 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2231254046077007 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9043:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1124 : ((((55895227125571 : ℚ) / 6250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9049 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9043 < q → q < 9049 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9049).mp (by decide +kernel))) hgap
  have hprev := thV_1123
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9049:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((55895227125571 : ℚ) / 6250000000) ≤ ((8934125930561389 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (9049:ℚ) := by decide +kernel
  have hratR : ((((55895227125571 : ℚ) / 6250000000) : ℚ) : ℝ) ≤ ((((8934125930561389 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9049:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1125 : ((((8952347854105649 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9059 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9049 < q → q < 9059 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9059).mp (by decide +kernel))) hgap
  have hprev := thV_1124
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9059:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8952347854105649 : ℚ) / 1000000000000) ≤ ((55895227125571 : ℚ) / 6250000000) + Work.RHContract.RegionI.logLowQ (9059:ℚ) := by decide +kernel
  have hratR : ((((8952347854105649 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((55895227125571 : ℚ) / 6250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9059:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1126 : ((((1792292050165983 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9067 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9059 < q → q < 9067 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9067).mp (by decide +kernel))) hgap
  have hprev := thV_1125
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9067:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1792292050165983 : ℚ) / 200000000000) ≤ ((8952347854105649 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (9067:ℚ) := by decide +kernel
  have hratR : ((((1792292050165983 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((8952347854105649 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9067:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1127 : ((((8970575291018657 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9091 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9067 < q → q < 9091 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9091).mp (by decide +kernel))) hgap
  have hprev := thV_1126
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9091:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8970575291018657 : ℚ) / 1000000000000) ≤ ((1792292050165983 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (9091:ℚ) := by decide +kernel
  have hratR : ((((8970575291018657 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1792292050165983 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9091:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1128 : ((((4489845825161891 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9103 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9091 < q → q < 9103 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9103).mp (by decide +kernel))) hgap
  have hprev := thV_1127
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9103:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4489845825161891 : ℚ) / 500000000000) ≤ ((8970575291018657 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (9103:ℚ) := by decide +kernel
  have hratR : ((((4489845825161891 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((8970575291018657 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9103:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1129 : ((((8988808668535147 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9109 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9103 < q → q < 9109 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9109).mp (by decide +kernel))) hgap
  have hprev := thV_1128
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9109:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((8988808668535147 : ℚ) / 1000000000000) ≤ ((4489845825161891 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (9109:ℚ) := by decide +kernel
  have hratR : ((((8988808668535147 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4489845825161891 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9109:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1130 : ((((2249481915216071 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9127 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9109 < q → q < 9127 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9127).mp (by decide +kernel))) hgap
  have hprev := thV_1129
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9127:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2249481915216071 : ℚ) / 250000000000) ≤ ((8988808668535147 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (9127:ℚ) := by decide +kernel
  have hratR : ((((2249481915216071 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((8988808668535147 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9127:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1131 : ((((2251761827591899 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9133 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9127 < q → q < 9133 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9133).mp (by decide +kernel))) hgap
  have hprev := thV_1130
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9133:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2251761827591899 : ℚ) / 250000000000) ≤ ((2249481915216071 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (9133:ℚ) := by decide +kernel
  have hratR : ((((2251761827591899 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((2249481915216071 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9133:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1132 : ((((1803233479549443 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9137 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9133 < q → q < 9137 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9137).mp (by decide +kernel))) hgap
  have hprev := thV_1131
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9137:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1803233479549443 : ℚ) / 200000000000) ≤ ((2251761827591899 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (9137:ℚ) := by decide +kernel
  have hratR : ((((1803233479549443 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((2251761827591899 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9137:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1133 : ((((9025289016185751 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9151 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9137 < q → q < 9151 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9151).mp (by decide +kernel))) hgap
  have hprev := thV_1132
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9151:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9025289016185751 : ℚ) / 1000000000000) ≤ ((1803233479549443 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (9151:ℚ) := by decide +kernel
  have hratR : ((((9025289016185751 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1803233479549443 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9151:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1134 : ((((9034411290075479 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9157 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9151 < q → q < 9157 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9157).mp (by decide +kernel))) hgap
  have hprev := thV_1133
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9157:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9034411290075479 : ℚ) / 1000000000000) ≤ ((9025289016185751 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (9157:ℚ) := by decide +kernel
  have hratR : ((((9034411290075479 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((9025289016185751 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9157:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1135 : ((((4521767000347057 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9161 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9157 < q → q < 9161 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9161).mp (by decide +kernel))) hgap
  have hprev := thV_1134
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9161:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4521767000347057 : ℚ) / 500000000000) ≤ ((9034411290075479 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (9161:ℚ) := by decide +kernel
  have hratR : ((((4521767000347057 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((9034411290075479 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9161:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1136 : ((((2263164505089061 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9173 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9161 < q → q < 9173 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9173).mp (by decide +kernel))) hgap
  have hprev := thV_1135
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9173:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2263164505089061 : ℚ) / 250000000000) ≤ ((4521767000347057 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (9173:ℚ) := by decide +kernel
  have hratR : ((((2263164505089061 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((4521767000347057 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9173:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1137 : ((((141590357996297 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9181 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9173 < q → q < 9181 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9181).mp (by decide +kernel))) hgap
  have hprev := thV_1136
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9181:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((141590357996297 : ℚ) / 15625000000) ≤ ((2263164505089061 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (9181:ℚ) := by decide +kernel
  have hratR : ((((141590357996297 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ ((((2263164505089061 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9181:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1138 : ((((90709084564799 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9187 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9181 < q → q < 9187 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9187).mp (by decide +kernel))) hgap
  have hprev := thV_1137
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9187:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((90709084564799 : ℚ) / 10000000000) ≤ ((141590357996297 : ℚ) / 15625000000) + Work.RHContract.RegionI.logLowQ (9187:ℚ) := by decide +kernel
  have hratR : ((((90709084564799 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ ((((141590357996297 : ℚ) / 15625000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9187:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1139 : ((((9080035306537997 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9199 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9187 < q → q < 9199 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9199).mp (by decide +kernel))) hgap
  have hprev := thV_1138
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9199:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9080035306537997 : ℚ) / 1000000000000) ≤ ((90709084564799 : ℚ) / 10000000000) + Work.RHContract.RegionI.logLowQ (9199:ℚ) := by decide +kernel
  have hratR : ((((9080035306537997 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90709084564799 : ℚ) / 10000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9199:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1140 : ((((71009082744777 : ℚ) / 7812500000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9203 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9199 < q → q < 9203 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9203).mp (by decide +kernel))) hgap
  have hprev := thV_1139
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9203:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((71009082744777 : ℚ) / 7812500000) ≤ ((9080035306537997 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (9203:ℚ) := by decide +kernel
  have hratR : ((((71009082744777 : ℚ) / 7812500000) : ℚ) : ℝ) ≤ ((((9080035306537997 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9203:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1141 : ((((4549145263936899 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9209 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9203 < q → q < 9209 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9209).mp (by decide +kernel))) hgap
  have hprev := thV_1140
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9209:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4549145263936899 : ℚ) / 500000000000) ≤ ((71009082744777 : ℚ) / 7812500000) + Work.RHContract.RegionI.logLowQ (9209:ℚ) := by decide +kernel
  have hratR : ((((4549145263936899 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((71009082744777 : ℚ) / 7812500000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9209:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1142 : ((((9107419766640957 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9221 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9209 < q → q < 9221 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9221).mp (by decide +kernel))) hgap
  have hprev := thV_1141
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9221:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9107419766640957 : ℚ) / 1000000000000) ≤ ((4549145263936899 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (9221:ℚ) := by decide +kernel
  have hratR : ((((9107419766640957 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4549145263936899 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9221:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1143 : ((((2279137413971289 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9227 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9221 < q → q < 9227 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9227).mp (by decide +kernel))) hgap
  have hprev := thV_1142
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9227:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2279137413971289 : ℚ) / 250000000000) ≤ ((9107419766640957 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (9227:ℚ) := by decide +kernel
  have hratR : ((((2279137413971289 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((9107419766640957 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9227:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1144 : ((((9125680844815447 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9239 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9227 < q → q < 9239 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9239).mp (by decide +kernel))) hgap
  have hprev := thV_1143
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9239:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9125680844815447 : ℚ) / 1000000000000) ≤ ((2279137413971289 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (9239:ℚ) := by decide +kernel
  have hratR : ((((9125680844815447 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2279137413971289 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9239:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1145 : ((((1826962450039191 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9241 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9239 < q → q < 9241 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9241).mp (by decide +kernel))) hgap
  have hprev := thV_1144
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9241:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1826962450039191 : ℚ) / 200000000000) ≤ ((9125680844815447 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (9241:ℚ) := by decide +kernel
  have hratR : ((((1826962450039191 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((9125680844815447 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9241:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1146 : ((((4571972692746821 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9257 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9241 < q → q < 9257 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9257).mp (by decide +kernel))) hgap
  have hprev := thV_1145
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9257:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4571972692746821 : ℚ) / 500000000000) ≤ ((1826962450039191 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (9257:ℚ) := by decide +kernel
  have hratR : ((((4571972692746821 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1826962450039191 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9257:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1147 : ((((1830616135797583 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9277 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9257 < q → q < 9277 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9277).mp (by decide +kernel))) hgap
  have hprev := thV_1146
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9277:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1830616135797583 : ℚ) / 200000000000) ≤ ((4571972692746821 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (9277:ℚ) := by decide +kernel
  have hratR : ((((1830616135797583 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((4571972692746821 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9277:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1148 : ((((9162216403563131 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9281 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9277 < q → q < 9281 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9281).mp (by decide +kernel))) hgap
  have hprev := thV_1147
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9281:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9162216403563131 : ℚ) / 1000000000000) ≤ ((1830616135797583 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (9281:ℚ) := by decide +kernel
  have hratR : ((((9162216403563131 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1830616135797583 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9281:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1149 : ((((9171352343609151 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9283 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9281 < q → q < 9283 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9283).mp (by decide +kernel))) hgap
  have hprev := thV_1148
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9283:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9171352343609151 : ℚ) / 1000000000000) ≤ ((9162216403563131 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (9283:ℚ) := by decide +kernel
  have hratR : ((((9171352343609151 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((9162216403563131 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9283:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1150 : ((((9180489360313329 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9293 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9283 < q → q < 9293 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9293).mp (by decide +kernel))) hgap
  have hprev := thV_1149
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9293:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9180489360313329 : ℚ) / 1000000000000) ≤ ((9171352343609151 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (9293:ℚ) := by decide +kernel
  have hratR : ((((9180489360313329 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((9171352343609151 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9293:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1151 : ((((4594814156042919 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9311 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9293 < q → q < 9311 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9311).mp (by decide +kernel))) hgap
  have hprev := thV_1150
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9311:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4594814156042919 : ℚ) / 500000000000) ≤ ((9180489360313329 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (9311:ℚ) := by decide +kernel
  have hratR : ((((4594814156042919 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((9180489360313329 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9311:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1152 : ((((2299692030672061 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9319 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9311 < q → q < 9319 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9319).mp (by decide +kernel))) hgap
  have hprev := thV_1151
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9319:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2299692030672061 : ℚ) / 250000000000) ≤ ((4594814156042919 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (9319:ℚ) := by decide +kernel
  have hratR : ((((2299692030672061 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((4594814156042919 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9319:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1153 : ((((9207908362429161 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9323 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9319 < q → q < 9323 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9323).mp (by decide +kernel))) hgap
  have hprev := thV_1152
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9323:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9207908362429161 : ℚ) / 1000000000000) ≤ ((2299692030672061 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (9323:ℚ) := by decide +kernel
  have hratR : ((((9207908362429161 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2299692030672061 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9323:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1154 : ((((1843410020541253 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9337 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9323 < q → q < 9337 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9337).mp (by decide +kernel))) hgap
  have hprev := thV_1153
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9337:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1843410020541253 : ℚ) / 200000000000) ≤ ((9207908362429161 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (9337:ℚ) := by decide +kernel
  have hratR : ((((1843410020541253 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((9207908362429161 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9337:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1155 : ((((4613096135647379 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9341 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9337 < q → q < 9341 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9341).mp (by decide +kernel))) hgap
  have hprev := thV_1154
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9341:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4613096135647379 : ℚ) / 500000000000) ≤ ((1843410020541253 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (9341:ℚ) := by decide +kernel
  have hratR : ((((4613096135647379 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1843410020541253 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9341:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1156 : ((((9235334653970171 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9343 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9341 < q → q < 9343 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9343).mp (by decide +kernel))) hgap
  have hprev := thV_1155
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9343:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9235334653970171 : ℚ) / 1000000000000) ≤ ((4613096135647379 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (9343:ℚ) := by decide +kernel
  have hratR : ((((9235334653970171 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4613096135647379 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9343:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1157 : ((((9244477678631483 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9349 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9343 < q → q < 9349 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9349).mp (by decide +kernel))) hgap
  have hprev := thV_1156
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9349:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9244477678631483 : ℚ) / 1000000000000) ≤ ((9235334653970171 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (9349:ℚ) := by decide +kernel
  have hratR : ((((9244477678631483 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((9235334653970171 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9349:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1158 : ((((9253623053721227 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9371 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9349 < q → q < 9371 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9371).mp (by decide +kernel))) hgap
  have hprev := thV_1157
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9371:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9253623053721227 : ℚ) / 1000000000000) ≤ ((9244477678631483 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (9371:ℚ) := by decide +kernel
  have hratR : ((((9253623053721227 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((9244477678631483 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9371:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1159 : ((((9262769068879267 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9377 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9371 < q → q < 9377 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9377).mp (by decide +kernel))) hgap
  have hprev := thV_1158
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9377:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9262769068879267 : ℚ) / 1000000000000) ≤ ((9253623053721227 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (9377:ℚ) := by decide +kernel
  have hratR : ((((9262769068879267 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((9253623053721227 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9377:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1160 : ((((2317979143984673 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9391 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9377 < q → q < 9391 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9391).mp (by decide +kernel))) hgap
  have hprev := thV_1159
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9391:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2317979143984673 : ℚ) / 250000000000) ≤ ((9262769068879267 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (9391:ℚ) := by decide +kernel
  have hratR : ((((2317979143984673 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((9262769068879267 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9391:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1161 : ((((1856212944340739 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9397 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9391 < q → q < 9397 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9397).mp (by decide +kernel))) hgap
  have hprev := thV_1160
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9397:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1856212944340739 : ℚ) / 200000000000) ≤ ((2317979143984673 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (9397:ℚ) := by decide +kernel
  have hratR : ((((1856212944340739 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((2317979143984673 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9397:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1162 : ((((145159586027603 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9403 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9397 < q → q < 9403 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9403).mp (by decide +kernel))) hgap
  have hprev := thV_1161
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9403:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((145159586027603 : ℚ) / 15625000000) ≤ ((1856212944340739 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (9403:ℚ) := by decide +kernel
  have hratR : ((((145159586027603 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ ((((1856212944340739 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9403:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1163 : ((((9299363352754759 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9413 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9403 < q → q < 9413 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9413).mp (by decide +kernel))) hgap
  have hprev := thV_1162
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9413:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9299363352754759 : ℚ) / 1000000000000) ≤ ((145159586027603 : ℚ) / 15625000000) + Work.RHContract.RegionI.logLowQ (9413:ℚ) := by decide +kernel
  have hratR : ((((9299363352754759 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((145159586027603 : ℚ) / 15625000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9413:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1164 : ((((4654256918478101 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9419 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9413 < q → q < 9419 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9419).mp (by decide +kernel))) hgap
  have hprev := thV_1163
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9419:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4654256918478101 : ℚ) / 500000000000) ≤ ((9299363352754759 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (9419:ℚ) := by decide +kernel
  have hratR : ((((4654256918478101 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((9299363352754759 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9419:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1165 : ((((9317664533471871 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9421 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9419 < q → q < 9421 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9421).mp (by decide +kernel))) hgap
  have hprev := thV_1164
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9421:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9317664533471871 : ℚ) / 1000000000000) ≤ ((4654256918478101 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (9421:ℚ) := by decide +kernel
  have hratR : ((((9317664533471871 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4654256918478101 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9421:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1166 : ((((1865363258176607 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9431 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9421 < q → q < 9431 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9431).mp (by decide +kernel))) hgap
  have hprev := thV_1165
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9431:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1865363258176607 : ℚ) / 200000000000) ≤ ((9317664533471871 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (9431:ℚ) := by decide +kernel
  have hratR : ((((1865363258176607 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((9317664533471871 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9431:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1167 : ((((1867193652067661 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9433 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9431 < q → q < 9433 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9433).mp (by decide +kernel))) hgap
  have hprev := thV_1166
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9433:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1867193652067661 : ℚ) / 200000000000) ≤ ((1865363258176607 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (9433:ℚ) := by decide +kernel
  have hratR : ((((1867193652067661 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((1865363258176607 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9433:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1168 : ((((9345120653746947 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9437 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9433 < q → q < 9437 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9437).mp (by decide +kernel))) hgap
  have hprev := thV_1167
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9437:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9345120653746947 : ℚ) / 1000000000000) ≤ ((1867193652067661 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (9437:ℚ) := by decide +kernel
  have hratR : ((((9345120653746947 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1867193652067661 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9437:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1169 : ((((2338568314766223 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9439 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9437 < q → q < 9439 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9439).mp (by decide +kernel))) hgap
  have hprev := thV_1168
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9439:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2338568314766223 : ℚ) / 250000000000) ≤ ((9345120653746947 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (9439:ℚ) := by decide +kernel
  have hratR : ((((2338568314766223 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((9345120653746947 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9439:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1170 : ((((9363428192426217 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9461 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9439 < q → q < 9461 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9461).mp (by decide +kernel))) hgap
  have hprev := thV_1169
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9461:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9363428192426217 : ℚ) / 1000000000000) ≤ ((2338568314766223 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (9461:ℚ) := by decide +kernel
  have hratR : ((((9363428192426217 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2338568314766223 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9461:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1171 : ((((1874516667431869 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9463 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9461 < q → q < 9463 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9463).mp (by decide +kernel))) hgap
  have hprev := thV_1170
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9463:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1874516667431869 : ℚ) / 200000000000) ≤ ((9363428192426217 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (9463:ℚ) := by decide +kernel
  have hratR : ((((1874516667431869 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((9363428192426217 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9463:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1172 : ((((4690869452251047 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9467 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9463 < q → q < 9467 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9467).mp (by decide +kernel))) hgap
  have hprev := thV_1171
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9467:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4690869452251047 : ℚ) / 500000000000) ≤ ((1874516667431869 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (9467:ℚ) := by decide +kernel
  have hratR : ((((4690869452251047 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1874516667431869 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9467:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1173 : ((((939089510542459 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9473 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9467 < q → q < 9473 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9473).mp (by decide +kernel))) hgap
  have hprev := thV_1172
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9473:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((939089510542459 : ℚ) / 100000000000) ≤ ((4690869452251047 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (9473:ℚ) := by decide +kernel
  have hratR : ((((939089510542459 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((4690869452251047 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9473:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1174 : ((((9400051939525663 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9479 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9473 < q → q < 9479 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9479).mp (by decide +kernel))) hgap
  have hprev := thV_1173
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9479:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9400051939525663 : ℚ) / 1000000000000) ≤ ((939089510542459 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (9479:ℚ) := by decide +kernel
  have hratR : ((((9400051939525663 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((939089510542459 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9479:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1175 : ((((4704605019391207 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9491 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9479 < q → q < 9491 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9491).mp (by decide +kernel))) hgap
  have hprev := thV_1174
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9491:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4704605019391207 : ℚ) / 500000000000) ≤ ((9400051939525663 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (9491:ℚ) := by decide +kernel
  have hratR : ((((4704605019391207 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((9400051939525663 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9491:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1176 : ((((9418368770017277 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9497 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9491 < q → q < 9497 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9497).mp (by decide +kernel))) hgap
  have hprev := thV_1175
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9497:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9418368770017277 : ℚ) / 1000000000000) ≤ ((4704605019391207 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (9497:ℚ) := by decide +kernel
  have hratR : ((((9418368770017277 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4704605019391207 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9497:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1177 : ((((471376448715819 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9511 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9497 < q → q < 9511 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9511).mp (by decide +kernel))) hgap
  have hprev := thV_1176
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9511:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((471376448715819 : ℚ) / 50000000000) ≤ ((9418368770017277 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (9511:ℚ) := by decide +kernel
  have hratR : ((((471376448715819 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((9418368770017277 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9511:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1178 : ((((4718345114738643 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9521 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9511 < q → q < 9521 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9521).mp (by decide +kernel))) hgap
  have hprev := thV_1177
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9521:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4718345114738643 : ℚ) / 500000000000) ≤ ((471376448715819 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (9521:ℚ) := by decide +kernel
  have hratR : ((((4718345114738643 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((471376448715819 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9521:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1179 : ((((23614631860541 : ℚ) / 2500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9533 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9521 < q → q < 9533 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9533).mp (by decide +kernel))) hgap
  have hprev := thV_1178
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9533:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((23614631860541 : ℚ) / 2500000000) ≤ ((4718345114738643 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (9533:ℚ) := by decide +kernel
  have hratR : ((((23614631860541 : ℚ) / 2500000000) : ℚ) : ℝ) ≤ ((((4718345114738643 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9533:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1180 : ((((1891003177630033 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9539 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9533 < q → q < 9539 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9539).mp (by decide +kernel))) hgap
  have hprev := thV_1179
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9539:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1891003177630033 : ℚ) / 200000000000) ≤ ((23614631860541 : ℚ) / 2500000000) + Work.RHContract.RegionI.logLowQ (9539:ℚ) := by decide +kernel
  have hratR : ((((1891003177630033 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((23614631860541 : ℚ) / 2500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9539:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1181 : ((((9464179870394783 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9547 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9539 < q → q < 9547 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9547).mp (by decide +kernel))) hgap
  have hprev := thV_1180
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9547:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9464179870394783 : ℚ) / 1000000000000) ≤ ((1891003177630033 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (9547:ℚ) := by decide +kernel
  have hratR : ((((9464179870394783 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1891003177630033 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9547:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1182 : ((((4736672135765719 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9551 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9547 < q → q < 9551 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9551).mp (by decide +kernel))) hgap
  have hprev := thV_1181
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9551:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4736672135765719 : ℚ) / 500000000000) ≤ ((9464179870394783 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (9551:ℚ) := by decide +kernel
  have hratR : ((((4736672135765719 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((9464179870394783 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9551:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1183 : ((((1896502486964227 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9587 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9551 < q → q < 9587 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9587).mp (by decide +kernel))) hgap
  have hprev := thV_1182
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9587:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1896502486964227 : ℚ) / 200000000000) ≤ ((4736672135765719 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (9587:ℚ) := by decide +kernel
  have hratR : ((((1896502486964227 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((4736672135765719 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9587:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1184 : ((((9491682057356453 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9601 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9587 < q → q < 9601 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9601).mp (by decide +kernel))) hgap
  have hprev := thV_1183
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9601:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9491682057356453 : ℚ) / 1000000000000) ≤ ((1896502486964227 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (9601:ℚ) := by decide +kernel
  have hratR : ((((9491682057356453 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1896502486964227 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9601:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1185 : ((((9500852928981139 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9613 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9601 < q → q < 9613 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9613).mp (by decide +kernel))) hgap
  have hprev := thV_1184
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9613:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9500852928981139 : ℚ) / 1000000000000) ≤ ((9491682057356453 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (9613:ℚ) := by decide +kernel
  have hratR : ((((9500852928981139 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((9491682057356453 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9613:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1186 : ((((1188753053070739 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9619 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9613 < q → q < 9619 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9619).mp (by decide +kernel))) hgap
  have hprev := thV_1185
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9619:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1188753053070739 : ℚ) / 125000000000) ≤ ((9500852928981139 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (9619:ℚ) := by decide +kernel
  have hratR : ((((1188753053070739 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((9500852928981139 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9619:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1187 : ((((9519196335907889 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9623 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9619 < q → q < 9623 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9623).mp (by decide +kernel))) hgap
  have hprev := thV_1186
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9623:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9519196335907889 : ℚ) / 1000000000000) ≤ ((1188753053070739 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (9623:ℚ) := by decide +kernel
  have hratR : ((((9519196335907889 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1188753053070739 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9623:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1188 : ((((9528368870561749 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9629 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9623 < q → q < 9629 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9629).mp (by decide +kernel))) hgap
  have hprev := thV_1187
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9629:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9528368870561749 : ℚ) / 1000000000000) ≤ ((9519196335907889 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (9629:ℚ) := by decide +kernel
  have hratR : ((((9528368870561749 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((9519196335907889 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9629:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1189 : ((((953754161289993 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9631 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9629 < q → q < 9631 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9631).mp (by decide +kernel))) hgap
  have hprev := thV_1188
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9631:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((953754161289993 : ℚ) / 100000000000) ≤ ((9528368870561749 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (9631:ℚ) := by decide +kernel
  have hratR : ((((953754161289993 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((9528368870561749 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9631:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1190 : ((((9546715600439061 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9643 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9631 < q → q < 9643 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9643).mp (by decide +kernel))) hgap
  have hprev := thV_1189
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9643:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9546715600439061 : ℚ) / 1000000000000) ≤ ((953754161289993 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (9643:ℚ) := by decide +kernel
  have hratR : ((((9546715600439061 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((953754161289993 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9643:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1191 : ((((4777945104998851 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9649 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9643 < q → q < 9649 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9649).mp (by decide +kernel))) hgap
  have hprev := thV_1190
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9649:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4777945104998851 : ℚ) / 500000000000) ≤ ((9546715600439061 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (9649:ℚ) := by decide +kernel
  have hratR : ((((4777945104998851 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((9546715600439061 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9649:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1192 : ((((3736353930639 : ℚ) / 390625000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9661 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9649 < q → q < 9661 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9661).mp (by decide +kernel))) hgap
  have hprev := thV_1191
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9661:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3736353930639 : ℚ) / 390625000) ≤ ((4777945104998851 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (9661:ℚ) := by decide +kernel
  have hratR : ((((3736353930639 : ℚ) / 390625000) : ℚ) : ℝ) ≤ ((((4777945104998851 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9661:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1193 : ((((9574243569647341 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9677 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9661 < q → q < 9677 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9677).mp (by decide +kernel))) hgap
  have hprev := thV_1192
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9677:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9574243569647341 : ℚ) / 1000000000000) ≤ ((3736353930639 : ℚ) / 390625000) + Work.RHContract.RegionI.logLowQ (9677:ℚ) := by decide +kernel
  have hratR : ((((9574243569647341 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3736353930639 : ℚ) / 390625000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9677:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1194 : ((((958342128351311 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9679 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9677 < q → q < 9679 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9679).mp (by decide +kernel))) hgap
  have hprev := thV_1193
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9679:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((958342128351311 : ℚ) / 100000000000) ≤ ((9574243569647341 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (9679:ℚ) := by decide +kernel
  have hratR : ((((958342128351311 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((9574243569647341 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9679:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1195 : ((((1918520006002023 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9689 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9679 < q → q < 9689 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9689).mp (by decide +kernel))) hgap
  have hprev := thV_1194
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9689:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1918520006002023 : ℚ) / 200000000000) ≤ ((958342128351311 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (9689:ℚ) := by decide +kernel
  have hratR : ((((1918520006002023 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((958342128351311 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9689:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1196 : ((((120022245023063 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9697 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9689 < q → q < 9697 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9697).mp (by decide +kernel))) hgap
  have hprev := thV_1195
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9697:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((120022245023063 : ℚ) / 12500000000) ≤ ((1918520006002023 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (9697:ℚ) := by decide +kernel
  have hratR : ((((120022245023063 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ ((((1918520006002023 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9697:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1197 : ((((2402740359963291 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9719 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9697 < q → q < 9719 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9719).mp (by decide +kernel))) hgap
  have hprev := thV_1196
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9719:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2402740359963291 : ℚ) / 250000000000) ≤ ((120022245023063 : ℚ) / 12500000000) + Work.RHContract.RegionI.logLowQ (9719:ℚ) := by decide +kernel
  have hratR : ((((2402740359963291 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((120022245023063 : ℚ) / 12500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9719:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1198 : ((((1924028696724521 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9721 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9719 < q → q < 9721 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9721).mp (by decide +kernel))) hgap
  have hprev := thV_1197
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9721:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1924028696724521 : ℚ) / 200000000000) ≤ ((2402740359963291 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (9721:ℚ) := by decide +kernel
  have hratR : ((((1924028696724521 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((2402740359963291 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9721:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1199 : ((((2407331690267913 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9733 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9721 < q → q < 9733 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9733).mp (by decide +kernel))) hgap
  have hprev := thV_1198
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9733:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2407331690267913 : ℚ) / 250000000000) ≤ ((1924028696724521 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (9733:ℚ) := by decide +kernel
  have hratR : ((((2407331690267913 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((1924028696724521 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9733:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1200 : ((((9638510654790233 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9739 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9733 < q → q < 9739 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9739).mp (by decide +kernel))) hgap
  have hprev := thV_1199
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9739:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9638510654790233 : ℚ) / 1000000000000) ≤ ((2407331690267913 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (9739:ℚ) := by decide +kernel
  have hratR : ((((9638510654790233 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2407331690267913 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9739:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1201 : ((((9647694959144279 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9743 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9739 < q → q < 9743 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9743).mp (by decide +kernel))) hgap
  have hprev := thV_1200
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9743:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9647694959144279 : ℚ) / 1000000000000) ≤ ((9638510654790233 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (9743:ℚ) := by decide +kernel
  have hratR : ((((9647694959144279 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((9638510654790233 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9743:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1202 : ((((1207109984891941 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9749 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9743 < q → q < 9749 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9749).mp (by decide +kernel))) hgap
  have hprev := thV_1201
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9749:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1207109984891941 : ℚ) / 125000000000) ≤ ((9647694959144279 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (9749:ℚ) := by decide +kernel
  have hratR : ((((1207109984891941 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((9647694959144279 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9749:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1203 : ((((2416516660941899 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9767 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9749 < q → q < 9767 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9767).mp (by decide +kernel))) hgap
  have hprev := thV_1202
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9767:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2416516660941899 : ℚ) / 250000000000) ≤ ((1207109984891941 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (9767:ℚ) := by decide +kernel
  have hratR : ((((2416516660941899 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((1207109984891941 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9767:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1204 : ((((9675253613149869 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9769 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9767 < q → q < 9769 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9769).mp (by decide +kernel))) hgap
  have hprev := thV_1203
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9769:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9675253613149869 : ℚ) / 1000000000000) ≤ ((2416516660941899 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (9769:ℚ) := by decide +kernel
  have hratR : ((((9675253613149869 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2416516660941899 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9769:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1205 : ((((484222090507689 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9781 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9769 < q → q < 9781 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9781).mp (by decide +kernel))) hgap
  have hprev := thV_1204
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9781:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((484222090507689 : ℚ) / 50000000000) ≤ ((9675253613149869 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (9781:ℚ) := by decide +kernel
  have hratR : ((((484222090507689 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((9675253613149869 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9781:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1206 : ((((4846815310201913 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9787 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9781 < q → q < 9787 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9787).mp (by decide +kernel))) hgap
  have hprev := thV_1205
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9787:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4846815310201913 : ℚ) / 500000000000) ≤ ((484222090507689 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (9787:ℚ) := by decide +kernel
  have hratR : ((((4846815310201913 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((484222090507689 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9787:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1207 : ((((48514099196379 : ℚ) / 5000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9791 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9787 < q → q < 9791 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9791).mp (by decide +kernel))) hgap
  have hprev := thV_1206
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9791:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((48514099196379 : ℚ) / 5000000000) ≤ ((4846815310201913 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (9791:ℚ) := by decide +kernel
  have hratR : ((((48514099196379 : ℚ) / 5000000000) : ℚ) : ℝ) ≤ ((((4846815310201913 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9791:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1208 : ((((4856005141506341 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9803 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9791 < q → q < 9803 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9803).mp (by decide +kernel))) hgap
  have hprev := thV_1207
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9803:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4856005141506341 : ℚ) / 500000000000) ≤ ((48514099196379 : ℚ) / 5000000000) + Work.RHContract.RegionI.logLowQ (9803:ℚ) := by decide +kernel
  have hratR : ((((4856005141506341 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((48514099196379 : ℚ) / 5000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9803:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1209 : ((((4860600771246733 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9811 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9803 < q → q < 9811 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9811).mp (by decide +kernel))) hgap
  have hprev := thV_1208
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9811:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4860600771246733 : ℚ) / 500000000000) ≤ ((4856005141506341 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (9811:ℚ) := by decide +kernel
  have hratR : ((((4860600771246733 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((4856005141506341 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9811:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1210 : ((((9730393413345779 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9817 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9811 < q → q < 9817 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9817).mp (by decide +kernel))) hgap
  have hprev := thV_1209
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9817:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9730393413345779 : ℚ) / 1000000000000) ≤ ((4860600771246733 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (9817:ℚ) := by decide +kernel
  have hratR : ((((9730393413345779 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4860600771246733 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9817:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1211 : ((((4869793252910483 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9829 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9817 < q → q < 9829 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9829).mp (by decide +kernel))) hgap
  have hprev := thV_1210
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9829:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4869793252910483 : ℚ) / 500000000000) ≤ ((9730393413345779 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (9829:ℚ) := by decide +kernel
  have hratR : ((((4869793252910483 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((9730393413345779 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9829:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1212 : ((((4874390002586183 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9833 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9829 < q → q < 9833 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9833).mp (by decide +kernel))) hgap
  have hprev := thV_1211
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9833:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4874390002586183 : ℚ) / 500000000000) ≤ ((4869793252910483 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (9833:ℚ) := by decide +kernel
  have hratR : ((((4874390002586183 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((4869793252910483 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9833:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1213 : ((((2439493528631963 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9839 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9833 < q → q < 9839 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9839).mp (by decide +kernel))) hgap
  have hprev := thV_1212
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9839:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2439493528631963 : ℚ) / 250000000000) ≤ ((4874390002586183 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (9839:ℚ) := by decide +kernel
  have hratR : ((((2439493528631963 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((4874390002586183 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9839:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1214 : ((((1220896180347041 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9851 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9839 < q → q < 9851 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9851).mp (by decide +kernel))) hgap
  have hprev := thV_1213
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9851:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1220896180347041 : ℚ) / 125000000000) ≤ ((2439493528631963 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (9851:ℚ) := by decide +kernel
  have hratR : ((((1220896180347041 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((2439493528631963 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9851:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1215 : ((((4888182689957307 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9857 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9851 < q → q < 9857 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9857).mp (by decide +kernel))) hgap
  have hprev := thV_1214
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9857:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4888182689957307 : ℚ) / 500000000000) ≤ ((1220896180347041 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (9857:ℚ) := by decide +kernel
  have hratR : ((((4888182689957307 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1220896180347041 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9857:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1216 : ((((9785561519933809 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9859 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9857 < q → q < 9859 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9859).mp (by decide +kernel))) hgap
  have hprev := thV_1215
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9859:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9785561519933809 : ℚ) / 1000000000000) ≤ ((4888182689957307 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (9859:ℚ) := by decide +kernel
  have hratR : ((((9785561519933809 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4888182689957307 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9859:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1217 : ((((9794758876374847 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9871 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9859 < q → q < 9871 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9871).mp (by decide +kernel))) hgap
  have hprev := thV_1216
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9871:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9794758876374847 : ℚ) / 1000000000000) ≤ ((9785561519933809 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (9871:ℚ) := by decide +kernel
  have hratR : ((((9794758876374847 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((9785561519933809 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9871:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1218 : ((((9803957447759843 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9883 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9871 < q → q < 9883 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9883).mp (by decide +kernel))) hgap
  have hprev := thV_1217
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9883:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9803957447759843 : ℚ) / 1000000000000) ≤ ((9794758876374847 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (9883:ℚ) := by decide +kernel
  have hratR : ((((9803957447759843 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((9794758876374847 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9883:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1219 : ((((245328910594959 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9887 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9883 < q → q < 9887 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9887).mp (by decide +kernel))) hgap
  have hprev := thV_1218
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9887:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((245328910594959 : ℚ) / 25000000000) ≤ ((9803957447759843 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (9887:ℚ) := by decide +kernel
  have hratR : ((((245328910594959 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((9803957447759843 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9887:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1220 : ((((9822356814836103 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9901 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9887 < q → q < 9901 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9901).mp (by decide +kernel))) hgap
  have hprev := thV_1219
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9901:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9822356814836103 : ℚ) / 1000000000000) ≤ ((245328910594959 : ℚ) / 25000000000) + Work.RHContract.RegionI.logLowQ (9901:ℚ) := by decide +kernel
  have hratR : ((((9822356814836103 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((245328910594959 : ℚ) / 25000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9901:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1221 : ((((307236181615303 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9907 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9901 < q → q < 9907 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9907).mp (by decide +kernel))) hgap
  have hprev := thV_1220
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9907:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((307236181615303 : ℚ) / 31250000000) ≤ ((9822356814836103 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (9907:ℚ) := by decide +kernel
  have hratR : ((((307236181615303 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((9822356814836103 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9907:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1222 : ((((984076042226023 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9923 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9907 < q → q < 9923 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9923).mp (by decide +kernel))) hgap
  have hprev := thV_1221
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9923:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((984076042226023 : ℚ) / 100000000000) ≤ ((307236181615303 : ℚ) / 31250000000) + Work.RHContract.RegionI.logLowQ (9923:ℚ) := by decide +kernel
  have hratR : ((((984076042226023 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((307236181615303 : ℚ) / 31250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9923:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1223 : ((((2462490909325971 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9929 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9923 < q → q < 9929 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9929).mp (by decide +kernel))) hgap
  have hprev := thV_1222
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9929:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2462490909325971 : ℚ) / 250000000000) ≤ ((984076042226023 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (9929:ℚ) := by decide +kernel
  have hratR : ((((2462490909325971 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((984076042226023 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9929:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1224 : ((((308098970429919 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9931 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9929 < q → q < 9931 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9931).mp (by decide +kernel))) hgap
  have hprev := thV_1223
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9931:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((308098970429919 : ℚ) / 31250000000) ≤ ((2462490909325971 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (9931:ℚ) := by decide +kernel
  have hratR : ((((308098970429919 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((2462490909325971 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9931:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1225 : ((((123354643458153 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9941 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9931 < q → q < 9941 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9941).mp (by decide +kernel))) hgap
  have hprev := thV_1224
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9941:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((123354643458153 : ℚ) / 12500000000) ≤ ((308098970429919 : ℚ) / 31250000000) + Work.RHContract.RegionI.logLowQ (9941:ℚ) := by decide +kernel
  have hratR : ((((123354643458153 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ ((((308098970429919 : ℚ) / 31250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9941:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1226 : ((((197551534079429 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9949 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9941 < q → q < 9949 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9949).mp (by decide +kernel))) hgap
  have hprev := thV_1225
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9949:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((197551534079429 : ℚ) / 20000000000) ≤ ((123354643458153 : ℚ) / 12500000000) + Work.RHContract.RegionI.logLowQ (9949:ℚ) := by decide +kernel
  have hratR : ((((197551534079429 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ ((((123354643458153 : ℚ) / 12500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9949:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1227 : ((((4943391869441519 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9967 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9949 < q → q < 9967 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9967).mp (by decide +kernel))) hgap
  have hprev := thV_1226
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9967:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4943391869441519 : ℚ) / 500000000000) ≤ ((197551534079429 : ℚ) / 20000000000) + Work.RHContract.RegionI.logLowQ (9967:ℚ) := by decide +kernel
  have hratR : ((((4943391869441519 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((197551534079429 : ℚ) / 20000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9967:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1228 : ((((494799568780003 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((9973 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9967 < q → q < 9973 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9973).mp (by decide +kernel))) hgap
  have hprev := thV_1227
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (9973:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((494799568780003 : ℚ) / 50000000000) ≤ ((4943391869441519 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (9973:ℚ) := by decide +kernel
  have hratR : ((((494799568780003 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((4943391869441519 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (9973:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1229 : ((((9905202415723771 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10007 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 9973 < q → q < 10007 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10007).mp (by decide +kernel))) hgap
  have hprev := thV_1228
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10007:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9905202415723771 : ℚ) / 1000000000000) ≤ ((494799568780003 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (10007:ℚ) := by decide +kernel
  have hratR : ((((9905202415723771 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((494799568780003 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10007:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1230 : ((((991441365568761 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10009 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10007 < q → q < 10009 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10009).mp (by decide +kernel))) hgap
  have hprev := thV_1229
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10009:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((991441365568761 : ℚ) / 100000000000) ≤ ((9905202415723771 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (10009:ℚ) := by decide +kernel
  have hratR : ((((991441365568761 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((9905202415723771 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10009:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1231 : ((((2480906922307011 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10037 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10009 < q → q < 10037 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10037).mp (by decide +kernel))) hgap
  have hprev := thV_1230
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10037:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2480906922307011 : ℚ) / 250000000000) ≤ ((991441365568761 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (10037:ℚ) := by decide +kernel
  have hratR : ((((2480906922307011 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((991441365568761 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10037:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1232 : ((((2483210480502839 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10039 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10037 < q → q < 10039 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10039).mp (by decide +kernel))) hgap
  have hprev := thV_1231
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10039:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2483210480502839 : ℚ) / 250000000000) ≤ ((2480906922307011 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (10039:ℚ) := by decide +kernel
  have hratR : ((((2483210480502839 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((2480906922307011 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10039:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1233 : ((((2485514585962567 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10061 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10039 < q → q < 10061 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10061).mp (by decide +kernel))) hgap
  have hprev := thV_1232
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10061:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2485514585962567 : ℚ) / 250000000000) ≤ ((2483210480502839 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (10061:ℚ) := by decide +kernel
  have hratR : ((((2485514585962567 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((2483210480502839 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10061:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1234 : ((((4975637680936809 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10067 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10061 < q → q < 10067 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10067).mp (by decide +kernel))) hgap
  have hprev := thV_1233
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10067:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4975637680936809 : ℚ) / 500000000000) ≤ ((2485514585962567 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (10067:ℚ) := by decide +kernel
  have hratR : ((((4975637680936809 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((2485514585962567 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10067:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1235 : ((((4980246289273077 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10069 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10067 < q → q < 10069 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10069).mp (by decide +kernel))) hgap
  have hprev := thV_1234
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10069:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4980246289273077 : ℚ) / 500000000000) ≤ ((4975637680936809 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (10069:ℚ) := by decide +kernel
  have hratR : ((((4980246289273077 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((4975637680936809 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10069:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1236 : ((((9969710787873129 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10079 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10069 < q → q < 10079 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10079).mp (by decide +kernel))) hgap
  have hprev := thV_1235
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10079:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9969710787873129 : ℚ) / 1000000000000) ≤ ((4980246289273077 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (10079:ℚ) := by decide +kernel
  have hratR : ((((9969710787873129 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4980246289273077 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10079:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1237 : ((((4989465093543107 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10091 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10079 < q → q < 10091 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10091).mp (by decide +kernel))) hgap
  have hprev := thV_1236
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10091:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((4989465093543107 : ℚ) / 500000000000) ≤ ((9969710787873129 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (10091:ℚ) := by decide +kernel
  have hratR : ((((4989465093543107 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((9969710787873129 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10091:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1238 : ((((9988149784476073 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10093 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10091 < q → q < 10093 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10093).mp (by decide +kernel))) hgap
  have hprev := thV_1237
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10093:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((9988149784476073 : ℚ) / 1000000000000) ≤ ((4989465093543107 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (10093:ℚ) := by decide +kernel
  have hratR : ((((9988149784476073 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4989465093543107 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10093:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1239 : ((((124967124702009 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10099 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10093 < q → q < 10099 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10099).mp (by decide +kernel))) hgap
  have hprev := thV_1238
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10099:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((124967124702009 : ℚ) / 12500000000) ≤ ((9988149784476073 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (10099:ℚ) := by decide +kernel
  have hratR : ((((124967124702009 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ ((((9988149784476073 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10099:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1240 : ((((1250823820480721 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10103 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10099 < q → q < 10103 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10103).mp (by decide +kernel))) hgap
  have hprev := thV_1239
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10103:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1250823820480721 : ℚ) / 125000000000) ≤ ((124967124702009 : ℚ) / 12500000000) + Work.RHContract.RegionI.logLowQ (10103:ℚ) := by decide +kernel
  have hratR : ((((1250823820480721 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((124967124702009 : ℚ) / 12500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10103:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1241 : ((((250395298576537 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10111 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10103 < q → q < 10111 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10111).mp (by decide +kernel))) hgap
  have hprev := thV_1240
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10111:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((250395298576537 : ℚ) / 25000000000) ≤ ((1250823820480721 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (10111:ℚ) := by decide +kernel
  have hratR : ((((250395298576537 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((1250823820480721 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10111:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1242 : ((((10025035495761549 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10133 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10111 < q → q < 10133 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10133).mp (by decide +kernel))) hgap
  have hprev := thV_1241
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10133:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10025035495761549 : ℚ) / 1000000000000) ≤ ((250395298576537 : ℚ) / 25000000000) + Work.RHContract.RegionI.logLowQ (10133:ℚ) := by decide +kernel
  have hratR : ((((10025035495761549 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((250395298576537 : ℚ) / 25000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10133:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1243 : ((((5017129820205561 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10139 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10133 < q → q < 10139 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10139).mp (by decide +kernel))) hgap
  have hprev := thV_1242
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10139:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5017129820205561 : ℚ) / 500000000000) ≤ ((10025035495761549 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (10139:ℚ) := by decide +kernel
  have hratR : ((((5017129820205561 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((10025035495761549 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10139:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1244 : ((((5021741991149677 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10141 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10139 < q → q < 10141 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10141).mp (by decide +kernel))) hgap
  have hprev := thV_1243
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10141:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5021741991149677 : ℚ) / 500000000000) ≤ ((5017129820205561 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (10141:ℚ) := by decide +kernel
  have hratR : ((((5021741991149677 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((5017129820205561 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10141:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1245 : ((((10052709309797759 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10151 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10141 < q → q < 10151 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10151).mp (by decide +kernel))) hgap
  have hprev := thV_1244
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10151:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10052709309797759 : ℚ) / 1000000000000) ≤ ((5021741991149677 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (10151:ℚ) := by decide +kernel
  have hratR : ((((10052709309797759 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5021741991149677 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10151:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1246 : ((((10061935425085471 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10159 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10151 < q → q < 10159 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10159).mp (by decide +kernel))) hgap
  have hprev := thV_1245
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10159:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10061935425085471 : ℚ) / 1000000000000) ≤ ((10052709309797759 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (10159:ℚ) := by decide +kernel
  have hratR : ((((10061935425085471 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((10052709309797759 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10159:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1247 : ((((10071161934035229 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10163 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10159 < q → q < 10163 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10163).mp (by decide +kernel))) hgap
  have hprev := thV_1246
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10163:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10071161934035229 : ℚ) / 1000000000000) ≤ ((10061935425085471 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (10163:ℚ) := by decide +kernel
  have hratR : ((((10071161934035229 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((10061935425085471 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10163:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1248 : ((((252009725829691 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10169 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10163 < q → q < 10169 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10169).mp (by decide +kernel))) hgap
  have hprev := thV_1247
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10169:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((252009725829691 : ℚ) / 25000000000) ≤ ((10071161934035229 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (10169:ℚ) := by decide +kernel
  have hratR : ((((252009725829691 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((10071161934035229 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10169:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1249 : ((((2522404229683863 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10177 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10169 < q → q < 10177 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10177).mp (by decide +kernel))) hgap
  have hprev := thV_1248
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10177:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2522404229683863 : ℚ) / 250000000000) ≤ ((252009725829691 : ℚ) / 25000000000) + Work.RHContract.RegionI.logLowQ (10177:ℚ) := by decide +kernel
  have hratR : ((((2522404229683863 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((252009725829691 : ℚ) / 25000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10177:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1250 : ((((10098845197249179 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10181 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10177 < q → q < 10181 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10181).mp (by decide +kernel))) hgap
  have hprev := thV_1249
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10181:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10098845197249179 : ℚ) / 1000000000000) ≤ ((2522404229683863 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (10181:ℚ) := by decide +kernel
  have hratR : ((((10098845197249179 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2522404229683863 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10181:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1251 : ((((1263509331716871 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10193 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10181 < q → q < 10193 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10193).mp (by decide +kernel))) hgap
  have hprev := thV_1250
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10193:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1263509331716871 : ℚ) / 125000000000) ≤ ((10098845197249179 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (10193:ℚ) := by decide +kernel
  have hratR : ((((1263509331716871 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((10098845197249179 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10193:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1252 : ((((1264663234322643 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10211 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10193 < q → q < 10211 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10211).mp (by decide +kernel))) hgap
  have hprev := thV_1251
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10211:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1264663234322643 : ℚ) / 125000000000) ≤ ((1263509331716871 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (10211:ℚ) := by decide +kernel
  have hratR : ((((1264663234322643 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((1263509331716871 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10211:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1253 : ((((10126538269940521 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10223 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10211 < q → q < 10223 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10223).mp (by decide +kernel))) hgap
  have hprev := thV_1252
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10223:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10126538269940521 : ℚ) / 1000000000000) ≤ ((1264663234322643 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (10223:ℚ) := by decide +kernel
  have hratR : ((((10126538269940521 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1264663234322643 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10223:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1254 : ((((5067886309880789 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10243 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10223 < q → q < 10243 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10243).mp (by decide +kernel))) hgap
  have hprev := thV_1253
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10243:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5067886309880789 : ℚ) / 500000000000) ≤ ((10126538269940521 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (10243:ℚ) := by decide +kernel
  have hratR : ((((5067886309880789 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((10126538269940521 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10243:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1255 : ((((5072503680008499 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10247 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10243 < q → q < 10247 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10247).mp (by decide +kernel))) hgap
  have hprev := thV_1254
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10247:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5072503680008499 : ℚ) / 500000000000) ≤ ((5067886309880789 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (10247:ℚ) := by decide +kernel
  have hratR : ((((5072503680008499 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((5067886309880789 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10247:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1256 : ((((634640167852393 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10253 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10247 < q → q < 10253 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10253).mp (by decide +kernel))) hgap
  have hprev := thV_1255
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10253:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((634640167852393 : ℚ) / 62500000000) ≤ ((5072503680008499 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (10253:ℚ) := by decide +kernel
  have hratR : ((((634640167852393 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((5072503680008499 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10253:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1257 : ((((2540869649070749 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10259 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10253 < q → q < 10259 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10259).mp (by decide +kernel))) hgap
  have hprev := thV_1256
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10259:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2540869649070749 : ℚ) / 250000000000) ≤ ((634640167852393 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (10259:ℚ) := by decide +kernel
  have hratR : ((((2540869649070749 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((634640167852393 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10259:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1258 : ((((2034543057285383 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10267 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10259 < q → q < 10267 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10267).mp (by decide +kernel))) hgap
  have hprev := thV_1257
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10267:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2034543057285383 : ℚ) / 200000000000) ≤ ((2540869649070749 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (10267:ℚ) := by decide +kernel
  have hratR : ((((2034543057285383 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((2540869649070749 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10267:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1259 : ((((10181952366092701 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10271 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10267 < q → q < 10271 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10271).mp (by decide +kernel))) hgap
  have hprev := thV_1258
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10271:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10181952366092701 : ℚ) / 1000000000000) ≤ ((2034543057285383 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (10271:ℚ) := by decide +kernel
  have hratR : ((((10181952366092701 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2034543057285383 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10271:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1260 : ((((10191189640462537 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10273 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10271 < q → q < 10273 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10273).mp (by decide +kernel))) hgap
  have hprev := thV_1259
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10273:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10191189640462537 : ℚ) / 1000000000000) ≤ ((10181952366092701 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (10273:ℚ) := by decide +kernel
  have hratR : ((((10191189640462537 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((10181952366092701 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10273:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1261 : ((((10200428471101533 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10289 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10273 < q → q < 10289 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10289).mp (by decide +kernel))) hgap
  have hprev := thV_1260
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10289:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10200428471101533 : ℚ) / 1000000000000) ≤ ((10191189640462537 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (10289:ℚ) := by decide +kernel
  have hratR : ((((10200428471101533 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((10191189640462537 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10289:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1262 : ((((10209668467355037 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10301 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10289 < q → q < 10301 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10301).mp (by decide +kernel))) hgap
  have hprev := thV_1261
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10301:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10209668467355037 : ℚ) / 1000000000000) ≤ ((10200428471101533 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (10301:ℚ) := by decide +kernel
  have hratR : ((((10209668467355037 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((10200428471101533 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10301:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1263 : ((((5109454328872801 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10303 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10301 < q → q < 10303 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10303).mp (by decide +kernel))) hgap
  have hprev := thV_1262
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10303:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5109454328872801 : ℚ) / 500000000000) ≤ ((10209668467355037 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (10303:ℚ) := by decide +kernel
  have hratR : ((((5109454328872801 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((10209668467355037 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10303:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1264 : ((((5114074909128269 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10313 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10303 < q → q < 10313 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10313).mp (by decide +kernel))) hgap
  have hprev := thV_1263
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10313:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5114074909128269 : ℚ) / 500000000000) ≤ ((5109454328872801 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (10313:ℚ) := by decide +kernel
  have hratR : ((((5114074909128269 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((5109454328872801 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10313:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1265 : ((((2559347938546681 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10321 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10313 < q → q < 10321 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10321).mp (by decide +kernel))) hgap
  have hprev := thV_1264
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10321:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2559347938546681 : ℚ) / 250000000000) ≤ ((5114074909128269 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (10321:ℚ) := by decide +kernel
  have hratR : ((((2559347938546681 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((5114074909128269 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10321:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1266 : ((((5123317329273097 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10331 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10321 < q → q < 10331 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10331).mp (by decide +kernel))) hgap
  have hprev := thV_1265
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10331:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5123317329273097 : ℚ) / 500000000000) ≤ ((2559347938546681 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (10331:ℚ) := by decide +kernel
  have hratR : ((((5123317329273097 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((2559347938546681 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10331:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1267 : ((((10255877756479029 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10333 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10331 < q → q < 10333 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10333).mp (by decide +kernel))) hgap
  have hprev := thV_1266
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10333:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10255877756479029 : ℚ) / 1000000000000) ≤ ((5123317329273097 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (10333:ℚ) := by decide +kernel
  have hratR : ((((10255877756479029 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5123317329273097 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10333:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1268 : ((((5132560620723109 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10337 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10333 < q → q < 10337 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10337).mp (by decide +kernel))) hgap
  have hprev := thV_1267
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10337:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5132560620723109 : ℚ) / 500000000000) ≤ ((10255877756479029 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (10337:ℚ) := by decide +kernel
  have hratR : ((((5132560620723109 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((10255877756479029 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10337:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1269 : ((((1284295663335527 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10343 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10337 < q → q < 10343 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10343).mp (by decide +kernel))) hgap
  have hprev := thV_1268
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10343:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1284295663335527 : ℚ) / 125000000000) ≤ ((5132560620723109 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (10343:ℚ) := by decide +kernel
  have hratR : ((((1284295663335527 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((5132560620723109 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10343:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1270 : ((((411344428983177 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10357 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10343 < q → q < 10357 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10357).mp (by decide +kernel))) hgap
  have hprev := thV_1269
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10357:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((411344428983177 : ℚ) / 40000000000) ≤ ((1284295663335527 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (10357:ℚ) := by decide +kernel
  have hratR : ((((411344428983177 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((1284295663335527 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10357:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1271 : ((((10292857300440603 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10369 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10357 < q → q < 10369 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10369).mp (by decide +kernel))) hgap
  have hprev := thV_1270
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10369:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10292857300440603 : ℚ) / 1000000000000) ≤ ((411344428983177 : ℚ) / 40000000000) + Work.RHContract.RegionI.logLowQ (10369:ℚ) := by decide +kernel
  have hratR : ((((10292857300440603 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((411344428983177 : ℚ) / 40000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10369:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1272 : ((((2575526498940769 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10391 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10369 < q → q < 10391 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10391).mp (by decide +kernel))) hgap
  have hprev := thV_1271
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10391:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2575526498940769 : ℚ) / 250000000000) ≤ ((10292857300440603 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (10391:ℚ) := by decide +kernel
  have hratR : ((((2575526498940769 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((10292857300440603 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10391:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1273 : ((((2577838865171589 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10399 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10391 < q → q < 10399 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10399).mp (by decide +kernel))) hgap
  have hprev := thV_1272
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10399:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2577838865171589 : ℚ) / 250000000000) ≤ ((2575526498940769 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (10399:ℚ) := by decide +kernel
  have hratR : ((((2577838865171589 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((2575526498940769 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10399:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1274 : ((((5160303807278883 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10427 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10399 < q → q < 10427 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10427).mp (by decide +kernel))) hgap
  have hprev := thV_1273
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10427:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5160303807278883 : ℚ) / 500000000000) ≤ ((2577838865171589 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (10427:ℚ) := by decide +kernel
  have hratR : ((((5160303807278883 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((2577838865171589 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10427:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1275 : ((((10329859960220507 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10429 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10427 < q → q < 10429 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10429).mp (by decide +kernel))) hgap
  have hprev := thV_1274
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10429:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10329859960220507 : ℚ) / 1000000000000) ≤ ((5160303807278883 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (10429:ℚ) := by decide +kernel
  have hratR : ((((10329859960220507 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5160303807278883 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10429:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1276 : ((((2067822537871119 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10433 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10429 < q → q < 10433 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10433).mp (by decide +kernel))) hgap
  have hprev := thV_1275
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10433:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2067822537871119 : ℚ) / 200000000000) ≤ ((10329859960220507 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (10433:ℚ) := by decide +kernel
  have hratR : ((((2067822537871119 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((10329859960220507 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10433:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1277 : ((((2587091833412437 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10453 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10433 < q → q < 10453 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10453).mp (by decide +kernel))) hgap
  have hprev := thV_1276
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10453:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2587091833412437 : ℚ) / 250000000000) ≤ ((2067822537871119 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (10453:ℚ) := by decide +kernel
  have hratR : ((((2587091833412437 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((2067822537871119 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10453:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1278 : ((((10357622360535967 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10457 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10453 < q → q < 10457 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10457).mp (by decide +kernel))) hgap
  have hprev := thV_1277
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10457:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10357622360535967 : ℚ) / 1000000000000) ≤ ((2587091833412437 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (10457:ℚ) := by decide +kernel
  have hratR : ((((10357622360535967 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2587091833412437 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10457:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1279 : ((((10366877578663341 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10459 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10457 < q → q < 10459 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10459).mp (by decide +kernel))) hgap
  have hprev := thV_1278
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10459:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10366877578663341 : ℚ) / 1000000000000) ≤ ((10357622360535967 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (10459:ℚ) := by decide +kernel
  have hratR : ((((10366877578663341 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((10357622360535967 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10459:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1280 : ((((5188066589581671 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10463 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10459 < q → q < 10463 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10463).mp (by decide +kernel))) hgap
  have hprev := thV_1279
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10463:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5188066589581671 : ℚ) / 500000000000) ≤ ((10366877578663341 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (10463:ℚ) := by decide +kernel
  have hratR : ((((5188066589581671 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((10366877578663341 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10463:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1281 : ((((2077078023363463 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10477 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10463 < q → q < 10477 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10477).mp (by decide +kernel))) hgap
  have hprev := thV_1280
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10477:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2077078023363463 : ℚ) / 200000000000) ≤ ((5188066589581671 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (10477:ℚ) := by decide +kernel
  have hratR : ((((2077078023363463 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((5188066589581671 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10477:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1282 : ((((1039464800848777 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10487 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10477 < q → q < 10487 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10487).mp (by decide +kernel))) hgap
  have hprev := thV_1281
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10487:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1039464800848777 : ℚ) / 100000000000) ≤ ((2077078023363463 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (10487:ℚ) := by decide +kernel
  have hratR : ((((1039464800848777 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((2077078023363463 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10487:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1283 : ((((2080781408755581 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10499 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10487 < q → q < 10499 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10499).mp (by decide +kernel))) hgap
  have hprev := thV_1282
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10499:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2080781408755581 : ℚ) / 200000000000) ≤ ((1039464800848777 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (10499:ℚ) := by decide +kernel
  have hratR : ((((2080781408755581 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((1039464800848777 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10499:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1284 : ((((10413166269544231 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10501 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10499 < q → q < 10501 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10501).mp (by decide +kernel))) hgap
  have hprev := thV_1283
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10501:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10413166269544231 : ℚ) / 1000000000000) ≤ ((2080781408755581 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (10501:ℚ) := by decide +kernel
  have hratR : ((((10413166269544231 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2080781408755581 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10501:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1285 : ((((10422426637406427 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10513 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10501 < q → q < 10513 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10513).mp (by decide +kernel))) hgap
  have hprev := thV_1284
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10513:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10422426637406427 : ℚ) / 1000000000000) ≤ ((10413166269544231 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (10513:ℚ) := by decide +kernel
  have hratR : ((((10422426637406427 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((10413166269544231 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10513:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1286 : ((((1303961065754613 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10529 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10513 < q → q < 10529 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10529).mp (by decide +kernel))) hgap
  have hprev := thV_1285
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10529:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1303961065754613 : ℚ) / 125000000000) ≤ ((10422426637406427 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (10529:ℚ) := by decide +kernel
  have hratR : ((((1303961065754613 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((10422426637406427 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10529:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1287 : ((((2088190120920181 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10531 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10529 < q → q < 10531 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10531).mp (by decide +kernel))) hgap
  have hprev := thV_1286
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10531:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2088190120920181 : ℚ) / 200000000000) ≤ ((1303961065754613 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (10531:ℚ) := by decide +kernel
  have hratR : ((((2088190120920181 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((1303961065754613 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10531:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1288 : ((((2612553834613333 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10559 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10531 < q → q < 10559 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10559).mp (by decide +kernel))) hgap
  have hprev := thV_1287
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10559:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2612553834613333 : ℚ) / 250000000000) ≤ ((2088190120920181 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (10559:ℚ) := by decide +kernel
  have hratR : ((((2612553834613333 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((2088190120920181 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10559:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1289 : ((((10459480829666393 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10567 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10559 < q → q < 10567 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10567).mp (by decide +kernel))) hgap
  have hprev := thV_1288
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10567:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10459480829666393 : ℚ) / 1000000000000) ≤ ((2612553834613333 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (10567:ℚ) := by decide +kernel
  have hratR : ((((10459480829666393 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2612553834613333 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10567:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1290 : ((((2617187100167111 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10589 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10567 < q → q < 10589 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10589).mp (by decide +kernel))) hgap
  have hprev := thV_1289
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10589:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2617187100167111 : ℚ) / 250000000000) ≤ ((10459480829666393 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (10589:ℚ) := by decide +kernel
  have hratR : ((((2617187100167111 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((10459480829666393 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10589:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1291 : ((((10478016726886239 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10597 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10589 < q → q < 10597 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10597).mp (by decide +kernel))) hgap
  have hprev := thV_1290
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10597:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10478016726886239 : ℚ) / 1000000000000) ≤ ((2617187100167111 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (10597:ℚ) := by decide +kernel
  have hratR : ((((10478016726886239 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2617187100167111 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10597:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1292 : ((((2621821357624533 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10601 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10597 < q → q < 10601 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10601).mp (by decide +kernel))) hgap
  have hprev := thV_1291
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10601:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2621821357624533 : ℚ) / 250000000000) ≤ ((10478016726886239 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (10601:ℚ) := by decide +kernel
  have hratR : ((((2621821357624533 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((10478016726886239 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10601:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1293 : ((((5248277349967129 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10607 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10601 < q → q < 10607 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10607).mp (by decide +kernel))) hgap
  have hprev := thV_1292
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10607:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5248277349967129 : ℚ) / 500000000000) ≤ ((2621821357624533 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (10607:ℚ) := by decide +kernel
  have hratR : ((((5248277349967129 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((2621821357624533 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10607:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1294 : ((((131322806685933 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10613 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10607 < q → q < 10613 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10613).mp (by decide +kernel))) hgap
  have hprev := thV_1293
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10613:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((131322806685933 : ℚ) / 12500000000) ≤ ((5248277349967129 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (10613:ℚ) := by decide +kernel
  have hratR : ((((131322806685933 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ ((((5248277349967129 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10613:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1295 : ((((10515095688082633 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10627 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10613 < q → q < 10627 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10627).mp (by decide +kernel))) hgap
  have hprev := thV_1294
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10627:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10515095688082633 : ℚ) / 1000000000000) ≤ ((131322806685933 : ℚ) / 12500000000) + Work.RHContract.RegionI.logLowQ (10627:ℚ) := by decide +kernel
  have hratR : ((((10515095688082633 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((131322806685933 : ℚ) / 12500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10627:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1296 : ((((5262183608809771 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10631 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10627 < q → q < 10631 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10631).mp (by decide +kernel))) hgap
  have hprev := thV_1295
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10631:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5262183608809771 : ℚ) / 500000000000) ≤ ((10515095688082633 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (10631:ℚ) := by decide +kernel
  have hratR : ((((5262183608809771 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((10515095688082633 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10631:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1297 : ((((10533639499389679 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10639 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10631 < q → q < 10639 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10639).mp (by decide +kernel))) hgap
  have hprev := thV_1296
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10639:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10533639499389679 : ℚ) / 1000000000000) ≤ ((5262183608809771 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (10639:ℚ) := by decide +kernel
  have hratR : ((((10533639499389679 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5262183608809771 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10639:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1298 : ((((5271456454224871 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10651 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10639 < q → q < 10651 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10651).mp (by decide +kernel))) hgap
  have hprev := thV_1297
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10651:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5271456454224871 : ℚ) / 500000000000) ≤ ((10533639499389679 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (10651:ℚ) := by decide +kernel
  have hratR : ((((5271456454224871 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((10533639499389679 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10651:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1299 : ((((10552186880678583 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10657 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10651 < q → q < 10657 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10657).mp (by decide +kernel))) hgap
  have hprev := thV_1298
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10657:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10552186880678583 : ℚ) / 1000000000000) ≤ ((5271456454224871 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (10657:ℚ) := by decide +kernel
  have hratR : ((((10552186880678583 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5271456454224871 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10657:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1300 : ((((10561461415759221 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10663 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10657 < q → q < 10663 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10663).mp (by decide +kernel))) hgap
  have hprev := thV_1299
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10663:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10561461415759221 : ℚ) / 1000000000000) ≤ ((10552186880678583 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (10663:ℚ) := by decide +kernel
  have hratR : ((((10561461415759221 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((10552186880678583 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10663:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1301 : ((((10570736325898467 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10667 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10663 < q → q < 10667 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10667).mp (by decide +kernel))) hgap
  have hprev := thV_1300
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10667:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10570736325898467 : ℚ) / 1000000000000) ≤ ((10561461415759221 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (10667:ℚ) := by decide +kernel
  have hratR : ((((10570736325898467 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((10561461415759221 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10667:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1302 : ((((2645003277305903 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10687 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10667 < q → q < 10687 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10687).mp (by decide +kernel))) hgap
  have hprev := thV_1301
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10687:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2645003277305903 : ℚ) / 250000000000) ≤ ((10570736325898467 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (10687:ℚ) := by decide +kernel
  have hratR : ((((2645003277305903 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((10570736325898467 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10687:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1303 : ((((5294645133382623 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10691 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10687 < q → q < 10691 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10691).mp (by decide +kernel))) hgap
  have hprev := thV_1302
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10691:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5294645133382623 : ℚ) / 500000000000) ≤ ((2645003277305903 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (10691:ℚ) := by decide +kernel
  have hratR : ((((5294645133382623 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((2645003277305903 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10691:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1304 : ((((10598569106550267 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10709 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10691 < q → q < 10709 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10709).mp (by decide +kernel))) hgap
  have hprev := thV_1303
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10709:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10598569106550267 : ℚ) / 1000000000000) ≤ ((5294645133382623 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (10709:ℚ) := by decide +kernel
  have hratR : ((((10598569106550267 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5294645133382623 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10709:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1305 : ((((2651962033269163 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10711 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10709 < q → q < 10711 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10711).mp (by decide +kernel))) hgap
  have hprev := thV_1304
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10711:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2651962033269163 : ℚ) / 250000000000) ≤ ((10598569106550267 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (10711:ℚ) := by decide +kernel
  have hratR : ((((2651962033269163 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((10598569106550267 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10711:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1306 : ((((2654282069829873 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10723 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10711 < q → q < 10723 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10723).mp (by decide +kernel))) hgap
  have hprev := thV_1305
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10723:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2654282069829873 : ℚ) / 250000000000) ≤ ((2651962033269163 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (10723:ℚ) := by decide +kernel
  have hratR : ((((2654282069829873 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((2651962033269163 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10723:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1307 : ((((10626408984950749 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10729 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10723 < q → q < 10729 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10729).mp (by decide +kernel))) hgap
  have hprev := thV_1306
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10729:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10626408984950749 : ℚ) / 1000000000000) ≤ ((2654282069829873 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (10729:ℚ) := by decide +kernel
  have hratR : ((((10626408984950749 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2654282069829873 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10729:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1308 : ((((10635690063333851 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10733 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10729 < q → q < 10733 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10733).mp (by decide +kernel))) hgap
  have hprev := thV_1307
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10733:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10635690063333851 : ℚ) / 1000000000000) ≤ ((10626408984950749 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (10733:ℚ) := by decide +kernel
  have hratR : ((((10635690063333851 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((10626408984950749 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10733:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1309 : ((((10644971700584329 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10739 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10733 < q → q < 10739 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10739).mp (by decide +kernel))) hgap
  have hprev := thV_1308
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10739:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10644971700584329 : ℚ) / 1000000000000) ≤ ((10635690063333851 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (10739:ℚ) := by decide +kernel
  have hratR : ((((10644971700584329 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((10635690063333851 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10739:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1310 : ((((532712732032267 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10753 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10739 < q → q < 10753 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10753).mp (by decide +kernel))) hgap
  have hprev := thV_1309
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10753:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((532712732032267 : ℚ) / 50000000000) ≤ ((10644971700584329 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (10753:ℚ) := by decide +kernel
  have hratR : ((((532712732032267 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((10644971700584329 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10753:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1311 : ((((10663539253258311 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10771 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10753 < q → q < 10771 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10771).mp (by decide +kernel))) hgap
  have hprev := thV_1310
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10771:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10663539253258311 : ℚ) / 1000000000000) ≤ ((532712732032267 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (10771:ℚ) := by decide +kernel
  have hratR : ((((10663539253258311 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((532712732032267 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10771:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1312 : ((((1067282479385947 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10781 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10771 < q → q < 10781 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10781).mp (by decide +kernel))) hgap
  have hprev := thV_1311
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10781:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1067282479385947 : ℚ) / 100000000000) ≤ ((10663539253258311 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (10781:ℚ) := by decide +kernel
  have hratR : ((((1067282479385947 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((10663539253258311 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10781:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1313 : ((((5341055538115821 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10789 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10781 < q → q < 10789 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10789).mp (by decide +kernel))) hgap
  have hprev := thV_1312
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10789:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5341055538115821 : ℚ) / 500000000000) ≤ ((1067282479385947 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (10789:ℚ) := by decide +kernel
  have hratR : ((((5341055538115821 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1067282479385947 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10789:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1314 : ((((2138279657008899 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10799 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10789 < q → q < 10799 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10799).mp (by decide +kernel))) hgap
  have hprev := thV_1313
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10799:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2138279657008899 : ℚ) / 200000000000) ≤ ((5341055538115821 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (10799:ℚ) := by decide +kernel
  have hratR : ((((2138279657008899 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((5341055538115821 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10799:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1315 : ((((10700688452712951 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10831 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10799 < q → q < 10831 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10831).mp (by decide +kernel))) hgap
  have hprev := thV_1314
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10831:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10700688452712951 : ℚ) / 1000000000000) ≤ ((2138279657008899 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (10831:ℚ) := by decide +kernel
  have hratR : ((((10700688452712951 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2138279657008899 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10831:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1316 : ((((5354989587096747 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10837 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10831 < q → q < 10837 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10837).mp (by decide +kernel))) hgap
  have hprev := thV_1315
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10837:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5354989587096747 : ℚ) / 500000000000) ≤ ((10700688452712951 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (10837:ℚ) := by decide +kernel
  have hratR : ((((5354989587096747 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((10700688452712951 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10837:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1317 : ((((5359635409006577 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10847 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10837 < q → q < 10847 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10847).mp (by decide +kernel))) hgap
  have hprev := thV_1316
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10847:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5359635409006577 : ℚ) / 500000000000) ≤ ((5354989587096747 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (10847:ℚ) := by decide +kernel
  have hratR : ((((5359635409006577 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((5354989587096747 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10847:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1318 : ((((536428150741411 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10853 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10847 < q → q < 10853 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10853).mp (by decide +kernel))) hgap
  have hprev := thV_1317
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10853:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((536428150741411 : ℚ) / 50000000000) ≤ ((5359635409006577 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (10853:ℚ) := by decide +kernel
  have hratR : ((((536428150741411 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((5359635409006577 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10853:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1319 : ((((10737855764333057 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10859 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10853 < q → q < 10859 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10859).mp (by decide +kernel))) hgap
  have hprev := thV_1318
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10859:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10737855764333057 : ℚ) / 1000000000000) ≤ ((536428150741411 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (10859:ℚ) := by decide +kernel
  have hratR : ((((10737855764333057 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((536428150741411 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10859:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1320 : ((((10747148697999957 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10861 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10859 < q → q < 10861 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10861).mp (by decide +kernel))) hgap
  have hprev := thV_1319
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10861:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10747148697999957 : ℚ) / 1000000000000) ≤ ((10737855764333057 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (10861:ℚ) := by decide +kernel
  have hratR : ((((10747148697999957 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((10737855764333057 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10861:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1321 : ((((268911054598741 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10867 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10861 < q → q < 10867 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10867).mp (by decide +kernel))) hgap
  have hprev := thV_1320
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10867:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((268911054598741 : ℚ) / 25000000000) ≤ ((10747148697999957 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (10867:ℚ) := by decide +kernel
  have hratR : ((((268911054598741 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((10747148697999957 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10867:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1322 : ((((2691434285290989 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10883 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10867 < q → q < 10883 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10883).mp (by decide +kernel))) hgap
  have hprev := thV_1321
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10883:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2691434285290989 : ℚ) / 250000000000) ≤ ((268911054598741 : ℚ) / 25000000000) + Work.RHContract.RegionI.logLowQ (10883:ℚ) := by decide +kernel
  have hratR : ((((2691434285290989 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((268911054598741 : ℚ) / 25000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10883:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1323 : ((((5387516324772461 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10889 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10883 < q → q < 10889 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10889).mp (by decide +kernel))) hgap
  have hprev := thV_1322
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10889:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5387516324772461 : ℚ) / 500000000000) ≤ ((2691434285290989 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (10889:ℚ) := by decide +kernel
  have hratR : ((((5387516324772461 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((2691434285290989 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10889:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1324 : ((((5392164170790309 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10891 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10889 < q → q < 10891 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10891).mp (by decide +kernel))) hgap
  have hprev := thV_1323
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10891:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5392164170790309 : ℚ) / 500000000000) ≤ ((5387516324772461 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (10891:ℚ) := by decide +kernel
  have hratR : ((((5392164170790309 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((5387516324772461 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10891:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1325 : ((((2158725026967389 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10903 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10891 < q → q < 10903 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10903).mp (by decide +kernel))) hgap
  have hprev := thV_1324
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10903:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2158725026967389 : ℚ) / 200000000000) ≤ ((5392164170790309 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (10903:ℚ) := by decide +kernel
  have hratR : ((((2158725026967389 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((5392164170790309 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10903:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1326 : ((((10802922478249163 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10909 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10903 < q → q < 10909 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10909).mp (by decide +kernel))) hgap
  have hprev := thV_1325
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10909:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10802922478249163 : ℚ) / 1000000000000) ≤ ((2158725026967389 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (10909:ℚ) := by decide +kernel
  have hratR : ((((10802922478249163 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2158725026967389 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10909:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1327 : ((((5406111192530559 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10937 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10909 < q → q < 10937 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10937).mp (by decide +kernel))) hgap
  have hprev := thV_1326
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10937:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5406111192530559 : ℚ) / 500000000000) ≤ ((10802922478249163 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (10937:ℚ) := by decide +kernel
  have hratR : ((((5406111192530559 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((10802922478249163 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10937:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1328 : ((((5410761237360929 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10939 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10937 < q → q < 10939 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10939).mp (by decide +kernel))) hgap
  have hprev := thV_1327
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10939:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5410761237360929 : ℚ) / 500000000000) ≤ ((5406111192530559 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (10939:ℚ) := by decide +kernel
  have hratR : ((((5410761237360929 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((5406111192530559 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10939:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1329 : ((((1353852934765669 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10949 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10939 < q → q < 10949 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10949).mp (by decide +kernel))) hgap
  have hprev := thV_1328
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10949:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1353852934765669 : ℚ) / 125000000000) ≤ ((5410761237360929 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (10949:ℚ) := by decide +kernel
  have hratR : ((((1353852934765669 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((5410761237360929 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10949:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1330 : ((((5420062605961189 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10957 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10949 < q → q < 10957 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10957).mp (by decide +kernel))) hgap
  have hprev := thV_1329
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10957:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5420062605961189 : ℚ) / 500000000000) ≤ ((1353852934765669 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (10957:ℚ) := by decide +kernel
  have hratR : ((((5420062605961189 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1353852934765669 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10957:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1331 : ((((10849428404907989 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10973 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10957 < q → q < 10973 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10973).mp (by decide +kernel))) hgap
  have hprev := thV_1330
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10973:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10849428404907989 : ℚ) / 1000000000000) ≤ ((5420062605961189 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (10973:ℚ) := by decide +kernel
  have hratR : ((((10849428404907989 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5420062605961189 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10973:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1332 : ((((2714683036135211 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10979 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10973 < q → q < 10979 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10979).mp (by decide +kernel))) hgap
  have hprev := thV_1331
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10979:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2714683036135211 : ℚ) / 250000000000) ≤ ((10849428404907989 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (10979:ℚ) := by decide +kernel
  have hratR : ((((2714683036135211 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((10849428404907989 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10979:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1333 : ((((2173607322514433 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10987 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10979 < q → q < 10987 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10987).mp (by decide +kernel))) hgap
  have hprev := thV_1332
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10987:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2173607322514433 : ℚ) / 200000000000) ≤ ((2714683036135211 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (10987:ℚ) := by decide +kernel
  have hratR : ((((2173607322514433 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((2714683036135211 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10987:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1334 : ((((2719335406638591 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((10993 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10987 < q → q < 10993 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10993).mp (by decide +kernel))) hgap
  have hprev := thV_1333
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (10993:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2719335406638591 : ℚ) / 250000000000) ≤ ((2173607322514433 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (10993:ℚ) := by decide +kernel
  have hratR : ((((2719335406638591 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((2173607322514433 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (10993:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1335 : ((((5443323774896427 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11003 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 10993 < q → q < 11003 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11003).mp (by decide +kernel))) hgap
  have hprev := thV_1334
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11003:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5443323774896427 : ℚ) / 500000000000) ≤ ((2719335406638591 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (11003:ℚ) := by decide +kernel
  have hratR : ((((5443323774896427 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((2719335406638591 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11003:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1336 : ((((10895955651879233 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11027 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11003 < q → q < 11027 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11027).mp (by decide +kernel))) hgap
  have hprev := thV_1335
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11027:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10895955651879233 : ℚ) / 1000000000000) ≤ ((5443323774896427 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (11027:ℚ) := by decide +kernel
  have hratR : ((((10895955651879233 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5443323774896427 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11027:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1337 : ((((436210622642109 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11047 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11027 < q → q < 11047 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11047).mp (by decide +kernel))) hgap
  have hprev := thV_1336
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11047:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((436210622642109 : ℚ) / 40000000000) ≤ ((10895955651879233 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (11047:ℚ) := by decide +kernel
  have hratR : ((((436210622642109 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((10895955651879233 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11047:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1338 : ((((682161024064993 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11057 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11047 < q → q < 11057 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11057).mp (by decide +kernel))) hgap
  have hprev := thV_1337
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11057:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((682161024064993 : ℚ) / 62500000000) ≤ ((436210622642109 : ℚ) / 40000000000) + Work.RHContract.RegionI.logLowQ (11057:ℚ) := by decide +kernel
  have hratR : ((((682161024064993 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((436210622642109 : ℚ) / 40000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11057:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1339 : ((((170685740388931 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11059 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11057 < q → q < 11059 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11059).mp (by decide +kernel))) hgap
  have hprev := thV_1338
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11059:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((170685740388931 : ℚ) / 15625000000) ≤ ((682161024064993 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (11059:ℚ) := by decide +kernel
  have hratR : ((((170685740388931 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ ((((682161024064993 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11059:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1340 : ((((1093319928857559 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11069 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11059 < q → q < 11069 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11069).mp (by decide +kernel))) hgap
  have hprev := thV_1339
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11069:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1093319928857559 : ℚ) / 100000000000) ≤ ((170685740388931 : ℚ) / 15625000000) + Work.RHContract.RegionI.logLowQ (11069:ℚ) := by decide +kernel
  have hratR : ((((1093319928857559 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((170685740388931 : ℚ) / 15625000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11069:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1341 : ((((1094251137292807 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11071 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11069 < q → q < 11071 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11071).mp (by decide +kernel))) hgap
  have hprev := thV_1340
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11071:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1094251137292807 : ℚ) / 100000000000) ≤ ((1093319928857559 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (11071:ℚ) := by decide +kernel
  have hratR : ((((1094251137292807 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((1093319928857559 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11071:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1342 : ((((5475912270303233 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11083 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11071 < q → q < 11083 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11083).mp (by decide +kernel))) hgap
  have hprev := thV_1341
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11083:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5475912270303233 : ℚ) / 500000000000) ≤ ((1094251137292807 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (11083:ℚ) := by decide +kernel
  have hratR : ((((5475912270303233 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1094251137292807 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11083:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1343 : ((((10961138069132859 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11087 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11083 < q → q < 11087 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11087).mp (by decide +kernel))) hgap
  have hprev := thV_1342
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11087:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10961138069132859 : ℚ) / 1000000000000) ≤ ((5475912270303233 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (11087:ℚ) := by decide +kernel
  have hratR : ((((10961138069132859 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5475912270303233 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11087:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1344 : ((((5485226069343609 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11093 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11087 < q → q < 11093 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11093).mp (by decide +kernel))) hgap
  have hprev := thV_1343
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11093:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5485226069343609 : ℚ) / 500000000000) ≤ ((10961138069132859 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (11093:ℚ) := by decide +kernel
  have hratR : ((((5485226069343609 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((10961138069132859 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11093:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1345 : ((((343117750298657 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11113 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11093 < q → q < 11113 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11113).mp (by decide +kernel))) hgap
  have hprev := thV_1344
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11113:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((343117750298657 : ℚ) / 31250000000) ≤ ((5485226069343609 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (11113:ℚ) := by decide +kernel
  have hratR : ((((343117750298657 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((5485226069343609 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11113:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1346 : ((((5494542120150439 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11117 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11113 < q → q < 11117 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11117).mp (by decide +kernel))) hgap
  have hprev := thV_1345
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11117:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5494542120150439 : ℚ) / 500000000000) ≤ ((343117750298657 : ℚ) / 31250000000) + Work.RHContract.RegionI.logLowQ (11117:ℚ) := by decide +kernel
  have hratR : ((((5494542120150439 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((343117750298657 : ℚ) / 31250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11117:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1347 : ((((10998400650933201 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11119 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11117 < q → q < 11119 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11119).mp (by decide +kernel))) hgap
  have hprev := thV_1346
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11119:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((10998400650933201 : ℚ) / 1000000000000) ≤ ((5494542120150439 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (11119:ℚ) := by decide +kernel
  have hratR : ((((10998400650933201 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5494542120150439 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11119:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1348 : ((((5503859070108657 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11131 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11119 < q → q < 11131 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11131).mp (by decide +kernel))) hgap
  have hprev := thV_1347
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11131:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5503859070108657 : ℚ) / 500000000000) ≤ ((10998400650933201 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (11131:ℚ) := by decide +kernel
  have hratR : ((((5503859070108657 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((10998400650933201 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11131:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1349 : ((((5508518622650351 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11149 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11131 < q → q < 11149 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11149).mp (by decide +kernel))) hgap
  have hprev := thV_1348
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11149:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5508518622650351 : ℚ) / 500000000000) ≤ ((5503859070108657 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (11149:ℚ) := by decide +kernel
  have hratR : ((((5508518622650351 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((5503859070108657 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11149:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1350 : ((((2756589311730877 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11159 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11149 < q → q < 11159 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11159).mp (by decide +kernel))) hgap
  have hprev := thV_1349
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11159:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2756589311730877 : ℚ) / 250000000000) ≤ ((5508518622650351 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (11159:ℚ) := by decide +kernel
  have hratR : ((((2756589311730877 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((5508518622650351 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11159:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1351 : ((((1379459678469723 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11161 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11159 < q → q < 11161 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11161).mp (by decide +kernel))) hgap
  have hprev := thV_1350
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11161:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1379459678469723 : ℚ) / 125000000000) ≤ ((2756589311730877 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (11161:ℚ) := by decide +kernel
  have hratR : ((((1379459678469723 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((2756589311730877 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11161:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1352 : ((((441799940166719 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11171 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11161 < q → q < 11171 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11171).mp (by decide +kernel))) hgap
  have hprev := thV_1351
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11171:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((441799940166719 : ℚ) / 40000000000) ≤ ((1379459678469723 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (11171:ℚ) := by decide +kernel
  have hratR : ((((441799940166719 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((1379459678469723 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11171:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1353 : ((((11054319759597143 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11173 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11171 < q → q < 11173 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11173).mp (by decide +kernel))) hgap
  have hprev := thV_1352
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11173:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11054319759597143 : ℚ) / 1000000000000) ≤ ((441799940166719 : ℚ) / 40000000000) + Work.RHContract.RegionI.logLowQ (11173:ℚ) := by decide +kernel
  have hratR : ((((11054319759597143 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((441799940166719 : ℚ) / 40000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11173:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1354 : ((((11063641372968149 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11177 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11173 < q → q < 11177 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11177).mp (by decide +kernel))) hgap
  have hprev := thV_1353
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11177:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11063641372968149 : ℚ) / 1000000000000) ≤ ((11054319759597143 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (11177:ℚ) := by decide +kernel
  have hratR : ((((11063641372968149 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((11054319759597143 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11177:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1355 : ((((11072964774129029 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11197 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11177 < q → q < 11197 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11197).mp (by decide +kernel))) hgap
  have hprev := thV_1354
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11197:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11072964774129029 : ℚ) / 1000000000000) ≤ ((11063641372968149 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (11197:ℚ) := by decide +kernel
  have hratR : ((((11072964774129029 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((11063641372968149 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11197:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1356 : ((((1108228960322411 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11213 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11197 < q → q < 11213 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11213).mp (by decide +kernel))) hgap
  have hprev := thV_1355
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11213:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1108228960322411 : ℚ) / 100000000000) ≤ ((11072964774129029 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (11213:ℚ) := by decide +kernel
  have hratR : ((((1108228960322411 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((11072964774129029 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11213:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1357 : ((((1386452093546531 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11239 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11213 < q → q < 11239 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11239).mp (by decide +kernel))) hgap
  have hprev := thV_1356
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11239:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1386452093546531 : ℚ) / 125000000000) ≤ ((1108228960322411 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (11239:ℚ) := by decide +kernel
  have hratR : ((((1386452093546531 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((1108228960322411 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11239:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1358 : ((((5550472124680309 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11243 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11239 < q → q < 11243 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11243).mp (by decide +kernel))) hgap
  have hprev := thV_1357
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11243:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5550472124680309 : ℚ) / 500000000000) ≤ ((1386452093546531 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (11243:ℚ) := by decide +kernel
  have hratR : ((((5550472124680309 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1386452093546531 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11243:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1359 : ((((11110272461649809 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11251 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11243 < q → q < 11251 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11251).mp (by decide +kernel))) hgap
  have hprev := thV_1358
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11251:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11110272461649809 : ℚ) / 1000000000000) ≤ ((5550472124680309 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (11251:ℚ) := by decide +kernel
  have hratR : ((((11110272461649809 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5550472124680309 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11251:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1360 : ((((347487537721337 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11257 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11251 < q → q < 11257 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11257).mp (by decide +kernel))) hgap
  have hprev := thV_1359
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11257:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((347487537721337 : ℚ) / 31250000000) ≤ ((11110272461649809 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (11257:ℚ) := by decide +kernel
  have hratR : ((((347487537721337 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((11110272461649809 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11257:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1361 : ((((11128930307787101 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11261 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11257 < q → q < 11261 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11261).mp (by decide +kernel))) hgap
  have hprev := thV_1360
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11261:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11128930307787101 : ℚ) / 1000000000000) ≤ ((347487537721337 : ℚ) / 31250000000) + Work.RHContract.RegionI.logLowQ (11261:ℚ) := by decide +kernel
  have hratR : ((((11128930307787101 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((347487537721337 : ℚ) / 31250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11261:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1362 : ((((5569130236774383 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11273 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11261 < q → q < 11273 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11273).mp (by decide +kernel))) hgap
  have hprev := thV_1361
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11273:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5569130236774383 : ℚ) / 500000000000) ≤ ((11128930307787101 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (11273:ℚ) := by decide +kernel
  have hratR : ((((5569130236774383 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((11128930307787101 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11273:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1363 : ((((5573795585707013 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11279 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11273 < q → q < 11279 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11279).mp (by decide +kernel))) hgap
  have hprev := thV_1362
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11279:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5573795585707013 : ℚ) / 500000000000) ≤ ((5569130236774383 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (11279:ℚ) := by decide +kernel
  have hratR : ((((5573795585707013 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((5569130236774383 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11279:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1364 : ((((5578461289155301 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11287 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11279 < q → q < 11287 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11287).mp (by decide +kernel))) hgap
  have hprev := thV_1363
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11287:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5578461289155301 : ℚ) / 500000000000) ≤ ((5573795585707013 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (11287:ℚ) := by decide +kernel
  have hratR : ((((5578461289155301 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((5573795585707013 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11287:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1365 : ((((11166255047812431 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11299 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11287 < q → q < 11299 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11299).mp (by decide +kernel))) hgap
  have hprev := thV_1364
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11299:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11166255047812431 : ℚ) / 1000000000000) ≤ ((5578461289155301 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (11299:ℚ) := by decide +kernel
  have hratR : ((((11166255047812431 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5578461289155301 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11299:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1366 : ((((11175588578791583 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11311 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11299 < q → q < 11311 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11311).mp (by decide +kernel))) hgap
  have hprev := thV_1365
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11311:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11175588578791583 : ℚ) / 1000000000000) ≤ ((11166255047812431 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (11311:ℚ) := by decide +kernel
  have hratR : ((((11175588578791583 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((11166255047812431 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11311:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1367 : ((((11184922640087169 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11317 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11311 < q → q < 11317 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11317).mp (by decide +kernel))) hgap
  have hprev := thV_1366
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11317:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11184922640087169 : ℚ) / 1000000000000) ≤ ((11175588578791583 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (11317:ℚ) := by decide +kernel
  have hratR : ((((11184922640087169 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((11175588578791583 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11317:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1368 : ((((11194257054770867 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11321 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11317 < q → q < 11321 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11321).mp (by decide +kernel))) hgap
  have hprev := thV_1367
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11321:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11194257054770867 : ℚ) / 1000000000000) ≤ ((11184922640087169 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (11321:ℚ) := by decide +kernel
  have hratR : ((((11194257054770867 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((11184922640087169 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11321:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1369 : ((((11203592175856361 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11329 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11321 < q → q < 11329 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11329).mp (by decide +kernel))) hgap
  have hprev := thV_1368
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11329:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11203592175856361 : ℚ) / 1000000000000) ≤ ((11194257054770867 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (11329:ℚ) := by decide +kernel
  have hratR : ((((11203592175856361 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((11194257054770867 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11329:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1370 : ((((11212929236977737 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11351 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11329 < q → q < 11351 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11351).mp (by decide +kernel))) hgap
  have hprev := thV_1369
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11351:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11212929236977737 : ℚ) / 1000000000000) ≤ ((11203592175856361 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (11351:ℚ) := by decide +kernel
  have hratR : ((((11212929236977737 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((11203592175856361 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11351:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1371 : ((((5611133237139761 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11353 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11351 < q → q < 11353 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11353).mp (by decide +kernel))) hgap
  have hprev := thV_1370
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11353:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5611133237139761 : ℚ) / 500000000000) ≤ ((11212929236977737 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (11353:ℚ) := by decide +kernel
  have hratR : ((((5611133237139761 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((11212929236977737 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11353:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1372 : ((((11231605119908271 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11369 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11353 < q → q < 11369 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11369).mp (by decide +kernel))) hgap
  have hprev := thV_1371
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11369:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11231605119908271 : ℚ) / 1000000000000) ≤ ((5611133237139761 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (11369:ℚ) := by decide +kernel
  have hratR : ((((11231605119908271 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5611133237139761 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11369:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1373 : ((((1405118124524777 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11383 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11369 < q → q < 11383 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11383).mp (by decide +kernel))) hgap
  have hprev := thV_1372
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11383:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1405118124524777 : ℚ) / 125000000000) ≤ ((11231605119908271 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (11383:ℚ) := by decide +kernel
  have hratR : ((((1405118124524777 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((11231605119908271 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11383:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1374 : ((((5625142875302767 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11393 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11383 < q → q < 11393 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11393).mp (by decide +kernel))) hgap
  have hprev := thV_1373
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11393:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5625142875302767 : ℚ) / 500000000000) ≤ ((1405118124524777 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (11393:ℚ) := by decide +kernel
  have hratR : ((((5625142875302767 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1405118124524777 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11393:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1375 : ((((11259627031513391 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11399 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11393 < q → q < 11399 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11399).mp (by decide +kernel))) hgap
  have hprev := thV_1374
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11399:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11259627031513391 : ℚ) / 1000000000000) ≤ ((5625142875302767 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (11399:ℚ) := by decide +kernel
  have hratR : ((((11259627031513391 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5625142875302767 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11399:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1376 : ((((5634484682295723 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11411 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11399 < q → q < 11411 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11411).mp (by decide +kernel))) hgap
  have hprev := thV_1375
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11411:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5634484682295723 : ℚ) / 500000000000) ≤ ((11259627031513391 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (11411:ℚ) := by decide +kernel
  have hratR : ((((5634484682295723 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((11259627031513391 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11411:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1377 : ((((56391563743669 : ℚ) / 5000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11423 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11411 < q → q < 11423 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11423).mp (by decide +kernel))) hgap
  have hprev := thV_1376
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11423:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((56391563743669 : ℚ) / 5000000000) ≤ ((5634484682295723 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (11423:ℚ) := by decide +kernel
  have hratR : ((((56391563743669 : ℚ) / 5000000000) : ℚ) : ℝ) ≤ ((((5634484682295723 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11423:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1378 : ((((11287657357723201 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11437 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11423 < q → q < 11437 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11437).mp (by decide +kernel))) hgap
  have hprev := thV_1377
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11437:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11287657357723201 : ℚ) / 1000000000000) ≤ ((56391563743669 : ℚ) / 5000000000) + Work.RHContract.RegionI.logLowQ (11437:ℚ) := by decide +kernel
  have hratR : ((((11287657357723201 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56391563743669 : ℚ) / 5000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11437:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1379 : ((((11297002491188139 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11443 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11437 < q → q < 11443 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11443).mp (by decide +kernel))) hgap
  have hprev := thV_1378
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11443:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11297002491188139 : ℚ) / 1000000000000) ≤ ((11287657357723201 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (11443:ℚ) := by decide +kernel
  have hratR : ((((11297002491188139 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((11287657357723201 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11443:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1380 : ((((5653173987075339 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11447 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11443 < q → q < 11447 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11447).mp (by decide +kernel))) hgap
  have hprev := thV_1379
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11447:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5653173987075339 : ℚ) / 500000000000) ≤ ((11297002491188139 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (11447:ℚ) := by decide +kernel
  have hratR : ((((5653173987075339 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((11297002491188139 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11447:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1381 : ((((11315695202771337 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11467 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11447 < q → q < 11467 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11467).mp (by decide +kernel))) hgap
  have hprev := thV_1380
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11467:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11315695202771337 : ℚ) / 1000000000000) ≤ ((5653173987075339 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (11467:ℚ) := by decide +kernel
  have hratR : ((((11315695202771337 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5653173987075339 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11467:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1382 : ((((5662521390079119 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11471 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11467 < q → q < 11471 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11471).mp (by decide +kernel))) hgap
  have hprev := thV_1381
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11471:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5662521390079119 : ℚ) / 500000000000) ≤ ((11315695202771337 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (11471:ℚ) := by decide +kernel
  have hratR : ((((5662521390079119 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((11315695202771337 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11471:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1383 : ((((5667195701557317 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11483 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11471 < q → q < 11483 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11483).mp (by decide +kernel))) hgap
  have hprev := thV_1382
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11483:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5667195701557317 : ℚ) / 500000000000) ≤ ((5662521390079119 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (11483:ℚ) := by decide +kernel
  have hratR : ((((5667195701557317 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((5662521390079119 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11483:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1384 : ((((2835935137111527 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11489 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11483 < q → q < 11489 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11489).mp (by decide +kernel))) hgap
  have hprev := thV_1383
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11489:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2835935137111527 : ℚ) / 250000000000) ≤ ((5667195701557317 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (11489:ℚ) := by decide +kernel
  have hratR : ((((2835935137111527 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((5667195701557317 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11489:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1385 : ((((5676544933920993 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11491 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11489 < q → q < 11491 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11491).mp (by decide +kernel))) hgap
  have hprev := thV_1384
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11491:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5676544933920993 : ℚ) / 500000000000) ≤ ((2835935137111527 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (11491:ℚ) := by decide +kernel
  have hratR : ((((5676544933920993 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((2835935137111527 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11491:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1386 : ((((142030496365617 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11497 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11491 < q → q < 11497 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11497).mp (by decide +kernel))) hgap
  have hprev := thV_1385
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11497:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((142030496365617 : ℚ) / 12500000000) ≤ ((5676544933920993 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (11497:ℚ) := by decide +kernel
  have hratR : ((((142030496365617 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ ((((5676544933920993 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11497:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1387 : ((((2842947518098969 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11503 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11497 < q → q < 11503 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11503).mp (by decide +kernel))) hgap
  have hprev := thV_1386
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11503:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2842947518098969 : ℚ) / 250000000000) ≤ ((142030496365617 : ℚ) / 12500000000) + Work.RHContract.RegionI.logLowQ (11503:ℚ) := by decide +kernel
  have hratR : ((((2842947518098969 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((142030496365617 : ℚ) / 12500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11503:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1388 : ((((11381141825517423 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11519 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11503 < q → q < 11519 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11519).mp (by decide +kernel))) hgap
  have hprev := thV_1387
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11519:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11381141825517423 : ℚ) / 1000000000000) ≤ ((2842947518098969 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (11519:ℚ) := by decide +kernel
  have hratR : ((((11381141825517423 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2842947518098969 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11519:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1389 : ((((2847623568225661 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11527 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11519 < q → q < 11527 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11527).mp (by decide +kernel))) hgap
  have hprev := thV_1388
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11527:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2847623568225661 : ℚ) / 250000000000) ≤ ((11381141825517423 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (11527:ℚ) := by decide +kernel
  have hratR : ((((2847623568225661 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((11381141825517423 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11527:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1390 : ((((11399848627031379 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11549 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11527 < q → q < 11549 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11549).mp (by decide +kernel))) hgap
  have hprev := thV_1389
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11549:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11399848627031379 : ℚ) / 1000000000000) ≤ ((2847623568225661 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (11549:ℚ) := by decide +kernel
  have hratR : ((((11399848627031379 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2847623568225661 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11549:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1391 : ((((356537598572509 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11551 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11549 < q → q < 11551 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11551).mp (by decide +kernel))) hgap
  have hprev := thV_1390
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11551:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((356537598572509 : ℚ) / 31250000000) ≤ ((11399848627031379 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (11551:ℚ) := by decide +kernel
  have hratR : ((((356537598572509 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((11399848627031379 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11551:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1392 : ((((285464002567713 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11579 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11551 < q → q < 11579 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11579).mp (by decide +kernel))) hgap
  have hprev := thV_1391
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11579:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((285464002567713 : ℚ) / 25000000000) ≤ ((356537598572509 : ℚ) / 31250000000) + Work.RHContract.RegionI.logLowQ (11579:ℚ) := by decide +kernel
  have hratR : ((((285464002567713 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((356537598572509 : ℚ) / 31250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11579:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1393 : ((((11427917741764137 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11587 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11579 < q → q < 11587 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11587).mp (by decide +kernel))) hgap
  have hprev := thV_1392
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11587:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11427917741764137 : ℚ) / 1000000000000) ≤ ((285464002567713 : ℚ) / 25000000000) + Work.RHContract.RegionI.logLowQ (11587:ℚ) := by decide +kernel
  have hratR : ((((11427917741764137 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((285464002567713 : ℚ) / 25000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11587:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1394 : ((((2859318974626857 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11593 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11587 < q → q < 11593 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11593).mp (by decide +kernel))) hgap
  have hprev := thV_1393
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11593:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2859318974626857 : ℚ) / 250000000000) ≤ ((11427917741764137 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (11593:ℚ) := by decide +kernel
  have hratR : ((((2859318974626857 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((11427917741764137 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11593:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1395 : ((((2289326880045401 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11597 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11593 < q → q < 11597 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11597).mp (by decide +kernel))) hgap
  have hprev := thV_1394
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11597:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2289326880045401 : ℚ) / 200000000000) ≤ ((2859318974626857 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (11597:ℚ) := by decide +kernel
  have hratR : ((((2289326880045401 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((2859318974626857 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11597:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1396 : ((((11455994625045139 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11617 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11597 < q → q < 11617 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11617).mp (by decide +kernel))) hgap
  have hprev := thV_1395
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11617:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11455994625045139 : ℚ) / 1000000000000) ≤ ((2289326880045401 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (11617:ℚ) := by decide +kernel
  have hratR : ((((11455994625045139 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2289326880045401 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11617:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1397 : ((((5732677597063491 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11621 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11617 < q → q < 11621 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11621).mp (by decide +kernel))) hgap
  have hprev := thV_1396
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11621:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5732677597063491 : ℚ) / 500000000000) ≤ ((11455994625045139 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (11621:ℚ) := by decide +kernel
  have hratR : ((((5732677597063491 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((11455994625045139 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11621:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1398 : ((((11474716795289419 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11633 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11621 < q → q < 11633 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11633).mp (by decide +kernel))) hgap
  have hprev := thV_1397
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11633:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11474716795289419 : ℚ) / 1000000000000) ≤ ((5732677597063491 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (11633:ℚ) := by decide +kernel
  have hratR : ((((11474716795289419 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5732677597063491 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11633:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1399 : ((((11484080457422959 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11657 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11633 < q → q < 11657 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11657).mp (by decide +kernel))) hgap
  have hprev := thV_1398
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11657:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11484080457422959 : ℚ) / 1000000000000) ≤ ((11474716795289419 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (11657:ℚ) := by decide +kernel
  have hratR : ((((11484080457422959 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((11474716795289419 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11657:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1400 : ((((2298689166758731 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11677 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11657 < q → q < 11677 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11677).mp (by decide +kernel))) hgap
  have hprev := thV_1399
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11677:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2298689166758731 : ℚ) / 200000000000) ≤ ((11484080457422959 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (11677:ℚ) := by decide +kernel
  have hratR : ((((2298689166758731 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((11484080457422959 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11677:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1401 : ((((11502811552659431 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11681 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11677 < q → q < 11681 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11681).mp (by decide +kernel))) hgap
  have hprev := thV_1400
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11681:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11502811552659431 : ℚ) / 1000000000000) ≤ ((2298689166758731 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (11681:ℚ) := by decide +kernel
  have hratR : ((((11502811552659431 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2298689166758731 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11681:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1402 : ((((11512177956163659 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11689 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11681 < q → q < 11689 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11689).mp (by decide +kernel))) hgap
  have hprev := thV_1401
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11689:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11512177956163659 : ℚ) / 1000000000000) ≤ ((11502811552659431 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (11689:ℚ) := by decide +kernel
  have hratR : ((((11512177956163659 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((11502811552659431 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11689:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1403 : ((((11521545214807327 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11699 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11689 < q → q < 11699 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11699).mp (by decide +kernel))) hgap
  have hprev := thV_1402
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11699:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11521545214807327 : ℚ) / 1000000000000) ≤ ((11512177956163659 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (11699:ℚ) := by decide +kernel
  have hratR : ((((11521545214807327 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((11512177956163659 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11699:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1404 : ((((5765456322195583 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11701 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11699 < q → q < 11701 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11701).mp (by decide +kernel))) hgap
  have hprev := thV_1403
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11701:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5765456322195583 : ℚ) / 500000000000) ≤ ((11521545214807327 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (11701:ℚ) := by decide +kernel
  have hratR : ((((5765456322195583 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((11521545214807327 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11701:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1405 : ((((5770140720222727 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11717 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11701 < q → q < 11717 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11717).mp (by decide +kernel))) hgap
  have hprev := thV_1404
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11717:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5770140720222727 : ℚ) / 500000000000) ≤ ((5765456322195583 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (11717:ℚ) := by decide +kernel
  have hratR : ((((5770140720222727 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((5765456322195583 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11717:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1406 : ((((11549650407177333 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11719 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11717 < q → q < 11719 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11719).mp (by decide +kernel))) hgap
  have hprev := thV_1405
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11719:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11549650407177333 : ℚ) / 1000000000000) ≤ ((5770140720222727 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (11719:ℚ) := by decide +kernel
  have hratR : ((((11549650407177333 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5770140720222727 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11719:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1407 : ((((11559020397363459 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11731 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11719 < q → q < 11731 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11731).mp (by decide +kernel))) hgap
  have hprev := thV_1406
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11731:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11559020397363459 : ℚ) / 1000000000000) ≤ ((11549650407177333 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (11731:ℚ) := by decide +kernel
  have hratR : ((((11559020397363459 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((11549650407177333 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11731:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1408 : ((((2892097852489361 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11743 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11731 < q → q < 11743 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11743).mp (by decide +kernel))) hgap
  have hprev := thV_1407
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11743:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2892097852489361 : ℚ) / 250000000000) ≤ ((11559020397363459 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (11743:ℚ) := by decide +kernel
  have hratR : ((((2892097852489361 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((11559020397363459 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11743:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1409 : ((((5788882656854953 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11777 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11743 < q → q < 11777 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11777).mp (by decide +kernel))) hgap
  have hprev := thV_1408
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11777:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5788882656854953 : ℚ) / 500000000000) ≤ ((2892097852489361 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (11777:ℚ) := by decide +kernel
  have hratR : ((((5788882656854953 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((2892097852489361 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11777:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1410 : ((((2317427877454097 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11779 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11777 < q → q < 11779 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11779).mp (by decide +kernel))) hgap
  have hprev := thV_1409
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11779:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2317427877454097 : ℚ) / 200000000000) ≤ ((5788882656854953 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (11779:ℚ) := by decide +kernel
  have hratR : ((((2317427877454097 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((5788882656854953 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11779:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1411 : ((((11596513800360819 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11783 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11779 < q → q < 11783 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11783).mp (by decide +kernel))) hgap
  have hprev := thV_1410
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11783:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11596513800360819 : ℚ) / 1000000000000) ≤ ((2317427877454097 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (11783:ℚ) := by decide +kernel
  have hratR : ((((11596513800360819 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2317427877454097 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11783:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1412 : ((((11605888722529731 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11789 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11783 < q → q < 11789 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11789).mp (by decide +kernel))) hgap
  have hprev := thV_1411
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11789:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11605888722529731 : ℚ) / 1000000000000) ≤ ((11596513800360819 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (11789:ℚ) := by decide +kernel
  have hratR : ((((11605888722529731 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((11596513800360819 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11789:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1413 : ((((11615264662078977 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11801 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11789 < q → q < 11801 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11801).mp (by decide +kernel))) hgap
  have hprev := thV_1412
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11801:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11615264662078977 : ℚ) / 1000000000000) ≤ ((11605888722529731 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (11801:ℚ) := by decide +kernel
  have hratR : ((((11615264662078977 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((11605888722529731 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11801:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1414 : ((((1453080138741313 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11807 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11801 < q → q < 11807 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11807).mp (by decide +kernel))) hgap
  have hprev := thV_1413
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11807:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1453080138741313 : ℚ) / 125000000000) ≤ ((11615264662078977 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (11807:ℚ) := by decide +kernel
  have hratR : ((((1453080138741313 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((11615264662078977 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11807:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1415 : ((((11634018065826073 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11813 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11807 < q → q < 11813 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11813).mp (by decide +kernel))) hgap
  have hprev := thV_1414
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11813:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11634018065826073 : ℚ) / 1000000000000) ≤ ((1453080138741313 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (11813:ℚ) := by decide +kernel
  have hratR : ((((11634018065826073 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1453080138741313 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11813:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1416 : ((((2910848924678111 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11821 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11813 < q → q < 11821 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11821).mp (by decide +kernel))) hgap
  have hprev := thV_1415
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11821:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2910848924678111 : ℚ) / 250000000000) ≤ ((11634018065826073 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (11821:ℚ) := by decide +kernel
  have hratR : ((((2910848924678111 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((11634018065826073 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11821:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1417 : ((((2330554767808263 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11827 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11821 < q → q < 11827 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11827).mp (by decide +kernel))) hgap
  have hprev := thV_1416
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11827:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2330554767808263 : ℚ) / 200000000000) ≤ ((2910848924678111 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (11827:ℚ) := by decide +kernel
  have hratR : ((((2330554767808263 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((2910848924678111 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11827:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1418 : ((((11662152317522189 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11831 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11827 < q → q < 11831 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11831).mp (by decide +kernel))) hgap
  have hprev := thV_1417
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11831:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11662152317522189 : ℚ) / 1000000000000) ≤ ((2330554767808263 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (11831:ℚ) := by decide +kernel
  have hratR : ((((11662152317522189 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2330554767808263 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11831:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1419 : ((((5835765482518097 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11833 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11831 < q → q < 11833 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11833).mp (by decide +kernel))) hgap
  have hprev := thV_1418
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11833:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5835765482518097 : ℚ) / 500000000000) ≤ ((11662152317522189 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (11833:ℚ) := by decide +kernel
  have hratR : ((((5835765482518097 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((11662152317522189 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11833:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1420 : ((((5840455059739113 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11839 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11833 < q → q < 11839 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11839).mp (by decide +kernel))) hgap
  have hprev := thV_1419
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11839:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5840455059739113 : ℚ) / 500000000000) ≤ ((5835765482518097 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (11839:ℚ) := by decide +kernel
  have hratR : ((((5840455059739113 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((5835765482518097 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11839:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1421 : ((((11690291299066507 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11863 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11839 < q → q < 11863 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11863).mp (by decide +kernel))) hgap
  have hprev := thV_1420
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11863:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11690291299066507 : ℚ) / 1000000000000) ≤ ((5840455059739113 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (11863:ℚ) := by decide +kernel
  have hratR : ((((11690291299066507 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5840455059739113 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11863:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1422 : ((((1462459101972599 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11867 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11863 < q → q < 11867 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11867).mp (by decide +kernel))) hgap
  have hprev := thV_1421
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11867:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1462459101972599 : ℚ) / 125000000000) ≤ ((11690291299066507 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (11867:ℚ) := by decide +kernel
  have hratR : ((((1462459101972599 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((11690291299066507 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11867:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1423 : ((((11709056016422393 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11887 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11867 < q → q < 11887 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11887).mp (by decide +kernel))) hgap
  have hprev := thV_1422
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11887:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11709056016422393 : ℚ) / 1000000000000) ≤ ((1462459101972599 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (11887:ℚ) := by decide +kernel
  have hratR : ((((11709056016422393 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1462459101972599 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11887:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1424 : ((((1171844005796549 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11897 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11887 < q → q < 11897 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11897).mp (by decide +kernel))) hgap
  have hprev := thV_1423
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11897:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1171844005796549 : ℚ) / 100000000000) ≤ ((11709056016422393 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (11897:ℚ) := by decide +kernel
  have hratR : ((((1171844005796549 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((11709056016422393 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11897:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1425 : ((((5863912301855139 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11903 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11897 < q → q < 11903 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11903).mp (by decide +kernel))) hgap
  have hprev := thV_1424
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11903:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5863912301855139 : ℚ) / 500000000000) ≤ ((1171844005796549 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (11903:ℚ) := by decide +kernel
  have hratR : ((((5863912301855139 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1171844005796549 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11903:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1426 : ((((5868604826701333 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11909 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11903 < q → q < 11909 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11909).mp (by decide +kernel))) hgap
  have hprev := thV_1425
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11909:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5868604826701333 : ℚ) / 500000000000) ≤ ((5863912301855139 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (11909:ℚ) := by decide +kernel
  have hratR : ((((5868604826701333 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((5863912301855139 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11909:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1427 : ((((2936648969496523 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11923 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11909 < q → q < 11923 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11923).mp (by decide +kernel))) hgap
  have hprev := thV_1426
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11923:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2936648969496523 : ℚ) / 250000000000) ≤ ((5868604826701333 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (11923:ℚ) := by decide +kernel
  have hratR : ((((2936648969496523 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((5868604826701333 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11923:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1428 : ((((11755982437999291 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11927 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11923 < q → q < 11927 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11927).mp (by decide +kernel))) hgap
  have hprev := thV_1427
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11927:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11755982437999291 : ℚ) / 1000000000000) ≤ ((2936648969496523 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (11927:ℚ) := by decide +kernel
  have hratR : ((((11755982437999291 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2936648969496523 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11927:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1429 : ((((11765369500946281 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11933 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11927 < q → q < 11933 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11933).mp (by decide +kernel))) hgap
  have hprev := thV_1428
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11933:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11765369500946281 : ℚ) / 1000000000000) ≤ ((11755982437999291 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (11933:ℚ) := by decide +kernel
  have hratR : ((((11765369500946281 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((11755982437999291 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11933:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1430 : ((((11774757066574247 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11939 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11933 < q → q < 11939 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11939).mp (by decide +kernel))) hgap
  have hprev := thV_1429
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11939:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11774757066574247 : ℚ) / 1000000000000) ≤ ((11765369500946281 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (11939:ℚ) := by decide +kernel
  have hratR : ((((11774757066574247 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((11765369500946281 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11939:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1431 : ((((11784144799706401 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11941 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11939 < q → q < 11941 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11941).mp (by decide +kernel))) hgap
  have hprev := thV_1430
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11941:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11784144799706401 : ℚ) / 1000000000000) ≤ ((11774757066574247 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (11941:ℚ) := by decide +kernel
  have hratR : ((((11784144799706401 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((11774757066574247 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11941:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1432 : ((((11793533537274899 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11953 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11941 < q → q < 11953 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11953).mp (by decide +kernel))) hgap
  have hprev := thV_1431
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11953:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11793533537274899 : ℚ) / 1000000000000) ≤ ((11784144799706401 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (11953:ℚ) := by decide +kernel
  have hratR : ((((11793533537274899 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((11784144799706401 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11953:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1433 : ((((368841336771359 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11959 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11953 < q → q < 11959 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11959).mp (by decide +kernel))) hgap
  have hprev := thV_1432
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11959:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((368841336771359 : ℚ) / 31250000000) ≤ ((11793533537274899 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (11959:ℚ) := by decide +kernel
  have hratR : ((((368841336771359 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((11793533537274899 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11959:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1434 : ((((5906156425966491 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11969 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11959 < q → q < 11969 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11969).mp (by decide +kernel))) hgap
  have hprev := thV_1433
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11969:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5906156425966491 : ℚ) / 500000000000) ≤ ((368841336771359 : ℚ) / 31250000000) + Work.RHContract.RegionI.logLowQ (11969:ℚ) := by decide +kernel
  have hratR : ((((5906156425966491 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((368841336771359 : ℚ) / 31250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11969:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1435 : ((((5910851547133427 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11971 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11969 < q → q < 11971 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11971).mp (by decide +kernel))) hgap
  have hprev := thV_1434
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11971:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5910851547133427 : ℚ) / 500000000000) ≤ ((5906156425966491 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (11971:ℚ) := by decide +kernel
  have hratR : ((((5910851547133427 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((5906156425966491 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11971:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1436 : ((((5915547085802057 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11981 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11971 < q → q < 11981 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11981).mp (by decide +kernel))) hgap
  have hprev := thV_1435
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11981:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5915547085802057 : ℚ) / 500000000000) ≤ ((5910851547133427 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (11981:ℚ) := by decide +kernel
  have hratR : ((((5915547085802057 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((5910851547133427 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11981:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1437 : ((((11840485749608941 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((11987 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11981 < q → q < 11987 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11987).mp (by decide +kernel))) hgap
  have hprev := thV_1436
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (11987:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11840485749608941 : ℚ) / 1000000000000) ≤ ((5915547085802057 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (11987:ℚ) := by decide +kernel
  have hratR : ((((11840485749608941 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5915547085802057 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (11987:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1438 : ((((1481234874337199 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12007 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 11987 < q → q < 12007 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12007).mp (by decide +kernel))) hgap
  have hprev := thV_1437
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12007:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1481234874337199 : ℚ) / 125000000000) ≤ ((11840485749608941 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (12007:ℚ) := by decide +kernel
  have hratR : ((((1481234874337199 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((11840485749608941 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12007:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1439 : ((((11859272572869767 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12011 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12007 < q → q < 12011 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12011).mp (by decide +kernel))) hgap
  have hprev := thV_1438
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12011:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11859272572869767 : ℚ) / 1000000000000) ≤ ((1481234874337199 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (12011:ℚ) := by decide +kernel
  have hratR : ((((11859272572869767 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1481234874337199 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12011:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1440 : ((((11868668313384767 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12037 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12011 < q → q < 12037 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12037).mp (by decide +kernel))) hgap
  have hprev := thV_1439
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12037:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11868668313384767 : ℚ) / 1000000000000) ≤ ((11859272572869767 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (12037:ℚ) := by decide +kernel
  have hratR : ((((11868668313384767 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((11859272572869767 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12037:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1441 : ((((11878064386153279 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12041 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12037 < q → q < 12041 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12041).mp (by decide +kernel))) hgap
  have hprev := thV_1440
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12041:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11878064386153279 : ℚ) / 1000000000000) ≤ ((11868668313384767 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (12041:ℚ) := by decide +kernel
  have hratR : ((((11878064386153279 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((11868668313384767 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12041:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1442 : ((((297186515625179 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12043 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12041 < q → q < 12043 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12043).mp (by decide +kernel))) hgap
  have hprev := thV_1441
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12043:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((297186515625179 : ℚ) / 25000000000) ≤ ((11878064386153279 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (12043:ℚ) := by decide +kernel
  have hratR : ((((297186515625179 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((11878064386153279 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12043:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1443 : ((((11896857361951703 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12049 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12043 < q → q < 12049 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12049).mp (by decide +kernel))) hgap
  have hprev := thV_1442
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12049:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11896857361951703 : ℚ) / 1000000000000) ≤ ((297186515625179 : ℚ) / 25000000000) + Work.RHContract.RegionI.logLowQ (12049:ℚ) := by decide +kernel
  have hratR : ((((11896857361951703 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((297186515625179 : ℚ) / 25000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12049:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1444 : ((((372070497597157 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12071 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12049 < q → q < 12071 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12071).mp (by decide +kernel))) hgap
  have hprev := thV_1443
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12071:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((372070497597157 : ℚ) / 31250000000) ≤ ((11896857361951703 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (12071:ℚ) := by decide +kernel
  have hratR : ((((372070497597157 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((11896857361951703 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12071:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1445 : ((((11915654649938977 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12073 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12071 < q → q < 12073 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12073).mp (by decide +kernel))) hgap
  have hprev := thV_1444
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12073:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11915654649938977 : ℚ) / 1000000000000) ≤ ((372070497597157 : ℚ) / 31250000000) + Work.RHContract.RegionI.logLowQ (12073:ℚ) := by decide +kernel
  have hratR : ((((11915654649938977 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((372070497597157 : ℚ) / 31250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12073:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1446 : ((((11925055362702557 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12097 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12073 < q → q < 12097 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12097).mp (by decide +kernel))) hgap
  have hprev := thV_1445
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12097:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11925055362702557 : ℚ) / 1000000000000) ≤ ((11915654649938977 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (12097:ℚ) := by decide +kernel
  have hratR : ((((11925055362702557 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((11915654649938977 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12097:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1447 : ((((477378256242879 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12101 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12097 < q → q < 12101 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12101).mp (by decide +kernel))) hgap
  have hprev := thV_1446
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12101:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((477378256242879 : ℚ) / 40000000000) ≤ ((11925055362702557 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (12101:ℚ) := by decide +kernel
  have hratR : ((((477378256242879 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((11925055362702557 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12101:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1448 : ((((11943857945145303 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12107 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12101 < q → q < 12107 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12107).mp (by decide +kernel))) hgap
  have hprev := thV_1447
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12107:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11943857945145303 : ℚ) / 1000000000000) ≤ ((477378256242879 : ℚ) / 40000000000) + Work.RHContract.RegionI.logLowQ (12107:ℚ) := by decide +kernel
  have hratR : ((((11943857945145303 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((477378256242879 : ℚ) / 40000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12107:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1449 : ((((5976629824699339 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12109 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12107 < q → q < 12109 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12109).mp (by decide +kernel))) hgap
  have hprev := thV_1448
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12109:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5976629824699339 : ℚ) / 500000000000) ≤ ((11943857945145303 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (12109:ℚ) := by decide +kernel
  have hratR : ((((5976629824699339 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((11943857945145303 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12109:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1450 : ((((2392532336786063 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12113 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12109 < q → q < 12113 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12113).mp (by decide +kernel))) hgap
  have hprev := thV_1449
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12113:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2392532336786063 : ℚ) / 200000000000) ≤ ((5976629824699339 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (12113:ℚ) := by decide +kernel
  have hratR : ((((2392532336786063 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((5976629824699339 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12113:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1451 : ((((1496508026709363 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12119 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12113 < q → q < 12119 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12119).mp (by decide +kernel))) hgap
  have hprev := thV_1450
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12119:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1496508026709363 : ℚ) / 125000000000) ≤ ((2392532336786063 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (12119:ℚ) := by decide +kernel
  have hratR : ((((1496508026709363 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((2392532336786063 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12119:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1452 : ((((5990734360911289 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12143 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12119 < q → q < 12143 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12143).mp (by decide +kernel))) hgap
  have hprev := thV_1451
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12143:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((5990734360911289 : ℚ) / 500000000000) ≤ ((1496508026709363 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (12143:ℚ) := by decide +kernel
  have hratR : ((((5990734360911289 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1496508026709363 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12143:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1453 : ((((11990873723960053 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12149 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12143 < q → q < 12149 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12149).mp (by decide +kernel))) hgap
  have hprev := thV_1452
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12149:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((11990873723960053 : ℚ) / 1000000000000) ≤ ((5990734360911289 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (12149:ℚ) := by decide +kernel
  have hratR : ((((11990873723960053 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5990734360911289 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12149:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1454 : ((((12000279384371229 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12157 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12149 < q → q < 12157 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12157).mp (by decide +kernel))) hgap
  have hprev := thV_1453
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12157:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12000279384371229 : ℚ) / 1000000000000) ≤ ((11990873723960053 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (12157:ℚ) := by decide +kernel
  have hratR : ((((12000279384371229 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((11990873723960053 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12157:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1455 : ((((1200968537375683 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12161 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12157 < q → q < 12161 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12161).mp (by decide +kernel))) hgap
  have hprev := thV_1454
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12161:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1200968537375683 : ℚ) / 100000000000) ≤ ((12000279384371229 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (12161:ℚ) := by decide +kernel
  have hratR : ((((1200968537375683 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((12000279384371229 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12161:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1456 : ((((12019091527589069 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12163 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12161 < q → q < 12163 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12163).mp (by decide +kernel))) hgap
  have hprev := thV_1455
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12163:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12019091527589069 : ℚ) / 1000000000000) ≤ ((1200968537375683 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (12163:ℚ) := by decide +kernel
  have hratR : ((((12019091527589069 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1200968537375683 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12163:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1457 : ((((3007125118221133 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12197 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12163 < q → q < 12197 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12197).mp (by decide +kernel))) hgap
  have hprev := thV_1456
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12197:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3007125118221133 : ℚ) / 250000000000) ≤ ((12019091527589069 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (12197:ℚ) := by decide +kernel
  have hratR : ((((3007125118221133 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((12019091527589069 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12197:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1458 : ((((3009477477495821 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12203 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12197 < q → q < 12203 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12203).mp (by decide +kernel))) hgap
  have hprev := thV_1457
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12203:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3009477477495821 : ℚ) / 250000000000) ≤ ((3007125118221133 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (12203:ℚ) := by decide +kernel
  have hratR : ((((3009477477495821 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((3007125118221133 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12203:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1459 : ((((12047320002443737 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12211 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12203 < q → q < 12211 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12211).mp (by decide +kernel))) hgap
  have hprev := thV_1458
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12211:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12047320002443737 : ℚ) / 1000000000000) ≤ ((3009477477495821 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (12211:ℚ) := by decide +kernel
  have hratR : ((((12047320002443737 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3009477477495821 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12211:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1460 : ((((12056731404340501 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12227 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12211 < q → q < 12227 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12227).mp (by decide +kernel))) hgap
  have hprev := thV_1459
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12227:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12056731404340501 : ℚ) / 1000000000000) ≤ ((12047320002443737 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (12227:ℚ) := by decide +kernel
  have hratR : ((((12056731404340501 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((12047320002443737 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12227:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1461 : ((((1508267973398813 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12239 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12227 < q → q < 12239 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12239).mp (by decide +kernel))) hgap
  have hprev := thV_1460
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12239:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1508267973398813 : ℚ) / 125000000000) ≤ ((12056731404340501 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (12239:ℚ) := by decide +kernel
  have hratR : ((((1508267973398813 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((12056731404340501 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12239:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1462 : ((((15094445416799 : ℚ) / 1250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12241 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12239 < q → q < 12241 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12241).mp (by decide +kernel))) hgap
  have hprev := thV_1461
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12241:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((15094445416799 : ℚ) / 1250000000) ≤ ((1508267973398813 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (12241:ℚ) := by decide +kernel
  have hratR : ((((15094445416799 : ℚ) / 1250000000) : ℚ) : ℝ) ≤ ((((1508267973398813 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12241:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1463 : ((((6042484848140557 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12251 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12241 < q → q < 12251 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12251).mp (by decide +kernel))) hgap
  have hprev := thV_1462
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12251:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6042484848140557 : ℚ) / 500000000000) ≤ ((15094445416799 : ℚ) / 1250000000) + Work.RHContract.RegionI.logLowQ (12251:ℚ) := by decide +kernel
  have hratR : ((((6042484848140557 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((15094445416799 : ℚ) / 1250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12251:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1464 : ((((3023595805590421 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12253 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12251 < q → q < 12253 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12253).mp (by decide +kernel))) hgap
  have hprev := thV_1463
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12253:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3023595805590421 : ℚ) / 250000000000) ≤ ((6042484848140557 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (12253:ℚ) := by decide +kernel
  have hratR : ((((3023595805590421 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((6042484848140557 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12253:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1465 : ((((6051898782118033 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12263 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12253 < q → q < 12263 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12263).mp (by decide +kernel))) hgap
  have hprev := thV_1464
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12263:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6051898782118033 : ℚ) / 500000000000) ≤ ((3023595805590421 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (12263:ℚ) := by decide +kernel
  have hratR : ((((6051898782118033 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((3023595805590421 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12263:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1466 : ((((12113212395267477 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12269 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12263 < q → q < 12269 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12269).mp (by decide +kernel))) hgap
  have hprev := thV_1465
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12269:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12113212395267477 : ℚ) / 1000000000000) ≤ ((6051898782118033 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (12269:ℚ) := by decide +kernel
  have hratR : ((((12113212395267477 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((6051898782118033 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12269:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1467 : ((((6061313939068139 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12277 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12269 < q → q < 12277 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12277).mp (by decide +kernel))) hgap
  have hprev := thV_1466
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12277:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6061313939068139 : ℚ) / 500000000000) ≤ ((12113212395267477 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (12277:ℚ) := by decide +kernel
  have hratR : ((((6061313939068139 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((12113212395267477 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12277:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1468 : ((((12132043686764509 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12281 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12277 < q → q < 12281 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12281).mp (by decide +kernel))) hgap
  have hprev := thV_1467
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12281:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12132043686764509 : ℚ) / 1000000000000) ≤ ((6061313939068139 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (12281:ℚ) := by decide +kernel
  have hratR : ((((12132043686764509 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((6061313939068139 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12281:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1469 : ((((6070730073296707 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12289 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12281 < q → q < 12289 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12289).mp (by decide +kernel))) hgap
  have hprev := thV_1468
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12289:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6070730073296707 : ℚ) / 500000000000) ≤ ((12132043686764509 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (12289:ℚ) := by decide +kernel
  have hratR : ((((6070730073296707 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((12132043686764509 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12289:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1470 : ((((12150877582428903 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12301 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12289 < q → q < 12301 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12301).mp (by decide +kernel))) hgap
  have hprev := thV_1469
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12301:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12150877582428903 : ℚ) / 1000000000000) ≤ ((6070730073296707 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (12301:ℚ) := by decide +kernel
  have hratR : ((((12150877582428903 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((6070730073296707 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12301:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1471 : ((((12160296805139461 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12323 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12301 < q → q < 12323 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12323).mp (by decide +kernel))) hgap
  have hprev := thV_1470
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12323:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12160296805139461 : ℚ) / 1000000000000) ≤ ((12150877582428903 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (12323:ℚ) := by decide +kernel
  have hratR : ((((12160296805139461 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((12150877582428903 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12323:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1472 : ((((243394330292519 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12329 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12323 < q → q < 12329 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12329).mp (by decide +kernel))) hgap
  have hprev := thV_1471
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12329:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((243394330292519 : ℚ) / 20000000000) ≤ ((12160296805139461 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (12329:ℚ) := by decide +kernel
  have hratR : ((((243394330292519 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ ((((12160296805139461 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12329:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1473 : ((((6089568679501157 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12343 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12329 < q → q < 12343 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12343).mp (by decide +kernel))) hgap
  have hprev := thV_1472
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12343:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6089568679501157 : ℚ) / 500000000000) ≤ ((243394330292519 : ℚ) / 20000000000) + Work.RHContract.RegionI.logLowQ (12343:ℚ) := by decide +kernel
  have hratR : ((((6089568679501157 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((243394330292519 : ℚ) / 20000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12343:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1474 : ((((6094279263698251 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12347 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12343 < q → q < 12347 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12347).mp (by decide +kernel))) hgap
  have hprev := thV_1473
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12347:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6094279263698251 : ℚ) / 500000000000) ≤ ((6089568679501157 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (12347:ℚ) := by decide +kernel
  have hratR : ((((6094279263698251 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((6089568679501157 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12347:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1475 : ((((1524747724918917 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12373 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12347 < q → q < 12373 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12373).mp (by decide +kernel))) hgap
  have hprev := thV_1474
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12373:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1524747724918917 : ℚ) / 125000000000) ≤ ((6094279263698251 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (12373:ℚ) := by decide +kernel
  have hratR : ((((1524747724918917 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((6094279263698251 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12373:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1476 : ((((2980323582651 : ℚ) / 244140625) : ℚ) : ℝ) ≤ Chebyshev.theta ((12377 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12373 < q → q < 12377 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12377).mp (by decide +kernel))) hgap
  have hprev := thV_1475
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12377:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2980323582651 : ℚ) / 244140625) ≤ ((1524747724918917 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (12377:ℚ) := by decide +kernel
  have hratR : ((((2980323582651 : ℚ) / 244140625) : ℚ) : ℝ) ≤ ((((1524747724918917 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12377:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1477 : ((((1527103643912831 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12379 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12377 < q → q < 12379 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12379).mp (by decide +kernel))) hgap
  have hprev := thV_1476
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12379:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1527103643912831 : ℚ) / 125000000000) ≤ ((2980323582651 : ℚ) / 244140625) + Work.RHContract.RegionI.logLowQ (12379:ℚ) := by decide +kernel
  have hratR : ((((1527103643912831 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((2980323582651 : ℚ) / 244140625) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12379:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1478 : ((((2445250775396177 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12391 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12379 < q → q < 12391 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12391).mp (by decide +kernel))) hgap
  have hprev := thV_1477
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12391:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2445250775396177 : ℚ) / 200000000000) ≤ ((1527103643912831 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (12391:ℚ) := by decide +kernel
  have hratR : ((((2445250775396177 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((1527103643912831 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12391:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1479 : ((((95591245385711 : ℚ) / 7812500000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12401 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12391 < q → q < 12401 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12401).mp (by decide +kernel))) hgap
  have hprev := thV_1478
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12401:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((95591245385711 : ℚ) / 7812500000) ≤ ((2445250775396177 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (12401:ℚ) := by decide +kernel
  have hratR : ((((95591245385711 : ℚ) / 7812500000) : ℚ) : ℝ) ≤ ((((2445250775396177 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12401:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1480 : ((((12245105586662403 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12409 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12401 < q → q < 12409 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12409).mp (by decide +kernel))) hgap
  have hprev := thV_1479
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12409:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12245105586662403 : ℚ) / 1000000000000) ≤ ((95591245385711 : ℚ) / 7812500000) + Work.RHContract.RegionI.logLowQ (12409:ℚ) := by decide +kernel
  have hratR : ((((12245105586662403 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((95591245385711 : ℚ) / 7812500000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12409:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1481 : ((((12254532086248539 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12413 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12409 < q → q < 12413 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12413).mp (by decide +kernel))) hgap
  have hprev := thV_1480
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12413:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12254532086248539 : ℚ) / 1000000000000) ≤ ((12245105586662403 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (12413:ℚ) := by decide +kernel
  have hratR : ((((12254532086248539 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((12245105586662403 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12413:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1482 : ((((12263959230112703 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12421 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12413 < q → q < 12421 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12421).mp (by decide +kernel))) hgap
  have hprev := thV_1481
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12421:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12263959230112703 : ℚ) / 1000000000000) ≤ ((12254532086248539 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (12421:ℚ) := by decide +kernel
  have hratR : ((((12263959230112703 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((12254532086248539 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12421:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1483 : ((((3068346834904069 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12433 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12421 < q → q < 12433 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12433).mp (by decide +kernel))) hgap
  have hprev := thV_1482
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12433:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3068346834904069 : ℚ) / 250000000000) ≤ ((12263959230112703 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (12433:ℚ) := by decide +kernel
  have hratR : ((((3068346834904069 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((12263959230112703 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12433:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1484 : ((((245656315415851 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12437 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12433 < q → q < 12437 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12437).mp (by decide +kernel))) hgap
  have hprev := thV_1483
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12437:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((245656315415851 : ℚ) / 20000000000) ≤ ((3068346834904069 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (12437:ℚ) := by decide +kernel
  have hratR : ((((245656315415851 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ ((((3068346834904069 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12437:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1485 : ((((12292245327009123 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12451 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12437 < q → q < 12451 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12451).mp (by decide +kernel))) hgap
  have hprev := thV_1484
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12451:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12292245327009123 : ℚ) / 1000000000000) ≤ ((245656315415851 : ℚ) / 20000000000) + Work.RHContract.RegionI.logLowQ (12451:ℚ) := by decide +kernel
  have hratR : ((((12292245327009123 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((245656315415851 : ℚ) / 20000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12451:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1486 : ((((12301675364998629 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12457 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12451 < q → q < 12457 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12457).mp (by decide +kernel))) hgap
  have hprev := thV_1485
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12457:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12301675364998629 : ℚ) / 1000000000000) ≤ ((12292245327009123 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (12457:ℚ) := by decide +kernel
  have hratR : ((((12301675364998629 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((12292245327009123 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12457:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1487 : ((((98488853492659 : ℚ) / 8000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12473 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12457 < q → q < 12473 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12473).mp (by decide +kernel))) hgap
  have hprev := thV_1486
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12473:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((98488853492659 : ℚ) / 8000000000) ≤ ((12301675364998629 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (12473:ℚ) := by decide +kernel
  have hratR : ((((98488853492659 : ℚ) / 8000000000) : ℚ) : ℝ) ≤ ((((12301675364998629 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12473:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1488 : ((((12320538489089503 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12479 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12473 < q → q < 12479 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12479).mp (by decide +kernel))) hgap
  have hprev := thV_1487
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12479:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12320538489089503 : ℚ) / 1000000000000) ≤ ((98488853492659 : ℚ) / 8000000000) + Work.RHContract.RegionI.logLowQ (12479:ℚ) := by decide +kernel
  have hratR : ((((12320538489089503 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((98488853492659 : ℚ) / 8000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12479:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1489 : ((((6164985466234119 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12487 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12479 < q → q < 12487 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12487).mp (by decide +kernel))) hgap
  have hprev := thV_1488
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12487:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6164985466234119 : ℚ) / 500000000000) ≤ ((12320538489089503 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (12487:ℚ) := by decide +kernel
  have hratR : ((((6164985466234119 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((12320538489089503 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12487:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1490 : ((((1542425462016103 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12491 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12487 < q → q < 12491 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12491).mp (by decide +kernel))) hgap
  have hprev := thV_1489
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12491:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1542425462016103 : ℚ) / 125000000000) ≤ ((6164985466234119 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (12491:ℚ) := by decide +kernel
  have hratR : ((((1542425462016103 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((6164985466234119 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12491:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1491 : ((((1234883694001993 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12497 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12491 < q → q < 12497 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12497).mp (by decide +kernel))) hgap
  have hprev := thV_1490
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12497:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1234883694001993 : ℚ) / 100000000000) ≤ ((1542425462016103 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (12497:ℚ) := by decide +kernel
  have hratR : ((((1234883694001993 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((1542425462016103 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12497:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1492 : ((((2471654132782209 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12503 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12497 < q → q < 12503 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12503).mp (by decide +kernel))) hgap
  have hprev := thV_1491
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12503:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2471654132782209 : ℚ) / 200000000000) ≤ ((1234883694001993 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (12503:ℚ) := by decide +kernel
  have hratR : ((((2471654132782209 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((1234883694001993 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12503:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1493 : ((((12367705027443983 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12511 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12503 < q → q < 12511 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12511).mp (by decide +kernel))) hgap
  have hprev := thV_1492
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12511:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12367705027443983 : ℚ) / 1000000000000) ≤ ((2471654132782209 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (12511:ℚ) := by decide +kernel
  have hratR : ((((12367705027443983 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2471654132782209 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12511:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1494 : ((((12377139870439931 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12517 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12511 < q → q < 12517 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12517).mp (by decide +kernel))) hgap
  have hprev := thV_1493
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12517:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12377139870439931 : ℚ) / 1000000000000) ≤ ((12367705027443983 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (12517:ℚ) := by decide +kernel
  have hratR : ((((12377139870439931 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((12367705027443983 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12517:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1495 : ((((2477315102406079 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12527 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12517 < q → q < 12527 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12527).mp (by decide +kernel))) hgap
  have hprev := thV_1494
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12527:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2477315102406079 : ℚ) / 200000000000) ≤ ((12377139870439931 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (12527:ℚ) := by decide +kernel
  have hratR : ((((2477315102406079 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((12377139870439931 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12527:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1496 : ((((6198006055546603 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12539 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12527 < q → q < 12539 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12539).mp (by decide +kernel))) hgap
  have hprev := thV_1495
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12539:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6198006055546603 : ℚ) / 500000000000) ≤ ((2477315102406079 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (12539:ℚ) := by decide +kernel
  have hratR : ((((6198006055546603 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((2477315102406079 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12539:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1497 : ((((248108977392913 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12541 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12539 < q → q < 12541 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12541).mp (by decide +kernel))) hgap
  have hprev := thV_1496
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12541:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((248108977392913 : ℚ) / 20000000000) ≤ ((6198006055546603 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (12541:ℚ) := by decide +kernel
  have hratR : ((((248108977392913 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ ((((6198006055546603 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12541:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1498 : ((((1241488610651443 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12547 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12541 < q → q < 12547 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12547).mp (by decide +kernel))) hgap
  have hprev := thV_1497
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12547:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1241488610651443 : ℚ) / 100000000000) ≤ ((248108977392913 : ℚ) / 20000000000) + Work.RHContract.RegionI.logLowQ (12547:ℚ) := by decide +kernel
  have hratR : ((((1241488610651443 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((248108977392913 : ℚ) / 20000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12547:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1499 : ((((3106080955367717 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12553 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12547 < q → q < 12553 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12553).mp (by decide +kernel))) hgap
  have hprev := thV_1498
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12553:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3106080955367717 : ℚ) / 250000000000) ≤ ((1241488610651443 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (12553:ℚ) := by decide +kernel
  have hratR : ((((3106080955367717 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((1241488610651443 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12553:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1500 : ((((12433762810211413 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12569 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12553 < q → q < 12569 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12569).mp (by decide +kernel))) hgap
  have hprev := thV_1499
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12569:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12433762810211413 : ℚ) / 1000000000000) ≤ ((3106080955367717 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (12569:ℚ) := by decide +kernel
  have hratR : ((((12433762810211413 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3106080955367717 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12569:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1501 : ((((155540030440451 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12577 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12569 < q → q < 12577 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12577).mp (by decide +kernel))) hgap
  have hprev := thV_1500
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12577:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((155540030440451 : ℚ) / 12500000000) ≤ ((12433762810211413 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (12577:ℚ) := by decide +kernel
  have hratR : ((((155540030440451 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ ((((12433762810211413 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12577:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1502 : ((((3113160634302073 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12583 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12577 < q → q < 12583 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12583).mp (by decide +kernel))) hgap
  have hprev := thV_1501
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12583:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3113160634302073 : ℚ) / 250000000000) ≤ ((155540030440451 : ℚ) / 12500000000) + Work.RHContract.RegionI.logLowQ (12583:ℚ) := by decide +kernel
  have hratR : ((((3113160634302073 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((155540030440451 : ℚ) / 12500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12583:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1503 : ((((6231041557950339 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12589 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12583 < q → q < 12589 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12589).mp (by decide +kernel))) hgap
  have hprev := thV_1502
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12589:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6231041557950339 : ℚ) / 500000000000) ≤ ((3113160634302073 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (12589:ℚ) := by decide +kernel
  have hratR : ((((6231041557950339 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((3113160634302073 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12589:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1504 : ((((1558940580919021 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12601 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12589 < q → q < 12601 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12601).mp (by decide +kernel))) hgap
  have hprev := thV_1503
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12601:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1558940580919021 : ℚ) / 125000000000) ≤ ((6231041557950339 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (12601:ℚ) := by decide +kernel
  have hratR : ((((1558940580919021 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((6231041557950339 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12601:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1505 : ((((1560120871509593 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12611 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12601 < q → q < 12611 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12611).mp (by decide +kernel))) hgap
  have hprev := thV_1504
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12611:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1560120871509593 : ℚ) / 125000000000) ≤ ((1558940580919021 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (12611:ℚ) := by decide +kernel
  have hratR : ((((1560120871509593 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((1558940580919021 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12611:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1506 : ((((12490409455380451 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12613 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12611 < q → q < 12613 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12613).mp (by decide +kernel))) hgap
  have hprev := thV_1505
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12613:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12490409455380451 : ℚ) / 1000000000000) ≤ ((1560120871509593 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (12613:ℚ) := by decide +kernel
  have hratR : ((((12490409455380451 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1560120871509593 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12613:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1507 : ((((3124963103567681 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12619 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12613 < q → q < 12619 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12619).mp (by decide +kernel))) hgap
  have hprev := thV_1506
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12619:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3124963103567681 : ℚ) / 250000000000) ≤ ((12490409455380451 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (12619:ℚ) := by decide +kernel
  have hratR : ((((3124963103567681 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((12490409455380451 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12619:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1508 : ((((12509296798565103 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12637 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12619 < q → q < 12637 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12637).mp (by decide +kernel))) hgap
  have hprev := thV_1507
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12637:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12509296798565103 : ℚ) / 1000000000000) ≤ ((3124963103567681 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (12637:ℚ) := by decide +kernel
  have hratR : ((((12509296798565103 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3124963103567681 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12637:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1509 : ((((12518741499340219 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12641 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12637 < q → q < 12641 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12641).mp (by decide +kernel))) hgap
  have hprev := thV_1508
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12641:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12518741499340219 : ℚ) / 1000000000000) ≤ ((12509296798565103 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (12641:ℚ) := by decide +kernel
  have hratR : ((((12518741499340219 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((12509296798565103 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12641:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1510 : ((((12528186674648719 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12647 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12641 < q → q < 12647 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12647).mp (by decide +kernel))) hgap
  have hprev := thV_1509
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12647:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12528186674648719 : ℚ) / 1000000000000) ≤ ((12518741499340219 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (12647:ℚ) := by decide +kernel
  have hratR : ((((12528186674648719 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((12518741499340219 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12647:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1511 : ((((1567204040533191 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12653 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12647 < q → q < 12653 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12653).mp (by decide +kernel))) hgap
  have hprev := thV_1510
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12653:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1567204040533191 : ℚ) / 125000000000) ≤ ((12528186674648719 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (12653:ℚ) := by decide +kernel
  have hratR : ((((1567204040533191 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((12528186674648719 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12653:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1512 : ((((2509415689593157 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12659 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12653 < q → q < 12659 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12659).mp (by decide +kernel))) hgap
  have hprev := thV_1511
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12659:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2509415689593157 : ℚ) / 200000000000) ≤ ((1567204040533191 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (12659:ℚ) := by decide +kernel
  have hratR : ((((2509415689593157 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((1567204040533191 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12659:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1513 : ((((3139131379789801 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12671 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12659 < q → q < 12671 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12671).mp (by decide +kernel))) hgap
  have hprev := thV_1512
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12671:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3139131379789801 : ℚ) / 250000000000) ≤ ((2509415689593157 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (12671:ℚ) := by decide +kernel
  have hratR : ((((3139131379789801 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((2509415689593157 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12671:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1514 : ((((12565974009911221 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12689 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12671 < q → q < 12689 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12689).mp (by decide +kernel))) hgap
  have hprev := thV_1513
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12689:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12565974009911221 : ℚ) / 1000000000000) ≤ ((3139131379789801 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (12689:ℚ) := by decide +kernel
  have hratR : ((((12565974009911221 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3139131379789801 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12689:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1515 : ((((12575423130931911 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12697 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12689 < q → q < 12697 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12697).mp (by decide +kernel))) hgap
  have hprev := thV_1514
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12697:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12575423130931911 : ℚ) / 1000000000000) ≤ ((12565974009911221 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (12697:ℚ) := by decide +kernel
  have hratR : ((((12575423130931911 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((12565974009911221 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12697:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1516 : ((((2516974544878711 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12703 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12697 < q → q < 12703 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12703).mp (by decide +kernel))) hgap
  have hprev := thV_1515
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12703:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2516974544878711 : ℚ) / 200000000000) ≤ ((12575423130931911 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (12703:ℚ) := by decide +kernel
  have hratR : ((((2516974544878711 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((12575423130931911 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12703:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1517 : ((((100754584838089 : ℚ) / 8000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12713 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12703 < q → q < 12713 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12713).mp (by decide +kernel))) hgap
  have hprev := thV_1516
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12713:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((100754584838089 : ℚ) / 8000000000) ≤ ((2516974544878711 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (12713:ℚ) := by decide +kernel
  have hratR : ((((100754584838089 : ℚ) / 8000000000) : ℚ) : ℝ) ≤ ((((2516974544878711 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12713:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1518 : ((((12603774114207901 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12721 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12713 < q → q < 12721 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12721).mp (by decide +kernel))) hgap
  have hprev := thV_1517
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12721:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12603774114207901 : ℚ) / 1000000000000) ≤ ((100754584838089 : ℚ) / 8000000000) + Work.RHContract.RegionI.logLowQ (12721:ℚ) := by decide +kernel
  have hratR : ((((12603774114207901 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((100754584838089 : ℚ) / 8000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12721:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1519 : ((((12613226537637631 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12739 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12721 < q → q < 12739 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12739).mp (by decide +kernel))) hgap
  have hprev := thV_1518
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12739:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12613226537637631 : ℚ) / 1000000000000) ≤ ((12603774114207901 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (12739:ℚ) := by decide +kernel
  have hratR : ((((12613226537637631 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((12603774114207901 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12739:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1520 : ((((12622679275014463 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12743 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12739 < q → q < 12743 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12743).mp (by decide +kernel))) hgap
  have hprev := thV_1519
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12743:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12622679275014463 : ℚ) / 1000000000000) ≤ ((12613226537637631 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (12743:ℚ) := by decide +kernel
  have hratR : ((((12622679275014463 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((12613226537637631 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12743:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1521 : ((((6316066555215311 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12757 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12743 < q → q < 12757 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12757).mp (by decide +kernel))) hgap
  have hprev := thV_1520
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12757:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6316066555215311 : ℚ) / 500000000000) ≤ ((12622679275014463 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (12757:ℚ) := by decide +kernel
  have hratR : ((((6316066555215311 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((12622679275014463 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12757:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1522 : ((((505663496642649 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12763 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12757 < q → q < 12763 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12763).mp (by decide +kernel))) hgap
  have hprev := thV_1521
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12763:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((505663496642649 : ℚ) / 40000000000) ≤ ((6316066555215311 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (12763:ℚ) := by decide +kernel
  have hratR : ((((505663496642649 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((6316066555215311 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12763:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1523 : ((((12651043131034977 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12781 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12763 < q → q < 12781 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12781).mp (by decide +kernel))) hgap
  have hprev := thV_1522
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12781:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12651043131034977 : ℚ) / 1000000000000) ≤ ((505663496642649 : ℚ) / 40000000000) + Work.RHContract.RegionI.logLowQ (12781:ℚ) := by decide +kernel
  have hratR : ((((12651043131034977 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((505663496642649 : ℚ) / 40000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12781:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1524 : ((((12660499628109197 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12791 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12781 < q → q < 12791 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12791).mp (by decide +kernel))) hgap
  have hprev := thV_1523
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12791:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12660499628109197 : ℚ) / 1000000000000) ≤ ((12651043131034977 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (12791:ℚ) := by decide +kernel
  have hratR : ((((12660499628109197 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((12651043131034977 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12791:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1525 : ((((12669956750427673 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12799 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12791 < q → q < 12799 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12799).mp (by decide +kernel))) hgap
  have hprev := thV_1524
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12799:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12669956750427673 : ℚ) / 1000000000000) ≤ ((12660499628109197 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (12799:ℚ) := by decide +kernel
  have hratR : ((((12669956750427673 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((12660499628109197 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12799:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1526 : ((((3169853663438031 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12809 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12799 < q → q < 12809 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12809).mp (by decide +kernel))) hgap
  have hprev := thV_1525
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12809:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3169853663438031 : ℚ) / 250000000000) ≤ ((12669956750427673 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (12809:ℚ) := by decide +kernel
  have hratR : ((((3169853663438031 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((12669956750427673 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12809:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1527 : ((((12688873493479297 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12821 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12809 < q → q < 12821 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12821).mp (by decide +kernel))) hgap
  have hprev := thV_1526
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12821:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12688873493479297 : ℚ) / 1000000000000) ≤ ((3169853663438031 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (12821:ℚ) := by decide +kernel
  have hratR : ((((12688873493479297 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3169853663438031 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12821:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1528 : ((((1587291561148547 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12823 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12821 < q → q < 12823 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12823).mp (by decide +kernel))) hgap
  have hprev := thV_1527
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12823:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1587291561148547 : ℚ) / 125000000000) ≤ ((12688873493479297 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (12823:ℚ) := by decide +kernel
  have hratR : ((((1587291561148547 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((12688873493479297 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12823:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1529 : ((((6353895976348623 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12829 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12823 < q → q < 12829 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12829).mp (by decide +kernel))) hgap
  have hprev := thV_1528
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12829:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6353895976348623 : ℚ) / 500000000000) ≤ ((1587291561148547 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (12829:ℚ) := by decide +kernel
  have hratR : ((((6353895976348623 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1587291561148547 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12829:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1530 : ((((12717252351149697 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12841 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12829 < q → q < 12841 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12841).mp (by decide +kernel))) hgap
  have hprev := thV_1529
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12841:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12717252351149697 : ℚ) / 1000000000000) ≤ ((6353895976348623 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (12841:ℚ) := by decide +kernel
  have hratR : ((((12717252351149697 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((6353895976348623 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12841:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1531 : ((((12726713683672427 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12853 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12841 < q → q < 12853 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12853).mp (by decide +kernel))) hgap
  have hprev := thV_1530
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12853:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12726713683672427 : ℚ) / 1000000000000) ≤ ((12717252351149697 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (12853:ℚ) := by decide +kernel
  have hratR : ((((12726713683672427 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((12717252351149697 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12853:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1532 : ((((3184044453295613 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12889 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12853 < q → q < 12889 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12889).mp (by decide +kernel))) hgap
  have hprev := thV_1531
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12889:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3184044453295613 : ℚ) / 250000000000) ≤ ((12726713683672427 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (12889:ℚ) := by decide +kernel
  have hratR : ((((3184044453295613 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((12726713683672427 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12889:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1533 : ((((12745642252986483 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12893 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12889 < q → q < 12893 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12893).mp (by decide +kernel))) hgap
  have hprev := thV_1532
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12893:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12745642252986483 : ℚ) / 1000000000000) ≤ ((3184044453295613 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (12893:ℚ) := by decide +kernel
  have hratR : ((((12745642252986483 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3184044453295613 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12893:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1534 : ((((3188776789512767 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12899 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12893 < q → q < 12899 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12899).mp (by decide +kernel))) hgap
  have hprev := thV_1533
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12899:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3188776789512767 : ℚ) / 250000000000) ≤ ((12745642252986483 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (12899:ℚ) := by decide +kernel
  have hratR : ((((3188776789512767 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((12745642252986483 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12899:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1535 : ((((12764572683126523 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12907 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12899 < q → q < 12907 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12907).mp (by decide +kernel))) hgap
  have hprev := thV_1534
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12907:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12764572683126523 : ℚ) / 1000000000000) ≤ ((3188776789512767 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (12907:ℚ) := by decide +kernel
  have hratR : ((((12764572683126523 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3188776789512767 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12907:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1536 : ((((6387019259031659 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12911 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12907 < q → q < 12911 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12911).mp (by decide +kernel))) hgap
  have hprev := thV_1535
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12911:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6387019259031659 : ℚ) / 500000000000) ≤ ((12764572683126523 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (12911:ℚ) := by decide +kernel
  have hratR : ((((6387019259031659 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((12764572683126523 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12911:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1537 : ((((1278350481761217 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12917 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12911 < q → q < 12917 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12917).mp (by decide +kernel))) hgap
  have hprev := thV_1536
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12917:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1278350481761217 : ℚ) / 100000000000) ≤ ((6387019259031659 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (12917:ℚ) := by decide +kernel
  have hratR : ((((1278350481761217 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((6387019259031659 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12917:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1538 : ((((12792971271983751 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12919 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12917 < q → q < 12919 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12919).mp (by decide +kernel))) hgap
  have hprev := thV_1537
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12919:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12792971271983751 : ℚ) / 1000000000000) ≤ ((1278350481761217 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (12919:ℚ) := by decide +kernel
  have hratR : ((((12792971271983751 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1278350481761217 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12919:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1539 : ((((200038094311389 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12923 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12919 < q → q < 12923 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12923).mp (by decide +kernel))) hgap
  have hprev := thV_1538
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12923:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((200038094311389 : ℚ) / 15625000000) ≤ ((12792971271983751 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (12923:ℚ) := by decide +kernel
  have hratR : ((((200038094311389 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ ((((12792971271983751 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12923:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1540 : ((((6405953095885169 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12941 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12923 < q → q < 12941 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12941).mp (by decide +kernel))) hgap
  have hprev := thV_1539
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12941:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6405953095885169 : ℚ) / 500000000000) ≤ ((200038094311389 : ℚ) / 15625000000) + Work.RHContract.RegionI.logLowQ (12941:ℚ) := by decide +kernel
  have hratR : ((((6405953095885169 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((200038094311389 : ℚ) / 15625000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12941:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1541 : ((((400667977327109 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12953 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12941 < q → q < 12953 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12953).mp (by decide +kernel))) hgap
  have hprev := thV_1540
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12953:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((400667977327109 : ℚ) / 31250000000) ≤ ((6405953095885169 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (12953:ℚ) := by decide +kernel
  have hratR : ((((400667977327109 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((6405953095885169 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12953:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1542 : ((((801927801266909 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12959 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12953 < q → q < 12959 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12959).mp (by decide +kernel))) hgap
  have hprev := thV_1541
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12959:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((801927801266909 : ℚ) / 62500000000) ≤ ((400667977327109 : ℚ) / 31250000000) + Work.RHContract.RegionI.logLowQ (12959:ℚ) := by decide +kernel
  have hratR : ((((801927801266909 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((400667977327109 : ℚ) / 31250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12959:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1543 : ((((12840314983214713 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12967 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12959 < q → q < 12967 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12967).mp (by decide +kernel))) hgap
  have hprev := thV_1542
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12967:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12840314983214713 : ℚ) / 1000000000000) ≤ ((801927801266909 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (12967:ℚ) := by decide +kernel
  have hratR : ((((12840314983214713 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((801927801266909 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12967:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1544 : ((((1606223201095613 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12973 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12967 < q → q < 12973 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12973).mp (by decide +kernel))) hgap
  have hprev := thV_1543
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12973:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1606223201095613 : ℚ) / 125000000000) ≤ ((12840314983214713 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (12973:ℚ) := by decide +kernel
  have hratR : ((((1606223201095613 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((12840314983214713 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12973:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1545 : ((((3214814174176803 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12979 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12973 < q → q < 12979 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12979).mp (by decide +kernel))) hgap
  have hprev := thV_1544
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12979:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3214814174176803 : ℚ) / 250000000000) ≤ ((1606223201095613 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (12979:ℚ) := by decide +kernel
  have hratR : ((((3214814174176803 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((1606223201095613 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12979:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1546 : ((((100536938224939 : ℚ) / 7812500000) : ℚ) : ℝ) ≤ Chebyshev.theta ((12983 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12979 < q → q < 12983 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12983).mp (by decide +kernel))) hgap
  have hprev := thV_1545
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (12983:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((100536938224939 : ℚ) / 7812500000) ≤ ((3214814174176803 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (12983:ℚ) := by decide +kernel
  have hratR : ((((100536938224939 : ℚ) / 7812500000) : ℚ) : ℝ) ≤ ((((3214814174176803 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (12983:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1547 : ((((6439100437172687 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13001 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 12983 < q → q < 13001 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13001).mp (by decide +kernel))) hgap
  have hprev := thV_1546
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13001:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6439100437172687 : ℚ) / 500000000000) ≤ ((100536938224939 : ℚ) / 7812500000) + Work.RHContract.RegionI.logLowQ (13001:ℚ) := by decide +kernel
  have hratR : ((((6439100437172687 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((100536938224939 : ℚ) / 7812500000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13001:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1548 : ((((6443836904860523 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13003 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13001 < q → q < 13003 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13003).mp (by decide +kernel))) hgap
  have hprev := thV_1547
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13003:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6443836904860523 : ℚ) / 500000000000) ≤ ((6439100437172687 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (13003:ℚ) := by decide +kernel
  have hratR : ((((6443836904860523 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((6439100437172687 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13003:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1549 : ((((1289714705267073 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13007 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13003 < q → q < 13007 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13007).mp (by decide +kernel))) hgap
  have hprev := thV_1548
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13007:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1289714705267073 : ℚ) / 100000000000) ≤ ((6443836904860523 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (13007:ℚ) := by decide +kernel
  have hratR : ((((1289714705267073 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((6443836904860523 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13007:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1550 : ((((806663778085747 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13009 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13007 < q → q < 13009 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13009).mp (by decide +kernel))) hgap
  have hprev := thV_1549
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13009:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((806663778085747 : ℚ) / 62500000000) ≤ ((1289714705267073 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (13009:ℚ) := by decide +kernel
  have hratR : ((((806663778085747 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((1289714705267073 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13009:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1551 : ((((12916095689250103 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13033 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13009 < q → q < 13033 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13033).mp (by decide +kernel))) hgap
  have hprev := thV_1550
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13033:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12916095689250103 : ℚ) / 1000000000000) ≤ ((806663778085747 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (13033:ℚ) := by decide +kernel
  have hratR : ((((12916095689250103 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((806663778085747 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13033:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1552 : ((((6462785617997193 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13037 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13033 < q → q < 13037 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13037).mp (by decide +kernel))) hgap
  have hprev := thV_1551
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13037:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6462785617997193 : ℚ) / 500000000000) ≤ ((12916095689250103 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (13037:ℚ) := by decide +kernel
  have hratR : ((((6462785617997193 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((12916095689250103 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13037:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1553 : ((((202110113169709 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13043 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13037 < q → q < 13043 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13043).mp (by decide +kernel))) hgap
  have hprev := thV_1552
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13043:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((202110113169709 : ℚ) / 15625000000) ≤ ((6462785617997193 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (13043:ℚ) := by decide +kernel
  have hratR : ((((202110113169709 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ ((((6462785617997193 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13043:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1554 : ((((6472261854819729 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13049 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13043 < q → q < 13049 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13049).mp (by decide +kernel))) hgap
  have hprev := thV_1553
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13049:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6472261854819729 : ℚ) / 500000000000) ≤ ((202110113169709 : ℚ) / 15625000000) + Work.RHContract.RegionI.logLowQ (13049:ℚ) := by decide +kernel
  have hratR : ((((6472261854819729 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((202110113169709 : ℚ) / 15625000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13049:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1555 : ((((2590800249744313 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13063 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13049 < q → q < 13063 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13063).mp (by decide +kernel))) hgap
  have hprev := thV_1554
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13063:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2590800249744313 : ℚ) / 200000000000) ≤ ((6472261854819729 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (13063:ℚ) := by decide +kernel
  have hratR : ((((2590800249744313 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((6472261854819729 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13063:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1556 : ((((12963481081733413 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13093 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13063 < q → q < 13093 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13093).mp (by decide +kernel))) hgap
  have hprev := thV_1555
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13093:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12963481081733413 : ℚ) / 1000000000000) ≤ ((2590800249744313 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (13093:ℚ) := by decide +kernel
  have hratR : ((((12963481081733413 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2590800249744313 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13093:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1557 : ((((12972961372900431 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13099 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13093 < q → q < 13099 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13099).mp (by decide +kernel))) hgap
  have hprev := thV_1556
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13099:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((12972961372900431 : ℚ) / 1000000000000) ≤ ((12963481081733413 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (13099:ℚ) := by decide +kernel
  have hratR : ((((12972961372900431 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((12963481081733413 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13099:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1558 : ((((1622805246173457 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13103 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13099 < q → q < 13103 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13103).mp (by decide +kernel))) hgap
  have hprev := thV_1557
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13103:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1622805246173457 : ℚ) / 125000000000) ≤ ((12972961372900431 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (13103:ℚ) := by decide +kernel
  have hratR : ((((1622805246173457 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((12972961372900431 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13103:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1559 : ((((6495961511840237 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13109 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13103 < q → q < 13109 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13109).mp (by decide +kernel))) hgap
  have hprev := thV_1558
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13109:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6495961511840237 : ℚ) / 500000000000) ≤ ((1622805246173457 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (13109:ℚ) := by decide +kernel
  have hratR : ((((6495961511840237 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1622805246173457 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13109:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1560 : ((((65007024964781 : ℚ) / 5000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13121 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13109 < q → q < 13121 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13121).mp (by decide +kernel))) hgap
  have hprev := thV_1559
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13121:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((65007024964781 : ℚ) / 5000000000) ≤ ((6495961511840237 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (13121:ℚ) := by decide +kernel
  have hratR : ((((65007024964781 : ℚ) / 5000000000) : ℚ) : ℝ) ≤ ((((6495961511840237 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13121:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1561 : ((((1626360927426203 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13127 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13121 < q → q < 13127 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13127).mp (by decide +kernel))) hgap
  have hprev := thV_1560
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13127:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1626360927426203 : ℚ) / 125000000000) ≤ ((65007024964781 : ℚ) / 5000000000) + Work.RHContract.RegionI.logLowQ (13127:ℚ) := by decide +kernel
  have hratR : ((((1626360927426203 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((65007024964781 : ℚ) / 5000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13127:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1562 : ((((13020371368280941 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13147 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13127 < q → q < 13147 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13147).mp (by decide +kernel))) hgap
  have hprev := thV_1561
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13147:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13020371368280941 : ℚ) / 1000000000000) ≤ ((1626360927426203 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (13147:ℚ) := by decide +kernel
  have hratR : ((((13020371368280941 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1626360927426203 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13147:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1563 : ((((13029855621357903 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13151 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13147 < q → q < 13151 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13151).mp (by decide +kernel))) hgap
  have hprev := thV_1562
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13151:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13029855621357903 : ℚ) / 1000000000000) ≤ ((13020371368280941 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (13151:ℚ) := by decide +kernel
  have hratR : ((((13029855621357903 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((13020371368280941 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13151:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1564 : ((((13039340482568673 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13159 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13151 < q → q < 13159 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13159).mp (by decide +kernel))) hgap
  have hprev := thV_1563
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13159:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13039340482568673 : ℚ) / 1000000000000) ≤ ((13029855621357903 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (13159:ℚ) := by decide +kernel
  have hratR : ((((13039340482568673 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((13029855621357903 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13159:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1565 : ((((13048825647707719 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13163 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13159 < q → q < 13163 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13163).mp (by decide +kernel))) hgap
  have hprev := thV_1564
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13163:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13048825647707719 : ℚ) / 1000000000000) ≤ ((13039340482568673 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (13163:ℚ) := by decide +kernel
  have hratR : ((((13048825647707719 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((13039340482568673 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13163:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1566 : ((((6529155710213169 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13171 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13163 < q → q < 13171 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13171).mp (by decide +kernel))) hgap
  have hprev := thV_1565
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13171:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6529155710213169 : ℚ) / 500000000000) ≤ ((13048825647707719 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (13171:ℚ) := by decide +kernel
  have hratR : ((((6529155710213169 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((13048825647707719 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13171:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1567 : ((((13067797648587503 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13177 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13171 < q → q < 13177 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13177).mp (by decide +kernel))) hgap
  have hprev := thV_1566
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13177:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13067797648587503 : ℚ) / 1000000000000) ≤ ((6529155710213169 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (13177:ℚ) := by decide +kernel
  have hratR : ((((13067797648587503 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((6529155710213169 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13177:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1568 : ((((13077284331983881 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13183 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13177 < q → q < 13183 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13183).mp (by decide +kernel))) hgap
  have hprev := thV_1567
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13183:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13077284331983881 : ℚ) / 1000000000000) ≤ ((13067797648587503 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (13183:ℚ) := by decide +kernel
  have hratR : ((((13077284331983881 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((13067797648587503 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13183:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1569 : ((((13086771318755309 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13187 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13183 < q → q < 13187 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13187).mp (by decide +kernel))) hgap
  have hprev := thV_1568
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13187:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13086771318755309 : ℚ) / 1000000000000) ≤ ((13077284331983881 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (13187:ℚ) := by decide +kernel
  have hratR : ((((13086771318755309 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((13077284331983881 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13187:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1570 : ((((13096260577910687 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13217 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13187 < q → q < 13217 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13217).mp (by decide +kernel))) hgap
  have hprev := thV_1569
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13217:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13096260577910687 : ℚ) / 1000000000000) ≤ ((13086771318755309 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (13217:ℚ) := by decide +kernel
  have hratR : ((((13096260577910687 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((13086771318755309 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13217:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1571 : ((((13105749988374887 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13219 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13217 < q → q < 13219 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13219).mp (by decide +kernel))) hgap
  have hprev := thV_1570
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13219:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13105749988374887 : ℚ) / 1000000000000) ≤ ((13096260577910687 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (13219:ℚ) := by decide +kernel
  have hratR : ((((13105749988374887 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((13096260577910687 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13219:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1572 : ((((1311524015503997 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13229 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13219 < q → q < 13229 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13229).mp (by decide +kernel))) hgap
  have hprev := thV_1571
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13229:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1311524015503997 : ℚ) / 100000000000) ≤ ((13105749988374887 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (13229:ℚ) := by decide +kernel
  have hratR : ((((1311524015503997 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((13105749988374887 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13229:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1573 : ((((1312473122839193 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13241 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13229 < q → q < 13241 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13241).mp (by decide +kernel))) hgap
  have hprev := thV_1572
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13241:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1312473122839193 : ℚ) / 100000000000) ≤ ((1311524015503997 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (13241:ℚ) := by decide +kernel
  have hratR : ((((1312473122839193 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((1311524015503997 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13241:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1574 : ((((6567111452872709 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13249 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13241 < q → q < 13249 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13249).mp (by decide +kernel))) hgap
  have hprev := thV_1573
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13249:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6567111452872709 : ℚ) / 500000000000) ≤ ((1312473122839193 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (13249:ℚ) := by decide +kernel
  have hratR : ((((6567111452872709 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1312473122839193 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13249:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1575 : ((((13143715337588153 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13259 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13249 < q → q < 13259 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13259).mp (by decide +kernel))) hgap
  have hprev := thV_1574
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13259:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13143715337588153 : ℚ) / 1000000000000) ≤ ((6567111452872709 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (13259:ℚ) := by decide +kernel
  have hratR : ((((13143715337588153 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((6567111452872709 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13259:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1576 : ((((1315320837261269 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13267 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13259 < q → q < 13267 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13267).mp (by decide +kernel))) hgap
  have hprev := thV_1575
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13267:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1315320837261269 : ℚ) / 100000000000) ≤ ((13143715337588153 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (13267:ℚ) := by decide +kernel
  have hratR : ((((1315320837261269 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((13143715337588153 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13267:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1577 : ((((3290675803750683 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13291 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13267 < q → q < 13291 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13291).mp (by decide +kernel))) hgap
  have hprev := thV_1576
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13291:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3290675803750683 : ℚ) / 250000000000) ≤ ((1315320837261269 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (13291:ℚ) := by decide +kernel
  have hratR : ((((3290675803750683 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((1315320837261269 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13291:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1578 : ((((13172198508724209 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13297 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13291 < q → q < 13297 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13297).mp (by decide +kernel))) hgap
  have hprev := thV_1577
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13297:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13172198508724209 : ℚ) / 1000000000000) ≤ ((3290675803750683 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (13297:ℚ) := by decide +kernel
  have hratR : ((((13172198508724209 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3290675803750683 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13297:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1579 : ((((3295423676124479 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13309 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13297 < q → q < 13309 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13309).mp (by decide +kernel))) hgap
  have hprev := thV_1578
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13309:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3295423676124479 : ℚ) / 250000000000) ≤ ((13172198508724209 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (13309:ℚ) := by decide +kernel
  have hratR : ((((3295423676124479 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((13172198508724209 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13309:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1580 : ((((1648898900096871 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13313 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13309 < q → q < 13313 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13313).mp (by decide +kernel))) hgap
  have hprev := thV_1579
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13313:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1648898900096871 : ℚ) / 125000000000) ≤ ((3295423676124479 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (13313:ℚ) := by decide +kernel
  have hratR : ((((1648898900096871 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((3295423676124479 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13313:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1581 : ((((25782595211139 : ℚ) / 1953125000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13327 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13313 < q → q < 13327 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13327).mp (by decide +kernel))) hgap
  have hprev := thV_1580
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13327:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((25782595211139 : ℚ) / 1953125000) ≤ ((1648898900096871 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (13327:ℚ) := by decide +kernel
  have hratR : ((((25782595211139 : ℚ) / 1953125000) : ℚ) : ℝ) ≤ ((((1648898900096871 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13327:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1582 : ((((6605093297764451 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13331 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13327 < q → q < 13331 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13331).mp (by decide +kernel))) hgap
  have hprev := thV_1581
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13331:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6605093297764451 : ℚ) / 500000000000) ≤ ((25782595211139 : ℚ) / 1953125000) + Work.RHContract.RegionI.logLowQ (13331:ℚ) := by decide +kernel
  have hratR : ((((6605093297764451 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((25782595211139 : ℚ) / 1953125000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13331:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1583 : ((((2643936978586429 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13337 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13331 < q → q < 13337 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13337).mp (by decide +kernel))) hgap
  have hprev := thV_1582
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13337:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2643936978586429 : ℚ) / 200000000000) ≤ ((6605093297764451 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (13337:ℚ) := by decide +kernel
  have hratR : ((((2643936978586429 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((6605093297764451 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13337:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1584 : ((((6614591670141453 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13339 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13337 < q → q < 13339 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13339).mp (by decide +kernel))) hgap
  have hprev := thV_1583
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13339:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6614591670141453 : ℚ) / 500000000000) ≤ ((2643936978586429 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (13339:ℚ) := by decide +kernel
  have hratR : ((((6614591670141453 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((2643936978586429 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13339:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1585 : ((((6619341942270749 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13367 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13339 < q → q < 13367 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13367).mp (by decide +kernel))) hgap
  have hprev := thV_1584
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13367:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6619341942270749 : ℚ) / 500000000000) ≤ ((6614591670141453 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (13367:ℚ) := by decide +kernel
  have hratR : ((((6619341942270749 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((6614591670141453 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13367:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1586 : ((((13248185475607423 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13381 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13367 < q → q < 13381 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13381).mp (by decide +kernel))) hgap
  have hprev := thV_1585
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13381:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13248185475607423 : ℚ) / 1000000000000) ≤ ((6619341942270749 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (13381:ℚ) := by decide +kernel
  have hratR : ((((13248185475607423 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((6619341942270749 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13381:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1587 : ((((82860551635527 : ℚ) / 6250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13397 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13381 < q → q < 13397 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13397).mp (by decide +kernel))) hgap
  have hprev := thV_1586
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13397:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((82860551635527 : ℚ) / 6250000000) ≤ ((13248185475607423 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (13397:ℚ) := by decide +kernel
  have hratR : ((((82860551635527 : ℚ) / 6250000000) : ℚ) : ℝ) ≤ ((((13248185475607423 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13397:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1588 : ((((13267191197037229 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13399 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13397 < q → q < 13399 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13399).mp (by decide +kernel))) hgap
  have hprev := thV_1587
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13399:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13267191197037229 : ℚ) / 1000000000000) ≤ ((82860551635527 : ℚ) / 6250000000) + Work.RHContract.RegionI.logLowQ (13399:ℚ) := by decide +kernel
  have hratR : ((((13267191197037229 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((82860551635527 : ℚ) / 6250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13399:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1589 : ((((41489671961183 : ℚ) / 3125000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13411 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13399 < q → q < 13411 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13411).mp (by decide +kernel))) hgap
  have hprev := thV_1588
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13411:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((41489671961183 : ℚ) / 3125000000) ≤ ((13267191197037229 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (13411:ℚ) := by decide +kernel
  have hratR : ((((41489671961183 : ℚ) / 3125000000) : ℚ) : ℝ) ≤ ((((13267191197037229 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13411:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1590 : ((((13286199305413771 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13417 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13411 < q → q < 13417 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13417).mp (by decide +kernel))) hgap
  have hprev := thV_1589
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13417:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13286199305413771 : ℚ) / 1000000000000) ≤ ((41489671961183 : ℚ) / 3125000000) + Work.RHContract.RegionI.logLowQ (13417:ℚ) := by decide +kernel
  have hratR : ((((13286199305413771 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((41489671961183 : ℚ) / 3125000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13417:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1591 : ((((13295703881333789 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13421 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13417 < q → q < 13421 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13421).mp (by decide +kernel))) hgap
  have hprev := thV_1590
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13421:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13295703881333789 : ℚ) / 1000000000000) ≤ ((13286199305413771 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (13421:ℚ) := by decide +kernel
  have hratR : ((((13295703881333789 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((13286199305413771 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13421:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1592 : ((((166315124329331 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13441 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13421 < q → q < 13441 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13441).mp (by decide +kernel))) hgap
  have hprev := thV_1591
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13441:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((166315124329331 : ℚ) / 12500000000) ≤ ((13295703881333789 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (13441:ℚ) := by decide +kernel
  have hratR : ((((166315124329331 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ ((((13295703881333789 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13441:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1593 : ((((13314716755074809 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13451 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13441 < q → q < 13451 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13451).mp (by decide +kernel))) hgap
  have hprev := thV_1592
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13451:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13314716755074809 : ℚ) / 1000000000000) ≤ ((166315124329331 : ℚ) / 12500000000) + Work.RHContract.RegionI.logLowQ (13451:ℚ) := by decide +kernel
  have hratR : ((((13314716755074809 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((166315124329331 : ℚ) / 12500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13451:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1594 : ((((13324224009767171 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13457 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13451 < q → q < 13457 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13457).mp (by decide +kernel))) hgap
  have hprev := thV_1593
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13457:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13324224009767171 : ℚ) / 1000000000000) ≤ ((13314716755074809 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (13457:ℚ) := by decide +kernel
  have hratR : ((((13324224009767171 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((13314716755074809 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13457:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1595 : ((((1333373171022477 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13463 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13457 < q → q < 13463 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13463).mp (by decide +kernel))) hgap
  have hprev := thV_1594
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13463:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1333373171022477 : ℚ) / 100000000000) ≤ ((13324224009767171 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (13463:ℚ) := by decide +kernel
  have hratR : ((((1333373171022477 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((13324224009767171 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13463:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1596 : ((((13343239856248989 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13469 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13463 < q → q < 13469 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13469).mp (by decide +kernel))) hgap
  have hprev := thV_1595
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13469:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13343239856248989 : ℚ) / 1000000000000) ≤ ((1333373171022477 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (13469:ℚ) := by decide +kernel
  have hratR : ((((13343239856248989 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1333373171022477 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13469:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1597 : ((((6676374298026689 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13477 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13469 < q → q < 13477 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13477).mp (by decide +kernel))) hgap
  have hprev := thV_1596
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13477:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6676374298026689 : ℚ) / 500000000000) ≤ ((13343239856248989 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (13477:ℚ) := by decide +kernel
  have hratR : ((((6676374298026689 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((13343239856248989 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13477:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1598 : ((((2672451615517503 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13487 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13477 < q → q < 13487 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13487).mp (by decide +kernel))) hgap
  have hprev := thV_1597
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13487:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2672451615517503 : ℚ) / 200000000000) ≤ ((6676374298026689 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (13487:ℚ) := by decide +kernel
  have hratR : ((((2672451615517503 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((6676374298026689 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13487:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1599 : ((((208933882007371 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13499 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13487 < q → q < 13499 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13499).mp (by decide +kernel))) hgap
  have hprev := thV_1598
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13499:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((208933882007371 : ℚ) / 15625000000) ≤ ((2672451615517503 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (13499:ℚ) := by decide +kernel
  have hratR : ((((208933882007371 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ ((((2672451615517503 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13499:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1600 : ((((6690639927966201 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13513 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13499 < q → q < 13513 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13513).mp (by decide +kernel))) hgap
  have hprev := thV_1599
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13513:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6690639927966201 : ℚ) / 500000000000) ≤ ((208933882007371 : ℚ) / 15625000000) + Work.RHContract.RegionI.logLowQ (13513:ℚ) := by decide +kernel
  have hratR : ((((6690639927966201 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((208933882007371 : ℚ) / 15625000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13513:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1601 : ((((1673849000393437 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13523 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13513 < q → q < 13523 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13523).mp (by decide +kernel))) hgap
  have hprev := thV_1600
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13523:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1673849000393437 : ℚ) / 125000000000) ≤ ((6690639927966201 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (13523:ℚ) := by decide +kernel
  have hratR : ((((1673849000393437 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((6690639927966201 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13523:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1602 : ((((6700152592550151 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13537 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13523 < q → q < 13537 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13537).mp (by decide +kernel))) hgap
  have hprev := thV_1601
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13537:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6700152592550151 : ℚ) / 500000000000) ≤ ((1673849000393437 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (13537:ℚ) := by decide +kernel
  have hratR : ((((6700152592550151 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1673849000393437 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13537:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1603 : ((((6704909774150469 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13553 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13537 < q → q < 13553 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13553).mp (by decide +kernel))) hgap
  have hprev := thV_1602
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13553:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6704909774150469 : ℚ) / 500000000000) ≤ ((6700152592550151 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (13553:ℚ) := by decide +kernel
  have hratR : ((((6704909774150469 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((6700152592550151 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13553:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1604 : ((((3354833735987511 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13567 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13553 < q → q < 13567 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13567).mp (by decide +kernel))) hgap
  have hprev := thV_1603
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13567:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3354833735987511 : ℚ) / 250000000000) ≤ ((6704909774150469 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (13567:ℚ) := by decide +kernel
  have hratR : ((((3354833735987511 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((6704909774150469 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13567:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1605 : ((((1678606384551283 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13577 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13567 < q → q < 13577 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13577).mp (by decide +kernel))) hgap
  have hprev := thV_1604
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13577:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1678606384551283 : ℚ) / 125000000000) ≤ ((3354833735987511 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (13577:ℚ) := by decide +kernel
  have hratR : ((((1678606384551283 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((3354833735987511 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13577:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1606 : ((((335959205987371 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13591 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13577 < q → q < 13591 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13591).mp (by decide +kernel))) hgap
  have hprev := thV_1605
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13591:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((335959205987371 : ℚ) / 25000000000) ≤ ((1678606384551283 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (13591:ℚ) := by decide +kernel
  have hratR : ((((335959205987371 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((1678606384551283 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13591:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1607 : ((((1680985730493827 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13597 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13591 < q → q < 13597 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13597).mp (by decide +kernel))) hgap
  have hprev := thV_1606
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13597:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1680985730493827 : ℚ) / 125000000000) ≤ ((335959205987371 : ℚ) / 25000000000) + Work.RHContract.RegionI.logLowQ (13597:ℚ) := by decide +kernel
  have hratR : ((((1680985730493827 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((335959205987371 : ℚ) / 25000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13597:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1608 : ((((13457404624444749 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13613 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13597 < q → q < 13613 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13613).mp (by decide +kernel))) hgap
  have hprev := thV_1607
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13613:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13457404624444749 : ℚ) / 1000000000000) ≤ ((1680985730493827 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (13613:ℚ) := by decide +kernel
  have hratR : ((((13457404624444749 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1680985730493827 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13613:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1609 : ((((6733461922798469 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13619 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13613 < q → q < 13619 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13619).mp (by decide +kernel))) hgap
  have hprev := thV_1608
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13619:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6733461922798469 : ℚ) / 500000000000) ≤ ((13457404624444749 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (13619:ℚ) := by decide +kernel
  have hratR : ((((6733461922798469 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((13457404624444749 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13619:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1610 : ((((3369110913497827 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13627 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13619 < q → q < 13627 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13627).mp (by decide +kernel))) hgap
  have hprev := thV_1609
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13627:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3369110913497827 : ℚ) / 250000000000) ≤ ((6733461922798469 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (13627:ℚ) := by decide +kernel
  have hratR : ((((3369110913497827 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((6733461922798469 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13627:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1611 : ((((6742981951295557 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13633 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13627 < q → q < 13633 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13633).mp (by decide +kernel))) hgap
  have hprev := thV_1610
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13633:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6742981951295557 : ℚ) / 500000000000) ≤ ((3369110913497827 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (13633:ℚ) := by decide +kernel
  have hratR : ((((6742981951295557 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((3369110913497827 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13633:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1612 : ((((1349548532412559 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13649 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13633 < q → q < 13649 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13649).mp (by decide +kernel))) hgap
  have hprev := thV_1611
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13649:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1349548532412559 : ℚ) / 100000000000) ≤ ((6742981951295557 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (13649:ℚ) := by decide +kernel
  have hratR : ((((1349548532412559 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((6742981951295557 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13649:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1613 : ((((13505008209896363 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13669 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13649 < q → q < 13669 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13669).mp (by decide +kernel))) hgap
  have hprev := thV_1612
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13669:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13505008209896363 : ℚ) / 1000000000000) ≤ ((1349548532412559 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (13669:ℚ) := by decide +kernel
  have hratR : ((((13505008209896363 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1349548532412559 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13669:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1614 : ((((13514531826982073 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13679 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13669 < q → q < 13679 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13679).mp (by decide +kernel))) hgap
  have hprev := thV_1613
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13679:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13514531826982073 : ℚ) / 1000000000000) ≤ ((13505008209896363 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (13679:ℚ) := by decide +kernel
  have hratR : ((((13514531826982073 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((13505008209896363 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13679:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1615 : ((((13524055590266613 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13681 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13679 < q → q < 13681 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13681).mp (by decide +kernel))) hgap
  have hprev := thV_1614
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13681:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13524055590266613 : ℚ) / 1000000000000) ≤ ((13514531826982073 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (13681:ℚ) := by decide +kernel
  have hratR : ((((13524055590266613 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((13514531826982073 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13681:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1616 : ((((3383394948004861 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13687 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13681 < q → q < 13687 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13687).mp (by decide +kernel))) hgap
  have hprev := thV_1615
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13687:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3383394948004861 : ℚ) / 250000000000) ≤ ((13524055590266613 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (13687:ℚ) := by decide +kernel
  have hratR : ((((3383394948004861 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((13524055590266613 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13687:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1617 : ((((6771552142988849 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13691 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13687 < q → q < 13691 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13691).mp (by decide +kernel))) hgap
  have hprev := thV_1616
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13691:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6771552142988849 : ℚ) / 500000000000) ≤ ((3383394948004861 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (13691:ℚ) := by decide +kernel
  have hratR : ((((6771552142988849 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((3383394948004861 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13691:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1618 : ((((271052578520133 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13693 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13691 < q → q < 13693 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13693).mp (by decide +kernel))) hgap
  have hprev := thV_1617
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13693:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((271052578520133 : ℚ) / 20000000000) ≤ ((6771552142988849 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (13693:ℚ) := by decide +kernel
  have hratR : ((((271052578520133 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ ((((6771552142988849 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13693:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1619 : ((((2712430771622601 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13697 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13693 < q → q < 13697 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13697).mp (by decide +kernel))) hgap
  have hprev := thV_1618
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13697:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2712430771622601 : ℚ) / 200000000000) ≤ ((271052578520133 : ℚ) / 20000000000) + Work.RHContract.RegionI.logLowQ (13697:ℚ) := by decide +kernel
  have hratR : ((((2712430771622601 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((271052578520133 : ℚ) / 20000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13697:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1620 : ((((13571679665940061 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13709 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13697 < q → q < 13709 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13709).mp (by decide +kernel))) hgap
  have hprev := thV_1619
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13709:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13571679665940061 : ℚ) / 1000000000000) ≤ ((2712430771622601 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (13709:ℚ) := by decide +kernel
  have hratR : ((((13571679665940061 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2712430771622601 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13709:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1621 : ((((6790602809823019 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13711 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13709 < q → q < 13711 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13711).mp (by decide +kernel))) hgap
  have hprev := thV_1620
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13711:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6790602809823019 : ℚ) / 500000000000) ≤ ((13571679665940061 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (13711:ℚ) := by decide +kernel
  have hratR : ((((6790602809823019 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((13571679665940061 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13711:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1622 : ((((13590732302427579 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13721 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13711 < q → q < 13721 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13721).mp (by decide +kernel))) hgap
  have hprev := thV_1621
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13721:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13590732302427579 : ℚ) / 1000000000000) ≤ ((6790602809823019 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (13721:ℚ) := by decide +kernel
  have hratR : ((((13590732302427579 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((6790602809823019 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13721:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1623 : ((((13600259130960469 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13723 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13721 < q → q < 13723 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13723).mp (by decide +kernel))) hgap
  have hprev := thV_1622
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13723:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13600259130960469 : ℚ) / 1000000000000) ≤ ((13590732302427579 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (13723:ℚ) := by decide +kernel
  have hratR : ((((13600259130960469 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((13590732302427579 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13723:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1624 : ((((13609786396619987 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13729 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13723 < q → q < 13729 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13729).mp (by decide +kernel))) hgap
  have hprev := thV_1623
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13729:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13609786396619987 : ℚ) / 1000000000000) ≤ ((13600259130960469 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (13729:ℚ) := by decide +kernel
  have hratR : ((((13609786396619987 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((13600259130960469 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13729:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1625 : ((((1361931526344433 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13751 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13729 < q → q < 13751 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13751).mp (by decide +kernel))) hgap
  have hprev := thV_1624
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13751:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1361931526344433 : ℚ) / 100000000000) ≤ ((13609786396619987 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (13751:ℚ) := by decide +kernel
  have hratR : ((((1361931526344433 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((13609786396619987 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13751:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1626 : ((((13628844566505411 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13757 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13751 < q → q < 13757 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13757).mp (by decide +kernel))) hgap
  have hprev := thV_1625
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13757:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13628844566505411 : ℚ) / 1000000000000) ≤ ((1361931526344433 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (13757:ℚ) := by decide +kernel
  have hratR : ((((13628844566505411 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1361931526344433 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13757:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1627 : ((((13638374014936459 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13759 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13757 < q → q < 13759 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13759).mp (by decide +kernel))) hgap
  have hprev := thV_1626
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13759:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13638374014936459 : ℚ) / 1000000000000) ≤ ((13628844566505411 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (13759:ℚ) := by decide +kernel
  have hratR : ((((13638374014936459 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((13628844566505411 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13759:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1628 : ((((13647903754044059 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13763 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13759 < q → q < 13763 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13763).mp (by decide +kernel))) hgap
  have hprev := thV_1627
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13763:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13647903754044059 : ℚ) / 1000000000000) ≤ ((13638374014936459 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (13763:ℚ) := by decide +kernel
  have hratR : ((((13647903754044059 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((13638374014936459 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13763:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1629 : ((((6828717400075777 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13781 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13763 < q → q < 13781 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13781).mp (by decide +kernel))) hgap
  have hprev := thV_1628
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13781:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6828717400075777 : ℚ) / 500000000000) ≤ ((13647903754044059 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (13781:ℚ) := by decide +kernel
  have hratR : ((((6828717400075777 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((13647903754044059 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13781:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1630 : ((((854185401662501 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13789 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13781 < q → q < 13789 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13789).mp (by decide +kernel))) hgap
  have hprev := thV_1629
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13789:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((854185401662501 : ℚ) / 62500000000) ≤ ((6828717400075777 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (13789:ℚ) := by decide +kernel
  have hratR : ((((854185401662501 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((6828717400075777 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13789:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1631 : ((((3419124694500347 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13799 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13789 < q → q < 13799 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13799).mp (by decide +kernel))) hgap
  have hprev := thV_1630
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13799:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3419124694500347 : ℚ) / 250000000000) ≤ ((854185401662501 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (13799:ℚ) := by decide +kernel
  have hratR : ((((3419124694500347 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((854185401662501 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13799:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1632 : ((((3421507927246731 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13807 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13799 < q → q < 13807 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13807).mp (by decide +kernel))) hgap
  have hprev := thV_1631
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13807:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3421507927246731 : ℚ) / 250000000000) ≤ ((3419124694500347 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (13807:ℚ) := by decide +kernel
  have hratR : ((((3421507927246731 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((3419124694500347 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13807:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1633 : ((((13695566232099009 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13829 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13807 < q → q < 13829 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13829).mp (by decide +kernel))) hgap
  have hprev := thV_1632
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13829:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13695566232099009 : ℚ) / 1000000000000) ≤ ((3421507927246731 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (13829:ℚ) := by decide +kernel
  have hratR : ((((13695566232099009 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3421507927246731 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13829:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1634 : ((((6852550449912127 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13831 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13829 < q → q < 13831 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13831).mp (by decide +kernel))) hgap
  have hprev := thV_1633
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13831:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6852550449912127 : ℚ) / 500000000000) ≤ ((13695566232099009 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (13831:ℚ) := by decide +kernel
  have hratR : ((((6852550449912127 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((13695566232099009 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13831:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1635 : ((((13714636290301771 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13841 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13831 < q → q < 13841 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13841).mp (by decide +kernel))) hgap
  have hprev := thV_1634
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13841:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13714636290301771 : ℚ) / 1000000000000) ≤ ((6852550449912127 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (13841:ℚ) := by decide +kernel
  have hratR : ((((13714636290301771 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((6852550449912127 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13841:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1636 : ((((686208649020923 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13859 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13841 < q → q < 13859 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13859).mp (by decide +kernel))) hgap
  have hprev := thV_1635
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13859:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((686208649020923 : ℚ) / 50000000000) ≤ ((13714636290301771 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (13859:ℚ) := by decide +kernel
  have hratR : ((((686208649020923 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((13714636290301771 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13859:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1637 : ((((13733710680199161 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13873 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13859 < q → q < 13873 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13873).mp (by decide +kernel))) hgap
  have hprev := thV_1636
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13873:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13733710680199161 : ℚ) / 1000000000000) ≤ ((686208649020923 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (13873:ℚ) := by decide +kernel
  have hratR : ((((13733710680199161 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((686208649020923 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13873:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1638 : ((((1717906083533519 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13877 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13873 < q → q < 13877 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13877).mp (by decide +kernel))) hgap
  have hprev := thV_1637
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13877:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1717906083533519 : ℚ) / 125000000000) ≤ ((13733710680199161 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (13877:ℚ) := by decide +kernel
  have hratR : ((((1717906083533519 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((13733710680199161 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13877:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1639 : ((((859549175028133 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13879 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13877 < q → q < 13879 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13879).mp (by decide +kernel))) hgap
  have hprev := thV_1638
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13879:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((859549175028133 : ℚ) / 62500000000) ≤ ((1717906083533519 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (13879:ℚ) := by decide +kernel
  have hratR : ((((859549175028133 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((1717906083533519 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13879:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1640 : ((((13762325220795783 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13883 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13879 < q → q < 13883 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13883).mp (by decide +kernel))) hgap
  have hprev := thV_1639
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13883:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13762325220795783 : ℚ) / 1000000000000) ≤ ((859549175028133 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (13883:ℚ) := by decide +kernel
  have hratR : ((((13762325220795783 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((859549175028133 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13883:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1641 : ((((688593246842569 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13901 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13883 < q → q < 13901 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13901).mp (by decide +kernel))) hgap
  have hprev := thV_1640
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13901:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((688593246842569 : ℚ) / 50000000000) ≤ ((13762325220795783 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (13901:ℚ) := by decide +kernel
  have hratR : ((((688593246842569 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((13762325220795783 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13901:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1642 : ((((1378140479677117 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13903 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13901 < q → q < 13903 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13903).mp (by decide +kernel))) hgap
  have hprev := thV_1641
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13903:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1378140479677117 : ℚ) / 100000000000) ≤ ((688593246842569 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (13903:ℚ) := by decide +kernel
  have hratR : ((((1378140479677117 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((688593246842569 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13903:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1643 : ((((13790944944357269 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13907 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13903 < q → q < 13907 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13907).mp (by decide +kernel))) hgap
  have hprev := thV_1642
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13907:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13790944944357269 : ℚ) / 1000000000000) ≤ ((1378140479677117 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (13907:ℚ) := by decide +kernel
  have hratR : ((((13790944944357269 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1378140479677117 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13907:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1644 : ((((13800485523287731 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13913 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13907 < q → q < 13913 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13913).mp (by decide +kernel))) hgap
  have hprev := thV_1643
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13913:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13800485523287731 : ℚ) / 1000000000000) ≤ ((13790944944357269 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (13913:ℚ) := by decide +kernel
  have hratR : ((((13800485523287731 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((13790944944357269 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13913:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1645 : ((((690501333852737 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13921 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13913 < q → q < 13921 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13921).mp (by decide +kernel))) hgap
  have hprev := thV_1644
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13921:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((690501333852737 : ℚ) / 50000000000) ≤ ((13800485523287731 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (13921:ℚ) := by decide +kernel
  have hratR : ((((690501333852737 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((13800485523287731 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13921:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1646 : ((((6909784274451533 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13931 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13921 < q → q < 13931 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13931).mp (by decide +kernel))) hgap
  have hprev := thV_1645
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13931:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6909784274451533 : ℚ) / 500000000000) ≤ ((690501333852737 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (13931:ℚ) := by decide +kernel
  have hratR : ((((6909784274451533 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((690501333852737 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13931:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1647 : ((((69145552821529 : ℚ) / 5000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13933 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13931 < q → q < 13933 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13933).mp (by decide +kernel))) hgap
  have hprev := thV_1646
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13933:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((69145552821529 : ℚ) / 5000000000) ≤ ((6909784274451533 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (13933:ℚ) := by decide +kernel
  have hratR : ((((69145552821529 : ℚ) / 5000000000) : ℚ) : ℝ) ≤ ((((6909784274451533 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13933:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1648 : ((((6919327365277681 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13963 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13933 < q → q < 13963 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13963).mp (by decide +kernel))) hgap
  have hprev := thV_1647
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13963:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6919327365277681 : ℚ) / 500000000000) ≤ ((69145552821529 : ℚ) / 5000000000) + Work.RHContract.RegionI.logLowQ (13963:ℚ) := by decide +kernel
  have hratR : ((((6919327365277681 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((69145552821529 : ℚ) / 5000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13963:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1649 : ((((1731024897904411 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13967 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13963 < q → q < 13967 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13967).mp (by decide +kernel))) hgap
  have hprev := thV_1648
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13967:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1731024897904411 : ℚ) / 125000000000) ≤ ((6919327365277681 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (13967:ℚ) := by decide +kernel
  have hratR : ((((1731024897904411 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((6919327365277681 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13967:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1650 : ((((13857745781531829 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13997 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13967 < q → q < 13997 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13997).mp (by decide +kernel))) hgap
  have hprev := thV_1649
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13997:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13857745781531829 : ℚ) / 1000000000000) ≤ ((1731024897904411 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (13997:ℚ) := by decide +kernel
  have hratR : ((((13857745781531829 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1731024897904411 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13997:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1651 : ((((3466823130676481 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((13999 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13997 < q → q < 13999 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13999).mp (by decide +kernel))) hgap
  have hprev := thV_1650
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (13999:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3466823130676481 : ℚ) / 250000000000) ≤ ((13857745781531829 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (13999:ℚ) := by decide +kernel
  have hratR : ((((3466823130676481 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((13857745781531829 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (13999:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1652 : ((((693841998898087 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14009 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 13999 < q → q < 14009 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14009).mp (by decide +kernel))) hgap
  have hprev := thV_1651
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14009:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((693841998898087 : ℚ) / 50000000000) ≤ ((3466823130676481 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (14009:ℚ) := by decide +kernel
  have hratR : ((((693841998898087 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((3466823130676481 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14009:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1653 : ((((13886387575972731 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14011 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14009 < q → q < 14011 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14011).mp (by decide +kernel))) hgap
  have hprev := thV_1652
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14011:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13886387575972731 : ℚ) / 1000000000000) ≤ ((693841998898087 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (14011:ℚ) := by decide +kernel
  have hratR : ((((13886387575972731 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((693841998898087 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14011:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1654 : ((((1389593645786407 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14029 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14011 < q → q < 14029 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14029).mp (by decide +kernel))) hgap
  have hprev := thV_1653
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14029:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1389593645786407 : ℚ) / 100000000000) ≤ ((13886387575972731 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (14029:ℚ) := by decide +kernel
  have hratR : ((((1389593645786407 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((13886387575972731 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14029:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1655 : ((((13905485624838441 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14033 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14029 < q → q < 14033 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14033).mp (by decide +kernel))) hgap
  have hprev := thV_1654
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14033:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13905485624838441 : ℚ) / 1000000000000) ≤ ((1389593645786407 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (14033:ℚ) := by decide +kernel
  have hratR : ((((13905485624838441 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1389593645786407 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14033:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1656 : ((((3478759018420417 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14051 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14033 < q → q < 14051 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14051).mp (by decide +kernel))) hgap
  have hprev := thV_1655
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14051:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3478759018420417 : ℚ) / 250000000000) ≤ ((13905485624838441 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (14051:ℚ) := by decide +kernel
  have hratR : ((((3478759018420417 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((13905485624838441 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14051:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1657 : ((((696229347472481 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14057 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14051 < q → q < 14057 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14057).mp (by decide +kernel))) hgap
  have hprev := thV_1656
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14057:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((696229347472481 : ℚ) / 50000000000) ≤ ((3478759018420417 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (14057:ℚ) := by decide +kernel
  have hratR : ((((696229347472481 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((3478759018420417 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14057:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1658 : ((((3483534705166757 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14071 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14057 < q → q < 14071 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14071).mp (by decide +kernel))) hgap
  have hprev := thV_1657
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14071:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3483534705166757 : ℚ) / 250000000000) ≤ ((696229347472481 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (14071:ℚ) := by decide +kernel
  have hratR : ((((3483534705166757 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((696229347472481 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14071:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1659 : ((((6971845701156783 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14081 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14071 < q → q < 14081 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14081).mp (by decide +kernel))) hgap
  have hprev := thV_1658
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14081:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((6971845701156783 : ℚ) / 500000000000) ≤ ((3483534705166757 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (14081:ℚ) := by decide +kernel
  have hratR : ((((6971845701156783 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((3483534705166757 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14081:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1660 : ((((1744155515748173 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14083 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14081 < q → q < 14083 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14083).mp (by decide +kernel))) hgap
  have hprev := thV_1659
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14083:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1744155515748173 : ℚ) / 125000000000) ≤ ((6971845701156783 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (14083:ℚ) := by decide +kernel
  have hratR : ((((1744155515748173 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((6971845701156783 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14083:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1661 : ((((2792559426729453 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14087 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14083 < q → q < 14087 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14087).mp (by decide +kernel))) hgap
  have hprev := thV_1660
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14087:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2792559426729453 : ℚ) / 200000000000) ≤ ((1744155515748173 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (14087:ℚ) := by decide +kernel
  have hratR : ((((2792559426729453 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((1744155515748173 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14087:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1662 : ((((174654394500637 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14107 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14087 < q → q < 14107 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14107).mp (by decide +kernel))) hgap
  have hprev := thV_1661
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14107:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((174654394500637 : ℚ) / 12500000000) ≤ ((2792559426729453 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (14107:ℚ) := by decide +kernel
  have hratR : ((((174654394500637 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ ((((2792559426729453 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14107:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1663 : ((((13981908535128601 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14143 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14107 < q → q < 14143 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14143).mp (by decide +kernel))) hgap
  have hprev := thV_1662
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14143:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13981908535128601 : ℚ) / 1000000000000) ≤ ((174654394500637 : ℚ) / 12500000000) + Work.RHContract.RegionI.logLowQ (14143:ℚ) := by decide +kernel
  have hratR : ((((13981908535128601 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((174654394500637 : ℚ) / 12500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14143:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1664 : ((((13991465934354417 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14149 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14143 < q → q < 14149 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14149).mp (by decide +kernel))) hgap
  have hprev := thV_1663
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14149:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((13991465934354417 : ℚ) / 1000000000000) ≤ ((13981908535128601 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (14149:ℚ) := by decide +kernel
  have hratR : ((((13991465934354417 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((13981908535128601 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14149:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1665 : ((((14001023616245771 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14153 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14149 < q → q < 14153 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14153).mp (by decide +kernel))) hgap
  have hprev := thV_1664
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14153:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14001023616245771 : ℚ) / 1000000000000) ≤ ((13991465934354417 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (14153:ℚ) := by decide +kernel
  have hratR : ((((14001023616245771 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((13991465934354417 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14153:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1666 : ((((3502645430496419 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14159 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14153 < q → q < 14159 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14159).mp (by decide +kernel))) hgap
  have hprev := thV_1665
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14159:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3502645430496419 : ℚ) / 250000000000) ≤ ((14001023616245771 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (14159:ℚ) := by decide +kernel
  have hratR : ((((3502645430496419 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((14001023616245771 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14159:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1667 : ((((14020140816007463 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14173 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14159 < q → q < 14173 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14173).mp (by decide +kernel))) hgap
  have hprev := thV_1666
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14173:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14020140816007463 : ℚ) / 1000000000000) ≤ ((3502645430496419 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (14173:ℚ) := by decide +kernel
  have hratR : ((((14020140816007463 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3502645430496419 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14173:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1668 : ((((14029700192216201 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14177 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14173 < q → q < 14177 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14177).mp (by decide +kernel))) hgap
  have hprev := thV_1667
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14177:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14029700192216201 : ℚ) / 1000000000000) ≤ ((14020140816007463 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (14177:ℚ) := by decide +kernel
  have hratR : ((((14029700192216201 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((14020140816007463 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14177:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1669 : ((((2807852195633297 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14197 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14177 < q → q < 14197 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14197).mp (by decide +kernel))) hgap
  have hprev := thV_1668
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14197:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2807852195633297 : ℚ) / 200000000000) ≤ ((14029700192216201 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (14197:ℚ) := by decide +kernel
  have hratR : ((((2807852195633297 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((14029700192216201 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14197:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1670 : ((((14048822468242977 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14207 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14197 < q → q < 14207 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14207).mp (by decide +kernel))) hgap
  have hprev := thV_1669
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14207:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14048822468242977 : ℚ) / 1000000000000) ≤ ((2807852195633297 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (14207:ℚ) := by decide +kernel
  have hratR : ((((14048822468242977 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2807852195633297 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14207:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1671 : ((((1405838494326397 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14221 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14207 < q → q < 14221 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14221).mp (by decide +kernel))) hgap
  have hprev := thV_1670
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14221:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1405838494326397 : ℚ) / 100000000000) ≤ ((14048822468242977 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (14221:ℚ) := by decide +kernel
  have hratR : ((((1405838494326397 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((14048822468242977 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14221:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1672 : ((((562717958563901 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14243 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14221 < q → q < 14243 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14243).mp (by decide +kernel))) hgap
  have hprev := thV_1671
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14243:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((562717958563901 : ℚ) / 40000000000) ≤ ((1405838494326397 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (14243:ℚ) := by decide +kernel
  have hratR : ((((562717958563901 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((1405838494326397 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14243:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1673 : ((((14077513406101941 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14249 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14243 < q → q < 14249 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14249).mp (by decide +kernel))) hgap
  have hprev := thV_1672
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14249:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14077513406101941 : ℚ) / 1000000000000) ≤ ((562717958563901 : ℚ) / 40000000000) + Work.RHContract.RegionI.logLowQ (14249:ℚ) := by decide +kernel
  have hratR : ((((14077513406101941 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((562717958563901 : ℚ) / 40000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14249:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1674 : ((((7043538994228617 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14251 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14249 < q → q < 14251 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14251).mp (by decide +kernel))) hgap
  have hprev := thV_1673
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14251:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7043538994228617 : ℚ) / 500000000000) ≤ ((14077513406101941 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (14251:ℚ) := by decide +kernel
  have hratR : ((((7043538994228617 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((14077513406101941 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14251:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1675 : ((((14096644673715307 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14281 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14251 < q → q < 14281 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14281).mp (by decide +kernel))) hgap
  have hprev := thV_1674
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14281:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14096644673715307 : ℚ) / 1000000000000) ≤ ((7043538994228617 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (14281:ℚ) := by decide +kernel
  have hratR : ((((14096644673715307 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((7043538994228617 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14281:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1676 : ((((3526553049724459 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14293 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14281 < q → q < 14293 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14293).mp (by decide +kernel))) hgap
  have hprev := thV_1675
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14293:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3526553049724459 : ℚ) / 250000000000) ≤ ((14096644673715307 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (14293:ℚ) := by decide +kernel
  have hratR : ((((3526553049724459 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((14096644673715307 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14293:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1677 : ((((14115780423478911 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14303 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14293 < q → q < 14303 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14303).mp (by decide +kernel))) hgap
  have hprev := thV_1676
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14303:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14115780423478911 : ℚ) / 1000000000000) ≤ ((3526553049724459 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (14303:ℚ) := by decide +kernel
  have hratR : ((((14115780423478911 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3526553049724459 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14303:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1678 : ((((1412534990574601 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14321 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14303 < q → q < 14321 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14321).mp (by decide +kernel))) hgap
  have hprev := thV_1677
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14321:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1412534990574601 : ℚ) / 100000000000) ≤ ((14115780423478911 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (14321:ℚ) := by decide +kernel
  have hratR : ((((1412534990574601 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((14115780423478911 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14321:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1679 : ((((1413491952765841 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14323 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14321 < q → q < 14323 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14323).mp (by decide +kernel))) hgap
  have hprev := thV_1678
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14323:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1413491952765841 : ℚ) / 100000000000) ≤ ((1412534990574601 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (14323:ℚ) := by decide +kernel
  have hratR : ((((1413491952765841 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((1412534990574601 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14323:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1680 : ((((3536122357200731 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14327 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14323 < q → q < 14327 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14327).mp (by decide +kernel))) hgap
  have hprev := thV_1679
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14327:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3536122357200731 : ℚ) / 250000000000) ≤ ((1413491952765841 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (14327:ℚ) := by decide +kernel
  have hratR : ((((3536122357200731 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((1413491952765841 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14327:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1681 : ((((14154060306646273 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14341 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14327 < q → q < 14341 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14341).mp (by decide +kernel))) hgap
  have hprev := thV_1680
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14341:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14154060306646273 : ℚ) / 1000000000000) ≤ ((3536122357200731 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (14341:ℚ) := by decide +kernel
  have hratR : ((((14154060306646273 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3536122357200731 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14341:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1682 : ((((885226975173937 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14347 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14341 < q → q < 14347 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14347).mp (by decide +kernel))) hgap
  have hprev := thV_1681
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14347:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((885226975173937 : ℚ) / 62500000000) ≤ ((14154060306646273 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (14347:ℚ) := by decide +kernel
  have hratR : ((((885226975173937 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((14154060306646273 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14347:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1683 : ((((14173204431166841 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14369 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14347 < q → q < 14369 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14369).mp (by decide +kernel))) hgap
  have hprev := thV_1682
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14369:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14173204431166841 : ℚ) / 1000000000000) ≤ ((885226975173937 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (14369:ℚ) := by decide +kernel
  have hratR : ((((14173204431166841 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((885226975173937 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14369:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1684 : ((((7091389255731749 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14387 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14369 < q → q < 14387 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14387).mp (by decide +kernel))) hgap
  have hprev := thV_1683
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14387:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7091389255731749 : ℚ) / 500000000000) ≤ ((14173204431166841 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (14387:ℚ) := by decide +kernel
  have hratR : ((((7091389255731749 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((14173204431166841 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14387:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1685 : ((((7096176365382441 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14389 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14387 < q → q < 14389 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14389).mp (by decide +kernel))) hgap
  have hprev := thV_1684
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14389:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7096176365382441 : ℚ) / 500000000000) ≤ ((7091389255731749 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (14389:ℚ) := by decide +kernel
  have hratR : ((((7096176365382441 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((7091389255731749 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14389:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1686 : ((((142019277836891 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14401 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14389 < q → q < 14401 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14401).mp (by decide +kernel))) hgap
  have hprev := thV_1685
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14401:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((142019277836891 : ℚ) / 10000000000) ≤ ((7096176365382441 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (14401:ℚ) := by decide +kernel
  have hratR : ((((142019277836891 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ ((((7096176365382441 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14401:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1687 : ((((7105751626582141 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14407 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14401 < q → q < 14407 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14407).mp (by decide +kernel))) hgap
  have hprev := thV_1686
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14407:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7105751626582141 : ℚ) / 500000000000) ≤ ((142019277836891 : ℚ) / 10000000000) + Work.RHContract.RegionI.logLowQ (14407:ℚ) := by decide +kernel
  have hratR : ((((7105751626582141 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((142019277836891 : ℚ) / 10000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14407:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1688 : ((((14221079000243741 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14411 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14407 < q → q < 14411 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14411).mp (by decide +kernel))) hgap
  have hprev := thV_1687
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14411:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14221079000243741 : ℚ) / 1000000000000) ≤ ((7105751626582141 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (14411:ℚ) := by decide +kernel
  have hratR : ((((14221079000243741 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((7105751626582141 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14411:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1689 : ((((3557663825575167 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14419 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14411 < q → q < 14419 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14419).mp (by decide +kernel))) hgap
  have hprev := thV_1688
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14419:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3557663825575167 : ℚ) / 250000000000) ≤ ((14221079000243741 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (14419:ℚ) := by decide +kernel
  have hratR : ((((3557663825575167 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((14221079000243741 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14419:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1690 : ((((1780028985216359 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14423 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14419 < q → q < 14423 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14423).mp (by decide +kernel))) hgap
  have hprev := thV_1689
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14423:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1780028985216359 : ℚ) / 125000000000) ≤ ((3557663825575167 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (14423:ℚ) := by decide +kernel
  have hratR : ((((1780028985216359 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((3557663825575167 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14423:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1691 : ((((3478957279218 : ℚ) / 244140625) : ℚ) : ℝ) ≤ Chebyshev.theta ((14431 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14423 < q → q < 14431 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14431).mp (by decide +kernel))) hgap
  have hprev := thV_1690
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14431:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3478957279218 : ℚ) / 244140625) ≤ ((1780028985216359 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (14431:ℚ) := by decide +kernel
  have hratR : ((((3478957279218 : ℚ) / 244140625) : ℚ) : ℝ) ≤ ((((1780028985216359 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14431:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1692 : ((((7129693282654089 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14437 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14431 < q → q < 14437 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14437).mp (by decide +kernel))) hgap
  have hprev := thV_1691
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14437:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7129693282654089 : ℚ) / 500000000000) ≤ ((3478957279218 : ℚ) / 244140625) + Work.RHContract.RegionI.logLowQ (14437:ℚ) := by decide +kernel
  have hratR : ((((7129693282654089 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((3478957279218 : ℚ) / 244140625) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14437:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1693 : ((((1783620600920541 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14447 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14437 < q → q < 14447 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14447).mp (by decide +kernel))) hgap
  have hprev := thV_1692
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14447:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1783620600920541 : ℚ) / 125000000000) ≤ ((7129693282654089 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (14447:ℚ) := by decide +kernel
  have hratR : ((((1783620600920541 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((7129693282654089 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14447:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1694 : ((((7139271593923971 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14449 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14447 < q → q < 14449 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14449).mp (by decide +kernel))) hgap
  have hprev := thV_1693
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14449:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7139271593923971 : ℚ) / 500000000000) ≤ ((1783620600920541 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (14449:ℚ) := by decide +kernel
  have hratR : ((((7139271593923971 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1783620600920541 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14449:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1695 : ((((14288122398494177 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14461 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14449 < q → q < 14461 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14461).mp (by decide +kernel))) hgap
  have hprev := thV_1694
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14461:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14288122398494177 : ℚ) / 1000000000000) ≤ ((7139271593923971 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (14461:ℚ) := by decide +kernel
  have hratR : ((((14288122398494177 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((7139271593923971 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14461:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1696 : ((((14297702853093579 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14479 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14461 < q → q < 14479 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14479).mp (by decide +kernel))) hgap
  have hprev := thV_1695
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14479:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14297702853093579 : ℚ) / 1000000000000) ≤ ((14288122398494177 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (14479:ℚ) := by decide +kernel
  have hratR : ((((14297702853093579 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((14288122398494177 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14479:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1697 : ((((715364199905501 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14489 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14479 < q → q < 14489 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14489).mp (by decide +kernel))) hgap
  have hprev := thV_1696
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14489:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((715364199905501 : ℚ) / 50000000000) ≤ ((14297702853093579 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (14489:ℚ) := by decide +kernel
  have hratR : ((((715364199905501 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((14297702853093579 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14489:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1698 : ((((71584330544551 : ℚ) / 5000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14503 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14489 < q → q < 14503 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14503).mp (by decide +kernel))) hgap
  have hprev := thV_1697
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14503:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((71584330544551 : ℚ) / 5000000000) ≤ ((715364199905501 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (14503:ℚ) := by decide +kernel
  have hratR : ((((71584330544551 : ℚ) / 5000000000) : ℚ) : ℝ) ≤ ((((715364199905501 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14503:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1699 : ((((111925385330643 : ℚ) / 7812500000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14519 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14503 < q → q < 14519 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14519).mp (by decide +kernel))) hgap
  have hprev := thV_1698
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14519:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((111925385330643 : ℚ) / 7812500000) ≤ ((71584330544551 : ℚ) / 5000000000) + Work.RHContract.RegionI.logLowQ (14519:ℚ) := by decide +kernel
  have hratR : ((((111925385330643 : ℚ) / 7812500000) : ℚ) : ℝ) ≤ ((((71584330544551 : ℚ) / 5000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14519:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1700 : ((((286720669990471 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14533 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14519 < q → q < 14533 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14533).mp (by decide +kernel))) hgap
  have hprev := thV_1699
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14533:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((286720669990471 : ℚ) / 20000000000) ≤ ((111925385330643 : ℚ) / 7812500000) + Work.RHContract.RegionI.logLowQ (14533:ℚ) := by decide +kernel
  have hratR : ((((286720669990471 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ ((((111925385330643 : ℚ) / 7812500000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14533:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1701 : ((((14345617951922597 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14537 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14533 < q → q < 14537 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14537).mp (by decide +kernel))) hgap
  have hprev := thV_1700
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14537:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14345617951922597 : ℚ) / 1000000000000) ≤ ((286720669990471 : ℚ) / 20000000000) + Work.RHContract.RegionI.logLowQ (14537:ℚ) := by decide +kernel
  have hratR : ((((14345617951922597 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((286720669990471 : ℚ) / 20000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14537:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1702 : ((((2871040563395279 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14543 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14537 < q → q < 14543 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14543).mp (by decide +kernel))) hgap
  have hprev := thV_1701
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14543:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2871040563395279 : ℚ) / 200000000000) ≤ ((14345617951922597 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (14543:ℚ) := by decide +kernel
  have hratR : ((((2871040563395279 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((14345617951922597 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14543:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1703 : ((((14364788094514731 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14549 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14543 < q → q < 14549 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14549).mp (by decide +kernel))) hgap
  have hprev := thV_1702
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14549:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14364788094514731 : ℚ) / 1000000000000) ≤ ((2871040563395279 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (14549:ℚ) := by decide +kernel
  have hratR : ((((14364788094514731 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2871040563395279 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14549:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1704 : ((((14374373509510111 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14551 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14549 < q → q < 14551 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14551).mp (by decide +kernel))) hgap
  have hprev := thV_1703
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14551:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14374373509510111 : ℚ) / 1000000000000) ≤ ((14364788094514731 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (14551:ℚ) := by decide +kernel
  have hratR : ((((14374373509510111 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((14364788094514731 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14551:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1705 : ((((449498729273853 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14557 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14551 < q → q < 14557 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14557).mp (by decide +kernel))) hgap
  have hprev := thV_1704
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14557:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((449498729273853 : ℚ) / 31250000000) ≤ ((14374373509510111 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (14557:ℚ) := by decide +kernel
  have hratR : ((((449498729273853 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((14374373509510111 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14557:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1706 : ((((14393545438760627 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14561 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14557 < q → q < 14561 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14561).mp (by decide +kernel))) hgap
  have hprev := thV_1705
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14561:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14393545438760627 : ℚ) / 1000000000000) ≤ ((449498729273853 : ℚ) / 31250000000) + Work.RHContract.RegionI.logLowQ (14561:ℚ) := by decide +kernel
  have hratR : ((((14393545438760627 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((449498729273853 : ℚ) / 31250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14561:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1707 : ((((1440313167810173 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14563 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14561 < q → q < 14563 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14563).mp (by decide +kernel))) hgap
  have hprev := thV_1706
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14563:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1440313167810173 : ℚ) / 100000000000) ≤ ((14393545438760627 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (14563:ℚ) := by decide +kernel
  have hratR : ((((1440313167810173 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((14393545438760627 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14563:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1708 : ((((7206359919138807 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14591 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14563 < q → q < 14591 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14591).mp (by decide +kernel))) hgap
  have hprev := thV_1707
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14591:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7206359919138807 : ℚ) / 500000000000) ≤ ((1440313167810173 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (14591:ℚ) := by decide +kernel
  have hratR : ((((7206359919138807 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1440313167810173 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14591:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1709 : ((((7211154067757451 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14593 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14591 < q → q < 14593 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14593).mp (by decide +kernel))) hgap
  have hprev := thV_1708
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14593:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7211154067757451 : ℚ) / 500000000000) ≤ ((7206359919138807 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (14593:ℚ) := by decide +kernel
  have hratR : ((((7211154067757451 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((7206359919138807 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14593:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1710 : ((((721594917482097 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14621 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14593 < q → q < 14621 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14621).mp (by decide +kernel))) hgap
  have hprev := thV_1709
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14621:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((721594917482097 : ℚ) / 50000000000) ≤ ((7211154067757451 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (14621:ℚ) := by decide +kernel
  have hratR : ((((721594917482097 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((7211154067757451 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14621:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1711 : ((((14441488974053447 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14627 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14621 < q → q < 14627 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14627).mp (by decide +kernel))) hgap
  have hprev := thV_1710
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14627:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14441488974053447 : ℚ) / 1000000000000) ≤ ((721594917482097 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (14627:ℚ) := by decide +kernel
  have hratR : ((((14441488974053447 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((721594917482097 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14627:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1712 : ((((2890215947037809 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14629 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14627 < q → q < 14629 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14629).mp (by decide +kernel))) hgap
  have hprev := thV_1711
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14629:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2890215947037809 : ℚ) / 200000000000) ≤ ((14441488974053447 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (14629:ℚ) := by decide +kernel
  have hratR : ((((2890215947037809 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((14441488974053447 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14629:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1713 : ((((7230335384858379 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14633 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14629 < q → q < 14633 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14633).mp (by decide +kernel))) hgap
  have hprev := thV_1712
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14633:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7230335384858379 : ℚ) / 500000000000) ≤ ((2890215947037809 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (14633:ℚ) := by decide +kernel
  have hratR : ((((7230335384858379 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((2890215947037809 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14633:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1714 : ((((289405244283851 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14639 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14633 < q → q < 14639 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14639).mp (by decide +kernel))) hgap
  have hprev := thV_1713
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14639:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((289405244283851 : ℚ) / 20000000000) ≤ ((7230335384858379 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (14639:ℚ) := by decide +kernel
  have hratR : ((((289405244283851 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ ((((7230335384858379 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14639:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1715 : ((((1809981826820101 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14653 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14639 < q → q < 14653 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14653).mp (by decide +kernel))) hgap
  have hprev := thV_1714
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14653:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1809981826820101 : ℚ) / 125000000000) ≤ ((289405244283851 : ℚ) / 20000000000) + Work.RHContract.RegionI.logLowQ (14653:ℚ) := by decide +kernel
  have hratR : ((((1809981826820101 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((289405244283851 : ℚ) / 20000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14653:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1716 : ((((905590455492091 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14657 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14653 < q → q < 14657 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14657).mp (by decide +kernel))) hgap
  have hprev := thV_1715
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14657:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((905590455492091 : ℚ) / 62500000000) ≤ ((1809981826820101 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (14657:ℚ) := by decide +kernel
  have hratR : ((((905590455492091 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((1809981826820101 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14657:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1717 : ((((3624760194893141 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14669 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14657 < q → q < 14669 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14669).mp (by decide +kernel))) hgap
  have hprev := thV_1716
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14669:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3624760194893141 : ℚ) / 250000000000) ≤ ((905590455492091 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (14669:ℚ) := by decide +kernel
  have hratR : ((((3624760194893141 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((905590455492091 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14669:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1718 : ((((14508635225210147 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14683 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14669 < q → q < 14683 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14683).mp (by decide +kernel))) hgap
  have hprev := thV_1717
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14683:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14508635225210147 : ℚ) / 1000000000000) ≤ ((3624760194893141 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (14683:ℚ) := by decide +kernel
  have hratR : ((((14508635225210147 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3624760194893141 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14683:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1719 : ((((14518230759950009 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14699 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14683 < q → q < 14699 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14699).mp (by decide +kernel))) hgap
  have hprev := thV_1718
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14699:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14518230759950009 : ℚ) / 1000000000000) ≤ ((14508635225210147 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (14699:ℚ) := by decide +kernel
  have hratR : ((((14518230759950009 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((14508635225210147 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14699:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1720 : ((((14527827246682327 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14713 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14699 < q → q < 14713 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14713).mp (by decide +kernel))) hgap
  have hprev := thV_1719
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14713:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14527827246682327 : ℚ) / 1000000000000) ≤ ((14518230759950009 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (14713:ℚ) := by decide +kernel
  have hratR : ((((14527827246682327 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((14518230759950009 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14713:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1721 : ((((14537424005246111 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14717 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14713 < q → q < 14717 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14717).mp (by decide +kernel))) hgap
  have hprev := thV_1720
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14717:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14537424005246111 : ℚ) / 1000000000000) ≤ ((14527827246682327 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (14717:ℚ) := by decide +kernel
  have hratR : ((((14537424005246111 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((14527827246682327 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14717:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1722 : ((((14547021171418597 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14723 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14717 < q → q < 14723 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14723).mp (by decide +kernel))) hgap
  have hprev := thV_1721
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14723:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14547021171418597 : ℚ) / 1000000000000) ≤ ((14537424005246111 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (14723:ℚ) := by decide +kernel
  have hratR : ((((14547021171418597 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((14537424005246111 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14723:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1723 : ((((1819577360101379 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14731 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14723 < q → q < 14731 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14731).mp (by decide +kernel))) hgap
  have hprev := thV_1722
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14731:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1819577360101379 : ℚ) / 125000000000) ≤ ((14547021171418597 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (14731:ℚ) := by decide +kernel
  have hratR : ((((1819577360101379 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((14547021171418597 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14731:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1724 : ((((2913243399484973 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14737 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14731 < q → q < 14737 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14737).mp (by decide +kernel))) hgap
  have hprev := thV_1723
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14737:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2913243399484973 : ℚ) / 200000000000) ≤ ((1819577360101379 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (14737:ℚ) := by decide +kernel
  have hratR : ((((2913243399484973 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((1819577360101379 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14737:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1725 : ((((3643953846356883 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14741 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14737 < q → q < 14741 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14741).mp (by decide +kernel))) hgap
  have hprev := thV_1724
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14741:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3643953846356883 : ℚ) / 250000000000) ≤ ((2913243399484973 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (14741:ℚ) := by decide +kernel
  have hratR : ((((3643953846356883 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((2913243399484973 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14741:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1726 : ((((14585414180375403 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14747 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14741 < q → q < 14747 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14747).mp (by decide +kernel))) hgap
  have hprev := thV_1725
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14747:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14585414180375403 : ℚ) / 1000000000000) ≤ ((3643953846356883 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (14747:ℚ) := by decide +kernel
  have hratR : ((((14585414180375403 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3643953846356883 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14747:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1727 : ((((14595013382102941 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14753 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14747 < q → q < 14753 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14753).mp (by decide +kernel))) hgap
  have hprev := thV_1726
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14753:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14595013382102941 : ℚ) / 1000000000000) ≤ ((14585414180375403 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (14753:ℚ) := by decide +kernel
  have hratR : ((((14595013382102941 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((14585414180375403 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14753:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1728 : ((((14604612990444743 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14759 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14753 < q → q < 14759 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14759).mp (by decide +kernel))) hgap
  have hprev := thV_1727
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14759:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14604612990444743 : ℚ) / 1000000000000) ≤ ((14595013382102941 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (14759:ℚ) := by decide +kernel
  have hratR : ((((14604612990444743 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((14595013382102941 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14759:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1729 : ((((14614213140681837 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14767 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14759 < q → q < 14767 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14767).mp (by decide +kernel))) hgap
  have hprev := thV_1728
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14767:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14614213140681837 : ℚ) / 1000000000000) ≤ ((14604612990444743 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (14767:ℚ) := by decide +kernel
  have hratR : ((((14614213140681837 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((14604612990444743 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14767:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1730 : ((((7311906780878249 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14771 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14767 < q → q < 14771 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14771).mp (by decide +kernel))) hgap
  have hprev := thV_1729
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14771:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7311906780878249 : ℚ) / 500000000000) ≤ ((14614213140681837 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (14771:ℚ) := by decide +kernel
  have hratR : ((((7311906780878249 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((14614213140681837 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14771:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1731 : ((((14633414524286333 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14779 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14771 < q → q < 14779 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14779).mp (by decide +kernel))) hgap
  have hprev := thV_1730
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14779:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14633414524286333 : ℚ) / 1000000000000) ≤ ((7311906780878249 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (14779:ℚ) := by decide +kernel
  have hratR : ((((14633414524286333 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((7311906780878249 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14779:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1732 : ((((7321507878716927 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14783 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14779 < q → q < 14783 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14783).mp (by decide +kernel))) hgap
  have hprev := thV_1731
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14783:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7321507878716927 : ℚ) / 500000000000) ≤ ((14633414524286333 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (14783:ℚ) := by decide +kernel
  have hratR : ((((7321507878716927 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((14633414524286333 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14783:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1733 : ((((14652617937166977 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14797 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14783 < q → q < 14797 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14797).mp (by decide +kernel))) hgap
  have hprev := thV_1732
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14797:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14652617937166977 : ℚ) / 1000000000000) ≤ ((7321507878716927 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (14797:ℚ) := by decide +kernel
  have hratR : ((((14652617937166977 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((7321507878716927 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14797:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1734 : ((((14662221197616179 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14813 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14797 < q → q < 14813 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14813).mp (by decide +kernel))) hgap
  have hprev := thV_1733
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14813:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14662221197616179 : ℚ) / 1000000000000) ≤ ((14652617937166977 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (14813:ℚ) := by decide +kernel
  have hratR : ((((14662221197616179 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((14652617937166977 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14813:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1735 : ((((3667956249496439 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14821 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14813 < q → q < 14821 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14821).mp (by decide +kernel))) hgap
  have hprev := thV_1734
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14821:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3667956249496439 : ℚ) / 250000000000) ≤ ((14662221197616179 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (14821:ℚ) := by decide +kernel
  have hratR : ((((3667956249496439 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((14662221197616179 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14821:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1736 : ((((7340714601552197 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14827 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14821 < q → q < 14827 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14827).mp (by decide +kernel))) hgap
  have hprev := thV_1735
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14827:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7340714601552197 : ℚ) / 500000000000) ≤ ((3667956249496439 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (14827:ℚ) := by decide +kernel
  have hratR : ((((7340714601552197 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((3667956249496439 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14827:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1737 : ((((3672758419491189 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14831 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14827 < q → q < 14831 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14831).mp (by decide +kernel))) hgap
  have hprev := thV_1736
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14831:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3672758419491189 : ℚ) / 250000000000) ≤ ((7340714601552197 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (14831:ℚ) := by decide +kernel
  have hratR : ((((3672758419491189 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((7340714601552197 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14831:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1738 : ((((14700638961614001 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14843 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14831 < q → q < 14843 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14843).mp (by decide +kernel))) hgap
  have hprev := thV_1737
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14843:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14700638961614001 : ℚ) / 1000000000000) ≤ ((3672758419491189 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (14843:ℚ) := by decide +kernel
  have hratR : ((((14700638961614001 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3672758419491189 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14843:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1739 : ((((3677561196023163 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14851 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14843 < q → q < 14851 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14851).mp (by decide +kernel))) hgap
  have hprev := thV_1738
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14851:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3677561196023163 : ℚ) / 250000000000) ≤ ((14700638961614001 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (14851:ℚ) := by decide +kernel
  have hratR : ((((3677561196023163 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((14700638961614001 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14851:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1740 : ((((7359925841679943 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14867 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14851 < q → q < 14867 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14867).mp (by decide +kernel))) hgap
  have hprev := thV_1739
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14867:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7359925841679943 : ℚ) / 500000000000) ≤ ((3677561196023163 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (14867:ℚ) := by decide +kernel
  have hratR : ((((7359925841679943 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((3677561196023163 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14867:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1741 : ((((14729458717144203 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14869 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14867 < q → q < 14869 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14869).mp (by decide +kernel))) hgap
  have hprev := thV_1740
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14869:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14729458717144203 : ℚ) / 1000000000000) ≤ ((7359925841679943 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (14869:ℚ) := by decide +kernel
  have hratR : ((((14729458717144203 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((7359925841679943 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14869:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1742 : ((((14739066423242651 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14879 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14869 < q → q < 14879 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14879).mp (by decide +kernel))) hgap
  have hprev := thV_1741
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14879:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14739066423242651 : ℚ) / 1000000000000) ≤ ((14729458717144203 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (14879:ℚ) := by decide +kernel
  have hratR : ((((14739066423242651 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((14729458717144203 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14879:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1743 : ((((3687168666716787 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14887 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14879 < q → q < 14887 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14887).mp (by decide +kernel))) hgap
  have hprev := thV_1742
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14887:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3687168666716787 : ℚ) / 250000000000) ≤ ((14739066423242651 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (14887:ℚ) := by decide +kernel
  have hratR : ((((3687168666716787 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((14739066423242651 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14887:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1744 : ((((7379141589573179 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14891 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14887 < q → q < 14891 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14891).mp (by decide +kernel))) hgap
  have hprev := thV_1743
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14891:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7379141589573179 : ℚ) / 500000000000) ≤ ((3687168666716787 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (14891:ℚ) := by decide +kernel
  have hratR : ((((7379141589573179 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((3687168666716787 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14891:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1745 : ((((7383946047136179 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14897 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14891 < q → q < 14897 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14897).mp (by decide +kernel))) hgap
  have hprev := thV_1744
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14897:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7383946047136179 : ℚ) / 500000000000) ≤ ((7379141589573179 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (14897:ℚ) := by decide +kernel
  have hratR : ((((7383946047136179 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((7379141589573179 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14897:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1746 : ((((1477750275319491 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14923 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14897 < q → q < 14923 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14923).mp (by decide +kernel))) hgap
  have hprev := thV_1745
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14923:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1477750275319491 : ℚ) / 100000000000) ≤ ((7383946047136179 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (14923:ℚ) := by decide +kernel
  have hratR : ((((1477750275319491 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((7383946047136179 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14923:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1747 : ((((1848389226762573 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14929 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14923 < q → q < 14929 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14929).mp (by decide +kernel))) hgap
  have hprev := thV_1746
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14929:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1848389226762573 : ℚ) / 125000000000) ≤ ((1477750275319491 : ℚ) / 100000000000) + Work.RHContract.RegionI.logLowQ (14929:ℚ) := by decide +kernel
  have hratR : ((((1848389226762573 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((1477750275319491 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14929:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1748 : ((((14796725544619247 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14939 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14929 < q → q < 14939 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14939).mp (by decide +kernel))) hgap
  have hprev := thV_1747
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14939:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14796725544619247 : ℚ) / 1000000000000) ≤ ((1848389226762573 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (14939:ℚ) := by decide +kernel
  have hratR : ((((14796725544619247 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1848389226762573 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14939:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1749 : ((((14806337810505653 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14947 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14939 < q → q < 14947 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14947).mp (by decide +kernel))) hgap
  have hprev := thV_1748
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14947:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14806337810505653 : ℚ) / 1000000000000) ≤ ((14796725544619247 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (14947:ℚ) := by decide +kernel
  have hratR : ((((14806337810505653 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((14796725544619247 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14947:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1750 : ((((14815950343968487 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14951 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14947 < q → q < 14951 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14951).mp (by decide +kernel))) hgap
  have hprev := thV_1749
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14951:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14815950343968487 : ℚ) / 1000000000000) ≤ ((14806337810505653 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (14951:ℚ) := by decide +kernel
  have hratR : ((((14815950343968487 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((14806337810505653 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14951:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1751 : ((((14825563278661767 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14957 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14951 < q → q < 14957 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14957).mp (by decide +kernel))) hgap
  have hprev := thV_1750
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14957:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14825563278661767 : ℚ) / 1000000000000) ≤ ((14815950343968487 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (14957:ℚ) := by decide +kernel
  have hratR : ((((14825563278661767 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((14815950343968487 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14957:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1752 : ((((7417588507666651 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14969 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14957 < q → q < 14969 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14969).mp (by decide +kernel))) hgap
  have hprev := thV_1751
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14969:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7417588507666651 : ℚ) / 500000000000) ≤ ((14825563278661767 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (14969:ℚ) := by decide +kernel
  have hratR : ((((7417588507666651 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((14825563278661767 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14969:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1753 : ((((2968958337366793 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((14983 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14969 < q → q < 14983 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14983).mp (by decide +kernel))) hgap
  have hprev := thV_1752
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (14983:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2968958337366793 : ℚ) / 200000000000) ≤ ((7417588507666651 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (14983:ℚ) := by decide +kernel
  have hratR : ((((2968958337366793 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((7417588507666651 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (14983:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1754 : ((((7427204179300999 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15013 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 14983 < q → q < 15013 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15013).mp (by decide +kernel))) hgap
  have hprev := thV_1753
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15013:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7427204179300999 : ℚ) / 500000000000) ≤ ((2968958337366793 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (15013:ℚ) := by decide +kernel
  have hratR : ((((7427204179300999 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((2968958337366793 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15013:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1755 : ((((7432012648385149 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15017 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15013 < q → q < 15017 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15017).mp (by decide +kernel))) hgap
  have hprev := thV_1754
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15017:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7432012648385149 : ℚ) / 500000000000) ≤ ((7427204179300999 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (15017:ℚ) := by decide +kernel
  have hratR : ((((7432012648385149 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((7427204179300999 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15017:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1756 : ((((14873643166781051 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15031 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15017 < q → q < 15031 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15031).mp (by decide +kernel))) hgap
  have hprev := thV_1755
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15031:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14873643166781051 : ℚ) / 1000000000000) ≤ ((7432012648385149 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (15031:ℚ) := by decide +kernel
  have hratR : ((((14873643166781051 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((7432012648385149 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15031:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1757 : ((((3720815624840883 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15053 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15031 < q → q < 15053 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15053).mp (by decide +kernel))) hgap
  have hprev := thV_1756
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15053:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3720815624840883 : ℚ) / 250000000000) ≤ ((14873643166781051 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (15053:ℚ) := by decide +kernel
  have hratR : ((((3720815624840883 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((14873643166781051 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15053:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1758 : ((((3723220590815091 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15061 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15053 < q → q < 15061 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15061).mp (by decide +kernel))) hgap
  have hprev := thV_1757
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15061:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3723220590815091 : ℚ) / 250000000000) ≤ ((3720815624840883 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (15061:ℚ) := by decide +kernel
  have hratR : ((((3723220590815091 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((3720815624840883 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15061:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1759 : ((((2980500604719959 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15073 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15061 < q → q < 15073 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15073).mp (by decide +kernel))) hgap
  have hprev := thV_1758
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15073:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((2980500604719959 : ℚ) / 200000000000) ≤ ((3723220590815091 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (15073:ℚ) := by decide +kernel
  have hratR : ((((2980500604719959 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((3723220590815091 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15073:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1760 : ((((7456061974639597 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15077 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15073 < q → q < 15077 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15077).mp (by decide +kernel))) hgap
  have hprev := thV_1759
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15077:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7456061974639597 : ℚ) / 500000000000) ≤ ((2980500604719959 : ℚ) / 200000000000) + Work.RHContract.RegionI.logLowQ (15077:ℚ) := by decide +kernel
  have hratR : ((((7456061974639597 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((2980500604719959 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15077:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1761 : ((((7460872636418291 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15083 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15077 < q → q < 15083 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15083).mp (by decide +kernel))) hgap
  have hprev := thV_1760
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15083:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7460872636418291 : ℚ) / 500000000000) ≤ ((7456061974639597 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (15083:ℚ) := by decide +kernel
  have hratR : ((((7460872636418291 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((7456061974639597 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15083:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1762 : ((((14931367126651821 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15091 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15083 < q → q < 15091 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15091).mp (by decide +kernel))) hgap
  have hprev := thV_1761
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15091:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14931367126651821 : ℚ) / 1000000000000) ≤ ((7460872636418291 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (15091:ℚ) := by decide +kernel
  have hratR : ((((14931367126651821 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((7460872636418291 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15091:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1763 : ((((14940989642894217 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15101 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15091 < q → q < 15101 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15101).mp (by decide +kernel))) hgap
  have hprev := thV_1762
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15101:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14940989642894217 : ℚ) / 1000000000000) ≤ ((14931367126651821 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (15101:ℚ) := by decide +kernel
  have hratR : ((((14940989642894217 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((14931367126651821 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15101:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1764 : ((((14950612556382381 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15107 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15101 < q → q < 15107 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15107).mp (by decide +kernel))) hgap
  have hprev := thV_1763
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15107:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14950612556382381 : ℚ) / 1000000000000) ≤ ((14940989642894217 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (15107:ℚ) := by decide +kernel
  have hratR : ((((14950612556382381 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((14940989642894217 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15107:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1765 : ((((7480118198082057 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15121 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15107 < q → q < 15121 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15121).mp (by decide +kernel))) hgap
  have hprev := thV_1764
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15121:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7480118198082057 : ℚ) / 500000000000) ≤ ((14950612556382381 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (15121:ℚ) := by decide +kernel
  have hratR : ((((7480118198082057 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((14950612556382381 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15121:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1766 : ((((7484930448529593 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15131 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15121 < q → q < 15131 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15131).mp (by decide +kernel))) hgap
  have hprev := thV_1765
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15131:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7484930448529593 : ℚ) / 500000000000) ≤ ((7480118198082057 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (15131:ℚ) := by decide +kernel
  have hratR : ((((7484930448529593 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((7480118198082057 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15131:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1767 : ((((14979485794412569 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15137 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15131 < q → q < 15137 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15137).mp (by decide +kernel))) hgap
  have hprev := thV_1766
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15137:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14979485794412569 : ℚ) / 1000000000000) ≤ ((7484930448529593 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (15137:ℚ) := by decide +kernel
  have hratR : ((((14979485794412569 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((7484930448529593 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15137:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1768 : ((((14989110823883801 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15139 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15137 < q → q < 15139 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15139).mp (by decide +kernel))) hgap
  have hprev := thV_1767
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15139:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((14989110823883801 : ℚ) / 1000000000000) ≤ ((14979485794412569 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (15139:ℚ) := by decide +kernel
  have hratR : ((((14989110823883801 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((14979485794412569 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15139:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1769 : ((((749936825684129 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15149 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15139 < q → q < 15149 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15149).mp (by decide +kernel))) hgap
  have hprev := thV_1768
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15149:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((749936825684129 : ℚ) / 50000000000) ≤ ((14989110823883801 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (15149:ℚ) := by decide +kernel
  have hratR : ((((749936825684129 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((14989110823883801 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15149:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1770 : ((((7504181497649641 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15161 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15149 < q → q < 15161 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15161).mp (by decide +kernel))) hgap
  have hprev := thV_1769
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15161:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7504181497649641 : ℚ) / 500000000000) ≤ ((749936825684129 : ℚ) / 50000000000) + Work.RHContract.RegionI.logLowQ (15161:ℚ) := by decide +kernel
  have hratR : ((((7504181497649641 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((749936825684129 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15161:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1771 : ((((15017990268107427 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15173 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15161 < q → q < 15173 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15173).mp (by decide +kernel))) hgap
  have hprev := thV_1770
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15173:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((15017990268107427 : ℚ) / 1000000000000) ≤ ((7504181497649641 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (15173:ℚ) := by decide +kernel
  have hratR : ((((15017990268107427 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((7504181497649641 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15173:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1772 : ((((15027618463181777 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15187 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15173 < q → q < 15187 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15187).mp (by decide +kernel))) hgap
  have hprev := thV_1771
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15187:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((15027618463181777 : ℚ) / 1000000000000) ≤ ((15017990268107427 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (15187:ℚ) := by decide +kernel
  have hratR : ((((15027618463181777 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((15017990268107427 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15187:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1773 : ((((15037247053252841 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15193 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15187 < q → q < 15193 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15193).mp (by decide +kernel))) hgap
  have hprev := thV_1772
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15193:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((15037247053252841 : ℚ) / 1000000000000) ≤ ((15027618463181777 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (15193:ℚ) := by decide +kernel
  have hratR : ((((15037247053252841 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((15027618463181777 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15193:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1774 : ((((7523438019082329 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15199 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15193 < q → q < 15199 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15199).mp (by decide +kernel))) hgap
  have hprev := thV_1773
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15199:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7523438019082329 : ℚ) / 500000000000) ≤ ((15037247053252841 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (15199:ℚ) := by decide +kernel
  have hratR : ((((7523438019082329 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((15037247053252841 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15199:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1775 : ((((7528253103332099 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15217 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15199 < q → q < 15217 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15217).mp (by decide +kernel))) hgap
  have hprev := thV_1774
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15217:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7528253103332099 : ℚ) / 500000000000) ≤ ((7523438019082329 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (15217:ℚ) := by decide +kernel
  have hratR : ((((7528253103332099 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((7523438019082329 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15217:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1776 : ((((15066137032107659 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15227 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15217 < q → q < 15227 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15227).mp (by decide +kernel))) hgap
  have hprev := thV_1775
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15227:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((15066137032107659 : ℚ) / 1000000000000) ≤ ((7528253103332099 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (15227:ℚ) := by decide +kernel
  have hratR : ((((15066137032107659 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((7528253103332099 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15227:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1777 : ((((942235515719401 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15233 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15227 < q → q < 15233 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15233).mp (by decide +kernel))) hgap
  have hprev := thV_1776
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15233:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((942235515719401 : ℚ) / 62500000000) ≤ ((15066137032107659 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (15233:ℚ) := by decide +kernel
  have hratR : ((((942235515719401 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((15066137032107659 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15233:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1778 : ((((7542699997975461 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15241 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15233 < q → q < 15241 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15241).mp (by decide +kernel))) hgap
  have hprev := thV_1777
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15241:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7542699997975461 : ℚ) / 500000000000) ≤ ((942235515719401 : ℚ) / 62500000000) + Work.RHContract.RegionI.logLowQ (15241:ℚ) := by decide +kernel
  have hratR : ((((7542699997975461 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((942235515719401 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15241:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1779 : ((((7547516460359717 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15259 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15241 < q → q < 15259 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15259).mp (by decide +kernel))) hgap
  have hprev := thV_1778
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15259:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7547516460359717 : ℚ) / 500000000000) ≤ ((7542699997975461 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (15259:ℚ) := by decide +kernel
  have hratR : ((((7547516460359717 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((7542699997975461 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15259:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1780 : ((((15104666107593969 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15263 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15259 < q → q < 15263 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15263).mp (by decide +kernel))) hgap
  have hprev := thV_1779
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15263:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((15104666107593969 : ℚ) / 1000000000000) ≤ ((7547516460359717 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (15263:ℚ) := by decide +kernel
  have hratR : ((((15104666107593969 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((7547516460359717 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15263:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1781 : ((((15114299687498773 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15269 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15263 < q → q < 15269 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15269).mp (by decide +kernel))) hgap
  have hprev := thV_1780
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15269:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((15114299687498773 : ℚ) / 1000000000000) ≤ ((15104666107593969 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (15269:ℚ) := by decide +kernel
  have hratR : ((((15114299687498773 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((15104666107593969 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15269:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1782 : ((((7561966699189673 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15271 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15269 < q → q < 15271 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15271).mp (by decide +kernel))) hgap
  have hprev := thV_1781
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15271:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7561966699189673 : ℚ) / 500000000000) ≤ ((15114299687498773 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (15271:ℚ) := by decide +kernel
  have hratR : ((((7561966699189673 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((15114299687498773 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15271:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1783 : ((((3783391875521083 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15277 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15271 < q → q < 15277 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15277).mp (by decide +kernel))) hgap
  have hprev := thV_1782
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15277:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((3783391875521083 : ℚ) / 250000000000) ≤ ((7561966699189673 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (15277:ℚ) := by decide +kernel
  have hratR : ((((3783391875521083 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((7561966699189673 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15277:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1784 : ((((15143202260153953 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15287 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15277 < q → q < 15287 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15287).mp (by decide +kernel))) hgap
  have hprev := thV_1783
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15287:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((15143202260153953 : ℚ) / 1000000000000) ≤ ((3783391875521083 : ℚ) / 250000000000) + Work.RHContract.RegionI.logLowQ (15287:ℚ) := by decide +kernel
  have hratR : ((((15143202260153953 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3783391875521083 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15287:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1785 : ((((7576418574522567 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15289 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15287 < q → q < 15289 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15289).mp (by decide +kernel))) hgap
  have hprev := thV_1784
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15289:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7576418574522567 : ℚ) / 500000000000) ≤ ((15143202260153953 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (15289:ℚ) := by decide +kernel
  have hratR : ((((7576418574522567 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((15143202260153953 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15289:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1786 : ((((7581236345893761 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15299 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15289 < q → q < 15299 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15299).mp (by decide +kernel))) hgap
  have hprev := thV_1785
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15299:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7581236345893761 : ℚ) / 500000000000) ≤ ((7576418574522567 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (15299:ℚ) := by decide +kernel
  have hratR : ((((7581236345893761 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((7576418574522567 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15299:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1787 : ((((7586054378651617 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15307 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15299 < q → q < 15307 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15307).mp (by decide +kernel))) hgap
  have hprev := thV_1786
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15307:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7586054378651617 : ℚ) / 500000000000) ≤ ((7581236345893761 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (15307:ℚ) := by decide +kernel
  have hratR : ((((7586054378651617 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((7581236345893761 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15307:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1788 : ((((15181745214719669 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15313 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15307 < q → q < 15313 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15313).mp (by decide +kernel))) hgap
  have hprev := thV_1787
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15313:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((15181745214719669 : ℚ) / 1000000000000) ≤ ((7586054378651617 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (15313:ℚ) := by decide +kernel
  have hratR : ((((15181745214719669 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((7586054378651617 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15313:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1789 : ((((7595691031941651 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15319 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15313 < q → q < 15319 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15319).mp (by decide +kernel))) hgap
  have hprev := thV_1788
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15319:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7595691031941651 : ℚ) / 500000000000) ≤ ((15181745214719669 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (15319:ℚ) := by decide +kernel
  have hratR : ((((7595691031941651 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((15181745214719669 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15319:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1790 : ((((1900127445702261 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15329 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15319 < q → q < 15329 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15329).mp (by decide +kernel))) hgap
  have hprev := thV_1789
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15329:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((1900127445702261 : ℚ) / 125000000000) ≤ ((7595691031941651 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (15329:ℚ) := by decide +kernel
  have hratR : ((((1900127445702261 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((7595691031941651 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15329:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1791 : ((((15210657197816019 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15331 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15329 < q → q < 15331 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15331).mp (by decide +kernel))) hgap
  have hprev := thV_1790
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15331:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((15210657197816019 : ℚ) / 1000000000000) ≤ ((1900127445702261 : ℚ) / 125000000000) + Work.RHContract.RegionI.logLowQ (15331:ℚ) := by decide +kernel
  have hratR : ((((15210657197816019 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1900127445702261 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15331:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1792 : ((((15220296003416953 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15349 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15331 < q → q < 15349 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15349).mp (by decide +kernel))) hgap
  have hprev := thV_1791
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15349:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((15220296003416953 : ℚ) / 1000000000000) ≤ ((15210657197816019 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (15349:ℚ) := by decide +kernel
  have hratR : ((((15220296003416953 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((15210657197816019 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15349:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1793 : ((((15229935460313989 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15359 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15349 < q → q < 15359 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15359).mp (by decide +kernel))) hgap
  have hprev := thV_1792
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15359:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((15229935460313989 : ℚ) / 1000000000000) ≤ ((15220296003416953 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (15359:ℚ) := by decide +kernel
  have hratR : ((((15229935460313989 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((15220296003416953 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15359:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1794 : ((((7619787523709679 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15361 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15359 < q → q < 15361 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15361).mp (by decide +kernel))) hgap
  have hprev := thV_1793
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15361:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7619787523709679 : ℚ) / 500000000000) ≤ ((15229935460313989 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (15361:ℚ) := by decide +kernel
  have hratR : ((((7619787523709679 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((15229935460313989 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15361:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1795 : ((((15249215415418891 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15373 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15361 < q → q < 15373 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15373).mp (by decide +kernel))) hgap
  have hprev := thV_1794
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15373:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((15249215415418891 : ℚ) / 1000000000000) ≤ ((7619787523709679 : ℚ) / 500000000000) + Work.RHContract.RegionI.logLowQ (15373:ℚ) := by decide +kernel
  have hratR : ((((15249215415418891 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((7619787523709679 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15373:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1796 : ((((15258856043581027 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15377 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15373 < q → q < 15377 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15377).mp (by decide +kernel))) hgap
  have hprev := thV_1795
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15377:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((15258856043581027 : ℚ) / 1000000000000) ≤ ((15249215415418891 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (15377:ℚ) := by decide +kernel
  have hratR : ((((15258856043581027 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((15249215415418891 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15377:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1797 : ((((15268497061860203 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15383 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15377 < q → q < 15383 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15383).mp (by decide +kernel))) hgap
  have hprev := thV_1796
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15383:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((15268497061860203 : ℚ) / 1000000000000) ≤ ((15258856043581027 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (15383:ℚ) := by decide +kernel
  have hratR : ((((15268497061860203 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((15258856043581027 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15383:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1798 : ((((15278138600058803 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15391 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15383 < q → q < 15391 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15391).mp (by decide +kernel))) hgap
  have hprev := thV_1797
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15391:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((15278138600058803 : ℚ) / 1000000000000) ≤ ((15268497061860203 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (15391:ℚ) := by decide +kernel
  have hratR : ((((15278138600058803 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((15268497061860203 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15391:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)
lemma thV_1799 : ((((7643890393888391 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ Chebyshev.theta ((15401 : ℕ) : ℝ) := by
  have hgap : ∀ q : ℕ, 15391 < q → q < 15401 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.2 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15401).mp (by decide +kernel))) hgap
  have hprev := thV_1798
  have hlog := Work.RHContract.RegionI.logLowQ_le (x := (15401:ℚ)) (by norm_num) (by norm_num)
  have hrat : ((7643890393888391 : ℚ) / 500000000000) ≤ ((15278138600058803 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logLowQ (15401:ℚ) := by decide +kernel
  have hratR : ((((7643890393888391 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((15278138600058803 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logLowQ (15401:ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep]
  exact le_trans hratR (add_le_add hprev hlog)

end

end Work.RHContract.RegionI
