import Mathlib
import Submission.Work.RHContract.A.RegionI.Data07

open scoped BigOperators

namespace Work.RHContract.RegionI

noncomputable section

lemma lrU_3051 : Commons.NumberTheory.Mertens.logRatioSum ((27961 : ℕ) : ℝ) ≤ ((((2903954333277 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27953 < q → q < 27961 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27961).mp (by decide +kernel))) hgap
  have hprev := lrU_3050
  have hcast : (((27961:ℕ):ℝ)/(((27961:ℕ):ℝ)-1)) = (((27961:ℚ)/((27961:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((27961:ℚ)/((27961:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((27961:ℚ)/((27961:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((27961:ℚ)/((27961:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2903918568537 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((27961:ℚ)/((27961:ℚ)-1)) : ℚ) ≤ ((2903954333277 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2903918568537 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((27961:ℚ)/((27961:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2903954333277 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3052 : Commons.NumberTheory.Mertens.logRatioSum ((27967 : ℕ) : ℝ) ≤ ((((362998761293 : ℚ) / 125000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27961 < q → q < 27967 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27967).mp (by decide +kernel))) hgap
  have hprev := lrU_3051
  have hcast : (((27967:ℕ):ℝ)/(((27967:ℕ):ℝ)-1)) = (((27967:ℚ)/((27967:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((27967:ℚ)/((27967:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((27967:ℚ)/((27967:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((27967:ℚ)/((27967:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2903954333277 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((27967:ℚ)/((27967:ℚ)-1)) : ℚ) ≤ ((362998761293 : ℚ) / 125000000000) := by decide +kernel
  have hratR : ((((2903954333277 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((27967:ℚ)/((27967:ℚ)-1)) : ℚ) : ℝ) ≤ ((((362998761293 : ℚ) / 125000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3053 : Commons.NumberTheory.Mertens.logRatioSum ((27983 : ℕ) : ℝ) ≤ ((((1452012913483 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27967 < q → q < 27983 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27983).mp (by decide +kernel))) hgap
  have hprev := lrU_3052
  have hcast : (((27983:ℕ):ℝ)/(((27983:ℕ):ℝ)-1)) = (((27983:ℚ)/((27983:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((27983:ℚ)/((27983:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((27983:ℚ)/((27983:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((27983:ℚ)/((27983:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((362998761293 : ℚ) / 125000000000) + Work.RHContract.RegionI.logUpQ (((27983:ℚ)/((27983:ℚ)-1)) : ℚ) ≤ ((1452012913483 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((362998761293 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((27983:ℚ)/((27983:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1452012913483 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3054 : Commons.NumberTheory.Mertens.logRatioSum ((27997 : ℕ) : ℝ) ≤ ((((2904061545717 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27983 < q → q < 27997 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27997).mp (by decide +kernel))) hgap
  have hprev := lrU_3053
  have hcast : (((27997:ℕ):ℝ)/(((27997:ℕ):ℝ)-1)) = (((27997:ℚ)/((27997:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((27997:ℚ)/((27997:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((27997:ℚ)/((27997:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((27997:ℚ)/((27997:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1452012913483 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((27997:ℚ)/((27997:ℚ)-1)) : ℚ) ≤ ((2904061545717 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((1452012913483 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((27997:ℚ)/((27997:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2904061545717 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3055 : Commons.NumberTheory.Mertens.logRatioSum ((28001 : ℕ) : ℝ) ≤ ((((580819451873 : ℚ) / 200000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 27997 < q → q < 28001 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28001).mp (by decide +kernel))) hgap
  have hprev := lrU_3054
  have hcast : (((28001:ℕ):ℝ)/(((28001:ℕ):ℝ)-1)) = (((28001:ℚ)/((28001:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28001:ℚ)/((28001:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28001:ℚ)/((28001:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28001:ℚ)/((28001:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2904061545717 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((28001:ℚ)/((28001:ℚ)-1)) : ℚ) ≤ ((580819451873 : ℚ) / 200000000000) := by decide +kernel
  have hratR : ((((2904061545717 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28001:ℚ)/((28001:ℚ)-1)) : ℚ) : ℝ) ≤ ((((580819451873 : ℚ) / 200000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3056 : Commons.NumberTheory.Mertens.logRatioSum ((28019 : ℕ) : ℝ) ≤ ((((290413295007 : ℚ) / 100000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28001 < q → q < 28019 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28019).mp (by decide +kernel))) hgap
  have hprev := lrU_3055
  have hcast : (((28019:ℕ):ℝ)/(((28019:ℕ):ℝ)-1)) = (((28019:ℚ)/((28019:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28019:ℚ)/((28019:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28019:ℚ)/((28019:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28019:ℚ)/((28019:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((580819451873 : ℚ) / 200000000000) + Work.RHContract.RegionI.logUpQ (((28019:ℚ)/((28019:ℚ)-1)) : ℚ) ≤ ((290413295007 : ℚ) / 100000000000) := by decide +kernel
  have hratR : ((((580819451873 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28019:ℚ)/((28019:ℚ)-1)) : ℚ) : ℝ) ≤ ((((290413295007 : ℚ) / 100000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3057 : Commons.NumberTheory.Mertens.logRatioSum ((28027 : ℕ) : ℝ) ≤ ((((2904168630587 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28019 < q → q < 28027 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28027).mp (by decide +kernel))) hgap
  have hprev := lrU_3056
  have hcast : (((28027:ℕ):ℝ)/(((28027:ℕ):ℝ)-1)) = (((28027:ℚ)/((28027:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28027:ℚ)/((28027:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28027:ℚ)/((28027:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28027:ℚ)/((28027:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((290413295007 : ℚ) / 100000000000) + Work.RHContract.RegionI.logUpQ (((28027:ℚ)/((28027:ℚ)-1)) : ℚ) ≤ ((2904168630587 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((290413295007 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28027:ℚ)/((28027:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2904168630587 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3058 : Commons.NumberTheory.Mertens.logRatioSum ((28031 : ℕ) : ℝ) ≤ ((((726051076503 : ℚ) / 250000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28027 < q → q < 28031 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28031).mp (by decide +kernel))) hgap
  have hprev := lrU_3057
  have hcast : (((28031:ℕ):ℝ)/(((28031:ℕ):ℝ)-1)) = (((28031:ℚ)/((28031:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28031:ℚ)/((28031:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28031:ℚ)/((28031:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28031:ℚ)/((28031:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2904168630587 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((28031:ℚ)/((28031:ℚ)-1)) : ℚ) ≤ ((726051076503 : ℚ) / 250000000000) := by decide +kernel
  have hratR : ((((2904168630587 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28031:ℚ)/((28031:ℚ)-1)) : ℚ) : ℝ) ≤ ((((726051076503 : ℚ) / 250000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3059 : Commons.NumberTheory.Mertens.logRatioSum ((28051 : ℕ) : ℝ) ≤ ((((2904239956001 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28031 < q → q < 28051 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28051).mp (by decide +kernel))) hgap
  have hprev := lrU_3058
  have hcast : (((28051:ℕ):ℝ)/(((28051:ℕ):ℝ)-1)) = (((28051:ℚ)/((28051:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28051:ℚ)/((28051:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28051:ℚ)/((28051:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28051:ℚ)/((28051:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((726051076503 : ℚ) / 250000000000) + Work.RHContract.RegionI.logUpQ (((28051:ℚ)/((28051:ℚ)-1)) : ℚ) ≤ ((2904239956001 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((726051076503 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28051:ℚ)/((28051:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2904239956001 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3060 : Commons.NumberTheory.Mertens.logRatioSum ((28057 : ℕ) : ℝ) ≤ ((((1452137799183 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28051 < q → q < 28057 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28057).mp (by decide +kernel))) hgap
  have hprev := lrU_3059
  have hcast : (((28057:ℕ):ℝ)/(((28057:ℕ):ℝ)-1)) = (((28057:ℚ)/((28057:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28057:ℚ)/((28057:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28057:ℚ)/((28057:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28057:ℚ)/((28057:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2904239956001 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((28057:ℚ)/((28057:ℚ)-1)) : ℚ) ≤ ((1452137799183 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((2904239956001 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28057:ℚ)/((28057:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1452137799183 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3061 : Commons.NumberTheory.Mertens.logRatioSum ((28069 : ℕ) : ℝ) ≤ ((((2904311225493 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28057 < q → q < 28069 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28069).mp (by decide +kernel))) hgap
  have hprev := lrU_3060
  have hcast : (((28069:ℕ):ℝ)/(((28069:ℕ):ℝ)-1)) = (((28069:ℚ)/((28069:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28069:ℚ)/((28069:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28069:ℚ)/((28069:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28069:ℚ)/((28069:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1452137799183 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((28069:ℚ)/((28069:ℚ)-1)) : ℚ) ≤ ((2904311225493 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((1452137799183 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28069:ℚ)/((28069:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2904311225493 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3062 : Commons.NumberTheory.Mertens.logRatioSum ((28081 : ℕ) : ℝ) ≤ ((((580869367479 : ℚ) / 200000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28069 < q → q < 28081 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28081).mp (by decide +kernel))) hgap
  have hprev := lrU_3061
  have hcast : (((28081:ℕ):ℝ)/(((28081:ℕ):ℝ)-1)) = (((28081:ℚ)/((28081:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28081:ℚ)/((28081:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28081:ℚ)/((28081:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28081:ℚ)/((28081:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2904311225493 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((28081:ℚ)/((28081:ℚ)-1)) : ℚ) ≤ ((580869367479 : ℚ) / 200000000000) := by decide +kernel
  have hratR : ((((2904311225493 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28081:ℚ)/((28081:ℚ)-1)) : ℚ) : ℝ) ≤ ((((580869367479 : ℚ) / 200000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3063 : Commons.NumberTheory.Mertens.logRatioSum ((28087 : ℕ) : ℝ) ≤ ((((2904382441689 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28081 < q → q < 28087 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28087).mp (by decide +kernel))) hgap
  have hprev := lrU_3062
  have hcast : (((28087:ℕ):ℝ)/(((28087:ℕ):ℝ)-1)) = (((28087:ℚ)/((28087:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28087:ℚ)/((28087:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28087:ℚ)/((28087:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28087:ℚ)/((28087:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((580869367479 : ℚ) / 200000000000) + Work.RHContract.RegionI.logUpQ (((28087:ℚ)/((28087:ℚ)-1)) : ℚ) ≤ ((2904382441689 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((580869367479 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28087:ℚ)/((28087:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2904382441689 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3064 : Commons.NumberTheory.Mertens.logRatioSum ((28097 : ℕ) : ℝ) ≤ ((((2904418033311 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28087 < q → q < 28097 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28097).mp (by decide +kernel))) hgap
  have hprev := lrU_3063
  have hcast : (((28097:ℕ):ℝ)/(((28097:ℕ):ℝ)-1)) = (((28097:ℚ)/((28097:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28097:ℚ)/((28097:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28097:ℚ)/((28097:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28097:ℚ)/((28097:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2904382441689 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((28097:ℚ)/((28097:ℚ)-1)) : ℚ) ≤ ((2904418033311 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2904382441689 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28097:ℚ)/((28097:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2904418033311 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3065 : Commons.NumberTheory.Mertens.logRatioSum ((28099 : ℕ) : ℝ) ≤ ((((907641757 : ℚ) / 312500000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28097 < q → q < 28099 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28099).mp (by decide +kernel))) hgap
  have hprev := lrU_3064
  have hcast : (((28099:ℕ):ℝ)/(((28099:ℕ):ℝ)-1)) = (((28099:ℚ)/((28099:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28099:ℚ)/((28099:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28099:ℚ)/((28099:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28099:ℚ)/((28099:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2904418033311 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((28099:ℚ)/((28099:ℚ)-1)) : ℚ) ≤ ((907641757 : ℚ) / 312500000) := by decide +kernel
  have hratR : ((((2904418033311 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28099:ℚ)/((28099:ℚ)-1)) : ℚ) : ℝ) ≤ ((((907641757 : ℚ) / 312500000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3066 : Commons.NumberTheory.Mertens.logRatioSum ((28109 : ℕ) : ℝ) ≤ ((((726122299707 : ℚ) / 250000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28099 < q → q < 28109 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28109).mp (by decide +kernel))) hgap
  have hprev := lrU_3065
  have hcast : (((28109:ℕ):ℝ)/(((28109:ℕ):ℝ)-1)) = (((28109:ℚ)/((28109:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28109:ℚ)/((28109:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28109:ℚ)/((28109:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28109:ℚ)/((28109:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((907641757 : ℚ) / 312500000) + Work.RHContract.RegionI.logUpQ (((28109:ℚ)/((28109:ℚ)-1)) : ℚ) ≤ ((726122299707 : ℚ) / 250000000000) := by decide +kernel
  have hratR : ((((907641757 : ℚ) / 312500000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28109:ℚ)/((28109:ℚ)-1)) : ℚ) : ℝ) ≤ ((((726122299707 : ℚ) / 250000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3067 : Commons.NumberTheory.Mertens.logRatioSum ((28111 : ℕ) : ℝ) ≤ ((((726131193181 : ℚ) / 250000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28109 < q → q < 28111 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28111).mp (by decide +kernel))) hgap
  have hprev := lrU_3066
  have hcast : (((28111:ℕ):ℝ)/(((28111:ℕ):ℝ)-1)) = (((28111:ℚ)/((28111:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28111:ℚ)/((28111:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28111:ℚ)/((28111:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28111:ℚ)/((28111:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((726122299707 : ℚ) / 250000000000) + Work.RHContract.RegionI.logUpQ (((28111:ℚ)/((28111:ℚ)-1)) : ℚ) ≤ ((726131193181 : ℚ) / 250000000000) := by decide +kernel
  have hratR : ((((726122299707 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28111:ℚ)/((28111:ℚ)-1)) : ℚ) : ℝ) ≤ ((((726131193181 : ℚ) / 250000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3068 : Commons.NumberTheory.Mertens.logRatioSum ((28123 : ℕ) : ℝ) ≤ ((((2904560331441 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28111 < q → q < 28123 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28123).mp (by decide +kernel))) hgap
  have hprev := lrU_3067
  have hcast : (((28123:ℕ):ℝ)/(((28123:ℕ):ℝ)-1)) = (((28123:ℚ)/((28123:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28123:ℚ)/((28123:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28123:ℚ)/((28123:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28123:ℚ)/((28123:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((726131193181 : ℚ) / 250000000000) + Work.RHContract.RegionI.logUpQ (((28123:ℚ)/((28123:ℚ)-1)) : ℚ) ≤ ((2904560331441 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((726131193181 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28123:ℚ)/((28123:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2904560331441 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3069 : Commons.NumberTheory.Mertens.logRatioSum ((28151 : ℕ) : ℝ) ≤ ((((2904595854789 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28123 < q → q < 28151 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28151).mp (by decide +kernel))) hgap
  have hprev := lrU_3068
  have hcast : (((28151:ℕ):ℝ)/(((28151:ℕ):ℝ)-1)) = (((28151:ℚ)/((28151:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28151:ℚ)/((28151:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28151:ℚ)/((28151:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28151:ℚ)/((28151:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2904560331441 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((28151:ℚ)/((28151:ℚ)-1)) : ℚ) ≤ ((2904595854789 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2904560331441 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28151:ℚ)/((28151:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2904595854789 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3070 : Commons.NumberTheory.Mertens.logRatioSum ((28163 : ℕ) : ℝ) ≤ ((((2904631363001 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28151 < q → q < 28163 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28163).mp (by decide +kernel))) hgap
  have hprev := lrU_3069
  have hcast : (((28163:ℕ):ℝ)/(((28163:ℕ):ℝ)-1)) = (((28163:ℚ)/((28163:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28163:ℚ)/((28163:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28163:ℚ)/((28163:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28163:ℚ)/((28163:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2904595854789 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((28163:ℚ)/((28163:ℚ)-1)) : ℚ) ≤ ((2904631363001 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2904595854789 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28163:ℚ)/((28163:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2904631363001 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3071 : Commons.NumberTheory.Mertens.logRatioSum ((28181 : ℕ) : ℝ) ≤ ((((726166712133 : ℚ) / 250000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28163 < q → q < 28181 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28181).mp (by decide +kernel))) hgap
  have hprev := lrU_3070
  have hcast : (((28181:ℕ):ℝ)/(((28181:ℕ):ℝ)-1)) = (((28181:ℚ)/((28181:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28181:ℚ)/((28181:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28181:ℚ)/((28181:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28181:ℚ)/((28181:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2904631363001 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((28181:ℚ)/((28181:ℚ)-1)) : ℚ) ≤ ((726166712133 : ℚ) / 250000000000) := by decide +kernel
  have hratR : ((((2904631363001 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28181:ℚ)/((28181:ℚ)-1)) : ℚ) : ℝ) ≤ ((((726166712133 : ℚ) / 250000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3072 : Commons.NumberTheory.Mertens.logRatioSum ((28183 : ℕ) : ℝ) ≤ ((((580940466309 : ℚ) / 200000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28181 < q → q < 28183 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28183).mp (by decide +kernel))) hgap
  have hprev := lrU_3071
  have hcast : (((28183:ℕ):ℝ)/(((28183:ℕ):ℝ)-1)) = (((28183:ℚ)/((28183:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28183:ℚ)/((28183:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28183:ℚ)/((28183:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28183:ℚ)/((28183:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((726166712133 : ℚ) / 250000000000) + Work.RHContract.RegionI.logUpQ (((28183:ℚ)/((28183:ℚ)-1)) : ℚ) ≤ ((580940466309 : ℚ) / 200000000000) := by decide +kernel
  have hratR : ((((726166712133 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28183:ℚ)/((28183:ℚ)-1)) : ℚ) : ℝ) ≤ ((((580940466309 : ℚ) / 200000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3073 : Commons.NumberTheory.Mertens.logRatioSum ((28201 : ℕ) : ℝ) ≤ ((((290473779191 : ℚ) / 100000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28183 < q → q < 28201 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28201).mp (by decide +kernel))) hgap
  have hprev := lrU_3072
  have hcast : (((28201:ℕ):ℝ)/(((28201:ℕ):ℝ)-1)) = (((28201:ℚ)/((28201:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28201:ℚ)/((28201:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28201:ℚ)/((28201:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28201:ℚ)/((28201:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((580940466309 : ℚ) / 200000000000) + Work.RHContract.RegionI.logUpQ (((28201:ℚ)/((28201:ℚ)-1)) : ℚ) ≤ ((290473779191 : ℚ) / 100000000000) := by decide +kernel
  have hratR : ((((580940466309 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28201:ℚ)/((28201:ℚ)-1)) : ℚ) : ℝ) ≤ ((((290473779191 : ℚ) / 100000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3074 : Commons.NumberTheory.Mertens.logRatioSum ((28211 : ℕ) : ℝ) ≤ ((((580954647941 : ℚ) / 200000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28201 < q → q < 28211 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28211).mp (by decide +kernel))) hgap
  have hprev := lrU_3073
  have hcast : (((28211:ℕ):ℝ)/(((28211:ℕ):ℝ)-1)) = (((28211:ℚ)/((28211:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28211:ℚ)/((28211:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28211:ℚ)/((28211:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28211:ℚ)/((28211:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((290473779191 : ℚ) / 100000000000) + Work.RHContract.RegionI.logUpQ (((28211:ℚ)/((28211:ℚ)-1)) : ℚ) ≤ ((580954647941 : ℚ) / 200000000000) := by decide +kernel
  have hratR : ((((290473779191 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28211:ℚ)/((28211:ℚ)-1)) : ℚ) : ℝ) ≤ ((((580954647941 : ℚ) / 200000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3075 : Commons.NumberTheory.Mertens.logRatioSum ((28219 : ℕ) : ℝ) ≤ ((((58096173549 : ℚ) / 20000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28211 < q → q < 28219 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28219).mp (by decide +kernel))) hgap
  have hprev := lrU_3074
  have hcast : (((28219:ℕ):ℝ)/(((28219:ℕ):ℝ)-1)) = (((28219:ℚ)/((28219:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28219:ℚ)/((28219:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28219:ℚ)/((28219:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28219:ℚ)/((28219:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((580954647941 : ℚ) / 200000000000) + Work.RHContract.RegionI.logUpQ (((28219:ℚ)/((28219:ℚ)-1)) : ℚ) ≤ ((58096173549 : ℚ) / 20000000000) := by decide +kernel
  have hratR : ((((580954647941 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28219:ℚ)/((28219:ℚ)-1)) : ℚ) : ℝ) ≤ ((((58096173549 : ℚ) / 20000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3076 : Commons.NumberTheory.Mertens.logRatioSum ((28229 : ℕ) : ℝ) ≤ ((((2904844102641 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28219 < q → q < 28229 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28229).mp (by decide +kernel))) hgap
  have hprev := lrU_3075
  have hcast : (((28229:ℕ):ℝ)/(((28229:ℕ):ℝ)-1)) = (((28229:ℚ)/((28229:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28229:ℚ)/((28229:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28229:ℚ)/((28229:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28229:ℚ)/((28229:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((58096173549 : ℚ) / 20000000000) + Work.RHContract.RegionI.logUpQ (((28229:ℚ)/((28229:ℚ)-1)) : ℚ) ≤ ((2904844102641 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((58096173549 : ℚ) / 20000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28229:ℚ)/((28229:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2904844102641 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3077 : Commons.NumberTheory.Mertens.logRatioSum ((28277 : ℕ) : ℝ) ≤ ((((2904879467697 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28229 < q → q < 28277 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28277).mp (by decide +kernel))) hgap
  have hprev := lrU_3076
  have hcast : (((28277:ℕ):ℝ)/(((28277:ℕ):ℝ)-1)) = (((28277:ℚ)/((28277:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28277:ℚ)/((28277:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28277:ℚ)/((28277:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28277:ℚ)/((28277:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2904844102641 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((28277:ℚ)/((28277:ℚ)-1)) : ℚ) ≤ ((2904879467697 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2904844102641 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28277:ℚ)/((28277:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2904879467697 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3078 : Commons.NumberTheory.Mertens.logRatioSum ((28279 : ℕ) : ℝ) ≤ ((((726228707563 : ℚ) / 250000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28277 < q → q < 28279 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28279).mp (by decide +kernel))) hgap
  have hprev := lrU_3077
  have hcast : (((28279:ℕ):ℝ)/(((28279:ℕ):ℝ)-1)) = (((28279:ℚ)/((28279:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28279:ℚ)/((28279:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28279:ℚ)/((28279:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28279:ℚ)/((28279:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2904879467697 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((28279:ℚ)/((28279:ℚ)-1)) : ℚ) ≤ ((726228707563 : ℚ) / 250000000000) := by decide +kernel
  have hratR : ((((2904879467697 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28279:ℚ)/((28279:ℚ)-1)) : ℚ) : ℝ) ≤ ((((726228707563 : ℚ) / 250000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3079 : Commons.NumberTheory.Mertens.logRatioSum ((28283 : ℕ) : ℝ) ≤ ((((1452475093903 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28279 < q → q < 28283 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28283).mp (by decide +kernel))) hgap
  have hprev := lrU_3078
  have hcast : (((28283:ℕ):ℝ)/(((28283:ℕ):ℝ)-1)) = (((28283:ℚ)/((28283:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28283:ℚ)/((28283:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28283:ℚ)/((28283:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28283:ℚ)/((28283:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((726228707563 : ℚ) / 250000000000) + Work.RHContract.RegionI.logUpQ (((28283:ℚ)/((28283:ℚ)-1)) : ℚ) ≤ ((1452475093903 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((726228707563 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28283:ℚ)/((28283:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1452475093903 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3080 : Commons.NumberTheory.Mertens.logRatioSum ((28289 : ℕ) : ℝ) ≤ ((((145249276893 : ℚ) / 50000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28283 < q → q < 28289 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28289).mp (by decide +kernel))) hgap
  have hprev := lrU_3079
  have hcast : (((28289:ℕ):ℝ)/(((28289:ℕ):ℝ)-1)) = (((28289:ℚ)/((28289:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28289:ℚ)/((28289:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28289:ℚ)/((28289:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28289:ℚ)/((28289:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1452475093903 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((28289:ℚ)/((28289:ℚ)-1)) : ℚ) ≤ ((145249276893 : ℚ) / 50000000000) := by decide +kernel
  have hratR : ((((1452475093903 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28289:ℚ)/((28289:ℚ)-1)) : ℚ) : ℝ) ≤ ((((145249276893 : ℚ) / 50000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3081 : Commons.NumberTheory.Mertens.logRatioSum ((28297 : ℕ) : ℝ) ≤ ((((18156380487 : ℚ) / 6250000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28289 < q → q < 28297 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28297).mp (by decide +kernel))) hgap
  have hprev := lrU_3080
  have hcast : (((28297:ℕ):ℝ)/(((28297:ℕ):ℝ)-1)) = (((28297:ℚ)/((28297:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28297:ℚ)/((28297:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28297:ℚ)/((28297:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28297:ℚ)/((28297:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((145249276893 : ℚ) / 50000000000) + Work.RHContract.RegionI.logUpQ (((28297:ℚ)/((28297:ℚ)-1)) : ℚ) ≤ ((18156380487 : ℚ) / 6250000000) := by decide +kernel
  have hratR : ((((145249276893 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28297:ℚ)/((28297:ℚ)-1)) : ℚ) : ℝ) ≤ ((((18156380487 : ℚ) / 6250000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3082 : Commons.NumberTheory.Mertens.logRatioSum ((28307 : ℕ) : ℝ) ≤ ((((581011241099 : ℚ) / 200000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28297 < q → q < 28307 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28307).mp (by decide +kernel))) hgap
  have hprev := lrU_3081
  have hcast : (((28307:ℕ):ℝ)/(((28307:ℕ):ℝ)-1)) = (((28307:ℚ)/((28307:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28307:ℚ)/((28307:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28307:ℚ)/((28307:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28307:ℚ)/((28307:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((18156380487 : ℚ) / 6250000000) + Work.RHContract.RegionI.logUpQ (((28307:ℚ)/((28307:ℚ)-1)) : ℚ) ≤ ((581011241099 : ℚ) / 200000000000) := by decide +kernel
  have hratR : ((((18156380487 : ℚ) / 6250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28307:ℚ)/((28307:ℚ)-1)) : ℚ) : ℝ) ≤ ((((581011241099 : ℚ) / 200000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3083 : Commons.NumberTheory.Mertens.logRatioSum ((28309 : ℕ) : ℝ) ≤ ((((116203661223 : ℚ) / 40000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28307 < q → q < 28309 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28309).mp (by decide +kernel))) hgap
  have hprev := lrU_3082
  have hcast : (((28309:ℕ):ℝ)/(((28309:ℕ):ℝ)-1)) = (((28309:ℚ)/((28309:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28309:ℚ)/((28309:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28309:ℚ)/((28309:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28309:ℚ)/((28309:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((581011241099 : ℚ) / 200000000000) + Work.RHContract.RegionI.logUpQ (((28309:ℚ)/((28309:ℚ)-1)) : ℚ) ≤ ((116203661223 : ℚ) / 40000000000) := by decide +kernel
  have hratR : ((((581011241099 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28309:ℚ)/((28309:ℚ)-1)) : ℚ) : ℝ) ≤ ((((116203661223 : ℚ) / 40000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3084 : Commons.NumberTheory.Mertens.logRatioSum ((28319 : ℕ) : ℝ) ≤ ((((145256342159 : ℚ) / 50000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28309 < q → q < 28319 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28319).mp (by decide +kernel))) hgap
  have hprev := lrU_3083
  have hcast : (((28319:ℕ):ℝ)/(((28319:ℕ):ℝ)-1)) = (((28319:ℚ)/((28319:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28319:ℚ)/((28319:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28319:ℚ)/((28319:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28319:ℚ)/((28319:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((116203661223 : ℚ) / 40000000000) + Work.RHContract.RegionI.logUpQ (((28319:ℚ)/((28319:ℚ)-1)) : ℚ) ≤ ((145256342159 : ℚ) / 50000000000) := by decide +kernel
  have hratR : ((((116203661223 : ℚ) / 40000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28319:ℚ)/((28319:ℚ)-1)) : ℚ) : ℝ) ≤ ((((145256342159 : ℚ) / 50000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3085 : Commons.NumberTheory.Mertens.logRatioSum ((28349 : ℕ) : ℝ) ≤ ((((181572632401 : ℚ) / 62500000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28319 < q → q < 28349 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28349).mp (by decide +kernel))) hgap
  have hprev := lrU_3084
  have hcast : (((28349:ℕ):ℝ)/(((28349:ℕ):ℝ)-1)) = (((28349:ℚ)/((28349:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28349:ℚ)/((28349:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28349:ℚ)/((28349:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28349:ℚ)/((28349:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((145256342159 : ℚ) / 50000000000) + Work.RHContract.RegionI.logUpQ (((28349:ℚ)/((28349:ℚ)-1)) : ℚ) ≤ ((181572632401 : ℚ) / 62500000000) := by decide +kernel
  have hratR : ((((145256342159 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28349:ℚ)/((28349:ℚ)-1)) : ℚ) : ℝ) ≤ ((((181572632401 : ℚ) / 62500000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3086 : Commons.NumberTheory.Mertens.logRatioSum ((28351 : ℕ) : ℝ) ≤ ((((2905197391163 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28349 < q → q < 28351 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28351).mp (by decide +kernel))) hgap
  have hprev := lrU_3085
  have hcast : (((28351:ℕ):ℝ)/(((28351:ℕ):ℝ)-1)) = (((28351:ℚ)/((28351:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28351:ℚ)/((28351:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28351:ℚ)/((28351:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28351:ℚ)/((28351:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((181572632401 : ℚ) / 62500000000) + Work.RHContract.RegionI.logUpQ (((28351:ℚ)/((28351:ℚ)-1)) : ℚ) ≤ ((2905197391163 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((181572632401 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28351:ℚ)/((28351:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2905197391163 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3087 : Commons.NumberTheory.Mertens.logRatioSum ((28387 : ℕ) : ℝ) ≤ ((((2905232619177 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28351 < q → q < 28387 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28387).mp (by decide +kernel))) hgap
  have hprev := lrU_3086
  have hcast : (((28387:ℕ):ℝ)/(((28387:ℕ):ℝ)-1)) = (((28387:ℚ)/((28387:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28387:ℚ)/((28387:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28387:ℚ)/((28387:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28387:ℚ)/((28387:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2905197391163 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((28387:ℚ)/((28387:ℚ)-1)) : ℚ) ≤ ((2905232619177 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2905197391163 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28387:ℚ)/((28387:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2905232619177 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3088 : Commons.NumberTheory.Mertens.logRatioSum ((28393 : ℕ) : ℝ) ≤ ((((1452633919873 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28387 < q → q < 28393 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28393).mp (by decide +kernel))) hgap
  have hprev := lrU_3087
  have hcast : (((28393:ℕ):ℝ)/(((28393:ℕ):ℝ)-1)) = (((28393:ℚ)/((28393:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28393:ℚ)/((28393:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28393:ℚ)/((28393:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28393:ℚ)/((28393:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2905232619177 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((28393:ℚ)/((28393:ℚ)-1)) : ℚ) ≤ ((1452633919873 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((2905232619177 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28393:ℚ)/((28393:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1452633919873 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3089 : Commons.NumberTheory.Mertens.logRatioSum ((28403 : ℕ) : ℝ) ≤ ((((581060609583 : ℚ) / 200000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28393 < q → q < 28403 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28403).mp (by decide +kernel))) hgap
  have hprev := lrU_3088
  have hcast : (((28403:ℕ):ℝ)/(((28403:ℕ):ℝ)-1)) = (((28403:ℚ)/((28403:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28403:ℚ)/((28403:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28403:ℚ)/((28403:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28403:ℚ)/((28403:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1452633919873 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((28403:ℚ)/((28403:ℚ)-1)) : ℚ) ≤ ((581060609583 : ℚ) / 200000000000) := by decide +kernel
  have hratR : ((((1452633919873 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28403:ℚ)/((28403:ℚ)-1)) : ℚ) : ℝ) ≤ ((((581060609583 : ℚ) / 200000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3090 : Commons.NumberTheory.Mertens.logRatioSum ((28409 : ℕ) : ℝ) ≤ ((((363167281081 : ℚ) / 125000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28403 < q → q < 28409 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28409).mp (by decide +kernel))) hgap
  have hprev := lrU_3089
  have hcast : (((28409:ℕ):ℝ)/(((28409:ℕ):ℝ)-1)) = (((28409:ℚ)/((28409:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28409:ℚ)/((28409:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28409:ℚ)/((28409:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28409:ℚ)/((28409:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((581060609583 : ℚ) / 200000000000) + Work.RHContract.RegionI.logUpQ (((28409:ℚ)/((28409:ℚ)-1)) : ℚ) ≤ ((363167281081 : ℚ) / 125000000000) := by decide +kernel
  have hratR : ((((581060609583 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28409:ℚ)/((28409:ℚ)-1)) : ℚ) : ℝ) ≤ ((((363167281081 : ℚ) / 125000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3091 : Commons.NumberTheory.Mertens.logRatioSum ((28411 : ℕ) : ℝ) ≤ ((((2905373446903 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28409 < q → q < 28411 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28411).mp (by decide +kernel))) hgap
  have hprev := lrU_3090
  have hcast : (((28411:ℕ):ℝ)/(((28411:ℕ):ℝ)-1)) = (((28411:ℚ)/((28411:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28411:ℚ)/((28411:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28411:ℚ)/((28411:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28411:ℚ)/((28411:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((363167281081 : ℚ) / 125000000000) + Work.RHContract.RegionI.logUpQ (((28411:ℚ)/((28411:ℚ)-1)) : ℚ) ≤ ((2905373446903 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((363167281081 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28411:ℚ)/((28411:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2905373446903 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3092 : Commons.NumberTheory.Mertens.logRatioSum ((28429 : ℕ) : ℝ) ≤ ((((2905408622871 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28411 < q → q < 28429 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28429).mp (by decide +kernel))) hgap
  have hprev := lrU_3091
  have hcast : (((28429:ℕ):ℝ)/(((28429:ℕ):ℝ)-1)) = (((28429:ℚ)/((28429:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28429:ℚ)/((28429:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28429:ℚ)/((28429:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28429:ℚ)/((28429:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2905373446903 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((28429:ℚ)/((28429:ℚ)-1)) : ℚ) ≤ ((2905408622871 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2905373446903 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28429:ℚ)/((28429:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2905408622871 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3093 : Commons.NumberTheory.Mertens.logRatioSum ((28433 : ℕ) : ℝ) ≤ ((((2905443793891 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28429 < q → q < 28433 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28433).mp (by decide +kernel))) hgap
  have hprev := lrU_3092
  have hcast : (((28433:ℕ):ℝ)/(((28433:ℕ):ℝ)-1)) = (((28433:ℚ)/((28433:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28433:ℚ)/((28433:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28433:ℚ)/((28433:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28433:ℚ)/((28433:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2905408622871 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((28433:ℚ)/((28433:ℚ)-1)) : ℚ) ≤ ((2905443793891 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2905408622871 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28433:ℚ)/((28433:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2905443793891 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3094 : Commons.NumberTheory.Mertens.logRatioSum ((28439 : ℕ) : ℝ) ≤ ((((290547895749 : ℚ) / 100000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28433 < q → q < 28439 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28439).mp (by decide +kernel))) hgap
  have hprev := lrU_3093
  have hcast : (((28439:ℕ):ℝ)/(((28439:ℕ):ℝ)-1)) = (((28439:ℚ)/((28439:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28439:ℚ)/((28439:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28439:ℚ)/((28439:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28439:ℚ)/((28439:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2905443793891 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((28439:ℚ)/((28439:ℚ)-1)) : ℚ) ≤ ((290547895749 : ℚ) / 100000000000) := by decide +kernel
  have hratR : ((((2905443793891 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28439:ℚ)/((28439:ℚ)-1)) : ℚ) : ℝ) ≤ ((((290547895749 : ℚ) / 100000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3095 : Commons.NumberTheory.Mertens.logRatioSum ((28447 : ℕ) : ℝ) ≤ ((((3631892639 : ℚ) / 1250000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28439 < q → q < 28447 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28447).mp (by decide +kernel))) hgap
  have hprev := lrU_3094
  have hcast : (((28447:ℕ):ℝ)/(((28447:ℕ):ℝ)-1)) = (((28447:ℚ)/((28447:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28447:ℚ)/((28447:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28447:ℚ)/((28447:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28447:ℚ)/((28447:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((290547895749 : ℚ) / 100000000000) + Work.RHContract.RegionI.logUpQ (((28447:ℚ)/((28447:ℚ)-1)) : ℚ) ≤ ((3631892639 : ℚ) / 1250000000) := by decide +kernel
  have hratR : ((((290547895749 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28447:ℚ)/((28447:ℚ)-1)) : ℚ) : ℝ) ≤ ((((3631892639 : ℚ) / 1250000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3096 : Commons.NumberTheory.Mertens.logRatioSum ((28463 : ℕ) : ℝ) ≤ ((((2905549245149 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28447 < q → q < 28463 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28463).mp (by decide +kernel))) hgap
  have hprev := lrU_3095
  have hcast : (((28463:ℕ):ℝ)/(((28463:ℕ):ℝ)-1)) = (((28463:ℚ)/((28463:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28463:ℚ)/((28463:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28463:ℚ)/((28463:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28463:ℚ)/((28463:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((3631892639 : ℚ) / 1250000000) + Work.RHContract.RegionI.logUpQ (((28463:ℚ)/((28463:ℚ)-1)) : ℚ) ≤ ((2905549245149 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((3631892639 : ℚ) / 1250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28463:ℚ)/((28463:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2905549245149 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3097 : Commons.NumberTheory.Mertens.logRatioSum ((28477 : ℕ) : ℝ) ≤ ((((116223374473 : ℚ) / 40000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28463 < q → q < 28477 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28477).mp (by decide +kernel))) hgap
  have hprev := lrU_3096
  have hcast : (((28477:ℕ):ℝ)/(((28477:ℕ):ℝ)-1)) = (((28477:ℚ)/((28477:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28477:ℚ)/((28477:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28477:ℚ)/((28477:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28477:ℚ)/((28477:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2905549245149 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((28477:ℚ)/((28477:ℚ)-1)) : ℚ) ≤ ((116223374473 : ℚ) / 40000000000) := by decide +kernel
  have hratR : ((((2905549245149 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28477:ℚ)/((28477:ℚ)-1)) : ℚ) : ℝ) ≤ ((((116223374473 : ℚ) / 40000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3098 : Commons.NumberTheory.Mertens.logRatioSum ((28493 : ℕ) : ℝ) ≤ ((((2905619458781 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28477 < q → q < 28493 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28493).mp (by decide +kernel))) hgap
  have hprev := lrU_3097
  have hcast : (((28493:ℕ):ℝ)/(((28493:ℕ):ℝ)-1)) = (((28493:ℚ)/((28493:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28493:ℚ)/((28493:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28493:ℚ)/((28493:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28493:ℚ)/((28493:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((116223374473 : ℚ) / 40000000000) + Work.RHContract.RegionI.logUpQ (((28493:ℚ)/((28493:ℚ)-1)) : ℚ) ≤ ((2905619458781 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((116223374473 : ℚ) / 40000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28493:ℚ)/((28493:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2905619458781 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3099 : Commons.NumberTheory.Mertens.logRatioSum ((28499 : ℕ) : ℝ) ≤ ((((726413637087 : ℚ) / 250000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28493 < q → q < 28499 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28499).mp (by decide +kernel))) hgap
  have hprev := lrU_3098
  have hcast : (((28499:ℕ):ℝ)/(((28499:ℕ):ℝ)-1)) = (((28499:ℚ)/((28499:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28499:ℚ)/((28499:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28499:ℚ)/((28499:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28499:ℚ)/((28499:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2905619458781 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((28499:ℚ)/((28499:ℚ)-1)) : ℚ) ≤ ((726413637087 : ℚ) / 250000000000) := by decide +kernel
  have hratR : ((((2905619458781 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28499:ℚ)/((28499:ℚ)-1)) : ℚ) : ℝ) ≤ ((((726413637087 : ℚ) / 250000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3100 : Commons.NumberTheory.Mertens.logRatioSum ((28513 : ℕ) : ℝ) ≤ ((((581137924137 : ℚ) / 200000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28499 < q → q < 28513 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28513).mp (by decide +kernel))) hgap
  have hprev := lrU_3099
  have hcast : (((28513:ℕ):ℝ)/(((28513:ℕ):ℝ)-1)) = (((28513:ℚ)/((28513:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28513:ℚ)/((28513:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28513:ℚ)/((28513:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28513:ℚ)/((28513:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((726413637087 : ℚ) / 250000000000) + Work.RHContract.RegionI.logUpQ (((28513:ℚ)/((28513:ℚ)-1)) : ℚ) ≤ ((581137924137 : ℚ) / 200000000000) := by decide +kernel
  have hratR : ((((726413637087 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28513:ℚ)/((28513:ℚ)-1)) : ℚ) : ℝ) ≤ ((((581137924137 : ℚ) / 200000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3101 : Commons.NumberTheory.Mertens.logRatioSum ((28517 : ℕ) : ℝ) ≤ ((((2905724688103 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28513 < q → q < 28517 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28517).mp (by decide +kernel))) hgap
  have hprev := lrU_3100
  have hcast : (((28517:ℕ):ℝ)/(((28517:ℕ):ℝ)-1)) = (((28517:ℚ)/((28517:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28517:ℚ)/((28517:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28517:ℚ)/((28517:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28517:ℚ)/((28517:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((581137924137 : ℚ) / 200000000000) + Work.RHContract.RegionI.logUpQ (((28517:ℚ)/((28517:ℚ)-1)) : ℚ) ≤ ((2905724688103 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((581137924137 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28517:ℚ)/((28517:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2905724688103 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3102 : Commons.NumberTheory.Mertens.logRatioSum ((28537 : ℕ) : ℝ) ≤ ((((2905759730943 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28517 < q → q < 28537 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28537).mp (by decide +kernel))) hgap
  have hprev := lrU_3101
  have hcast : (((28537:ℕ):ℝ)/(((28537:ℕ):ℝ)-1)) = (((28537:ℚ)/((28537:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28537:ℚ)/((28537:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28537:ℚ)/((28537:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28537:ℚ)/((28537:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2905724688103 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((28537:ℚ)/((28537:ℚ)-1)) : ℚ) ≤ ((2905759730943 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2905724688103 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28537:ℚ)/((28537:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2905759730943 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3103 : Commons.NumberTheory.Mertens.logRatioSum ((28541 : ℕ) : ℝ) ≤ ((((363224346109 : ℚ) / 125000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28537 < q → q < 28541 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28541).mp (by decide +kernel))) hgap
  have hprev := lrU_3102
  have hcast : (((28541:ℕ):ℝ)/(((28541:ℕ):ℝ)-1)) = (((28541:ℚ)/((28541:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28541:ℚ)/((28541:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28541:ℚ)/((28541:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28541:ℚ)/((28541:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2905759730943 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((28541:ℚ)/((28541:ℚ)-1)) : ℚ) ≤ ((363224346109 : ℚ) / 125000000000) := by decide +kernel
  have hratR : ((((2905759730943 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28541:ℚ)/((28541:ℚ)-1)) : ℚ) : ℝ) ≤ ((((363224346109 : ℚ) / 125000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3104 : Commons.NumberTheory.Mertens.logRatioSum ((28547 : ℕ) : ℝ) ≤ ((((2905829799437 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28541 < q → q < 28547 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28547).mp (by decide +kernel))) hgap
  have hprev := lrU_3103
  have hcast : (((28547:ℕ):ℝ)/(((28547:ℕ):ℝ)-1)) = (((28547:ℚ)/((28547:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28547:ℚ)/((28547:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28547:ℚ)/((28547:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28547:ℚ)/((28547:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((363224346109 : ℚ) / 125000000000) + Work.RHContract.RegionI.logUpQ (((28547:ℚ)/((28547:ℚ)-1)) : ℚ) ≤ ((2905829799437 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((363224346109 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28547:ℚ)/((28547:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2905829799437 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3105 : Commons.NumberTheory.Mertens.logRatioSum ((28549 : ℕ) : ℝ) ≤ ((((726466206887 : ℚ) / 250000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28547 < q → q < 28549 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28549).mp (by decide +kernel))) hgap
  have hprev := lrU_3104
  have hcast : (((28549:ℕ):ℝ)/(((28549:ℕ):ℝ)-1)) = (((28549:ℚ)/((28549:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28549:ℚ)/((28549:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28549:ℚ)/((28549:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28549:ℚ)/((28549:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2905829799437 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((28549:ℚ)/((28549:ℚ)-1)) : ℚ) ≤ ((726466206887 : ℚ) / 250000000000) := by decide +kernel
  have hratR : ((((2905829799437 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28549:ℚ)/((28549:ℚ)-1)) : ℚ) : ℝ) ≤ ((((726466206887 : ℚ) / 250000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3106 : Commons.NumberTheory.Mertens.logRatioSum ((28559 : ℕ) : ℝ) ≤ ((((2905899843393 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28549 < q → q < 28559 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28559).mp (by decide +kernel))) hgap
  have hprev := lrU_3105
  have hcast : (((28559:ℕ):ℝ)/(((28559:ℕ):ℝ)-1)) = (((28559:ℚ)/((28559:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28559:ℚ)/((28559:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28559:ℚ)/((28559:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28559:ℚ)/((28559:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((726466206887 : ℚ) / 250000000000) + Work.RHContract.RegionI.logUpQ (((28559:ℚ)/((28559:ℚ)-1)) : ℚ) ≤ ((2905899843393 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((726466206887 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28559:ℚ)/((28559:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2905899843393 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3107 : Commons.NumberTheory.Mertens.logRatioSum ((28571 : ℕ) : ℝ) ≤ ((((2905934844531 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28559 < q → q < 28571 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28571).mp (by decide +kernel))) hgap
  have hprev := lrU_3106
  have hcast : (((28571:ℕ):ℝ)/(((28571:ℕ):ℝ)-1)) = (((28571:ℚ)/((28571:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28571:ℚ)/((28571:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28571:ℚ)/((28571:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28571:ℚ)/((28571:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2905899843393 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((28571:ℚ)/((28571:ℚ)-1)) : ℚ) ≤ ((2905934844531 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2905899843393 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28571:ℚ)/((28571:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2905934844531 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3108 : Commons.NumberTheory.Mertens.logRatioSum ((28573 : ℕ) : ℝ) ≤ ((((2905969843219 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28571 < q → q < 28573 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28573).mp (by decide +kernel))) hgap
  have hprev := lrU_3107
  have hcast : (((28573:ℕ):ℝ)/(((28573:ℕ):ℝ)-1)) = (((28573:ℚ)/((28573:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28573:ℚ)/((28573:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28573:ℚ)/((28573:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28573:ℚ)/((28573:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2905934844531 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((28573:ℚ)/((28573:ℚ)-1)) : ℚ) ≤ ((2905969843219 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2905934844531 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28573:ℚ)/((28573:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2905969843219 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3109 : Commons.NumberTheory.Mertens.logRatioSum ((28579 : ℕ) : ℝ) ≤ ((((2906004834559 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28573 < q → q < 28579 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28579).mp (by decide +kernel))) hgap
  have hprev := lrU_3108
  have hcast : (((28579:ℕ):ℝ)/(((28579:ℕ):ℝ)-1)) = (((28579:ℚ)/((28579:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28579:ℚ)/((28579:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28579:ℚ)/((28579:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28579:ℚ)/((28579:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2905969843219 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((28579:ℚ)/((28579:ℚ)-1)) : ℚ) ≤ ((2906004834559 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2905969843219 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28579:ℚ)/((28579:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2906004834559 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3110 : Commons.NumberTheory.Mertens.logRatioSum ((28591 : ℕ) : ℝ) ≤ ((((2906039811213 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28579 < q → q < 28591 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28591).mp (by decide +kernel))) hgap
  have hprev := lrU_3109
  have hcast : (((28591:ℕ):ℝ)/(((28591:ℕ):ℝ)-1)) = (((28591:ℚ)/((28591:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28591:ℚ)/((28591:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28591:ℚ)/((28591:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28591:ℚ)/((28591:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2906004834559 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((28591:ℚ)/((28591:ℚ)-1)) : ℚ) ≤ ((2906039811213 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2906004834559 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28591:ℚ)/((28591:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2906039811213 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3111 : Commons.NumberTheory.Mertens.logRatioSum ((28597 : ℕ) : ℝ) ≤ ((((181629673783 : ℚ) / 62500000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28591 < q → q < 28597 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28597).mp (by decide +kernel))) hgap
  have hprev := lrU_3110
  have hcast : (((28597:ℕ):ℝ)/(((28597:ℕ):ℝ)-1)) = (((28597:ℚ)/((28597:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28597:ℚ)/((28597:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28597:ℚ)/((28597:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28597:ℚ)/((28597:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2906039811213 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((28597:ℚ)/((28597:ℚ)-1)) : ℚ) ≤ ((181629673783 : ℚ) / 62500000000) := by decide +kernel
  have hratR : ((((2906039811213 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28597:ℚ)/((28597:ℚ)-1)) : ℚ) : ℝ) ≤ ((((181629673783 : ℚ) / 62500000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3112 : Commons.NumberTheory.Mertens.logRatioSum ((28603 : ℕ) : ℝ) ≤ ((((2906109742507 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28597 < q → q < 28603 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28603).mp (by decide +kernel))) hgap
  have hprev := lrU_3111
  have hcast : (((28603:ℕ):ℝ)/(((28603:ℕ):ℝ)-1)) = (((28603:ℚ)/((28603:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28603:ℚ)/((28603:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28603:ℚ)/((28603:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28603:ℚ)/((28603:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((181629673783 : ℚ) / 62500000000) + Work.RHContract.RegionI.logUpQ (((28603:ℚ)/((28603:ℚ)-1)) : ℚ) ≤ ((2906109742507 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((181629673783 : ℚ) / 62500000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28603:ℚ)/((28603:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2906109742507 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3113 : Commons.NumberTheory.Mertens.logRatioSum ((28607 : ℕ) : ℝ) ≤ ((((1453072349799 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28603 < q → q < 28607 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28607).mp (by decide +kernel))) hgap
  have hprev := lrU_3112
  have hcast : (((28607:ℕ):ℝ)/(((28607:ℕ):ℝ)-1)) = (((28607:ℚ)/((28607:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28607:ℚ)/((28607:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28607:ℚ)/((28607:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28607:ℚ)/((28607:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2906109742507 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((28607:ℚ)/((28607:ℚ)-1)) : ℚ) ≤ ((1453072349799 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((2906109742507 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28607:ℚ)/((28607:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1453072349799 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3114 : Commons.NumberTheory.Mertens.logRatioSum ((28619 : ℕ) : ℝ) ≤ ((((2906179642031 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28607 < q → q < 28619 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28619).mp (by decide +kernel))) hgap
  have hprev := lrU_3113
  have hcast : (((28619:ℕ):ℝ)/(((28619:ℕ):ℝ)-1)) = (((28619:ℚ)/((28619:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28619:ℚ)/((28619:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28619:ℚ)/((28619:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28619:ℚ)/((28619:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1453072349799 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((28619:ℚ)/((28619:ℚ)-1)) : ℚ) ≤ ((2906179642031 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((1453072349799 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28619:ℚ)/((28619:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2906179642031 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3115 : Commons.NumberTheory.Mertens.logRatioSum ((28621 : ℕ) : ℝ) ≤ ((((1453107291011 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28619 < q → q < 28621 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28621).mp (by decide +kernel))) hgap
  have hprev := lrU_3114
  have hcast : (((28621:ℕ):ℝ)/(((28621:ℕ):ℝ)-1)) = (((28621:ℚ)/((28621:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28621:ℚ)/((28621:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28621:ℚ)/((28621:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28621:ℚ)/((28621:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2906179642031 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((28621:ℚ)/((28621:ℚ)-1)) : ℚ) ≤ ((1453107291011 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((2906179642031 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28621:ℚ)/((28621:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1453107291011 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3116 : Commons.NumberTheory.Mertens.logRatioSum ((28627 : ℕ) : ℝ) ≤ ((((290624951469 : ℚ) / 100000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28621 < q → q < 28627 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28627).mp (by decide +kernel))) hgap
  have hprev := lrU_3115
  have hcast : (((28627:ℕ):ℝ)/(((28627:ℕ):ℝ)-1)) = (((28627:ℚ)/((28627:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28627:ℚ)/((28627:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28627:ℚ)/((28627:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28627:ℚ)/((28627:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1453107291011 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((28627:ℚ)/((28627:ℚ)-1)) : ℚ) ≤ ((290624951469 : ℚ) / 100000000000) := by decide +kernel
  have hratR : ((((1453107291011 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28627:ℚ)/((28627:ℚ)-1)) : ℚ) : ℝ) ≤ ((((290624951469 : ℚ) / 100000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3117 : Commons.NumberTheory.Mertens.logRatioSum ((28631 : ℕ) : ℝ) ≤ ((((2906284442477 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28627 < q → q < 28631 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28631).mp (by decide +kernel))) hgap
  have hprev := lrU_3116
  have hcast : (((28631:ℕ):ℝ)/(((28631:ℕ):ℝ)-1)) = (((28631:ℚ)/((28631:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28631:ℚ)/((28631:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28631:ℚ)/((28631:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28631:ℚ)/((28631:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((290624951469 : ℚ) / 100000000000) + Work.RHContract.RegionI.logUpQ (((28631:ℚ)/((28631:ℚ)-1)) : ℚ) ≤ ((2906284442477 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((290624951469 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28631:ℚ)/((28631:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2906284442477 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3118 : Commons.NumberTheory.Mertens.logRatioSum ((28643 : ℕ) : ℝ) ≤ ((((2906319355631 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28631 < q → q < 28643 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28643).mp (by decide +kernel))) hgap
  have hprev := lrU_3117
  have hcast : (((28643:ℕ):ℝ)/(((28643:ℕ):ℝ)-1)) = (((28643:ℚ)/((28643:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28643:ℚ)/((28643:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28643:ℚ)/((28643:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28643:ℚ)/((28643:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2906284442477 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((28643:ℚ)/((28643:ℚ)-1)) : ℚ) ≤ ((2906319355631 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2906284442477 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28643:ℚ)/((28643:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2906319355631 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3119 : Commons.NumberTheory.Mertens.logRatioSum ((28649 : ℕ) : ℝ) ≤ ((((2906354261473 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28643 < q → q < 28649 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28649).mp (by decide +kernel))) hgap
  have hprev := lrU_3118
  have hcast : (((28649:ℕ):ℝ)/(((28649:ℕ):ℝ)-1)) = (((28649:ℚ)/((28649:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28649:ℚ)/((28649:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28649:ℚ)/((28649:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28649:ℚ)/((28649:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2906319355631 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((28649:ℚ)/((28649:ℚ)-1)) : ℚ) ≤ ((2906354261473 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2906319355631 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28649:ℚ)/((28649:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2906354261473 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3120 : Commons.NumberTheory.Mertens.logRatioSum ((28657 : ℕ) : ℝ) ≤ ((((290638915757 : ℚ) / 100000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28649 < q → q < 28657 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28657).mp (by decide +kernel))) hgap
  have hprev := lrU_3119
  have hcast : (((28657:ℕ):ℝ)/(((28657:ℕ):ℝ)-1)) = (((28657:ℚ)/((28657:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28657:ℚ)/((28657:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28657:ℚ)/((28657:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28657:ℚ)/((28657:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2906354261473 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((28657:ℚ)/((28657:ℚ)-1)) : ℚ) ≤ ((290638915757 : ℚ) / 100000000000) := by decide +kernel
  have hratR : ((((2906354261473 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28657:ℚ)/((28657:ℚ)-1)) : ℚ) : ℝ) ≤ ((((290638915757 : ℚ) / 100000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3121 : Commons.NumberTheory.Mertens.logRatioSum ((28661 : ℕ) : ℝ) ≤ ((((2906424048797 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28657 < q → q < 28661 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28661).mp (by decide +kernel))) hgap
  have hprev := lrU_3120
  have hcast : (((28661:ℕ):ℝ)/(((28661:ℕ):ℝ)-1)) = (((28661:ℚ)/((28661:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28661:ℚ)/((28661:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28661:ℚ)/((28661:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28661:ℚ)/((28661:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((290638915757 : ℚ) / 100000000000) + Work.RHContract.RegionI.logUpQ (((28661:ℚ)/((28661:ℚ)-1)) : ℚ) ≤ ((2906424048797 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((290638915757 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28661:ℚ)/((28661:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2906424048797 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3122 : Commons.NumberTheory.Mertens.logRatioSum ((28663 : ℕ) : ℝ) ≤ ((((2906458937589 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28661 < q → q < 28663 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28663).mp (by decide +kernel))) hgap
  have hprev := lrU_3121
  have hcast : (((28663:ℕ):ℝ)/(((28663:ℕ):ℝ)-1)) = (((28663:ℚ)/((28663:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28663:ℚ)/((28663:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28663:ℚ)/((28663:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28663:ℚ)/((28663:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2906424048797 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((28663:ℚ)/((28663:ℚ)-1)) : ℚ) ≤ ((2906458937589 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2906424048797 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28663:ℚ)/((28663:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2906458937589 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3123 : Commons.NumberTheory.Mertens.logRatioSum ((28669 : ℕ) : ℝ) ≤ ((((72662345477 : ℚ) / 25000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28663 < q → q < 28669 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28669).mp (by decide +kernel))) hgap
  have hprev := lrU_3122
  have hcast : (((28669:ℕ):ℝ)/(((28669:ℕ):ℝ)-1)) = (((28669:ℚ)/((28669:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28669:ℚ)/((28669:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28669:ℚ)/((28669:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28669:ℚ)/((28669:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2906458937589 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((28669:ℚ)/((28669:ℚ)-1)) : ℚ) ≤ ((72662345477 : ℚ) / 25000000000) := by decide +kernel
  have hratR : ((((2906458937589 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28669:ℚ)/((28669:ℚ)-1)) : ℚ) : ℝ) ≤ ((((72662345477 : ℚ) / 25000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3124 : Commons.NumberTheory.Mertens.logRatioSum ((28687 : ℕ) : ℝ) ≤ ((((2906528678683 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28669 < q → q < 28687 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28687).mp (by decide +kernel))) hgap
  have hprev := lrU_3123
  have hcast : (((28687:ℕ):ℝ)/(((28687:ℕ):ℝ)-1)) = (((28687:ℚ)/((28687:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28687:ℚ)/((28687:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28687:ℚ)/((28687:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28687:ℚ)/((28687:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((72662345477 : ℚ) / 25000000000) + Work.RHContract.RegionI.logUpQ (((28687:ℚ)/((28687:ℚ)-1)) : ℚ) ≤ ((2906528678683 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((72662345477 : ℚ) / 25000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28687:ℚ)/((28687:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2906528678683 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3125 : Commons.NumberTheory.Mertens.logRatioSum ((28697 : ℕ) : ℝ) ≤ ((((2906563526139 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28687 < q → q < 28697 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28697).mp (by decide +kernel))) hgap
  have hprev := lrU_3124
  have hcast : (((28697:ℕ):ℝ)/(((28697:ℕ):ℝ)-1)) = (((28697:ℚ)/((28697:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28697:ℚ)/((28697:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28697:ℚ)/((28697:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28697:ℚ)/((28697:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2906528678683 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((28697:ℚ)/((28697:ℚ)-1)) : ℚ) ≤ ((2906563526139 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2906528678683 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28697:ℚ)/((28697:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2906563526139 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3126 : Commons.NumberTheory.Mertens.logRatioSum ((28703 : ℕ) : ℝ) ≤ ((((290659836631 : ℚ) / 100000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28697 < q → q < 28703 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28703).mp (by decide +kernel))) hgap
  have hprev := lrU_3125
  have hcast : (((28703:ℕ):ℝ)/(((28703:ℕ):ℝ)-1)) = (((28703:ℚ)/((28703:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28703:ℚ)/((28703:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28703:ℚ)/((28703:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28703:ℚ)/((28703:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2906563526139 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((28703:ℚ)/((28703:ℚ)-1)) : ℚ) ≤ ((290659836631 : ℚ) / 100000000000) := by decide +kernel
  have hratR : ((((2906563526139 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28703:ℚ)/((28703:ℚ)-1)) : ℚ) : ℝ) ≤ ((((290659836631 : ℚ) / 100000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3127 : Commons.NumberTheory.Mertens.logRatioSum ((28711 : ℕ) : ℝ) ≤ ((((2906633196773 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28703 < q → q < 28711 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28711).mp (by decide +kernel))) hgap
  have hprev := lrU_3126
  have hcast : (((28711:ℕ):ℝ)/(((28711:ℕ):ℝ)-1)) = (((28711:ℚ)/((28711:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28711:ℚ)/((28711:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28711:ℚ)/((28711:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28711:ℚ)/((28711:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((290659836631 : ℚ) / 100000000000) + Work.RHContract.RegionI.logUpQ (((28711:ℚ)/((28711:ℚ)-1)) : ℚ) ≤ ((2906633196773 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((290659836631 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28711:ℚ)/((28711:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2906633196773 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3128 : Commons.NumberTheory.Mertens.logRatioSum ((28723 : ℕ) : ℝ) ≤ ((((726667003171 : ℚ) / 250000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28711 < q → q < 28723 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28723).mp (by decide +kernel))) hgap
  have hprev := lrU_3127
  have hcast : (((28723:ℕ):ℝ)/(((28723:ℕ):ℝ)-1)) = (((28723:ℚ)/((28723:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28723:ℚ)/((28723:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28723:ℚ)/((28723:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28723:ℚ)/((28723:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2906633196773 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((28723:ℚ)/((28723:ℚ)-1)) : ℚ) ≤ ((726667003171 : ℚ) / 250000000000) := by decide +kernel
  have hratR : ((((2906633196773 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28723:ℚ)/((28723:ℚ)-1)) : ℚ) : ℝ) ≤ ((((726667003171 : ℚ) / 250000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3129 : Commons.NumberTheory.Mertens.logRatioSum ((28729 : ℕ) : ℝ) ≤ ((((726675705331 : ℚ) / 250000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28723 < q → q < 28729 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28729).mp (by decide +kernel))) hgap
  have hprev := lrU_3128
  have hcast : (((28729:ℕ):ℝ)/(((28729:ℕ):ℝ)-1)) = (((28729:ℚ)/((28729:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28729:ℚ)/((28729:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28729:ℚ)/((28729:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28729:ℚ)/((28729:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((726667003171 : ℚ) / 250000000000) + Work.RHContract.RegionI.logUpQ (((28729:ℚ)/((28729:ℚ)-1)) : ℚ) ≤ ((726675705331 : ℚ) / 250000000000) := by decide +kernel
  have hratR : ((((726667003171 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28729:ℚ)/((28729:ℚ)-1)) : ℚ) : ℝ) ≤ ((((726675705331 : ℚ) / 250000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3130 : Commons.NumberTheory.Mertens.logRatioSum ((28751 : ℕ) : ℝ) ≤ ((((11354443763 : ℚ) / 3906250000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28729 < q → q < 28751 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28751).mp (by decide +kernel))) hgap
  have hprev := lrU_3129
  have hcast : (((28751:ℕ):ℝ)/(((28751:ℕ):ℝ)-1)) = (((28751:ℚ)/((28751:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28751:ℚ)/((28751:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28751:ℚ)/((28751:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28751:ℚ)/((28751:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((726675705331 : ℚ) / 250000000000) + Work.RHContract.RegionI.logUpQ (((28751:ℚ)/((28751:ℚ)-1)) : ℚ) ≤ ((11354443763 : ℚ) / 3906250000) := by decide +kernel
  have hratR : ((((726675705331 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28751:ℚ)/((28751:ℚ)-1)) : ℚ) : ℝ) ≤ ((((11354443763 : ℚ) / 3906250000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3131 : Commons.NumberTheory.Mertens.logRatioSum ((28753 : ℕ) : ℝ) ≤ ((((2906772382913 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28751 < q → q < 28753 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28753).mp (by decide +kernel))) hgap
  have hprev := lrU_3130
  have hcast : (((28753:ℕ):ℝ)/(((28753:ℕ):ℝ)-1)) = (((28753:ℚ)/((28753:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28753:ℚ)/((28753:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28753:ℚ)/((28753:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28753:ℚ)/((28753:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((11354443763 : ℚ) / 3906250000) + Work.RHContract.RegionI.logUpQ (((28753:ℚ)/((28753:ℚ)-1)) : ℚ) ≤ ((2906772382913 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((11354443763 : ℚ) / 3906250000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28753:ℚ)/((28753:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2906772382913 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3132 : Commons.NumberTheory.Mertens.logRatioSum ((28759 : ℕ) : ℝ) ≤ ((((1453403577621 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28753 < q → q < 28759 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28759).mp (by decide +kernel))) hgap
  have hprev := lrU_3131
  have hcast : (((28759:ℕ):ℝ)/(((28759:ℕ):ℝ)-1)) = (((28759:ℚ)/((28759:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28759:ℚ)/((28759:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28759:ℚ)/((28759:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28759:ℚ)/((28759:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2906772382913 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((28759:ℚ)/((28759:ℚ)-1)) : ℚ) ≤ ((1453403577621 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((2906772382913 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28759:ℚ)/((28759:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1453403577621 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3133 : Commons.NumberTheory.Mertens.logRatioSum ((28771 : ℕ) : ℝ) ≤ ((((2906841913067 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28759 < q → q < 28771 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28771).mp (by decide +kernel))) hgap
  have hprev := lrU_3132
  have hcast : (((28771:ℕ):ℝ)/(((28771:ℕ):ℝ)-1)) = (((28771:ℚ)/((28771:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28771:ℚ)/((28771:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28771:ℚ)/((28771:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28771:ℚ)/((28771:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1453403577621 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((28771:ℚ)/((28771:ℚ)-1)) : ℚ) ≤ ((2906841913067 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((1453403577621 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28771:ℚ)/((28771:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2906841913067 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3134 : Commons.NumberTheory.Mertens.logRatioSum ((28789 : ℕ) : ℝ) ≤ ((((72671916229 : ℚ) / 25000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28771 < q → q < 28789 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28789).mp (by decide +kernel))) hgap
  have hprev := lrU_3133
  have hcast : (((28789:ℕ):ℝ)/(((28789:ℕ):ℝ)-1)) = (((28789:ℚ)/((28789:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28789:ℚ)/((28789:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28789:ℚ)/((28789:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28789:ℚ)/((28789:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2906841913067 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((28789:ℚ)/((28789:ℚ)-1)) : ℚ) ≤ ((72671916229 : ℚ) / 25000000000) := by decide +kernel
  have hratR : ((((2906841913067 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28789:ℚ)/((28789:ℚ)-1)) : ℚ) : ℝ) ≤ ((((72671916229 : ℚ) / 25000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3135 : Commons.NumberTheory.Mertens.logRatioSum ((28793 : ℕ) : ℝ) ≤ ((((2906911380427 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28789 < q → q < 28793 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28793).mp (by decide +kernel))) hgap
  have hprev := lrU_3134
  have hcast : (((28793:ℕ):ℝ)/(((28793:ℕ):ℝ)-1)) = (((28793:ℚ)/((28793:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28793:ℚ)/((28793:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28793:ℚ)/((28793:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28793:ℚ)/((28793:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((72671916229 : ℚ) / 25000000000) + Work.RHContract.RegionI.logUpQ (((28793:ℚ)/((28793:ℚ)-1)) : ℚ) ≤ ((2906911380427 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((72671916229 : ℚ) / 25000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28793:ℚ)/((28793:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2906911380427 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3136 : Commons.NumberTheory.Mertens.logRatioSum ((28807 : ℕ) : ℝ) ≤ ((((581389218963 : ℚ) / 200000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28793 < q → q < 28807 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28807).mp (by decide +kernel))) hgap
  have hprev := lrU_3135
  have hcast : (((28807:ℕ):ℝ)/(((28807:ℕ):ℝ)-1)) = (((28807:ℚ)/((28807:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28807:ℚ)/((28807:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28807:ℚ)/((28807:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28807:ℚ)/((28807:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2906911380427 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((28807:ℚ)/((28807:ℚ)-1)) : ℚ) ≤ ((581389218963 : ℚ) / 200000000000) := by decide +kernel
  have hratR : ((((2906911380427 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28807:ℚ)/((28807:ℚ)-1)) : ℚ) : ℝ) ≤ ((((581389218963 : ℚ) / 200000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3137 : Commons.NumberTheory.Mertens.logRatioSum ((28813 : ℕ) : ℝ) ≤ ((((1453490400987 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28807 < q → q < 28813 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28813).mp (by decide +kernel))) hgap
  have hprev := lrU_3136
  have hcast : (((28813:ℕ):ℝ)/(((28813:ℕ):ℝ)-1)) = (((28813:ℚ)/((28813:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28813:ℚ)/((28813:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28813:ℚ)/((28813:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28813:ℚ)/((28813:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((581389218963 : ℚ) / 200000000000) + Work.RHContract.RegionI.logUpQ (((28813:ℚ)/((28813:ℚ)-1)) : ℚ) ≤ ((1453490400987 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((581389218963 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28813:ℚ)/((28813:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1453490400987 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3138 : Commons.NumberTheory.Mertens.logRatioSum ((28817 : ℕ) : ℝ) ≤ ((((581403100863 : ℚ) / 200000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28813 < q → q < 28817 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28817).mp (by decide +kernel))) hgap
  have hprev := lrU_3137
  have hcast : (((28817:ℕ):ℝ)/(((28817:ℕ):ℝ)-1)) = (((28817:ℚ)/((28817:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28817:ℚ)/((28817:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28817:ℚ)/((28817:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28817:ℚ)/((28817:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1453490400987 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((28817:ℚ)/((28817:ℚ)-1)) : ℚ) ≤ ((581403100863 : ℚ) / 200000000000) := by decide +kernel
  have hratR : ((((1453490400987 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28817:ℚ)/((28817:ℚ)-1)) : ℚ) : ℝ) ≤ ((((581403100863 : ℚ) / 200000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3139 : Commons.NumberTheory.Mertens.logRatioSum ((28837 : ℕ) : ℝ) ≤ ((((726762545647 : ℚ) / 250000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28817 < q → q < 28837 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28837).mp (by decide +kernel))) hgap
  have hprev := lrU_3138
  have hcast : (((28837:ℕ):ℝ)/(((28837:ℕ):ℝ)-1)) = (((28837:ℚ)/((28837:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28837:ℚ)/((28837:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28837:ℚ)/((28837:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28837:ℚ)/((28837:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((581403100863 : ℚ) / 200000000000) + Work.RHContract.RegionI.logUpQ (((28837:ℚ)/((28837:ℚ)-1)) : ℚ) ≤ ((726762545647 : ℚ) / 250000000000) := by decide +kernel
  have hratR : ((((581403100863 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28837:ℚ)/((28837:ℚ)-1)) : ℚ) : ℝ) ≤ ((((726762545647 : ℚ) / 250000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3140 : Commons.NumberTheory.Mertens.logRatioSum ((28843 : ℕ) : ℝ) ≤ ((((2907084853647 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28837 < q → q < 28843 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28843).mp (by decide +kernel))) hgap
  have hprev := lrU_3139
  have hcast : (((28843:ℕ):ℝ)/(((28843:ℕ):ℝ)-1)) = (((28843:ℚ)/((28843:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28843:ℚ)/((28843:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28843:ℚ)/((28843:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28843:ℚ)/((28843:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((726762545647 : ℚ) / 250000000000) + Work.RHContract.RegionI.logUpQ (((28843:ℚ)/((28843:ℚ)-1)) : ℚ) ≤ ((2907084853647 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((726762545647 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28843:ℚ)/((28843:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2907084853647 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3141 : Commons.NumberTheory.Mertens.logRatioSum ((28859 : ℕ) : ℝ) ≤ ((((2907119505483 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28843 < q → q < 28859 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28859).mp (by decide +kernel))) hgap
  have hprev := lrU_3140
  have hcast : (((28859:ℕ):ℝ)/(((28859:ℕ):ℝ)-1)) = (((28859:ℚ)/((28859:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28859:ℚ)/((28859:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28859:ℚ)/((28859:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28859:ℚ)/((28859:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2907084853647 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((28859:ℚ)/((28859:ℚ)-1)) : ℚ) ≤ ((2907119505483 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2907084853647 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28859:ℚ)/((28859:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2907119505483 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3142 : Commons.NumberTheory.Mertens.logRatioSum ((28867 : ℕ) : ℝ) ≤ ((((726788536929 : ℚ) / 250000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28859 < q → q < 28867 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28867).mp (by decide +kernel))) hgap
  have hprev := lrU_3141
  have hcast : (((28867:ℕ):ℝ)/(((28867:ℕ):ℝ)-1)) = (((28867:ℚ)/((28867:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28867:ℚ)/((28867:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28867:ℚ)/((28867:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28867:ℚ)/((28867:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2907119505483 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((28867:ℚ)/((28867:ℚ)-1)) : ℚ) ≤ ((726788536929 : ℚ) / 250000000000) := by decide +kernel
  have hratR : ((((2907119505483 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28867:ℚ)/((28867:ℚ)-1)) : ℚ) : ℝ) ≤ ((((726788536929 : ℚ) / 250000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3143 : Commons.NumberTheory.Mertens.logRatioSum ((28871 : ℕ) : ℝ) ≤ ((((2907188785149 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28867 < q → q < 28871 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28871).mp (by decide +kernel))) hgap
  have hprev := lrU_3142
  have hcast : (((28871:ℕ):ℝ)/(((28871:ℕ):ℝ)-1)) = (((28871:ℚ)/((28871:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28871:ℚ)/((28871:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28871:ℚ)/((28871:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28871:ℚ)/((28871:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((726788536929 : ℚ) / 250000000000) + Work.RHContract.RegionI.logUpQ (((28871:ℚ)/((28871:ℚ)-1)) : ℚ) ≤ ((2907188785149 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((726788536929 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28871:ℚ)/((28871:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2907188785149 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3144 : Commons.NumberTheory.Mertens.logRatioSum ((28879 : ℕ) : ℝ) ≤ ((((2907223412987 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28871 < q → q < 28879 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28879).mp (by decide +kernel))) hgap
  have hprev := lrU_3143
  have hcast : (((28879:ℕ):ℝ)/(((28879:ℕ):ℝ)-1)) = (((28879:ℚ)/((28879:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28879:ℚ)/((28879:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28879:ℚ)/((28879:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28879:ℚ)/((28879:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2907188785149 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((28879:ℚ)/((28879:ℚ)-1)) : ℚ) ≤ ((2907223412987 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2907188785149 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28879:ℚ)/((28879:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2907223412987 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3145 : Commons.NumberTheory.Mertens.logRatioSum ((28901 : ℕ) : ℝ) ≤ ((((581451602893 : ℚ) / 200000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28879 < q → q < 28901 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28901).mp (by decide +kernel))) hgap
  have hprev := lrU_3144
  have hcast : (((28901:ℕ):ℝ)/(((28901:ℕ):ℝ)-1)) = (((28901:ℚ)/((28901:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28901:ℚ)/((28901:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28901:ℚ)/((28901:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28901:ℚ)/((28901:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2907223412987 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((28901:ℚ)/((28901:ℚ)-1)) : ℚ) ≤ ((581451602893 : ℚ) / 200000000000) := by decide +kernel
  have hratR : ((((2907223412987 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28901:ℚ)/((28901:ℚ)-1)) : ℚ) : ℝ) ≤ ((((581451602893 : ℚ) / 200000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3146 : Commons.NumberTheory.Mertens.logRatioSum ((28909 : ℕ) : ℝ) ≤ ((((90852893949 : ℚ) / 31250000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28901 < q → q < 28909 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28909).mp (by decide +kernel))) hgap
  have hprev := lrU_3145
  have hcast : (((28909:ℕ):ℝ)/(((28909:ℕ):ℝ)-1)) = (((28909:ℚ)/((28909:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28909:ℚ)/((28909:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28909:ℚ)/((28909:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28909:ℚ)/((28909:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((581451602893 : ℚ) / 200000000000) + Work.RHContract.RegionI.logUpQ (((28909:ℚ)/((28909:ℚ)-1)) : ℚ) ≤ ((90852893949 : ℚ) / 31250000000) := by decide +kernel
  have hratR : ((((581451602893 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28909:ℚ)/((28909:ℚ)-1)) : ℚ) : ℝ) ≤ ((((90852893949 : ℚ) / 31250000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3147 : Commons.NumberTheory.Mertens.logRatioSum ((28921 : ℕ) : ℝ) ≤ ((((2907327183917 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28909 < q → q < 28921 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28921).mp (by decide +kernel))) hgap
  have hprev := lrU_3146
  have hcast : (((28921:ℕ):ℝ)/(((28921:ℕ):ℝ)-1)) = (((28921:ℚ)/((28921:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28921:ℚ)/((28921:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28921:ℚ)/((28921:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28921:ℚ)/((28921:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((90852893949 : ℚ) / 31250000000) + Work.RHContract.RegionI.logUpQ (((28921:ℚ)/((28921:ℚ)-1)) : ℚ) ≤ ((2907327183917 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((90852893949 : ℚ) / 31250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28921:ℚ)/((28921:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2907327183917 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3148 : Commons.NumberTheory.Mertens.logRatioSum ((28927 : ℕ) : ℝ) ≤ ((((1453680877147 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28921 < q → q < 28927 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28927).mp (by decide +kernel))) hgap
  have hprev := lrU_3147
  have hcast : (((28927:ℕ):ℝ)/(((28927:ℕ):ℝ)-1)) = (((28927:ℚ)/((28927:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28927:ℚ)/((28927:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28927:ℚ)/((28927:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28927:ℚ)/((28927:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2907327183917 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((28927:ℚ)/((28927:ℚ)-1)) : ℚ) ≤ ((1453680877147 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((2907327183917 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28927:ℚ)/((28927:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1453680877147 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3149 : Commons.NumberTheory.Mertens.logRatioSum ((28933 : ℕ) : ℝ) ≤ ((((1453698158751 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28927 < q → q < 28933 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28933).mp (by decide +kernel))) hgap
  have hprev := lrU_3148
  have hcast : (((28933:ℕ):ℝ)/(((28933:ℕ):ℝ)-1)) = (((28933:ℚ)/((28933:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28933:ℚ)/((28933:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28933:ℚ)/((28933:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28933:ℚ)/((28933:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1453680877147 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((28933:ℚ)/((28933:ℚ)-1)) : ℚ) ≤ ((1453698158751 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((1453680877147 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28933:ℚ)/((28933:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1453698158751 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3150 : Commons.NumberTheory.Mertens.logRatioSum ((28949 : ℕ) : ℝ) ≤ ((((2907430861607 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28933 < q → q < 28949 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28949).mp (by decide +kernel))) hgap
  have hprev := lrU_3149
  have hcast : (((28949:ℕ):ℝ)/(((28949:ℕ):ℝ)-1)) = (((28949:ℚ)/((28949:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28949:ℚ)/((28949:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28949:ℚ)/((28949:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28949:ℚ)/((28949:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1453698158751 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((28949:ℚ)/((28949:ℚ)-1)) : ℚ) ≤ ((2907430861607 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((1453698158751 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28949:ℚ)/((28949:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2907430861607 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3151 : Commons.NumberTheory.Mertens.logRatioSum ((28961 : ℕ) : ℝ) ≤ ((((1453732695699 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28949 < q → q < 28961 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28961).mp (by decide +kernel))) hgap
  have hprev := lrU_3150
  have hcast : (((28961:ℕ):ℝ)/(((28961:ℕ):ℝ)-1)) = (((28961:ℚ)/((28961:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28961:ℚ)/((28961:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28961:ℚ)/((28961:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28961:ℚ)/((28961:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2907430861607 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((28961:ℚ)/((28961:ℚ)-1)) : ℚ) ≤ ((1453732695699 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((2907430861607 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28961:ℚ)/((28961:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1453732695699 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3152 : Commons.NumberTheory.Mertens.logRatioSum ((28979 : ℕ) : ℝ) ≤ ((((2907499899741 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28961 < q → q < 28979 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28979).mp (by decide +kernel))) hgap
  have hprev := lrU_3151
  have hcast : (((28979:ℕ):ℝ)/(((28979:ℕ):ℝ)-1)) = (((28979:ℚ)/((28979:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((28979:ℚ)/((28979:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((28979:ℚ)/((28979:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((28979:ℚ)/((28979:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1453732695699 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((28979:ℚ)/((28979:ℚ)-1)) : ℚ) ≤ ((2907499899741 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((1453732695699 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((28979:ℚ)/((28979:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2907499899741 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3153 : Commons.NumberTheory.Mertens.logRatioSum ((29009 : ℕ) : ℝ) ≤ ((((726883593099 : ℚ) / 250000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 28979 < q → q < 29009 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29009).mp (by decide +kernel))) hgap
  have hprev := lrU_3152
  have hcast : (((29009:ℕ):ℝ)/(((29009:ℕ):ℝ)-1)) = (((29009:ℚ)/((29009:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29009:ℚ)/((29009:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29009:ℚ)/((29009:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29009:ℚ)/((29009:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2907499899741 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((29009:ℚ)/((29009:ℚ)-1)) : ℚ) ≤ ((726883593099 : ℚ) / 250000000000) := by decide +kernel
  have hratR : ((((2907499899741 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29009:ℚ)/((29009:ℚ)-1)) : ℚ) : ℝ) ≤ ((((726883593099 : ℚ) / 250000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3154 : Commons.NumberTheory.Mertens.logRatioSum ((29017 : ℕ) : ℝ) ≤ ((((2907568835547 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29009 < q → q < 29017 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29017).mp (by decide +kernel))) hgap
  have hprev := lrU_3153
  have hcast : (((29017:ℕ):ℝ)/(((29017:ℕ):ℝ)-1)) = (((29017:ℚ)/((29017:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29017:ℚ)/((29017:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29017:ℚ)/((29017:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29017:ℚ)/((29017:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((726883593099 : ℚ) / 250000000000) + Work.RHContract.RegionI.logUpQ (((29017:ℚ)/((29017:ℚ)-1)) : ℚ) ≤ ((2907568835547 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((726883593099 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29017:ℚ)/((29017:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2907568835547 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3155 : Commons.NumberTheory.Mertens.logRatioSum ((29021 : ℕ) : ℝ) ≤ ((((726900823487 : ℚ) / 250000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29017 < q → q < 29021 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29021).mp (by decide +kernel))) hgap
  have hprev := lrU_3154
  have hcast : (((29021:ℕ):ℝ)/(((29021:ℕ):ℝ)-1)) = (((29021:ℚ)/((29021:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29021:ℚ)/((29021:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29021:ℚ)/((29021:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29021:ℚ)/((29021:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2907568835547 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((29021:ℚ)/((29021:ℚ)-1)) : ℚ) ≤ ((726900823487 : ℚ) / 250000000000) := by decide +kernel
  have hratR : ((((2907568835547 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29021:ℚ)/((29021:ℚ)-1)) : ℚ) : ℝ) ≤ ((((726900823487 : ℚ) / 250000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3156 : Commons.NumberTheory.Mertens.logRatioSum ((29023 : ℕ) : ℝ) ≤ ((((1453818874987 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29021 < q → q < 29023 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29023).mp (by decide +kernel))) hgap
  have hprev := lrU_3155
  have hcast : (((29023:ℕ):ℝ)/(((29023:ℕ):ℝ)-1)) = (((29023:ℚ)/((29023:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29023:ℚ)/((29023:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29023:ℚ)/((29023:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29023:ℚ)/((29023:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((726900823487 : ℚ) / 250000000000) + Work.RHContract.RegionI.logUpQ (((29023:ℚ)/((29023:ℚ)-1)) : ℚ) ≤ ((1453818874987 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((726900823487 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29023:ℚ)/((29023:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1453818874987 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3157 : Commons.NumberTheory.Mertens.logRatioSum ((29027 : ℕ) : ℝ) ≤ ((((726918050313 : ℚ) / 250000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29023 < q → q < 29027 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29027).mp (by decide +kernel))) hgap
  have hprev := lrU_3156
  have hcast : (((29027:ℕ):ℝ)/(((29027:ℕ):ℝ)-1)) = (((29027:ℚ)/((29027:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29027:ℚ)/((29027:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29027:ℚ)/((29027:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29027:ℚ)/((29027:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1453818874987 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((29027:ℚ)/((29027:ℚ)-1)) : ℚ) ≤ ((726918050313 : ℚ) / 250000000000) := by decide +kernel
  have hratR : ((((1453818874987 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29027:ℚ)/((29027:ℚ)-1)) : ℚ) : ℝ) ≤ ((((726918050313 : ℚ) / 250000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3158 : Commons.NumberTheory.Mertens.logRatioSum ((29033 : ℕ) : ℝ) ≤ ((((290770664541 : ℚ) / 100000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29027 < q → q < 29033 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29033).mp (by decide +kernel))) hgap
  have hprev := lrU_3157
  have hcast : (((29033:ℕ):ℝ)/(((29033:ℕ):ℝ)-1)) = (((29033:ℚ)/((29033:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29033:ℚ)/((29033:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29033:ℚ)/((29033:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29033:ℚ)/((29033:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((726918050313 : ℚ) / 250000000000) + Work.RHContract.RegionI.logUpQ (((29033:ℚ)/((29033:ℚ)-1)) : ℚ) ≤ ((290770664541 : ℚ) / 100000000000) := by decide +kernel
  have hratR : ((((726918050313 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29033:ℚ)/((29033:ℚ)-1)) : ℚ) : ℝ) ≤ ((((290770664541 : ℚ) / 100000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3159 : Commons.NumberTheory.Mertens.logRatioSum ((29059 : ℕ) : ℝ) ≤ ((((2907741058749 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29033 < q → q < 29059 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29059).mp (by decide +kernel))) hgap
  have hprev := lrU_3158
  have hcast : (((29059:ℕ):ℝ)/(((29059:ℕ):ℝ)-1)) = (((29059:ℚ)/((29059:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29059:ℚ)/((29059:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29059:ℚ)/((29059:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29059:ℚ)/((29059:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((290770664541 : ℚ) / 100000000000) + Work.RHContract.RegionI.logUpQ (((29059:ℚ)/((29059:ℚ)-1)) : ℚ) ≤ ((2907741058749 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((290770664541 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29059:ℚ)/((29059:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2907741058749 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3160 : Commons.NumberTheory.Mertens.logRatioSum ((29063 : ℕ) : ℝ) ≤ ((((363471933419 : ℚ) / 125000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29059 < q → q < 29063 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29063).mp (by decide +kernel))) hgap
  have hprev := lrU_3159
  have hcast : (((29063:ℕ):ℝ)/(((29063:ℕ):ℝ)-1)) = (((29063:ℚ)/((29063:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29063:ℚ)/((29063:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29063:ℚ)/((29063:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29063:ℚ)/((29063:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2907741058749 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((29063:ℚ)/((29063:ℚ)-1)) : ℚ) ≤ ((363471933419 : ℚ) / 125000000000) := by decide +kernel
  have hratR : ((((2907741058749 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29063:ℚ)/((29063:ℚ)-1)) : ℚ) : ℝ) ≤ ((((363471933419 : ℚ) / 125000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3161 : Commons.NumberTheory.Mertens.logRatioSum ((29077 : ℕ) : ℝ) ≤ ((((2907809859387 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29063 < q → q < 29077 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29077).mp (by decide +kernel))) hgap
  have hprev := lrU_3160
  have hcast : (((29077:ℕ):ℝ)/(((29077:ℕ):ℝ)-1)) = (((29077:ℚ)/((29077:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29077:ℚ)/((29077:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29077:ℚ)/((29077:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29077:ℚ)/((29077:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((363471933419 : ℚ) / 125000000000) + Work.RHContract.RegionI.logUpQ (((29077:ℚ)/((29077:ℚ)-1)) : ℚ) ≤ ((2907809859387 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((363471933419 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29077:ℚ)/((29077:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2907809859387 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3162 : Commons.NumberTheory.Mertens.logRatioSum ((29101 : ℕ) : ℝ) ≤ ((((1453922111529 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29077 < q → q < 29101 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29101).mp (by decide +kernel))) hgap
  have hprev := lrU_3161
  have hcast : (((29101:ℕ):ℝ)/(((29101:ℕ):ℝ)-1)) = (((29101:ℚ)/((29101:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29101:ℚ)/((29101:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29101:ℚ)/((29101:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29101:ℚ)/((29101:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2907809859387 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((29101:ℚ)/((29101:ℚ)-1)) : ℚ) ≤ ((1453922111529 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((2907809859387 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29101:ℚ)/((29101:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1453922111529 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3163 : Commons.NumberTheory.Mertens.logRatioSum ((29123 : ℕ) : ℝ) ≤ ((((290787856077 : ℚ) / 100000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29101 < q → q < 29123 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29123).mp (by decide +kernel))) hgap
  have hprev := lrU_3162
  have hcast : (((29123:ℕ):ℝ)/(((29123:ℕ):ℝ)-1)) = (((29123:ℚ)/((29123:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29123:ℚ)/((29123:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29123:ℚ)/((29123:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29123:ℚ)/((29123:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1453922111529 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((29123:ℚ)/((29123:ℚ)-1)) : ℚ) ≤ ((290787856077 : ℚ) / 100000000000) := by decide +kernel
  have hratR : ((((1453922111529 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29123:ℚ)/((29123:ℚ)-1)) : ℚ) : ℝ) ≤ ((((290787856077 : ℚ) / 100000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3164 : Commons.NumberTheory.Mertens.logRatioSum ((29129 : ℕ) : ℝ) ≤ ((((2907912891409 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29123 < q → q < 29129 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29129).mp (by decide +kernel))) hgap
  have hprev := lrU_3163
  have hcast : (((29129:ℕ):ℝ)/(((29129:ℕ):ℝ)-1)) = (((29129:ℚ)/((29129:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29129:ℚ)/((29129:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29129:ℚ)/((29129:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29129:ℚ)/((29129:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((290787856077 : ℚ) / 100000000000) + Work.RHContract.RegionI.logUpQ (((29129:ℚ)/((29129:ℚ)-1)) : ℚ) ≤ ((2907912891409 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((290787856077 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29129:ℚ)/((29129:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2907912891409 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3165 : Commons.NumberTheory.Mertens.logRatioSum ((29131 : ℕ) : ℝ) ≤ ((((2907947219691 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29129 < q → q < 29131 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29131).mp (by decide +kernel))) hgap
  have hprev := lrU_3164
  have hcast : (((29131:ℕ):ℝ)/(((29131:ℕ):ℝ)-1)) = (((29131:ℚ)/((29131:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29131:ℚ)/((29131:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29131:ℚ)/((29131:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29131:ℚ)/((29131:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2907912891409 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((29131:ℚ)/((29131:ℚ)-1)) : ℚ) ≤ ((2907947219691 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2907912891409 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29131:ℚ)/((29131:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2907947219691 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3166 : Commons.NumberTheory.Mertens.logRatioSum ((29137 : ℕ) : ℝ) ≤ ((((363497692613 : ℚ) / 125000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29131 < q → q < 29137 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29137).mp (by decide +kernel))) hgap
  have hprev := lrU_3165
  have hcast : (((29137:ℕ):ℝ)/(((29137:ℕ):ℝ)-1)) = (((29137:ℚ)/((29137:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29137:ℚ)/((29137:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29137:ℚ)/((29137:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29137:ℚ)/((29137:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2907947219691 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((29137:ℚ)/((29137:ℚ)-1)) : ℚ) ≤ ((363497692613 : ℚ) / 125000000000) := by decide +kernel
  have hratR : ((((2907947219691 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29137:ℚ)/((29137:ℚ)-1)) : ℚ) : ℝ) ≤ ((((363497692613 : ℚ) / 125000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3167 : Commons.NumberTheory.Mertens.logRatioSum ((29147 : ℕ) : ℝ) ≤ ((((2908015850341 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29137 < q → q < 29147 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29147).mp (by decide +kernel))) hgap
  have hprev := lrU_3166
  have hcast : (((29147:ℕ):ℝ)/(((29147:ℕ):ℝ)-1)) = (((29147:ℚ)/((29147:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29147:ℚ)/((29147:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29147:ℚ)/((29147:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29147:ℚ)/((29147:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((363497692613 : ℚ) / 125000000000) + Work.RHContract.RegionI.logUpQ (((29147:ℚ)/((29147:ℚ)-1)) : ℚ) ≤ ((2908015850341 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((363497692613 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29147:ℚ)/((29147:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2908015850341 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3168 : Commons.NumberTheory.Mertens.logRatioSum ((29153 : ℕ) : ℝ) ≤ ((((2908050152717 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29147 < q → q < 29153 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29153).mp (by decide +kernel))) hgap
  have hprev := lrU_3167
  have hcast : (((29153:ℕ):ℝ)/(((29153:ℕ):ℝ)-1)) = (((29153:ℚ)/((29153:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29153:ℚ)/((29153:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29153:ℚ)/((29153:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29153:ℚ)/((29153:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2908015850341 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((29153:ℚ)/((29153:ℚ)-1)) : ℚ) ≤ ((2908050152717 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2908015850341 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29153:ℚ)/((29153:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2908050152717 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3169 : Commons.NumberTheory.Mertens.logRatioSum ((29167 : ℕ) : ℝ) ≤ ((((727021109657 : ℚ) / 250000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29153 < q → q < 29167 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29167).mp (by decide +kernel))) hgap
  have hprev := lrU_3168
  have hcast : (((29167:ℕ):ℝ)/(((29167:ℕ):ℝ)-1)) = (((29167:ℚ)/((29167:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29167:ℚ)/((29167:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29167:ℚ)/((29167:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29167:ℚ)/((29167:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2908050152717 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((29167:ℚ)/((29167:ℚ)-1)) : ℚ) ≤ ((727021109657 : ℚ) / 250000000000) := by decide +kernel
  have hratR : ((((2908050152717 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29167:ℚ)/((29167:ℚ)-1)) : ℚ) : ℝ) ≤ ((((727021109657 : ℚ) / 250000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3170 : Commons.NumberTheory.Mertens.logRatioSum ((29173 : ℕ) : ℝ) ≤ ((((2908118717487 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29167 < q → q < 29173 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29173).mp (by decide +kernel))) hgap
  have hprev := lrU_3169
  have hcast : (((29173:ℕ):ℝ)/(((29173:ℕ):ℝ)-1)) = (((29173:ℚ)/((29173:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29173:ℚ)/((29173:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29173:ℚ)/((29173:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29173:ℚ)/((29173:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((727021109657 : ℚ) / 250000000000) + Work.RHContract.RegionI.logUpQ (((29173:ℚ)/((29173:ℚ)-1)) : ℚ) ≤ ((2908118717487 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((727021109657 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29173:ℚ)/((29173:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2908118717487 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3171 : Commons.NumberTheory.Mertens.logRatioSum ((29179 : ℕ) : ℝ) ≤ ((((2908152989297 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29173 < q → q < 29179 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29179).mp (by decide +kernel))) hgap
  have hprev := lrU_3170
  have hcast : (((29179:ℕ):ℝ)/(((29179:ℕ):ℝ)-1)) = (((29179:ℚ)/((29179:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29179:ℚ)/((29179:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29179:ℚ)/((29179:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29179:ℚ)/((29179:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2908118717487 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((29179:ℚ)/((29179:ℚ)-1)) : ℚ) ≤ ((2908152989297 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2908118717487 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29179:ℚ)/((29179:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2908152989297 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3172 : Commons.NumberTheory.Mertens.logRatioSum ((29191 : ℕ) : ℝ) ≤ ((((1454093623509 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29179 < q → q < 29191 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29191).mp (by decide +kernel))) hgap
  have hprev := lrU_3171
  have hcast : (((29191:ℕ):ℝ)/(((29191:ℕ):ℝ)-1)) = (((29191:ℚ)/((29191:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29191:ℚ)/((29191:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29191:ℚ)/((29191:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29191:ℚ)/((29191:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2908152989297 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((29191:ℚ)/((29191:ℚ)-1)) : ℚ) ≤ ((1454093623509 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((2908152989297 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29191:ℚ)/((29191:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1454093623509 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3173 : Commons.NumberTheory.Mertens.logRatioSum ((29201 : ℕ) : ℝ) ≤ ((((2908221493007 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29191 < q → q < 29201 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29201).mp (by decide +kernel))) hgap
  have hprev := lrU_3172
  have hcast : (((29201:ℕ):ℝ)/(((29201:ℕ):ℝ)-1)) = (((29201:ℚ)/((29201:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29201:ℚ)/((29201:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29201:ℚ)/((29201:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29201:ℚ)/((29201:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1454093623509 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((29201:ℚ)/((29201:ℚ)-1)) : ℚ) ≤ ((2908221493007 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((1454093623509 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29201:ℚ)/((29201:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2908221493007 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3174 : Commons.NumberTheory.Mertens.logRatioSum ((29207 : ℕ) : ℝ) ≤ ((((2908255731961 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29201 < q → q < 29207 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29207).mp (by decide +kernel))) hgap
  have hprev := lrU_3173
  have hcast : (((29207:ℕ):ℝ)/(((29207:ℕ):ℝ)-1)) = (((29207:ℚ)/((29207:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29207:ℚ)/((29207:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29207:ℚ)/((29207:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29207:ℚ)/((29207:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2908221493007 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((29207:ℚ)/((29207:ℚ)-1)) : ℚ) ≤ ((2908255731961 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2908221493007 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29207:ℚ)/((29207:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2908255731961 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3175 : Commons.NumberTheory.Mertens.logRatioSum ((29209 : ℕ) : ℝ) ≤ ((((2908289968571 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29207 < q → q < 29209 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29209).mp (by decide +kernel))) hgap
  have hprev := lrU_3174
  have hcast : (((29209:ℕ):ℝ)/(((29209:ℕ):ℝ)-1)) = (((29209:ℚ)/((29209:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29209:ℚ)/((29209:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29209:ℚ)/((29209:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29209:ℚ)/((29209:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2908255731961 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((29209:ℚ)/((29209:ℚ)-1)) : ℚ) ≤ ((2908289968571 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2908255731961 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29209:ℚ)/((29209:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2908289968571 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3176 : Commons.NumberTheory.Mertens.logRatioSum ((29221 : ℕ) : ℝ) ≤ ((((2908324191121 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29209 < q → q < 29221 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29221).mp (by decide +kernel))) hgap
  have hprev := lrU_3175
  have hcast : (((29221:ℕ):ℝ)/(((29221:ℕ):ℝ)-1)) = (((29221:ℚ)/((29221:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29221:ℚ)/((29221:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29221:ℚ)/((29221:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29221:ℚ)/((29221:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2908289968571 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((29221:ℚ)/((29221:ℚ)-1)) : ℚ) ≤ ((2908324191121 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2908289968571 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29221:ℚ)/((29221:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2908324191121 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3177 : Commons.NumberTheory.Mertens.logRatioSum ((29231 : ℕ) : ℝ) ≤ ((((2908358401963 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29221 < q → q < 29231 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29231).mp (by decide +kernel))) hgap
  have hprev := lrU_3176
  have hcast : (((29231:ℕ):ℝ)/(((29231:ℕ):ℝ)-1)) = (((29231:ℚ)/((29231:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29231:ℚ)/((29231:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29231:ℚ)/((29231:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29231:ℚ)/((29231:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2908324191121 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((29231:ℚ)/((29231:ℚ)-1)) : ℚ) ≤ ((2908358401963 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2908324191121 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29231:ℚ)/((29231:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2908358401963 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3178 : Commons.NumberTheory.Mertens.logRatioSum ((29243 : ℕ) : ℝ) ≤ ((((1454196299383 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29231 < q → q < 29243 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29243).mp (by decide +kernel))) hgap
  have hprev := lrU_3177
  have hcast : (((29243:ℕ):ℝ)/(((29243:ℕ):ℝ)-1)) = (((29243:ℚ)/((29243:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29243:ℚ)/((29243:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29243:ℚ)/((29243:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29243:ℚ)/((29243:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2908358401963 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((29243:ℚ)/((29243:ℚ)-1)) : ℚ) ≤ ((1454196299383 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((2908358401963 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29243:ℚ)/((29243:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1454196299383 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3179 : Commons.NumberTheory.Mertens.logRatioSum ((29251 : ℕ) : ℝ) ≤ ((((363553348277 : ℚ) / 125000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29243 < q → q < 29251 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29251).mp (by decide +kernel))) hgap
  have hprev := lrU_3178
  have hcast : (((29251:ℕ):ℝ)/(((29251:ℕ):ℝ)-1)) = (((29251:ℚ)/((29251:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29251:ℚ)/((29251:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29251:ℚ)/((29251:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29251:ℚ)/((29251:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1454196299383 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((29251:ℚ)/((29251:ℚ)-1)) : ℚ) ≤ ((363553348277 : ℚ) / 125000000000) := by decide +kernel
  have hratR : ((((1454196299383 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29251:ℚ)/((29251:ℚ)-1)) : ℚ) : ℝ) ≤ ((((363553348277 : ℚ) / 125000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3180 : Commons.NumberTheory.Mertens.logRatioSum ((29269 : ℕ) : ℝ) ≤ ((((2908460952641 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29251 < q → q < 29269 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29269).mp (by decide +kernel))) hgap
  have hprev := lrU_3179
  have hcast : (((29269:ℕ):ℝ)/(((29269:ℕ):ℝ)-1)) = (((29269:ℚ)/((29269:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29269:ℚ)/((29269:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29269:ℚ)/((29269:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29269:ℚ)/((29269:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((363553348277 : ℚ) / 125000000000) + Work.RHContract.RegionI.logUpQ (((29269:ℚ)/((29269:ℚ)-1)) : ℚ) ≤ ((2908460952641 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((363553348277 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29269:ℚ)/((29269:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2908460952641 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3181 : Commons.NumberTheory.Mertens.logRatioSum ((29287 : ℕ) : ℝ) ≤ ((((2908495098067 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29269 < q → q < 29287 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29287).mp (by decide +kernel))) hgap
  have hprev := lrU_3180
  have hcast : (((29287:ℕ):ℝ)/(((29287:ℕ):ℝ)-1)) = (((29287:ℚ)/((29287:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29287:ℚ)/((29287:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29287:ℚ)/((29287:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29287:ℚ)/((29287:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2908460952641 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((29287:ℚ)/((29287:ℚ)-1)) : ℚ) ≤ ((2908495098067 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2908460952641 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29287:ℚ)/((29287:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2908495098067 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3182 : Commons.NumberTheory.Mertens.logRatioSum ((29297 : ℕ) : ℝ) ≤ ((((1454264615919 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29287 < q → q < 29297 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29297).mp (by decide +kernel))) hgap
  have hprev := lrU_3181
  have hcast : (((29297:ℕ):ℝ)/(((29297:ℕ):ℝ)-1)) = (((29297:ℚ)/((29297:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29297:ℚ)/((29297:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29297:ℚ)/((29297:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29297:ℚ)/((29297:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2908495098067 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((29297:ℚ)/((29297:ℚ)-1)) : ℚ) ≤ ((1454264615919 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((2908495098067 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29297:ℚ)/((29297:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1454264615919 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3183 : Commons.NumberTheory.Mertens.logRatioSum ((29303 : ℕ) : ℝ) ≤ ((((2908563358619 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29297 < q → q < 29303 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29303).mp (by decide +kernel))) hgap
  have hprev := lrU_3182
  have hcast : (((29303:ℕ):ℝ)/(((29303:ℕ):ℝ)-1)) = (((29303:ℚ)/((29303:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29303:ℚ)/((29303:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29303:ℚ)/((29303:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29303:ℚ)/((29303:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1454264615919 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((29303:ℚ)/((29303:ℚ)-1)) : ℚ) ≤ ((2908563358619 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((1454264615919 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29303:ℚ)/((29303:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2908563358619 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3184 : Commons.NumberTheory.Mertens.logRatioSum ((29311 : ℕ) : ℝ) ≤ ((((1454298738043 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29303 < q → q < 29311 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29311).mp (by decide +kernel))) hgap
  have hprev := lrU_3183
  have hcast : (((29311:ℕ):ℝ)/(((29311:ℕ):ℝ)-1)) = (((29311:ℚ)/((29311:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29311:ℚ)/((29311:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29311:ℚ)/((29311:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29311:ℚ)/((29311:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2908563358619 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((29311:ℚ)/((29311:ℚ)-1)) : ℚ) ≤ ((1454298738043 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((2908563358619 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29311:ℚ)/((29311:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1454298738043 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3185 : Commons.NumberTheory.Mertens.logRatioSum ((29327 : ℕ) : ℝ) ≤ ((((2908631574939 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29311 < q → q < 29327 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29327).mp (by decide +kernel))) hgap
  have hprev := lrU_3184
  have hcast : (((29327:ℕ):ℝ)/(((29327:ℕ):ℝ)-1)) = (((29327:ℚ)/((29327:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29327:ℚ)/((29327:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29327:ℚ)/((29327:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29327:ℚ)/((29327:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1454298738043 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((29327:ℚ)/((29327:ℚ)-1)) : ℚ) ≤ ((2908631574939 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((1454298738043 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29327:ℚ)/((29327:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2908631574939 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3186 : Commons.NumberTheory.Mertens.logRatioSum ((29333 : ℕ) : ℝ) ≤ ((((2908665666817 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29327 < q → q < 29333 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29333).mp (by decide +kernel))) hgap
  have hprev := lrU_3185
  have hcast : (((29333:ℕ):ℝ)/(((29333:ℕ):ℝ)-1)) = (((29333:ℚ)/((29333:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29333:ℚ)/((29333:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29333:ℚ)/((29333:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29333:ℚ)/((29333:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2908631574939 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((29333:ℚ)/((29333:ℚ)-1)) : ℚ) ≤ ((2908665666817 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2908631574939 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29333:ℚ)/((29333:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2908665666817 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3187 : Commons.NumberTheory.Mertens.logRatioSum ((29339 : ℕ) : ℝ) ≤ ((((2908699751723 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29333 < q → q < 29339 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29339).mp (by decide +kernel))) hgap
  have hprev := lrU_3186
  have hcast : (((29339:ℕ):ℝ)/(((29339:ℕ):ℝ)-1)) = (((29339:ℚ)/((29339:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29339:ℚ)/((29339:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29339:ℚ)/((29339:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29339:ℚ)/((29339:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2908665666817 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((29339:ℚ)/((29339:ℚ)-1)) : ℚ) ≤ ((2908699751723 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2908665666817 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29339:ℚ)/((29339:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2908699751723 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3188 : Commons.NumberTheory.Mertens.logRatioSum ((29347 : ℕ) : ℝ) ≤ ((((2908733827337 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29339 < q → q < 29347 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29347).mp (by decide +kernel))) hgap
  have hprev := lrU_3187
  have hcast : (((29347:ℕ):ℝ)/(((29347:ℕ):ℝ)-1)) = (((29347:ℚ)/((29347:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29347:ℚ)/((29347:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29347:ℚ)/((29347:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29347:ℚ)/((29347:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2908699751723 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((29347:ℚ)/((29347:ℚ)-1)) : ℚ) ≤ ((2908733827337 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2908699751723 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29347:ℚ)/((29347:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2908733827337 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3189 : Commons.NumberTheory.Mertens.logRatioSum ((29363 : ℕ) : ℝ) ≤ ((((2908767884383 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29347 < q → q < 29363 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29363).mp (by decide +kernel))) hgap
  have hprev := lrU_3188
  have hcast : (((29363:ℕ):ℝ)/(((29363:ℕ):ℝ)-1)) = (((29363:ℚ)/((29363:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29363:ℚ)/((29363:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29363:ℚ)/((29363:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29363:ℚ)/((29363:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2908733827337 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((29363:ℚ)/((29363:ℚ)-1)) : ℚ) ≤ ((2908767884383 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2908733827337 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29363:ℚ)/((29363:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2908767884383 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3190 : Commons.NumberTheory.Mertens.logRatioSum ((29383 : ℕ) : ℝ) ≤ ((((2908801918247 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29363 < q → q < 29383 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29383).mp (by decide +kernel))) hgap
  have hprev := lrU_3189
  have hcast : (((29383:ℕ):ℝ)/(((29383:ℕ):ℝ)-1)) = (((29383:ℚ)/((29383:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29383:ℚ)/((29383:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29383:ℚ)/((29383:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29383:ℚ)/((29383:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2908767884383 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((29383:ℚ)/((29383:ℚ)-1)) : ℚ) ≤ ((2908801918247 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2908767884383 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29383:ℚ)/((29383:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2908801918247 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3191 : Commons.NumberTheory.Mertens.logRatioSum ((29387 : ℕ) : ℝ) ≤ ((((2908835947479 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29383 < q → q < 29387 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29387).mp (by decide +kernel))) hgap
  have hprev := lrU_3190
  have hcast : (((29387:ℕ):ℝ)/(((29387:ℕ):ℝ)-1)) = (((29387:ℚ)/((29387:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29387:ℚ)/((29387:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29387:ℚ)/((29387:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29387:ℚ)/((29387:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2908801918247 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((29387:ℚ)/((29387:ℚ)-1)) : ℚ) ≤ ((2908835947479 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2908801918247 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29387:ℚ)/((29387:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2908835947479 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3192 : Commons.NumberTheory.Mertens.logRatioSum ((29389 : ℕ) : ℝ) ≤ ((((581773994879 : ℚ) / 200000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29387 < q → q < 29389 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29389).mp (by decide +kernel))) hgap
  have hprev := lrU_3191
  have hcast : (((29389:ℕ):ℝ)/(((29389:ℕ):ℝ)-1)) = (((29389:ℚ)/((29389:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29389:ℚ)/((29389:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29389:ℚ)/((29389:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29389:ℚ)/((29389:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2908835947479 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((29389:ℚ)/((29389:ℚ)-1)) : ℚ) ≤ ((581773994879 : ℚ) / 200000000000) := by decide +kernel
  have hratR : ((((2908835947479 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29389:ℚ)/((29389:ℚ)-1)) : ℚ) : ℝ) ≤ ((((581773994879 : ℚ) / 200000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3193 : Commons.NumberTheory.Mertens.logRatioSum ((29399 : ℕ) : ℝ) ≤ ((((363612998717 : ℚ) / 125000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29389 < q → q < 29399 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29399).mp (by decide +kernel))) hgap
  have hprev := lrU_3192
  have hcast : (((29399:ℕ):ℝ)/(((29399:ℕ):ℝ)-1)) = (((29399:ℚ)/((29399:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29399:ℚ)/((29399:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29399:ℚ)/((29399:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29399:ℚ)/((29399:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((581773994879 : ℚ) / 200000000000) + Work.RHContract.RegionI.logUpQ (((29399:ℚ)/((29399:ℚ)-1)) : ℚ) ≤ ((363612998717 : ℚ) / 125000000000) := by decide +kernel
  have hratR : ((((581773994879 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29399:ℚ)/((29399:ℚ)-1)) : ℚ) : ℝ) ≤ ((((363612998717 : ℚ) / 125000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3194 : Commons.NumberTheory.Mertens.logRatioSum ((29401 : ℕ) : ℝ) ≤ ((((2908938002763 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29399 < q → q < 29401 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29401).mp (by decide +kernel))) hgap
  have hprev := lrU_3193
  have hcast : (((29401:ℕ):ℝ)/(((29401:ℕ):ℝ)-1)) = (((29401:ℚ)/((29401:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29401:ℚ)/((29401:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29401:ℚ)/((29401:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29401:ℚ)/((29401:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((363612998717 : ℚ) / 125000000000) + Work.RHContract.RegionI.logUpQ (((29401:ℚ)/((29401:ℚ)-1)) : ℚ) ≤ ((2908938002763 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((363612998717 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29401:ℚ)/((29401:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2908938002763 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3195 : Commons.NumberTheory.Mertens.logRatioSum ((29411 : ℕ) : ℝ) ≤ ((((1454486002113 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29401 < q → q < 29411 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29411).mp (by decide +kernel))) hgap
  have hprev := lrU_3194
  have hcast : (((29411:ℕ):ℝ)/(((29411:ℕ):ℝ)-1)) = (((29411:ℚ)/((29411:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29411:ℚ)/((29411:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29411:ℚ)/((29411:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29411:ℚ)/((29411:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2908938002763 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((29411:ℚ)/((29411:ℚ)-1)) : ℚ) ≤ ((1454486002113 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((2908938002763 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29411:ℚ)/((29411:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1454486002113 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3196 : Commons.NumberTheory.Mertens.logRatioSum ((29423 : ℕ) : ℝ) ≤ ((((2909005991821 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29411 < q → q < 29423 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29423).mp (by decide +kernel))) hgap
  have hprev := lrU_3195
  have hcast : (((29423:ℕ):ℝ)/(((29423:ℕ):ℝ)-1)) = (((29423:ℚ)/((29423:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29423:ℚ)/((29423:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29423:ℚ)/((29423:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29423:ℚ)/((29423:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1454486002113 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((29423:ℚ)/((29423:ℚ)-1)) : ℚ) ≤ ((2909005991821 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((1454486002113 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29423:ℚ)/((29423:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2909005991821 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3197 : Commons.NumberTheory.Mertens.logRatioSum ((29429 : ℕ) : ℝ) ≤ ((((2909039972487 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29423 < q → q < 29429 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29429).mp (by decide +kernel))) hgap
  have hprev := lrU_3196
  have hcast : (((29429:ℕ):ℝ)/(((29429:ℕ):ℝ)-1)) = (((29429:ℚ)/((29429:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29429:ℚ)/((29429:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29429:ℚ)/((29429:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29429:ℚ)/((29429:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2909005991821 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((29429:ℚ)/((29429:ℚ)-1)) : ℚ) ≤ ((2909039972487 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2909005991821 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29429:ℚ)/((29429:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2909039972487 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3198 : Commons.NumberTheory.Mertens.logRatioSum ((29437 : ℕ) : ℝ) ≤ ((((1454536971959 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29429 < q → q < 29437 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29437).mp (by decide +kernel))) hgap
  have hprev := lrU_3197
  have hcast : (((29437:ℕ):ℝ)/(((29437:ℕ):ℝ)-1)) = (((29437:ℚ)/((29437:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29437:ℚ)/((29437:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29437:ℚ)/((29437:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29437:ℚ)/((29437:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2909039972487 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((29437:ℚ)/((29437:ℚ)-1)) : ℚ) ≤ ((1454536971959 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((2909039972487 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29437:ℚ)/((29437:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1454536971959 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3199 : Commons.NumberTheory.Mertens.logRatioSum ((29443 : ℕ) : ℝ) ≤ ((((1454553954213 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29437 < q → q < 29443 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29443).mp (by decide +kernel))) hgap
  have hprev := lrU_3198
  have hcast : (((29443:ℕ):ℝ)/(((29443:ℕ):ℝ)-1)) = (((29443:ℚ)/((29443:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29443:ℚ)/((29443:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29443:ℚ)/((29443:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29443:ℚ)/((29443:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1454536971959 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((29443:ℚ)/((29443:ℚ)-1)) : ℚ) ≤ ((1454553954213 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((1454536971959 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29443:ℚ)/((29443:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1454553954213 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3200 : Commons.NumberTheory.Mertens.logRatioSum ((29453 : ℕ) : ℝ) ≤ ((((1454570930701 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29443 < q → q < 29453 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29453).mp (by decide +kernel))) hgap
  have hprev := lrU_3199
  have hcast : (((29453:ℕ):ℝ)/(((29453:ℕ):ℝ)-1)) = (((29453:ℚ)/((29453:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29453:ℚ)/((29453:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29453:ℚ)/((29453:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29453:ℚ)/((29453:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1454553954213 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((29453:ℚ)/((29453:ℚ)-1)) : ℚ) ≤ ((1454570930701 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((1454553954213 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29453:ℚ)/((29453:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1454570930701 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3201 : Commons.NumberTheory.Mertens.logRatioSum ((29473 : ℕ) : ℝ) ≤ ((((2909175791337 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29453 < q → q < 29473 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29473).mp (by decide +kernel))) hgap
  have hprev := lrU_3200
  have hcast : (((29473:ℕ):ℝ)/(((29473:ℕ):ℝ)-1)) = (((29473:ℚ)/((29473:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29473:ℚ)/((29473:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29473:ℚ)/((29473:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29473:ℚ)/((29473:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1454570930701 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((29473:ℚ)/((29473:ℚ)-1)) : ℚ) ≤ ((2909175791337 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((1454570930701 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29473:ℚ)/((29473:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2909175791337 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3202 : Commons.NumberTheory.Mertens.logRatioSum ((29483 : ℕ) : ℝ) ≤ ((((727302427441 : ℚ) / 250000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29473 < q → q < 29483 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29483).mp (by decide +kernel))) hgap
  have hprev := lrU_3201
  have hcast : (((29483:ℕ):ℝ)/(((29483:ℕ):ℝ)-1)) = (((29483:ℚ)/((29483:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29483:ℚ)/((29483:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29483:ℚ)/((29483:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29483:ℚ)/((29483:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2909175791337 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((29483:ℚ)/((29483:ℚ)-1)) : ℚ) ≤ ((727302427441 : ℚ) / 250000000000) := by decide +kernel
  have hratR : ((((2909175791337 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29483:ℚ)/((29483:ℚ)-1)) : ℚ) : ℝ) ≤ ((((727302427441 : ℚ) / 250000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3203 : Commons.NumberTheory.Mertens.logRatioSum ((29501 : ℕ) : ℝ) ≤ ((((581848721499 : ℚ) / 200000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29483 < q → q < 29501 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29501).mp (by decide +kernel))) hgap
  have hprev := lrU_3202
  have hcast : (((29501:ℕ):ℝ)/(((29501:ℕ):ℝ)-1)) = (((29501:ℚ)/((29501:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29501:ℚ)/((29501:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29501:ℚ)/((29501:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29501:ℚ)/((29501:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((727302427441 : ℚ) / 250000000000) + Work.RHContract.RegionI.logUpQ (((29501:ℚ)/((29501:ℚ)-1)) : ℚ) ≤ ((581848721499 : ℚ) / 200000000000) := by decide +kernel
  have hratR : ((((727302427441 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29501:ℚ)/((29501:ℚ)-1)) : ℚ) : ℝ) ≤ ((((581848721499 : ℚ) / 200000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3204 : Commons.NumberTheory.Mertens.logRatioSum ((29527 : ℕ) : ℝ) ≤ ((((2909277475377 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29501 < q → q < 29527 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29527).mp (by decide +kernel))) hgap
  have hprev := lrU_3203
  have hcast : (((29527:ℕ):ℝ)/(((29527:ℕ):ℝ)-1)) = (((29527:ℚ)/((29527:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29527:ℚ)/((29527:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29527:ℚ)/((29527:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29527:ℚ)/((29527:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((581848721499 : ℚ) / 200000000000) + Work.RHContract.RegionI.logUpQ (((29527:ℚ)/((29527:ℚ)-1)) : ℚ) ≤ ((2909277475377 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((581848721499 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29527:ℚ)/((29527:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2909277475377 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3205 : Commons.NumberTheory.Mertens.logRatioSum ((29531 : ℕ) : ℝ) ≤ ((((2909311338671 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29527 < q → q < 29531 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29531).mp (by decide +kernel))) hgap
  have hprev := lrU_3204
  have hcast : (((29531:ℕ):ℝ)/(((29531:ℕ):ℝ)-1)) = (((29531:ℚ)/((29531:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29531:ℚ)/((29531:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29531:ℚ)/((29531:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29531:ℚ)/((29531:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2909277475377 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((29531:ℚ)/((29531:ℚ)-1)) : ℚ) ≤ ((2909311338671 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2909277475377 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29531:ℚ)/((29531:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2909311338671 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3206 : Commons.NumberTheory.Mertens.logRatioSum ((29537 : ℕ) : ℝ) ≤ ((((1454672597543 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29531 < q → q < 29537 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29537).mp (by decide +kernel))) hgap
  have hprev := lrU_3205
  have hcast : (((29537:ℕ):ℝ)/(((29537:ℕ):ℝ)-1)) = (((29537:ℚ)/((29537:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29537:ℚ)/((29537:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29537:ℚ)/((29537:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29537:ℚ)/((29537:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2909311338671 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((29537:ℚ)/((29537:ℚ)-1)) : ℚ) ≤ ((1454672597543 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((2909311338671 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29537:ℚ)/((29537:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1454672597543 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3207 : Commons.NumberTheory.Mertens.logRatioSum ((29567 : ℕ) : ℝ) ≤ ((((2909379017149 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29537 < q → q < 29567 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29567).mp (by decide +kernel))) hgap
  have hprev := lrU_3206
  have hcast : (((29567:ℕ):ℝ)/(((29567:ℕ):ℝ)-1)) = (((29567:ℚ)/((29567:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29567:ℚ)/((29567:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29567:ℚ)/((29567:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29567:ℚ)/((29567:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1454672597543 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((29567:ℚ)/((29567:ℚ)-1)) : ℚ) ≤ ((2909379017149 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((1454672597543 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29567:ℚ)/((29567:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2909379017149 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3208 : Commons.NumberTheory.Mertens.logRatioSum ((29569 : ℕ) : ℝ) ≤ ((((727353209231 : ℚ) / 250000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29567 < q → q < 29569 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29569).mp (by decide +kernel))) hgap
  have hprev := lrU_3207
  have hcast : (((29569:ℕ):ℝ)/(((29569:ℕ):ℝ)-1)) = (((29569:ℚ)/((29569:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29569:ℚ)/((29569:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29569:ℚ)/((29569:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29569:ℚ)/((29569:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2909379017149 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((29569:ℚ)/((29569:ℚ)-1)) : ℚ) ≤ ((727353209231 : ℚ) / 250000000000) := by decide +kernel
  have hratR : ((((2909379017149 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29569:ℚ)/((29569:ℚ)-1)) : ℚ) : ℝ) ≤ ((((727353209231 : ℚ) / 250000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3209 : Commons.NumberTheory.Mertens.logRatioSum ((29573 : ℕ) : ℝ) ≤ ((((727361663031 : ℚ) / 250000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29569 < q → q < 29573 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29573).mp (by decide +kernel))) hgap
  have hprev := lrU_3208
  have hcast : (((29573:ℕ):ℝ)/(((29573:ℕ):ℝ)-1)) = (((29573:ℚ)/((29573:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29573:ℚ)/((29573:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29573:ℚ)/((29573:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29573:ℚ)/((29573:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((727353209231 : ℚ) / 250000000000) + Work.RHContract.RegionI.logUpQ (((29573:ℚ)/((29573:ℚ)-1)) : ℚ) ≤ ((727361663031 : ℚ) / 250000000000) := by decide +kernel
  have hratR : ((((727353209231 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29573:ℚ)/((29573:ℚ)-1)) : ℚ) : ℝ) ≤ ((((727361663031 : ℚ) / 250000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3210 : Commons.NumberTheory.Mertens.logRatioSum ((29581 : ℕ) : ℝ) ≤ ((((2909480458179 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29573 < q → q < 29581 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29581).mp (by decide +kernel))) hgap
  have hprev := lrU_3209
  have hcast : (((29581:ℕ):ℝ)/(((29581:ℕ):ℝ)-1)) = (((29581:ℚ)/((29581:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29581:ℚ)/((29581:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29581:ℚ)/((29581:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29581:ℚ)/((29581:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((727361663031 : ℚ) / 250000000000) + Work.RHContract.RegionI.logUpQ (((29581:ℚ)/((29581:ℚ)-1)) : ℚ) ≤ ((2909480458179 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((727361663031 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29581:ℚ)/((29581:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2909480458179 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3211 : Commons.NumberTheory.Mertens.logRatioSum ((29587 : ℕ) : ℝ) ≤ ((((1454757128689 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29581 < q → q < 29587 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29587).mp (by decide +kernel))) hgap
  have hprev := lrU_3210
  have hcast : (((29587:ℕ):ℝ)/(((29587:ℕ):ℝ)-1)) = (((29587:ℚ)/((29587:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29587:ℚ)/((29587:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29587:ℚ)/((29587:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29587:ℚ)/((29587:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2909480458179 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((29587:ℚ)/((29587:ℚ)-1)) : ℚ) ≤ ((1454757128689 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((2909480458179 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29587:ℚ)/((29587:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1454757128689 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3212 : Commons.NumberTheory.Mertens.logRatioSum ((29599 : ℕ) : ℝ) ≤ ((((1454774021437 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29587 < q → q < 29599 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29599).mp (by decide +kernel))) hgap
  have hprev := lrU_3211
  have hcast : (((29599:ℕ):ℝ)/(((29599:ℕ):ℝ)-1)) = (((29599:ℚ)/((29599:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29599:ℚ)/((29599:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29599:ℚ)/((29599:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29599:ℚ)/((29599:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1454757128689 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((29599:ℚ)/((29599:ℚ)-1)) : ℚ) ≤ ((1454774021437 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((1454757128689 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29599:ℚ)/((29599:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1454774021437 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3213 : Commons.NumberTheory.Mertens.logRatioSum ((29611 : ℕ) : ℝ) ≤ ((((1454790907339 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29599 < q → q < 29611 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29611).mp (by decide +kernel))) hgap
  have hprev := lrU_3212
  have hcast : (((29611:ℕ):ℝ)/(((29611:ℕ):ℝ)-1)) = (((29611:ℚ)/((29611:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29611:ℚ)/((29611:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29611:ℚ)/((29611:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29611:ℚ)/((29611:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1454774021437 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((29611:ℚ)/((29611:ℚ)-1)) : ℚ) ≤ ((1454790907339 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((1454774021437 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29611:ℚ)/((29611:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1454790907339 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3214 : Commons.NumberTheory.Mertens.logRatioSum ((29629 : ℕ) : ℝ) ≤ ((((581923113193 : ℚ) / 200000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29611 < q → q < 29629 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29629).mp (by decide +kernel))) hgap
  have hprev := lrU_3213
  have hcast : (((29629:ℕ):ℝ)/(((29629:ℕ):ℝ)-1)) = (((29629:ℚ)/((29629:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29629:ℚ)/((29629:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29629:ℚ)/((29629:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29629:ℚ)/((29629:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1454790907339 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((29629:ℚ)/((29629:ℚ)-1)) : ℚ) ≤ ((581923113193 : ℚ) / 200000000000) := by decide +kernel
  have hratR : ((((1454790907339 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29629:ℚ)/((29629:ℚ)-1)) : ℚ) : ℝ) ≤ ((((581923113193 : ℚ) / 200000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3215 : Commons.NumberTheory.Mertens.logRatioSum ((29633 : ℕ) : ℝ) ≤ ((((363706164087 : ℚ) / 125000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29629 < q → q < 29633 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29633).mp (by decide +kernel))) hgap
  have hprev := lrU_3214
  have hcast : (((29633:ℕ):ℝ)/(((29633:ℕ):ℝ)-1)) = (((29633:ℚ)/((29633:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29633:ℚ)/((29633:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29633:ℚ)/((29633:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29633:ℚ)/((29633:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((581923113193 : ℚ) / 200000000000) + Work.RHContract.RegionI.logUpQ (((29633:ℚ)/((29633:ℚ)-1)) : ℚ) ≤ ((363706164087 : ℚ) / 125000000000) := by decide +kernel
  have hratR : ((((581923113193 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29633:ℚ)/((29633:ℚ)-1)) : ℚ) : ℝ) ≤ ((((363706164087 : ℚ) / 125000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3216 : Commons.NumberTheory.Mertens.logRatioSum ((29641 : ℕ) : ℝ) ≤ ((((2909683050319 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29633 < q → q < 29641 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29641).mp (by decide +kernel))) hgap
  have hprev := lrU_3215
  have hcast : (((29641:ℕ):ℝ)/(((29641:ℕ):ℝ)-1)) = (((29641:ℚ)/((29641:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29641:ℚ)/((29641:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29641:ℚ)/((29641:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29641:ℚ)/((29641:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((363706164087 : ℚ) / 125000000000) + Work.RHContract.RegionI.logUpQ (((29641:ℚ)/((29641:ℚ)-1)) : ℚ) ≤ ((2909683050319 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((363706164087 : ℚ) / 125000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29641:ℚ)/((29641:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2909683050319 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3217 : Commons.NumberTheory.Mertens.logRatioSum ((29663 : ℕ) : ℝ) ≤ ((((72742919073 : ℚ) / 25000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29641 < q → q < 29663 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29663).mp (by decide +kernel))) hgap
  have hprev := lrU_3216
  have hcast : (((29663:ℕ):ℝ)/(((29663:ℕ):ℝ)-1)) = (((29663:ℚ)/((29663:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29663:ℚ)/((29663:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29663:ℚ)/((29663:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29663:ℚ)/((29663:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2909683050319 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((29663:ℚ)/((29663:ℚ)-1)) : ℚ) ≤ ((72742919073 : ℚ) / 25000000000) := by decide +kernel
  have hratR : ((((2909683050319 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29663:ℚ)/((29663:ℚ)-1)) : ℚ) : ℝ) ≤ ((((72742919073 : ℚ) / 25000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3218 : Commons.NumberTheory.Mertens.logRatioSum ((29669 : ℕ) : ℝ) ≤ ((((2909750468703 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29663 < q → q < 29669 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29669).mp (by decide +kernel))) hgap
  have hprev := lrU_3217
  have hcast : (((29669:ℕ):ℝ)/(((29669:ℕ):ℝ)-1)) = (((29669:ℚ)/((29669:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29669:ℚ)/((29669:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29669:ℚ)/((29669:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29669:ℚ)/((29669:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((72742919073 : ℚ) / 25000000000) + Work.RHContract.RegionI.logUpQ (((29669:ℚ)/((29669:ℚ)-1)) : ℚ) ≤ ((2909750468703 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((72742919073 : ℚ) / 25000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29669:ℚ)/((29669:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2909750468703 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3219 : Commons.NumberTheory.Mertens.logRatioSum ((29671 : ℕ) : ℝ) ≤ ((((1454892086107 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29669 < q → q < 29671 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29671).mp (by decide +kernel))) hgap
  have hprev := lrU_3218
  have hcast : (((29671:ℕ):ℝ)/(((29671:ℕ):ℝ)-1)) = (((29671:ℚ)/((29671:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29671:ℚ)/((29671:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29671:ℚ)/((29671:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29671:ℚ)/((29671:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2909750468703 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((29671:ℚ)/((29671:ℚ)-1)) : ℚ) ≤ ((1454892086107 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((2909750468703 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29671:ℚ)/((29671:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1454892086107 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3220 : Commons.NumberTheory.Mertens.logRatioSum ((29683 : ℕ) : ℝ) ≤ ((((2909817862099 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29671 < q → q < 29683 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29683).mp (by decide +kernel))) hgap
  have hprev := lrU_3219
  have hcast : (((29683:ℕ):ℝ)/(((29683:ℕ):ℝ)-1)) = (((29683:ℚ)/((29683:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29683:ℚ)/((29683:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29683:ℚ)/((29683:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29683:ℚ)/((29683:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1454892086107 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((29683:ℚ)/((29683:ℚ)-1)) : ℚ) ≤ ((2909817862099 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((1454892086107 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29683:ℚ)/((29683:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2909817862099 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3221 : Commons.NumberTheory.Mertens.logRatioSum ((29717 : ℕ) : ℝ) ≤ ((((1454925756719 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29683 < q → q < 29717 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29717).mp (by decide +kernel))) hgap
  have hprev := lrU_3220
  have hcast : (((29717:ℕ):ℝ)/(((29717:ℕ):ℝ)-1)) = (((29717:ℚ)/((29717:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29717:ℚ)/((29717:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29717:ℚ)/((29717:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29717:ℚ)/((29717:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2909817862099 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((29717:ℚ)/((29717:ℚ)-1)) : ℚ) ≤ ((1454925756719 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((2909817862099 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29717:ℚ)/((29717:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1454925756719 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3222 : Commons.NumberTheory.Mertens.logRatioSum ((29723 : ℕ) : ℝ) ≤ ((((90933911187 : ℚ) / 31250000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29717 < q → q < 29723 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29723).mp (by decide +kernel))) hgap
  have hprev := lrU_3221
  have hcast : (((29723:ℕ):ℝ)/(((29723:ℕ):ℝ)-1)) = (((29723:ℚ)/((29723:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29723:ℚ)/((29723:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29723:ℚ)/((29723:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29723:ℚ)/((29723:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1454925756719 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((29723:ℚ)/((29723:ℚ)-1)) : ℚ) ≤ ((90933911187 : ℚ) / 31250000000) := by decide +kernel
  have hratR : ((((1454925756719 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29723:ℚ)/((29723:ℚ)-1)) : ℚ) : ℝ) ≤ ((((90933911187 : ℚ) / 31250000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3223 : Commons.NumberTheory.Mertens.logRatioSum ((29741 : ℕ) : ℝ) ≤ ((((2909918782167 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29723 < q → q < 29741 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29741).mp (by decide +kernel))) hgap
  have hprev := lrU_3222
  have hcast : (((29741:ℕ):ℝ)/(((29741:ℕ):ℝ)-1)) = (((29741:ℚ)/((29741:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29741:ℚ)/((29741:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29741:ℚ)/((29741:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29741:ℚ)/((29741:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((90933911187 : ℚ) / 31250000000) + Work.RHContract.RegionI.logUpQ (((29741:ℚ)/((29741:ℚ)-1)) : ℚ) ≤ ((2909918782167 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((90933911187 : ℚ) / 31250000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29741:ℚ)/((29741:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2909918782167 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3224 : Commons.NumberTheory.Mertens.logRatioSum ((29753 : ℕ) : ℝ) ≤ ((((727488098197 : ℚ) / 250000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29741 < q → q < 29753 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29753).mp (by decide +kernel))) hgap
  have hprev := lrU_3223
  have hcast : (((29753:ℕ):ℝ)/(((29753:ℕ):ℝ)-1)) = (((29753:ℚ)/((29753:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29753:ℚ)/((29753:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29753:ℚ)/((29753:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29753:ℚ)/((29753:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2909918782167 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((29753:ℚ)/((29753:ℚ)-1)) : ℚ) ≤ ((727488098197 : ℚ) / 250000000000) := by decide +kernel
  have hratR : ((((2909918782167 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29753:ℚ)/((29753:ℚ)-1)) : ℚ) : ℝ) ≤ ((((727488098197 : ℚ) / 250000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3225 : Commons.NumberTheory.Mertens.logRatioSum ((29759 : ℕ) : ℝ) ≤ ((((2909985996633 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29753 < q → q < 29759 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29759).mp (by decide +kernel))) hgap
  have hprev := lrU_3224
  have hcast : (((29759:ℕ):ℝ)/(((29759:ℕ):ℝ)-1)) = (((29759:ℚ)/((29759:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29759:ℚ)/((29759:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29759:ℚ)/((29759:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29759:ℚ)/((29759:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((727488098197 : ℚ) / 250000000000) + Work.RHContract.RegionI.logUpQ (((29759:ℚ)/((29759:ℚ)-1)) : ℚ) ≤ ((2909985996633 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((727488098197 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29759:ℚ)/((29759:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2909985996633 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3226 : Commons.NumberTheory.Mertens.logRatioSum ((29761 : ℕ) : ℝ) ≤ ((((2910019598219 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29759 < q → q < 29761 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29761).mp (by decide +kernel))) hgap
  have hprev := lrU_3225
  have hcast : (((29761:ℕ):ℝ)/(((29761:ℕ):ℝ)-1)) = (((29761:ℚ)/((29761:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29761:ℚ)/((29761:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29761:ℚ)/((29761:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29761:ℚ)/((29761:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2909985996633 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((29761:ℚ)/((29761:ℚ)-1)) : ℚ) ≤ ((2910019598219 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2909985996633 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29761:ℚ)/((29761:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2910019598219 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3227 : Commons.NumberTheory.Mertens.logRatioSum ((29789 : ℕ) : ℝ) ≤ ((((2910053168221 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29761 < q → q < 29789 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29789).mp (by decide +kernel))) hgap
  have hprev := lrU_3226
  have hcast : (((29789:ℕ):ℝ)/(((29789:ℕ):ℝ)-1)) = (((29789:ℚ)/((29789:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29789:ℚ)/((29789:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29789:ℚ)/((29789:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29789:ℚ)/((29789:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2910019598219 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((29789:ℚ)/((29789:ℚ)-1)) : ℚ) ≤ ((2910053168221 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((2910019598219 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29789:ℚ)/((29789:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2910053168221 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3228 : Commons.NumberTheory.Mertens.logRatioSum ((29803 : ℕ) : ℝ) ≤ ((((1455043361227 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29789 < q → q < 29803 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29803).mp (by decide +kernel))) hgap
  have hprev := lrU_3227
  have hcast : (((29803:ℕ):ℝ)/(((29803:ℕ):ℝ)-1)) = (((29803:ℚ)/((29803:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29803:ℚ)/((29803:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29803:ℚ)/((29803:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29803:ℚ)/((29803:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2910053168221 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((29803:ℚ)/((29803:ℚ)-1)) : ℚ) ≤ ((1455043361227 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((2910053168221 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29803:ℚ)/((29803:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1455043361227 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3229 : Commons.NumberTheory.Mertens.logRatioSum ((29819 : ℕ) : ℝ) ≤ ((((1455060129341 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29803 < q → q < 29819 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29819).mp (by decide +kernel))) hgap
  have hprev := lrU_3228
  have hcast : (((29819:ℕ):ℝ)/(((29819:ℕ):ℝ)-1)) = (((29819:ℚ)/((29819:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29819:ℚ)/((29819:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29819:ℚ)/((29819:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29819:ℚ)/((29819:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1455043361227 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((29819:ℚ)/((29819:ℚ)-1)) : ℚ) ≤ ((1455060129341 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((1455043361227 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29819:ℚ)/((29819:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1455060129341 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3230 : Commons.NumberTheory.Mertens.logRatioSum ((29833 : ℕ) : ℝ) ≤ ((((727538444793 : ℚ) / 250000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29819 < q → q < 29833 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29833).mp (by decide +kernel))) hgap
  have hprev := lrU_3229
  have hcast : (((29833:ℕ):ℝ)/(((29833:ℕ):ℝ)-1)) = (((29833:ℚ)/((29833:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29833:ℚ)/((29833:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29833:ℚ)/((29833:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29833:ℚ)/((29833:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1455060129341 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((29833:ℚ)/((29833:ℚ)-1)) : ℚ) ≤ ((727538444793 : ℚ) / 250000000000) := by decide +kernel
  have hratR : ((((1455060129341 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29833:ℚ)/((29833:ℚ)-1)) : ℚ) : ℝ) ≤ ((((727538444793 : ℚ) / 250000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3231 : Commons.NumberTheory.Mertens.logRatioSum ((29837 : ℕ) : ℝ) ≤ ((((45471676487 : ℚ) / 15625000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29833 < q → q < 29837 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29837).mp (by decide +kernel))) hgap
  have hprev := lrU_3230
  have hcast : (((29837:ℕ):ℝ)/(((29837:ℕ):ℝ)-1)) = (((29837:ℚ)/((29837:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29837:ℚ)/((29837:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29837:ℚ)/((29837:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29837:ℚ)/((29837:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((727538444793 : ℚ) / 250000000000) + Work.RHContract.RegionI.logUpQ (((29837:ℚ)/((29837:ℚ)-1)) : ℚ) ≤ ((45471676487 : ℚ) / 15625000000) := by decide +kernel
  have hratR : ((((727538444793 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29837:ℚ)/((29837:ℚ)-1)) : ℚ) : ℝ) ≤ ((((45471676487 : ℚ) / 15625000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3232 : Commons.NumberTheory.Mertens.logRatioSum ((29851 : ℕ) : ℝ) ≤ ((((582044159089 : ℚ) / 200000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29837 < q → q < 29851 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29851).mp (by decide +kernel))) hgap
  have hprev := lrU_3231
  have hcast : (((29851:ℕ):ℝ)/(((29851:ℕ):ℝ)-1)) = (((29851:ℚ)/((29851:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29851:ℚ)/((29851:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29851:ℚ)/((29851:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29851:ℚ)/((29851:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((45471676487 : ℚ) / 15625000000) + Work.RHContract.RegionI.logUpQ (((29851:ℚ)/((29851:ℚ)-1)) : ℚ) ≤ ((582044159089 : ℚ) / 200000000000) := by decide +kernel
  have hratR : ((((45471676487 : ℚ) / 15625000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29851:ℚ)/((29851:ℚ)-1)) : ℚ) : ℝ) ≤ ((((582044159089 : ℚ) / 200000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3233 : Commons.NumberTheory.Mertens.logRatioSum ((29863 : ℕ) : ℝ) ≤ ((((145512714113 : ℚ) / 50000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29851 < q → q < 29863 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29863).mp (by decide +kernel))) hgap
  have hprev := lrU_3232
  have hcast : (((29863:ℕ):ℝ)/(((29863:ℕ):ℝ)-1)) = (((29863:ℚ)/((29863:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29863:ℚ)/((29863:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29863:ℚ)/((29863:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29863:ℚ)/((29863:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((582044159089 : ℚ) / 200000000000) + Work.RHContract.RegionI.logUpQ (((29863:ℚ)/((29863:ℚ)-1)) : ℚ) ≤ ((145512714113 : ℚ) / 50000000000) := by decide +kernel
  have hratR : ((((582044159089 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29863:ℚ)/((29863:ℚ)-1)) : ℚ) : ℝ) ≤ ((((145512714113 : ℚ) / 50000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3234 : Commons.NumberTheory.Mertens.logRatioSum ((29867 : ℕ) : ℝ) ≤ ((((291028776459 : ℚ) / 100000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29863 < q → q < 29867 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29867).mp (by decide +kernel))) hgap
  have hprev := lrU_3233
  have hcast : (((29867:ℕ):ℝ)/(((29867:ℕ):ℝ)-1)) = (((29867:ℚ)/((29867:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29867:ℚ)/((29867:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29867:ℚ)/((29867:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29867:ℚ)/((29867:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((145512714113 : ℚ) / 50000000000) + Work.RHContract.RegionI.logUpQ (((29867:ℚ)/((29867:ℚ)-1)) : ℚ) ≤ ((291028776459 : ℚ) / 100000000000) := by decide +kernel
  have hratR : ((((145512714113 : ℚ) / 50000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29867:ℚ)/((29867:ℚ)-1)) : ℚ) : ℝ) ≤ ((((291028776459 : ℚ) / 100000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3235 : Commons.NumberTheory.Mertens.logRatioSum ((29873 : ℕ) : ℝ) ≤ ((((582064248039 : ℚ) / 200000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29867 < q → q < 29873 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29873).mp (by decide +kernel))) hgap
  have hprev := lrU_3234
  have hcast : (((29873:ℕ):ℝ)/(((29873:ℕ):ℝ)-1)) = (((29873:ℚ)/((29873:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29873:ℚ)/((29873:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29873:ℚ)/((29873:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29873:ℚ)/((29873:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((291028776459 : ℚ) / 100000000000) + Work.RHContract.RegionI.logUpQ (((29873:ℚ)/((29873:ℚ)-1)) : ℚ) ≤ ((582064248039 : ℚ) / 200000000000) := by decide +kernel
  have hratR : ((((291028776459 : ℚ) / 100000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29873:ℚ)/((29873:ℚ)-1)) : ℚ) : ℝ) ≤ ((((582064248039 : ℚ) / 200000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3236 : Commons.NumberTheory.Mertens.logRatioSum ((29879 : ℕ) : ℝ) ≤ ((((1455177354539 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29873 < q → q < 29879 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29879).mp (by decide +kernel))) hgap
  have hprev := lrU_3235
  have hcast : (((29879:ℕ):ℝ)/(((29879:ℕ):ℝ)-1)) = (((29879:ℚ)/((29879:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29879:ℚ)/((29879:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29879:ℚ)/((29879:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29879:ℚ)/((29879:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((582064248039 : ℚ) / 200000000000) + Work.RHContract.RegionI.logUpQ (((29879:ℚ)/((29879:ℚ)-1)) : ℚ) ≤ ((1455177354539 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((582064248039 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29879:ℚ)/((29879:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1455177354539 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3237 : Commons.NumberTheory.Mertens.logRatioSum ((29881 : ℕ) : ℝ) ≤ ((((2910388175721 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29879 < q → q < 29881 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29881).mp (by decide +kernel))) hgap
  have hprev := lrU_3236
  have hcast : (((29881:ℕ):ℝ)/(((29881:ℕ):ℝ)-1)) = (((29881:ℚ)/((29881:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29881:ℚ)/((29881:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29881:ℚ)/((29881:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29881:ℚ)/((29881:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1455177354539 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((29881:ℚ)/((29881:ℚ)-1)) : ℚ) ≤ ((2910388175721 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((1455177354539 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29881:ℚ)/((29881:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2910388175721 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3238 : Commons.NumberTheory.Mertens.logRatioSum ((29917 : ℕ) : ℝ) ≤ ((((727605400523 : ℚ) / 250000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29881 < q → q < 29917 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29917).mp (by decide +kernel))) hgap
  have hprev := lrU_3237
  have hcast : (((29917:ℕ):ℝ)/(((29917:ℕ):ℝ)-1)) = (((29917:ℚ)/((29917:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29917:ℚ)/((29917:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29917:ℚ)/((29917:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29917:ℚ)/((29917:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2910388175721 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((29917:ℚ)/((29917:ℚ)-1)) : ℚ) ≤ ((727605400523 : ℚ) / 250000000000) := by decide +kernel
  have hratR : ((((2910388175721 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29917:ℚ)/((29917:ℚ)-1)) : ℚ) : ℝ) ≤ ((((727605400523 : ℚ) / 250000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3239 : Commons.NumberTheory.Mertens.logRatioSum ((29921 : ℕ) : ℝ) ≤ ((((1455227511997 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29917 < q → q < 29921 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29921).mp (by decide +kernel))) hgap
  have hprev := lrU_3238
  have hcast : (((29921:ℕ):ℝ)/(((29921:ℕ):ℝ)-1)) = (((29921:ℚ)/((29921:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29921:ℚ)/((29921:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29921:ℚ)/((29921:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29921:ℚ)/((29921:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((727605400523 : ℚ) / 250000000000) + Work.RHContract.RegionI.logUpQ (((29921:ℚ)/((29921:ℚ)-1)) : ℚ) ≤ ((1455227511997 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((727605400523 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29921:ℚ)/((29921:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1455227511997 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3240 : Commons.NumberTheory.Mertens.logRatioSum ((29927 : ℕ) : ℝ) ≤ ((((582097687839 : ℚ) / 200000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29921 < q → q < 29927 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29927).mp (by decide +kernel))) hgap
  have hprev := lrU_3239
  have hcast : (((29927:ℕ):ℝ)/(((29927:ℕ):ℝ)-1)) = (((29927:ℚ)/((29927:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29927:ℚ)/((29927:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29927:ℚ)/((29927:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29927:ℚ)/((29927:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1455227511997 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((29927:ℚ)/((29927:ℚ)-1)) : ℚ) ≤ ((582097687839 : ℚ) / 200000000000) := by decide +kernel
  have hratR : ((((1455227511997 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29927:ℚ)/((29927:ℚ)-1)) : ℚ) : ℝ) ≤ ((((582097687839 : ℚ) / 200000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3241 : Commons.NumberTheory.Mertens.logRatioSum ((29947 : ℕ) : ℝ) ≤ ((((2910521832079 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29927 < q → q < 29947 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29947).mp (by decide +kernel))) hgap
  have hprev := lrU_3240
  have hcast : (((29947:ℕ):ℝ)/(((29947:ℕ):ℝ)-1)) = (((29947:ℚ)/((29947:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29947:ℚ)/((29947:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29947:ℚ)/((29947:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29947:ℚ)/((29947:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((582097687839 : ℚ) / 200000000000) + Work.RHContract.RegionI.logUpQ (((29947:ℚ)/((29947:ℚ)-1)) : ℚ) ≤ ((2910521832079 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((582097687839 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29947:ℚ)/((29947:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2910521832079 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3242 : Commons.NumberTheory.Mertens.logRatioSum ((29959 : ℕ) : ℝ) ≤ ((((727638802897 : ℚ) / 250000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29947 < q → q < 29959 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29959).mp (by decide +kernel))) hgap
  have hprev := lrU_3241
  have hcast : (((29959:ℕ):ℝ)/(((29959:ℕ):ℝ)-1)) = (((29959:ℚ)/((29959:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29959:ℚ)/((29959:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29959:ℚ)/((29959:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29959:ℚ)/((29959:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2910521832079 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((29959:ℚ)/((29959:ℚ)-1)) : ℚ) ≤ ((727638802897 : ℚ) / 250000000000) := by decide +kernel
  have hratR : ((((2910521832079 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29959:ℚ)/((29959:ℚ)-1)) : ℚ) : ℝ) ≤ ((((727638802897 : ℚ) / 250000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3243 : Commons.NumberTheory.Mertens.logRatioSum ((29983 : ℕ) : ℝ) ≤ ((((1455294282189 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29959 < q → q < 29983 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29983).mp (by decide +kernel))) hgap
  have hprev := lrU_3242
  have hcast : (((29983:ℕ):ℝ)/(((29983:ℕ):ℝ)-1)) = (((29983:ℚ)/((29983:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29983:ℚ)/((29983:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29983:ℚ)/((29983:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29983:ℚ)/((29983:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((727638802897 : ℚ) / 250000000000) + Work.RHContract.RegionI.logUpQ (((29983:ℚ)/((29983:ℚ)-1)) : ℚ) ≤ ((1455294282189 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((727638802897 : ℚ) / 250000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29983:ℚ)/((29983:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1455294282189 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3244 : Commons.NumberTheory.Mertens.logRatioSum ((29989 : ℕ) : ℝ) ≤ ((((582124382099 : ℚ) / 200000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29983 < q → q < 29989 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29989).mp (by decide +kernel))) hgap
  have hprev := lrU_3243
  have hcast : (((29989:ℕ):ℝ)/(((29989:ℕ):ℝ)-1)) = (((29989:ℚ)/((29989:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((29989:ℚ)/((29989:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((29989:ℚ)/((29989:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((29989:ℚ)/((29989:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1455294282189 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((29989:ℚ)/((29989:ℚ)-1)) : ℚ) ≤ ((582124382099 : ℚ) / 200000000000) := by decide +kernel
  have hratR : ((((1455294282189 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((29989:ℚ)/((29989:ℚ)-1)) : ℚ) : ℝ) ≤ ((((582124382099 : ℚ) / 200000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3245 : Commons.NumberTheory.Mertens.logRatioSum ((30011 : ℕ) : ℝ) ≤ ((((1455327616083 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 29989 < q → q < 30011 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 30011).mp (by decide +kernel))) hgap
  have hprev := lrU_3244
  have hcast : (((30011:ℕ):ℝ)/(((30011:ℕ):ℝ)-1)) = (((30011:ℚ)/((30011:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((30011:ℚ)/((30011:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((30011:ℚ)/((30011:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((30011:ℚ)/((30011:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((582124382099 : ℚ) / 200000000000) + Work.RHContract.RegionI.logUpQ (((30011:ℚ)/((30011:ℚ)-1)) : ℚ) ≤ ((1455327616083 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((582124382099 : ℚ) / 200000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((30011:ℚ)/((30011:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1455327616083 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3246 : Commons.NumberTheory.Mertens.logRatioSum ((30013 : ℕ) : ℝ) ≤ ((((2910688551617 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 30011 < q → q < 30013 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 30013).mp (by decide +kernel))) hgap
  have hprev := lrU_3245
  have hcast : (((30013:ℕ):ℝ)/(((30013:ℕ):ℝ)-1)) = (((30013:ℚ)/((30013:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((30013:ℚ)/((30013:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((30013:ℚ)/((30013:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((30013:ℚ)/((30013:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1455327616083 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((30013:ℚ)/((30013:ℚ)-1)) : ℚ) ≤ ((2910688551617 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((1455327616083 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((30013:ℚ)/((30013:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2910688551617 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3247 : Commons.NumberTheory.Mertens.logRatioSum ((30029 : ℕ) : ℝ) ≤ ((((1455360926657 : ℚ) / 500000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 30013 < q → q < 30029 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 30029).mp (by decide +kernel))) hgap
  have hprev := lrU_3246
  have hcast : (((30029:ℕ):ℝ)/(((30029:ℕ):ℝ)-1)) = (((30029:ℚ)/((30029:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((30029:ℚ)/((30029:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((30029:ℚ)/((30029:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((30029:ℚ)/((30029:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((2910688551617 : ℚ) / 1000000000000) + Work.RHContract.RegionI.logUpQ (((30029:ℚ)/((30029:ℚ)-1)) : ℚ) ≤ ((1455360926657 : ℚ) / 500000000000) := by decide +kernel
  have hratR : ((((2910688551617 : ℚ) / 1000000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((30029:ℚ)/((30029:ℚ)-1)) : ℚ) : ℝ) ≤ ((((1455360926657 : ℚ) / 500000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma lrU_3248 : Commons.NumberTheory.Mertens.logRatioSum ((30047 : ℕ) : ℝ) ≤ ((((2910755135061 : ℚ) / 1000000000000) : ℚ) : ℝ) := by
  have hgap : ∀ q : ℕ, 30029 < q → q < 30047 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 30047).mp (by decide +kernel))) hgap
  have hprev := lrU_3247
  have hcast : (((30047:ℕ):ℝ)/(((30047:ℕ):ℝ)-1)) = (((30047:ℚ)/((30047:ℚ)-1)) : ℚ) := by push_cast; ring
  have hlog : Real.log (((30047:ℚ)/((30047:ℚ)-1)) : ℚ) ≤ (Work.RHContract.RegionI.logUpQ (((30047:ℚ)/((30047:ℚ)-1)) : ℚ) : ℝ) :=
    Work.RHContract.RegionI.le_logUpQ (x := ((30047:ℚ)/((30047:ℚ)-1))) (by norm_num) (by norm_num)
  have hrat : ((1455360926657 : ℚ) / 500000000000) + Work.RHContract.RegionI.logUpQ (((30047:ℚ)/((30047:ℚ)-1)) : ℚ) ≤ ((2910755135061 : ℚ) / 1000000000000) := by decide +kernel
  have hratR : ((((1455360926657 : ℚ) / 500000000000) : ℚ) : ℝ) + (Work.RHContract.RegionI.logUpQ (((30047:ℚ)/((30047:ℚ)-1)) : ℚ) : ℝ) ≤ ((((2910755135061 : ℚ) / 1000000000000) : ℚ) : ℝ) := by exact_mod_cast hrat
  rw [hstep, hcast]
  exact le_trans (add_le_add hprev hlog) hratR
lemma s2L_0 : ((((1 : ℚ) / 4) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  rw [show Nat.primesLE 2 = {2} by decide +kernel, Finset.sum_singleton]
  have h : (((1 : ℚ) / 4) : ℚ) = (2:ℚ)^(-2:ℤ) := by decide +kernel
  rw [h]
  push_cast
  norm_num
lemma s2L_1 : ((((361111111111 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2 < q → q < 3 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3).mp (by decide +kernel))) hgap
  have hprev := s2L_0
  have hrat : ((361111111111 : ℚ) / 1000000000000) ≤ ((1 : ℚ) / 4) + (3:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((361111111111 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1 : ℚ) / 4) : ℚ) : ℝ) + ((3:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3:ℚ)^(-2:ℤ) : ℝ) = ((3:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2 : ((((401111111111 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3 < q → q < 5 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5).mp (by decide +kernel))) hgap
  have hprev := s2L_1
  have hrat : ((401111111111 : ℚ) / 1000000000000) ≤ ((361111111111 : ℚ) / 1000000000000) + (5:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((401111111111 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((361111111111 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((5:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5:ℚ)^(-2:ℤ) : ℝ) = ((5:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3 : ((((52689909297 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5 < q → q < 7 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7).mp (by decide +kernel))) hgap
  have hprev := s2L_2
  have hrat : ((52689909297 : ℚ) / 125000000000) ≤ ((401111111111 : ℚ) / 1000000000000) + (7:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((52689909297 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((401111111111 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((7:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7:ℚ)^(-2:ℤ) : ℝ) = ((7:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_4 : ((((85956747437 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7 < q → q < 11 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11).mp (by decide +kernel))) hgap
  have hprev := s2L_3
  have hrat : ((85956747437 : ℚ) / 200000000000) ≤ ((52689909297 : ℚ) / 125000000000) + (11:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((85956747437 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((52689909297 : ℚ) / 125000000000) : ℚ) : ℝ) + ((11:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11:ℚ)^(-2:ℤ) : ℝ) = ((11:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_5 : ((((108925224237 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11 < q → q < 13 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13).mp (by decide +kernel))) hgap
  have hprev := s2L_4
  have hrat : ((108925224237 : ℚ) / 250000000000) ≤ ((85956747437 : ℚ) / 200000000000) + (13:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((108925224237 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((85956747437 : ℚ) / 200000000000) : ℚ) : ℝ) + ((13:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13:ℚ)^(-2:ℤ) : ℝ) = ((13:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_6 : ((((5489513807 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13 < q → q < 17 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17).mp (by decide +kernel))) hgap
  have hprev := s2L_5
  have hrat : ((5489513807 : ℚ) / 12500000000) ≤ ((108925224237 : ℚ) / 250000000000) + (17:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((5489513807 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ ((((108925224237 : ℚ) / 250000000000) : ℚ) : ℝ) + ((17:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17:ℚ)^(-2:ℤ) : ℝ) = ((17:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_7 : ((((220965593831 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17 < q → q < 19 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19).mp (by decide +kernel))) hgap
  have hprev := s2L_6
  have hrat : ((220965593831 : ℚ) / 500000000000) ≤ ((5489513807 : ℚ) / 12500000000) + (19:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((220965593831 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((5489513807 : ℚ) / 12500000000) : ℚ) : ℝ) + ((19:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19:ℚ)^(-2:ℤ) : ℝ) = ((19:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_8 : ((((44382154683 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19 < q → q < 23 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23).mp (by decide +kernel))) hgap
  have hprev := s2L_7
  have hrat : ((44382154683 : ℚ) / 100000000000) ≤ ((220965593831 : ℚ) / 500000000000) + (23:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((44382154683 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((220965593831 : ℚ) / 500000000000) : ℚ) : ℝ) + ((23:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23:ℚ)^(-2:ℤ) : ℝ) = ((23:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_9 : ((((27813162967 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23 < q → q < 29 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29).mp (by decide +kernel))) hgap
  have hprev := s2L_8
  have hrat : ((27813162967 : ℚ) / 62500000000) ≤ ((44382154683 : ℚ) / 100000000000) + (29:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((27813162967 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((44382154683 : ℚ) / 100000000000) : ℚ) : ℝ) + ((29:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29:ℚ)^(-2:ℤ) : ℝ) = ((29:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_10 : ((((223025595099 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 31, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29 < q → q < 31 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 31).mp (by decide +kernel))) hgap
  have hprev := s2L_9
  have hrat : ((223025595099 : ℚ) / 500000000000) ≤ ((27813162967 : ℚ) / 62500000000) + (31:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((223025595099 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((27813162967 : ℚ) / 62500000000) : ℚ) : ℝ) + ((31:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((31:ℚ)^(-2:ℤ) : ℝ) = ((31:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_11 : ((((446781650387 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 37, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 31 < q → q < 37 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 37).mp (by decide +kernel))) hgap
  have hprev := s2L_10
  have hrat : ((446781650387 : ℚ) / 1000000000000) ≤ ((223025595099 : ℚ) / 500000000000) + (37:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((446781650387 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((223025595099 : ℚ) / 500000000000) : ℚ) : ℝ) + ((37:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((37:ℚ)^(-2:ℤ) : ℝ) = ((37:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_12 : ((((27961033399 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 41, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 37 < q → q < 41 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 41).mp (by decide +kernel))) hgap
  have hprev := s2L_11
  have hrat : ((27961033399 : ℚ) / 62500000000) ≤ ((446781650387 : ℚ) / 1000000000000) + (41:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((27961033399 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((446781650387 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((41:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((41:ℚ)^(-2:ℤ) : ℝ) = ((41:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_13 : ((((223958683633 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 43, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 41 < q → q < 43 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 43).mp (by decide +kernel))) hgap
  have hprev := s2L_12
  have hrat : ((223958683633 : ℚ) / 500000000000) ≤ ((27961033399 : ℚ) / 62500000000) + (43:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((223958683633 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((27961033399 : ℚ) / 62500000000) : ℚ) : ℝ) + ((43:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((43:ℚ)^(-2:ℤ) : ℝ) = ((43:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_14 : ((((56046257599 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 47, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 43 < q → q < 47 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 47).mp (by decide +kernel))) hgap
  have hprev := s2L_13
  have hrat : ((56046257599 : ℚ) / 125000000000) ≤ ((223958683633 : ℚ) / 500000000000) + (47:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56046257599 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((223958683633 : ℚ) / 500000000000) : ℚ) : ℝ) + ((47:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((47:ℚ)^(-2:ℤ) : ℝ) = ((47:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_15 : ((((56090757421 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 53, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 47 < q → q < 53 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 53).mp (by decide +kernel))) hgap
  have hprev := s2L_14
  have hrat : ((56090757421 : ℚ) / 125000000000) ≤ ((56046257599 : ℚ) / 125000000000) + (53:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56090757421 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((56046257599 : ℚ) / 125000000000) : ℚ) : ℝ) + ((53:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((53:ℚ)^(-2:ℤ) : ℝ) = ((53:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_16 : ((((449013333139 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 59, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 53 < q → q < 59 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 59).mp (by decide +kernel))) hgap
  have hprev := s2L_15
  have hrat : ((449013333139 : ℚ) / 1000000000000) ≤ ((56090757421 : ℚ) / 125000000000) + (59:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((449013333139 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56090757421 : ℚ) / 125000000000) : ℚ) : ℝ) + ((59:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((59:ℚ)^(-2:ℤ) : ℝ) = ((59:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_17 : ((((4492820781 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 61, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 59 < q → q < 61 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 61).mp (by decide +kernel))) hgap
  have hprev := s2L_16
  have hrat : ((4492820781 : ℚ) / 10000000000) ≤ ((449013333139 : ℚ) / 1000000000000) + (61:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((4492820781 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ ((((449013333139 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((61:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((61:ℚ)^(-2:ℤ) : ℝ) = ((61:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_18 : ((((449504844863 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 67, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 61 < q → q < 67 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 67).mp (by decide +kernel))) hgap
  have hprev := s2L_17
  have hrat : ((449504844863 : ℚ) / 1000000000000) ≤ ((4492820781 : ℚ) / 10000000000) + (67:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((449504844863 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4492820781 : ℚ) / 10000000000) : ℚ) : ℝ) + ((67:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((67:ℚ)^(-2:ℤ) : ℝ) = ((67:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_19 : ((((449703218201 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 71, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 67 < q → q < 71 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 71).mp (by decide +kernel))) hgap
  have hprev := s2L_18
  have hrat : ((449703218201 : ℚ) / 1000000000000) ≤ ((449504844863 : ℚ) / 1000000000000) + (71:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((449703218201 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((449504844863 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((71:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((71:ℚ)^(-2:ℤ) : ℝ) = ((71:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_20 : ((((112472717667 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 73, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 71 < q → q < 73 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 73).mp (by decide +kernel))) hgap
  have hprev := s2L_19
  have hrat : ((112472717667 : ℚ) / 250000000000) ≤ ((449703218201 : ℚ) / 1000000000000) + (73:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((112472717667 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((449703218201 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((73:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((73:ℚ)^(-2:ℤ) : ℝ) = ((73:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_21 : ((((2250255507 : ℚ) / 5000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 79, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 73 < q → q < 79 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 79).mp (by decide +kernel))) hgap
  have hprev := s2L_20
  have hrat : ((2250255507 : ℚ) / 5000000000) ≤ ((112472717667 : ℚ) / 250000000000) + (79:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((2250255507 : ℚ) / 5000000000) : ℚ) : ℝ) ≤ ((((112472717667 : ℚ) / 250000000000) : ℚ) : ℝ) + ((79:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((79:ℚ)^(-2:ℤ) : ℝ) = ((79:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_22 : ((((450196260349 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 83, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 79 < q → q < 83 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 83).mp (by decide +kernel))) hgap
  have hprev := s2L_21
  have hrat : ((450196260349 : ℚ) / 1000000000000) ≤ ((2250255507 : ℚ) / 5000000000) + (83:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((450196260349 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2250255507 : ℚ) / 5000000000) : ℚ) : ℝ) + ((83:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((83:ℚ)^(-2:ℤ) : ℝ) = ((83:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_23 : ((((90064501407 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 89, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 83 < q → q < 89 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 89).mp (by decide +kernel))) hgap
  have hprev := s2L_22
  have hrat : ((90064501407 : ℚ) / 200000000000) ≤ ((450196260349 : ℚ) / 1000000000000) + (89:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90064501407 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((450196260349 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((89:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((89:ℚ)^(-2:ℤ) : ℝ) = ((89:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_24 : ((((90085757651 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 97, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 89 < q → q < 97 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 97).mp (by decide +kernel))) hgap
  have hprev := s2L_23
  have hrat : ((90085757651 : ℚ) / 200000000000) ≤ ((90064501407 : ℚ) / 200000000000) + (97:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90085757651 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((90064501407 : ℚ) / 200000000000) : ℚ) : ℝ) + ((97:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((97:ℚ)^(-2:ℤ) : ℝ) = ((97:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_25 : ((((450526817859 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 101, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 97 < q → q < 101 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 101).mp (by decide +kernel))) hgap
  have hprev := s2L_24
  have hrat : ((450526817859 : ℚ) / 1000000000000) ≤ ((90085757651 : ℚ) / 200000000000) + (101:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((450526817859 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90085757651 : ℚ) / 200000000000) : ℚ) : ℝ) + ((101:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((101:ℚ)^(-2:ℤ) : ℝ) = ((101:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_26 : ((((450621077449 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 103, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 101 < q → q < 103 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 103).mp (by decide +kernel))) hgap
  have hprev := s2L_25
  have hrat : ((450621077449 : ℚ) / 1000000000000) ≤ ((450526817859 : ℚ) / 1000000000000) + (103:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((450621077449 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((450526817859 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((103:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((103:ℚ)^(-2:ℤ) : ℝ) = ((103:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_27 : ((((450708421321 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 107, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 103 < q → q < 107 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 107).mp (by decide +kernel))) hgap
  have hprev := s2L_26
  have hrat : ((450708421321 : ℚ) / 1000000000000) ≤ ((450621077449 : ℚ) / 1000000000000) + (107:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((450708421321 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((450621077449 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((107:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((107:ℚ)^(-2:ℤ) : ℝ) = ((107:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_28 : ((((11269814733 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 109, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 107 < q → q < 109 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 109).mp (by decide +kernel))) hgap
  have hprev := s2L_27
  have hrat : ((11269814733 : ℚ) / 25000000000) ≤ ((450708421321 : ℚ) / 1000000000000) + (109:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((11269814733 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((450708421321 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((109:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((109:ℚ)^(-2:ℤ) : ℝ) = ((109:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_29 : ((((112717725997 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 113, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 109 < q → q < 113 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 113).mp (by decide +kernel))) hgap
  have hprev := s2L_28
  have hrat : ((112717725997 : ℚ) / 250000000000) ≤ ((11269814733 : ℚ) / 25000000000) + (113:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((112717725997 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((11269814733 : ℚ) / 25000000000) : ℚ) : ℝ) + ((113:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((113:ℚ)^(-2:ℤ) : ℝ) = ((113:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_30 : ((((28183306507 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 127, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 113 < q → q < 127 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 127).mp (by decide +kernel))) hgap
  have hprev := s2L_29
  have hrat : ((28183306507 : ℚ) / 62500000000) ≤ ((112717725997 : ℚ) / 250000000000) + (127:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28183306507 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((112717725997 : ℚ) / 250000000000) : ℚ) : ℝ) + ((127:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((127:ℚ)^(-2:ℤ) : ℝ) = ((127:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_31 : ((((225495587887 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 131, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 127 < q → q < 131 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 131).mp (by decide +kernel))) hgap
  have hprev := s2L_30
  have hrat : ((225495587887 : ℚ) / 500000000000) ≤ ((28183306507 : ℚ) / 62500000000) + (131:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((225495587887 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((28183306507 : ℚ) / 62500000000) : ℚ) : ℝ) + ((131:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((131:ℚ)^(-2:ℤ) : ℝ) = ((131:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_32 : ((((451044455117 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 137, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 131 < q → q < 137 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 137).mp (by decide +kernel))) hgap
  have hprev := s2L_31
  have hrat : ((451044455117 : ℚ) / 1000000000000) ≤ ((225495587887 : ℚ) / 500000000000) + (137:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((451044455117 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((225495587887 : ℚ) / 500000000000) : ℚ) : ℝ) + ((137:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((137:ℚ)^(-2:ℤ) : ℝ) = ((137:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_33 : ((((28193513267 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 139, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 137 < q → q < 139 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 139).mp (by decide +kernel))) hgap
  have hprev := s2L_32
  have hrat : ((28193513267 : ℚ) / 62500000000) ≤ ((451044455117 : ℚ) / 1000000000000) + (139:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28193513267 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((451044455117 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((139:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((139:ℚ)^(-2:ℤ) : ℝ) = ((139:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_34 : ((((56392656911 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 149, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 139 < q → q < 149 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 149).mp (by decide +kernel))) hgap
  have hprev := s2L_33
  have hrat : ((56392656911 : ℚ) / 125000000000) ≤ ((28193513267 : ℚ) / 62500000000) + (149:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56392656911 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((28193513267 : ℚ) / 62500000000) : ℚ) : ℝ) + ((149:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((149:ℚ)^(-2:ℤ) : ℝ) = ((149:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_35 : ((((451185113013 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 151, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 149 < q → q < 151 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 151).mp (by decide +kernel))) hgap
  have hprev := s2L_34
  have hrat : ((451185113013 : ℚ) / 1000000000000) ≤ ((56392656911 : ℚ) / 125000000000) + (151:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((451185113013 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56392656911 : ℚ) / 125000000000) : ℚ) : ℝ) + ((151:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((151:ℚ)^(-2:ℤ) : ℝ) = ((151:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_36 : ((((45122568261 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 157, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 151 < q → q < 157 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 157).mp (by decide +kernel))) hgap
  have hprev := s2L_35
  have hrat : ((45122568261 : ℚ) / 100000000000) ≤ ((451185113013 : ℚ) / 1000000000000) + (157:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45122568261 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((451185113013 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((157:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((157:ℚ)^(-2:ℤ) : ℝ) = ((157:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_37 : ((((225631660229 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 163, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 157 < q → q < 163 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 163).mp (by decide +kernel))) hgap
  have hprev := s2L_36
  have hrat : ((225631660229 : ℚ) / 500000000000) ≤ ((45122568261 : ℚ) / 100000000000) + (163:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((225631660229 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((45122568261 : ℚ) / 100000000000) : ℚ) : ℝ) + ((163:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((163:ℚ)^(-2:ℤ) : ℝ) = ((163:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_38 : ((((56412397111 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 167, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 163 < q → q < 167 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 167).mp (by decide +kernel))) hgap
  have hprev := s2L_37
  have hrat : ((56412397111 : ℚ) / 125000000000) ≤ ((225631660229 : ℚ) / 500000000000) + (167:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56412397111 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((225631660229 : ℚ) / 500000000000) : ℚ) : ℝ) + ((167:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((167:ℚ)^(-2:ℤ) : ℝ) = ((167:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_39 : ((((451332589297 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 173, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 167 < q → q < 173 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 173).mp (by decide +kernel))) hgap
  have hprev := s2L_38
  have hrat : ((451332589297 : ℚ) / 1000000000000) ≤ ((56412397111 : ℚ) / 125000000000) + (173:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((451332589297 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56412397111 : ℚ) / 125000000000) : ℚ) : ℝ) + ((173:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((173:ℚ)^(-2:ℤ) : ℝ) = ((173:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_40 : ((((451363799309 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 179, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 173 < q → q < 179 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 179).mp (by decide +kernel))) hgap
  have hprev := s2L_39
  have hrat : ((451363799309 : ℚ) / 1000000000000) ≤ ((451332589297 : ℚ) / 1000000000000) + (179:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((451363799309 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((451332589297 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((179:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((179:ℚ)^(-2:ℤ) : ℝ) = ((179:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_41 : ((((451394323407 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 181, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 179 < q → q < 181 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 181).mp (by decide +kernel))) hgap
  have hprev := s2L_40
  have hrat : ((451394323407 : ℚ) / 1000000000000) ≤ ((451363799309 : ℚ) / 1000000000000) + (181:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((451394323407 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((451363799309 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((181:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((181:ℚ)^(-2:ℤ) : ℝ) = ((181:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_42 : ((((56427716867 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 191, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 181 < q → q < 191 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 191).mp (by decide +kernel))) hgap
  have hprev := s2L_41
  have hrat : ((56427716867 : ℚ) / 125000000000) ≤ ((451394323407 : ℚ) / 1000000000000) + (191:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56427716867 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((451394323407 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((191:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((191:ℚ)^(-2:ℤ) : ℝ) = ((191:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_43 : ((((225724290647 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 193, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 191 < q → q < 193 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 193).mp (by decide +kernel))) hgap
  have hprev := s2L_42
  have hrat : ((225724290647 : ℚ) / 500000000000) ≤ ((56427716867 : ℚ) / 125000000000) + (193:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((225724290647 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((56427716867 : ℚ) / 125000000000) : ℚ) : ℝ) + ((193:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((193:ℚ)^(-2:ℤ) : ℝ) = ((193:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_44 : ((((14108573391 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 197, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 193 < q → q < 197 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 197).mp (by decide +kernel))) hgap
  have hprev := s2L_43
  have hrat : ((14108573391 : ℚ) / 31250000000) ≤ ((225724290647 : ℚ) / 500000000000) + (197:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((14108573391 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((225724290647 : ℚ) / 500000000000) : ℚ) : ℝ) + ((197:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((197:ℚ)^(-2:ℤ) : ℝ) = ((197:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_45 : ((((451499600399 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 199, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 197 < q → q < 199 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 199).mp (by decide +kernel))) hgap
  have hprev := s2L_44
  have hrat : ((451499600399 : ℚ) / 1000000000000) ≤ ((14108573391 : ℚ) / 31250000000) + (199:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((451499600399 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((14108573391 : ℚ) / 31250000000) : ℚ) : ℝ) + ((199:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((199:ℚ)^(-2:ℤ) : ℝ) = ((199:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_46 : ((((451522061709 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 211, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 199 < q → q < 211 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 211).mp (by decide +kernel))) hgap
  have hprev := s2L_45
  have hrat : ((451522061709 : ℚ) / 1000000000000) ≤ ((451499600399 : ℚ) / 1000000000000) + (211:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((451522061709 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((451499600399 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((211:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((211:ℚ)^(-2:ℤ) : ℝ) = ((211:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_47 : ((((451542170699 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 223, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 211 < q → q < 223 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 223).mp (by decide +kernel))) hgap
  have hprev := s2L_46
  have hrat : ((451542170699 : ℚ) / 1000000000000) ≤ ((451522061709 : ℚ) / 1000000000000) + (223:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((451542170699 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((451522061709 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((223:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((223:ℚ)^(-2:ℤ) : ℝ) = ((223:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_48 : ((((225780788623 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 227, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 223 < q → q < 227 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 227).mp (by decide +kernel))) hgap
  have hprev := s2L_47
  have hrat : ((225780788623 : ℚ) / 500000000000) ≤ ((451542170699 : ℚ) / 1000000000000) + (227:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((225780788623 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((451542170699 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((227:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((227:ℚ)^(-2:ℤ) : ℝ) = ((227:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_49 : ((((90316129259 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 229, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 227 < q → q < 229 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 229).mp (by decide +kernel))) hgap
  have hprev := s2L_48
  have hrat : ((90316129259 : ℚ) / 200000000000) ≤ ((225780788623 : ℚ) / 500000000000) + (229:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90316129259 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((225780788623 : ℚ) / 500000000000) : ℚ) : ℝ) + ((229:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((229:ℚ)^(-2:ℤ) : ℝ) = ((229:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_50 : ((((56449883279 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 233, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 229 < q → q < 233 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 233).mp (by decide +kernel))) hgap
  have hprev := s2L_49
  have hrat : ((56449883279 : ℚ) / 125000000000) ≤ ((90316129259 : ℚ) / 200000000000) + (233:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56449883279 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((90316129259 : ℚ) / 200000000000) : ℚ) : ℝ) + ((233:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((233:ℚ)^(-2:ℤ) : ℝ) = ((233:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_51 : ((((882063619 : ℚ) / 1953125000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 239, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 233 < q → q < 239 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 239).mp (by decide +kernel))) hgap
  have hprev := s2L_50
  have hrat : ((882063619 : ℚ) / 1953125000) ≤ ((56449883279 : ℚ) / 125000000000) + (239:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((882063619 : ℚ) / 1953125000) : ℚ) : ℝ) ≤ ((((56449883279 : ℚ) / 125000000000) : ℚ) : ℝ) + ((239:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((239:ℚ)^(-2:ℤ) : ℝ) = ((239:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_52 : ((((225816895131 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 241, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 239 < q → q < 241 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 241).mp (by decide +kernel))) hgap
  have hprev := s2L_51
  have hrat : ((225816895131 : ℚ) / 500000000000) ≤ ((882063619 : ℚ) / 1953125000) + (241:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((225816895131 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((882063619 : ℚ) / 1953125000) : ℚ) : ℝ) + ((241:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((241:ℚ)^(-2:ℤ) : ℝ) = ((241:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_53 : ((((18065986521 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 251, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 241 < q → q < 251 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 251).mp (by decide +kernel))) hgap
  have hprev := s2L_52
  have hrat : ((18065986521 : ℚ) / 40000000000) ≤ ((225816895131 : ℚ) / 500000000000) + (251:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18065986521 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((225816895131 : ℚ) / 500000000000) : ℚ) : ℝ) + ((251:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((251:ℚ)^(-2:ℤ) : ℝ) = ((251:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_54 : ((((451664803299 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 257, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 251 < q → q < 257 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 257).mp (by decide +kernel))) hgap
  have hprev := s2L_53
  have hrat : ((451664803299 : ℚ) / 1000000000000) ≤ ((18065986521 : ℚ) / 40000000000) + (257:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((451664803299 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((18065986521 : ℚ) / 40000000000) : ℚ) : ℝ) + ((257:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((257:ℚ)^(-2:ℤ) : ℝ) = ((257:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_55 : ((((225839630321 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 263, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 257 < q → q < 263 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 263).mp (by decide +kernel))) hgap
  have hprev := s2L_54
  have hrat : ((225839630321 : ℚ) / 500000000000) ≤ ((451664803299 : ℚ) / 1000000000000) + (263:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((225839630321 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((451664803299 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((263:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((263:ℚ)^(-2:ℤ) : ℝ) = ((263:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_56 : ((((5646163503 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 269, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 263 < q → q < 269 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 269).mp (by decide +kernel))) hgap
  have hprev := s2L_55
  have hrat : ((5646163503 : ℚ) / 12500000000) ≤ ((225839630321 : ℚ) / 500000000000) + (269:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((5646163503 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ ((((225839630321 : ℚ) / 500000000000) : ℚ) : ℝ) + ((269:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((269:ℚ)^(-2:ℤ) : ℝ) = ((269:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_57 : ((((112926674153 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 271, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 269 < q → q < 271 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 271).mp (by decide +kernel))) hgap
  have hprev := s2L_56
  have hrat : ((112926674153 : ℚ) / 250000000000) ≤ ((5646163503 : ℚ) / 12500000000) + (271:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((112926674153 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((5646163503 : ℚ) / 12500000000) : ℚ) : ℝ) + ((271:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((271:ℚ)^(-2:ℤ) : ℝ) = ((271:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_58 : ((((451719729493 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 277, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 271 < q → q < 277 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 277).mp (by decide +kernel))) hgap
  have hprev := s2L_57
  have hrat : ((451719729493 : ℚ) / 1000000000000) ≤ ((112926674153 : ℚ) / 250000000000) + (277:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((451719729493 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((112926674153 : ℚ) / 250000000000) : ℚ) : ℝ) + ((277:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((277:ℚ)^(-2:ℤ) : ℝ) = ((277:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_59 : ((((112933098493 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 281, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 277 < q → q < 281 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 281).mp (by decide +kernel))) hgap
  have hprev := s2L_58
  have hrat : ((112933098493 : ℚ) / 250000000000) ≤ ((451719729493 : ℚ) / 1000000000000) + (281:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((112933098493 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((451719729493 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((281:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((281:ℚ)^(-2:ℤ) : ℝ) = ((281:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_60 : ((((451744880081 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 283, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 281 < q → q < 283 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 283).mp (by decide +kernel))) hgap
  have hprev := s2L_59
  have hrat : ((451744880081 : ℚ) / 1000000000000) ≤ ((112933098493 : ℚ) / 250000000000) + (283:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((451744880081 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((112933098493 : ℚ) / 250000000000) : ℚ) : ℝ) + ((283:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((283:ℚ)^(-2:ℤ) : ℝ) = ((283:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_61 : ((((11293913211 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 293, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 283 < q → q < 293 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 293).mp (by decide +kernel))) hgap
  have hprev := s2L_60
  have hrat : ((11293913211 : ℚ) / 25000000000) ≤ ((451744880081 : ℚ) / 1000000000000) + (293:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((11293913211 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((451744880081 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((293:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((293:ℚ)^(-2:ℤ) : ℝ) = ((293:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_62 : ((((56470892329 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 307, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 293 < q → q < 307 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 307).mp (by decide +kernel))) hgap
  have hprev := s2L_61
  have hrat : ((56470892329 : ℚ) / 125000000000) ≤ ((11293913211 : ℚ) / 25000000000) + (307:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56470892329 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((11293913211 : ℚ) / 25000000000) : ℚ) : ℝ) + ((307:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((307:ℚ)^(-2:ℤ) : ℝ) = ((307:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_63 : ((((28236092353 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 311, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 307 < q → q < 311 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 311).mp (by decide +kernel))) hgap
  have hprev := s2L_62
  have hrat : ((28236092353 : ℚ) / 62500000000) ≤ ((56470892329 : ℚ) / 125000000000) + (311:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28236092353 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((56470892329 : ℚ) / 125000000000) : ℚ) : ℝ) + ((311:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((311:ℚ)^(-2:ℤ) : ℝ) = ((311:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_64 : ((((225893842479 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 313, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 311 < q → q < 313 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 313).mp (by decide +kernel))) hgap
  have hprev := s2L_63
  have hrat : ((225893842479 : ℚ) / 500000000000) ≤ ((28236092353 : ℚ) / 62500000000) + (313:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((225893842479 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((28236092353 : ℚ) / 62500000000) : ℚ) : ℝ) + ((313:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((313:ℚ)^(-2:ℤ) : ℝ) = ((313:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_65 : ((((90359527259 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 317, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 313 < q → q < 317 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 317).mp (by decide +kernel))) hgap
  have hprev := s2L_64
  have hrat : ((90359527259 : ℚ) / 200000000000) ≤ ((225893842479 : ℚ) / 500000000000) + (317:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90359527259 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((225893842479 : ℚ) / 500000000000) : ℚ) : ℝ) + ((317:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((317:ℚ)^(-2:ℤ) : ℝ) = ((317:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_66 : ((((45180676363 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 331, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 317 < q → q < 331 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 331).mp (by decide +kernel))) hgap
  have hprev := s2L_65
  have hrat : ((45180676363 : ℚ) / 100000000000) ≤ ((90359527259 : ℚ) / 200000000000) + (331:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45180676363 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((90359527259 : ℚ) / 200000000000) : ℚ) : ℝ) + ((331:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((331:ℚ)^(-2:ℤ) : ℝ) = ((331:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_67 : ((((451815568849 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 337, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 331 < q → q < 337 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 337).mp (by decide +kernel))) hgap
  have hprev := s2L_66
  have hrat : ((451815568849 : ℚ) / 1000000000000) ≤ ((45180676363 : ℚ) / 100000000000) + (337:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((451815568849 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((45180676363 : ℚ) / 100000000000) : ℚ) : ℝ) + ((337:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((337:ℚ)^(-2:ℤ) : ℝ) = ((337:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_68 : ((((112955968469 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 347, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 337 < q → q < 347 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 347).mp (by decide +kernel))) hgap
  have hprev := s2L_67
  have hrat : ((112955968469 : ℚ) / 250000000000) ≤ ((451815568849 : ℚ) / 1000000000000) + (347:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((112955968469 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((451815568849 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((347:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((347:ℚ)^(-2:ℤ) : ℝ) = ((347:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_69 : ((((451832083989 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 349, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 347 < q → q < 349 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 349).mp (by decide +kernel))) hgap
  have hprev := s2L_68
  have hrat : ((451832083989 : ℚ) / 1000000000000) ≤ ((112955968469 : ℚ) / 250000000000) + (349:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((451832083989 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((112955968469 : ℚ) / 250000000000) : ℚ) : ℝ) + ((349:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((349:ℚ)^(-2:ℤ) : ℝ) = ((349:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_70 : ((((451840109091 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 353, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 349 < q → q < 353 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 353).mp (by decide +kernel))) hgap
  have hprev := s2L_69
  have hrat : ((451840109091 : ℚ) / 1000000000000) ≤ ((451832083989 : ℚ) / 1000000000000) + (353:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((451840109091 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((451832083989 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((353:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((353:ℚ)^(-2:ℤ) : ℝ) = ((353:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_71 : ((((225923934093 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 359, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 353 < q → q < 359 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 359).mp (by decide +kernel))) hgap
  have hprev := s2L_70
  have hrat : ((225923934093 : ℚ) / 500000000000) ≤ ((451840109091 : ℚ) / 1000000000000) + (359:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((225923934093 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((451840109091 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((359:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((359:ℚ)^(-2:ℤ) : ℝ) = ((359:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_72 : ((((451855292697 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 367, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 359 < q → q < 367 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 367).mp (by decide +kernel))) hgap
  have hprev := s2L_71
  have hrat : ((451855292697 : ℚ) / 1000000000000) ≤ ((225923934093 : ℚ) / 500000000000) + (367:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((451855292697 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((225923934093 : ℚ) / 500000000000) : ℚ) : ℝ) + ((367:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((367:ℚ)^(-2:ℤ) : ℝ) = ((367:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_73 : ((((451862480271 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 373, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 367 < q → q < 373 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 373).mp (by decide +kernel))) hgap
  have hprev := s2L_72
  have hrat : ((451862480271 : ℚ) / 1000000000000) ≤ ((451855292697 : ℚ) / 1000000000000) + (373:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((451862480271 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((451855292697 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((373:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((373:ℚ)^(-2:ℤ) : ℝ) = ((373:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_74 : ((((451869442071 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 379, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 373 < q → q < 379 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 379).mp (by decide +kernel))) hgap
  have hprev := s2L_73
  have hrat : ((451869442071 : ℚ) / 1000000000000) ≤ ((451862480271 : ℚ) / 1000000000000) + (379:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((451869442071 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((451862480271 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((379:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((379:ℚ)^(-2:ℤ) : ℝ) = ((379:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_75 : ((((225938129607 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 383, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 379 < q → q < 383 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 383).mp (by decide +kernel))) hgap
  have hprev := s2L_74
  have hrat : ((225938129607 : ℚ) / 500000000000) ≤ ((451869442071 : ℚ) / 1000000000000) + (383:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((225938129607 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((451869442071 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((383:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((383:ℚ)^(-2:ℤ) : ℝ) = ((383:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_76 : ((((225941433841 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 389, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 383 < q → q < 389 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 389).mp (by decide +kernel))) hgap
  have hprev := s2L_75
  have hrat : ((225941433841 : ℚ) / 500000000000) ≤ ((225938129607 : ℚ) / 500000000000) + (389:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((225941433841 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((225938129607 : ℚ) / 500000000000) : ℚ) : ℝ) + ((389:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((389:ℚ)^(-2:ℤ) : ℝ) = ((389:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_77 : ((((451889212497 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 397, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 389 < q → q < 397 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 397).mp (by decide +kernel))) hgap
  have hprev := s2L_76
  have hrat : ((451889212497 : ℚ) / 1000000000000) ≤ ((225941433841 : ℚ) / 500000000000) + (397:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((451889212497 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((225941433841 : ℚ) / 500000000000) : ℚ) : ℝ) + ((397:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((397:ℚ)^(-2:ℤ) : ℝ) = ((397:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_78 : ((((451895431363 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 401, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 397 < q → q < 401 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 401).mp (by decide +kernel))) hgap
  have hprev := s2L_77
  have hrat : ((451895431363 : ℚ) / 1000000000000) ≤ ((451889212497 : ℚ) / 1000000000000) + (401:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((451895431363 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((451889212497 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((401:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((401:ℚ)^(-2:ℤ) : ℝ) = ((401:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_79 : ((((28243838083 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 409, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 401 < q → q < 409 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 409).mp (by decide +kernel))) hgap
  have hprev := s2L_78
  have hrat : ((28243838083 : ℚ) / 62500000000) ≤ ((451895431363 : ℚ) / 1000000000000) + (409:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28243838083 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((451895431363 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((409:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((409:ℚ)^(-2:ℤ) : ℝ) = ((409:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_80 : ((((451907105353 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 419, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 409 < q → q < 419 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 419).mp (by decide +kernel))) hgap
  have hprev := s2L_79
  have hrat : ((451907105353 : ℚ) / 1000000000000) ≤ ((28243838083 : ℚ) / 62500000000) + (419:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((451907105353 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((28243838083 : ℚ) / 62500000000) : ℚ) : ℝ) + ((419:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((419:ℚ)^(-2:ℤ) : ℝ) = ((419:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_81 : ((((112978186847 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 421, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 419 < q → q < 421 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 421).mp (by decide +kernel))) hgap
  have hprev := s2L_80
  have hrat : ((112978186847 : ℚ) / 250000000000) ≤ ((451907105353 : ℚ) / 1000000000000) + (421:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((112978186847 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((451907105353 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((421:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((421:ℚ)^(-2:ℤ) : ℝ) = ((421:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_82 : ((((451918130649 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 431, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 421 < q → q < 431 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 431).mp (by decide +kernel))) hgap
  have hprev := s2L_81
  have hrat : ((451918130649 : ℚ) / 1000000000000) ≤ ((112978186847 : ℚ) / 250000000000) + (431:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((451918130649 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((112978186847 : ℚ) / 250000000000) : ℚ) : ℝ) + ((431:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((431:ℚ)^(-2:ℤ) : ℝ) = ((431:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_83 : ((((90384692859 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 433, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 431 < q → q < 433 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 433).mp (by decide +kernel))) hgap
  have hprev := s2L_82
  have hrat : ((90384692859 : ℚ) / 200000000000) ≤ ((451918130649 : ℚ) / 1000000000000) + (433:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90384692859 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((451918130649 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((433:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((433:ℚ)^(-2:ℤ) : ℝ) = ((433:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_84 : ((((451928653143 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 439, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 433 < q → q < 439 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 439).mp (by decide +kernel))) hgap
  have hprev := s2L_83
  have hrat : ((451928653143 : ℚ) / 1000000000000) ≤ ((90384692859 : ℚ) / 200000000000) + (439:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((451928653143 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90384692859 : ℚ) / 200000000000) : ℚ) : ℝ) + ((439:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((439:ℚ)^(-2:ℤ) : ℝ) = ((439:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_85 : ((((45193374871 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 443, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 439 < q → q < 443 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 443).mp (by decide +kernel))) hgap
  have hprev := s2L_84
  have hrat : ((45193374871 : ℚ) / 100000000000) ≤ ((451928653143 : ℚ) / 1000000000000) + (443:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45193374871 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((451928653143 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((443:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((443:ℚ)^(-2:ℤ) : ℝ) = ((443:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_86 : ((((225969354501 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 449, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 443 < q → q < 449 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 449).mp (by decide +kernel))) hgap
  have hprev := s2L_85
  have hrat : ((225969354501 : ℚ) / 500000000000) ≤ ((45193374871 : ℚ) / 100000000000) + (449:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((225969354501 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((45193374871 : ℚ) / 100000000000) : ℚ) : ℝ) + ((449:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((449:ℚ)^(-2:ℤ) : ℝ) = ((449:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_87 : ((((9038869943 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 457, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 449 < q → q < 457 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 457).mp (by decide +kernel))) hgap
  have hprev := s2L_86
  have hrat : ((9038869943 : ℚ) / 20000000000) ≤ ((225969354501 : ℚ) / 500000000000) + (457:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((9038869943 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ ((((225969354501 : ℚ) / 500000000000) : ℚ) : ℝ) + ((457:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((457:ℚ)^(-2:ℤ) : ℝ) = ((457:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_88 : ((((451948202567 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 461, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 457 < q → q < 461 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 461).mp (by decide +kernel))) hgap
  have hprev := s2L_87
  have hrat : ((451948202567 : ℚ) / 1000000000000) ≤ ((9038869943 : ℚ) / 20000000000) + (461:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((451948202567 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((9038869943 : ℚ) / 20000000000) : ℚ) : ℝ) + ((461:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((461:ℚ)^(-2:ℤ) : ℝ) = ((461:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_89 : ((((22597643371 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 463, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 461 < q → q < 463 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 463).mp (by decide +kernel))) hgap
  have hprev := s2L_88
  have hrat : ((22597643371 : ℚ) / 50000000000) ≤ ((451948202567 : ℚ) / 1000000000000) + (463:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22597643371 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((451948202567 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((463:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((463:ℚ)^(-2:ℤ) : ℝ) = ((463:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_90 : ((((451957452703 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 467, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 463 < q → q < 467 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 467).mp (by decide +kernel))) hgap
  have hprev := s2L_89
  have hrat : ((451957452703 : ℚ) / 1000000000000) ≤ ((22597643371 : ℚ) / 50000000000) + (467:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((451957452703 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((22597643371 : ℚ) / 50000000000) : ℚ) : ℝ) + ((467:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((467:ℚ)^(-2:ℤ) : ℝ) = ((467:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_91 : ((((451961811121 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 479, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 467 < q → q < 479 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 479).mp (by decide +kernel))) hgap
  have hprev := s2L_90
  have hrat : ((451961811121 : ℚ) / 1000000000000) ≤ ((451957452703 : ℚ) / 1000000000000) + (479:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((451961811121 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((451957452703 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((479:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((479:ℚ)^(-2:ℤ) : ℝ) = ((479:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_92 : ((((451966027523 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 487, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 479 < q → q < 487 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 487).mp (by decide +kernel))) hgap
  have hprev := s2L_91
  have hrat : ((451966027523 : ℚ) / 1000000000000) ≤ ((451961811121 : ℚ) / 1000000000000) + (487:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((451966027523 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((451961811121 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((487:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((487:ℚ)^(-2:ℤ) : ℝ) = ((487:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_93 : ((((225985087753 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 491, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 487 < q → q < 491 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 491).mp (by decide +kernel))) hgap
  have hprev := s2L_92
  have hrat : ((225985087753 : ℚ) / 500000000000) ≤ ((451966027523 : ℚ) / 1000000000000) + (491:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((225985087753 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((451966027523 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((491:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((491:ℚ)^(-2:ℤ) : ℝ) = ((491:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_94 : ((((225987095777 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 499, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 491 < q → q < 499 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 499).mp (by decide +kernel))) hgap
  have hprev := s2L_93
  have hrat : ((225987095777 : ℚ) / 500000000000) ≤ ((225985087753 : ℚ) / 500000000000) + (499:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((225987095777 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((225985087753 : ℚ) / 500000000000) : ℚ) : ℝ) + ((499:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((499:ℚ)^(-2:ℤ) : ℝ) = ((499:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_95 : ((((225989071991 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 503, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 499 < q → q < 503 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 503).mp (by decide +kernel))) hgap
  have hprev := s2L_94
  have hrat : ((225989071991 : ℚ) / 500000000000) ≤ ((225987095777 : ℚ) / 500000000000) + (503:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((225989071991 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((225987095777 : ℚ) / 500000000000) : ℚ) : ℝ) + ((503:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((503:ℚ)^(-2:ℤ) : ℝ) = ((503:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_96 : ((((225991001889 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 509, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 503 < q → q < 509 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 509).mp (by decide +kernel))) hgap
  have hprev := s2L_95
  have hrat : ((225991001889 : ℚ) / 500000000000) ≤ ((225989071991 : ℚ) / 500000000000) + (509:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((225991001889 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((225989071991 : ℚ) / 500000000000) : ℚ) : ℝ) + ((509:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((509:ℚ)^(-2:ℤ) : ℝ) = ((509:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_97 : ((((451985687819 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 521, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 509 < q → q < 521 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 521).mp (by decide +kernel))) hgap
  have hprev := s2L_96
  have hrat : ((451985687819 : ℚ) / 1000000000000) ≤ ((225991001889 : ℚ) / 500000000000) + (521:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((451985687819 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((225991001889 : ℚ) / 500000000000) : ℚ) : ℝ) + ((521:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((521:ℚ)^(-2:ℤ) : ℝ) = ((521:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_98 : ((((225994671869 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 523, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 521 < q → q < 523 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 523).mp (by decide +kernel))) hgap
  have hprev := s2L_97
  have hrat : ((225994671869 : ℚ) / 500000000000) ≤ ((451985687819 : ℚ) / 1000000000000) + (523:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((225994671869 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((451985687819 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((523:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((523:ℚ)^(-2:ℤ) : ℝ) = ((523:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_99 : ((((451992760427 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 541, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 523 < q → q < 541 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 541).mp (by decide +kernel))) hgap
  have hprev := s2L_98
  have hrat : ((451992760427 : ℚ) / 1000000000000) ≤ ((225994671869 : ℚ) / 500000000000) + (541:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((451992760427 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((225994671869 : ℚ) / 500000000000) : ℚ) : ℝ) + ((541:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((541:ℚ)^(-2:ℤ) : ℝ) = ((541:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_100 : ((((112999025643 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 547, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 541 < q → q < 547 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 547).mp (by decide +kernel))) hgap
  have hprev := s2L_99
  have hrat : ((112999025643 : ℚ) / 250000000000) ≤ ((451992760427 : ℚ) / 1000000000000) + (547:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((112999025643 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((451992760427 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((547:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((547:ℚ)^(-2:ℤ) : ℝ) = ((547:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_101 : ((((451999325789 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 557, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 547 < q → q < 557 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 557).mp (by decide +kernel))) hgap
  have hprev := s2L_100
  have hrat : ((451999325789 : ℚ) / 1000000000000) ≤ ((112999025643 : ℚ) / 250000000000) + (557:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((451999325789 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((112999025643 : ℚ) / 250000000000) : ℚ) : ℝ) + ((557:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((557:ℚ)^(-2:ℤ) : ℝ) = ((557:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_102 : ((((452002480671 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 563, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 557 < q → q < 563 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 563).mp (by decide +kernel))) hgap
  have hprev := s2L_101
  have hrat : ((452002480671 : ℚ) / 1000000000000) ≤ ((451999325789 : ℚ) / 1000000000000) + (563:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452002480671 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((451999325789 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((563:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((563:ℚ)^(-2:ℤ) : ℝ) = ((563:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_103 : ((((452005569369 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 569, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 563 < q → q < 569 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 569).mp (by decide +kernel))) hgap
  have hprev := s2L_102
  have hrat : ((452005569369 : ℚ) / 1000000000000) ≤ ((452002480671 : ℚ) / 1000000000000) + (569:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452005569369 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452002480671 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((569:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((569:ℚ)^(-2:ℤ) : ℝ) = ((569:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_104 : ((((452008636467 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 571, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 569 < q → q < 571 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 571).mp (by decide +kernel))) hgap
  have hprev := s2L_103
  have hrat : ((452008636467 : ℚ) / 1000000000000) ≤ ((452005569369 : ℚ) / 1000000000000) + (571:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452008636467 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452005569369 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((571:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((571:ℚ)^(-2:ℤ) : ℝ) = ((571:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_105 : ((((45201164011 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 577, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 571 < q → q < 577 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 577).mp (by decide +kernel))) hgap
  have hprev := s2L_104
  have hrat : ((45201164011 : ℚ) / 100000000000) ≤ ((452008636467 : ℚ) / 1000000000000) + (577:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45201164011 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((452008636467 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((577:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((577:ℚ)^(-2:ℤ) : ℝ) = ((577:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_106 : ((((226007271143 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 587, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 577 < q → q < 587 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 587).mp (by decide +kernel))) hgap
  have hprev := s2L_105
  have hrat : ((226007271143 : ℚ) / 500000000000) ≤ ((45201164011 : ℚ) / 100000000000) + (587:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226007271143 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((45201164011 : ℚ) / 100000000000) : ℚ) : ℝ) + ((587:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((587:ℚ)^(-2:ℤ) : ℝ) = ((587:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_107 : ((((45201738603 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 593, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 587 < q → q < 593 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 593).mp (by decide +kernel))) hgap
  have hprev := s2L_106
  have hrat : ((45201738603 : ℚ) / 100000000000) ≤ ((226007271143 : ℚ) / 500000000000) + (593:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45201738603 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((226007271143 : ℚ) / 500000000000) : ℚ) : ℝ) + ((593:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((593:ℚ)^(-2:ℤ) : ℝ) = ((593:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_108 : ((((45202017309 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 599, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 593 < q → q < 599 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 599).mp (by decide +kernel))) hgap
  have hprev := s2L_107
  have hrat : ((45202017309 : ℚ) / 100000000000) ≤ ((45201738603 : ℚ) / 100000000000) + (599:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45202017309 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((45201738603 : ℚ) / 100000000000) : ℚ) : ℝ) + ((599:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((599:ℚ)^(-2:ℤ) : ℝ) = ((599:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_109 : ((((452022941631 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 601, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 599 < q → q < 601 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 601).mp (by decide +kernel))) hgap
  have hprev := s2L_108
  have hrat : ((452022941631 : ℚ) / 1000000000000) ≤ ((45202017309 : ℚ) / 100000000000) + (601:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452022941631 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((45202017309 : ℚ) / 100000000000) : ℚ) : ℝ) + ((601:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((601:ℚ)^(-2:ℤ) : ℝ) = ((601:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_110 : ((((45202565571 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 607, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 601 < q → q < 607 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 607).mp (by decide +kernel))) hgap
  have hprev := s2L_109
  have hrat : ((45202565571 : ℚ) / 100000000000) ≤ ((452022941631 : ℚ) / 1000000000000) + (607:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45202565571 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((452022941631 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((607:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((607:ℚ)^(-2:ℤ) : ℝ) = ((607:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_111 : ((((452028316919 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 613, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 607 < q → q < 613 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 613).mp (by decide +kernel))) hgap
  have hprev := s2L_110
  have hrat : ((452028316919 : ℚ) / 1000000000000) ≤ ((45202565571 : ℚ) / 100000000000) + (613:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452028316919 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((45202565571 : ℚ) / 100000000000) : ℚ) : ℝ) + ((613:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((613:ℚ)^(-2:ℤ) : ℝ) = ((613:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_112 : ((((90406188747 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 617, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 613 < q → q < 617 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 617).mp (by decide +kernel))) hgap
  have hprev := s2L_111
  have hrat : ((90406188747 : ℚ) / 200000000000) ≤ ((452028316919 : ℚ) / 1000000000000) + (617:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90406188747 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452028316919 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((617:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((617:ℚ)^(-2:ℤ) : ℝ) = ((617:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_113 : ((((452033553603 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 619, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 617 < q → q < 619 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 619).mp (by decide +kernel))) hgap
  have hprev := s2L_112
  have hrat : ((452033553603 : ℚ) / 1000000000000) ≤ ((90406188747 : ℚ) / 200000000000) + (619:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452033553603 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90406188747 : ℚ) / 200000000000) : ℚ) : ℝ) + ((619:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((619:ℚ)^(-2:ℤ) : ℝ) = ((619:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_114 : ((((452036065149 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 631, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 619 < q → q < 631 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 631).mp (by decide +kernel))) hgap
  have hprev := s2L_113
  have hrat : ((452036065149 : ℚ) / 1000000000000) ≤ ((452033553603 : ℚ) / 1000000000000) + (631:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452036065149 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452033553603 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((631:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((631:ℚ)^(-2:ℤ) : ℝ) = ((631:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_115 : ((((452038498943 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 641, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 631 < q → q < 641 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 641).mp (by decide +kernel))) hgap
  have hprev := s2L_114
  have hrat : ((452038498943 : ℚ) / 1000000000000) ≤ ((452036065149 : ℚ) / 1000000000000) + (641:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452038498943 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452036065149 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((641:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((641:ℚ)^(-2:ℤ) : ℝ) = ((641:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_116 : ((((22602045881 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 643, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 641 < q → q < 643 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 643).mp (by decide +kernel))) hgap
  have hprev := s2L_115
  have hrat : ((22602045881 : ℚ) / 50000000000) ≤ ((452038498943 : ℚ) / 1000000000000) + (643:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22602045881 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((452038498943 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((643:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((643:ℚ)^(-2:ℤ) : ℝ) = ((643:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_117 : ((((113010826621 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 647, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 643 < q → q < 647 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 647).mp (by decide +kernel))) hgap
  have hprev := s2L_116
  have hrat : ((113010826621 : ℚ) / 250000000000) ≤ ((22602045881 : ℚ) / 50000000000) + (647:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113010826621 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((22602045881 : ℚ) / 50000000000) : ℚ) : ℝ) + ((647:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((647:ℚ)^(-2:ℤ) : ℝ) = ((647:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_118 : ((((9040913033 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 653, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 647 < q → q < 653 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 653).mp (by decide +kernel))) hgap
  have hprev := s2L_117
  have hrat : ((9040913033 : ℚ) / 20000000000) ≤ ((113010826621 : ℚ) / 250000000000) + (653:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((9040913033 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ ((((113010826621 : ℚ) / 250000000000) : ℚ) : ℝ) + ((653:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((653:ℚ)^(-2:ℤ) : ℝ) = ((653:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_119 : ((((226023977153 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 659, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 653 < q → q < 659 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 659).mp (by decide +kernel))) hgap
  have hprev := s2L_118
  have hrat : ((226023977153 : ℚ) / 500000000000) ≤ ((9040913033 : ℚ) / 20000000000) + (659:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226023977153 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((9040913033 : ℚ) / 20000000000) : ℚ) : ℝ) + ((659:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((659:ℚ)^(-2:ℤ) : ℝ) = ((659:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_120 : ((((452050243049 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 661, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 659 < q → q < 661 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 661).mp (by decide +kernel))) hgap
  have hprev := s2L_119
  have hrat : ((452050243049 : ℚ) / 1000000000000) ≤ ((226023977153 : ℚ) / 500000000000) + (661:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452050243049 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226023977153 : ℚ) / 500000000000) : ℚ) : ℝ) + ((661:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((661:ℚ)^(-2:ℤ) : ℝ) = ((661:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_121 : ((((4520524509 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 673, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 661 < q → q < 673 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 673).mp (by decide +kernel))) hgap
  have hprev := s2L_120
  have hrat : ((4520524509 : ℚ) / 10000000000) ≤ ((452050243049 : ℚ) / 1000000000000) + (673:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((4520524509 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ ((((452050243049 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((673:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((673:ℚ)^(-2:ℤ) : ℝ) = ((673:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_122 : ((((226027316369 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 677, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 673 < q → q < 677 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 677).mp (by decide +kernel))) hgap
  have hprev := s2L_121
  have hrat : ((226027316369 : ℚ) / 500000000000) ≤ ((4520524509 : ℚ) / 10000000000) + (677:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226027316369 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((4520524509 : ℚ) / 10000000000) : ℚ) : ℝ) + ((677:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((677:ℚ)^(-2:ℤ) : ℝ) = ((677:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_123 : ((((452056776411 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 683, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 677 < q → q < 683 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 683).mp (by decide +kernel))) hgap
  have hprev := s2L_122
  have hrat : ((452056776411 : ℚ) / 1000000000000) ≤ ((226027316369 : ℚ) / 500000000000) + (683:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452056776411 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226027316369 : ℚ) / 500000000000) : ℚ) : ℝ) + ((683:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((683:ℚ)^(-2:ℤ) : ℝ) = ((683:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_124 : ((((90411774147 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 691, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 683 < q → q < 691 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 691).mp (by decide +kernel))) hgap
  have hprev := s2L_123
  have hrat : ((90411774147 : ℚ) / 200000000000) ≤ ((452056776411 : ℚ) / 1000000000000) + (691:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90411774147 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452056776411 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((691:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((691:ℚ)^(-2:ℤ) : ℝ) = ((691:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_125 : ((((113015226433 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 701, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 691 < q → q < 701 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 701).mp (by decide +kernel))) hgap
  have hprev := s2L_124
  have hrat : ((113015226433 : ℚ) / 250000000000) ≤ ((90411774147 : ℚ) / 200000000000) + (701:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113015226433 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((90411774147 : ℚ) / 200000000000) : ℚ) : ℝ) + ((701:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((701:ℚ)^(-2:ℤ) : ℝ) = ((701:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_126 : ((((90412579013 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 709, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 701 < q → q < 709 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 709).mp (by decide +kernel))) hgap
  have hprev := s2L_125
  have hrat : ((90412579013 : ℚ) / 200000000000) ≤ ((113015226433 : ℚ) / 250000000000) + (709:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90412579013 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((113015226433 : ℚ) / 250000000000) : ℚ) : ℝ) + ((709:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((709:ℚ)^(-2:ℤ) : ℝ) = ((709:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_127 : ((((226032414723 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 719, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 709 < q → q < 719 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 719).mp (by decide +kernel))) hgap
  have hprev := s2L_126
  have hrat : ((226032414723 : ℚ) / 500000000000) ≤ ((90412579013 : ℚ) / 200000000000) + (719:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226032414723 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((90412579013 : ℚ) / 200000000000) : ℚ) : ℝ) + ((719:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((719:ℚ)^(-2:ℤ) : ℝ) = ((719:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_128 : ((((452066721489 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 727, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 719 < q → q < 727 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 727).mp (by decide +kernel))) hgap
  have hprev := s2L_127
  have hrat : ((452066721489 : ℚ) / 1000000000000) ≤ ((226032414723 : ℚ) / 500000000000) + (727:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452066721489 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226032414723 : ℚ) / 500000000000) : ℚ) : ℝ) + ((727:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((727:ℚ)^(-2:ℤ) : ℝ) = ((727:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_129 : ((((113017145671 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 733, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 727 < q → q < 733 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 733).mp (by decide +kernel))) hgap
  have hprev := s2L_128
  have hrat : ((113017145671 : ℚ) / 250000000000) ≤ ((452066721489 : ℚ) / 1000000000000) + (733:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113017145671 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452066721489 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((733:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((733:ℚ)^(-2:ℤ) : ℝ) = ((733:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_130 : ((((22603520689 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 739, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 733 < q → q < 739 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 739).mp (by decide +kernel))) hgap
  have hprev := s2L_129
  have hrat : ((22603520689 : ℚ) / 50000000000) ≤ ((113017145671 : ℚ) / 250000000000) + (739:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22603520689 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((113017145671 : ℚ) / 250000000000) : ℚ) : ℝ) + ((739:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((739:ℚ)^(-2:ℤ) : ℝ) = ((739:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_131 : ((((452072225213 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 743, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 739 < q → q < 743 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 743).mp (by decide +kernel))) hgap
  have hprev := s2L_130
  have hrat : ((452072225213 : ℚ) / 1000000000000) ≤ ((22603520689 : ℚ) / 50000000000) + (743:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452072225213 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((22603520689 : ℚ) / 50000000000) : ℚ) : ℝ) + ((743:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((743:ℚ)^(-2:ℤ) : ℝ) = ((743:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_132 : ((((452073998259 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 751, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 743 < q → q < 751 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 751).mp (by decide +kernel))) hgap
  have hprev := s2L_131
  have hrat : ((452073998259 : ℚ) / 1000000000000) ≤ ((452072225213 : ℚ) / 1000000000000) + (751:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452073998259 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452072225213 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((751:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((751:ℚ)^(-2:ℤ) : ℝ) = ((751:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_133 : ((((45207574331 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 757, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 751 < q → q < 757 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 757).mp (by decide +kernel))) hgap
  have hprev := s2L_132
  have hrat : ((45207574331 : ℚ) / 100000000000) ≤ ((452073998259 : ℚ) / 1000000000000) + (757:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45207574331 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((452073998259 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((757:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((757:ℚ)^(-2:ℤ) : ℝ) = ((757:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_134 : ((((28254841879 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 761, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 757 < q → q < 761 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 761).mp (by decide +kernel))) hgap
  have hprev := s2L_133
  have hrat : ((28254841879 : ℚ) / 62500000000) ≤ ((45207574331 : ℚ) / 100000000000) + (761:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28254841879 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((45207574331 : ℚ) / 100000000000) : ℚ) : ℝ) + ((761:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((761:ℚ)^(-2:ℤ) : ℝ) = ((761:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_135 : ((((226039580539 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 769, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 761 < q → q < 769 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 769).mp (by decide +kernel))) hgap
  have hprev := s2L_134
  have hrat : ((226039580539 : ℚ) / 500000000000) ≤ ((28254841879 : ℚ) / 62500000000) + (769:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226039580539 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((28254841879 : ℚ) / 62500000000) : ℚ) : ℝ) + ((769:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((769:ℚ)^(-2:ℤ) : ℝ) = ((769:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_136 : ((((113020208659 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 773, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 769 < q → q < 773 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 773).mp (by decide +kernel))) hgap
  have hprev := s2L_135
  have hrat : ((113020208659 : ℚ) / 250000000000) ≤ ((226039580539 : ℚ) / 500000000000) + (773:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113020208659 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226039580539 : ℚ) / 500000000000) : ℚ) : ℝ) + ((773:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((773:ℚ)^(-2:ℤ) : ℝ) = ((773:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_137 : ((((226041224591 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 787, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 773 < q → q < 787 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 787).mp (by decide +kernel))) hgap
  have hprev := s2L_136
  have hrat : ((226041224591 : ℚ) / 500000000000) ≤ ((113020208659 : ℚ) / 250000000000) + (787:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226041224591 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113020208659 : ℚ) / 250000000000) : ℚ) : ℝ) + ((787:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((787:ℚ)^(-2:ℤ) : ℝ) = ((787:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_138 : ((((226042011733 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 797, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 787 < q → q < 797 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 797).mp (by decide +kernel))) hgap
  have hprev := s2L_137
  have hrat : ((226042011733 : ℚ) / 500000000000) ≤ ((226041224591 : ℚ) / 500000000000) + (797:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226042011733 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226041224591 : ℚ) / 500000000000) : ℚ) : ℝ) + ((797:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((797:ℚ)^(-2:ℤ) : ℝ) = ((797:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_139 : ((((226042775697 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 809, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 797 < q → q < 809 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 809).mp (by decide +kernel))) hgap
  have hprev := s2L_138
  have hrat : ((226042775697 : ℚ) / 500000000000) ≤ ((226042011733 : ℚ) / 500000000000) + (809:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226042775697 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226042011733 : ℚ) / 500000000000) : ℚ) : ℝ) + ((809:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((809:ℚ)^(-2:ℤ) : ℝ) = ((809:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_140 : ((((90417414359 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 811, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 809 < q → q < 811 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 811).mp (by decide +kernel))) hgap
  have hprev := s2L_139
  have hrat : ((90417414359 : ℚ) / 200000000000) ≤ ((226042775697 : ℚ) / 500000000000) + (811:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90417414359 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((226042775697 : ℚ) / 500000000000) : ℚ) : ℝ) + ((811:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((811:ℚ)^(-2:ℤ) : ℝ) = ((811:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_141 : ((((56511069423 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 821, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 811 < q → q < 821 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 821).mp (by decide +kernel))) hgap
  have hprev := s2L_140
  have hrat : ((56511069423 : ℚ) / 125000000000) ≤ ((90417414359 : ℚ) / 200000000000) + (821:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56511069423 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((90417414359 : ℚ) / 200000000000) : ℚ) : ℝ) + ((821:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((821:ℚ)^(-2:ℤ) : ℝ) = ((821:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_142 : ((((452090031771 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 823, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 821 < q → q < 823 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 823).mp (by decide +kernel))) hgap
  have hprev := s2L_141
  have hrat : ((452090031771 : ℚ) / 1000000000000) ≤ ((56511069423 : ℚ) / 125000000000) + (823:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452090031771 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56511069423 : ℚ) / 125000000000) : ℚ) : ℝ) + ((823:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((823:ℚ)^(-2:ℤ) : ℝ) = ((823:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_143 : ((((452091493911 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 827, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 823 < q → q < 827 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 827).mp (by decide +kernel))) hgap
  have hprev := s2L_142
  have hrat : ((452091493911 : ℚ) / 1000000000000) ≤ ((452090031771 : ℚ) / 1000000000000) + (827:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452091493911 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452090031771 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((827:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((827:ℚ)^(-2:ℤ) : ℝ) = ((827:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_144 : ((((113023237251 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 829, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 827 < q → q < 829 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 829).mp (by decide +kernel))) hgap
  have hprev := s2L_143
  have hrat : ((113023237251 : ℚ) / 250000000000) ≤ ((452091493911 : ℚ) / 1000000000000) + (829:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113023237251 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452091493911 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((829:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((829:ℚ)^(-2:ℤ) : ℝ) = ((829:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_145 : ((((452094369617 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 839, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 829 < q → q < 839 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 839).mp (by decide +kernel))) hgap
  have hprev := s2L_144
  have hrat : ((452094369617 : ℚ) / 1000000000000) ≤ ((113023237251 : ℚ) / 250000000000) + (839:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452094369617 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113023237251 : ℚ) / 250000000000) : ℚ) : ℝ) + ((839:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((839:ℚ)^(-2:ℤ) : ℝ) = ((839:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_146 : ((((452095743981 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 853, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 839 < q → q < 853 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 853).mp (by decide +kernel))) hgap
  have hprev := s2L_145
  have hrat : ((452095743981 : ℚ) / 1000000000000) ≤ ((452094369617 : ℚ) / 1000000000000) + (853:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452095743981 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452094369617 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((853:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((853:ℚ)^(-2:ℤ) : ℝ) = ((853:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_147 : ((((90419421109 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 857, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 853 < q → q < 857 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 857).mp (by decide +kernel))) hgap
  have hprev := s2L_146
  have hrat : ((90419421109 : ℚ) / 200000000000) ≤ ((452095743981 : ℚ) / 1000000000000) + (857:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90419421109 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452095743981 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((857:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((857:ℚ)^(-2:ℤ) : ℝ) = ((857:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_148 : ((((452098460777 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 859, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 857 < q → q < 859 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 859).mp (by decide +kernel))) hgap
  have hprev := s2L_147
  have hrat : ((452098460777 : ℚ) / 1000000000000) ≤ ((90419421109 : ℚ) / 200000000000) + (859:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452098460777 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90419421109 : ℚ) / 200000000000) : ℚ) : ℝ) + ((859:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((859:ℚ)^(-2:ℤ) : ℝ) = ((859:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_149 : ((((18083992139 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 863, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 859 < q → q < 863 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 863).mp (by decide +kernel))) hgap
  have hprev := s2L_148
  have hrat : ((18083992139 : ℚ) / 40000000000) ≤ ((452098460777 : ℚ) / 1000000000000) + (863:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18083992139 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((452098460777 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((863:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((863:ℚ)^(-2:ℤ) : ℝ) = ((863:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_150 : ((((452101103647 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 877, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 863 < q → q < 877 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 877).mp (by decide +kernel))) hgap
  have hprev := s2L_149
  have hrat : ((452101103647 : ℚ) / 1000000000000) ≤ ((18083992139 : ℚ) / 40000000000) + (877:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452101103647 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((18083992139 : ℚ) / 40000000000) : ℚ) : ℝ) + ((877:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((877:ℚ)^(-2:ℤ) : ℝ) = ((877:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_151 : ((((452102392039 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 881, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 877 < q → q < 881 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 881).mp (by decide +kernel))) hgap
  have hprev := s2L_150
  have hrat : ((452102392039 : ℚ) / 1000000000000) ≤ ((452101103647 : ℚ) / 1000000000000) + (881:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452102392039 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452101103647 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((881:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((881:ℚ)^(-2:ℤ) : ℝ) = ((881:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_152 : ((((452103674601 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 883, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 881 < q → q < 883 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 883).mp (by decide +kernel))) hgap
  have hprev := s2L_151
  have hrat : ((452103674601 : ℚ) / 1000000000000) ≤ ((452102392039 : ℚ) / 1000000000000) + (883:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452103674601 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452102392039 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((883:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((883:ℚ)^(-2:ℤ) : ℝ) = ((883:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_153 : ((((226052472811 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 887, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 883 < q → q < 887 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 887).mp (by decide +kernel))) hgap
  have hprev := s2L_152
  have hrat : ((226052472811 : ℚ) / 500000000000) ≤ ((452103674601 : ℚ) / 1000000000000) + (887:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226052472811 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452103674601 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((887:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((887:ℚ)^(-2:ℤ) : ℝ) = ((887:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_154 : ((((452106161207 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 907, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 887 < q → q < 907 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 907).mp (by decide +kernel))) hgap
  have hprev := s2L_153
  have hrat : ((452106161207 : ℚ) / 1000000000000) ≤ ((226052472811 : ℚ) / 500000000000) + (907:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452106161207 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226052472811 : ℚ) / 500000000000) : ℚ) : ℝ) + ((907:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((907:ℚ)^(-2:ℤ) : ℝ) = ((907:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_155 : ((((22605368307 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 911, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 907 < q → q < 911 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 911).mp (by decide +kernel))) hgap
  have hprev := s2L_154
  have hrat : ((22605368307 : ℚ) / 50000000000) ≤ ((452106161207 : ℚ) / 1000000000000) + (911:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22605368307 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((452106161207 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((911:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((911:ℚ)^(-2:ℤ) : ℝ) = ((911:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_156 : ((((452108550187 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 919, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 911 < q → q < 919 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 919).mp (by decide +kernel))) hgap
  have hprev := s2L_155
  have hrat : ((452108550187 : ℚ) / 1000000000000) ≤ ((22605368307 : ℚ) / 50000000000) + (919:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452108550187 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((22605368307 : ℚ) / 50000000000) : ℚ) : ℝ) + ((919:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((919:ℚ)^(-2:ℤ) : ℝ) = ((919:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_157 : ((((5651371361 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 929, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 919 < q → q < 929 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 929).mp (by decide +kernel))) hgap
  have hprev := s2L_156
  have hrat : ((5651371361 : ℚ) / 12500000000) ≤ ((452108550187 : ℚ) / 1000000000000) + (929:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((5651371361 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ ((((452108550187 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((929:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((929:ℚ)^(-2:ℤ) : ℝ) = ((929:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_158 : ((((3532115999 : ℚ) / 7812500000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 937, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 929 < q → q < 937 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 937).mp (by decide +kernel))) hgap
  have hprev := s2L_157
  have hrat : ((3532115999 : ℚ) / 7812500000) ≤ ((5651371361 : ℚ) / 12500000000) + (937:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((3532115999 : ℚ) / 7812500000) : ℚ) : ℝ) ≤ ((((5651371361 : ℚ) / 12500000000) : ℚ) : ℝ) + ((937:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((937:ℚ)^(-2:ℤ) : ℝ) = ((937:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_159 : ((((452111977201 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 941, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 937 < q → q < 941 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 941).mp (by decide +kernel))) hgap
  have hprev := s2L_158
  have hrat : ((452111977201 : ℚ) / 1000000000000) ≤ ((3532115999 : ℚ) / 7812500000) + (941:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452111977201 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3532115999 : ℚ) / 7812500000) : ℚ) : ℝ) + ((941:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((941:ℚ)^(-2:ℤ) : ℝ) = ((941:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_160 : ((((90422618453 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 947, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 941 < q → q < 947 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 947).mp (by decide +kernel))) hgap
  have hprev := s2L_159
  have hrat : ((90422618453 : ℚ) / 200000000000) ≤ ((452111977201 : ℚ) / 1000000000000) + (947:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90422618453 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452111977201 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((947:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((947:ℚ)^(-2:ℤ) : ℝ) = ((947:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_161 : ((((452114193333 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 953, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 947 < q → q < 953 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 953).mp (by decide +kernel))) hgap
  have hprev := s2L_160
  have hrat : ((452114193333 : ℚ) / 1000000000000) ≤ ((90422618453 : ℚ) / 200000000000) + (953:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452114193333 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90422618453 : ℚ) / 200000000000) : ℚ) : ℝ) + ((953:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((953:ℚ)^(-2:ℤ) : ℝ) = ((953:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_162 : ((((452115262749 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 967, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 953 < q → q < 967 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 967).mp (by decide +kernel))) hgap
  have hprev := s2L_161
  have hrat : ((452115262749 : ℚ) / 1000000000000) ≤ ((452114193333 : ℚ) / 1000000000000) + (967:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452115262749 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452114193333 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((967:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((967:ℚ)^(-2:ℤ) : ℝ) = ((967:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_163 : ((((452116323373 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 971, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 967 < q → q < 971 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 971).mp (by decide +kernel))) hgap
  have hprev := s2L_162
  have hrat : ((452116323373 : ℚ) / 1000000000000) ≤ ((452115262749 : ℚ) / 1000000000000) + (971:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452116323373 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452115262749 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((971:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((971:ℚ)^(-2:ℤ) : ℝ) = ((971:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_164 : ((((45211737101 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 977, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 971 < q → q < 977 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 977).mp (by decide +kernel))) hgap
  have hprev := s2L_163
  have hrat : ((45211737101 : ℚ) / 100000000000) ≤ ((452116323373 : ℚ) / 1000000000000) + (977:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45211737101 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((452116323373 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((977:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((977:ℚ)^(-2:ℤ) : ℝ) = ((977:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_165 : ((((452118405897 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 983, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 977 < q → q < 983 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 983).mp (by decide +kernel))) hgap
  have hprev := s2L_164
  have hrat : ((452118405897 : ℚ) / 1000000000000) ≤ ((45211737101 : ℚ) / 100000000000) + (983:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452118405897 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((45211737101 : ℚ) / 100000000000) : ℚ) : ℝ) + ((983:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((983:ℚ)^(-2:ℤ) : ℝ) = ((983:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_166 : ((((226059712071 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 991, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 983 < q → q < 991 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 991).mp (by decide +kernel))) hgap
  have hprev := s2L_165
  have hrat : ((226059712071 : ℚ) / 500000000000) ≤ ((452118405897 : ℚ) / 1000000000000) + (991:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226059712071 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452118405897 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((991:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((991:ℚ)^(-2:ℤ) : ℝ) = ((991:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_167 : ((((452120430169 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 997, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 991 < q → q < 997 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 997).mp (by decide +kernel))) hgap
  have hprev := s2L_166
  have hrat : ((452120430169 : ℚ) / 1000000000000) ≤ ((226059712071 : ℚ) / 500000000000) + (997:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452120430169 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226059712071 : ℚ) / 500000000000) : ℚ) : ℝ) + ((997:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((997:ℚ)^(-2:ℤ) : ℝ) = ((997:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_168 : ((((452121412409 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1009, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 997 < q → q < 1009 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1009).mp (by decide +kernel))) hgap
  have hprev := s2L_167
  have hrat : ((452121412409 : ℚ) / 1000000000000) ≤ ((452120430169 : ℚ) / 1000000000000) + (1009:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452121412409 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452120430169 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((1009:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1009:ℚ)^(-2:ℤ) : ℝ) = ((1009:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_169 : ((((452122386907 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1013, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1009 < q → q < 1013 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1013).mp (by decide +kernel))) hgap
  have hprev := s2L_168
  have hrat : ((452122386907 : ℚ) / 1000000000000) ≤ ((452121412409 : ℚ) / 1000000000000) + (1013:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452122386907 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452121412409 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((1013:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1013:ℚ)^(-2:ℤ) : ℝ) = ((1013:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_170 : ((((452123349963 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1019, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1013 < q → q < 1019 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1019).mp (by decide +kernel))) hgap
  have hprev := s2L_169
  have hrat : ((452123349963 : ℚ) / 1000000000000) ≤ ((452122386907 : ℚ) / 1000000000000) + (1019:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452123349963 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452122386907 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((1019:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1019:ℚ)^(-2:ℤ) : ℝ) = ((1019:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_171 : ((((452124309249 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1021, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1019 < q → q < 1021 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1021).mp (by decide +kernel))) hgap
  have hprev := s2L_170
  have hrat : ((452124309249 : ℚ) / 1000000000000) ≤ ((452123349963 : ℚ) / 1000000000000) + (1021:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452124309249 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452123349963 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((1021:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1021:ℚ)^(-2:ℤ) : ℝ) = ((1021:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_172 : ((((452125250017 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1031, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1021 < q → q < 1031 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1031).mp (by decide +kernel))) hgap
  have hprev := s2L_171
  have hrat : ((452125250017 : ℚ) / 1000000000000) ≤ ((452124309249 : ℚ) / 1000000000000) + (1031:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452125250017 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452124309249 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((1031:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1031:ℚ)^(-2:ℤ) : ℝ) = ((1031:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_173 : ((((90425237429 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1033, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1031 < q → q < 1033 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1033).mp (by decide +kernel))) hgap
  have hprev := s2L_172
  have hrat : ((90425237429 : ℚ) / 200000000000) ≤ ((452125250017 : ℚ) / 1000000000000) + (1033:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90425237429 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452125250017 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((1033:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1033:ℚ)^(-2:ℤ) : ℝ) = ((1033:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_174 : ((((452127113481 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1039, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1033 < q → q < 1039 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1039).mp (by decide +kernel))) hgap
  have hprev := s2L_173
  have hrat : ((452127113481 : ℚ) / 1000000000000) ≤ ((90425237429 : ℚ) / 200000000000) + (1039:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452127113481 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90425237429 : ℚ) / 200000000000) : ℚ) : ℝ) + ((1039:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1039:ℚ)^(-2:ℤ) : ℝ) = ((1039:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_175 : ((((2825800139 : ℚ) / 6250000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1049, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1039 < q → q < 1049 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1049).mp (by decide +kernel))) hgap
  have hprev := s2L_174
  have hrat : ((2825800139 : ℚ) / 6250000000) ≤ ((452127113481 : ℚ) / 1000000000000) + (1049:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((2825800139 : ℚ) / 6250000000) : ℚ) : ℝ) ≤ ((((452127113481 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((1049:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1049:ℚ)^(-2:ℤ) : ℝ) = ((1049:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_176 : ((((56516115943 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1051, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1049 < q → q < 1051 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1051).mp (by decide +kernel))) hgap
  have hprev := s2L_175
  have hrat : ((56516115943 : ℚ) / 125000000000) ≤ ((2825800139 : ℚ) / 6250000000) + (1051:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56516115943 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((2825800139 : ℚ) / 6250000000) : ℚ) : ℝ) + ((1051:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1051:ℚ)^(-2:ℤ) : ℝ) = ((1051:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_177 : ((((452129815863 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1061, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1051 < q → q < 1061 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1061).mp (by decide +kernel))) hgap
  have hprev := s2L_176
  have hrat : ((452129815863 : ℚ) / 1000000000000) ≤ ((56516115943 : ℚ) / 125000000000) + (1061:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452129815863 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56516115943 : ℚ) / 125000000000) : ℚ) : ℝ) + ((1061:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1061:ℚ)^(-2:ℤ) : ℝ) = ((1061:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_178 : ((((452130700843 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1063, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1061 < q → q < 1063 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1063).mp (by decide +kernel))) hgap
  have hprev := s2L_177
  have hrat : ((452130700843 : ℚ) / 1000000000000) ≤ ((452129815863 : ℚ) / 1000000000000) + (1063:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452130700843 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452129815863 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((1063:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1063:ℚ)^(-2:ℤ) : ℝ) = ((1063:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_179 : ((((113032893979 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1069, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1063 < q → q < 1069 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1069).mp (by decide +kernel))) hgap
  have hprev := s2L_178
  have hrat : ((113032893979 : ℚ) / 250000000000) ≤ ((452130700843 : ℚ) / 1000000000000) + (1069:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113032893979 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452130700843 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((1069:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1069:ℚ)^(-2:ℤ) : ℝ) = ((1069:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_180 : ((((56516552781 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1087, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1069 < q → q < 1087 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1087).mp (by decide +kernel))) hgap
  have hprev := s2L_179
  have hrat : ((56516552781 : ℚ) / 125000000000) ≤ ((113032893979 : ℚ) / 250000000000) + (1087:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56516552781 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((113032893979 : ℚ) / 250000000000) : ℚ) : ℝ) + ((1087:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1087:ℚ)^(-2:ℤ) : ℝ) = ((1087:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_181 : ((((90426652477 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1091, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1087 < q → q < 1091 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1091).mp (by decide +kernel))) hgap
  have hprev := s2L_180
  have hrat : ((90426652477 : ℚ) / 200000000000) ≤ ((56516552781 : ℚ) / 125000000000) + (1091:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90426652477 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((56516552781 : ℚ) / 125000000000) : ℚ) : ℝ) + ((1091:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1091:ℚ)^(-2:ℤ) : ℝ) = ((1091:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_182 : ((((9042681989 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1093, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1091 < q → q < 1093 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1093).mp (by decide +kernel))) hgap
  have hprev := s2L_181
  have hrat : ((9042681989 : ℚ) / 20000000000) ≤ ((90426652477 : ℚ) / 200000000000) + (1093:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((9042681989 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ ((((90426652477 : ℚ) / 200000000000) : ℚ) : ℝ) + ((1093:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1093:ℚ)^(-2:ℤ) : ℝ) = ((1093:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_183 : ((((226067465211 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1097, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1093 < q → q < 1097 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1097).mp (by decide +kernel))) hgap
  have hprev := s2L_182
  have hrat : ((226067465211 : ℚ) / 500000000000) ≤ ((9042681989 : ℚ) / 20000000000) + (1097:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226067465211 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((9042681989 : ℚ) / 20000000000) : ℚ) : ℝ) + ((1097:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1097:ℚ)^(-2:ℤ) : ℝ) = ((1097:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_184 : ((((226067876189 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1103, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1097 < q → q < 1103 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1103).mp (by decide +kernel))) hgap
  have hprev := s2L_183
  have hrat : ((226067876189 : ℚ) / 500000000000) ≤ ((226067465211 : ℚ) / 500000000000) + (1103:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226067876189 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226067465211 : ℚ) / 500000000000) : ℚ) : ℝ) + ((1103:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1103:ℚ)^(-2:ℤ) : ℝ) = ((1103:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_185 : ((((56517070683 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1109, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1103 < q → q < 1109 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1109).mp (by decide +kernel))) hgap
  have hprev := s2L_184
  have hrat : ((56517070683 : ℚ) / 125000000000) ≤ ((226067876189 : ℚ) / 500000000000) + (1109:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56517070683 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((226067876189 : ℚ) / 500000000000) : ℚ) : ℝ) + ((1109:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1109:ℚ)^(-2:ℤ) : ℝ) = ((1109:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_186 : ((((90427473389 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1117, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1109 < q → q < 1117 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1117).mp (by decide +kernel))) hgap
  have hprev := s2L_185
  have hrat : ((90427473389 : ℚ) / 200000000000) ≤ ((56517070683 : ℚ) / 125000000000) + (1117:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90427473389 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((56517070683 : ℚ) / 125000000000) : ℚ) : ℝ) + ((1117:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1117:ℚ)^(-2:ℤ) : ℝ) = ((1117:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_187 : ((((90427631977 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1123, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1117 < q → q < 1123 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1123).mp (by decide +kernel))) hgap
  have hprev := s2L_186
  have hrat : ((90427631977 : ℚ) / 200000000000) ≤ ((90427473389 : ℚ) / 200000000000) + (1123:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90427631977 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((90427473389 : ℚ) / 200000000000) : ℚ) : ℝ) + ((1123:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1123:ℚ)^(-2:ℤ) : ℝ) = ((1123:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_188 : ((((452138944419 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1129, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1123 < q → q < 1129 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1129).mp (by decide +kernel))) hgap
  have hprev := s2L_187
  have hrat : ((452138944419 : ℚ) / 1000000000000) ≤ ((90427631977 : ℚ) / 200000000000) + (1129:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452138944419 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90427631977 : ℚ) / 200000000000) : ℚ) : ℝ) + ((1129:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1129:ℚ)^(-2:ℤ) : ℝ) = ((1129:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_189 : ((((452139699249 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1151, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1129 < q → q < 1151 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1151).mp (by decide +kernel))) hgap
  have hprev := s2L_188
  have hrat : ((452139699249 : ℚ) / 1000000000000) ≤ ((452138944419 : ℚ) / 1000000000000) + (1151:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452139699249 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452138944419 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((1151:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1151:ℚ)^(-2:ℤ) : ℝ) = ((1151:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_190 : ((((226070225731 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1153, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1151 < q → q < 1153 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1153).mp (by decide +kernel))) hgap
  have hprev := s2L_189
  have hrat : ((226070225731 : ℚ) / 500000000000) ≤ ((452139699249 : ℚ) / 1000000000000) + (1153:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226070225731 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452139699249 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((1153:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1153:ℚ)^(-2:ℤ) : ℝ) = ((1153:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_191 : ((((90428238159 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1163, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1153 < q → q < 1163 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1163).mp (by decide +kernel))) hgap
  have hprev := s2L_190
  have hrat : ((90428238159 : ℚ) / 200000000000) ≤ ((226070225731 : ℚ) / 500000000000) + (1163:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90428238159 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((226070225731 : ℚ) / 500000000000) : ℚ) : ℝ) + ((1163:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1163:ℚ)^(-2:ℤ) : ℝ) = ((1163:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_192 : ((((452141920061 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1171, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1163 < q → q < 1171 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1171).mp (by decide +kernel))) hgap
  have hprev := s2L_191
  have hrat : ((452141920061 : ℚ) / 1000000000000) ≤ ((90428238159 : ℚ) / 200000000000) + (1171:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452141920061 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90428238159 : ℚ) / 200000000000) : ℚ) : ℝ) + ((1171:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1171:ℚ)^(-2:ℤ) : ℝ) = ((1171:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_193 : ((((452142637029 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1181, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1171 < q → q < 1181 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1181).mp (by decide +kernel))) hgap
  have hprev := s2L_192
  have hrat : ((452142637029 : ℚ) / 1000000000000) ≤ ((452141920061 : ℚ) / 1000000000000) + (1181:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452142637029 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452141920061 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((1181:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1181:ℚ)^(-2:ℤ) : ℝ) = ((1181:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_194 : ((((452143346767 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1187, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1181 < q → q < 1187 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1187).mp (by decide +kernel))) hgap
  have hprev := s2L_193
  have hrat : ((452143346767 : ℚ) / 1000000000000) ≤ ((452142637029 : ℚ) / 1000000000000) + (1187:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452143346767 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452142637029 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((1187:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1187:ℚ)^(-2:ℤ) : ℝ) = ((1187:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_195 : ((((56518006173 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1193, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1187 < q → q < 1193 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1193).mp (by decide +kernel))) hgap
  have hprev := s2L_194
  have hrat : ((56518006173 : ℚ) / 125000000000) ≤ ((452143346767 : ℚ) / 1000000000000) + (1193:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56518006173 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452143346767 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((1193:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1193:ℚ)^(-2:ℤ) : ℝ) = ((1193:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_196 : ((((28259046417 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1201, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1193 < q → q < 1201 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1201).mp (by decide +kernel))) hgap
  have hprev := s2L_195
  have hrat : ((28259046417 : ℚ) / 62500000000) ≤ ((56518006173 : ℚ) / 125000000000) + (1201:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28259046417 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((56518006173 : ℚ) / 125000000000) : ℚ) : ℝ) + ((1201:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1201:ℚ)^(-2:ℤ) : ℝ) = ((1201:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_197 : ((((452145422311 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1213, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1201 < q → q < 1213 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1213).mp (by decide +kernel))) hgap
  have hprev := s2L_196
  have hrat : ((452145422311 : ℚ) / 1000000000000) ≤ ((28259046417 : ℚ) / 62500000000) + (1213:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452145422311 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((28259046417 : ℚ) / 62500000000) : ℚ) : ℝ) + ((1213:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1213:ℚ)^(-2:ℤ) : ℝ) = ((1213:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_198 : ((((452146097489 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1217, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1213 < q → q < 1217 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1217).mp (by decide +kernel))) hgap
  have hprev := s2L_197
  have hrat : ((452146097489 : ℚ) / 1000000000000) ≤ ((452145422311 : ℚ) / 1000000000000) + (1217:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452146097489 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452145422311 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((1217:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1217:ℚ)^(-2:ℤ) : ℝ) = ((1217:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_199 : ((((452146766059 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1223, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1217 < q → q < 1223 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1223).mp (by decide +kernel))) hgap
  have hprev := s2L_198
  have hrat : ((452146766059 : ℚ) / 1000000000000) ≤ ((452146097489 : ℚ) / 1000000000000) + (1223:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452146766059 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452146097489 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((1223:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1223:ℚ)^(-2:ℤ) : ℝ) = ((1223:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_200 : ((((452147428117 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1229, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1223 < q → q < 1229 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1229).mp (by decide +kernel))) hgap
  have hprev := s2L_199
  have hrat : ((452147428117 : ℚ) / 1000000000000) ≤ ((452146766059 : ℚ) / 1000000000000) + (1229:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452147428117 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452146766059 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((1229:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1229:ℚ)^(-2:ℤ) : ℝ) = ((1229:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_201 : ((((18085923521 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1231, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1229 < q → q < 1231 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1231).mp (by decide +kernel))) hgap
  have hprev := s2L_200
  have hrat : ((18085923521 : ℚ) / 40000000000) ≤ ((452147428117 : ℚ) / 1000000000000) + (1231:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18085923521 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((452147428117 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((1231:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1231:ℚ)^(-2:ℤ) : ℝ) = ((1231:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_202 : ((((452148741547 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1237, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1231 < q → q < 1237 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1237).mp (by decide +kernel))) hgap
  have hprev := s2L_201
  have hrat : ((452148741547 : ℚ) / 1000000000000) ≤ ((18085923521 : ℚ) / 40000000000) + (1237:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452148741547 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((18085923521 : ℚ) / 40000000000) : ℚ) : ℝ) + ((1237:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1237:ℚ)^(-2:ℤ) : ℝ) = ((1237:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_203 : ((((113037345643 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1249, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1237 < q → q < 1249 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1249).mp (by decide +kernel))) hgap
  have hprev := s2L_202
  have hrat : ((113037345643 : ℚ) / 250000000000) ≤ ((452148741547 : ℚ) / 1000000000000) + (1249:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113037345643 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452148741547 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((1249:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1249:ℚ)^(-2:ℤ) : ℝ) = ((1249:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_204 : ((((226075006727 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1259, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1249 < q → q < 1259 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1259).mp (by decide +kernel))) hgap
  have hprev := s2L_203
  have hrat : ((226075006727 : ℚ) / 500000000000) ≤ ((113037345643 : ℚ) / 250000000000) + (1259:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226075006727 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113037345643 : ℚ) / 250000000000) : ℚ) : ℝ) + ((1259:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1259:ℚ)^(-2:ℤ) : ℝ) = ((1259:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_205 : ((((113037656669 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1277, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1259 < q → q < 1277 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1277).mp (by decide +kernel))) hgap
  have hprev := s2L_204
  have hrat : ((113037656669 : ℚ) / 250000000000) ≤ ((226075006727 : ℚ) / 500000000000) + (1277:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113037656669 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226075006727 : ℚ) / 500000000000) : ℚ) : ℝ) + ((1277:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1277:ℚ)^(-2:ℤ) : ℝ) = ((1277:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_206 : ((((226075618991 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1279, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1277 < q → q < 1279 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1279).mp (by decide +kernel))) hgap
  have hprev := s2L_205
  have hrat : ((226075618991 : ℚ) / 500000000000) ≤ ((113037656669 : ℚ) / 250000000000) + (1279:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226075618991 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113037656669 : ℚ) / 250000000000) : ℚ) : ℝ) + ((1279:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1279:ℚ)^(-2:ℤ) : ℝ) = ((1279:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_207 : ((((226075922741 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1283, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1279 < q → q < 1283 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1283).mp (by decide +kernel))) hgap
  have hprev := s2L_206
  have hrat : ((226075922741 : ℚ) / 500000000000) ≤ ((226075618991 : ℚ) / 500000000000) + (1283:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226075922741 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226075618991 : ℚ) / 500000000000) : ℚ) : ℝ) + ((1283:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1283:ℚ)^(-2:ℤ) : ℝ) = ((1283:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_208 : ((((22607622367 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1289, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1283 < q → q < 1289 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1289).mp (by decide +kernel))) hgap
  have hprev := s2L_207
  have hrat : ((22607622367 : ℚ) / 50000000000) ≤ ((226075922741 : ℚ) / 500000000000) + (1289:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22607622367 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((226075922741 : ℚ) / 500000000000) : ℚ) : ℝ) + ((1289:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1289:ℚ)^(-2:ℤ) : ℝ) = ((1289:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_209 : ((((226076523667 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1291, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1289 < q → q < 1291 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1291).mp (by decide +kernel))) hgap
  have hprev := s2L_208
  have hrat : ((226076523667 : ℚ) / 500000000000) ≤ ((22607622367 : ℚ) / 50000000000) + (1291:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226076523667 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((22607622367 : ℚ) / 50000000000) : ℚ) : ℝ) + ((1291:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1291:ℚ)^(-2:ℤ) : ℝ) = ((1291:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_210 : ((((45215364179 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1297, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1291 < q → q < 1297 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1297).mp (by decide +kernel))) hgap
  have hprev := s2L_209
  have hrat : ((45215364179 : ℚ) / 100000000000) ≤ ((226076523667 : ℚ) / 500000000000) + (1297:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45215364179 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((226076523667 : ℚ) / 500000000000) : ℚ) : ℝ) + ((1297:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1297:ℚ)^(-2:ℤ) : ℝ) = ((1297:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_211 : ((((113038558149 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1301, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1297 < q → q < 1301 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1301).mp (by decide +kernel))) hgap
  have hprev := s2L_210
  have hrat : ((113038558149 : ℚ) / 250000000000) ≤ ((45215364179 : ℚ) / 100000000000) + (1301:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113038558149 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((45215364179 : ℚ) / 100000000000) : ℚ) : ℝ) + ((1301:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1301:ℚ)^(-2:ℤ) : ℝ) = ((1301:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_212 : ((((45215482159 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1303, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1301 < q → q < 1303 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1303).mp (by decide +kernel))) hgap
  have hprev := s2L_211
  have hrat : ((45215482159 : ℚ) / 100000000000) ≤ ((113038558149 : ℚ) / 250000000000) + (1303:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45215482159 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((113038558149 : ℚ) / 250000000000) : ℚ) : ℝ) + ((1303:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1303:ℚ)^(-2:ℤ) : ℝ) = ((1303:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_213 : ((((56519425873 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1307, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1303 < q → q < 1307 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1307).mp (by decide +kernel))) hgap
  have hprev := s2L_212
  have hrat : ((56519425873 : ℚ) / 125000000000) ≤ ((45215482159 : ℚ) / 100000000000) + (1307:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56519425873 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((45215482159 : ℚ) / 100000000000) : ℚ) : ℝ) + ((1307:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1307:ℚ)^(-2:ℤ) : ℝ) = ((1307:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_214 : ((((18086239271 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1319, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1307 < q → q < 1319 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1319).mp (by decide +kernel))) hgap
  have hprev := s2L_213
  have hrat : ((18086239271 : ℚ) / 40000000000) ≤ ((56519425873 : ℚ) / 125000000000) + (1319:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18086239271 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((56519425873 : ℚ) / 125000000000) : ℚ) : ℝ) + ((1319:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1319:ℚ)^(-2:ℤ) : ℝ) = ((1319:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_215 : ((((452156554827 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1321, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1319 < q → q < 1321 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1321).mp (by decide +kernel))) hgap
  have hprev := s2L_214
  have hrat : ((452156554827 : ℚ) / 1000000000000) ≤ ((18086239271 : ℚ) / 40000000000) + (1321:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452156554827 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((18086239271 : ℚ) / 40000000000) : ℚ) : ℝ) + ((1321:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1321:ℚ)^(-2:ℤ) : ℝ) = ((1321:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_216 : ((((452157122709 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1327, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1321 < q → q < 1327 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1327).mp (by decide +kernel))) hgap
  have hprev := s2L_215
  have hrat : ((452157122709 : ℚ) / 1000000000000) ≤ ((452156554827 : ℚ) / 1000000000000) + (1327:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452157122709 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452156554827 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((1327:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1327:ℚ)^(-2:ℤ) : ℝ) = ((1327:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_217 : ((((113039415643 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1361, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1327 < q → q < 1361 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1361).mp (by decide +kernel))) hgap
  have hprev := s2L_216
  have hrat : ((113039415643 : ℚ) / 250000000000) ≤ ((452157122709 : ℚ) / 1000000000000) + (1361:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113039415643 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452157122709 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((1361:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1361:ℚ)^(-2:ℤ) : ℝ) = ((1361:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_218 : ((((226079098853 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1367, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1361 < q → q < 1367 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1367).mp (by decide +kernel))) hgap
  have hprev := s2L_217
  have hrat : ((226079098853 : ℚ) / 500000000000) ≤ ((113039415643 : ℚ) / 250000000000) + (1367:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226079098853 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113039415643 : ℚ) / 250000000000) : ℚ) : ℝ) + ((1367:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1367:ℚ)^(-2:ℤ) : ℝ) = ((1367:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_219 : ((((452158728173 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1373, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1367 < q → q < 1373 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1373).mp (by decide +kernel))) hgap
  have hprev := s2L_218
  have hrat : ((452158728173 : ℚ) / 1000000000000) ≤ ((226079098853 : ℚ) / 500000000000) + (1373:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452158728173 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226079098853 : ℚ) / 500000000000) : ℚ) : ℝ) + ((1373:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1373:ℚ)^(-2:ℤ) : ℝ) = ((1373:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_220 : ((((14129976641 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1381, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1373 < q → q < 1381 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1381).mp (by decide +kernel))) hgap
  have hprev := s2L_219
  have hrat : ((14129976641 : ℚ) / 31250000000) ≤ ((452158728173 : ℚ) / 1000000000000) + (1381:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((14129976641 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((452158728173 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((1381:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1381:ℚ)^(-2:ℤ) : ℝ) = ((1381:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_221 : ((((90431952689 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1399, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1381 < q → q < 1399 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1399).mp (by decide +kernel))) hgap
  have hprev := s2L_220
  have hrat : ((90431952689 : ℚ) / 200000000000) ≤ ((14129976641 : ℚ) / 31250000000) + (1399:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90431952689 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((14129976641 : ℚ) / 31250000000) : ℚ) : ℝ) + ((1399:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1399:ℚ)^(-2:ℤ) : ℝ) = ((1399:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_222 : ((((28260016697 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1409, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1399 < q → q < 1409 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1409).mp (by decide +kernel))) hgap
  have hprev := s2L_221
  have hrat : ((28260016697 : ℚ) / 62500000000) ≤ ((90431952689 : ℚ) / 200000000000) + (1409:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28260016697 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((90431952689 : ℚ) / 200000000000) : ℚ) : ℝ) + ((1409:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1409:ℚ)^(-2:ℤ) : ℝ) = ((1409:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_223 : ((((113040190249 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1423, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1409 < q → q < 1423 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1423).mp (by decide +kernel))) hgap
  have hprev := s2L_222
  have hrat : ((113040190249 : ℚ) / 250000000000) ≤ ((28260016697 : ℚ) / 62500000000) + (1423:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113040190249 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((28260016697 : ℚ) / 62500000000) : ℚ) : ℝ) + ((1423:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1423:ℚ)^(-2:ℤ) : ℝ) = ((1423:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_224 : ((((18086450083 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1427, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1423 < q → q < 1427 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1427).mp (by decide +kernel))) hgap
  have hprev := s2L_223
  have hrat : ((18086450083 : ℚ) / 40000000000) ≤ ((113040190249 : ℚ) / 250000000000) + (1427:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18086450083 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((113040190249 : ℚ) / 250000000000) : ℚ) : ℝ) + ((1427:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1427:ℚ)^(-2:ℤ) : ℝ) = ((1427:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_225 : ((((452161741781 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1429, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1427 < q → q < 1429 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1429).mp (by decide +kernel))) hgap
  have hprev := s2L_224
  have hrat : ((452161741781 : ℚ) / 1000000000000) ≤ ((18086450083 : ℚ) / 40000000000) + (1429:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452161741781 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((18086450083 : ℚ) / 40000000000) : ℚ) : ℝ) + ((1429:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1429:ℚ)^(-2:ℤ) : ℝ) = ((1429:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_226 : ((((452162228757 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1433, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1429 < q → q < 1433 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1433).mp (by decide +kernel))) hgap
  have hprev := s2L_225
  have hrat : ((452162228757 : ℚ) / 1000000000000) ≤ ((452161741781 : ℚ) / 1000000000000) + (1433:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452162228757 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452161741781 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((1433:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1433:ℚ)^(-2:ℤ) : ℝ) = ((1433:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_227 : ((((706504237 : ℚ) / 1562500000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1439, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1433 < q → q < 1439 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1439).mp (by decide +kernel))) hgap
  have hprev := s2L_226
  have hrat : ((706504237 : ℚ) / 1562500000) ≤ ((452162228757 : ℚ) / 1000000000000) + (1439:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((706504237 : ℚ) / 1562500000) : ℚ) : ℝ) ≤ ((((452162228757 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((1439:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1439:ℚ)^(-2:ℤ) : ℝ) = ((1439:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_228 : ((((226081594639 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1447, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1439 < q → q < 1447 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1447).mp (by decide +kernel))) hgap
  have hprev := s2L_227
  have hrat : ((226081594639 : ℚ) / 500000000000) ≤ ((706504237 : ℚ) / 1562500000) + (1447:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226081594639 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((706504237 : ℚ) / 1562500000) : ℚ) : ℝ) + ((1447:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1447:ℚ)^(-2:ℤ) : ℝ) = ((1447:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_229 : ((((226081832123 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1451, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1447 < q → q < 1451 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1451).mp (by decide +kernel))) hgap
  have hprev := s2L_228
  have hrat : ((226081832123 : ℚ) / 500000000000) ≤ ((226081594639 : ℚ) / 500000000000) + (1451:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226081832123 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226081594639 : ℚ) / 500000000000) : ℚ) : ℝ) + ((1451:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1451:ℚ)^(-2:ℤ) : ℝ) = ((1451:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_230 : ((((113041034477 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1453, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1451 < q → q < 1453 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1453).mp (by decide +kernel))) hgap
  have hprev := s2L_229
  have hrat : ((113041034477 : ℚ) / 250000000000) ≤ ((226081832123 : ℚ) / 500000000000) + (1453:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113041034477 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226081832123 : ℚ) / 500000000000) : ℚ) : ℝ) + ((1453:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1453:ℚ)^(-2:ℤ) : ℝ) = ((1453:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_231 : ((((226082303841 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1459, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1453 < q → q < 1459 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1459).mp (by decide +kernel))) hgap
  have hprev := s2L_230
  have hrat : ((226082303841 : ℚ) / 500000000000) ≤ ((113041034477 : ℚ) / 250000000000) + (1459:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226082303841 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113041034477 : ℚ) / 250000000000) : ℚ) : ℝ) + ((1459:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1459:ℚ)^(-2:ℤ) : ℝ) = ((1459:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_232 : ((((452165069823 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1471, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1459 < q → q < 1471 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1471).mp (by decide +kernel))) hgap
  have hprev := s2L_231
  have hrat : ((452165069823 : ℚ) / 1000000000000) ≤ ((226082303841 : ℚ) / 500000000000) + (1471:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452165069823 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226082303841 : ℚ) / 500000000000) : ℚ) : ℝ) + ((1471:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1471:ℚ)^(-2:ℤ) : ℝ) = ((1471:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_233 : ((((28260345359 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1481, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1471 < q → q < 1481 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1481).mp (by decide +kernel))) hgap
  have hprev := s2L_232
  have hrat : ((28260345359 : ℚ) / 62500000000) ≤ ((452165069823 : ℚ) / 1000000000000) + (1481:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28260345359 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((452165069823 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((1481:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1481:ℚ)^(-2:ℤ) : ℝ) = ((1481:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_234 : ((((113041495109 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1483, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1481 < q → q < 1483 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1483).mp (by decide +kernel))) hgap
  have hprev := s2L_233
  have hrat : ((113041495109 : ℚ) / 250000000000) ≤ ((28260345359 : ℚ) / 62500000000) + (1483:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113041495109 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((28260345359 : ℚ) / 62500000000) : ℚ) : ℝ) + ((1483:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1483:ℚ)^(-2:ℤ) : ℝ) = ((1483:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_235 : ((((90433286537 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1487, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1483 < q → q < 1487 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1487).mp (by decide +kernel))) hgap
  have hprev := s2L_234
  have hrat : ((90433286537 : ℚ) / 200000000000) ≤ ((113041495109 : ℚ) / 250000000000) + (1487:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90433286537 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((113041495109 : ℚ) / 250000000000) : ℚ) : ℝ) + ((1487:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1487:ℚ)^(-2:ℤ) : ℝ) = ((1487:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_236 : ((((11304172093 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1489, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1487 < q → q < 1489 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1489).mp (by decide +kernel))) hgap
  have hprev := s2L_235
  have hrat : ((11304172093 : ℚ) / 25000000000) ≤ ((90433286537 : ℚ) / 200000000000) + (1489:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((11304172093 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((90433286537 : ℚ) / 200000000000) : ℚ) : ℝ) + ((1489:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1489:ℚ)^(-2:ℤ) : ℝ) = ((1489:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_237 : ((((452167332341 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1493, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1489 < q → q < 1493 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1493).mp (by decide +kernel))) hgap
  have hprev := s2L_236
  have hrat : ((452167332341 : ℚ) / 1000000000000) ≤ ((11304172093 : ℚ) / 25000000000) + (1493:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452167332341 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((11304172093 : ℚ) / 25000000000) : ℚ) : ℝ) + ((1493:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1493:ℚ)^(-2:ℤ) : ℝ) = ((1493:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_238 : ((((226083888689 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1499, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1493 < q → q < 1499 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1499).mp (by decide +kernel))) hgap
  have hprev := s2L_237
  have hrat : ((226083888689 : ℚ) / 500000000000) ≤ ((452167332341 : ℚ) / 1000000000000) + (1499:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226083888689 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452167332341 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((1499:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1499:ℚ)^(-2:ℤ) : ℝ) = ((1499:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_239 : ((((226084107687 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1511, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1499 < q → q < 1511 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1511).mp (by decide +kernel))) hgap
  have hprev := s2L_238
  have hrat : ((226084107687 : ℚ) / 500000000000) ≤ ((226083888689 : ℚ) / 500000000000) + (1511:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226084107687 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226083888689 : ℚ) / 500000000000) : ℚ) : ℝ) + ((1511:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1511:ℚ)^(-2:ℤ) : ℝ) = ((1511:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_240 : ((((14130270203 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1523, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1511 < q → q < 1523 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1523).mp (by decide +kernel))) hgap
  have hprev := s2L_239
  have hrat : ((14130270203 : ℚ) / 31250000000) ≤ ((226084107687 : ℚ) / 500000000000) + (1523:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((14130270203 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((226084107687 : ℚ) / 500000000000) : ℚ) : ℝ) + ((1523:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1523:ℚ)^(-2:ℤ) : ℝ) = ((1523:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_241 : ((((113042268281 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1531, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1523 < q → q < 1531 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1531).mp (by decide +kernel))) hgap
  have hprev := s2L_240
  have hrat : ((113042268281 : ℚ) / 250000000000) ≤ ((14130270203 : ℚ) / 31250000000) + (1531:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113042268281 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((14130270203 : ℚ) / 31250000000) : ℚ) : ℝ) + ((1531:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1531:ℚ)^(-2:ℤ) : ℝ) = ((1531:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_242 : ((((226084746571 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1543, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1531 < q → q < 1543 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1543).mp (by decide +kernel))) hgap
  have hprev := s2L_241
  have hrat : ((226084746571 : ℚ) / 500000000000) ≤ ((113042268281 : ℚ) / 250000000000) + (1543:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226084746571 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113042268281 : ℚ) / 250000000000) : ℚ) : ℝ) + ((1543:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1543:ℚ)^(-2:ℤ) : ℝ) = ((1543:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_243 : ((((56521238739 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1549, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1543 < q → q < 1549 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1549).mp (by decide +kernel))) hgap
  have hprev := s2L_242
  have hrat : ((56521238739 : ℚ) / 125000000000) ≤ ((226084746571 : ℚ) / 500000000000) + (1549:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56521238739 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((226084746571 : ℚ) / 500000000000) : ℚ) : ℝ) + ((1549:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1549:ℚ)^(-2:ℤ) : ℝ) = ((1549:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_244 : ((((226085162269 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1553, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1549 < q → q < 1553 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1553).mp (by decide +kernel))) hgap
  have hprev := s2L_243
  have hrat : ((226085162269 : ℚ) / 500000000000) ≤ ((56521238739 : ℚ) / 125000000000) + (1553:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226085162269 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((56521238739 : ℚ) / 125000000000) : ℚ) : ℝ) + ((1553:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1553:ℚ)^(-2:ℤ) : ℝ) = ((1553:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_245 : ((((452170735979 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1559, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1553 < q → q < 1559 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1559).mp (by decide +kernel))) hgap
  have hprev := s2L_244
  have hrat : ((452170735979 : ℚ) / 1000000000000) ≤ ((226085162269 : ℚ) / 500000000000) + (1559:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452170735979 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226085162269 : ℚ) / 500000000000) : ℚ) : ℝ) + ((1559:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1559:ℚ)^(-2:ℤ) : ℝ) = ((1559:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_246 : ((((452171143229 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1567, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1559 < q → q < 1567 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1567).mp (by decide +kernel))) hgap
  have hprev := s2L_245
  have hrat : ((452171143229 : ℚ) / 1000000000000) ≤ ((452170735979 : ℚ) / 1000000000000) + (1567:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452171143229 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452170735979 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((1567:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1567:ℚ)^(-2:ℤ) : ℝ) = ((1567:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_247 : ((((56521443551 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1571, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1567 < q → q < 1571 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1571).mp (by decide +kernel))) hgap
  have hprev := s2L_246
  have hrat : ((56521443551 : ℚ) / 125000000000) ≤ ((452171143229 : ℚ) / 1000000000000) + (1571:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56521443551 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452171143229 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((1571:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1571:ℚ)^(-2:ℤ) : ℝ) = ((1571:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_248 : ((((113042987373 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1579, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1571 < q → q < 1579 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1579).mp (by decide +kernel))) hgap
  have hprev := s2L_247
  have hrat : ((113042987373 : ℚ) / 250000000000) ≤ ((56521443551 : ℚ) / 125000000000) + (1579:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113042987373 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((56521443551 : ℚ) / 125000000000) : ℚ) : ℝ) + ((1579:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1579:ℚ)^(-2:ℤ) : ℝ) = ((1579:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_249 : ((((452172348551 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1583, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1579 < q → q < 1583 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1583).mp (by decide +kernel))) hgap
  have hprev := s2L_248
  have hrat : ((452172348551 : ℚ) / 1000000000000) ≤ ((113042987373 : ℚ) / 250000000000) + (1583:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452172348551 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113042987373 : ℚ) / 250000000000) : ℚ) : ℝ) + ((1583:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1583:ℚ)^(-2:ℤ) : ℝ) = ((1583:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_250 : ((((113043185161 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1597, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1583 < q → q < 1597 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1597).mp (by decide +kernel))) hgap
  have hprev := s2L_249
  have hrat : ((113043185161 : ℚ) / 250000000000) ≤ ((452172348551 : ℚ) / 1000000000000) + (1597:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113043185161 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452172348551 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((1597:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1597:ℚ)^(-2:ℤ) : ℝ) = ((1597:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_251 : ((((452173130781 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1601, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1597 < q → q < 1601 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1601).mp (by decide +kernel))) hgap
  have hprev := s2L_250
  have hrat : ((452173130781 : ℚ) / 1000000000000) ≤ ((113043185161 : ℚ) / 250000000000) + (1601:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452173130781 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113043185161 : ℚ) / 250000000000) : ℚ) : ℝ) + ((1601:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1601:ℚ)^(-2:ℤ) : ℝ) = ((1601:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_252 : ((((45217351801 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1607, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1601 < q → q < 1607 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1607).mp (by decide +kernel))) hgap
  have hprev := s2L_251
  have hrat : ((45217351801 : ℚ) / 100000000000) ≤ ((452173130781 : ℚ) / 1000000000000) + (1607:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45217351801 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((452173130781 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((1607:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1607:ℚ)^(-2:ℤ) : ℝ) = ((1607:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_253 : ((((452173904277 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1609, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1607 < q → q < 1609 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1609).mp (by decide +kernel))) hgap
  have hprev := s2L_252
  have hrat : ((452173904277 : ℚ) / 1000000000000) ≤ ((45217351801 : ℚ) / 100000000000) + (1609:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452173904277 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((45217351801 : ℚ) / 100000000000) : ℚ) : ℝ) + ((1609:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1609:ℚ)^(-2:ℤ) : ℝ) = ((1609:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_254 : ((((45217428863 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1613, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1609 < q → q < 1613 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1613).mp (by decide +kernel))) hgap
  have hprev := s2L_253
  have hrat : ((45217428863 : ℚ) / 100000000000) ≤ ((452173904277 : ℚ) / 1000000000000) + (1613:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45217428863 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((452173904277 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((1613:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1613:ℚ)^(-2:ℤ) : ℝ) = ((1613:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_255 : ((((22608733507 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1619, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1613 < q → q < 1619 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1619).mp (by decide +kernel))) hgap
  have hprev := s2L_254
  have hrat : ((22608733507 : ℚ) / 50000000000) ≤ ((45217428863 : ℚ) / 100000000000) + (1619:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22608733507 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((45217428863 : ℚ) / 100000000000) : ℚ) : ℝ) + ((1619:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1619:ℚ)^(-2:ℤ) : ℝ) = ((1619:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_256 : ((((452175050709 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1621, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1619 < q → q < 1621 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1621).mp (by decide +kernel))) hgap
  have hprev := s2L_255
  have hrat : ((452175050709 : ℚ) / 1000000000000) ≤ ((22608733507 : ℚ) / 50000000000) + (1621:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452175050709 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((22608733507 : ℚ) / 50000000000) : ℚ) : ℝ) + ((1621:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1621:ℚ)^(-2:ℤ) : ℝ) = ((1621:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_257 : ((((113043857119 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1627, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1621 < q → q < 1627 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1627).mp (by decide +kernel))) hgap
  have hprev := s2L_256
  have hrat : ((113043857119 : ℚ) / 250000000000) ≤ ((452175050709 : ℚ) / 1000000000000) + (1627:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113043857119 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452175050709 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((1627:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1627:ℚ)^(-2:ℤ) : ℝ) = ((1627:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_258 : ((((226087900821 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1637, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1627 < q → q < 1637 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1637).mp (by decide +kernel))) hgap
  have hprev := s2L_257
  have hrat : ((226087900821 : ℚ) / 500000000000) ≤ ((113043857119 : ℚ) / 250000000000) + (1637:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226087900821 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113043857119 : ℚ) / 250000000000) : ℚ) : ℝ) + ((1637:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1637:ℚ)^(-2:ℤ) : ℝ) = ((1637:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_259 : ((((226088082927 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1657, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1637 < q → q < 1657 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1657).mp (by decide +kernel))) hgap
  have hprev := s2L_258
  have hrat : ((226088082927 : ℚ) / 500000000000) ≤ ((226087900821 : ℚ) / 500000000000) + (1657:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226088082927 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226087900821 : ℚ) / 500000000000) : ℚ) : ℝ) + ((1657:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1657:ℚ)^(-2:ℤ) : ℝ) = ((1657:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_260 : ((((452176527443 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1663, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1657 < q → q < 1663 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1663).mp (by decide +kernel))) hgap
  have hprev := s2L_259
  have hrat : ((452176527443 : ℚ) / 1000000000000) ≤ ((226088082927 : ℚ) / 500000000000) + (1663:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452176527443 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226088082927 : ℚ) / 500000000000) : ℚ) : ℝ) + ((1663:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1663:ℚ)^(-2:ℤ) : ℝ) = ((1663:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_261 : ((((452176887299 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1667, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1663 < q → q < 1667 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1667).mp (by decide +kernel))) hgap
  have hprev := s2L_260
  have hrat : ((452176887299 : ℚ) / 1000000000000) ≤ ((452176527443 : ℚ) / 1000000000000) + (1667:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452176887299 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452176527443 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((1667:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1667:ℚ)^(-2:ℤ) : ℝ) = ((1667:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_262 : ((((452177246293 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1669, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1667 < q → q < 1669 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1669).mp (by decide +kernel))) hgap
  have hprev := s2L_261
  have hrat : ((452177246293 : ℚ) / 1000000000000) ≤ ((452176887299 : ℚ) / 1000000000000) + (1669:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452177246293 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452176887299 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((1669:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1669:ℚ)^(-2:ℤ) : ℝ) = ((1669:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_263 : ((((452177595181 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1693, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1669 < q → q < 1693 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1693).mp (by decide +kernel))) hgap
  have hprev := s2L_262
  have hrat : ((452177595181 : ℚ) / 1000000000000) ≤ ((452177246293 : ℚ) / 1000000000000) + (1693:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452177595181 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452177246293 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((1693:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1693:ℚ)^(-2:ℤ) : ℝ) = ((1693:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_264 : ((((226088971213 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1697, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1693 < q → q < 1697 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1697).mp (by decide +kernel))) hgap
  have hprev := s2L_263
  have hrat : ((226088971213 : ℚ) / 500000000000) ≤ ((452177595181 : ℚ) / 1000000000000) + (1697:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226088971213 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452177595181 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((1697:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1697:ℚ)^(-2:ℤ) : ℝ) = ((1697:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_265 : ((((226089144427 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1699, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1697 < q → q < 1699 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1699).mp (by decide +kernel))) hgap
  have hprev := s2L_264
  have hrat : ((226089144427 : ℚ) / 500000000000) ≤ ((226088971213 : ℚ) / 500000000000) + (1699:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226089144427 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226088971213 : ℚ) / 500000000000) : ℚ) : ℝ) + ((1699:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1699:ℚ)^(-2:ℤ) : ℝ) = ((1699:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_266 : ((((452178631239 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1709, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1699 < q → q < 1709 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1709).mp (by decide +kernel))) hgap
  have hprev := s2L_265
  have hrat : ((452178631239 : ℚ) / 1000000000000) ≤ ((226089144427 : ℚ) / 500000000000) + (1709:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452178631239 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226089144427 : ℚ) / 500000000000) : ℚ) : ℝ) + ((1709:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1709:ℚ)^(-2:ℤ) : ℝ) = ((1709:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_267 : ((((226089484433 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1721, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1709 < q → q < 1721 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1721).mp (by decide +kernel))) hgap
  have hprev := s2L_266
  have hrat : ((226089484433 : ℚ) / 500000000000) ≤ ((452178631239 : ℚ) / 1000000000000) + (1721:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226089484433 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452178631239 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((1721:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1721:ℚ)^(-2:ℤ) : ℝ) = ((1721:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_268 : ((((45217930571 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1723, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1721 < q → q < 1723 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1723).mp (by decide +kernel))) hgap
  have hprev := s2L_267
  have hrat : ((45217930571 : ℚ) / 100000000000) ≤ ((226089484433 : ℚ) / 500000000000) + (1723:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45217930571 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((226089484433 : ℚ) / 500000000000) : ℚ) : ℝ) + ((1723:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1723:ℚ)^(-2:ℤ) : ℝ) = ((1723:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_269 : ((((226089819339 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1733, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1723 < q → q < 1733 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1733).mp (by decide +kernel))) hgap
  have hprev := s2L_268
  have hrat : ((226089819339 : ℚ) / 500000000000) ≤ ((45217930571 : ℚ) / 100000000000) + (1733:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226089819339 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((45217930571 : ℚ) / 100000000000) : ℚ) : ℝ) + ((1733:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1733:ℚ)^(-2:ℤ) : ℝ) = ((1733:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_270 : ((((452179968593 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1741, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1733 < q → q < 1741 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1741).mp (by decide +kernel))) hgap
  have hprev := s2L_269
  have hrat : ((452179968593 : ℚ) / 1000000000000) ≤ ((226089819339 : ℚ) / 500000000000) + (1741:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452179968593 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226089819339 : ℚ) / 500000000000) : ℚ) : ℝ) + ((1741:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1741:ℚ)^(-2:ℤ) : ℝ) = ((1741:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_271 : ((((226090148123 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1747, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1741 < q → q < 1747 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1747).mp (by decide +kernel))) hgap
  have hprev := s2L_270
  have hrat : ((226090148123 : ℚ) / 500000000000) ≤ ((452179968593 : ℚ) / 1000000000000) + (1747:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226090148123 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452179968593 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((1747:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1747:ℚ)^(-2:ℤ) : ℝ) = ((1747:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_272 : ((((452180621659 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1753, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1747 < q → q < 1753 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1753).mp (by decide +kernel))) hgap
  have hprev := s2L_271
  have hrat : ((452180621659 : ℚ) / 1000000000000) ≤ ((226090148123 : ℚ) / 500000000000) + (1753:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452180621659 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226090148123 : ℚ) / 500000000000) : ℚ) : ℝ) + ((1753:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1753:ℚ)^(-2:ℤ) : ℝ) = ((1753:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_273 : ((((56522618107 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1759, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1753 < q → q < 1759 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1759).mp (by decide +kernel))) hgap
  have hprev := s2L_272
  have hrat : ((56522618107 : ℚ) / 125000000000) ≤ ((452180621659 : ℚ) / 1000000000000) + (1759:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56522618107 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452180621659 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((1759:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1759:ℚ)^(-2:ℤ) : ℝ) = ((1759:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_274 : ((((452181261539 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1777, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1759 < q → q < 1777 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1777).mp (by decide +kernel))) hgap
  have hprev := s2L_273
  have hrat : ((452181261539 : ℚ) / 1000000000000) ≤ ((56522618107 : ℚ) / 125000000000) + (1777:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452181261539 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56522618107 : ℚ) / 125000000000) : ℚ) : ℝ) + ((1777:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1777:ℚ)^(-2:ℤ) : ℝ) = ((1777:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_275 : ((((226090788047 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1783, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1777 < q → q < 1783 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1783).mp (by decide +kernel))) hgap
  have hprev := s2L_274
  have hrat : ((226090788047 : ℚ) / 500000000000) ≤ ((452181261539 : ℚ) / 1000000000000) + (1783:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226090788047 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452181261539 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((1783:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1783:ℚ)^(-2:ℤ) : ℝ) = ((1783:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_276 : ((((226090944621 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1787, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1783 < q → q < 1787 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1787).mp (by decide +kernel))) hgap
  have hprev := s2L_275
  have hrat : ((226090944621 : ℚ) / 500000000000) ≤ ((226090788047 : ℚ) / 500000000000) + (1787:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226090944621 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226090788047 : ℚ) / 500000000000) : ℚ) : ℝ) + ((1787:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1787:ℚ)^(-2:ℤ) : ℝ) = ((1787:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_277 : ((((452182201691 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1789, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1787 < q → q < 1789 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1789).mp (by decide +kernel))) hgap
  have hprev := s2L_276
  have hrat : ((452182201691 : ℚ) / 1000000000000) ≤ ((226090944621 : ℚ) / 500000000000) + (1789:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452182201691 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226090944621 : ℚ) / 500000000000) : ℚ) : ℝ) + ((1789:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1789:ℚ)^(-2:ℤ) : ℝ) = ((1789:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_278 : ((((45218250999 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1801, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1789 < q → q < 1801 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1801).mp (by decide +kernel))) hgap
  have hprev := s2L_277
  have hrat : ((45218250999 : ℚ) / 100000000000) ≤ ((452182201691 : ℚ) / 1000000000000) + (1801:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45218250999 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((452182201691 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((1801:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1801:ℚ)^(-2:ℤ) : ℝ) = ((1801:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_279 : ((((452182814893 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1811, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1801 < q → q < 1811 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1811).mp (by decide +kernel))) hgap
  have hprev := s2L_278
  have hrat : ((452182814893 : ℚ) / 1000000000000) ≤ ((45218250999 : ℚ) / 100000000000) + (1811:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452182814893 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((45218250999 : ℚ) / 100000000000) : ℚ) : ℝ) + ((1811:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1811:ℚ)^(-2:ℤ) : ℝ) = ((1811:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_280 : ((((113045778949 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1823, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1811 < q → q < 1823 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1823).mp (by decide +kernel))) hgap
  have hprev := s2L_279
  have hrat : ((113045778949 : ℚ) / 250000000000) ≤ ((452182814893 : ℚ) / 1000000000000) + (1823:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113045778949 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452182814893 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((1823:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1823:ℚ)^(-2:ℤ) : ℝ) = ((1823:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_281 : ((((18087336563 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1831, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1823 < q → q < 1831 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1831).mp (by decide +kernel))) hgap
  have hprev := s2L_280
  have hrat : ((18087336563 : ℚ) / 40000000000) ≤ ((113045778949 : ℚ) / 250000000000) + (1831:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18087336563 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((113045778949 : ℚ) / 250000000000) : ℚ) : ℝ) + ((1831:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1831:ℚ)^(-2:ℤ) : ℝ) = ((1831:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_282 : ((((452183707209 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1847, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1831 < q → q < 1847 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1847).mp (by decide +kernel))) hgap
  have hprev := s2L_281
  have hrat : ((452183707209 : ℚ) / 1000000000000) ≤ ((18087336563 : ℚ) / 40000000000) + (1847:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452183707209 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((18087336563 : ℚ) / 40000000000) : ℚ) : ℝ) + ((1847:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1847:ℚ)^(-2:ℤ) : ℝ) = ((1847:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_283 : ((((452183995949 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1861, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1847 < q → q < 1861 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1861).mp (by decide +kernel))) hgap
  have hprev := s2L_282
  have hrat : ((452183995949 : ℚ) / 1000000000000) ≤ ((452183707209 : ℚ) / 1000000000000) + (1861:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452183995949 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452183707209 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((1861:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1861:ℚ)^(-2:ℤ) : ℝ) = ((1861:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_284 : ((((113046070709 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1867, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1861 < q → q < 1867 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1867).mp (by decide +kernel))) hgap
  have hprev := s2L_283
  have hrat : ((113046070709 : ℚ) / 250000000000) ≤ ((452183995949 : ℚ) / 1000000000000) + (1867:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113046070709 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452183995949 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((1867:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1867:ℚ)^(-2:ℤ) : ℝ) = ((1867:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_285 : ((((452184568497 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1871, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1867 < q → q < 1871 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1871).mp (by decide +kernel))) hgap
  have hprev := s2L_284
  have hrat : ((452184568497 : ℚ) / 1000000000000) ≤ ((113046070709 : ℚ) / 250000000000) + (1871:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452184568497 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113046070709 : ℚ) / 250000000000) : ℚ) : ℝ) + ((1871:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1871:ℚ)^(-2:ℤ) : ℝ) = ((1871:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_286 : ((((452184853549 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1873, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1871 < q → q < 1873 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1873).mp (by decide +kernel))) hgap
  have hprev := s2L_285
  have hrat : ((452184853549 : ℚ) / 1000000000000) ≤ ((452184568497 : ℚ) / 1000000000000) + (1873:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452184853549 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452184568497 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((1873:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1873:ℚ)^(-2:ℤ) : ℝ) = ((1873:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_287 : ((((452185137387 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1877, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1873 < q → q < 1877 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1877).mp (by decide +kernel))) hgap
  have hprev := s2L_286
  have hrat : ((452185137387 : ℚ) / 1000000000000) ≤ ((452184853549 : ℚ) / 1000000000000) + (1877:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452185137387 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452184853549 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((1877:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1877:ℚ)^(-2:ℤ) : ℝ) = ((1877:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_288 : ((((452185420621 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1879, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1877 < q → q < 1879 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1879).mp (by decide +kernel))) hgap
  have hprev := s2L_287
  have hrat : ((452185420621 : ℚ) / 1000000000000) ≤ ((452185137387 : ℚ) / 1000000000000) + (1879:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452185420621 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452185137387 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((1879:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1879:ℚ)^(-2:ℤ) : ℝ) = ((1879:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_289 : ((((883175197 : ℚ) / 1953125000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1889, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1879 < q → q < 1889 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1889).mp (by decide +kernel))) hgap
  have hprev := s2L_288
  have hrat : ((883175197 : ℚ) / 1953125000) ≤ ((452185420621 : ℚ) / 1000000000000) + (1889:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((883175197 : ℚ) / 1953125000) : ℚ) : ℝ) ≤ ((((452185420621 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((1889:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1889:ℚ)^(-2:ℤ) : ℝ) = ((1889:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_290 : ((((22609298879 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1901, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1889 < q → q < 1901 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1901).mp (by decide +kernel))) hgap
  have hprev := s2L_289
  have hrat : ((22609298879 : ℚ) / 50000000000) ≤ ((883175197 : ℚ) / 1953125000) + (1901:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22609298879 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((883175197 : ℚ) / 1953125000) : ℚ) : ℝ) + ((1901:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1901:ℚ)^(-2:ℤ) : ℝ) = ((1901:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_291 : ((((226093126279 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1907, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1901 < q → q < 1907 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1907).mp (by decide +kernel))) hgap
  have hprev := s2L_290
  have hrat : ((226093126279 : ℚ) / 500000000000) ≤ ((22609298879 : ℚ) / 50000000000) + (1907:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226093126279 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((22609298879 : ℚ) / 50000000000) : ℚ) : ℝ) + ((1907:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1907:ℚ)^(-2:ℤ) : ℝ) = ((1907:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_292 : ((((226093262907 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1913, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1907 < q → q < 1913 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1913).mp (by decide +kernel))) hgap
  have hprev := s2L_291
  have hrat : ((226093262907 : ℚ) / 500000000000) ≤ ((226093126279 : ℚ) / 500000000000) + (1913:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226093262907 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226093126279 : ℚ) / 500000000000) : ℚ) : ℝ) + ((1913:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1913:ℚ)^(-2:ℤ) : ℝ) = ((1913:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_293 : ((((452186793999 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1931, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1913 < q → q < 1931 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1931).mp (by decide +kernel))) hgap
  have hprev := s2L_292
  have hrat : ((452186793999 : ℚ) / 1000000000000) ≤ ((226093262907 : ℚ) / 500000000000) + (1931:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452186793999 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226093262907 : ℚ) / 500000000000) : ℚ) : ℝ) + ((1931:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1931:ℚ)^(-2:ℤ) : ℝ) = ((1931:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_294 : ((((452187061629 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1933, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1931 < q → q < 1933 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1933).mp (by decide +kernel))) hgap
  have hprev := s2L_293
  have hrat : ((452187061629 : ℚ) / 1000000000000) ≤ ((452186793999 : ℚ) / 1000000000000) + (1933:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452187061629 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452186793999 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((1933:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1933:ℚ)^(-2:ℤ) : ℝ) = ((1933:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_295 : ((((452187324883 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1949, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1933 < q → q < 1949 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1949).mp (by decide +kernel))) hgap
  have hprev := s2L_294
  have hrat : ((452187324883 : ℚ) / 1000000000000) ≤ ((452187061629 : ℚ) / 1000000000000) + (1949:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452187324883 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452187061629 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((1949:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1949:ℚ)^(-2:ℤ) : ℝ) = ((1949:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_296 : ((((226093793799 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1951, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1949 < q → q < 1951 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1951).mp (by decide +kernel))) hgap
  have hprev := s2L_295
  have hrat : ((226093793799 : ℚ) / 500000000000) ≤ ((452187324883 : ℚ) / 1000000000000) + (1951:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226093793799 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452187324883 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((1951:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1951:ℚ)^(-2:ℤ) : ℝ) = ((1951:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_297 : ((((452187844487 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1973, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1951 < q → q < 1973 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1973).mp (by decide +kernel))) hgap
  have hprev := s2L_296
  have hrat : ((452187844487 : ℚ) / 1000000000000) ≤ ((226093793799 : ℚ) / 500000000000) + (1973:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452187844487 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226093793799 : ℚ) / 500000000000) : ℚ) : ℝ) + ((1973:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1973:ℚ)^(-2:ℤ) : ℝ) = ((1973:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_298 : ((((22609404991 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1979, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1973 < q → q < 1979 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1979).mp (by decide +kernel))) hgap
  have hprev := s2L_297
  have hrat : ((22609404991 : ℚ) / 50000000000) ≤ ((452187844487 : ℚ) / 1000000000000) + (1979:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22609404991 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((452187844487 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((1979:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1979:ℚ)^(-2:ℤ) : ℝ) = ((1979:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_299 : ((((452188353101 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1987, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1979 < q → q < 1987 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1987).mp (by decide +kernel))) hgap
  have hprev := s2L_298
  have hrat : ((452188353101 : ℚ) / 1000000000000) ≤ ((22609404991 : ℚ) / 50000000000) + (1987:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452188353101 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((22609404991 : ℚ) / 50000000000) : ℚ) : ℝ) + ((1987:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1987:ℚ)^(-2:ℤ) : ℝ) = ((1987:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_300 : ((((22609430243 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1993, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1987 < q → q < 1993 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1993).mp (by decide +kernel))) hgap
  have hprev := s2L_299
  have hrat : ((22609430243 : ℚ) / 50000000000) ≤ ((452188353101 : ℚ) / 1000000000000) + (1993:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22609430243 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((452188353101 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((1993:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1993:ℚ)^(-2:ℤ) : ℝ) = ((1993:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_301 : ((((452188855611 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1997, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1993 < q → q < 1997 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1997).mp (by decide +kernel))) hgap
  have hprev := s2L_300
  have hrat : ((452188855611 : ℚ) / 1000000000000) ≤ ((22609430243 : ℚ) / 50000000000) + (1997:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452188855611 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((22609430243 : ℚ) / 50000000000) : ℚ) : ℝ) + ((1997:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1997:ℚ)^(-2:ℤ) : ℝ) = ((1997:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_302 : ((((452189105861 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 1999, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1997 < q → q < 1999 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 1999).mp (by decide +kernel))) hgap
  have hprev := s2L_301
  have hrat : ((452189105861 : ℚ) / 1000000000000) ≤ ((452188855611 : ℚ) / 1000000000000) + (1999:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452189105861 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452188855611 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((1999:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((1999:ℚ)^(-2:ℤ) : ℝ) = ((1999:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_303 : ((((56523669389 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2003, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 1999 < q → q < 2003 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2003).mp (by decide +kernel))) hgap
  have hprev := s2L_302
  have hrat : ((56523669389 : ℚ) / 125000000000) ≤ ((452189105861 : ℚ) / 1000000000000) + (2003:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56523669389 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452189105861 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((2003:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2003:ℚ)^(-2:ℤ) : ℝ) = ((2003:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_304 : ((((28261850149 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2011, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2003 < q → q < 2011 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2011).mp (by decide +kernel))) hgap
  have hprev := s2L_303
  have hrat : ((28261850149 : ℚ) / 62500000000) ≤ ((56523669389 : ℚ) / 125000000000) + (2011:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28261850149 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((56523669389 : ℚ) / 125000000000) : ℚ) : ℝ) + ((2011:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2011:ℚ)^(-2:ℤ) : ℝ) = ((2011:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_305 : ((((452189848187 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2017, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2011 < q → q < 2017 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2017).mp (by decide +kernel))) hgap
  have hprev := s2L_304
  have hrat : ((452189848187 : ℚ) / 1000000000000) ≤ ((28261850149 : ℚ) / 62500000000) + (2017:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452189848187 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((28261850149 : ℚ) / 62500000000) : ℚ) : ℝ) + ((2017:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2017:ℚ)^(-2:ℤ) : ℝ) = ((2017:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_306 : ((((452190091571 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2027, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2017 < q → q < 2027 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2027).mp (by decide +kernel))) hgap
  have hprev := s2L_305
  have hrat : ((452190091571 : ℚ) / 1000000000000) ≤ ((452189848187 : ℚ) / 1000000000000) + (2027:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452190091571 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452189848187 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((2027:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2027:ℚ)^(-2:ℤ) : ℝ) = ((2027:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_307 : ((((18087613379 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2029, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2027 < q → q < 2029 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2029).mp (by decide +kernel))) hgap
  have hprev := s2L_306
  have hrat : ((18087613379 : ℚ) / 40000000000) ≤ ((452190091571 : ℚ) / 1000000000000) + (2029:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18087613379 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((452190091571 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((2029:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2029:ℚ)^(-2:ℤ) : ℝ) = ((2029:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_308 : ((((226095287501 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2039, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2029 < q → q < 2039 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2039).mp (by decide +kernel))) hgap
  have hprev := s2L_307
  have hrat : ((226095287501 : ℚ) / 500000000000) ≤ ((18087613379 : ℚ) / 40000000000) + (2039:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226095287501 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((18087613379 : ℚ) / 40000000000) : ℚ) : ℝ) + ((2039:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2039:ℚ)^(-2:ℤ) : ℝ) = ((2039:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_309 : ((((22609540613 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2053, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2039 < q → q < 2053 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2053).mp (by decide +kernel))) hgap
  have hprev := s2L_308
  have hrat : ((22609540613 : ℚ) / 50000000000) ≤ ((226095287501 : ℚ) / 500000000000) + (2053:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22609540613 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((226095287501 : ℚ) / 500000000000) : ℚ) : ℝ) + ((2053:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2053:ℚ)^(-2:ℤ) : ℝ) = ((2053:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_310 : ((((56523880903 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2063, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2053 < q → q < 2063 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2063).mp (by decide +kernel))) hgap
  have hprev := s2L_309
  have hrat : ((56523880903 : ℚ) / 125000000000) ≤ ((22609540613 : ℚ) / 50000000000) + (2063:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56523880903 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((22609540613 : ℚ) / 50000000000) : ℚ) : ℝ) + ((2063:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2063:ℚ)^(-2:ℤ) : ℝ) = ((2063:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_311 : ((((452191280827 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2069, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2063 < q → q < 2069 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2069).mp (by decide +kernel))) hgap
  have hprev := s2L_310
  have hrat : ((452191280827 : ℚ) / 1000000000000) ≤ ((56523880903 : ℚ) / 125000000000) + (2069:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452191280827 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56523880903 : ℚ) / 125000000000) : ℚ) : ℝ) + ((2069:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2069:ℚ)^(-2:ℤ) : ℝ) = ((2069:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_312 : ((((452191511743 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2081, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2069 < q → q < 2081 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2081).mp (by decide +kernel))) hgap
  have hprev := s2L_311
  have hrat : ((452191511743 : ℚ) / 1000000000000) ≤ ((452191280827 : ℚ) / 1000000000000) + (2081:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452191511743 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452191280827 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((2081:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2081:ℚ)^(-2:ℤ) : ℝ) = ((2081:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_313 : ((((56523967777 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2083, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2081 < q → q < 2083 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2083).mp (by decide +kernel))) hgap
  have hprev := s2L_312
  have hrat : ((56523967777 : ℚ) / 125000000000) ≤ ((452191511743 : ℚ) / 1000000000000) + (2083:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56523967777 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452191511743 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((2083:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2083:ℚ)^(-2:ℤ) : ℝ) = ((2083:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_314 : ((((452191971807 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2087, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2083 < q → q < 2087 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2087).mp (by decide +kernel))) hgap
  have hprev := s2L_313
  have hrat : ((452191971807 : ℚ) / 1000000000000) ≤ ((56523967777 : ℚ) / 125000000000) + (2087:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452191971807 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56523967777 : ℚ) / 125000000000) : ℚ) : ℝ) + ((2087:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2087:ℚ)^(-2:ℤ) : ℝ) = ((2087:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_315 : ((((226096100479 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2089, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2087 < q → q < 2089 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2089).mp (by decide +kernel))) hgap
  have hprev := s2L_314
  have hrat : ((226096100479 : ℚ) / 500000000000) ≤ ((452191971807 : ℚ) / 1000000000000) + (2089:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226096100479 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452191971807 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((2089:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2089:ℚ)^(-2:ℤ) : ℝ) = ((2089:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_316 : ((((452192427931 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2099, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2089 < q → q < 2099 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2099).mp (by decide +kernel))) hgap
  have hprev := s2L_315
  have hrat : ((452192427931 : ℚ) / 1000000000000) ≤ ((226096100479 : ℚ) / 500000000000) + (2099:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452192427931 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226096100479 : ℚ) / 500000000000) : ℚ) : ℝ) + ((2099:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2099:ℚ)^(-2:ℤ) : ℝ) = ((2099:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_317 : ((((452192652331 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2111, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2099 < q → q < 2111 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2111).mp (by decide +kernel))) hgap
  have hprev := s2L_316
  have hrat : ((452192652331 : ℚ) / 1000000000000) ≤ ((452192427931 : ℚ) / 1000000000000) + (2111:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452192652331 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452192427931 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((2111:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2111:ℚ)^(-2:ℤ) : ℝ) = ((2111:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_318 : ((((226096438153 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2113, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2111 < q → q < 2113 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2113).mp (by decide +kernel))) hgap
  have hprev := s2L_317
  have hrat : ((226096438153 : ℚ) / 500000000000) ≤ ((452192652331 : ℚ) / 1000000000000) + (2113:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226096438153 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452192652331 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((2113:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2113:ℚ)^(-2:ℤ) : ℝ) = ((2113:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_319 : ((((452193096927 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2129, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2113 < q → q < 2129 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2129).mp (by decide +kernel))) hgap
  have hprev := s2L_318
  have hrat : ((452193096927 : ℚ) / 1000000000000) ≤ ((226096438153 : ℚ) / 500000000000) + (2129:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452193096927 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226096438153 : ℚ) / 500000000000) : ℚ) : ℝ) + ((2129:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2129:ℚ)^(-2:ℤ) : ℝ) = ((2129:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_320 : ((((90438663427 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2131, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2129 < q → q < 2131 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2131).mp (by decide +kernel))) hgap
  have hprev := s2L_319
  have hrat : ((90438663427 : ℚ) / 200000000000) ≤ ((452193096927 : ℚ) / 1000000000000) + (2131:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90438663427 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452193096927 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((2131:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2131:ℚ)^(-2:ℤ) : ℝ) = ((2131:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_321 : ((((113048384027 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2137, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2131 < q → q < 2137 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2137).mp (by decide +kernel))) hgap
  have hprev := s2L_320
  have hrat : ((113048384027 : ℚ) / 250000000000) ≤ ((90438663427 : ℚ) / 200000000000) + (2137:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113048384027 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((90438663427 : ℚ) / 200000000000) : ℚ) : ℝ) + ((2137:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2137:ℚ)^(-2:ℤ) : ℝ) = ((2137:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_322 : ((((452193754263 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2141, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2137 < q → q < 2141 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2141).mp (by decide +kernel))) hgap
  have hprev := s2L_321
  have hrat : ((452193754263 : ℚ) / 1000000000000) ≤ ((113048384027 : ℚ) / 250000000000) + (2141:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452193754263 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113048384027 : ℚ) / 250000000000) : ℚ) : ℝ) + ((2141:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2141:ℚ)^(-2:ℤ) : ℝ) = ((2141:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_323 : ((((452193972011 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2143, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2141 < q → q < 2143 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2143).mp (by decide +kernel))) hgap
  have hprev := s2L_322
  have hrat : ((452193972011 : ℚ) / 1000000000000) ≤ ((452193754263 : ℚ) / 1000000000000) + (2143:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452193972011 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452193754263 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((2143:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2143:ℚ)^(-2:ℤ) : ℝ) = ((2143:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_324 : ((((452194187741 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2153, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2143 < q → q < 2153 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2153).mp (by decide +kernel))) hgap
  have hprev := s2L_323
  have hrat : ((452194187741 : ℚ) / 1000000000000) ≤ ((452193972011 : ℚ) / 1000000000000) + (2153:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452194187741 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452193972011 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((2153:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2153:ℚ)^(-2:ℤ) : ℝ) = ((2153:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_325 : ((((452194401877 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2161, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2153 < q → q < 2161 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2161).mp (by decide +kernel))) hgap
  have hprev := s2L_324
  have hrat : ((452194401877 : ℚ) / 1000000000000) ≤ ((452194187741 : ℚ) / 1000000000000) + (2161:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452194401877 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452194187741 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((2161:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2161:ℚ)^(-2:ℤ) : ℝ) = ((2161:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_326 : ((((45219461249 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2179, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2161 < q → q < 2179 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2179).mp (by decide +kernel))) hgap
  have hprev := s2L_325
  have hrat : ((45219461249 : ℚ) / 100000000000) ≤ ((452194401877 : ℚ) / 1000000000000) + (2179:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45219461249 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((452194401877 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((2179:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2179:ℚ)^(-2:ℤ) : ℝ) = ((2179:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_327 : ((((452194818539 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2203, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2179 < q → q < 2203 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2203).mp (by decide +kernel))) hgap
  have hprev := s2L_326
  have hrat : ((452194818539 : ℚ) / 1000000000000) ≤ ((45219461249 : ℚ) / 100000000000) + (2203:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452194818539 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((45219461249 : ℚ) / 100000000000) : ℚ) : ℝ) + ((2203:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2203:ℚ)^(-2:ℤ) : ℝ) = ((2203:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_328 : ((((226097511921 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2207, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2203 < q → q < 2207 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2207).mp (by decide +kernel))) hgap
  have hprev := s2L_327
  have hrat : ((226097511921 : ℚ) / 500000000000) ≤ ((452194818539 : ℚ) / 1000000000000) + (2207:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226097511921 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452194818539 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((2207:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2207:ℚ)^(-2:ℤ) : ℝ) = ((2207:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_329 : ((((452195228033 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2213, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2207 < q → q < 2213 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2213).mp (by decide +kernel))) hgap
  have hprev := s2L_328
  have hrat : ((452195228033 : ℚ) / 1000000000000) ≤ ((226097511921 : ℚ) / 500000000000) + (2213:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452195228033 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226097511921 : ℚ) / 500000000000) : ℚ) : ℝ) + ((2213:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2213:ℚ)^(-2:ℤ) : ℝ) = ((2213:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_330 : ((((90439086151 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2221, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2213 < q → q < 2221 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2221).mp (by decide +kernel))) hgap
  have hprev := s2L_329
  have hrat : ((90439086151 : ℚ) / 200000000000) ≤ ((452195228033 : ℚ) / 1000000000000) + (2221:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90439086151 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452195228033 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((2221:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2221:ℚ)^(-2:ℤ) : ℝ) = ((2221:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_331 : ((((113048907647 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2237, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2221 < q → q < 2237 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2237).mp (by decide +kernel))) hgap
  have hprev := s2L_330
  have hrat : ((113048907647 : ℚ) / 250000000000) ≤ ((90439086151 : ℚ) / 200000000000) + (2237:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113048907647 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((90439086151 : ℚ) / 200000000000) : ℚ) : ℝ) + ((2237:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2237:ℚ)^(-2:ℤ) : ℝ) = ((2237:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_332 : ((((28262239379 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2239, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2237 < q → q < 2239 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2239).mp (by decide +kernel))) hgap
  have hprev := s2L_331
  have hrat : ((28262239379 : ℚ) / 62500000000) ≤ ((113048907647 : ℚ) / 250000000000) + (2239:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28262239379 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((113048907647 : ℚ) / 250000000000) : ℚ) : ℝ) + ((2239:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2239:ℚ)^(-2:ℤ) : ℝ) = ((2239:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_333 : ((((452196028829 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2243, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2239 < q → q < 2243 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2243).mp (by decide +kernel))) hgap
  have hprev := s2L_332
  have hrat : ((452196028829 : ℚ) / 1000000000000) ≤ ((28262239379 : ℚ) / 62500000000) + (2243:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452196028829 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((28262239379 : ℚ) / 62500000000) : ℚ) : ℝ) + ((2243:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2243:ℚ)^(-2:ℤ) : ℝ) = ((2243:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_334 : ((((56524528273 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2251, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2243 < q → q < 2251 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2251).mp (by decide +kernel))) hgap
  have hprev := s2L_333
  have hrat : ((56524528273 : ℚ) / 125000000000) ≤ ((452196028829 : ℚ) / 1000000000000) + (2251:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56524528273 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452196028829 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((2251:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2251:ℚ)^(-2:ℤ) : ℝ) = ((2251:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_335 : ((((452196420763 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2267, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2251 < q → q < 2267 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2267).mp (by decide +kernel))) hgap
  have hprev := s2L_334
  have hrat : ((452196420763 : ℚ) / 1000000000000) ≤ ((56524528273 : ℚ) / 125000000000) + (2267:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452196420763 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56524528273 : ℚ) / 125000000000) : ℚ) : ℝ) + ((2267:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2267:ℚ)^(-2:ℤ) : ℝ) = ((2267:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_336 : ((((452196614999 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2269, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2267 < q → q < 2269 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2269).mp (by decide +kernel))) hgap
  have hprev := s2L_335
  have hrat : ((452196614999 : ℚ) / 1000000000000) ≤ ((452196420763 : ℚ) / 1000000000000) + (2269:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452196614999 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452196420763 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((2269:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2269:ℚ)^(-2:ℤ) : ℝ) = ((2269:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_337 : ((((56524601069 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2273, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2269 < q → q < 2273 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2273).mp (by decide +kernel))) hgap
  have hprev := s2L_336
  have hrat : ((56524601069 : ℚ) / 125000000000) ≤ ((452196614999 : ℚ) / 1000000000000) + (2273:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56524601069 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452196614999 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((2273:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2273:ℚ)^(-2:ℤ) : ℝ) = ((2273:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_338 : ((((1808788003 : ℚ) / 4000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2281, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2273 < q → q < 2281 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2281).mp (by decide +kernel))) hgap
  have hprev := s2L_337
  have hrat : ((1808788003 : ℚ) / 4000000000) ≤ ((56524601069 : ℚ) / 125000000000) + (2281:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((1808788003 : ℚ) / 4000000000) : ℚ) : ℝ) ≤ ((((56524601069 : ℚ) / 125000000000) : ℚ) : ℝ) + ((2281:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2281:ℚ)^(-2:ℤ) : ℝ) = ((2281:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_339 : ((((452197191941 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2287, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2281 < q → q < 2287 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2287).mp (by decide +kernel))) hgap
  have hprev := s2L_338
  have hrat : ((452197191941 : ℚ) / 1000000000000) ≤ ((1808788003 : ℚ) / 4000000000) + (2287:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452197191941 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1808788003 : ℚ) / 4000000000) : ℚ) : ℝ) + ((2287:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2287:ℚ)^(-2:ℤ) : ℝ) = ((2287:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_340 : ((((113049345533 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2293, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2287 < q → q < 2293 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2293).mp (by decide +kernel))) hgap
  have hprev := s2L_339
  have hrat : ((113049345533 : ℚ) / 250000000000) ≤ ((452197191941 : ℚ) / 1000000000000) + (2293:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113049345533 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452197191941 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((2293:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2293:ℚ)^(-2:ℤ) : ℝ) = ((2293:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_341 : ((((226098785831 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2297, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2293 < q → q < 2297 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2297).mp (by decide +kernel))) hgap
  have hprev := s2L_340
  have hrat : ((226098785831 : ℚ) / 500000000000) ≤ ((113049345533 : ℚ) / 250000000000) + (2297:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226098785831 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113049345533 : ℚ) / 250000000000) : ℚ) : ℝ) + ((2297:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2297:ℚ)^(-2:ℤ) : ℝ) = ((2297:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_342 : ((((452197759227 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2309, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2297 < q → q < 2309 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2309).mp (by decide +kernel))) hgap
  have hprev := s2L_341
  have hrat : ((452197759227 : ℚ) / 1000000000000) ≤ ((226098785831 : ℚ) / 500000000000) + (2309:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452197759227 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226098785831 : ℚ) / 500000000000) : ℚ) : ℝ) + ((2309:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2309:ℚ)^(-2:ℤ) : ℝ) = ((2309:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_343 : ((((452197946467 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2311, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2309 < q → q < 2311 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2311).mp (by decide +kernel))) hgap
  have hprev := s2L_342
  have hrat : ((452197946467 : ℚ) / 1000000000000) ≤ ((452197759227 : ℚ) / 1000000000000) + (2311:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452197946467 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452197759227 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((2311:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2311:ℚ)^(-2:ℤ) : ℝ) = ((2311:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_344 : ((((28262383137 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2333, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2311 < q → q < 2333 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2333).mp (by decide +kernel))) hgap
  have hprev := s2L_343
  have hrat : ((28262383137 : ℚ) / 62500000000) ≤ ((452197946467 : ℚ) / 1000000000000) + (2333:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28262383137 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((452197946467 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((2333:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2333:ℚ)^(-2:ℤ) : ℝ) = ((2333:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_345 : ((((28262394561 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2339, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2333 < q → q < 2339 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2339).mp (by decide +kernel))) hgap
  have hprev := s2L_344
  have hrat : ((28262394561 : ℚ) / 62500000000) ≤ ((28262383137 : ℚ) / 62500000000) + (2339:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28262394561 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((28262383137 : ℚ) / 62500000000) : ℚ) : ℝ) + ((2339:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2339:ℚ)^(-2:ℤ) : ℝ) = ((2339:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_346 : ((((56524811931 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2341, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2339 < q → q < 2341 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2341).mp (by decide +kernel))) hgap
  have hprev := s2L_345
  have hrat : ((56524811931 : ℚ) / 125000000000) ≤ ((28262394561 : ℚ) / 62500000000) + (2341:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56524811931 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((28262394561 : ℚ) / 62500000000) : ℚ) : ℝ) + ((2341:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2341:ℚ)^(-2:ℤ) : ℝ) = ((2341:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_347 : ((((113049669247 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2347, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2341 < q → q < 2347 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2347).mp (by decide +kernel))) hgap
  have hprev := s2L_346
  have hrat : ((113049669247 : ℚ) / 250000000000) ≤ ((56524811931 : ℚ) / 125000000000) + (2347:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113049669247 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((56524811931 : ℚ) / 125000000000) : ℚ) : ℝ) + ((2347:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2347:ℚ)^(-2:ℤ) : ℝ) = ((2347:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_348 : ((((452198857911 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2351, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2347 < q → q < 2351 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2351).mp (by decide +kernel))) hgap
  have hprev := s2L_347
  have hrat : ((452198857911 : ℚ) / 1000000000000) ≤ ((113049669247 : ℚ) / 250000000000) + (2351:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452198857911 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113049669247 : ℚ) / 250000000000) : ℚ) : ℝ) + ((2351:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2351:ℚ)^(-2:ℤ) : ℝ) = ((2351:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_349 : ((((226099518957 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2357, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2351 < q → q < 2357 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2357).mp (by decide +kernel))) hgap
  have hprev := s2L_348
  have hrat : ((226099518957 : ℚ) / 500000000000) ≤ ((452198857911 : ℚ) / 1000000000000) + (2357:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226099518957 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452198857911 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((2357:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2357:ℚ)^(-2:ℤ) : ℝ) = ((2357:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_350 : ((((226099607899 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2371, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2357 < q → q < 2371 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2371).mp (by decide +kernel))) hgap
  have hprev := s2L_349
  have hrat : ((226099607899 : ℚ) / 500000000000) ≤ ((226099518957 : ℚ) / 500000000000) + (2371:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226099607899 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226099518957 : ℚ) / 500000000000) : ℚ) : ℝ) + ((2371:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2371:ℚ)^(-2:ℤ) : ℝ) = ((2371:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_351 : ((((90439878557 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2377, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2371 < q → q < 2377 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2377).mp (by decide +kernel))) hgap
  have hprev := s2L_350
  have hrat : ((90439878557 : ℚ) / 200000000000) ≤ ((226099607899 : ℚ) / 500000000000) + (2377:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90439878557 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((226099607899 : ℚ) / 500000000000) : ℚ) : ℝ) + ((2377:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2377:ℚ)^(-2:ℤ) : ℝ) = ((2377:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_352 : ((((452199569177 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2381, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2377 < q → q < 2381 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2381).mp (by decide +kernel))) hgap
  have hprev := s2L_351
  have hrat : ((452199569177 : ℚ) / 1000000000000) ≤ ((90439878557 : ℚ) / 200000000000) + (2381:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452199569177 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90439878557 : ℚ) / 200000000000) : ℚ) : ℝ) + ((2381:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2381:ℚ)^(-2:ℤ) : ℝ) = ((2381:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_353 : ((((452199745273 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2383, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2381 < q → q < 2383 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2383).mp (by decide +kernel))) hgap
  have hprev := s2L_352
  have hrat : ((452199745273 : ℚ) / 1000000000000) ≤ ((452199569177 : ℚ) / 1000000000000) + (2383:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452199745273 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452199569177 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((2383:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2383:ℚ)^(-2:ℤ) : ℝ) = ((2383:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_354 : ((((226099960243 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2389, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2383 < q → q < 2389 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2389).mp (by decide +kernel))) hgap
  have hprev := s2L_353
  have hrat : ((226099960243 : ℚ) / 500000000000) ≤ ((452199745273 : ℚ) / 1000000000000) + (2389:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226099960243 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452199745273 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((2389:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2389:ℚ)^(-2:ℤ) : ℝ) = ((2389:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_355 : ((((226100047557 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2393, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2389 < q → q < 2393 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2393).mp (by decide +kernel))) hgap
  have hprev := s2L_354
  have hrat : ((226100047557 : ℚ) / 500000000000) ≤ ((226099960243 : ℚ) / 500000000000) + (2393:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226100047557 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226099960243 : ℚ) / 500000000000) : ℚ) : ℝ) + ((2393:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2393:ℚ)^(-2:ℤ) : ℝ) = ((2393:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_356 : ((((452200268869 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2399, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2393 < q → q < 2399 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2399).mp (by decide +kernel))) hgap
  have hprev := s2L_355
  have hrat : ((452200268869 : ℚ) / 1000000000000) ≤ ((226100047557 : ℚ) / 500000000000) + (2399:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452200268869 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226100047557 : ℚ) / 500000000000) : ℚ) : ℝ) + ((2399:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2399:ℚ)^(-2:ℤ) : ℝ) = ((2399:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_357 : ((((452200440899 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2411, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2399 < q → q < 2411 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2411).mp (by decide +kernel))) hgap
  have hprev := s2L_356
  have hrat : ((452200440899 : ℚ) / 1000000000000) ≤ ((452200268869 : ℚ) / 1000000000000) + (2411:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452200440899 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452200268869 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((2411:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2411:ℚ)^(-2:ℤ) : ℝ) = ((2411:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_358 : ((((113050153019 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2417, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2411 < q → q < 2417 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2417).mp (by decide +kernel))) hgap
  have hprev := s2L_357
  have hrat : ((113050153019 : ℚ) / 250000000000) ≤ ((452200440899 : ℚ) / 1000000000000) + (2417:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113050153019 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452200440899 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((2417:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2417:ℚ)^(-2:ℤ) : ℝ) = ((2417:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_359 : ((((226100391203 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2423, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2417 < q → q < 2423 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2423).mp (by decide +kernel))) hgap
  have hprev := s2L_358
  have hrat : ((226100391203 : ℚ) / 500000000000) ≤ ((113050153019 : ℚ) / 250000000000) + (2423:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226100391203 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113050153019 : ℚ) / 250000000000) : ℚ) : ℝ) + ((2423:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2423:ℚ)^(-2:ℤ) : ℝ) = ((2423:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_360 : ((((90440190157 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2437, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2423 < q → q < 2437 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2437).mp (by decide +kernel))) hgap
  have hprev := s2L_359
  have hrat : ((90440190157 : ℚ) / 200000000000) ≤ ((226100391203 : ℚ) / 500000000000) + (2437:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90440190157 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((226100391203 : ℚ) / 500000000000) : ℚ) : ℝ) + ((2437:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2437:ℚ)^(-2:ℤ) : ℝ) = ((2437:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_361 : ((((452201118613 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2441, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2437 < q → q < 2441 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2441).mp (by decide +kernel))) hgap
  have hprev := s2L_360
  have hrat : ((452201118613 : ℚ) / 1000000000000) ≤ ((90440190157 : ℚ) / 200000000000) + (2441:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452201118613 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90440190157 : ℚ) / 200000000000) : ℚ) : ℝ) + ((2441:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2441:ℚ)^(-2:ℤ) : ℝ) = ((2441:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_362 : ((((226100642809 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2447, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2441 < q → q < 2447 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2447).mp (by decide +kernel))) hgap
  have hprev := s2L_361
  have hrat : ((226100642809 : ℚ) / 500000000000) ≤ ((452201118613 : ℚ) / 1000000000000) + (2447:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226100642809 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452201118613 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((2447:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2447:ℚ)^(-2:ℤ) : ℝ) = ((2447:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_363 : ((((452201450997 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2459, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2447 < q → q < 2459 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2459).mp (by decide +kernel))) hgap
  have hprev := s2L_362
  have hrat : ((452201450997 : ℚ) / 1000000000000) ≤ ((226100642809 : ℚ) / 500000000000) + (2459:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452201450997 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226100642809 : ℚ) / 500000000000) : ℚ) : ℝ) + ((2459:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2459:ℚ)^(-2:ℤ) : ℝ) = ((2459:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_364 : ((((226100807653 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2467, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2459 < q → q < 2467 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2467).mp (by decide +kernel))) hgap
  have hprev := s2L_363
  have hrat : ((226100807653 : ℚ) / 500000000000) ≤ ((452201450997 : ℚ) / 1000000000000) + (2467:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226100807653 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452201450997 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((2467:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2467:ℚ)^(-2:ℤ) : ℝ) = ((2467:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_365 : ((((226100889409 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2473, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2467 < q → q < 2473 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2473).mp (by decide +kernel))) hgap
  have hprev := s2L_364
  have hrat : ((226100889409 : ℚ) / 500000000000) ≤ ((226100807653 : ℚ) / 500000000000) + (2473:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226100889409 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226100807653 : ℚ) / 500000000000) : ℚ) : ℝ) + ((2473:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2473:ℚ)^(-2:ℤ) : ℝ) = ((2473:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_366 : ((((452201941803 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2477, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2473 < q → q < 2477 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2477).mp (by decide +kernel))) hgap
  have hprev := s2L_365
  have hrat : ((452201941803 : ℚ) / 1000000000000) ≤ ((226100889409 : ℚ) / 500000000000) + (2477:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452201941803 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226100889409 : ℚ) / 500000000000) : ℚ) : ℝ) + ((2477:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2477:ℚ)^(-2:ℤ) : ℝ) = ((2477:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_367 : ((((452202101419 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2503, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2477 < q → q < 2503 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2503).mp (by decide +kernel))) hgap
  have hprev := s2L_366
  have hrat : ((452202101419 : ℚ) / 1000000000000) ≤ ((452201941803 : ℚ) / 1000000000000) + (2503:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452202101419 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452201941803 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((2503:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2503:ℚ)^(-2:ℤ) : ℝ) = ((2503:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_368 : ((((113050564691 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2521, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2503 < q → q < 2521 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2521).mp (by decide +kernel))) hgap
  have hprev := s2L_367
  have hrat : ((113050564691 : ℚ) / 250000000000) ≤ ((452202101419 : ℚ) / 1000000000000) + (2521:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113050564691 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452202101419 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((2521:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2521:ℚ)^(-2:ℤ) : ℝ) = ((2521:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_369 : ((((113050603717 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2531, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2521 < q → q < 2531 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2531).mp (by decide +kernel))) hgap
  have hprev := s2L_368
  have hrat : ((113050603717 : ℚ) / 250000000000) ≤ ((113050564691 : ℚ) / 250000000000) + (2531:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113050603717 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((113050564691 : ℚ) / 250000000000) : ℚ) : ℝ) + ((2531:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2531:ℚ)^(-2:ℤ) : ℝ) = ((2531:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_370 : ((((45220256999 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2539, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2531 < q → q < 2539 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2539).mp (by decide +kernel))) hgap
  have hprev := s2L_369
  have hrat : ((45220256999 : ℚ) / 100000000000) ≤ ((113050603717 : ℚ) / 250000000000) + (2539:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45220256999 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((113050603717 : ℚ) / 250000000000) : ℚ) : ℝ) + ((2539:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2539:ℚ)^(-2:ℤ) : ℝ) = ((2539:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_371 : ((((28262670289 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2543, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2539 < q → q < 2543 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2543).mp (by decide +kernel))) hgap
  have hprev := s2L_370
  have hrat : ((28262670289 : ℚ) / 62500000000) ≤ ((45220256999 : ℚ) / 100000000000) + (2543:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28262670289 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((45220256999 : ℚ) / 100000000000) : ℚ) : ℝ) + ((2543:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2543:ℚ)^(-2:ℤ) : ℝ) = ((2543:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_372 : ((((452202878531 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2549, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2543 < q → q < 2549 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2549).mp (by decide +kernel))) hgap
  have hprev := s2L_371
  have hrat : ((452202878531 : ℚ) / 1000000000000) ≤ ((28262670289 : ℚ) / 62500000000) + (2549:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452202878531 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((28262670289 : ℚ) / 62500000000) : ℚ) : ℝ) + ((2549:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2549:ℚ)^(-2:ℤ) : ℝ) = ((2549:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_373 : ((((452203032197 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2551, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2549 < q → q < 2551 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2551).mp (by decide +kernel))) hgap
  have hprev := s2L_372
  have hrat : ((452203032197 : ℚ) / 1000000000000) ≤ ((452202878531 : ℚ) / 1000000000000) + (2551:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452203032197 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452202878531 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((2551:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2551:ℚ)^(-2:ℤ) : ℝ) = ((2551:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_374 : ((((452203185143 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2557, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2551 < q → q < 2557 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2557).mp (by decide +kernel))) hgap
  have hprev := s2L_373
  have hrat : ((452203185143 : ℚ) / 1000000000000) ≤ ((452203032197 : ℚ) / 1000000000000) + (2557:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452203185143 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452203032197 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((2557:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2557:ℚ)^(-2:ℤ) : ℝ) = ((2557:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_375 : ((((45220333549 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2579, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2557 < q → q < 2579 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2579).mp (by decide +kernel))) hgap
  have hprev := s2L_374
  have hrat : ((45220333549 : ℚ) / 100000000000) ≤ ((452203185143 : ℚ) / 1000000000000) + (2579:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45220333549 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((452203185143 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((2579:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2579:ℚ)^(-2:ℤ) : ℝ) = ((2579:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_376 : ((((14131358889 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2591, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2579 < q → q < 2591 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2591).mp (by decide +kernel))) hgap
  have hprev := s2L_375
  have hrat : ((14131358889 : ℚ) / 31250000000) ≤ ((45220333549 : ℚ) / 100000000000) + (2591:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((14131358889 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((45220333549 : ℚ) / 100000000000) : ℚ) : ℝ) + ((2591:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2591:ℚ)^(-2:ℤ) : ℝ) = ((2591:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_377 : ((((56525454147 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2593, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2591 < q → q < 2593 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2593).mp (by decide +kernel))) hgap
  have hprev := s2L_376
  have hrat : ((56525454147 : ℚ) / 125000000000) ≤ ((14131358889 : ℚ) / 31250000000) + (2593:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56525454147 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((14131358889 : ℚ) / 31250000000) : ℚ) : ℝ) + ((2593:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2593:ℚ)^(-2:ℤ) : ℝ) = ((2593:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_378 : ((((226101890043 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2609, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2593 < q → q < 2609 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2609).mp (by decide +kernel))) hgap
  have hprev := s2L_377
  have hrat : ((226101890043 : ℚ) / 500000000000) ≤ ((56525454147 : ℚ) / 125000000000) + (2609:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226101890043 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((56525454147 : ℚ) / 125000000000) : ℚ) : ℝ) + ((2609:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2609:ℚ)^(-2:ℤ) : ℝ) = ((2609:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_379 : ((((452203926099 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2617, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2609 < q → q < 2617 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2617).mp (by decide +kernel))) hgap
  have hprev := s2L_378
  have hrat : ((452203926099 : ℚ) / 1000000000000) ≤ ((226101890043 : ℚ) / 500000000000) + (2617:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452203926099 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226101890043 : ℚ) / 500000000000) : ℚ) : ℝ) + ((2617:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2617:ℚ)^(-2:ℤ) : ℝ) = ((2617:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_380 : ((((452204071667 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2621, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2617 < q → q < 2621 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2621).mp (by decide +kernel))) hgap
  have hprev := s2L_379
  have hrat : ((452204071667 : ℚ) / 1000000000000) ≤ ((452203926099 : ℚ) / 1000000000000) + (2621:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452204071667 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452203926099 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((2621:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2621:ℚ)^(-2:ℤ) : ℝ) = ((2621:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_381 : ((((452204215911 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2633, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2621 < q → q < 2633 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2633).mp (by decide +kernel))) hgap
  have hprev := s2L_380
  have hrat : ((452204215911 : ℚ) / 1000000000000) ≤ ((452204071667 : ℚ) / 1000000000000) + (2633:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452204215911 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452204071667 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((2633:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2633:ℚ)^(-2:ℤ) : ℝ) = ((2633:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_382 : ((((452204358633 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2647, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2633 < q → q < 2647 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2647).mp (by decide +kernel))) hgap
  have hprev := s2L_381
  have hrat : ((452204358633 : ℚ) / 1000000000000) ≤ ((452204215911 : ℚ) / 1000000000000) + (2647:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452204358633 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452204215911 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((2647:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2647:ℚ)^(-2:ℤ) : ℝ) = ((2647:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_383 : ((((452204500283 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2657, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2647 < q → q < 2657 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2657).mp (by decide +kernel))) hgap
  have hprev := s2L_382
  have hrat : ((452204500283 : ℚ) / 1000000000000) ≤ ((452204358633 : ℚ) / 1000000000000) + (2657:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452204500283 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452204358633 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((2657:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2657:ℚ)^(-2:ℤ) : ℝ) = ((2657:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_384 : ((((11305116043 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2659, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2657 < q → q < 2659 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2659).mp (by decide +kernel))) hgap
  have hprev := s2L_383
  have hrat : ((11305116043 : ℚ) / 25000000000) ≤ ((452204500283 : ℚ) / 1000000000000) + (2659:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((11305116043 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((452204500283 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((2659:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2659:ℚ)^(-2:ℤ) : ℝ) = ((2659:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_385 : ((((113051195683 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2663, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2659 < q → q < 2663 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2663).mp (by decide +kernel))) hgap
  have hprev := s2L_384
  have hrat : ((113051195683 : ℚ) / 250000000000) ≤ ((11305116043 : ℚ) / 25000000000) + (2663:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113051195683 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((11305116043 : ℚ) / 25000000000) : ℚ) : ℝ) + ((2663:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2663:ℚ)^(-2:ℤ) : ℝ) = ((2663:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_386 : ((((452204922901 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2671, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2663 < q → q < 2671 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2671).mp (by decide +kernel))) hgap
  have hprev := s2L_385
  have hrat : ((452204922901 : ℚ) / 1000000000000) ≤ ((113051195683 : ℚ) / 250000000000) + (2671:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452204922901 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113051195683 : ℚ) / 250000000000) : ℚ) : ℝ) + ((2671:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2671:ℚ)^(-2:ℤ) : ℝ) = ((2671:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_387 : ((((226102531221 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2677, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2671 < q → q < 2677 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2677).mp (by decide +kernel))) hgap
  have hprev := s2L_386
  have hrat : ((226102531221 : ℚ) / 500000000000) ≤ ((452204922901 : ℚ) / 1000000000000) + (2677:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226102531221 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452204922901 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((2677:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2677:ℚ)^(-2:ℤ) : ℝ) = ((2677:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_388 : ((((5652565017 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2683, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2677 < q → q < 2683 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2683).mp (by decide +kernel))) hgap
  have hprev := s2L_387
  have hrat : ((5652565017 : ℚ) / 12500000000) ≤ ((226102531221 : ℚ) / 500000000000) + (2683:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((5652565017 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ ((((226102531221 : ℚ) / 500000000000) : ℚ) : ℝ) + ((2683:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2683:ℚ)^(-2:ℤ) : ℝ) = ((2683:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_389 : ((((56525667483 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2687, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2683 < q → q < 2687 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2687).mp (by decide +kernel))) hgap
  have hprev := s2L_388
  have hrat : ((56525667483 : ℚ) / 125000000000) ≤ ((5652565017 : ℚ) / 12500000000) + (2687:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56525667483 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((5652565017 : ℚ) / 12500000000) : ℚ) : ℝ) + ((2687:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2687:ℚ)^(-2:ℤ) : ℝ) = ((2687:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_390 : ((((226102739081 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2689, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2687 < q → q < 2689 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2689).mp (by decide +kernel))) hgap
  have hprev := s2L_389
  have hrat : ((226102739081 : ℚ) / 500000000000) ≤ ((56525667483 : ℚ) / 125000000000) + (2689:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226102739081 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((56525667483 : ℚ) / 125000000000) : ℚ) : ℝ) + ((2689:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2689:ℚ)^(-2:ℤ) : ℝ) = ((2689:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_391 : ((((9044112321 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2693, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2689 < q → q < 2693 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2693).mp (by decide +kernel))) hgap
  have hprev := s2L_390
  have hrat : ((9044112321 : ℚ) / 20000000000) ≤ ((226102739081 : ℚ) / 500000000000) + (2693:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((9044112321 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ ((((226102739081 : ℚ) / 500000000000) : ℚ) : ℝ) + ((2693:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2693:ℚ)^(-2:ℤ) : ℝ) = ((2693:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_392 : ((((18088230133 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2699, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2693 < q → q < 2699 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2699).mp (by decide +kernel))) hgap
  have hprev := s2L_391
  have hrat : ((18088230133 : ℚ) / 40000000000) ≤ ((9044112321 : ℚ) / 20000000000) + (2699:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18088230133 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((9044112321 : ℚ) / 20000000000) : ℚ) : ℝ) + ((2699:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2699:ℚ)^(-2:ℤ) : ℝ) = ((2699:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_393 : ((((45220588979 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2707, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2699 < q → q < 2707 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2707).mp (by decide +kernel))) hgap
  have hprev := s2L_392
  have hrat : ((45220588979 : ℚ) / 100000000000) ≤ ((18088230133 : ℚ) / 40000000000) + (2707:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45220588979 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((18088230133 : ℚ) / 40000000000) : ℚ) : ℝ) + ((2707:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2707:ℚ)^(-2:ℤ) : ℝ) = ((2707:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_394 : ((((452206025853 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2711, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2707 < q → q < 2711 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2711).mp (by decide +kernel))) hgap
  have hprev := s2L_393
  have hrat : ((452206025853 : ℚ) / 1000000000000) ≤ ((45220588979 : ℚ) / 100000000000) + (2711:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452206025853 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((45220588979 : ℚ) / 100000000000) : ℚ) : ℝ) + ((2711:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2711:ℚ)^(-2:ℤ) : ℝ) = ((2711:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_395 : ((((90441232343 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2713, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2711 < q → q < 2713 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2713).mp (by decide +kernel))) hgap
  have hprev := s2L_394
  have hrat : ((90441232343 : ℚ) / 200000000000) ≤ ((452206025853 : ℚ) / 1000000000000) + (2713:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90441232343 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452206025853 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((2713:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2713:ℚ)^(-2:ℤ) : ℝ) = ((2713:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_396 : ((((226103148489 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2719, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2713 < q → q < 2719 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2719).mp (by decide +kernel))) hgap
  have hprev := s2L_395
  have hrat : ((226103148489 : ℚ) / 500000000000) ≤ ((90441232343 : ℚ) / 200000000000) + (2719:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226103148489 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((90441232343 : ℚ) / 200000000000) : ℚ) : ℝ) + ((2719:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2719:ℚ)^(-2:ℤ) : ℝ) = ((2719:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_397 : ((((113051607813 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2729, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2719 < q → q < 2729 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2729).mp (by decide +kernel))) hgap
  have hprev := s2L_396
  have hrat : ((113051607813 : ℚ) / 250000000000) ≤ ((226103148489 : ℚ) / 500000000000) + (2729:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113051607813 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226103148489 : ℚ) / 500000000000) : ℚ) : ℝ) + ((2729:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2729:ℚ)^(-2:ℤ) : ℝ) = ((2729:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_398 : ((((452206565329 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2731, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2729 < q → q < 2731 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2731).mp (by decide +kernel))) hgap
  have hprev := s2L_397
  have hrat : ((452206565329 : ℚ) / 1000000000000) ≤ ((113051607813 : ℚ) / 250000000000) + (2731:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452206565329 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113051607813 : ℚ) / 250000000000) : ℚ) : ℝ) + ((2731:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2731:ℚ)^(-2:ℤ) : ℝ) = ((2731:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_399 : ((((45220669843 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2741, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2731 < q → q < 2741 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2741).mp (by decide +kernel))) hgap
  have hprev := s2L_398
  have hrat : ((45220669843 : ℚ) / 100000000000) ≤ ((452206565329 : ℚ) / 1000000000000) + (2741:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45220669843 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((452206565329 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((2741:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2741:ℚ)^(-2:ℤ) : ℝ) = ((2741:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_400 : ((((452206830757 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2749, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2741 < q → q < 2749 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2749).mp (by decide +kernel))) hgap
  have hprev := s2L_399
  have hrat : ((452206830757 : ℚ) / 1000000000000) ≤ ((45220669843 : ℚ) / 100000000000) + (2749:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452206830757 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((45220669843 : ℚ) / 100000000000) : ℚ) : ℝ) + ((2749:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2749:ℚ)^(-2:ℤ) : ℝ) = ((2749:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_401 : ((((4522069627 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2753, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2749 < q → q < 2753 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2753).mp (by decide +kernel))) hgap
  have hprev := s2L_400
  have hrat : ((4522069627 : ℚ) / 10000000000) ≤ ((452206830757 : ℚ) / 1000000000000) + (2753:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((4522069627 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ ((((452206830757 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((2753:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2753:ℚ)^(-2:ℤ) : ℝ) = ((2753:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_402 : ((((452207093311 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2767, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2753 < q → q < 2767 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2767).mp (by decide +kernel))) hgap
  have hprev := s2L_401
  have hrat : ((452207093311 : ℚ) / 1000000000000) ≤ ((4522069627 : ℚ) / 10000000000) + (2767:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452207093311 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4522069627 : ℚ) / 10000000000) : ℚ) : ℝ) + ((2767:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2767:ℚ)^(-2:ℤ) : ℝ) = ((2767:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_403 : ((((452207222983 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2777, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2767 < q → q < 2777 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2777).mp (by decide +kernel))) hgap
  have hprev := s2L_402
  have hrat : ((452207222983 : ℚ) / 1000000000000) ≤ ((452207093311 : ℚ) / 1000000000000) + (2777:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452207222983 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452207093311 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((2777:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2777:ℚ)^(-2:ℤ) : ℝ) = ((2777:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_404 : ((((226103675771 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2789, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2777 < q → q < 2789 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2789).mp (by decide +kernel))) hgap
  have hprev := s2L_403
  have hrat : ((226103675771 : ℚ) / 500000000000) ≤ ((452207222983 : ℚ) / 1000000000000) + (2789:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226103675771 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452207222983 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((2789:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2789:ℚ)^(-2:ℤ) : ℝ) = ((2789:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_405 : ((((113051869979 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2791, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2789 < q → q < 2791 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2791).mp (by decide +kernel))) hgap
  have hprev := s2L_404
  have hrat : ((113051869979 : ℚ) / 250000000000) ≤ ((226103675771 : ℚ) / 500000000000) + (2791:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113051869979 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226103675771 : ℚ) / 500000000000) : ℚ) : ℝ) + ((2791:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2791:ℚ)^(-2:ℤ) : ℝ) = ((2791:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_406 : ((((22610380387 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2797, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2791 < q → q < 2797 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2797).mp (by decide +kernel))) hgap
  have hprev := s2L_405
  have hrat : ((22610380387 : ℚ) / 50000000000) ≤ ((113051869979 : ℚ) / 250000000000) + (2797:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22610380387 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((113051869979 : ℚ) / 250000000000) : ℚ) : ℝ) + ((2797:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2797:ℚ)^(-2:ℤ) : ℝ) = ((2797:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_407 : ((((452207735199 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2801, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2797 < q → q < 2801 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2801).mp (by decide +kernel))) hgap
  have hprev := s2L_406
  have hrat : ((452207735199 : ℚ) / 1000000000000) ≤ ((22610380387 : ℚ) / 50000000000) + (2801:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452207735199 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((22610380387 : ℚ) / 50000000000) : ℚ) : ℝ) + ((2801:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2801:ℚ)^(-2:ℤ) : ℝ) = ((2801:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_408 : ((((452207862477 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2803, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2801 < q → q < 2803 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2803).mp (by decide +kernel))) hgap
  have hprev := s2L_407
  have hrat : ((452207862477 : ℚ) / 1000000000000) ≤ ((452207735199 : ℚ) / 1000000000000) + (2803:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452207862477 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452207735199 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((2803:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2803:ℚ)^(-2:ℤ) : ℝ) = ((2803:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_409 : ((((226103994157 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2819, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2803 < q → q < 2819 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2819).mp (by decide +kernel))) hgap
  have hprev := s2L_408
  have hrat : ((226103994157 : ℚ) / 500000000000) ≤ ((452207862477 : ℚ) / 1000000000000) + (2819:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226103994157 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452207862477 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((2819:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2819:ℚ)^(-2:ℤ) : ℝ) = ((2819:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_410 : ((((45220811291 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2833, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2819 < q → q < 2833 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2833).mp (by decide +kernel))) hgap
  have hprev := s2L_409
  have hrat : ((45220811291 : ℚ) / 100000000000) ≤ ((226103994157 : ℚ) / 500000000000) + (2833:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45220811291 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((226103994157 : ℚ) / 500000000000) : ℚ) : ℝ) + ((2833:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2833:ℚ)^(-2:ℤ) : ℝ) = ((2833:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_411 : ((((90441647431 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2837, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2833 < q → q < 2837 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2837).mp (by decide +kernel))) hgap
  have hprev := s2L_410
  have hrat : ((90441647431 : ℚ) / 200000000000) ≤ ((45220811291 : ℚ) / 100000000000) + (2837:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90441647431 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((45220811291 : ℚ) / 100000000000) : ℚ) : ℝ) + ((2837:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2837:ℚ)^(-2:ℤ) : ℝ) = ((2837:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_412 : ((((113052090219 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2843, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2837 < q → q < 2843 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2843).mp (by decide +kernel))) hgap
  have hprev := s2L_411
  have hrat : ((113052090219 : ℚ) / 250000000000) ≤ ((90441647431 : ℚ) / 200000000000) + (2843:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113052090219 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((90441647431 : ℚ) / 200000000000) : ℚ) : ℝ) + ((2843:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2843:ℚ)^(-2:ℤ) : ℝ) = ((2843:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_413 : ((((7065757561 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2851, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2843 < q → q < 2851 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2851).mp (by decide +kernel))) hgap
  have hprev := s2L_412
  have hrat : ((7065757561 : ℚ) / 15625000000) ≤ ((113052090219 : ℚ) / 250000000000) + (2851:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((7065757561 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ ((((113052090219 : ℚ) / 250000000000) : ℚ) : ℝ) + ((2851:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2851:ℚ)^(-2:ℤ) : ℝ) = ((2851:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_414 : ((((28263037901 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2857, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2851 < q → q < 2857 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2857).mp (by decide +kernel))) hgap
  have hprev := s2L_413
  have hrat : ((28263037901 : ℚ) / 62500000000) ≤ ((7065757561 : ℚ) / 15625000000) + (2857:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28263037901 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((7065757561 : ℚ) / 15625000000) : ℚ) : ℝ) + ((2857:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2857:ℚ)^(-2:ℤ) : ℝ) = ((2857:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_415 : ((((90441745717 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2861, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2857 < q → q < 2861 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2861).mp (by decide +kernel))) hgap
  have hprev := s2L_414
  have hrat : ((90441745717 : ℚ) / 200000000000) ≤ ((28263037901 : ℚ) / 62500000000) + (2861:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90441745717 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((28263037901 : ℚ) / 62500000000) : ℚ) : ℝ) + ((2861:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2861:ℚ)^(-2:ℤ) : ℝ) = ((2861:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_416 : ((((28263053077 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2879, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2861 < q → q < 2879 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2879).mp (by decide +kernel))) hgap
  have hprev := s2L_415
  have hrat : ((28263053077 : ℚ) / 62500000000) ≤ ((90441745717 : ℚ) / 200000000000) + (2879:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28263053077 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((90441745717 : ℚ) / 200000000000) : ℚ) : ℝ) + ((2879:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2879:ℚ)^(-2:ℤ) : ℝ) = ((2879:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_417 : ((((452208969211 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2887, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2879 < q → q < 2887 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2887).mp (by decide +kernel))) hgap
  have hprev := s2L_416
  have hrat : ((452208969211 : ℚ) / 1000000000000) ≤ ((28263053077 : ℚ) / 62500000000) + (2887:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452208969211 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((28263053077 : ℚ) / 62500000000) : ℚ) : ℝ) + ((2887:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2887:ℚ)^(-2:ℤ) : ℝ) = ((2887:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_418 : ((((452209088363 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2897, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2887 < q → q < 2897 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2897).mp (by decide +kernel))) hgap
  have hprev := s2L_417
  have hrat : ((452209088363 : ℚ) / 1000000000000) ≤ ((452208969211 : ℚ) / 1000000000000) + (2897:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452209088363 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452208969211 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((2897:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2897:ℚ)^(-2:ℤ) : ℝ) = ((2897:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_419 : ((((452209207023 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2903, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2897 < q → q < 2903 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2903).mp (by decide +kernel))) hgap
  have hprev := s2L_418
  have hrat : ((452209207023 : ℚ) / 1000000000000) ≤ ((452209088363 : ℚ) / 1000000000000) + (2903:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452209207023 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452209088363 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((2903:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2903:ℚ)^(-2:ℤ) : ℝ) = ((2903:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_420 : ((((226104662597 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2909, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2903 < q → q < 2909 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2909).mp (by decide +kernel))) hgap
  have hprev := s2L_419
  have hrat : ((226104662597 : ℚ) / 500000000000) ≤ ((452209207023 : ℚ) / 1000000000000) + (2909:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226104662597 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452209207023 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((2909:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2909:ℚ)^(-2:ℤ) : ℝ) = ((2909:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_421 : ((((226104721359 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2917, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2909 < q → q < 2917 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2917).mp (by decide +kernel))) hgap
  have hprev := s2L_420
  have hrat : ((226104721359 : ℚ) / 500000000000) ≤ ((226104662597 : ℚ) / 500000000000) + (2917:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226104721359 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226104662597 : ℚ) / 500000000000) : ℚ) : ℝ) + ((2917:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2917:ℚ)^(-2:ℤ) : ℝ) = ((2917:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_422 : ((((5652619493 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2927, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2917 < q → q < 2927 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2927).mp (by decide +kernel))) hgap
  have hprev := s2L_421
  have hrat : ((5652619493 : ℚ) / 12500000000) ≤ ((226104721359 : ℚ) / 500000000000) + (2927:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((5652619493 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ ((((226104721359 : ℚ) / 500000000000) : ℚ) : ℝ) + ((2927:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2927:ℚ)^(-2:ℤ) : ℝ) = ((2927:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_423 : ((((452209675211 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2939, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2927 < q → q < 2939 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2939).mp (by decide +kernel))) hgap
  have hprev := s2L_422
  have hrat : ((452209675211 : ℚ) / 1000000000000) ≤ ((5652619493 : ℚ) / 12500000000) + (2939:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452209675211 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5652619493 : ℚ) / 12500000000) : ℚ) : ℝ) + ((2939:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2939:ℚ)^(-2:ℤ) : ℝ) = ((2939:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_424 : ((((452209789887 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2953, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2939 < q → q < 2953 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2953).mp (by decide +kernel))) hgap
  have hprev := s2L_423
  have hrat : ((452209789887 : ℚ) / 1000000000000) ≤ ((452209675211 : ℚ) / 1000000000000) + (2953:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452209789887 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452209675211 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((2953:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2953:ℚ)^(-2:ℤ) : ℝ) = ((2953:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_425 : ((((452209904253 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2957, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2953 < q → q < 2957 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2957).mp (by decide +kernel))) hgap
  have hprev := s2L_424
  have hrat : ((452209904253 : ℚ) / 1000000000000) ≤ ((452209789887 : ℚ) / 1000000000000) + (2957:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452209904253 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452209789887 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((2957:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2957:ℚ)^(-2:ℤ) : ℝ) = ((2957:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_426 : ((((113052504539 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2963, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2957 < q → q < 2963 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2963).mp (by decide +kernel))) hgap
  have hprev := s2L_425
  have hrat : ((113052504539 : ℚ) / 250000000000) ≤ ((452209904253 : ℚ) / 1000000000000) + (2963:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113052504539 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452209904253 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((2963:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2963:ℚ)^(-2:ℤ) : ℝ) = ((2963:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_427 : ((((452210131599 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2969, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2963 < q → q < 2969 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2969).mp (by decide +kernel))) hgap
  have hprev := s2L_426
  have hrat : ((452210131599 : ℚ) / 1000000000000) ≤ ((113052504539 : ℚ) / 250000000000) + (2969:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452210131599 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113052504539 : ℚ) / 250000000000) : ℚ) : ℝ) + ((2969:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2969:ℚ)^(-2:ℤ) : ℝ) = ((2969:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_428 : ((((452210244889 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2971, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2969 < q → q < 2971 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2971).mp (by decide +kernel))) hgap
  have hprev := s2L_427
  have hrat : ((452210244889 : ℚ) / 1000000000000) ≤ ((452210131599 : ℚ) / 1000000000000) + (2971:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452210244889 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452210131599 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((2971:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2971:ℚ)^(-2:ℤ) : ℝ) = ((2971:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_429 : ((((226105178037 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 2999, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2971 < q → q < 2999 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 2999).mp (by decide +kernel))) hgap
  have hprev := s2L_428
  have hrat : ((226105178037 : ℚ) / 500000000000) ≤ ((452210244889 : ℚ) / 1000000000000) + (2999:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226105178037 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452210244889 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((2999:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((2999:ℚ)^(-2:ℤ) : ℝ) = ((2999:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_430 : ((((452210467111 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3001, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 2999 < q → q < 3001 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3001).mp (by decide +kernel))) hgap
  have hprev := s2L_429
  have hrat : ((452210467111 : ℚ) / 1000000000000) ≤ ((226105178037 : ℚ) / 500000000000) + (3001:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452210467111 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226105178037 : ℚ) / 500000000000) : ℚ) : ℝ) + ((3001:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3001:ℚ)^(-2:ℤ) : ℝ) = ((3001:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_431 : ((((452210577411 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3011, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3001 < q → q < 3011 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3011).mp (by decide +kernel))) hgap
  have hprev := s2L_430
  have hrat : ((452210577411 : ℚ) / 1000000000000) ≤ ((452210467111 : ℚ) / 1000000000000) + (3011:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452210577411 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452210467111 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((3011:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3011:ℚ)^(-2:ℤ) : ℝ) = ((3011:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_432 : ((((452210687127 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3019, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3011 < q → q < 3019 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3019).mp (by decide +kernel))) hgap
  have hprev := s2L_431
  have hrat : ((452210687127 : ℚ) / 1000000000000) ≤ ((452210577411 : ℚ) / 1000000000000) + (3019:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452210687127 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452210577411 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((3019:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3019:ℚ)^(-2:ℤ) : ℝ) = ((3019:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_433 : ((((452210796553 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3023, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3019 < q → q < 3023 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3023).mp (by decide +kernel))) hgap
  have hprev := s2L_432
  have hrat : ((452210796553 : ℚ) / 1000000000000) ≤ ((452210687127 : ℚ) / 1000000000000) + (3023:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452210796553 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452210687127 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((3023:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3023:ℚ)^(-2:ℤ) : ℝ) = ((3023:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_434 : ((((452210904973 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3037, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3023 < q → q < 3037 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3037).mp (by decide +kernel))) hgap
  have hprev := s2L_433
  have hrat : ((452210904973 : ℚ) / 1000000000000) ≤ ((452210796553 : ℚ) / 1000000000000) + (3037:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452210904973 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452210796553 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((3037:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3037:ℚ)^(-2:ℤ) : ℝ) = ((3037:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_435 : ((((113052753277 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3041, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3037 < q → q < 3041 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3041).mp (by decide +kernel))) hgap
  have hprev := s2L_434
  have hrat : ((113052753277 : ℚ) / 250000000000) ≤ ((452210904973 : ℚ) / 1000000000000) + (3041:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113052753277 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452210904973 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((3041:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3041:ℚ)^(-2:ℤ) : ℝ) = ((3041:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_436 : ((((113052780169 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3049, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3041 < q → q < 3049 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3049).mp (by decide +kernel))) hgap
  have hprev := s2L_435
  have hrat : ((113052780169 : ℚ) / 250000000000) ≤ ((113052753277 : ℚ) / 250000000000) + (3049:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113052780169 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((113052753277 : ℚ) / 250000000000) : ℚ) : ℝ) + ((3049:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3049:ℚ)^(-2:ℤ) : ℝ) = ((3049:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_437 : ((((226105613701 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3061, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3049 < q → q < 3061 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3061).mp (by decide +kernel))) hgap
  have hprev := s2L_436
  have hrat : ((226105613701 : ℚ) / 500000000000) ≤ ((113052780169 : ℚ) / 250000000000) + (3061:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226105613701 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113052780169 : ℚ) / 250000000000) : ℚ) : ℝ) + ((3061:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3061:ℚ)^(-2:ℤ) : ℝ) = ((3061:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_438 : ((((452211333711 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3067, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3061 < q → q < 3067 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3067).mp (by decide +kernel))) hgap
  have hprev := s2L_437
  have hrat : ((452211333711 : ℚ) / 1000000000000) ≤ ((226105613701 : ℚ) / 500000000000) + (3067:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452211333711 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226105613701 : ℚ) / 500000000000) : ℚ) : ℝ) + ((3067:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3067:ℚ)^(-2:ℤ) : ℝ) = ((3067:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_439 : ((((452211439193 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3079, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3067 < q → q < 3079 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3079).mp (by decide +kernel))) hgap
  have hprev := s2L_438
  have hrat : ((452211439193 : ℚ) / 1000000000000) ≤ ((452211333711 : ℚ) / 1000000000000) + (3079:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452211439193 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452211333711 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((3079:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3079:ℚ)^(-2:ℤ) : ℝ) = ((3079:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_440 : ((((226105772201 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3083, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3079 < q → q < 3083 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3083).mp (by decide +kernel))) hgap
  have hprev := s2L_439
  have hrat : ((226105772201 : ℚ) / 500000000000) ≤ ((452211439193 : ℚ) / 1000000000000) + (3083:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226105772201 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452211439193 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((3083:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3083:ℚ)^(-2:ℤ) : ℝ) = ((3083:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_441 : ((((226105824601 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3089, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3083 < q → q < 3089 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3089).mp (by decide +kernel))) hgap
  have hprev := s2L_440
  have hrat : ((226105824601 : ℚ) / 500000000000) ≤ ((226105772201 : ℚ) / 500000000000) + (3089:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226105824601 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226105772201 : ℚ) / 500000000000) : ℚ) : ℝ) + ((3089:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3089:ℚ)^(-2:ℤ) : ℝ) = ((3089:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_442 : ((((226105876329 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3109, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3089 < q → q < 3109 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3109).mp (by decide +kernel))) hgap
  have hprev := s2L_441
  have hrat : ((226105876329 : ℚ) / 500000000000) ≤ ((226105824601 : ℚ) / 500000000000) + (3109:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226105876329 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226105824601 : ℚ) / 500000000000) : ℚ) : ℝ) + ((3109:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3109:ℚ)^(-2:ℤ) : ℝ) = ((3109:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_443 : ((((113052963863 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3119, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3109 < q → q < 3119 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3119).mp (by decide +kernel))) hgap
  have hprev := s2L_442
  have hrat : ((113052963863 : ℚ) / 250000000000) ≤ ((226105876329 : ℚ) / 500000000000) + (3119:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113052963863 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226105876329 : ℚ) / 500000000000) : ℚ) : ℝ) + ((3119:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3119:ℚ)^(-2:ℤ) : ℝ) = ((3119:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_444 : ((((226105979057 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3121, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3119 < q → q < 3121 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3121).mp (by decide +kernel))) hgap
  have hprev := s2L_443
  have hrat : ((226105979057 : ℚ) / 500000000000) ≤ ((113052963863 : ℚ) / 250000000000) + (3121:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226105979057 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113052963863 : ℚ) / 250000000000) : ℚ) : ℝ) + ((3121:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3121:ℚ)^(-2:ℤ) : ℝ) = ((3121:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_445 : ((((113053014933 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3137, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3121 < q → q < 3137 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3137).mp (by decide +kernel))) hgap
  have hprev := s2L_444
  have hrat : ((113053014933 : ℚ) / 250000000000) ≤ ((226105979057 : ℚ) / 500000000000) + (3137:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113053014933 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226105979057 : ℚ) / 500000000000) : ℚ) : ℝ) + ((3137:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3137:ℚ)^(-2:ℤ) : ℝ) = ((3137:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_446 : ((((226106079843 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3163, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3137 < q → q < 3163 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3163).mp (by decide +kernel))) hgap
  have hprev := s2L_445
  have hrat : ((226106079843 : ℚ) / 500000000000) ≤ ((113053014933 : ℚ) / 250000000000) + (3163:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226106079843 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113053014933 : ℚ) / 250000000000) : ℚ) : ℝ) + ((3163:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3163:ℚ)^(-2:ℤ) : ℝ) = ((3163:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_447 : ((((113053064847 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3167, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3163 < q → q < 3167 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3167).mp (by decide +kernel))) hgap
  have hprev := s2L_446
  have hrat : ((113053064847 : ℚ) / 250000000000) ≤ ((226106079843 : ℚ) / 500000000000) + (3167:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113053064847 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226106079843 : ℚ) / 500000000000) : ℚ) : ℝ) + ((3167:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3167:ℚ)^(-2:ℤ) : ℝ) = ((3167:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_448 : ((((113053089741 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3169, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3167 < q → q < 3169 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3169).mp (by decide +kernel))) hgap
  have hprev := s2L_447
  have hrat : ((113053089741 : ℚ) / 250000000000) ≤ ((113053064847 : ℚ) / 250000000000) + (3169:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113053089741 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((113053064847 : ℚ) / 250000000000) : ℚ) : ℝ) + ((3169:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3169:ℚ)^(-2:ℤ) : ℝ) = ((3169:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_449 : ((((45221245779 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3181, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3169 < q → q < 3181 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3181).mp (by decide +kernel))) hgap
  have hprev := s2L_448
  have hrat : ((45221245779 : ℚ) / 100000000000) ≤ ((113053089741 : ℚ) / 250000000000) + (3181:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45221245779 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((113053089741 : ℚ) / 250000000000) : ℚ) : ℝ) + ((3181:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3181:ℚ)^(-2:ℤ) : ℝ) = ((3181:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_450 : ((((113053139061 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3187, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3181 < q → q < 3187 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3187).mp (by decide +kernel))) hgap
  have hprev := s2L_449
  have hrat : ((113053139061 : ℚ) / 250000000000) ≤ ((45221245779 : ℚ) / 100000000000) + (3187:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113053139061 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((45221245779 : ℚ) / 100000000000) : ℚ) : ℝ) + ((3187:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3187:ℚ)^(-2:ℤ) : ℝ) = ((3187:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_451 : ((((452212654451 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3191, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3187 < q → q < 3191 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3191).mp (by decide +kernel))) hgap
  have hprev := s2L_450
  have hrat : ((452212654451 : ℚ) / 1000000000000) ≤ ((113053139061 : ℚ) / 250000000000) + (3191:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452212654451 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113053139061 : ℚ) / 250000000000) : ℚ) : ℝ) + ((3191:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3191:ℚ)^(-2:ℤ) : ℝ) = ((3191:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_452 : ((((113053187981 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3203, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3191 < q → q < 3203 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3203).mp (by decide +kernel))) hgap
  have hprev := s2L_451
  have hrat : ((113053187981 : ℚ) / 250000000000) ≤ ((452212654451 : ℚ) / 1000000000000) + (3203:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113053187981 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452212654451 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((3203:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3203:ℚ)^(-2:ℤ) : ℝ) = ((3203:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_453 : ((((452212849033 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3209, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3203 < q → q < 3209 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3209).mp (by decide +kernel))) hgap
  have hprev := s2L_452
  have hrat : ((452212849033 : ℚ) / 1000000000000) ≤ ((113053187981 : ℚ) / 250000000000) + (3209:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452212849033 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113053187981 : ℚ) / 250000000000) : ℚ) : ℝ) + ((3209:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3209:ℚ)^(-2:ℤ) : ℝ) = ((3209:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_454 : ((((452212945659 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3217, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3209 < q → q < 3217 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3217).mp (by decide +kernel))) hgap
  have hprev := s2L_453
  have hrat : ((452212945659 : ℚ) / 1000000000000) ≤ ((452212849033 : ℚ) / 1000000000000) + (3217:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452212945659 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452212849033 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((3217:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3217:ℚ)^(-2:ℤ) : ℝ) = ((3217:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_455 : ((((226106521023 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3221, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3217 < q → q < 3221 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3221).mp (by decide +kernel))) hgap
  have hprev := s2L_454
  have hrat : ((226106521023 : ℚ) / 500000000000) ≤ ((452212945659 : ℚ) / 1000000000000) + (3221:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226106521023 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452212945659 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((3221:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3221:ℚ)^(-2:ℤ) : ℝ) = ((3221:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_456 : ((((113053284489 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3229, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3221 < q → q < 3229 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3229).mp (by decide +kernel))) hgap
  have hprev := s2L_455
  have hrat : ((113053284489 : ℚ) / 250000000000) ≤ ((226106521023 : ℚ) / 500000000000) + (3229:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113053284489 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226106521023 : ℚ) / 500000000000) : ℚ) : ℝ) + ((3229:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3229:ℚ)^(-2:ℤ) : ℝ) = ((3229:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_457 : ((((113053308143 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3251, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3229 < q → q < 3251 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3251).mp (by decide +kernel))) hgap
  have hprev := s2L_456
  have hrat : ((113053308143 : ℚ) / 250000000000) ≤ ((113053284489 : ℚ) / 250000000000) + (3251:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113053308143 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((113053284489 : ℚ) / 250000000000) : ℚ) : ℝ) + ((3251:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3251:ℚ)^(-2:ℤ) : ℝ) = ((3251:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_458 : ((((14131666471 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3253, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3251 < q → q < 3253 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3253).mp (by decide +kernel))) hgap
  have hprev := s2L_457
  have hrat : ((14131666471 : ℚ) / 31250000000) ≤ ((113053308143 : ℚ) / 250000000000) + (3253:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((14131666471 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((113053308143 : ℚ) / 250000000000) : ℚ) : ℝ) + ((3253:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3253:ℚ)^(-2:ℤ) : ℝ) = ((3253:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_459 : ((((22610671067 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3257, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3253 < q → q < 3257 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3257).mp (by decide +kernel))) hgap
  have hprev := s2L_458
  have hrat : ((22610671067 : ℚ) / 50000000000) ≤ ((14131666471 : ℚ) / 31250000000) + (3257:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22610671067 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((14131666471 : ℚ) / 31250000000) : ℚ) : ℝ) + ((3257:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3257:ℚ)^(-2:ℤ) : ℝ) = ((3257:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_460 : ((((113053378873 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3259, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3257 < q → q < 3259 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3259).mp (by decide +kernel))) hgap
  have hprev := s2L_459
  have hrat : ((113053378873 : ℚ) / 250000000000) ≤ ((22610671067 : ℚ) / 50000000000) + (3259:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113053378873 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((22610671067 : ℚ) / 50000000000) : ℚ) : ℝ) + ((3259:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3259:ℚ)^(-2:ℤ) : ℝ) = ((3259:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_461 : ((((226106804477 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3271, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3259 < q → q < 3271 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3271).mp (by decide +kernel))) hgap
  have hprev := s2L_460
  have hrat : ((226106804477 : ℚ) / 500000000000) ≤ ((113053378873 : ℚ) / 250000000000) + (3271:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226106804477 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113053378873 : ℚ) / 250000000000) : ℚ) : ℝ) + ((3271:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3271:ℚ)^(-2:ℤ) : ℝ) = ((3271:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_462 : ((((452213700837 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3299, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3271 < q → q < 3299 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3299).mp (by decide +kernel))) hgap
  have hprev := s2L_461
  have hrat : ((452213700837 : ℚ) / 1000000000000) ≤ ((226106804477 : ℚ) / 500000000000) + (3299:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452213700837 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226106804477 : ℚ) / 500000000000) : ℚ) : ℝ) + ((3299:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3299:ℚ)^(-2:ℤ) : ℝ) = ((3299:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_463 : ((((14131681019 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3301, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3299 < q → q < 3301 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3301).mp (by decide +kernel))) hgap
  have hprev := s2L_462
  have hrat : ((14131681019 : ℚ) / 31250000000) ≤ ((452213700837 : ℚ) / 1000000000000) + (3301:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((14131681019 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((452213700837 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((3301:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3301:ℚ)^(-2:ℤ) : ℝ) = ((3301:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_464 : ((((452213884047 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3307, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3301 < q → q < 3307 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3307).mp (by decide +kernel))) hgap
  have hprev := s2L_463
  have hrat : ((452213884047 : ℚ) / 1000000000000) ≤ ((14131681019 : ℚ) / 31250000000) + (3307:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452213884047 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((14131681019 : ℚ) / 31250000000) : ℚ) : ℝ) + ((3307:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3307:ℚ)^(-2:ℤ) : ℝ) = ((3307:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_465 : ((((90442795031 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3313, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3307 < q → q < 3313 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3313).mp (by decide +kernel))) hgap
  have hprev := s2L_464
  have hrat : ((90442795031 : ℚ) / 200000000000) ≤ ((452213884047 : ℚ) / 1000000000000) + (3313:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90442795031 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452213884047 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((3313:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3313:ℚ)^(-2:ℤ) : ℝ) = ((3313:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_466 : ((((226107032967 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3319, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3313 < q → q < 3319 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3319).mp (by decide +kernel))) hgap
  have hprev := s2L_465
  have hrat : ((226107032967 : ℚ) / 500000000000) ≤ ((90442795031 : ℚ) / 200000000000) + (3319:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226107032967 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((90442795031 : ℚ) / 200000000000) : ℚ) : ℝ) + ((3319:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3319:ℚ)^(-2:ℤ) : ℝ) = ((3319:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_467 : ((((226107078247 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3323, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3319 < q → q < 3323 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3323).mp (by decide +kernel))) hgap
  have hprev := s2L_466
  have hrat : ((226107078247 : ℚ) / 500000000000) ≤ ((226107032967 : ℚ) / 500000000000) + (3323:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226107078247 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226107032967 : ℚ) / 500000000000) : ℚ) : ℝ) + ((3323:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3323:ℚ)^(-2:ℤ) : ℝ) = ((3323:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_468 : ((((56526780841 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3329, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3323 < q → q < 3329 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3329).mp (by decide +kernel))) hgap
  have hprev := s2L_467
  have hrat : ((56526780841 : ℚ) / 125000000000) ≤ ((226107078247 : ℚ) / 500000000000) + (3329:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56526780841 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((226107078247 : ℚ) / 500000000000) : ℚ) : ℝ) + ((3329:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3329:ℚ)^(-2:ℤ) : ℝ) = ((3329:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_469 : ((((226107168427 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3331, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3329 < q → q < 3331 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3331).mp (by decide +kernel))) hgap
  have hprev := s2L_468
  have hrat : ((226107168427 : ℚ) / 500000000000) ≤ ((56526780841 : ℚ) / 125000000000) + (3331:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226107168427 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((56526780841 : ℚ) / 125000000000) : ℚ) : ℝ) + ((3331:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3331:ℚ)^(-2:ℤ) : ℝ) = ((3331:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_470 : ((((226107213167 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3343, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3331 < q → q < 3343 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3343).mp (by decide +kernel))) hgap
  have hprev := s2L_469
  have hrat : ((226107213167 : ℚ) / 500000000000) ≤ ((226107168427 : ℚ) / 500000000000) + (3343:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226107213167 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226107168427 : ℚ) / 500000000000) : ℚ) : ℝ) + ((3343:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3343:ℚ)^(-2:ℤ) : ℝ) = ((3343:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_471 : ((((1130536289 : ℚ) / 2500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3347, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3343 < q → q < 3347 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3347).mp (by decide +kernel))) hgap
  have hprev := s2L_470
  have hrat : ((1130536289 : ℚ) / 2500000000) ≤ ((226107213167 : ℚ) / 500000000000) + (3347:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((1130536289 : ℚ) / 2500000000) : ℚ) : ℝ) ≤ ((((226107213167 : ℚ) / 500000000000) : ℚ) : ℝ) + ((3347:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3347:ℚ)^(-2:ℤ) : ℝ) = ((3347:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_472 : ((((452214604229 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3359, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3347 < q → q < 3359 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3359).mp (by decide +kernel))) hgap
  have hprev := s2L_471
  have hrat : ((452214604229 : ℚ) / 1000000000000) ≤ ((1130536289 : ℚ) / 2500000000) + (3359:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452214604229 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1130536289 : ℚ) / 2500000000) : ℚ) : ℝ) + ((3359:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3359:ℚ)^(-2:ℤ) : ℝ) = ((3359:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_473 : ((((452214692753 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3361, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3359 < q → q < 3361 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3361).mp (by decide +kernel))) hgap
  have hprev := s2L_472
  have hrat : ((452214692753 : ℚ) / 1000000000000) ≤ ((452214604229 : ℚ) / 1000000000000) + (3361:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452214692753 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452214604229 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((3361:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3361:ℚ)^(-2:ℤ) : ℝ) = ((3361:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_474 : ((((28263423797 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3371, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3361 < q → q < 3371 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3371).mp (by decide +kernel))) hgap
  have hprev := s2L_473
  have hrat : ((28263423797 : ℚ) / 62500000000) ≤ ((452214692753 : ℚ) / 1000000000000) + (3371:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28263423797 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((452214692753 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((3371:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3371:ℚ)^(-2:ℤ) : ℝ) = ((3371:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_475 : ((((452214868647 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3373, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3371 < q → q < 3373 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3373).mp (by decide +kernel))) hgap
  have hprev := s2L_474
  have hrat : ((452214868647 : ℚ) / 1000000000000) ≤ ((28263423797 : ℚ) / 62500000000) + (3373:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452214868647 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((28263423797 : ℚ) / 62500000000) : ℚ) : ℝ) + ((3373:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3373:ℚ)^(-2:ℤ) : ℝ) = ((3373:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_476 : ((((226107477857 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3389, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3373 < q → q < 3389 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3389).mp (by decide +kernel))) hgap
  have hprev := s2L_475
  have hrat : ((226107477857 : ℚ) / 500000000000) ≤ ((452214868647 : ℚ) / 1000000000000) + (3389:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226107477857 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452214868647 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((3389:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3389:ℚ)^(-2:ℤ) : ℝ) = ((3389:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_477 : ((((226107521339 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3391, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3389 < q → q < 3391 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3391).mp (by decide +kernel))) hgap
  have hprev := s2L_476
  have hrat : ((226107521339 : ℚ) / 500000000000) ≤ ((226107477857 : ℚ) / 500000000000) + (3391:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226107521339 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226107477857 : ℚ) / 500000000000) : ℚ) : ℝ) + ((3391:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3391:ℚ)^(-2:ℤ) : ℝ) = ((3391:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_478 : ((((113053782207 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3407, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3391 < q → q < 3407 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3407).mp (by decide +kernel))) hgap
  have hprev := s2L_477
  have hrat : ((113053782207 : ℚ) / 250000000000) ≤ ((226107521339 : ℚ) / 500000000000) + (3407:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113053782207 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226107521339 : ℚ) / 500000000000) : ℚ) : ℝ) + ((3407:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3407:ℚ)^(-2:ℤ) : ℝ) = ((3407:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_479 : ((((18088608587 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3413, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3407 < q → q < 3413 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3413).mp (by decide +kernel))) hgap
  have hprev := s2L_478
  have hrat : ((18088608587 : ℚ) / 40000000000) ≤ ((113053782207 : ℚ) / 250000000000) + (3413:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18088608587 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((113053782207 : ℚ) / 250000000000) : ℚ) : ℝ) + ((3413:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3413:ℚ)^(-2:ℤ) : ℝ) = ((3413:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_480 : ((((18088611981 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3433, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3413 < q → q < 3433 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3433).mp (by decide +kernel))) hgap
  have hprev := s2L_479
  have hrat : ((18088611981 : ℚ) / 40000000000) ≤ ((18088608587 : ℚ) / 40000000000) + (3433:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18088611981 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((18088608587 : ℚ) / 40000000000) : ℚ) : ℝ) + ((3433:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3433:ℚ)^(-2:ℤ) : ℝ) = ((3433:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_481 : ((((452215383589 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3449, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3433 < q → q < 3449 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3449).mp (by decide +kernel))) hgap
  have hprev := s2L_480
  have hrat : ((452215383589 : ℚ) / 1000000000000) ≤ ((18088611981 : ℚ) / 40000000000) + (3449:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452215383589 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((18088611981 : ℚ) / 40000000000) : ℚ) : ℝ) + ((3449:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3449:ℚ)^(-2:ℤ) : ℝ) = ((3449:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_482 : ((((90443093453 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3457, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3449 < q → q < 3457 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3457).mp (by decide +kernel))) hgap
  have hprev := s2L_481
  have hrat : ((90443093453 : ℚ) / 200000000000) ≤ ((452215383589 : ℚ) / 1000000000000) + (3457:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90443093453 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452215383589 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((3457:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3457:ℚ)^(-2:ℤ) : ℝ) = ((3457:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_483 : ((((452215550747 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3461, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3457 < q → q < 3461 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3461).mp (by decide +kernel))) hgap
  have hprev := s2L_482
  have hrat : ((452215550747 : ℚ) / 1000000000000) ≤ ((90443093453 : ℚ) / 200000000000) + (3461:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452215550747 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90443093453 : ℚ) / 200000000000) : ℚ) : ℝ) + ((3461:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3461:ℚ)^(-2:ℤ) : ℝ) = ((3461:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_484 : ((((452215634133 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3463, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3461 < q → q < 3463 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3463).mp (by decide +kernel))) hgap
  have hprev := s2L_483
  have hrat : ((452215634133 : ℚ) / 1000000000000) ≤ ((452215550747 : ℚ) / 1000000000000) + (3463:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452215634133 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452215550747 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((3463:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3463:ℚ)^(-2:ℤ) : ℝ) = ((3463:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_485 : ((((452215717327 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3467, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3463 < q → q < 3467 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3467).mp (by decide +kernel))) hgap
  have hprev := s2L_484
  have hrat : ((452215717327 : ℚ) / 1000000000000) ≤ ((452215634133 : ℚ) / 1000000000000) + (3467:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452215717327 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452215634133 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((3467:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3467:ℚ)^(-2:ℤ) : ℝ) = ((3467:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_486 : ((((18088632017 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3469, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3467 < q → q < 3469 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3469).mp (by decide +kernel))) hgap
  have hprev := s2L_485
  have hrat : ((18088632017 : ℚ) / 40000000000) ≤ ((452215717327 : ℚ) / 1000000000000) + (3469:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18088632017 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((452215717327 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((3469:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3469:ℚ)^(-2:ℤ) : ℝ) = ((3469:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_487 : ((((452215882479 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3491, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3469 < q → q < 3491 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3491).mp (by decide +kernel))) hgap
  have hprev := s2L_486
  have hrat : ((452215882479 : ℚ) / 1000000000000) ≤ ((18088632017 : ℚ) / 40000000000) + (3491:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452215882479 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((18088632017 : ℚ) / 40000000000) : ℚ) : ℝ) + ((3491:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3491:ℚ)^(-2:ℤ) : ℝ) = ((3491:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_488 : ((((226107982079 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3499, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3491 < q → q < 3499 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3499).mp (by decide +kernel))) hgap
  have hprev := s2L_487
  have hrat : ((226107982079 : ℚ) / 500000000000) ≤ ((452215882479 : ℚ) / 1000000000000) + (3499:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226107982079 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452215882479 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((3499:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3499:ℚ)^(-2:ℤ) : ℝ) = ((3499:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_489 : ((((452216045279 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3511, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3499 < q → q < 3511 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3511).mp (by decide +kernel))) hgap
  have hprev := s2L_488
  have hrat : ((452216045279 : ℚ) / 1000000000000) ≤ ((226107982079 : ℚ) / 500000000000) + (3511:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452216045279 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226107982079 : ℚ) / 500000000000) : ℚ) : ℝ) + ((3511:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3511:ℚ)^(-2:ℤ) : ℝ) = ((3511:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_490 : ((((113054031531 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3517, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3511 < q → q < 3517 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3517).mp (by decide +kernel))) hgap
  have hprev := s2L_489
  have hrat : ((113054031531 : ℚ) / 250000000000) ≤ ((452216045279 : ℚ) / 1000000000000) + (3517:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113054031531 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452216045279 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((3517:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3517:ℚ)^(-2:ℤ) : ℝ) = ((3517:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_491 : ((((452216206511 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3527, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3517 < q → q < 3527 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3527).mp (by decide +kernel))) hgap
  have hprev := s2L_490
  have hrat : ((452216206511 : ℚ) / 1000000000000) ≤ ((113054031531 : ℚ) / 250000000000) + (3527:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452216206511 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113054031531 : ℚ) / 250000000000) : ℚ) : ℝ) + ((3527:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3527:ℚ)^(-2:ℤ) : ℝ) = ((3527:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_492 : ((((452216286807 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3529, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3527 < q → q < 3529 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3529).mp (by decide +kernel))) hgap
  have hprev := s2L_491
  have hrat : ((452216286807 : ℚ) / 1000000000000) ≤ ((452216206511 : ℚ) / 1000000000000) + (3529:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452216286807 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452216206511 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((3529:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3529:ℚ)^(-2:ℤ) : ℝ) = ((3529:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_493 : ((((452216366921 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3533, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3529 < q → q < 3533 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3533).mp (by decide +kernel))) hgap
  have hprev := s2L_492
  have hrat : ((452216366921 : ℚ) / 1000000000000) ≤ ((452216286807 : ℚ) / 1000000000000) + (3533:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452216366921 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452216286807 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((3533:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3533:ℚ)^(-2:ℤ) : ℝ) = ((3533:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_494 : ((((113054111691 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3539, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3533 < q → q < 3539 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3539).mp (by decide +kernel))) hgap
  have hprev := s2L_493
  have hrat : ((113054111691 : ℚ) / 250000000000) ≤ ((452216366921 : ℚ) / 1000000000000) + (3539:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113054111691 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452216366921 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((3539:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3539:ℚ)^(-2:ℤ) : ℝ) = ((3539:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_495 : ((((452216526517 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3541, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3539 < q → q < 3541 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3541).mp (by decide +kernel))) hgap
  have hprev := s2L_494
  have hrat : ((452216526517 : ℚ) / 1000000000000) ≤ ((113054111691 : ℚ) / 250000000000) + (3541:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452216526517 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113054111691 : ℚ) / 250000000000) : ℚ) : ℝ) + ((3541:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3541:ℚ)^(-2:ℤ) : ℝ) = ((3541:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_496 : ((((226108303 : ℚ) / 500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3547, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3541 < q → q < 3547 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3547).mp (by decide +kernel))) hgap
  have hprev := s2L_495
  have hrat : ((226108303 : ℚ) / 500000000) ≤ ((452216526517 : ℚ) / 1000000000000) + (3547:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226108303 : ℚ) / 500000000) : ℚ) : ℝ) ≤ ((((452216526517 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((3547:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3547:ℚ)^(-2:ℤ) : ℝ) = ((3547:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_497 : ((((452216685037 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3557, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3547 < q → q < 3557 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3557).mp (by decide +kernel))) hgap
  have hprev := s2L_496
  have hrat : ((452216685037 : ℚ) / 1000000000000) ≤ ((226108303 : ℚ) / 500000000) + (3557:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452216685037 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226108303 : ℚ) / 500000000) : ℚ) : ℝ) + ((3557:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3557:ℚ)^(-2:ℤ) : ℝ) = ((3557:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_498 : ((((90443352797 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3559, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3557 < q → q < 3559 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3559).mp (by decide +kernel))) hgap
  have hprev := s2L_497
  have hrat : ((90443352797 : ℚ) / 200000000000) ≤ ((452216685037 : ℚ) / 1000000000000) + (3559:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90443352797 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452216685037 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((3559:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3559:ℚ)^(-2:ℤ) : ℝ) = ((3559:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_499 : ((((452216842403 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3571, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3559 < q → q < 3571 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3571).mp (by decide +kernel))) hgap
  have hprev := s2L_498
  have hrat : ((452216842403 : ℚ) / 1000000000000) ≤ ((90443352797 : ℚ) / 200000000000) + (3571:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452216842403 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90443352797 : ℚ) / 200000000000) : ℚ) : ℝ) + ((3571:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3571:ℚ)^(-2:ℤ) : ℝ) = ((3571:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_500 : ((((7065889381 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3581, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3571 < q → q < 3581 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3581).mp (by decide +kernel))) hgap
  have hprev := s2L_499
  have hrat : ((7065889381 : ℚ) / 15625000000) ≤ ((452216842403 : ℚ) / 1000000000000) + (3581:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((7065889381 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ ((((452216842403 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((3581:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3581:ℚ)^(-2:ℤ) : ℝ) = ((3581:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_501 : ((((226108499139 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3583, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3581 < q → q < 3583 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3583).mp (by decide +kernel))) hgap
  have hprev := s2L_500
  have hrat : ((226108499139 : ℚ) / 500000000000) ≤ ((7065889381 : ℚ) / 15625000000) + (3583:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226108499139 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((7065889381 : ℚ) / 15625000000) : ℚ) : ℝ) + ((3583:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3583:ℚ)^(-2:ℤ) : ℝ) = ((3583:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_502 : ((((452217075739 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3593, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3583 < q → q < 3593 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3593).mp (by decide +kernel))) hgap
  have hprev := s2L_501
  have hrat : ((452217075739 : ℚ) / 1000000000000) ≤ ((226108499139 : ℚ) / 500000000000) + (3593:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452217075739 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226108499139 : ℚ) / 500000000000) : ℚ) : ℝ) + ((3593:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3593:ℚ)^(-2:ℤ) : ℝ) = ((3593:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_503 : ((((2261085763 : ℚ) / 5000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3607, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3593 < q → q < 3607 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3607).mp (by decide +kernel))) hgap
  have hprev := s2L_502
  have hrat : ((2261085763 : ℚ) / 5000000000) ≤ ((452217075739 : ℚ) / 1000000000000) + (3607:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((2261085763 : ℚ) / 5000000000) : ℚ) : ℝ) ≤ ((((452217075739 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((3607:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3607:ℚ)^(-2:ℤ) : ℝ) = ((3607:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_504 : ((((226108614603 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3613, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3607 < q → q < 3613 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3613).mp (by decide +kernel))) hgap
  have hprev := s2L_503
  have hrat : ((226108614603 : ℚ) / 500000000000) ≤ ((2261085763 : ℚ) / 5000000000) + (3613:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226108614603 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((2261085763 : ℚ) / 5000000000) : ℚ) : ℝ) + ((3613:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3613:ℚ)^(-2:ℤ) : ℝ) = ((3613:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_505 : ((((226108652821 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3617, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3613 < q → q < 3617 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3617).mp (by decide +kernel))) hgap
  have hprev := s2L_504
  have hrat : ((226108652821 : ℚ) / 500000000000) ≤ ((226108614603 : ℚ) / 500000000000) + (3617:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226108652821 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226108614603 : ℚ) / 500000000000) : ℚ) : ℝ) + ((3617:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3617:ℚ)^(-2:ℤ) : ℝ) = ((3617:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_506 : ((((18088695273 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3623, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3617 < q → q < 3623 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3623).mp (by decide +kernel))) hgap
  have hprev := s2L_505
  have hrat : ((18088695273 : ℚ) / 40000000000) ≤ ((226108652821 : ℚ) / 500000000000) + (3623:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18088695273 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((226108652821 : ℚ) / 500000000000) : ℚ) : ℝ) + ((3623:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3623:ℚ)^(-2:ℤ) : ℝ) = ((3623:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_507 : ((((452217457673 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3631, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3623 < q → q < 3631 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3631).mp (by decide +kernel))) hgap
  have hprev := s2L_506
  have hrat : ((452217457673 : ℚ) / 1000000000000) ≤ ((18088695273 : ℚ) / 40000000000) + (3631:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452217457673 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((18088695273 : ℚ) / 40000000000) : ℚ) : ℝ) + ((3631:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3631:ℚ)^(-2:ℤ) : ℝ) = ((3631:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_508 : ((((452217533271 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3637, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3631 < q → q < 3637 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3637).mp (by decide +kernel))) hgap
  have hprev := s2L_507
  have hrat : ((452217533271 : ℚ) / 1000000000000) ≤ ((452217457673 : ℚ) / 1000000000000) + (3637:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452217533271 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452217457673 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((3637:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3637:ℚ)^(-2:ℤ) : ℝ) = ((3637:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_509 : ((((22610880431 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3643, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3637 < q → q < 3643 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3643).mp (by decide +kernel))) hgap
  have hprev := s2L_508
  have hrat : ((22610880431 : ℚ) / 50000000000) ≤ ((452217533271 : ℚ) / 1000000000000) + (3643:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22610880431 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((452217533271 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((3643:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3643:ℚ)^(-2:ℤ) : ℝ) = ((3643:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_510 : ((((28263605207 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3659, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3643 < q → q < 3659 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3659).mp (by decide +kernel))) hgap
  have hprev := s2L_509
  have hrat : ((28263605207 : ℚ) / 62500000000) ≤ ((22610880431 : ℚ) / 50000000000) + (3659:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28263605207 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((22610880431 : ℚ) / 50000000000) : ℚ) : ℝ) + ((3659:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3659:ℚ)^(-2:ℤ) : ℝ) = ((3659:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_511 : ((((113054439379 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3671, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3659 < q → q < 3671 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3671).mp (by decide +kernel))) hgap
  have hprev := s2L_510
  have hrat : ((113054439379 : ℚ) / 250000000000) ≤ ((28263605207 : ℚ) / 62500000000) + (3671:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113054439379 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((28263605207 : ℚ) / 62500000000) : ℚ) : ℝ) + ((3671:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3671:ℚ)^(-2:ℤ) : ℝ) = ((3671:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_512 : ((((452217831639 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3673, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3671 < q → q < 3673 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3673).mp (by decide +kernel))) hgap
  have hprev := s2L_511
  have hrat : ((452217831639 : ℚ) / 1000000000000) ≤ ((113054439379 : ℚ) / 250000000000) + (3673:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452217831639 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113054439379 : ℚ) / 250000000000) : ℚ) : ℝ) + ((3673:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3673:ℚ)^(-2:ℤ) : ℝ) = ((3673:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_513 : ((((452217905601 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3677, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3673 < q → q < 3677 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3677).mp (by decide +kernel))) hgap
  have hprev := s2L_512
  have hrat : ((452217905601 : ℚ) / 1000000000000) ≤ ((452217831639 : ℚ) / 1000000000000) + (3677:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452217905601 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452217831639 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((3677:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3677:ℚ)^(-2:ℤ) : ℝ) = ((3677:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_514 : ((((452217979003 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3691, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3677 < q → q < 3691 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3691).mp (by decide +kernel))) hgap
  have hprev := s2L_513
  have hrat : ((452217979003 : ℚ) / 1000000000000) ≤ ((452217905601 : ℚ) / 1000000000000) + (3691:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452217979003 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452217905601 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((3691:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3691:ℚ)^(-2:ℤ) : ℝ) = ((3691:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_515 : ((((452218052167 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3697, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3691 < q → q < 3697 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3697).mp (by decide +kernel))) hgap
  have hprev := s2L_514
  have hrat : ((452218052167 : ℚ) / 1000000000000) ≤ ((452217979003 : ℚ) / 1000000000000) + (3697:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452218052167 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452217979003 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((3697:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3697:ℚ)^(-2:ℤ) : ℝ) = ((3697:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_516 : ((((452218125173 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3701, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3697 < q → q < 3701 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3701).mp (by decide +kernel))) hgap
  have hprev := s2L_515
  have hrat : ((452218125173 : ℚ) / 1000000000000) ≤ ((452218052167 : ℚ) / 1000000000000) + (3701:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452218125173 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452218052167 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((3701:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3701:ℚ)^(-2:ℤ) : ℝ) = ((3701:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_517 : ((((56527274733 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3709, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3701 < q → q < 3709 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3709).mp (by decide +kernel))) hgap
  have hprev := s2L_516
  have hrat : ((56527274733 : ℚ) / 125000000000) ≤ ((452218125173 : ℚ) / 1000000000000) + (3709:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56527274733 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452218125173 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((3709:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3709:ℚ)^(-2:ℤ) : ℝ) = ((3709:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_518 : ((((90443654033 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3719, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3709 < q → q < 3719 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3719).mp (by decide +kernel))) hgap
  have hprev := s2L_517
  have hrat : ((90443654033 : ℚ) / 200000000000) ≤ ((56527274733 : ℚ) / 125000000000) + (3719:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90443654033 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((56527274733 : ℚ) / 125000000000) : ℚ) : ℝ) + ((3719:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3719:ℚ)^(-2:ℤ) : ℝ) = ((3719:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_519 : ((((113054585539 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3727, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3719 < q → q < 3727 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3727).mp (by decide +kernel))) hgap
  have hprev := s2L_518
  have hrat : ((113054585539 : ℚ) / 250000000000) ≤ ((90443654033 : ℚ) / 200000000000) + (3727:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113054585539 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((90443654033 : ℚ) / 200000000000) : ℚ) : ℝ) + ((3727:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3727:ℚ)^(-2:ℤ) : ℝ) = ((3727:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_520 : ((((113054603479 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3733, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3727 < q → q < 3733 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3733).mp (by decide +kernel))) hgap
  have hprev := s2L_519
  have hrat : ((113054603479 : ℚ) / 250000000000) ≤ ((113054585539 : ℚ) / 250000000000) + (3733:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113054603479 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((113054585539 : ℚ) / 250000000000) : ℚ) : ℝ) + ((3733:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3733:ℚ)^(-2:ℤ) : ℝ) = ((3733:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_521 : ((((226109242723 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3739, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3733 < q → q < 3739 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3739).mp (by decide +kernel))) hgap
  have hprev := s2L_520
  have hrat : ((226109242723 : ℚ) / 500000000000) ≤ ((113054603479 : ℚ) / 250000000000) + (3739:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226109242723 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113054603479 : ℚ) / 250000000000) : ℚ) : ℝ) + ((3739:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3739:ℚ)^(-2:ℤ) : ℝ) = ((3739:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_522 : ((((452218556141 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3761, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3739 < q → q < 3761 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3761).mp (by decide +kernel))) hgap
  have hprev := s2L_521
  have hrat : ((452218556141 : ℚ) / 1000000000000) ≤ ((226109242723 : ℚ) / 500000000000) + (3761:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452218556141 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226109242723 : ℚ) / 500000000000) : ℚ) : ℝ) + ((3761:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3761:ℚ)^(-2:ℤ) : ℝ) = ((3761:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_523 : ((((452218626611 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3767, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3761 < q → q < 3767 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3767).mp (by decide +kernel))) hgap
  have hprev := s2L_522
  have hrat : ((452218626611 : ℚ) / 1000000000000) ≤ ((452218556141 : ℚ) / 1000000000000) + (3767:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452218626611 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452218556141 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((3767:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3767:ℚ)^(-2:ℤ) : ℝ) = ((3767:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_524 : ((((226109348503 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3769, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3767 < q → q < 3769 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3769).mp (by decide +kernel))) hgap
  have hprev := s2L_523
  have hrat : ((226109348503 : ℚ) / 500000000000) ≤ ((452218626611 : ℚ) / 1000000000000) + (3769:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226109348503 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452218626611 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((3769:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3769:ℚ)^(-2:ℤ) : ℝ) = ((3769:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_525 : ((((452218767029 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3779, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3769 < q → q < 3779 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3779).mp (by decide +kernel))) hgap
  have hprev := s2L_524
  have hrat : ((452218767029 : ℚ) / 1000000000000) ≤ ((226109348503 : ℚ) / 500000000000) + (3779:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452218767029 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226109348503 : ℚ) / 500000000000) : ℚ) : ℝ) + ((3779:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3779:ℚ)^(-2:ℤ) : ℝ) = ((3779:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_526 : ((((56527354567 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3793, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3779 < q → q < 3793 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3793).mp (by decide +kernel))) hgap
  have hprev := s2L_525
  have hrat : ((56527354567 : ℚ) / 125000000000) ≤ ((452218767029 : ℚ) / 1000000000000) + (3793:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56527354567 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452218767029 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((3793:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3793:ℚ)^(-2:ℤ) : ℝ) = ((3793:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_527 : ((((452218905897 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3797, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3793 < q → q < 3797 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3797).mp (by decide +kernel))) hgap
  have hprev := s2L_526
  have hrat : ((452218905897 : ℚ) / 1000000000000) ≤ ((56527354567 : ℚ) / 125000000000) + (3797:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452218905897 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56527354567 : ℚ) / 125000000000) : ℚ) : ℝ) + ((3797:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3797:ℚ)^(-2:ℤ) : ℝ) = ((3797:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_528 : ((((452218975039 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3803, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3797 < q → q < 3803 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3803).mp (by decide +kernel))) hgap
  have hprev := s2L_527
  have hrat : ((452218975039 : ℚ) / 1000000000000) ≤ ((452218905897 : ℚ) / 1000000000000) + (3803:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452218975039 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452218905897 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((3803:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3803:ℚ)^(-2:ℤ) : ℝ) = ((3803:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_529 : ((((452219043531 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3821, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3803 < q → q < 3821 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3821).mp (by decide +kernel))) hgap
  have hprev := s2L_528
  have hrat : ((452219043531 : ℚ) / 1000000000000) ≤ ((452218975039 : ℚ) / 1000000000000) + (3821:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452219043531 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452218975039 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((3821:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3821:ℚ)^(-2:ℤ) : ℝ) = ((3821:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_530 : ((((28263694497 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3823, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3821 < q → q < 3823 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3823).mp (by decide +kernel))) hgap
  have hprev := s2L_529
  have hrat : ((28263694497 : ℚ) / 62500000000) ≤ ((452219043531 : ℚ) / 1000000000000) + (3823:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28263694497 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((452219043531 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((3823:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3823:ℚ)^(-2:ℤ) : ℝ) = ((3823:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_531 : ((((28263698751 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3833, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3823 < q → q < 3833 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3833).mp (by decide +kernel))) hgap
  have hprev := s2L_530
  have hrat : ((28263698751 : ℚ) / 62500000000) ≤ ((28263694497 : ℚ) / 62500000000) + (3833:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28263698751 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((28263694497 : ℚ) / 62500000000) : ℚ) : ℝ) + ((3833:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3833:ℚ)^(-2:ℤ) : ℝ) = ((3833:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_532 : ((((226109623793 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3847, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3833 < q → q < 3847 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3847).mp (by decide +kernel))) hgap
  have hprev := s2L_531
  have hrat : ((226109623793 : ℚ) / 500000000000) ≤ ((28263698751 : ℚ) / 62500000000) + (3847:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226109623793 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((28263698751 : ℚ) / 62500000000) : ℚ) : ℝ) + ((3847:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3847:ℚ)^(-2:ℤ) : ℝ) = ((3847:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_533 : ((((90443863003 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3851, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3847 < q → q < 3851 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3851).mp (by decide +kernel))) hgap
  have hprev := s2L_532
  have hrat : ((90443863003 : ℚ) / 200000000000) ≤ ((226109623793 : ℚ) / 500000000000) + (3851:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90443863003 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((226109623793 : ℚ) / 500000000000) : ℚ) : ℝ) + ((3851:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3851:ℚ)^(-2:ℤ) : ℝ) = ((3851:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_534 : ((((226109691187 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3853, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3851 < q → q < 3853 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3853).mp (by decide +kernel))) hgap
  have hprev := s2L_533
  have hrat : ((226109691187 : ℚ) / 500000000000) ≤ ((90443863003 : ℚ) / 200000000000) + (3853:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226109691187 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((90443863003 : ℚ) / 200000000000) : ℚ) : ℝ) + ((3853:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3853:ℚ)^(-2:ℤ) : ℝ) = ((3853:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_535 : ((((90443889877 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3863, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3853 < q → q < 3863 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3863).mp (by decide +kernel))) hgap
  have hprev := s2L_534
  have hrat : ((90443889877 : ℚ) / 200000000000) ≤ ((226109691187 : ℚ) / 500000000000) + (3863:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90443889877 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((226109691187 : ℚ) / 500000000000) : ℚ) : ℝ) + ((3863:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3863:ℚ)^(-2:ℤ) : ℝ) = ((3863:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_536 : ((((452219515913 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3877, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3863 < q → q < 3877 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3877).mp (by decide +kernel))) hgap
  have hprev := s2L_535
  have hrat : ((452219515913 : ℚ) / 1000000000000) ≤ ((90443889877 : ℚ) / 200000000000) + (3877:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452219515913 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90443889877 : ℚ) / 200000000000) : ℚ) : ℝ) + ((3877:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3877:ℚ)^(-2:ℤ) : ℝ) = ((3877:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_537 : ((((14131861947 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3881, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3877 < q → q < 3881 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3881).mp (by decide +kernel))) hgap
  have hprev := s2L_536
  have hrat : ((14131861947 : ℚ) / 31250000000) ≤ ((452219515913 : ℚ) / 1000000000000) + (3881:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((14131861947 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((452219515913 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((3881:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3881:ℚ)^(-2:ℤ) : ℝ) = ((3881:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_538 : ((((226109824211 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3889, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3881 < q → q < 3889 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3889).mp (by decide +kernel))) hgap
  have hprev := s2L_537
  have hrat : ((226109824211 : ℚ) / 500000000000) ≤ ((14131861947 : ℚ) / 31250000000) + (3889:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226109824211 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((14131861947 : ℚ) / 31250000000) : ℚ) : ℝ) + ((3889:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3889:ℚ)^(-2:ℤ) : ℝ) = ((3889:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_539 : ((((113054928483 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3907, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3889 < q → q < 3907 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3907).mp (by decide +kernel))) hgap
  have hprev := s2L_538
  have hrat : ((113054928483 : ℚ) / 250000000000) ≤ ((226109824211 : ℚ) / 500000000000) + (3907:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113054928483 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226109824211 : ℚ) / 500000000000) : ℚ) : ℝ) + ((3907:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3907:ℚ)^(-2:ℤ) : ℝ) = ((3907:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_540 : ((((113054944827 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3911, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3907 < q → q < 3911 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3911).mp (by decide +kernel))) hgap
  have hprev := s2L_539
  have hrat : ((113054944827 : ℚ) / 250000000000) ≤ ((113054928483 : ℚ) / 250000000000) + (3911:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113054944827 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((113054928483 : ℚ) / 250000000000) : ℚ) : ℝ) + ((3911:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3911:ℚ)^(-2:ℤ) : ℝ) = ((3911:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_541 : ((((113054961121 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3917, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3911 < q → q < 3917 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3917).mp (by decide +kernel))) hgap
  have hprev := s2L_540
  have hrat : ((113054961121 : ℚ) / 250000000000) ≤ ((113054944827 : ℚ) / 250000000000) + (3917:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113054961121 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((113054944827 : ℚ) / 250000000000) : ℚ) : ℝ) + ((3917:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3917:ℚ)^(-2:ℤ) : ℝ) = ((3917:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_542 : ((((226109954797 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3919, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3917 < q → q < 3919 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3919).mp (by decide +kernel))) hgap
  have hprev := s2L_541
  have hrat : ((226109954797 : ℚ) / 500000000000) ≤ ((113054961121 : ℚ) / 250000000000) + (3919:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226109954797 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113054961121 : ℚ) / 250000000000) : ℚ) : ℝ) + ((3919:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3919:ℚ)^(-2:ℤ) : ℝ) = ((3919:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_543 : ((((452219974571 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3923, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3919 < q → q < 3923 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3923).mp (by decide +kernel))) hgap
  have hprev := s2L_542
  have hrat : ((452219974571 : ℚ) / 1000000000000) ≤ ((226109954797 : ℚ) / 500000000000) + (3923:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452219974571 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226109954797 : ℚ) / 500000000000) : ℚ) : ℝ) + ((3923:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3923:ℚ)^(-2:ℤ) : ℝ) = ((3923:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_544 : ((((9044400787 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3929, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3923 < q → q < 3929 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3929).mp (by decide +kernel))) hgap
  have hprev := s2L_543
  have hrat : ((9044400787 : ℚ) / 20000000000) ≤ ((452219974571 : ℚ) / 1000000000000) + (3929:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((9044400787 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ ((((452219974571 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((3929:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3929:ℚ)^(-2:ℤ) : ℝ) = ((3929:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_545 : ((((452220104063 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3931, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3929 < q → q < 3931 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3931).mp (by decide +kernel))) hgap
  have hprev := s2L_544
  have hrat : ((452220104063 : ℚ) / 1000000000000) ≤ ((9044400787 : ℚ) / 20000000000) + (3931:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452220104063 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((9044400787 : ℚ) / 20000000000) : ℚ) : ℝ) + ((3931:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3931:ℚ)^(-2:ℤ) : ℝ) = ((3931:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_546 : ((((452220168383 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3943, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3931 < q → q < 3943 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3943).mp (by decide +kernel))) hgap
  have hprev := s2L_545
  have hrat : ((452220168383 : ℚ) / 1000000000000) ≤ ((452220104063 : ℚ) / 1000000000000) + (3943:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452220168383 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452220104063 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((3943:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3943:ℚ)^(-2:ℤ) : ℝ) = ((3943:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_547 : ((((113055058143 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3947, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3943 < q → q < 3947 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3947).mp (by decide +kernel))) hgap
  have hprev := s2L_546
  have hrat : ((113055058143 : ℚ) / 250000000000) ≤ ((452220168383 : ℚ) / 1000000000000) + (3947:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113055058143 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452220168383 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((3947:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3947:ℚ)^(-2:ℤ) : ℝ) = ((3947:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_548 : ((((113055074029 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3967, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3947 < q → q < 3967 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3967).mp (by decide +kernel))) hgap
  have hprev := s2L_547
  have hrat : ((113055074029 : ℚ) / 250000000000) ≤ ((113055058143 : ℚ) / 250000000000) + (3967:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113055074029 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((113055058143 : ℚ) / 250000000000) : ℚ) : ℝ) + ((3967:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3967:ℚ)^(-2:ℤ) : ℝ) = ((3967:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_549 : ((((452220358961 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 3989, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3967 < q → q < 3989 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 3989).mp (by decide +kernel))) hgap
  have hprev := s2L_548
  have hrat : ((452220358961 : ℚ) / 1000000000000) ≤ ((113055074029 : ℚ) / 250000000000) + (3989:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452220358961 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113055074029 : ℚ) / 250000000000) : ℚ) : ℝ) + ((3989:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((3989:ℚ)^(-2:ℤ) : ℝ) = ((3989:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_550 : ((((452220421429 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4001, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 3989 < q → q < 4001 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4001).mp (by decide +kernel))) hgap
  have hprev := s2L_549
  have hrat : ((452220421429 : ℚ) / 1000000000000) ≤ ((452220358961 : ℚ) / 1000000000000) + (4001:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452220421429 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452220358961 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((4001:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4001:ℚ)^(-2:ℤ) : ℝ) = ((4001:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_551 : ((((90444096767 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4003, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4001 < q → q < 4003 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4003).mp (by decide +kernel))) hgap
  have hprev := s2L_550
  have hrat : ((90444096767 : ℚ) / 200000000000) ≤ ((452220421429 : ℚ) / 1000000000000) + (4003:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90444096767 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452220421429 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((4003:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4003:ℚ)^(-2:ℤ) : ℝ) = ((4003:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_552 : ((((113055136529 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4007, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4003 < q → q < 4007 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4007).mp (by decide +kernel))) hgap
  have hprev := s2L_551
  have hrat : ((113055136529 : ℚ) / 250000000000) ≤ ((90444096767 : ℚ) / 200000000000) + (4007:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113055136529 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((90444096767 : ℚ) / 200000000000) : ℚ) : ℝ) + ((4007:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4007:ℚ)^(-2:ℤ) : ℝ) = ((4007:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_553 : ((((452220608211 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4013, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4007 < q → q < 4013 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4013).mp (by decide +kernel))) hgap
  have hprev := s2L_552
  have hrat : ((452220608211 : ℚ) / 1000000000000) ≤ ((113055136529 : ℚ) / 250000000000) + (4013:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452220608211 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113055136529 : ℚ) / 250000000000) : ℚ) : ℝ) + ((4013:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4013:ℚ)^(-2:ℤ) : ℝ) = ((4013:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_554 : ((((452220670121 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4019, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4013 < q → q < 4019 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4019).mp (by decide +kernel))) hgap
  have hprev := s2L_553
  have hrat : ((452220670121 : ℚ) / 1000000000000) ≤ ((452220608211 : ℚ) / 1000000000000) + (4019:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452220670121 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452220608211 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((4019:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4019:ℚ)^(-2:ℤ) : ℝ) = ((4019:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_555 : ((((452220731969 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4021, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4019 < q → q < 4021 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4021).mp (by decide +kernel))) hgap
  have hprev := s2L_554
  have hrat : ((452220731969 : ℚ) / 1000000000000) ≤ ((452220670121 : ℚ) / 1000000000000) + (4021:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452220731969 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452220670121 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((4021:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4021:ℚ)^(-2:ℤ) : ℝ) = ((4021:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_556 : ((((452220793633 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4027, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4021 < q → q < 4027 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4027).mp (by decide +kernel))) hgap
  have hprev := s2L_555
  have hrat : ((452220793633 : ℚ) / 1000000000000) ≤ ((452220731969 : ℚ) / 1000000000000) + (4027:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452220793633 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452220731969 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((4027:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4027:ℚ)^(-2:ℤ) : ℝ) = ((4027:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_557 : ((((452220854629 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4049, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4027 < q → q < 4049 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4049).mp (by decide +kernel))) hgap
  have hprev := s2L_556
  have hrat : ((452220854629 : ℚ) / 1000000000000) ≤ ((452220793633 : ℚ) / 1000000000000) + (4049:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452220854629 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452220793633 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((4049:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4049:ℚ)^(-2:ℤ) : ℝ) = ((4049:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_558 : ((((90444183113 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4051, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4049 < q → q < 4051 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4051).mp (by decide +kernel))) hgap
  have hprev := s2L_557
  have hrat : ((90444183113 : ℚ) / 200000000000) ≤ ((452220854629 : ℚ) / 1000000000000) + (4051:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90444183113 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452220854629 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((4051:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4051:ℚ)^(-2:ℤ) : ℝ) = ((4051:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_559 : ((((452220976321 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4057, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4051 < q → q < 4057 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4057).mp (by decide +kernel))) hgap
  have hprev := s2L_558
  have hrat : ((452220976321 : ℚ) / 1000000000000) ≤ ((90444183113 : ℚ) / 200000000000) + (4057:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452220976321 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90444183113 : ℚ) / 200000000000) : ℚ) : ℝ) + ((4057:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4057:ℚ)^(-2:ℤ) : ℝ) = ((4057:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_560 : ((((2261105183 : ℚ) / 5000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4073, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4057 < q → q < 4073 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4073).mp (by decide +kernel))) hgap
  have hprev := s2L_559
  have hrat : ((2261105183 : ℚ) / 5000000000) ≤ ((452220976321 : ℚ) / 1000000000000) + (4073:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((2261105183 : ℚ) / 5000000000) : ℚ) : ℝ) ≤ ((((452220976321 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((4073:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4073:ℚ)^(-2:ℤ) : ℝ) = ((4073:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_561 : ((((226110548351 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4079, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4073 < q → q < 4079 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4079).mp (by decide +kernel))) hgap
  have hprev := s2L_560
  have hrat : ((226110548351 : ℚ) / 500000000000) ≤ ((2261105183 : ℚ) / 5000000000) + (4079:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226110548351 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((2261105183 : ℚ) / 5000000000) : ℚ) : ℝ) + ((4079:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4079:ℚ)^(-2:ℤ) : ℝ) = ((4079:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_562 : ((((113055289113 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4091, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4079 < q → q < 4091 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4091).mp (by decide +kernel))) hgap
  have hprev := s2L_561
  have hrat : ((113055289113 : ℚ) / 250000000000) ≤ ((226110548351 : ℚ) / 500000000000) + (4091:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113055289113 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226110548351 : ℚ) / 500000000000) : ℚ) : ℝ) + ((4091:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4091:ℚ)^(-2:ℤ) : ℝ) = ((4091:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_563 : ((((28263826009 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4093, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4091 < q → q < 4093 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4093).mp (by decide +kernel))) hgap
  have hprev := s2L_562
  have hrat : ((28263826009 : ℚ) / 62500000000) ≤ ((113055289113 : ℚ) / 250000000000) + (4093:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28263826009 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((113055289113 : ℚ) / 250000000000) : ℚ) : ℝ) + ((4093:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4093:ℚ)^(-2:ℤ) : ℝ) = ((4093:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_564 : ((((452221275661 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4099, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4093 < q → q < 4099 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4099).mp (by decide +kernel))) hgap
  have hprev := s2L_563
  have hrat : ((452221275661 : ℚ) / 1000000000000) ≤ ((28263826009 : ℚ) / 62500000000) + (4099:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452221275661 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((28263826009 : ℚ) / 62500000000) : ℚ) : ℝ) + ((4099:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4099:ℚ)^(-2:ℤ) : ℝ) = ((4099:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_565 : ((((452221334831 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4111, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4099 < q → q < 4111 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4111).mp (by decide +kernel))) hgap
  have hprev := s2L_564
  have hrat : ((452221334831 : ℚ) / 1000000000000) ≤ ((452221275661 : ℚ) / 1000000000000) + (4111:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452221334831 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452221275661 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((4111:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4111:ℚ)^(-2:ℤ) : ℝ) = ((4111:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_566 : ((((452221393543 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4127, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4111 < q → q < 4127 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4127).mp (by decide +kernel))) hgap
  have hprev := s2L_565
  have hrat : ((452221393543 : ℚ) / 1000000000000) ≤ ((452221334831 : ℚ) / 1000000000000) + (4127:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452221393543 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452221334831 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((4127:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4127:ℚ)^(-2:ℤ) : ℝ) = ((4127:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_567 : ((((226110726099 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4129, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4127 < q → q < 4129 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4129).mp (by decide +kernel))) hgap
  have hprev := s2L_566
  have hrat : ((226110726099 : ℚ) / 500000000000) ≤ ((452221393543 : ℚ) / 1000000000000) + (4129:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226110726099 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452221393543 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((4129:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4129:ℚ)^(-2:ℤ) : ℝ) = ((4129:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_568 : ((((22611075537 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4133, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4129 < q → q < 4133 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4133).mp (by decide +kernel))) hgap
  have hprev := s2L_567
  have hrat : ((22611075537 : ℚ) / 50000000000) ≤ ((226110726099 : ℚ) / 500000000000) + (4133:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22611075537 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((226110726099 : ℚ) / 500000000000) : ℚ) : ℝ) + ((4133:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4133:ℚ)^(-2:ℤ) : ℝ) = ((4133:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_569 : ((((56527696139 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4139, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4133 < q → q < 4139 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4139).mp (by decide +kernel))) hgap
  have hprev := s2L_568
  have hrat : ((56527696139 : ℚ) / 125000000000) ≤ ((22611075537 : ℚ) / 50000000000) + (4139:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56527696139 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((22611075537 : ℚ) / 50000000000) : ℚ) : ℝ) + ((4139:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4139:ℚ)^(-2:ℤ) : ℝ) = ((4139:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_570 : ((((452221627091 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4153, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4139 < q → q < 4153 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4153).mp (by decide +kernel))) hgap
  have hprev := s2L_569
  have hrat : ((452221627091 : ℚ) / 1000000000000) ≤ ((56527696139 : ℚ) / 125000000000) + (4153:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452221627091 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56527696139 : ℚ) / 125000000000) : ℚ) : ℝ) + ((4153:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4153:ℚ)^(-2:ℤ) : ℝ) = ((4153:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_571 : ((((452221684959 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4157, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4153 < q → q < 4157 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4157).mp (by decide +kernel))) hgap
  have hprev := s2L_570
  have hrat : ((452221684959 : ℚ) / 1000000000000) ≤ ((452221627091 : ℚ) / 1000000000000) + (4157:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452221684959 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452221627091 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((4157:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4157:ℚ)^(-2:ℤ) : ℝ) = ((4157:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_572 : ((((452221742771 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4159, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4157 < q → q < 4159 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4159).mp (by decide +kernel))) hgap
  have hprev := s2L_571
  have hrat : ((452221742771 : ℚ) / 1000000000000) ≤ ((452221684959 : ℚ) / 1000000000000) + (4159:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452221742771 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452221684959 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((4159:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4159:ℚ)^(-2:ℤ) : ℝ) = ((4159:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_573 : ((((226110900043 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4177, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4159 < q → q < 4177 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4177).mp (by decide +kernel))) hgap
  have hprev := s2L_572
  have hrat : ((226110900043 : ℚ) / 500000000000) ≤ ((452221742771 : ℚ) / 1000000000000) + (4177:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226110900043 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452221742771 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((4177:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4177:ℚ)^(-2:ℤ) : ℝ) = ((4177:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_574 : ((((113055464187 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4201, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4177 < q → q < 4201 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4201).mp (by decide +kernel))) hgap
  have hprev := s2L_573
  have hrat : ((113055464187 : ℚ) / 250000000000) ≤ ((226110900043 : ℚ) / 500000000000) + (4201:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113055464187 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226110900043 : ℚ) / 500000000000) : ℚ) : ℝ) + ((4201:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4201:ℚ)^(-2:ℤ) : ℝ) = ((4201:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_575 : ((((452221913141 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4211, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4201 < q → q < 4211 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4211).mp (by decide +kernel))) hgap
  have hprev := s2L_574
  have hrat : ((452221913141 : ℚ) / 1000000000000) ≤ ((113055464187 : ℚ) / 250000000000) + (4211:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452221913141 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113055464187 : ℚ) / 250000000000) : ℚ) : ℝ) + ((4211:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4211:ℚ)^(-2:ℤ) : ℝ) = ((4211:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_576 : ((((226110984687 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4217, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4211 < q → q < 4217 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4217).mp (by decide +kernel))) hgap
  have hprev := s2L_575
  have hrat : ((226110984687 : ℚ) / 500000000000) ≤ ((452221913141 : ℚ) / 1000000000000) + (4217:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226110984687 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452221913141 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((4217:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4217:ℚ)^(-2:ℤ) : ℝ) = ((4217:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_577 : ((((452222025553 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4219, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4217 < q → q < 4219 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4219).mp (by decide +kernel))) hgap
  have hprev := s2L_576
  have hrat : ((452222025553 : ℚ) / 1000000000000) ≤ ((226110984687 : ℚ) / 500000000000) + (4219:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452222025553 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226110984687 : ℚ) / 500000000000) : ℚ) : ℝ) + ((4219:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4219:ℚ)^(-2:ℤ) : ℝ) = ((4219:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_578 : ((((452222081467 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4229, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4219 < q → q < 4229 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4229).mp (by decide +kernel))) hgap
  have hprev := s2L_577
  have hrat : ((452222081467 : ℚ) / 1000000000000) ≤ ((452222025553 : ℚ) / 1000000000000) + (4229:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452222081467 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452222025553 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((4229:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4229:ℚ)^(-2:ℤ) : ℝ) = ((4229:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_579 : ((((28263883583 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4231, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4229 < q → q < 4231 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4231).mp (by decide +kernel))) hgap
  have hprev := s2L_578
  have hrat : ((28263883583 : ℚ) / 62500000000) ≤ ((452222081467 : ℚ) / 1000000000000) + (4231:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28263883583 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((452222081467 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((4231:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4231:ℚ)^(-2:ℤ) : ℝ) = ((4231:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_580 : ((((226111096463 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4241, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4231 < q → q < 4241 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4241).mp (by decide +kernel))) hgap
  have hprev := s2L_579
  have hrat : ((226111096463 : ℚ) / 500000000000) ≤ ((28263883583 : ℚ) / 62500000000) + (4241:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226111096463 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((28263883583 : ℚ) / 62500000000) : ℚ) : ℝ) + ((4241:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4241:ℚ)^(-2:ℤ) : ℝ) = ((4241:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_581 : ((((56527781059 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4243, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4241 < q → q < 4243 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4243).mp (by decide +kernel))) hgap
  have hprev := s2L_580
  have hrat : ((56527781059 : ℚ) / 125000000000) ≤ ((226111096463 : ℚ) / 500000000000) + (4243:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56527781059 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((226111096463 : ℚ) / 500000000000) : ℚ) : ℝ) + ((4243:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4243:ℚ)^(-2:ℤ) : ℝ) = ((4243:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_582 : ((((452222303757 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4253, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4243 < q → q < 4253 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4253).mp (by decide +kernel))) hgap
  have hprev := s2L_581
  have hrat : ((452222303757 : ℚ) / 1000000000000) ≤ ((56527781059 : ℚ) / 125000000000) + (4253:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452222303757 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56527781059 : ℚ) / 125000000000) : ℚ) : ℝ) + ((4253:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4253:ℚ)^(-2:ℤ) : ℝ) = ((4253:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_583 : ((((226111179443 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4259, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4253 < q → q < 4259 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4259).mp (by decide +kernel))) hgap
  have hprev := s2L_582
  have hrat : ((226111179443 : ℚ) / 500000000000) ≤ ((452222303757 : ℚ) / 1000000000000) + (4259:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226111179443 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452222303757 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((4259:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4259:ℚ)^(-2:ℤ) : ℝ) = ((4259:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_584 : ((((452222413963 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4261, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4259 < q → q < 4261 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4261).mp (by decide +kernel))) hgap
  have hprev := s2L_583
  have hrat : ((452222413963 : ℚ) / 1000000000000) ≤ ((226111179443 : ℚ) / 500000000000) + (4261:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452222413963 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226111179443 : ℚ) / 500000000000) : ℚ) : ℝ) + ((4261:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4261:ℚ)^(-2:ℤ) : ℝ) = ((4261:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_585 : ((((452222468783 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4271, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4261 < q → q < 4271 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4271).mp (by decide +kernel))) hgap
  have hprev := s2L_584
  have hrat : ((452222468783 : ℚ) / 1000000000000) ≤ ((452222413963 : ℚ) / 1000000000000) + (4271:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452222468783 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452222413963 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((4271:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4271:ℚ)^(-2:ℤ) : ℝ) = ((4271:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_586 : ((((452222523551 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4273, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4271 < q → q < 4273 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4273).mp (by decide +kernel))) hgap
  have hprev := s2L_585
  have hrat : ((452222523551 : ℚ) / 1000000000000) ≤ ((452222468783 : ℚ) / 1000000000000) + (4273:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452222523551 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452222468783 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((4273:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4273:ℚ)^(-2:ℤ) : ℝ) = ((4273:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_587 : ((((28263911129 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4283, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4273 < q → q < 4283 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4283).mp (by decide +kernel))) hgap
  have hprev := s2L_586
  have hrat : ((28263911129 : ℚ) / 62500000000) ≤ ((452222523551 : ℚ) / 1000000000000) + (4283:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28263911129 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((452222523551 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((4283:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4283:ℚ)^(-2:ℤ) : ℝ) = ((4283:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_588 : ((((18088905297 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4289, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4283 < q → q < 4289 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4289).mp (by decide +kernel))) hgap
  have hprev := s2L_587
  have hrat : ((18088905297 : ℚ) / 40000000000) ≤ ((28263911129 : ℚ) / 62500000000) + (4289:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18088905297 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((28263911129 : ℚ) / 62500000000) : ℚ) : ℝ) + ((4289:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4289:ℚ)^(-2:ℤ) : ℝ) = ((4289:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_589 : ((((452222686583 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4297, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4289 < q → q < 4297 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4297).mp (by decide +kernel))) hgap
  have hprev := s2L_588
  have hrat : ((452222686583 : ℚ) / 1000000000000) ≤ ((18088905297 : ℚ) / 40000000000) + (4297:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452222686583 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((18088905297 : ℚ) / 40000000000) : ℚ) : ℝ) + ((4297:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4297:ℚ)^(-2:ℤ) : ℝ) = ((4297:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_590 : ((((452222739993 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4327, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4297 < q → q < 4327 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4327).mp (by decide +kernel))) hgap
  have hprev := s2L_589
  have hrat : ((452222739993 : ℚ) / 1000000000000) ≤ ((452222686583 : ℚ) / 1000000000000) + (4327:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452222739993 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452222686583 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((4327:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4327:ℚ)^(-2:ℤ) : ℝ) = ((4327:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_591 : ((((452222793157 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4337, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4327 < q → q < 4337 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4337).mp (by decide +kernel))) hgap
  have hprev := s2L_590
  have hrat : ((452222793157 : ℚ) / 1000000000000) ≤ ((452222739993 : ℚ) / 1000000000000) + (4337:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452222793157 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452222739993 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((4337:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4337:ℚ)^(-2:ℤ) : ℝ) = ((4337:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_592 : ((((7065981973 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4339, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4337 < q → q < 4339 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4339).mp (by decide +kernel))) hgap
  have hprev := s2L_591
  have hrat : ((7065981973 : ℚ) / 15625000000) ≤ ((452222793157 : ℚ) / 1000000000000) + (4339:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((7065981973 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ ((((452222793157 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((4339:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4339:ℚ)^(-2:ℤ) : ℝ) = ((4339:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_593 : ((((452222899143 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4349, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4339 < q → q < 4349 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4349).mp (by decide +kernel))) hgap
  have hprev := s2L_592
  have hrat : ((452222899143 : ℚ) / 1000000000000) ≤ ((7065981973 : ℚ) / 15625000000) + (4349:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452222899143 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((7065981973 : ℚ) / 15625000000) : ℚ) : ℝ) + ((4349:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4349:ℚ)^(-2:ℤ) : ℝ) = ((4349:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_594 : ((((22611147591 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4357, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4349 < q → q < 4357 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4357).mp (by decide +kernel))) hgap
  have hprev := s2L_593
  have hrat : ((22611147591 : ℚ) / 50000000000) ≤ ((452222899143 : ℚ) / 1000000000000) + (4357:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22611147591 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((452222899143 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((4357:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4357:ℚ)^(-2:ℤ) : ℝ) = ((4357:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_595 : ((((7065984443 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4363, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4357 < q → q < 4363 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4363).mp (by decide +kernel))) hgap
  have hprev := s2L_594
  have hrat : ((7065984443 : ℚ) / 15625000000) ≤ ((22611147591 : ℚ) / 50000000000) + (4363:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((7065984443 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ ((((22611147591 : ℚ) / 50000000000) : ℚ) : ℝ) + ((4363:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4363:ℚ)^(-2:ℤ) : ℝ) = ((4363:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_596 : ((((113055764161 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4373, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4363 < q → q < 4373 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4373).mp (by decide +kernel))) hgap
  have hprev := s2L_595
  have hrat : ((113055764161 : ℚ) / 250000000000) ≤ ((7065984443 : ℚ) / 15625000000) + (4373:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113055764161 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((7065984443 : ℚ) / 15625000000) : ℚ) : ℝ) + ((4373:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4373:ℚ)^(-2:ℤ) : ℝ) = ((4373:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_597 : ((((113055777127 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4391, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4373 < q → q < 4391 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4391).mp (by decide +kernel))) hgap
  have hprev := s2L_596
  have hrat : ((113055777127 : ℚ) / 250000000000) ≤ ((113055764161 : ℚ) / 250000000000) + (4391:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113055777127 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((113055764161 : ℚ) / 250000000000) : ℚ) : ℝ) + ((4391:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4391:ℚ)^(-2:ℤ) : ℝ) = ((4391:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_598 : ((((452223160231 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4397, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4391 < q → q < 4397 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4397).mp (by decide +kernel))) hgap
  have hprev := s2L_597
  have hrat : ((452223160231 : ℚ) / 1000000000000) ≤ ((113055777127 : ℚ) / 250000000000) + (4397:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452223160231 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113055777127 : ℚ) / 250000000000) : ℚ) : ℝ) + ((4397:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4397:ℚ)^(-2:ℤ) : ℝ) = ((4397:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_599 : ((((452223211673 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4409, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4397 < q → q < 4409 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4409).mp (by decide +kernel))) hgap
  have hprev := s2L_598
  have hrat : ((452223211673 : ℚ) / 1000000000000) ≤ ((452223160231 : ℚ) / 1000000000000) + (4409:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452223211673 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452223160231 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((4409:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4409:ℚ)^(-2:ℤ) : ℝ) = ((4409:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_600 : ((((113055815709 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4421, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4409 < q → q < 4421 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4421).mp (by decide +kernel))) hgap
  have hprev := s2L_599
  have hrat : ((113055815709 : ℚ) / 250000000000) ≤ ((452223211673 : ℚ) / 1000000000000) + (4421:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113055815709 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452223211673 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((4421:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4421:ℚ)^(-2:ℤ) : ℝ) = ((4421:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_601 : ((((452223313953 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4423, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4421 < q → q < 4423 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4423).mp (by decide +kernel))) hgap
  have hprev := s2L_600
  have hrat : ((452223313953 : ℚ) / 1000000000000) ≤ ((113055815709 : ℚ) / 250000000000) + (4423:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452223313953 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113055815709 : ℚ) / 250000000000) : ℚ) : ℝ) + ((4423:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4423:ℚ)^(-2:ℤ) : ℝ) = ((4423:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_602 : ((((28263960291 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4441, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4423 < q → q < 4441 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4441).mp (by decide +kernel))) hgap
  have hprev := s2L_601
  have hrat : ((28263960291 : ℚ) / 62500000000) ≤ ((452223313953 : ℚ) / 1000000000000) + (4441:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28263960291 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((452223313953 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((4441:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4441:ℚ)^(-2:ℤ) : ℝ) = ((4441:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_603 : ((((226111707611 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4447, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4441 < q → q < 4447 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4447).mp (by decide +kernel))) hgap
  have hprev := s2L_602
  have hrat : ((226111707611 : ℚ) / 500000000000) ≤ ((28263960291 : ℚ) / 62500000000) + (4447:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226111707611 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((28263960291 : ℚ) / 62500000000) : ℚ) : ℝ) + ((4447:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4447:ℚ)^(-2:ℤ) : ℝ) = ((4447:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_604 : ((((452223465697 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4451, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4447 < q → q < 4451 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4451).mp (by decide +kernel))) hgap
  have hprev := s2L_603
  have hrat : ((452223465697 : ℚ) / 1000000000000) ≤ ((226111707611 : ℚ) / 500000000000) + (4451:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452223465697 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226111707611 : ℚ) / 500000000000) : ℚ) : ℝ) + ((4451:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4451:ℚ)^(-2:ℤ) : ℝ) = ((4451:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_605 : ((((452223516037 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4457, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4451 < q → q < 4457 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4457).mp (by decide +kernel))) hgap
  have hprev := s2L_604
  have hrat : ((452223516037 : ℚ) / 1000000000000) ≤ ((452223465697 : ℚ) / 1000000000000) + (4457:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452223516037 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452223465697 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((4457:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4457:ℚ)^(-2:ℤ) : ℝ) = ((4457:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_606 : ((((452223566241 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4463, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4457 < q → q < 4463 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4463).mp (by decide +kernel))) hgap
  have hprev := s2L_605
  have hrat : ((452223566241 : ℚ) / 1000000000000) ≤ ((452223516037 : ℚ) / 1000000000000) + (4463:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452223566241 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452223516037 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((4463:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4463:ℚ)^(-2:ℤ) : ℝ) = ((4463:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_607 : ((((452223616043 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4481, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4463 < q → q < 4481 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4481).mp (by decide +kernel))) hgap
  have hprev := s2L_606
  have hrat : ((452223616043 : ℚ) / 1000000000000) ≤ ((452223566241 : ℚ) / 1000000000000) + (4481:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452223616043 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452223566241 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((4481:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4481:ℚ)^(-2:ℤ) : ℝ) = ((4481:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_608 : ((((2261118329 : ℚ) / 5000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4483, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4481 < q → q < 4483 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4483).mp (by decide +kernel))) hgap
  have hprev := s2L_607
  have hrat : ((2261118329 : ℚ) / 5000000000) ≤ ((452223616043 : ℚ) / 1000000000000) + (4483:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((2261118329 : ℚ) / 5000000000) : ℚ) : ℝ) ≤ ((((452223616043 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((4483:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4483:ℚ)^(-2:ℤ) : ℝ) = ((4483:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_609 : ((((56527964417 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4493, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4483 < q → q < 4493 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4493).mp (by decide +kernel))) hgap
  have hprev := s2L_608
  have hrat : ((56527964417 : ℚ) / 125000000000) ≤ ((2261118329 : ℚ) / 5000000000) + (4493:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56527964417 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((2261118329 : ℚ) / 5000000000) : ℚ) : ℝ) + ((4493:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4493:ℚ)^(-2:ℤ) : ℝ) = ((4493:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_610 : ((((90444752913 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4507, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4493 < q → q < 4507 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4507).mp (by decide +kernel))) hgap
  have hprev := s2L_609
  have hrat : ((90444752913 : ℚ) / 200000000000) ≤ ((56527964417 : ℚ) / 125000000000) + (4507:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90444752913 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((56527964417 : ℚ) / 125000000000) : ℚ) : ℝ) + ((4507:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4507:ℚ)^(-2:ℤ) : ℝ) = ((4507:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_611 : ((((452223813663 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4513, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4507 < q → q < 4513 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4513).mp (by decide +kernel))) hgap
  have hprev := s2L_610
  have hrat : ((452223813663 : ℚ) / 1000000000000) ≤ ((90444752913 : ℚ) / 200000000000) + (4513:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452223813663 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90444752913 : ℚ) / 200000000000) : ℚ) : ℝ) + ((4513:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4513:ℚ)^(-2:ℤ) : ℝ) = ((4513:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_612 : ((((226111931337 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4517, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4513 < q → q < 4517 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4517).mp (by decide +kernel))) hgap
  have hprev := s2L_611
  have hrat : ((226111931337 : ℚ) / 500000000000) ≤ ((452223813663 : ℚ) / 1000000000000) + (4517:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226111931337 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452223813663 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((4517:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4517:ℚ)^(-2:ℤ) : ℝ) = ((4517:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_613 : ((((226111955821 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4519, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4517 < q → q < 4519 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4519).mp (by decide +kernel))) hgap
  have hprev := s2L_612
  have hrat : ((226111955821 : ℚ) / 500000000000) ≤ ((226111931337 : ℚ) / 500000000000) + (4519:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226111955821 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226111931337 : ℚ) / 500000000000) : ℚ) : ℝ) + ((4519:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4519:ℚ)^(-2:ℤ) : ℝ) = ((4519:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_614 : ((((452223960523 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4523, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4519 < q → q < 4523 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4523).mp (by decide +kernel))) hgap
  have hprev := s2L_613
  have hrat : ((452223960523 : ℚ) / 1000000000000) ≤ ((226111955821 : ℚ) / 500000000000) + (4523:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452223960523 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226111955821 : ℚ) / 500000000000) : ℚ) : ℝ) + ((4523:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4523:ℚ)^(-2:ℤ) : ℝ) = ((4523:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_615 : ((((45222400889 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4547, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4523 < q → q < 4547 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4547).mp (by decide +kernel))) hgap
  have hprev := s2L_614
  have hrat : ((45222400889 : ℚ) / 100000000000) ≤ ((452223960523 : ℚ) / 1000000000000) + (4547:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45222400889 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((452223960523 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((4547:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4547:ℚ)^(-2:ℤ) : ℝ) = ((4547:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_616 : ((((226112028607 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4549, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4547 < q → q < 4549 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4549).mp (by decide +kernel))) hgap
  have hprev := s2L_615
  have hrat : ((226112028607 : ℚ) / 500000000000) ≤ ((45222400889 : ℚ) / 100000000000) + (4549:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226112028607 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((45222400889 : ℚ) / 100000000000) : ℚ) : ℝ) + ((4549:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4549:ℚ)^(-2:ℤ) : ℝ) = ((4549:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_617 : ((((113056026321 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4561, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4549 < q → q < 4561 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4561).mp (by decide +kernel))) hgap
  have hprev := s2L_616
  have hrat : ((113056026321 : ℚ) / 250000000000) ≤ ((226112028607 : ℚ) / 500000000000) + (4561:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113056026321 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226112028607 : ℚ) / 500000000000) : ℚ) : ℝ) + ((4561:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4561:ℚ)^(-2:ℤ) : ℝ) = ((4561:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_618 : ((((113056038307 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4567, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4561 < q → q < 4567 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4567).mp (by decide +kernel))) hgap
  have hprev := s2L_617
  have hrat : ((113056038307 : ℚ) / 250000000000) ≤ ((113056026321 : ℚ) / 250000000000) + (4567:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113056038307 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((113056026321 : ℚ) / 250000000000) : ℚ) : ℝ) + ((4567:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4567:ℚ)^(-2:ℤ) : ℝ) = ((4567:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_619 : ((((226112100419 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4583, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4567 < q → q < 4583 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4583).mp (by decide +kernel))) hgap
  have hprev := s2L_618
  have hrat : ((226112100419 : ℚ) / 500000000000) ≤ ((113056038307 : ℚ) / 250000000000) + (4583:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226112100419 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113056038307 : ℚ) / 250000000000) : ℚ) : ℝ) + ((4583:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4583:ℚ)^(-2:ℤ) : ℝ) = ((4583:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_620 : ((((226112124141 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4591, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4583 < q → q < 4591 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4591).mp (by decide +kernel))) hgap
  have hprev := s2L_619
  have hrat : ((226112124141 : ℚ) / 500000000000) ≤ ((226112100419 : ℚ) / 500000000000) + (4591:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226112124141 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226112100419 : ℚ) / 500000000000) : ℚ) : ℝ) + ((4591:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4591:ℚ)^(-2:ℤ) : ℝ) = ((4591:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_621 : ((((226112147801 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4597, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4591 < q → q < 4597 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4597).mp (by decide +kernel))) hgap
  have hprev := s2L_620
  have hrat : ((226112147801 : ℚ) / 500000000000) ≤ ((226112124141 : ℚ) / 500000000000) + (4597:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226112147801 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226112124141 : ℚ) / 500000000000) : ℚ) : ℝ) + ((4597:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4597:ℚ)^(-2:ℤ) : ℝ) = ((4597:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_622 : ((((452224342799 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4603, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4597 < q → q < 4603 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4603).mp (by decide +kernel))) hgap
  have hprev := s2L_621
  have hrat : ((452224342799 : ℚ) / 1000000000000) ≤ ((226112147801 : ℚ) / 500000000000) + (4603:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452224342799 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226112147801 : ℚ) / 500000000000) : ℚ) : ℝ) + ((4603:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4603:ℚ)^(-2:ℤ) : ℝ) = ((4603:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_623 : ((((452224389629 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4621, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4603 < q → q < 4621 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4621).mp (by decide +kernel))) hgap
  have hprev := s2L_622
  have hrat : ((452224389629 : ℚ) / 1000000000000) ≤ ((452224342799 : ℚ) / 1000000000000) + (4621:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452224389629 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452224342799 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((4621:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4621:ℚ)^(-2:ℤ) : ℝ) = ((4621:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_624 : ((((56528054517 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4637, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4621 < q → q < 4637 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4637).mp (by decide +kernel))) hgap
  have hprev := s2L_623
  have hrat : ((56528054517 : ℚ) / 125000000000) ≤ ((452224389629 : ℚ) / 1000000000000) + (4637:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56528054517 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452224389629 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((4637:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4637:ℚ)^(-2:ℤ) : ℝ) = ((4637:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_625 : ((((452224482603 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4639, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4637 < q → q < 4639 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4639).mp (by decide +kernel))) hgap
  have hprev := s2L_624
  have hrat : ((452224482603 : ℚ) / 1000000000000) ≤ ((56528054517 : ℚ) / 125000000000) + (4639:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452224482603 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56528054517 : ℚ) / 125000000000) : ℚ) : ℝ) + ((4639:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4639:ℚ)^(-2:ℤ) : ℝ) = ((4639:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_626 : ((((45222452899 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4643, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4639 < q → q < 4643 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4643).mp (by decide +kernel))) hgap
  have hprev := s2L_625
  have hrat : ((45222452899 : ℚ) / 100000000000) ≤ ((452224482603 : ℚ) / 1000000000000) + (4643:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45222452899 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((452224482603 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((4643:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4643:ℚ)^(-2:ℤ) : ℝ) = ((4643:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_627 : ((((226112287629 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4649, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4643 < q → q < 4649 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4649).mp (by decide +kernel))) hgap
  have hprev := s2L_626
  have hrat : ((226112287629 : ℚ) / 500000000000) ≤ ((45222452899 : ℚ) / 100000000000) + (4649:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226112287629 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((45222452899 : ℚ) / 100000000000) : ℚ) : ℝ) + ((4649:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4649:ℚ)^(-2:ℤ) : ℝ) = ((4649:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_628 : ((((226112310743 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4651, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4649 < q → q < 4651 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4651).mp (by decide +kernel))) hgap
  have hprev := s2L_627
  have hrat : ((226112310743 : ℚ) / 500000000000) ≤ ((226112287629 : ℚ) / 500000000000) + (4651:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226112310743 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226112287629 : ℚ) / 500000000000) : ℚ) : ℝ) + ((4651:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4651:ℚ)^(-2:ℤ) : ℝ) = ((4651:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_629 : ((((90444933519 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4657, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4651 < q → q < 4657 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4657).mp (by decide +kernel))) hgap
  have hprev := s2L_628
  have hrat : ((90444933519 : ℚ) / 200000000000) ≤ ((226112310743 : ℚ) / 500000000000) + (4657:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90444933519 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((226112310743 : ℚ) / 500000000000) : ℚ) : ℝ) + ((4657:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4657:ℚ)^(-2:ℤ) : ℝ) = ((4657:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_630 : ((((90444942717 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4663, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4657 < q → q < 4663 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4663).mp (by decide +kernel))) hgap
  have hprev := s2L_629
  have hrat : ((90444942717 : ℚ) / 200000000000) ≤ ((90444933519 : ℚ) / 200000000000) + (4663:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90444942717 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((90444933519 : ℚ) / 200000000000) : ℚ) : ℝ) + ((4663:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4663:ℚ)^(-2:ℤ) : ℝ) = ((4663:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_631 : ((((226112379689 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4673, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4663 < q → q < 4673 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4673).mp (by decide +kernel))) hgap
  have hprev := s2L_630
  have hrat : ((226112379689 : ℚ) / 500000000000) ≤ ((90444942717 : ℚ) / 200000000000) + (4673:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226112379689 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((90444942717 : ℚ) / 200000000000) : ℚ) : ℝ) + ((4673:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4673:ℚ)^(-2:ℤ) : ℝ) = ((4673:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_632 : ((((226112402527 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4679, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4673 < q → q < 4679 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4679).mp (by decide +kernel))) hgap
  have hprev := s2L_631
  have hrat : ((226112402527 : ℚ) / 500000000000) ≤ ((226112379689 : ℚ) / 500000000000) + (4679:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226112402527 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226112379689 : ℚ) / 500000000000) : ℚ) : ℝ) + ((4679:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4679:ℚ)^(-2:ℤ) : ℝ) = ((4679:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_633 : ((((452224850497 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4691, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4679 < q → q < 4691 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4691).mp (by decide +kernel))) hgap
  have hprev := s2L_632
  have hrat : ((452224850497 : ℚ) / 1000000000000) ≤ ((226112402527 : ℚ) / 500000000000) + (4691:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452224850497 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226112402527 : ℚ) / 500000000000) : ℚ) : ℝ) + ((4691:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4691:ℚ)^(-2:ℤ) : ℝ) = ((4691:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_634 : ((((113056223927 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4703, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4691 < q → q < 4703 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4703).mp (by decide +kernel))) hgap
  have hprev := s2L_633
  have hrat : ((113056223927 : ℚ) / 250000000000) ≤ ((452224850497 : ℚ) / 1000000000000) + (4703:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113056223927 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452224850497 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((4703:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4703:ℚ)^(-2:ℤ) : ℝ) = ((4703:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_635 : ((((18088997623 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4721, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4703 < q → q < 4721 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4721).mp (by decide +kernel))) hgap
  have hprev := s2L_634
  have hrat : ((18088997623 : ℚ) / 40000000000) ≤ ((113056223927 : ℚ) / 250000000000) + (4721:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18088997623 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((113056223927 : ℚ) / 250000000000) : ℚ) : ℝ) + ((4721:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4721:ℚ)^(-2:ℤ) : ℝ) = ((4721:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_636 : ((((113056246351 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4723, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4721 < q → q < 4723 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4723).mp (by decide +kernel))) hgap
  have hprev := s2L_635
  have hrat : ((113056246351 : ℚ) / 250000000000) ≤ ((18088997623 : ℚ) / 40000000000) + (4723:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113056246351 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((18088997623 : ℚ) / 40000000000) : ℚ) : ℝ) + ((4723:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4723:ℚ)^(-2:ℤ) : ℝ) = ((4723:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_637 : ((((452225030119 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4729, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4723 < q → q < 4729 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4729).mp (by decide +kernel))) hgap
  have hprev := s2L_636
  have hrat : ((452225030119 : ℚ) / 1000000000000) ≤ ((113056246351 : ℚ) / 250000000000) + (4729:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452225030119 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113056246351 : ℚ) / 250000000000) : ℚ) : ℝ) + ((4729:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4729:ℚ)^(-2:ℤ) : ℝ) = ((4729:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_638 : ((((452225074759 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4733, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4729 < q → q < 4733 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4733).mp (by decide +kernel))) hgap
  have hprev := s2L_637
  have hrat : ((452225074759 : ℚ) / 1000000000000) ≤ ((452225030119 : ℚ) / 1000000000000) + (4733:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452225074759 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452225030119 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((4733:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4733:ℚ)^(-2:ℤ) : ℝ) = ((4733:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_639 : ((((452225119061 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4751, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4733 < q → q < 4751 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4751).mp (by decide +kernel))) hgap
  have hprev := s2L_638
  have hrat : ((452225119061 : ℚ) / 1000000000000) ≤ ((452225074759 : ℚ) / 1000000000000) + (4751:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452225119061 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452225074759 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((4751:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4751:ℚ)^(-2:ℤ) : ℝ) = ((4751:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_640 : ((((226112581607 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4759, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4751 < q → q < 4759 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4759).mp (by decide +kernel))) hgap
  have hprev := s2L_639
  have hrat : ((226112581607 : ℚ) / 500000000000) ≤ ((452225119061 : ℚ) / 1000000000000) + (4759:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226112581607 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452225119061 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((4759:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4759:ℚ)^(-2:ℤ) : ℝ) = ((4759:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_641 : ((((18089008277 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4783, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4759 < q → q < 4783 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4783).mp (by decide +kernel))) hgap
  have hprev := s2L_640
  have hrat : ((18089008277 : ℚ) / 40000000000) ≤ ((226112581607 : ℚ) / 500000000000) + (4783:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18089008277 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((226112581607 : ℚ) / 500000000000) : ℚ) : ℝ) + ((4783:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4783:ℚ)^(-2:ℤ) : ℝ) = ((4783:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_642 : ((((452225250563 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4787, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4783 < q → q < 4787 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4787).mp (by decide +kernel))) hgap
  have hprev := s2L_641
  have hrat : ((452225250563 : ℚ) / 1000000000000) ≤ ((18089008277 : ℚ) / 40000000000) + (4787:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452225250563 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((18089008277 : ℚ) / 40000000000) : ℚ) : ℝ) + ((4787:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4787:ℚ)^(-2:ℤ) : ℝ) = ((4787:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_643 : ((((90445058833 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4789, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4787 < q → q < 4789 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4789).mp (by decide +kernel))) hgap
  have hprev := s2L_642
  have hrat : ((90445058833 : ℚ) / 200000000000) ≤ ((452225250563 : ℚ) / 1000000000000) + (4789:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90445058833 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452225250563 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((4789:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4789:ℚ)^(-2:ℤ) : ℝ) = ((4789:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_644 : ((((226112668847 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4793, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4789 < q → q < 4793 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4793).mp (by decide +kernel))) hgap
  have hprev := s2L_643
  have hrat : ((226112668847 : ℚ) / 500000000000) ≤ ((90445058833 : ℚ) / 200000000000) + (4793:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226112668847 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((90445058833 : ℚ) / 200000000000) : ℚ) : ℝ) + ((4793:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4793:ℚ)^(-2:ℤ) : ℝ) = ((4793:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_645 : ((((226112690557 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4799, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4793 < q → q < 4799 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4799).mp (by decide +kernel))) hgap
  have hprev := s2L_644
  have hrat : ((226112690557 : ℚ) / 500000000000) ≤ ((226112668847 : ℚ) / 500000000000) + (4799:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226112690557 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226112668847 : ℚ) / 500000000000) : ℚ) : ℝ) + ((4799:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4799:ℚ)^(-2:ℤ) : ℝ) = ((4799:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_646 : ((((226112712249 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4801, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4799 < q → q < 4801 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4801).mp (by decide +kernel))) hgap
  have hprev := s2L_645
  have hrat : ((226112712249 : ℚ) / 500000000000) ≤ ((226112690557 : ℚ) / 500000000000) + (4801:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226112712249 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226112690557 : ℚ) / 500000000000) : ℚ) : ℝ) + ((4801:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4801:ℚ)^(-2:ℤ) : ℝ) = ((4801:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_647 : ((((226112733833 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4813, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4801 < q → q < 4813 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4813).mp (by decide +kernel))) hgap
  have hprev := s2L_646
  have hrat : ((226112733833 : ℚ) / 500000000000) ≤ ((226112712249 : ℚ) / 500000000000) + (4813:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226112733833 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226112712249 : ℚ) / 500000000000) : ℚ) : ℝ) + ((4813:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4813:ℚ)^(-2:ℤ) : ℝ) = ((4813:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_648 : ((((226112755381 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4817, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4813 < q → q < 4817 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4817).mp (by decide +kernel))) hgap
  have hprev := s2L_647
  have hrat : ((226112755381 : ℚ) / 500000000000) ≤ ((226112733833 : ℚ) / 500000000000) + (4817:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226112755381 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226112733833 : ℚ) / 500000000000) : ℚ) : ℝ) + ((4817:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4817:ℚ)^(-2:ℤ) : ℝ) = ((4817:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_649 : ((((452225553609 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4831, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4817 < q → q < 4831 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4831).mp (by decide +kernel))) hgap
  have hprev := s2L_648
  have hrat : ((452225553609 : ℚ) / 1000000000000) ≤ ((226112755381 : ℚ) / 500000000000) + (4831:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452225553609 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226112755381 : ℚ) / 500000000000) : ℚ) : ℝ) + ((4831:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4831:ℚ)^(-2:ℤ) : ℝ) = ((4831:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_650 : ((((452225595929 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4861, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4831 < q → q < 4861 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4861).mp (by decide +kernel))) hgap
  have hprev := s2L_649
  have hrat : ((452225595929 : ℚ) / 1000000000000) ≤ ((452225553609 : ℚ) / 1000000000000) + (4861:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452225595929 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452225553609 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((4861:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4861:ℚ)^(-2:ℤ) : ℝ) = ((4861:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_651 : ((((18089025523 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4871, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4861 < q → q < 4871 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4871).mp (by decide +kernel))) hgap
  have hprev := s2L_650
  have hrat : ((18089025523 : ℚ) / 40000000000) ≤ ((452225595929 : ℚ) / 1000000000000) + (4871:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18089025523 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((452225595929 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((4871:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4871:ℚ)^(-2:ℤ) : ℝ) = ((4871:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_652 : ((((226112840059 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4877, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4871 < q → q < 4877 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4877).mp (by decide +kernel))) hgap
  have hprev := s2L_651
  have hrat : ((226112840059 : ℚ) / 500000000000) ≤ ((18089025523 : ℚ) / 40000000000) + (4877:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226112840059 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((18089025523 : ℚ) / 40000000000) : ℚ) : ℝ) + ((4877:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4877:ℚ)^(-2:ℤ) : ℝ) = ((4877:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_653 : ((((226112860977 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4889, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4877 < q → q < 4889 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4889).mp (by decide +kernel))) hgap
  have hprev := s2L_652
  have hrat : ((226112860977 : ℚ) / 500000000000) ≤ ((226112840059 : ℚ) / 500000000000) + (4889:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226112860977 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226112840059 : ℚ) / 500000000000) : ℚ) : ℝ) + ((4889:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4889:ℚ)^(-2:ℤ) : ℝ) = ((4889:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_654 : ((((14132055111 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4903, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4889 < q → q < 4903 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4903).mp (by decide +kernel))) hgap
  have hprev := s2L_653
  have hrat : ((14132055111 : ℚ) / 31250000000) ≤ ((226112860977 : ℚ) / 500000000000) + (4903:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((14132055111 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((226112860977 : ℚ) / 500000000000) : ℚ) : ℝ) + ((4903:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4903:ℚ)^(-2:ℤ) : ℝ) = ((4903:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_655 : ((((56528225631 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4909, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4903 < q → q < 4909 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4909).mp (by decide +kernel))) hgap
  have hprev := s2L_654
  have hrat : ((56528225631 : ℚ) / 125000000000) ≤ ((14132055111 : ℚ) / 31250000000) + (4909:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56528225631 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((14132055111 : ℚ) / 31250000000) : ℚ) : ℝ) + ((4909:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4909:ℚ)^(-2:ℤ) : ℝ) = ((4909:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_656 : ((((56528230797 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4919, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4909 < q → q < 4919 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4919).mp (by decide +kernel))) hgap
  have hprev := s2L_655
  have hrat : ((56528230797 : ℚ) / 125000000000) ≤ ((56528225631 : ℚ) / 125000000000) + (4919:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56528230797 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((56528225631 : ℚ) / 125000000000) : ℚ) : ℝ) + ((4919:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4919:ℚ)^(-2:ℤ) : ℝ) = ((4919:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_657 : ((((452225887503 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4931, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4919 < q → q < 4931 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4931).mp (by decide +kernel))) hgap
  have hprev := s2L_656
  have hrat : ((452225887503 : ℚ) / 1000000000000) ≤ ((56528230797 : ℚ) / 125000000000) + (4931:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452225887503 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56528230797 : ℚ) / 125000000000) : ℚ) : ℝ) + ((4931:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4931:ℚ)^(-2:ℤ) : ℝ) = ((4931:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_658 : ((((113056482149 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4933, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4931 < q → q < 4933 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4933).mp (by decide +kernel))) hgap
  have hprev := s2L_657
  have hrat : ((113056482149 : ℚ) / 250000000000) ≤ ((452225887503 : ℚ) / 1000000000000) + (4933:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113056482149 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452225887503 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((4933:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4933:ℚ)^(-2:ℤ) : ℝ) = ((4933:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_659 : ((((452225969623 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4937, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4933 < q → q < 4937 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4937).mp (by decide +kernel))) hgap
  have hprev := s2L_658
  have hrat : ((452225969623 : ℚ) / 1000000000000) ≤ ((113056482149 : ℚ) / 250000000000) + (4937:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452225969623 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113056482149 : ℚ) / 250000000000) : ℚ) : ℝ) + ((4937:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4937:ℚ)^(-2:ℤ) : ℝ) = ((4937:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_660 : ((((9044520211 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4943, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4937 < q → q < 4943 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4943).mp (by decide +kernel))) hgap
  have hprev := s2L_659
  have hrat : ((9044520211 : ℚ) / 20000000000) ≤ ((452225969623 : ℚ) / 1000000000000) + (4943:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((9044520211 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ ((((452225969623 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((4943:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4943:ℚ)^(-2:ℤ) : ℝ) = ((4943:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_661 : ((((90445210269 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4951, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4943 < q → q < 4951 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4951).mp (by decide +kernel))) hgap
  have hprev := s2L_660
  have hrat : ((90445210269 : ℚ) / 200000000000) ≤ ((9044520211 : ℚ) / 20000000000) + (4951:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90445210269 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((9044520211 : ℚ) / 20000000000) : ℚ) : ℝ) + ((4951:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4951:ℚ)^(-2:ℤ) : ℝ) = ((4951:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_662 : ((((452226092041 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4957, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4951 < q → q < 4957 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4957).mp (by decide +kernel))) hgap
  have hprev := s2L_661
  have hrat : ((452226092041 : ℚ) / 1000000000000) ≤ ((90445210269 : ℚ) / 200000000000) + (4957:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452226092041 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90445210269 : ℚ) / 200000000000) : ℚ) : ℝ) + ((4957:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4957:ℚ)^(-2:ℤ) : ℝ) = ((4957:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_663 : ((((226113066287 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4967, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4957 < q → q < 4967 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4967).mp (by decide +kernel))) hgap
  have hprev := s2L_662
  have hrat : ((226113066287 : ℚ) / 500000000000) ≤ ((452226092041 : ℚ) / 1000000000000) + (4967:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226113066287 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452226092041 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((4967:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4967:ℚ)^(-2:ℤ) : ℝ) = ((4967:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_664 : ((((226113086537 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4969, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4967 < q → q < 4969 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4969).mp (by decide +kernel))) hgap
  have hprev := s2L_663
  have hrat : ((226113086537 : ℚ) / 500000000000) ≤ ((226113066287 : ℚ) / 500000000000) + (4969:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226113086537 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226113066287 : ℚ) / 500000000000) : ℚ) : ℝ) + ((4969:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4969:ℚ)^(-2:ℤ) : ℝ) = ((4969:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_665 : ((((452226213509 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4973, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4969 < q → q < 4973 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4973).mp (by decide +kernel))) hgap
  have hprev := s2L_664
  have hrat : ((452226213509 : ℚ) / 1000000000000) ≤ ((226113086537 : ℚ) / 500000000000) + (4973:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452226213509 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226113086537 : ℚ) / 500000000000) : ℚ) : ℝ) + ((4973:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4973:ℚ)^(-2:ℤ) : ℝ) = ((4973:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_666 : ((((452226253717 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4987, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4973 < q → q < 4987 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4987).mp (by decide +kernel))) hgap
  have hprev := s2L_665
  have hrat : ((452226253717 : ℚ) / 1000000000000) ≤ ((452226213509 : ℚ) / 1000000000000) + (4987:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452226253717 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452226213509 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((4987:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4987:ℚ)^(-2:ℤ) : ℝ) = ((4987:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_667 : ((((452226293829 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4993, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4987 < q → q < 4993 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4993).mp (by decide +kernel))) hgap
  have hprev := s2L_666
  have hrat : ((452226293829 : ℚ) / 1000000000000) ≤ ((452226253717 : ℚ) / 1000000000000) + (4993:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452226293829 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452226253717 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((4993:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4993:ℚ)^(-2:ℤ) : ℝ) = ((4993:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_668 : ((((90445266769 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 4999, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4993 < q → q < 4999 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 4999).mp (by decide +kernel))) hgap
  have hprev := s2L_667
  have hrat : ((90445266769 : ℚ) / 200000000000) ≤ ((452226293829 : ℚ) / 1000000000000) + (4999:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90445266769 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452226293829 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((4999:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((4999:ℚ)^(-2:ℤ) : ℝ) = ((4999:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_669 : ((((452226373797 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5003, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 4999 < q → q < 5003 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5003).mp (by decide +kernel))) hgap
  have hprev := s2L_668
  have hrat : ((452226373797 : ℚ) / 1000000000000) ≤ ((90445266769 : ℚ) / 200000000000) + (5003:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452226373797 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90445266769 : ℚ) / 200000000000) : ℚ) : ℝ) + ((5003:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5003:ℚ)^(-2:ℤ) : ℝ) = ((5003:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_670 : ((((452226413653 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5009, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5003 < q → q < 5009 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5009).mp (by decide +kernel))) hgap
  have hprev := s2L_669
  have hrat : ((452226413653 : ℚ) / 1000000000000) ≤ ((452226373797 : ℚ) / 1000000000000) + (5009:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452226413653 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452226373797 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((5009:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5009:ℚ)^(-2:ℤ) : ℝ) = ((5009:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_671 : ((((452226453477 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5011, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5009 < q → q < 5011 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5011).mp (by decide +kernel))) hgap
  have hprev := s2L_670
  have hrat : ((452226453477 : ℚ) / 1000000000000) ≤ ((452226413653 : ℚ) / 1000000000000) + (5011:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452226453477 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452226413653 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((5011:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5011:ℚ)^(-2:ℤ) : ℝ) = ((5011:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_672 : ((((452226493143 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5021, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5011 < q → q < 5021 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5021).mp (by decide +kernel))) hgap
  have hprev := s2L_671
  have hrat : ((452226493143 : ℚ) / 1000000000000) ≤ ((452226453477 : ℚ) / 1000000000000) + (5021:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452226493143 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452226453477 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((5021:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5021:ℚ)^(-2:ℤ) : ℝ) = ((5021:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_673 : ((((452226532777 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5023, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5021 < q → q < 5023 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5023).mp (by decide +kernel))) hgap
  have hprev := s2L_672
  have hrat : ((452226532777 : ℚ) / 1000000000000) ≤ ((452226493143 : ℚ) / 1000000000000) + (5023:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452226532777 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452226493143 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((5023:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5023:ℚ)^(-2:ℤ) : ℝ) = ((5023:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_674 : ((((706604019 : ℚ) / 1562500000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5039, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5023 < q → q < 5039 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5039).mp (by decide +kernel))) hgap
  have hprev := s2L_673
  have hrat : ((706604019 : ℚ) / 1562500000) ≤ ((452226532777 : ℚ) / 1000000000000) + (5039:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((706604019 : ℚ) / 1562500000) : ℚ) : ℝ) ≤ ((((452226532777 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((5039:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5039:ℚ)^(-2:ℤ) : ℝ) = ((5039:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_675 : ((((113056652839 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5051, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5039 < q → q < 5051 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5051).mp (by decide +kernel))) hgap
  have hprev := s2L_674
  have hrat : ((113056652839 : ℚ) / 250000000000) ≤ ((706604019 : ℚ) / 1562500000) + (5051:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113056652839 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((706604019 : ℚ) / 1562500000) : ℚ) : ℝ) + ((5051:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5051:ℚ)^(-2:ℤ) : ℝ) = ((5051:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_676 : ((((113056662607 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5059, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5051 < q → q < 5059 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5059).mp (by decide +kernel))) hgap
  have hprev := s2L_675
  have hrat : ((113056662607 : ℚ) / 250000000000) ≤ ((113056652839 : ℚ) / 250000000000) + (5059:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113056662607 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((113056652839 : ℚ) / 250000000000) : ℚ) : ℝ) + ((5059:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5059:ℚ)^(-2:ℤ) : ℝ) = ((5059:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_677 : ((((452226689223 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5077, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5059 < q → q < 5077 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5077).mp (by decide +kernel))) hgap
  have hprev := s2L_676
  have hrat : ((452226689223 : ℚ) / 1000000000000) ≤ ((113056662607 : ℚ) / 250000000000) + (5077:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452226689223 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113056662607 : ℚ) / 250000000000) : ℚ) : ℝ) + ((5077:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5077:ℚ)^(-2:ℤ) : ℝ) = ((5077:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_678 : ((((452226727957 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5081, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5077 < q → q < 5081 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5081).mp (by decide +kernel))) hgap
  have hprev := s2L_677
  have hrat : ((452226727957 : ℚ) / 1000000000000) ≤ ((452226689223 : ℚ) / 1000000000000) + (5081:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452226727957 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452226689223 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((5081:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5081:ℚ)^(-2:ℤ) : ℝ) = ((5081:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_679 : ((((2261133833 : ℚ) / 5000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5087, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5081 < q → q < 5087 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5087).mp (by decide +kernel))) hgap
  have hprev := s2L_678
  have hrat : ((2261133833 : ℚ) / 5000000000) ≤ ((452226727957 : ℚ) / 1000000000000) + (5087:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((2261133833 : ℚ) / 5000000000) : ℚ) : ℝ) ≤ ((((452226727957 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((5087:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5087:ℚ)^(-2:ℤ) : ℝ) = ((5087:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_680 : ((((452226805061 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5099, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5087 < q → q < 5099 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5099).mp (by decide +kernel))) hgap
  have hprev := s2L_679
  have hrat : ((452226805061 : ℚ) / 1000000000000) ≤ ((2261133833 : ℚ) / 5000000000) + (5099:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452226805061 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2261133833 : ℚ) / 5000000000) : ℚ) : ℝ) + ((5099:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5099:ℚ)^(-2:ℤ) : ℝ) = ((5099:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_681 : ((((113056710873 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5101, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5099 < q → q < 5101 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5101).mp (by decide +kernel))) hgap
  have hprev := s2L_680
  have hrat : ((113056710873 : ℚ) / 250000000000) ≤ ((452226805061 : ℚ) / 1000000000000) + (5101:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113056710873 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452226805061 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((5101:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5101:ℚ)^(-2:ℤ) : ℝ) = ((5101:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_682 : ((((452226881833 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5107, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5101 < q → q < 5107 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5107).mp (by decide +kernel))) hgap
  have hprev := s2L_681
  have hrat : ((452226881833 : ℚ) / 1000000000000) ≤ ((113056710873 : ℚ) / 250000000000) + (5107:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452226881833 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113056710873 : ℚ) / 250000000000) : ℚ) : ℝ) + ((5107:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5107:ℚ)^(-2:ℤ) : ℝ) = ((5107:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_683 : ((((113056730021 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5113, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5107 < q → q < 5113 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5113).mp (by decide +kernel))) hgap
  have hprev := s2L_682
  have hrat : ((113056730021 : ℚ) / 250000000000) ≤ ((452226881833 : ℚ) / 1000000000000) + (5113:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113056730021 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452226881833 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((5113:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5113:ℚ)^(-2:ℤ) : ℝ) = ((5113:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_684 : ((((90445391649 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5119, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5113 < q → q < 5119 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5119).mp (by decide +kernel))) hgap
  have hprev := s2L_683
  have hrat : ((90445391649 : ℚ) / 200000000000) ≤ ((113056730021 : ℚ) / 250000000000) + (5119:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90445391649 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((113056730021 : ℚ) / 250000000000) : ℚ) : ℝ) + ((5119:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5119:ℚ)^(-2:ℤ) : ℝ) = ((5119:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_685 : ((((56528374499 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5147, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5119 < q → q < 5147 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5147).mp (by decide +kernel))) hgap
  have hprev := s2L_684
  have hrat : ((56528374499 : ℚ) / 125000000000) ≤ ((90445391649 : ℚ) / 200000000000) + (5147:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56528374499 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((90445391649 : ℚ) / 200000000000) : ℚ) : ℝ) + ((5147:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5147:ℚ)^(-2:ℤ) : ℝ) = ((5147:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_686 : ((((452227033651 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5153, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5147 < q → q < 5153 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5153).mp (by decide +kernel))) hgap
  have hprev := s2L_685
  have hrat : ((452227033651 : ℚ) / 1000000000000) ≤ ((56528374499 : ℚ) / 125000000000) + (5153:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452227033651 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56528374499 : ℚ) / 125000000000) : ℚ) : ℝ) + ((5153:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5153:ℚ)^(-2:ℤ) : ℝ) = ((5153:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_687 : ((((452227071107 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5167, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5153 < q → q < 5167 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5167).mp (by decide +kernel))) hgap
  have hprev := s2L_686
  have hrat : ((452227071107 : ℚ) / 1000000000000) ≤ ((452227033651 : ℚ) / 1000000000000) + (5167:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452227071107 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452227033651 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((5167:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5167:ℚ)^(-2:ℤ) : ℝ) = ((5167:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_688 : ((((90445421701 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5171, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5167 < q → q < 5171 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5171).mp (by decide +kernel))) hgap
  have hprev := s2L_687
  have hrat : ((90445421701 : ℚ) / 200000000000) ≤ ((452227071107 : ℚ) / 1000000000000) + (5171:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90445421701 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452227071107 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((5171:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5171:ℚ)^(-2:ℤ) : ℝ) = ((5171:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_689 : ((((452227145787 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5179, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5171 < q → q < 5179 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5179).mp (by decide +kernel))) hgap
  have hprev := s2L_688
  have hrat : ((452227145787 : ℚ) / 1000000000000) ≤ ((90445421701 : ℚ) / 200000000000) + (5179:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452227145787 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90445421701 : ℚ) / 200000000000) : ℚ) : ℝ) + ((5179:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5179:ℚ)^(-2:ℤ) : ℝ) = ((5179:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_690 : ((((226113591463 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5189, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5179 < q → q < 5189 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5189).mp (by decide +kernel))) hgap
  have hprev := s2L_689
  have hrat : ((226113591463 : ℚ) / 500000000000) ≤ ((452227145787 : ℚ) / 1000000000000) + (5189:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226113591463 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452227145787 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((5189:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5189:ℚ)^(-2:ℤ) : ℝ) = ((5189:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_691 : ((((9044544399 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5197, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5189 < q → q < 5197 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5197).mp (by decide +kernel))) hgap
  have hprev := s2L_690
  have hrat : ((9044544399 : ℚ) / 20000000000) ≤ ((226113591463 : ℚ) / 500000000000) + (5197:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((9044544399 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ ((((226113591463 : ℚ) / 500000000000) : ℚ) : ℝ) + ((5197:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5197:ℚ)^(-2:ℤ) : ℝ) = ((5197:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_692 : ((((113056814201 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5209, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5197 < q → q < 5209 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5209).mp (by decide +kernel))) hgap
  have hprev := s2L_691
  have hrat : ((113056814201 : ℚ) / 250000000000) ≤ ((9044544399 : ℚ) / 20000000000) + (5209:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113056814201 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((9044544399 : ℚ) / 20000000000) : ℚ) : ℝ) + ((5209:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5209:ℚ)^(-2:ℤ) : ℝ) = ((5209:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_693 : ((((90445458681 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5227, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5209 < q → q < 5227 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5227).mp (by decide +kernel))) hgap
  have hprev := s2L_692
  have hrat : ((90445458681 : ℚ) / 200000000000) ≤ ((113056814201 : ℚ) / 250000000000) + (5227:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90445458681 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((113056814201 : ℚ) / 250000000000) : ℚ) : ℝ) + ((5227:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5227:ℚ)^(-2:ℤ) : ℝ) = ((5227:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_694 : ((((9044546599 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5231, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5227 < q → q < 5231 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5231).mp (by decide +kernel))) hgap
  have hprev := s2L_693
  have hrat : ((9044546599 : ℚ) / 20000000000) ≤ ((90445458681 : ℚ) / 200000000000) + (5231:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((9044546599 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ ((((90445458681 : ℚ) / 200000000000) : ℚ) : ℝ) + ((5231:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5231:ℚ)^(-2:ℤ) : ℝ) = ((5231:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_695 : ((((452227366467 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5233, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5231 < q → q < 5233 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5233).mp (by decide +kernel))) hgap
  have hprev := s2L_694
  have hrat : ((452227366467 : ℚ) / 1000000000000) ≤ ((9044546599 : ℚ) / 20000000000) + (5233:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452227366467 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((9044546599 : ℚ) / 20000000000) : ℚ) : ℝ) + ((5233:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5233:ℚ)^(-2:ℤ) : ℝ) = ((5233:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_696 : ((((28264212683 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5237, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5233 < q → q < 5237 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5237).mp (by decide +kernel))) hgap
  have hprev := s2L_695
  have hrat : ((28264212683 : ℚ) / 62500000000) ≤ ((452227366467 : ℚ) / 1000000000000) + (5237:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28264212683 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((452227366467 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((5237:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5237:ℚ)^(-2:ℤ) : ℝ) = ((5237:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_697 : ((((452227439057 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5261, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5237 < q → q < 5261 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5261).mp (by decide +kernel))) hgap
  have hprev := s2L_696
  have hrat : ((452227439057 : ℚ) / 1000000000000) ≤ ((28264212683 : ℚ) / 62500000000) + (5261:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452227439057 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((28264212683 : ℚ) / 62500000000) : ℚ) : ℝ) + ((5261:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5261:ℚ)^(-2:ℤ) : ℝ) = ((5261:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_698 : ((((226113737511 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5273, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5261 < q → q < 5273 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5273).mp (by decide +kernel))) hgap
  have hprev := s2L_697
  have hrat : ((226113737511 : ℚ) / 500000000000) ≤ ((452227439057 : ℚ) / 1000000000000) + (5273:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226113737511 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452227439057 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((5273:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5273:ℚ)^(-2:ℤ) : ℝ) = ((5273:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_699 : ((((90445502181 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5279, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5273 < q → q < 5279 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5279).mp (by decide +kernel))) hgap
  have hprev := s2L_698
  have hrat : ((90445502181 : ℚ) / 200000000000) ≤ ((226113737511 : ℚ) / 500000000000) + (5279:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90445502181 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((226113737511 : ℚ) / 500000000000) : ℚ) : ℝ) + ((5279:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5279:ℚ)^(-2:ℤ) : ℝ) = ((5279:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_700 : ((((452227546761 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5281, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5279 < q → q < 5281 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5281).mp (by decide +kernel))) hgap
  have hprev := s2L_699
  have hrat : ((452227546761 : ℚ) / 1000000000000) ≤ ((90445502181 : ℚ) / 200000000000) + (5281:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452227546761 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90445502181 : ℚ) / 200000000000) : ℚ) : ℝ) + ((5281:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5281:ℚ)^(-2:ℤ) : ℝ) = ((5281:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_701 : ((((452227582401 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5297, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5281 < q → q < 5297 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5297).mp (by decide +kernel))) hgap
  have hprev := s2L_700
  have hrat : ((452227582401 : ℚ) / 1000000000000) ≤ ((452227546761 : ℚ) / 1000000000000) + (5297:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452227582401 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452227546761 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((5297:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5297:ℚ)^(-2:ℤ) : ℝ) = ((5297:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))

end

end Work.RHContract.RegionI
