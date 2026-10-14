import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Sqrt
import Submission.Work.FTS.StrongEps.EpsE4Thr.Coer1LhatO
import Submission.Work.FTS.StrongEps.EpsE4Thr.step2_data_ge_O
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkDzdIterSqLe
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.hkMem_fk_mul
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.DelicateHon
import Submission.Work.FTS.StrongPersist.N6Trans.T1Hon.EasyLeibIntBound
import Submission.Work.FTS_EllLimOK.PkgRepair
import Submission.Work.FTS_MuLamOK.Rows.Rl1Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "IP4" => Work.FTS.CoercivityFix.Assembly.IP4
local notation "IP2" => Work.FTS.CoercivityFix.Assembly.IP2
local notation "IP3" => Work.FTS.CoercivityFix.Assembly.IP3

/-- **The `Ê₂`-defect norm bound on the open class** (the open analogue of
`Assembly.hE2_unif`), from `E2hat_HkSq_le_uniform_O` via `Real.sqrt`. -/
theorem hE2_unif_O (n : ℕ) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ α : ℝ, 0 < α → ∀ f : Fn, RegQo α (n + 1) f →
      Work.Spaces.HkNorm α n (Work.FTS.CoercivityFix.E2hat f)
        ≤ κ * (Work.Spaces.HkNorm α n f + Work.Spaces.HkNorm α n (Work.Spaces.Dth f)) := by
  obtain ⟨Cn, hCn, hb⟩ := E2hat_HkSq_le_uniform_O n
  refine ⟨Real.sqrt Cn, Real.sqrt_nonneg _, fun α hα f hf => ?_⟩
  have hA0 : 0 ≤ Work.Spaces.HkSq α n f := Work.Spaces.HkSq_nonneg α n f
  have hB0 : 0 ≤ Work.Spaces.HkSq α n (Work.Spaces.Dth f) :=
    Work.Spaces.HkSq_nonneg α n _
  have hsq : Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)
      ≤ (Real.sqrt (Work.Spaces.HkSq α n f)
          + Real.sqrt (Work.Spaces.HkSq α n (Work.Spaces.Dth f))) ^ 2 := by
    rw [add_sq, Real.sq_sqrt hA0, Real.sq_sqrt hB0]
    nlinarith [Real.sqrt_nonneg (Work.Spaces.HkSq α n f),
      Real.sqrt_nonneg (Work.Spaces.HkSq α n (Work.Spaces.Dth f)),
      mul_nonneg (Real.sqrt_nonneg (Work.Spaces.HkSq α n f))
        (Real.sqrt_nonneg (Work.Spaces.HkSq α n (Work.Spaces.Dth f)))]
  have hsplit : Real.sqrt (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f))
      ≤ Real.sqrt (Work.Spaces.HkSq α n f)
        + Real.sqrt (Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by
    have h := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))] at h
  rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, Work.Spaces.HkNorm]
  calc Real.sqrt (Work.Spaces.HkSq α n (Work.FTS.CoercivityFix.E2hat f))
      ≤ Real.sqrt (Cn * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f))) :=
        Real.sqrt_le_sqrt (hb α hα f hf)
    _ = Real.sqrt Cn
          * Real.sqrt (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) :=
        Real.sqrt_mul hCn.le _
    _ ≤ Real.sqrt Cn * (Real.sqrt (Work.Spaces.HkSq α n f)
          + Real.sqrt (Work.Spaces.HkSq α n (Work.Spaces.Dth f))) :=
        mul_le_mul_of_nonneg_left hsplit (Real.sqrt_nonneg Cn)


end Work.FTS.StrongEps.EpsE4Thr
