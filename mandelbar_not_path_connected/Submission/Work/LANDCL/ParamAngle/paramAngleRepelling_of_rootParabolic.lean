import Mathlib
import Submission.Work.LANDCL.Defs
import Submission.Work.LANDCL.ParamAngle.cycle_mem_ne_fixed

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LANDCL.ParamAngle

open LeanEval.ComplexAnalysis (Tantibar)

/-- **The window angle `paramAngle = 23/63` does not land at a parabolic point.**

At a root-parabolic parameter `c` the only parabolic points of `T_c` lie on the exact
period-`5` cycle of the characteristic point `z₁` (`Work.LANDCL.OnlyParabolicIsCycleOf`),
whereas the landing point of the periodic ray `R_c(23/63)` is fixed by `(T_c)^[6]`
(`Work.Landing.landsAt_periodic`, `23/63` having exact period `6` under angle doubling).

Were that landing point parabolic it would be `(T_c)^[j] z₁` for some `j < 5`; being fixed by
`(T_c)^[6]` it would then satisfy `T_c ((T_c)^[j] z₁) = (T_c)^[6 + j] z₁ = (T_c)^[j + 1] z₁ =
(T_c)^[j] z₁`, i.e. it would be a *fixed* point of `T_c` on the period-`5` cycle, which is
impossible (`Work.LANDCL.ParamAngle.cycle_mem_ne_fixed`).  Hence the landing point is not
parabolic, and the even-period landing dichotomy makes it repelling. -/
theorem paramAngleRepelling_of_rootParabolic {c : ℂ} (d : Work.EL.RootParabolic c)
    (hper : Work.Landing.PeriodicRaysLand c)
    (hdich : Work.Landing.EvenPeriodLandingDichotomy c)
    (huniq : Work.LANDCL.OnlyParabolicIsCycleOf c d.z₁) :
    Work.Final.ParamAngleRepelling c := by
  -- `23/63` is a periodic angle, so the ray `R_c(23/63)` lands.
  obtain ⟨z, hland⟩ :=
    hper Work.Landing.paramAngle
      ⟨6, by norm_num, Work.Landing.Angle.exactPeriodAngle_paramAngle.2.1⟩
  -- The landing point is a periodic point of `T_c` of period dividing `6`.
  have h6 : (Tantibar c)^[6] z = z :=
    Work.Landing.landsAt_periodic hland Work.Landing.Angle.exactPeriodAngle_paramAngle.2.1
  -- The landing point is not parabolic.
  have hpar : ∀ m : ℕ, ¬ Work.Landing.IsParabolic c m z := by
    intro m hm
    obtain ⟨h5, hne, hcycle⟩ := huniq
    obtain ⟨j, hj, hzj⟩ := hcycle z ⟨m, hm⟩
    -- `T_c z` is again `(T_c)^[6]`-fixed: `T_c z = T_c^{6+j} z₁ = T_c^{j+1} z₁`.
    have hA : (Tantibar c)^[6 + j] d.z₁ = (Tantibar c)^[j + 1] d.z₁ := by
      rw [show 6 + j = (j + 1) + 5 by omega, Function.iterate_add_apply, h5]
    have hTz : Tantibar c z = z := by
      rw [hzj, ← Function.iterate_succ_apply' (Tantibar c) j d.z₁, ← hA]
      rw [Function.iterate_add_apply, ← hzj]
      exact h6
    -- But `(T_c)^[j] z₁` is not a fixed point of `T_c` for `j < 5`.
    exact cycle_mem_ne_fixed c d.z₁ h5 hne j hj (by rwa [hzj] at hTz)
  exact Work.Final.ParamAngleRepelling.of_landing hdich hland hpar

end Work.LANDCL.ParamAngle
