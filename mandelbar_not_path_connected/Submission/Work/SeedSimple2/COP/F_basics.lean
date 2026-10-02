/-
Copyright: subproject `Submission/Work/SeedSimple2/` of `mandelbar_not_path_connected`.

# SeedSimple2/COP — L1: the basic facts about `F = (T_c)^10` at `z₁`

`NOTES_LEAD_mandelbar_rn0.md` §2, L1.  `F` fixes `z₁`, has derivative `1` there (so it is a
holomorphic local homeomorphism at `z₁`), and is therefore injective on a ball around `z₁`.
-/
import Mathlib
import Submission.Work.SeedSimple2.Main
import Submission.Work.ELRig.localInjOn_F
import Submission.Work.ELRig.rayPt_iterate

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set Function
open scoped Topology
open LeanEval.ComplexAnalysis (Tantibar)

set_option linter.unusedVariables false

noncomputable section

namespace Work.SeedSimple2.COP

theorem F_z₁ {c : ℂ} (d : Work.EL.RootParabolic c) : Work.EL.F c d.z₁ = d.z₁ := by
  rw [Work.EL.F_eq_tantibar]
  have h : (10 : ℕ) = 5 + 5 := rfl
  rw [h, Function.iterate_add_apply]
  exact (congrArg (fun z => (Tantibar c)^[5] z) d.per_half).trans d.per_half

theorem deriv_F_z₁ {c : ℂ} (d : Work.EL.RootParabolic c) : deriv (Work.EL.F c) d.z₁ = 1 := by
  show deriv ((Work.Landing.Tsq c)^[5]) d.z₁ = 1
  exact d.mult

theorem exists_injOn_F {c : ℂ} (d : Work.EL.RootParabolic c) :
    ∃ ε > 0, Set.InjOn (Work.EL.F c) (Metric.ball d.z₁ ε) :=
  Work.ELRig.localInjOn_F (c := c) (z₁ := d.z₁) (by rw [deriv_F_z₁ d]; exact one_ne_zero)

/-- Near `z₁`, a point different from `z₁` is not mapped to `z₁`. -/
theorem F_ne_z₁ {c : ℂ} (d : Work.EL.RootParabolic c) :
    ∃ ε > 0, ∀ z : ℂ, z ∈ Metric.ball d.z₁ ε → z ≠ d.z₁ → Work.EL.F c z ≠ d.z₁ := by
  obtain ⟨ε, hε, hinj⟩ := exists_injOn_F d
  refine ⟨ε, hε, fun z hz hz0 hF => hz0 ?_⟩
  refine hinj hz (Metric.mem_ball.mpr (by simpa using hε)) ?_
  rw [hF, F_z₁ d]

end Work.SeedSimple2.COP

end
