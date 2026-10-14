import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.StrongEps.EpsE4Thr.UnifIPOIP4
import Submission.Work.FTS.StrongPersist.H6Row6.Basic
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkDzdIterSqLe
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundR
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.UnifIPOOfCoer =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.Nonlin (Xn)

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "IP4" => Work.FTS.CoercivityFix.Assembly.IP4

/-- **`UnifIPO` for `IP4` from the two remaining clauses.**

`lo` and `up` are supplied by `lo_four_open`/`up_four_open` (which hold for every `α > 0` on
`RegQo α 4`/`RegQo α 5`, hence a fortiori on the coercivity class `CoerAdmO`).

The `lo`/`up` constants are *existential*, so the conclusion returns them together with `Ccs`; the
`coer` and `Dz_self` clauses are taken at the caller's `α₂` (the reduction pins the range of the
resulting interface to `min α₂ 1`). -/
theorem unifIPO_IP4_of_coer {c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ}
    (h₁ : 0 < c₁) (h₂ : 0 < c₂) (h₁' : 0 < c₁') (h₂' : 0 < c₂')
    (h₁'' : 0 < c₁'') (h₂'' : 0 < c₂'')
    {α₂ cc : ℝ} (hα₂ : 0 < α₂) (hcc : 0 < cc)
    (hcoer : ∀ α ∈ Set.Ioc 0 α₂, ∀ f : Fn, CoerAdmO α f →
      cc * Work.Spaces.HkSq α 4 f
        ≤ IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α (Work.Coercivity.LGammaT α f) f)
    (hdz : ∃ Cdz : ℝ, 0 < Cdz ∧ ∀ α ∈ Set.Ioc 0 α₂, ∀ f : Fn, CoerAdmO α f →
      |IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α (Work.Spaces.Dz f) f| ≤ Cdz * Xn α f ^ 2) :
    ∃ clo Cup Ccs : ℝ, 0 < clo ∧ 0 < Cup ∧ 0 < Ccs ∧
      UnifIPO (IP4 c₁ c₂ c₁' c₂' c₁'' c₂'') (min α₂ 1) cc clo Cup Ccs := by
  obtain ⟨clo, hclo, hlo⟩ := lo_four_open (c₁ := c₁) (c₂ := c₂) (c₁' := c₁') (c₂' := c₂')
    (c₁'' := c₁'') (c₂'' := c₂'') h₁ h₂ h₁' h₂' h₁'' h₂''
  obtain ⟨Cup, hCup, hup⟩ := up_four_open (c₁ := c₁) (c₂ := c₂) (c₁' := c₁') (c₂' := c₂')
    (c₁'' := c₁'') (c₂'' := c₂'') h₁ h₂ h₁' h₂' h₁'' h₂''
  obtain ⟨Ccs, hCcs, hU⟩ :=
    unifIPO_IP4_of_open_clauses (c₁ := c₁) (c₂ := c₂) (c₁' := c₁') (c₂' := c₂')
      (c₁'' := c₁'') (c₂'' := c₂'')
      (le_of_lt h₁) (le_of_lt h₂) (le_of_lt h₁') (le_of_lt h₂') (le_of_lt h₁'') (le_of_lt h₂'')
      hα₂ hcc hclo hCup
      (fun α hα f hf => hlo α hα.1 f hf.regQoFour)
      (fun α hα f hf => hup α hα.1 f hf.1)
      hcoer hdz
  exact ⟨clo, Cup, Ccs, hclo, hCup, hCcs, hU⟩

end Work.FTS.StrongEps.EpsE4Thr
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Row6.Lift =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Row6

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false





end Work.FTS.StrongPersist.H6Row6
end
end
