/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/UnifIPOOfCoerFinal.lean` — the level-four coercivity
interface with a **single** remaining obligation: the coercivity of `𝓛_Γ^T`

Session 7 reduced the level-four barrier of the `ε`-scheme's a-priori estimate to the open-class
interface `UnifIPO (IP4 …)`.  Of its clauses

* the six algebraic clauses, `symm`, `cs` and `nonneg` are proved on the open class
  (`UnifIPOIP4.IP4_cs_open`, `unifIPO_IP4_of_open_clauses`);
* `lo` and `up` — the comparability of `IP4` with the squared `ℋ⁴`-norm — are proved
  (`LoFourOpen.lo_four_open`, `up_four_open`);
* `Dz_self` is proved (`dz_four_RegQo`);
* **`coer`** — the coercivity `cc·|f|²_{ℋ⁴} ≤ IP4 α (𝓛_Γ^T f) f` on `CoerAdmO` — is the single
  remaining clause (the paper's §6 estimate; its frozen version is the `CoercivityFix` chain,
  whose open-class re-run this session has begun: `IntPkgO`, `IntPkg_O`, `LedgerO`,
  `Coerc1Open.coer1_LGammaT_O_of_dzslot`, `StepCoerO.step_coer_O`, the four slot ports).

This module removes `Dz_self` from the hypotheses, so that `unifIPO_IP4_of_coer` has exactly one
input.  A consumer composes the resulting instance with `apriori_fourth_of_barrier_open` (taking
`hIP := hU`, `α₂ := min α₂ 1`, the `clo`/`Cup`/`Ccs` from the returned tuple).

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Real.Sqrt
import Submission.Work.FTS.StrongEps.EpsE4Thr.UnifIPOOfCoer
import Submission.Work.FTS.StrongEps.EpsE4Thr.dz_four_RegQo

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

/-- **`UnifIPO` for `IP4` from the coercivity clause alone.**  `lo`, `up` and `Dz_self` are
supplied by `lo_four_open`, `up_four_open` and `dz_four_RegQo`; `coer` is the hypothesis. -/
theorem unifIPO_IP4_of_coer_only {c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ}
    (h₁ : 0 < c₁) (h₂ : 0 < c₂) (h₁' : 0 < c₁') (h₂' : 0 < c₂')
    (h₁'' : 0 < c₁'') (h₂'' : 0 < c₂'')
    {α₂ cc : ℝ} (hα₂ : 0 < α₂) (hcc : 0 < cc)
    (hcoer : ∀ α ∈ Set.Ioc 0 α₂, ∀ f : Fn, CoerAdmO α f →
      cc * Work.Spaces.HkSq α 4 f
        ≤ IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α (Work.Coercivity.LGammaT α f) f) :
    ∃ clo Cup Ccs : ℝ, 0 < clo ∧ 0 < Cup ∧ 0 < Ccs ∧
      UnifIPO (IP4 c₁ c₂ c₁' c₂' c₁'' c₂'') (min α₂ 1) cc clo Cup Ccs := by
  obtain ⟨Cdz, hCdz, hdzb⟩ :=
    dz_four_RegQo (c₁ := c₁) (c₂ := c₂) (c₁' := c₁') (c₂' := c₂')
      (c₁'' := c₁'') (c₂'' := c₂'') h₁ h₂ h₁' h₂' h₁'' h₂''
  refine unifIPO_IP4_of_coer h₁ h₂ h₁' h₂' h₁'' h₂'' hα₂ hcc hcoer ⟨Cdz, hCdz, ?_⟩
  intro α hα f hf
  have h := hdzb α hα.1 f hf.1
  have hsq : (Xn α f) ^ 2 = Work.Spaces.HkSq α 4 f := by
    rw [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 f)]
  rwa [hsq]

end Work.FTS.StrongEps.EpsE4Thr
