import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.StrongEps.E4R3.Flow5
import Submission.Work.FTS.IPGen.IP4Add
import Submission.Work.FTS.IPGen.IP4Smul
import Submission.Work.FTS.CoercivityFix.Transfer.H1IP_cs_of_mem
import Submission.Work.FTS.CoercivityFix.Assembly.V_core
import Submission.Work.FTS.CoercivityFix.Assembly.H1IP_core_Q

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Flow5Leaves/IP4Algebra.lean` — the three algebraic facts about `IP4` used by the product rule

* `IP4_add_open`  — additivity of `IP4` in its first argument on the open class `HQo α 4`
                    (`IPGen.Comm2o_three`; the `RegQ`-based `Assembly.V_core` is unusable here);
* `IP4_symm_fts`  — symmetry for arbitrary coefficients (`Assembly.vc_symm` + `H1IP_comm`);
* `IP4_cs_HQo`    — Cauchy–Schwarz on `HQo α 4` with a constant depending only on the six step
                    coefficients (three lifts of `StrongPersist.abs_HkIPStep_le` above
                    `Transfer.H1IP_cs_of_mem`).

These are the `ℋ⁴`-versions of `StrongEps/IP4_Jeps_comm.lean`'s lemmas; they are restated here
because that module imports `StrongEps.IP6_Jeps_comm`, which declares a `smoothOpen_Jeps` clashing
with the one in `StrongEps.JepsSmoothOpen` (already in the cone of `E4R3/Flow5.lean`), so that the
two cannot be imported together.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Flow5Leaves

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

local notation "IP4" => Work.FTS.CoercivityFix.Assembly.IP4

/-- **Additivity of `IP4` in its first argument on the open class `HQo α 4`** (the `Comm2o`
induction of `IPGen`, `Comm2o_three`). -/
theorem IP4_add_open {α : ℝ} (hα : 0 < α) {c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ} {f₁ f₂ g : Fn}
    (h₁ : Work.FTS.EllipticEst.SmoothOpen f₁) (h₂ : Work.FTS.EllipticEst.SmoothOpen f₂)
    (h₃ : Work.FTS.EllipticEst.SmoothOpen g)
    (m₁ : Work.Spaces.HkMem α 4 f₁) (m₂ : Work.Spaces.HkMem α 4 f₂)
    (m₃ : Work.Spaces.HkMem α 4 g) :
    IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α (f₁ + f₂) g
      = IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f₁ g + IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f₂ g :=
  (Work.FTS.IPGen.Comm2o_three α (by linarith [hα])).add f₁ f₂ g h₁ h₂ h₃ m₁ m₂ m₃

/-- **Symmetry of `IP4`** for arbitrary coefficients (the recursion `HkIPStep` preserves symmetry,
`Assembly.vc_symm`, and its base `H1IP` is symmetric, `Assembly.H1IP_comm`). -/
theorem IP4_symm_fts (c₁ c₂ c₁' c₂' c₁'' c₂'' α : ℝ) (f g : Fn) :
    IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f g = IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α g f :=
  Work.FTS.CoercivityFix.Assembly.vc_symm (c₁ := c₁'') (c₂ := c₂'')
    (Work.FTS.CoercivityFix.Assembly.vc_symm (c₁ := c₁') (c₂ := c₂')
      (Work.FTS.CoercivityFix.Assembly.vc_symm (c₁ := c₁) (c₂ := c₂)
        (Work.FTS.CoercivityFix.Assembly.H1IP_comm α))) f g

/-- **Cauchy–Schwarz for `IP4` on the open class `HQo α 4`**, with a constant depending only on the
six step coefficients: three lifts of `StrongPersist.abs_HkIPStep_le` above the `ℋ¹`-bound
`Transfer.H1IP_cs_of_mem`. -/
theorem IP4_cs_HQo (c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ) :
    ∃ CC : ℝ, 0 < CC ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 → ∀ f g : Fn,
      Work.FTS.VocabO.HQo α 4 f → Work.FTS.VocabO.HQo α 4 g →
      |IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f g|
        ≤ CC * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 4 g := by
  refine ⟨(1 + |c₁''| + |c₂''|) * ((1 + |c₁'| + |c₂'|) * ((1 + |c₁| + |c₂|) * 10 ^ 22)),
    by positivity, ?_⟩
  intro α hα f g hf hg
  have hα0 : 0 < α := hα.1
  have hbase : ∀ u v : ℝ → ℝ → ℝ, Work.FTS.VocabO.HQo α 1 u → Work.FTS.VocabO.HQo α 1 v →
      |Work.Coercivity.H1IP α u v| ≤ 10 ^ 22 * Work.Spaces.HkNorm α 1 u
        * Work.Spaces.HkNorm α 1 v :=
    fun u v hu hv => Work.FTS.CoercivityFix.Transfer.H1IP_cs_of_mem α hα0 u v hu.2 hv.2
  have h1 := Work.FTS.StrongPersist.abs_HkIPStep_le (α := α) hα0 (n := 1)
    (IP := Work.Coercivity.H1IP α) (CC := 10 ^ 22) (c₁ := c₁) (c₂ := c₂)
    (by norm_num) hbase
  have h2 := Work.FTS.StrongPersist.abs_HkIPStep_le (α := α) hα0 (n := 2)
    (IP := Work.Coercivity.HkIPStep c₁ c₂ (Work.Coercivity.H1IP α))
    (CC := (1 + |c₁| + |c₂|) * 10 ^ 22) (c₁ := c₁') (c₂ := c₂') (by positivity) h1
  have h3 := Work.FTS.StrongPersist.abs_HkIPStep_le (α := α) hα0 (n := 3)
    (IP := Work.Coercivity.HkIPStep c₁' c₂'
      (Work.Coercivity.HkIPStep c₁ c₂ (Work.Coercivity.H1IP α)))
    (CC := (1 + |c₁'| + |c₂'|) * ((1 + |c₁| + |c₂|) * 10 ^ 22))
    (c₁ := c₁'') (c₂ := c₂'') (by positivity) h2
  simpa only [Work.FTS.CoercivityFix.Assembly.IP4] using h3 f g hf hg

end Work.FTS.StrongEps.E4R3.Flow5Leaves
