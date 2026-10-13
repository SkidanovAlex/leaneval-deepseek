import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Defs
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.L6Ctx_JfamP_proof

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `E4R3/Apriori4Leaves/L6CtxJfamP.lean` — LEAF S5 (**PROVED**, session 23)

curric-46 install 2026-10-12 (`cbc/fts_apriori6_ruling.md` §3 S5).  The level-six context at the
projected mollified slices — what `H6Pair` (instantiated by the PROVED `H6Pair_ones3`) and
`H6Aux.H6Lin_IP6` consume — from `ClassC` + ball + `hEll` + `StarPkg6`.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.E4R4

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.StrongEps

set_option autoImplicit false

/-- **LEAF (S5), proved** the level-six context at the projected mollified slices. -/
theorem L6Ctx_JfamP :
    ∀ C₀ Ce Cs : ℝ, ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α ∈ Ioc 0 α₀,
    ∀ {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}, IsSmoothKernel ρ →
    (∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u)) →
    Work.FTS.StrongPersist.StarPkg6 α Cs Φs → MuLamOK α C₀ Φs E →
    ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ (g : Fam) (τ : ℝ), 0 ≤ τ →
      Work.FTS.ClassC.ClassC α (slice (JfamP ρ ε g) τ) →
      Work.FTS.Nonlin.Xn α (slice (JfamP ρ ε g) τ) ≤ C₀ * α ^ 2 →
      Work.FTS.StrongPersist.L6Ctx (IP6o) α (C₀ * α ^ 2) Ce Cs E Φs
        (JfamP ρ ε g) (Work.FTS.Nonlin.PsiCan Φs E (JfamP ρ ε g)) τ :=
  Work.FTS.StrongEps.E4R3.Apriori4Proofs.L6Ctx_JfamP_proof

end Work.FTS.StrongEps.EpsE4Thr.E4R4
