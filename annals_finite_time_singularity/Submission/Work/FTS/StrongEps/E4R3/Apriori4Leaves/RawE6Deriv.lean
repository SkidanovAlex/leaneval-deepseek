import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `E4R3/Apriori4Leaves/RawE6Deriv.lean` — OPEN LEAF S4 (research-low/mid; RISK R2 — dispatch FIRST)

curric-46 install 2026-10-12 (`cbc/fts_apriori6_ruling.md` §3 S4 / Risk R2; REVIEW fix F5).
The raw level-six energy identity along a regular solution.

**R2 (REVIEW F5).** Per-slice `HkMem 6` + joint `C¹` (all `EpsRegP` gives) does NOT yield
`HasDerivAt rawE6`: domination and the global pieces (`L12(·)(0)` inside `P₀`, the elliptic solve
`E`) need a bound uniform in `τ`.  This leaf therefore carries the uniform-in-`τ` bound
`hbdd6 : ∃ B, ∀ τ ∈ [0,T], Xn6 α (slice g τ) ≤ B` as an EXPLICIT hypothesis (`EpsRegP` is not
edited).  Its consumer (the `ℋ⁶`-half `sixthChapterB_leaf`) does not have `hbdd6` from `EpsRegP`;
if this probe confirms `hbdd6` is needed, the lead decides whether to add it to `EpsRegP` (then
re-prove `EpsRegP.mono`, `RegGlueP`, `Reduction.exists_sol_of_localStep_apriori`, `EpsMemRegP`,
`EpsUniformMem_of_parts3`; `LocalStep3` must output it).
Route: L²-Fréchet differentiability of `τ ↦ D^a g(τ)` from `g(τ+h) − g(τ) = ∫ P₀JX`; continuity of
`s ↦ P₀JX(s)` into weighted L² from the `J` gain, `EpsRHSPLipXProof`, `EpsSlotLipP` and `hbdd6`.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.E4R4

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.StrongGlobal (Xn6)
open Work.FTS.StrongEps

set_option autoImplicit false

/-- **OPEN LEAF (S4)** continuity and derivative of the raw level-six energy. -/
theorem rawE6_deriv {α ε T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn} {g : Fam}
    (hρ : IsSmoothKernel ρ) (hα : 0 < α) (hα1 : α ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1) (hT : 0 < T)
    (hsol : IsEpsSolP α ρ ε T Φs E g₀ g) (hreg : EpsRegP α ρ ε T g)
    (hbdd6 : ∃ B : ℝ, ∀ τ ∈ Icc 0 T, Xn6 α (slice g τ) ≤ B) :
    ContinuousOn (rawE6 α g) (Icc 0 T) ∧
      ∀ τ ∈ Ioo 0 T, HasDerivAt (rawE6 α g)
        (2 * IP6o α (epsRHSP α ρ ε Φs E g τ) (slice g τ)) τ := by
  sorry

end Work.FTS.StrongEps.EpsE4Thr.E4R4
