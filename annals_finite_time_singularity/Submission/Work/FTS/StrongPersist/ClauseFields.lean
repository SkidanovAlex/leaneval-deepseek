/-
# `Work.FTS.StrongPersist.ClauseFields` — inhabited fields of the level-six clause packages

The clause packages of `Defs.lean` are interfaces; this file records the fields that are
**proved** for the concrete objects, so that a consumer of `persist_H6` can see exactly what is
still open.

* `N6Norm_l12H` — the `l12H` field of `N6Norm`: the angular average `L₁₂` maps the honest
  `ℋ⁶`-class into itself with an `α`-independent constant.  This is proved (for `Cpow = 0`) in
  `Submission/Work/FTS/StrongPersist/N6_L12H.lean` by the level-four argument of
  `FTS/OpenPkg/l12H_field.lean` re-run at level six: `L₁₂(g)` is `θ`-independent, so only the
  radial slots survive, the index-raising recursion `D_z^i L₁₂(g) = -Qang g (i-1)` turns the
  slots into angular moments, and the weighted `L²`-bound for the moments (`QangSq6`) closes.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.Defs
import Submission.Work.FTS.StrongPersist.N6_L12H

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.VocabO (HQo)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The `l12H` field of `N6Norm` is inhabited.**  `∃ Xi Cpow α₂` (with `Xi > 0`, `Cpow ≥ 0`,
`α₂ > 0`) such that for every `α ∈ (0, α₂]` and every `g` of the honest `ℋ⁶`-class with vanishing
zero mode, `z ↦ L₁₂(g)(z)` is in `ℋ⁶` and `|L₁₂(g)|_{ℋ⁶} ≤ Xi α^{-Cpow} |g|_{ℋ⁶}`.  (The proved
witness has `Cpow = 0` and an explicit `Xi`.) -/
theorem N6Norm_l12H :
    ∃ Xi Cpow α₂ : ℝ, 0 < Xi ∧ 0 ≤ Cpow ∧ 0 < α₂ ∧
      ∀ α ∈ Set.Ioc 0 α₂, ∀ g : Fn, HQo α 6 g → Work.Construction.L12 g 0 = 0 →
        H6Mem α (fun z θ => Work.Construction.L12 g z) ∧
        Xn6 α (fun z θ => Work.Construction.L12 g z) ≤ Xi * α ^ (-Cpow) * Xn6 α g := by
  obtain ⟨Xi, Cpow, hXi, hCp, h⟩ := N6_L12H
  exact ⟨Xi, Cpow, 1, hXi, hCp, one_pos, fun α hα => h α hα.1⟩

end Work.FTS.StrongPersist
