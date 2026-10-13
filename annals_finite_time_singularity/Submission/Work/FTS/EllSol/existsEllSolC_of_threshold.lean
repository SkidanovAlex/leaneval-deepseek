import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum.Ineq
import Submission.Work.FTS.EllSol.existsEllSolC_classC_noEst

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.EllSol.existsEllSolC_of_threshold` (curric-46 lead install, 2026-10-10)

Route (b) of `cbc/fts_final_redesign.md` §G5: `existsEllSolC_classC_of` with the hypothesis
"`EllClassOk 8` for all `α ≤ 1/4`" replaced by "for all `α ≤ α₁`, some `α₁ > 0`" — the shape
that A2 (`Work.FTS.ClassC.ellClassOk_exists_of_classC`) delivers. Same proof, threshold
`min α₀ α₁`. PROVED; does not use `vthTransfer_classC`.

`ExistsEllSolC` from A2 is then `existsEllSolC_of_threshold ClassC.ellClassOk_exists_of_classC`
(see `Submission.Work.FTS.FinalV2.WireSkeleton`, `existsEllSolC_routeB`).
-/

namespace Work.FTS.EllSol

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- `existsEllSolC_classC_of` re-thresholded: `EllClassOk 8` is only needed for `α ≤ α₁`. -/
theorem existsEllSolC_of_threshold
    (hb : ∃ α₁ : ℝ, 0 < α₁ ∧ ∀ α : ℝ, 0 < α → α ≤ α₁ → ∀ g : Fn,
      Work.FTS.ClassC.ClassC α g → ∃ Ψ : Fn, Work.FTS.EllExist.EllClassOk 8 α g Ψ) :
    Work.FTS.ClassC.ExistsEllSolC := by
  obtain ⟨α₁, hα₁, hb⟩ := hb
  obtain ⟨Ce, α₀, hCe, hα₀, hPkg⟩ :=
    Work.FTS.EllSol.ellPkgConj_of_classOk (Work.FTS.EllSol.ellEstUnifAll 4 (by norm_num))
      (Work.FTS.EllSol.ellEstUnifAll 6 (by norm_num))
  refine ⟨Ce, hCe, min α₀ α₁, lt_min hα₀ hα₁, ?_⟩
  intro α hα hαm
  have hα₀' : α ≤ α₀ := le_trans hαm (min_le_left _ _)
  have hα₁' : α ≤ α₁ := le_trans hαm (min_le_right _ _)
  let P : Fn → Fn → Prop := fun g Ψ =>
    Work.FTS.EllExist.EllClassOk 8 α g Ψ ∧ Work.FTS.VocabO.EllPkgGo α Ce g Ψ ∧
      Work.FTS.ClassC.EllPkgK α 6 Ce g Ψ
  have hPkg' : ∀ g Ψ : Fn, Work.FTS.ClassC.ClassC α g →
      Work.FTS.EllExist.EllClassOk 8 α g Ψ → P g Ψ := by
    intro g Ψ hg hok
    have h := hPkg α g Ψ hα hα₀' (Work.FTS.EllSol.classC_to_ellSolClassC hg) hok
    exact ⟨hok, h.1, Work.FTS.EllSol.EllPkgK_of_ellSol h.2⟩
  have hP0 : P 0 0 :=
    hPkg' 0 0 (Work.FTS.ClassC.classC_zero α) (Work.FTS.EllSol.ellClassOk_zero_eight_fts α)
  have hPlin : ∀ g g' Ψ Ψ' : Fn, ∀ c : ℝ, Work.FTS.ClassC.ClassC α g →
      Work.FTS.ClassC.ClassC α g' → P g Ψ → P g' Ψ' →
      P (g + c • g') (Ψ + c • Ψ') := by
    intro g g' Ψ Ψ' c hg hg' hP hP'
    exact hPkg' (g + c • g') (Ψ + c • Ψ')
      (Work.FTS.ClassC.classC_add hg (Work.FTS.ClassC.classC_smul c hg'))
      (Work.FTS.ClassC.ellClassOk_add_gen 8 hα c hg hg' hP.1 hP'.1)
  have hex : ∀ g, Work.FTS.ClassC.ClassC α g → ∃ Ψ, P g Ψ := by
    intro g hg
    obtain ⟨Ψ, hok⟩ := hb α hα hα₁' g hg
    exact ⟨Ψ, hPkg' g Ψ hg hok⟩
  obtain ⟨E, hE⟩ := Work.FTS.ClassC.exists_linear_selector_classC hP0 hPlin hex
  exact ⟨E, fun g hg => ⟨(hE g hg).2.1, (hE g hg).2.2⟩⟩

end Work.FTS.EllSol
