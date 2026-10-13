import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.ClassC.A1
import Submission.Work.FTS.ClassC.A6
import Submission.Work.FTS.ClassC.ellClassOk_add_gen
import Submission.Work.FTS.EllExist.LevelK
import Submission.Work.FTS.EllSol.ellPkgConj_of_classOk

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.EllSol.existsEllSolC_classC_of`

The class-`C` elliptic layer, in the "second order logic" form of the lead's design (A): from

* (`hb`) an *arbitrary* assignment `g ↦ Ψ` of a level-`8` solution to every profile `g` of the
  linear class `Work.FTS.ClassC.ClassC α g` (this is the existence node A2, here taken as a
  hypothesis, in the range `α ≤ 1/4`),
* (`hEst4`, `hEst6`) the uniform elliptic estimates at levels `4` and `6`,

build a **linear** solution operator `E : Fn →ₗ[ℝ] Fn` carrying both the `ℋ⁴`-package
`Work.FTS.VocabO.EllPkgGo` (owner `VocabO`) and the `ℋ⁶`-package `Work.FTS.ClassC.EllPkgK 6`,
i.e. the frozen `Prop` `Work.FTS.ClassC.ExistsEllSolC`.

## The route

* `Work.FTS.EllSol.ellPkgConj_of_classOk hEst4 hEst6` turns `EllClassOk 8` data over the older
  (7-field) class `Work.FTS.EllSol.ClassC` into the two packages at *one* constant `Ce` and one
  range `α ≤ α₀`.  The class `Work.FTS.ClassC.ClassC` implies that older class
  (`classC_to_ellSolClassC`; the extra fields `mem8`, `tr7` are simply dropped), and the two
  `EllPkgK` structures have identical fields (`ClassC.EllPkgK_of_ellSol`).
* The relation `P g Ψ := EllClassOk 8 α g Ψ ∧ EllPkgGo α Ce g Ψ ∧ EllPkgK α 6 Ce g Ψ` is
  `0`-inhabited (the zero profile: `ellClassOk_zero_eight_fts`) and closed under
  `(g, Ψ) ↦ (g + c • g', Ψ + c • Ψ')` over `ClassC α`: the first component is
  `Work.FTS.ClassC.ellClassOk_add_gen 8` (A3) and the two packages are *re-derived* from the
  hypothesis `ellPkgConj_of_classOk` rather than added.
* `Work.FTS.ClassC.exists_linear_selector_classC` (A6, the Hamel step) then produces the linear
  selector `E`.
-/

namespace Work.FTS.EllSol

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- The class `Work.FTS.ClassC.ClassC` (nine fields) implies the older class
`Work.FTS.EllSol.ClassC` (seven fields) of the `EllSol`/`VthAuxC` chain: the extra honesty fields
`mem8` and `tr7` are simply dropped. -/
theorem classC_to_ellSolClassC {α : ℝ} {g : Fn} (h : Work.FTS.ClassC.ClassC α g) :
    ClassC α g :=
  ⟨h.norm, h.reg, h.mem, h.tr, h.fsm, h.axis, h.l12⟩

/-- The two `EllPkgK` structures (in `Work.FTS.ClassC` and in `Work.FTS.EllSol`) have exactly the
same five fields, so either converts to the other. -/
theorem EllPkgK_of_ellSol {α : ℝ} {k : ℕ} {Ce : ℝ} {g Ψ : Fn}
    (h : EllPkgK α k Ce g Ψ) : Work.FTS.ClassC.EllPkgK α k Ce g Ψ :=
  ⟨h.sol, h.smooth, h.R, h.U, h.V⟩

/-- The zero profile has the zero level-`8` solution (the `0`-inhabitation of the relation used by
the Hamel step).  Verbatim the proof of `Work.FTS.ClassC.ellClassOk_zero_eight`, kept local so
that this module does not depend on the slot-based assembly `Work.FTS.ClassC.Main`. -/
theorem ellClassOk_zero_eight_fts (α : ℝ) :
    Work.FTS.EllExist.EllClassOk 8 α (0 : Fn) (0 : Fn) := by
  refine ⟨Work.FTS.EllipticEst.IsBslSol_zero α, ?_, ?_⟩
  · change ContDiffOn ℝ Work.Stability.smoothOrder (fun _ : ℝ × ℝ => (0 : ℝ))
      Work.FTS.EllipticEst.Q0
    exact contDiffOn_const
  · have horth : Work.Elliptic.orthSource (0 : Fn) = (0 : Fn) := Work.FTS.EllSol.orthSource_zero
    have hsin : Work.FTS.EllExist.shiftSing α (0 : Fn) (0 : Fn) = (0 : Fn) := by
      funext z θ
      rw [Work.FTS.EllExist.shiftSing_apply, Work.FTS.EllSol.Gsing_zero]
      simp
    rw [horth, hsin]
    exact Work.FTS.EllSol.ellWeakPos_zero α 8

theorem existsEllSolC_classC_of
    (hb : ∀ (α : ℝ), 0 < α → α ≤ 1 / 4 → ∀ g : Work.FTS.Galerkin.Fn,
      Work.FTS.ClassC.ClassC α g → ∃ Ψ : Work.FTS.Galerkin.Fn,
        Work.FTS.EllExist.EllClassOk 8 α g Ψ)
    (hEst4 : ∃ C : ℝ, 0 < C ∧ Work.FTS.EllipticEst.TT.EllEstUnif 4 C)
    (hEst6 : ∃ C : ℝ, 0 < C ∧ Work.FTS.EllipticEst.TT.EllEstUnif 6 C) :
    Work.FTS.ClassC.ExistsEllSolC := by
  -- the two packages at a single constant, from the uniform estimates
  obtain ⟨Ce, α₀, hCe, hα₀, hPkg⟩ := ellPkgConj_of_classOk hEst4 hEst6
  refine ⟨Ce, hCe, min α₀ (1 / 4), lt_min hα₀ (by norm_num), ?_⟩
  intro α hα hαm
  have hα₀' : α ≤ α₀ := le_trans hαm (min_le_left _ _)
  have hα4 : α ≤ 1 / 4 := le_trans hαm (min_le_right _ _)
  -- the relation carrying the solution class and the two packages
  let P : Fn → Fn → Prop := fun g Ψ =>
    Work.FTS.EllExist.EllClassOk 8 α g Ψ ∧ Work.FTS.VocabO.EllPkgGo α Ce g Ψ ∧
      Work.FTS.ClassC.EllPkgK α 6 Ce g Ψ
  have hPkg' : ∀ g Ψ : Fn, Work.FTS.ClassC.ClassC α g →
      Work.FTS.EllExist.EllClassOk 8 α g Ψ → P g Ψ := by
    intro g Ψ hg hok
    have h := hPkg α g Ψ hα hα₀' (classC_to_ellSolClassC hg) hok
    exact ⟨hok, h.1, EllPkgK_of_ellSol h.2⟩
  have hP0 : P 0 0 :=
    hPkg' 0 0 (Work.FTS.ClassC.classC_zero α) (ellClassOk_zero_eight_fts α)
  have hPlin : ∀ g g' Ψ Ψ' : Fn, ∀ c : ℝ, Work.FTS.ClassC.ClassC α g →
      Work.FTS.ClassC.ClassC α g' → P g Ψ → P g' Ψ' →
      P (g + c • g') (Ψ + c • Ψ') := by
    intro g g' Ψ Ψ' c hg hg' hP hP'
    exact hPkg' (g + c • g') (Ψ + c • Ψ')
      (Work.FTS.ClassC.classC_add hg (Work.FTS.ClassC.classC_smul c hg'))
      (Work.FTS.ClassC.ellClassOk_add_gen 8 hα c hg hg' hP.1 hP'.1)
  have hex : ∀ g, Work.FTS.ClassC.ClassC α g → ∃ Ψ, P g Ψ := by
    intro g hg
    obtain ⟨Ψ, hok⟩ := hb α hα hα4 g hg
    exact ⟨Ψ, hPkg' g Ψ hg hok⟩
  -- the Hamel step
  obtain ⟨E, hE⟩ := Work.FTS.ClassC.exists_linear_selector_classC hP0 hPlin hex
  exact ⟨E, fun g hg => ⟨(hE g hg).2.1, (hE g hg).2.2⟩⟩

end Work.FTS.EllSol
