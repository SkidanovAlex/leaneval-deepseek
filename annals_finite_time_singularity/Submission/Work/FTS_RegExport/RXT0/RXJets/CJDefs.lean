import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS_RegExport.RXT0.RXJets.slabDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT0.RXJets.CJHyps` — the hypothesis bundle of `coeffJetsJointCont`

`coeffJetsJointCont` has ten hypotheses (`hα`, `hα13`, `hEll`, `hEL3`, `hStar`, `hSol`, `hOK`,
`hμ`, `hL12`, `hSlot`).  The proof is split over several modules (the file-size guard of the
project forbids a single large module), so the ten are bundled here into one `Prop`-valued
structure; the statement of `coeffJetsJointCont` itself is *unchanged* and still takes the ten
hypotheses separately, constructing this structure at the top of its proof.
-/

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXT0.RXJets

set_option autoImplicit false

/-- **The hypothesis bundle of `coeffJetsJointCont`**, verbatim. -/
structure CJHyps (α C₀ Ce Cs : ℝ) (Φs : Work.FTS.Galerkin.Fn)
    (E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn) (g : Work.FTS.Galerkin.Fam) : Prop where
  hα : 0 < α
  hα13 : α ≤ 1 / 3
  hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) u →
    Work.FTS.Final.EllPkgGo (Work.FTS.Regularity.pExp α) Ce u (E u) ∧
      Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp α) 6 Ce u (E u)
  hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E
  hStar : Work.FTS.Final.StarPkgo2 (Work.FTS.Regularity.pExp α) Cs Φs
  hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g
  hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g
  hμ : Work.FTS.RegExportIface.ClockBd α Φs E g
  hL12 : ∀ S > 0, ∀ j : ℕ, j ≤ 2 →
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter j
      (fun z (_ : ℝ) => Work.Construction.L12
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) p.2) z) p.1 0)
      (Set.Ioi (0:ℝ) ×ˢ Set.Icc (0:ℝ) S) ∧
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter j
      (fun z (_ : ℝ) => Work.Construction.FK
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) p.2) z) p.1 0)
      (Set.Ioi (0:ℝ) ×ˢ Set.Icc (0:ℝ) S)
  hSlot : ∀ S > 0, ∀ j i : ℕ, j + i ≤ 2 →
    (ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed j i
      (fun z θ => Work.Construction.Vop
        (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
          (Work.FTS.Galerkin.slice g p.2.2) (E (Work.FTS.Galerkin.slice g p.2.2))) z θ)
      p.1 p.2.1)
      (Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S))) ∧
    (ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed j i
      (fun z θ => Work.Construction.Rop (Work.FTS.Regularity.pExp α)
        (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
          (Work.FTS.Galerkin.slice g p.2.2) (E (Work.FTS.Galerkin.slice g p.2.2))) z θ)
      p.1 p.2.1)
      (Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S))) ∧
    (ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed j i
      (fun z θ => Work.Construction.Uop (Work.FTS.Regularity.pExp α)
        (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
          (Work.FTS.Galerkin.slice g p.2.2) (E (Work.FTS.Galerkin.slice g p.2.2))) z θ
        / Real.sin (2 * θ)) p.1 p.2.1)
      (Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S)))

end Work.FTS_RegExport.RXT0.RXJets
