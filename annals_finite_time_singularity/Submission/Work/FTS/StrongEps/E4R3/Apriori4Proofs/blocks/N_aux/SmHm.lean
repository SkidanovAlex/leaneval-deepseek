import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.NMem6Parts
import Submission.Work.FTS.StrongEps.EpsGdotThird
import Submission.Work.FTS.StrongEps.ClassCRHS.SmoothOpenRHS
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `N_aux.SmHm` — the smoothness and `ℋ⁶`-honesty of the `N`-block `blkN`

The first two fields of `BData α w K (blkN α Φs w Φg)`, for the hypotheses of
`blocks/N_BData`:

* `SmoothOpen (blkN α Φs w Φg)`, from `ClassCRHS.SmoothOpenRHS` (open-quadrant `C^∞` of `N`);
* `HkMem α 6 (blkN α Φs w Φg)`, from `Apriori4Proofs.nMem6_of_parts`.

The only bridges needed are the repackaging `ClassC.EllPkgK → StrongPersist.EllPkgK` (the two
structures carry the two copies of `IsBslSolPos`) and the extraction of `H6Adm α w` from
`ClassC α w` plus the off-quadrant vanishing hypothesis (`H6Adm_of_classC_of_eqzero`).
-/

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- The two copies of the elliptic package at order `k` agree (they differ only in the copy of
`IsBslSolPos` they carry). -/
theorem ellPkgK_toStrongPersist {α : ℝ} {k : ℕ} {Ce : ℝ} {g Φg : Fn}
    (h : Work.FTS.ClassC.EllPkgK α k Ce g Φg) :
    Work.FTS.StrongPersist.EllPkgK α k Ce g Φg where
  sol := Work.FTS.StrongEps.isBslSolPos_toStrongPersist h.sol
  smooth := h.smooth
  R := h.R
  U := h.U
  V := h.V

/-- **`SmoothOpen` of the `N`-block.** -/
theorem smoothOpen_blkN {α Ce Cs : ℝ} {Φs w Φg : Fn}
    (hα : 0 < α) (hα1 : α ≤ 1) (hw : Work.FTS.ClassC.ClassC α w)
    (hgo : Work.FTS.VocabO.EllPkgGo α Ce w Φg)
    (hstar : Work.FTS.StrongPersist.StarPkg6 α Cs Φs) :
    Work.FTS.EllipticEst.SmoothOpen
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkN α Φs w Φg) :=
  Work.FTS.StrongEps.ClassCRHS.SmoothOpenRHS hα hα1 hw hgo hstar.toStarPkgo2 |>.2.2.2.2

/-- **`HkMem α 6` of the `N`-block.** -/
theorem hkMem_blkN {α Ce Cs : ℝ} {Φs w Φg : Fn}
    (hα : 0 < α) (hα1 : α ≤ 1) (hw : Work.FTS.ClassC.ClassC α w)
    (hzero : ∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (Real.pi / 2)) → w z θ = 0)
    (hgo : Work.FTS.VocabO.EllPkgGo α Ce w Φg)
    (hK : Work.FTS.ClassC.EllPkgK α 6 Ce w Φg)
    (hstar : Work.FTS.StrongPersist.StarPkg6 α Cs Φs) :
    Work.Spaces.HkMem α 6
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkN α Φs w Φg) :=
  (Work.FTS.StrongEps.E4R3.Apriori4Proofs.nMem6_of_parts hα hα1
    (Work.FTS.StrongEps.H6Adm_of_classC_of_eqzero hw hzero) hw.mem hgo.smooth
    hstar.smooth (ellPkgK_toStrongPersist hK) hstar).2

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux
