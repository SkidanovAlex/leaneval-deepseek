import Mathlib
import Submission.Work.LerayHirsch.FlagBundle
import Submission.Work.LerayHirsch.paracompactSpace_projSpace
import Submission.Work.LerayHirsch.WhitneyParacompact
import Submission.Work.LerayHirsch.lerayHirsch_of_kunnethCP
import Submission.Work.LerayHirsch.lerayHirschGlue
import Submission.Work.LerayHirsch.SplitLines
import Submission.Work.LerayHirsch.whitneySumFormulaPar_one_of_splitLines

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# The chapter's results with every topological instance discharged

This module collects the headline results of the LERAYHIRSCH chapter in the form in which a consumer
uses them: the two topological instances of the projectivisation are *proved*
(`Work.LerayHirsch.t2Space_projSpace`, `Work.LerayHirsch.paracompactSpace_projSpace`), so the
splitting principle and the Whitney assembly over paracompact Hausdorff bases depend only on

* `hK : Work.LerayHirsch.KunnethCP` — the Leray–Hirsch theorem for the trivial case, subproject
  KUNNETH,

and, for the Whitney formula, on the line-bundle case
`∀ N, Work.LerayHirsch.WhitneySumFormulaPar 1 N`.
-/

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom

noncomputable section

/-- **The splitting principle, from Künneth alone**: for a complex gluing-data bundle of rank `m`
over a paracompact Hausdorff base there is a flag bundle `P` — paracompact and Hausdorff itself —
with `π^*` injective on cohomology in every degree and `π^*E ≅ lineSumCore m L` a direct sum of
complex line bundles over a common cover of `P`. -/
theorem splittingPrinciple_of_kunnethCP (hK : KunnethCP) :
    ∀ {m : ℕ} {B : Type} [TopologicalSpace B] [ParacompactSpace B] [T2Space B] {ι : Type}
      [Fintype ι] (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι),
      SplittingPrinciple Z :=
  fun {m B} _ _ _ {ι} _ Z =>
    splittingPrinciple_of_kunnethCP_aux hK (fun Z => paracompactSpace_projSpace Z) m Z

/-- **The Whitney sum formula over paracompact Hausdorff bases, from Künneth and the line-bundle
case**: the Leray–Hirsch theorem (`hK`) and the Whitney formula in ranks `(1, N)` over paracompact
Hausdorff bases (`hLine`) imply the Whitney formula `c_k(E ⊕ F) = Σ_{i+j=k} c_i(E) ⌣ c_j(F)` in all
ranks.  The two topological instances of the projectivisation are discharged here by
`Work.LerayHirsch.t2Space_projSpace` and `Work.LerayHirsch.paracompactSpace_projSpace`. -/
theorem whitneySumFormulaPar_of_kunnethCP (hK : KunnethCP)
    (hLine : ∀ N : ℕ, WhitneySumFormulaPar 1 N) :
    ∀ m₁ m₂ : ℕ, WhitneySumFormulaPar m₁ m₂ :=
  whitneySumFormulaPar_of_lerayHirsch (lerayHirschFull_of_kunnethCP hK) hLine

/-- **The Whitney sum formula in all degrees over paracompact Hausdorff bases, from the split
case**: the Leray–Hirsch theorem (`hK`) and the split case `Work.LerayHirsch.WhitneySumFormulaSplit`
— the ranks `(1, n)` case for a line bundle and an explicit direct sum of line bundles — imply the
Whitney formula `c_k(E ⊕ F) = Σ_{i+j=k} c_i(E) ⌣ c_j(F)` in all ranks, over paracompact Hausdorff
bases.  The passage from the split case to the line-bundle case is the flag-bundle argument
`Work.LerayHirsch.whitneySumFormulaPar_one_of_splitLines`, and the passage from the line-bundle case
to all ranks is `Work.LerayHirsch.whitneySumFormulaPar_of_lerayHirsch`. -/
theorem whitneySumFormulaPar_of_splitLines (hK : KunnethCP)
    (hsplit : WhitneySumFormulaSplit) :
    ∀ m₁ m₂ : ℕ, WhitneySumFormulaPar m₁ m₂ :=
  whitneySumFormulaPar_of_lerayHirsch (lerayHirschFull_of_kunnethCP hK)
    (whitneySumFormulaPar_one_of_splitLines hK
      (fun Z => paracompactSpace_projSpace Z) hsplit)

end

end Work.LerayHirsch
