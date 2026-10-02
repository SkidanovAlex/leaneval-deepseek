import Mathlib
import Submission.Work.LerayHirsch.SplitLines
import Submission.Work.LerayHirsch.FlagBundle
import Submission.Work.LerayHirsch.WhitneyParacompact
import Submission.Work.LerayHirsch.LineSum
import Submission.Work.LerayHirsch.WhitneySumSnd
import Submission.Work.Whitney.ChernProduct
import Submission.Work.Whitney.chernClass_whitneySum_of_lt

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
# The general line-bundle case of the Whitney formula follows from its split case

`Work.LerayHirsch.WhitneySumFormulaSplit` is the *split* case of the Whitney sum formula: the ranks
`(1, n)` case for a line bundle and an explicit iterated direct sum `lineSumCore n M` of line
bundles.  This module proves that it implies the whole line-bundle case
`Work.LerayHirsch.WhitneySumFormulaPar 1 N` over paracompact Hausdorff bases, by pulling the
identity back along the **flag bundle** `W.π : W.P → B` of the second summand
(`Work.LerayHirsch.splittingPrinciple_of_kunnethCP_aux`), where
`π^*(Z₁ ⊕ Z₂) ≅ (π^*Z₁) ⊕ lineSumCore N W.L` has the shape of the split case.

The conclusion is read back with the injectivity of `π^*` on cohomology (`W.inj`), and the right-hand
side is moved along the pullback with `Work.Whitney.chernProductSum_CohMap` and
`Work.Whitney.chernProductSum_congr_second`.
-/

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom

noncomputable section

/-- **The general line-bundle case of the Whitney formula follows from its split case.** -/
theorem whitneySumFormulaPar_one_of_splitLines (hK : Work.LerayHirsch.KunnethCP)
    (hPar : ∀ {m : ℕ} {B : Type} [TopologicalSpace B] [ParacompactSpace B] [T2Space B]
      {ι : Type} [Fintype ι] (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι),
      ParacompactSpace (Work.LerayHirsch.ProjSpace Z))
    (hsplit : Work.LerayHirsch.WhitneySumFormulaSplit) :
    ∀ N : ℕ, Work.LerayHirsch.WhitneySumFormulaPar 1 N := by
  intro N B _htB _hparB _ht2B ι₁ ι₂ _hfin₁ _hfin₂ Z₁ Z₂ k
  obtain ⟨P, tP, hparP, ht2P, ⟨W⟩⟩ := splittingPrinciple_of_kunnethCP_aux hK hPar N Z₂
  letI : TopologicalSpace P := tP
  letI : ParacompactSpace P := hparP
  letI : T2Space P := ht2P
  letI : Fintype W.ιL := W.finL
  refine W.inj (2 * k) ?_
  rw [← chernClass_comap (Work.Whitney.whitneySum Z₁ Z₂) W.π,
    Work.Whitney.whitneySum_bundleComap Z₁ Z₂ W.π]
  have hstep : chernClass (1 + N) k
        (Work.Whitney.whitneySum (bundleComap Z₁ W.π) (bundleComap Z₂ W.π))
      = chernClass (1 + N) k
        (Work.Whitney.whitneySum (bundleComap Z₁ W.π) (lineSumCore N W.L)) :=
    Work.Whitney.chernClass_BundleIso_of_eq rfl _
      _ (nonempty_bundleIso_whitneySum_snd (bundleComap Z₁ W.π) (bundleComap Z₂ W.π)
        (lineSumCore N W.L) W.iso.some).some k
  rw [hstep, hsplit N (bundleComap Z₁ W.π) W.L k,
    Work.Whitney.chernProductSum_CohMap Z₁ Z₂ W.π k]
  exact (Work.Whitney.chernProductSum_congr_second (bundleComap Z₁ W.π)
    (bundleComap Z₂ W.π) (lineSumCore N W.L) k
    (fun i => Work.Whitney.chernClass_BundleIso_of_eq rfl (bundleComap Z₂ W.π)
      (lineSumCore N W.L) W.iso.some i)).symm

end

end Work.LerayHirsch
