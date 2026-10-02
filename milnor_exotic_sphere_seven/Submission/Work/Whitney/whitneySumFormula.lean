import Mathlib
import Submission.Work.Whitney.whitneySumFormulaSplit
import Submission.Work.LerayHirsch.Main
import Submission.Work.Kunneth.kunnethCP

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# THE WHITNEY SUM FORMULA for `Work.Thom.chernClass` over paracompact Hausdorff bases

With the split case `Work.Whitney.whitneySumFormulaSplit : Work.LerayHirsch.WhitneySumFormulaSplit`
settled (`Submission/Work/Whitney/whitneySumFormulaSplit.lean`), the whole assembly of area WHITNEY
closes:

* `Work.Whitney.whitneySumFormulaPar_one : ∀ N, Work.LerayHirsch.WhitneySumFormulaPar 1 N`
  (the `(1,N)` family: `Work.LerayHirsch.whitneySumFormulaPar_one_of_splitLines` with
  `Work.Kunneth.kunnethCP` and the paracompactness of the projectivisation);
* **`Work.Whitney.chernClass_whitneySum_paracompact`**: for complex bundles `Z₁`, `Z₂` over a
  paracompact Hausdorff base and every `k`,

    `c_k(Z₁ ⊕ Z₂) = Σ_{i+j=k} c_i(Z₁) ⌣ c_j(Z₂)`;

  this is `Work.LerayHirsch.WhitneySumFormulaPar`, i.e. deliverable item 2 of the area in the
  generality in which the workspace proves it (the split case — hence paracompactness — is needed
  because `Work.LerayHirsch.SplitsOverProj` is false off paracompact Hausdorff bases).

Outside the paracompact Hausdorff setting the two unconditional halves are on disk and are the
sharpest available: `Work.Whitney.chernClass_whitneySum_of_lt` (degrees `k ≤ max(m₁,m₂) − 1`, from the
induction hypothesis at smaller total rank) and `Work.Whitney.chernClass_whitneySum_top` (`(T)`).
-/

namespace Work.Whitney

open Work.TangentClasses Work.Thom

noncomputable section

/-- **The `(1,N)` family of the Whitney sum formula** over paracompact Hausdorff bases. -/
theorem whitneySumFormulaPar_one : ∀ N : ℕ, Work.LerayHirsch.WhitneySumFormulaPar 1 N :=
  Work.LerayHirsch.whitneySumFormulaPar_one_of_splitLines Work.Kunneth.kunnethCP
    (fun Z => Work.LerayHirsch.paracompactSpace_projSpace Z) whitneySumFormulaSplit

/-- **THE WHITNEY SUM FORMULA**: the total Chern class is multiplicative under direct sums,
`c_k(Z₁ ⊕ Z₂) = Σ_{i+j=k} c_i(Z₁) ⌣ c_j(Z₂)`, for complex vector bundles over a paracompact Hausdorff
base (`Work.LerayHirsch.WhitneySumFormulaPar`). -/
theorem chernClass_whitneySum_paracompact {m₁ m₂ : ℕ} {B : Type} [TopologicalSpace B]
    [ParacompactSpace B] [T2Space B] {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂) (k : ℕ) :
    Work.Thom.chernClass (m₁ + m₂) k (whitneySum Z₁ Z₂) = chernProductSum Z₁ Z₂ k :=
  Work.LerayHirsch.whitneySumFormulaPar_of_splitLines Work.Kunneth.kunnethCP
    whitneySumFormulaSplit m₁ m₂ Z₁ Z₂ k

/-- **The Whitney sum formula in all ranks**, in the `Prop` form of the LERAYHIRSCH chapter:
`Work.LerayHirsch.whitneySumFormulaPar_of_splitLines` with the two inputs discharged. -/
theorem whitneySumFormulaPar : ∀ m₁ m₂ : ℕ, Work.LerayHirsch.WhitneySumFormulaPar m₁ m₂ :=
  Work.LerayHirsch.whitneySumFormulaPar_of_splitLines Work.Kunneth.kunnethCP
    whitneySumFormulaSplit

end

end Work.Whitney
