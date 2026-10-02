import Mathlib
import Submission.Work.Gen.EulerChernCP4
import Submission.Work.LerayHirsch.WhitneyParacompact
import Submission.Work.Whitney.chernProductSum_eq_fin
import Submission.Work.Gen.whitneySumFormulaPar_one_N
import Submission.Work.Kunneth.kunnethCP

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The `ℂP⁴`-restricted Whitney formula from its **paracompact** form

`Work.Gen.WhFormulaCP4` (`Submission/Work/Gen/EulerChernCP4.lean`) is the Whitney sum formula for
pairs of complex bundles over `ℂP⁴`, in the `Fin (j+1)` presentation.  It is the input of gaps `1`–`2`
of the deliverable `Work.Gen.generators8` (`README.md`, SESSION 9).

The tree currently offers it only from the *arbitrary-base* `Work.Gen.WhitneyFormula`
(`Work.Gen.whFormulaCP4_of_whitney`).  But `ℂP⁴` is compact Hausdorff, hence paracompact, and the
whole splitting / Leray–Hirsch / flag-bundle machinery of `Submission/Work/LerayHirsch/` is stated
over paracompact Hausdorff bases, where `Work.LerayHirsch.WhitneySumFormulaPar` lives
(`Submission/Work/LerayHirsch/WhitneyParacompact.lean`; `SplitsOverProj` is *false* off that class of
bases, see `WhitneySumFormulaPar`'s docstring and the reviews of
`Work.Gen.whitneySumFormulaPar_one_N`).

This module records that the paracompact form suffices: `WhFormulaCP4` follows from
`∀ m₁ m₂, WhitneySumFormulaPar m₁ m₂` alone.  So gaps `1`–`2` of the deliverable are gated on the
*paracompact* Whitney formula (which the LERAYHIRSCH route can deliver, with
`Work.Whitney.TopClassMul` and the `(1,N)` family as its inputs) and not on the strictly stronger
arbitrary-base form.
-/

open CategoryTheory

namespace Work.Gen

noncomputable section

/-- **`WhFormulaCP4` from the paracompact Whitney formula.**  The bridge is
`Work.Whitney.chernProductSum_eq_fin`: its right-hand side is literally the `Fin (j+1)` sum of
`Work.Gen.WhFormulaCP4`, and `Work.LerayHirsch.WhitneySumFormulaPar` gives the left-hand side. -/
theorem whFormulaCP4_of_par
    (h : ∀ m₁ m₂ : ℕ, Work.LerayHirsch.WhitneySumFormulaPar m₁ m₂) : WhFormulaCP4 := by
  intro ι₁ ι₂ _ _ m₁ m₂ j Z₁ Z₂
  rw [h m₁ m₂ Z₁ Z₂ j]
  exact Work.Whitney.chernProductSum_eq_fin Z₁ Z₂ j

/-! ## The paracompact Whitney formula from the Leray--Hirsch roof

`Work.LerayHirsch.whitneySumFormulaPar_of_lerayHirsch` (`Submission/Work/LerayHirsch/
WhitneyParacompact.lean`) is the roof: it needs exactly two inputs, the Leray--Hirsch theorem for
every complex bundle (`hLH`) and the `(1,N)` family (`hLine`).  The second is
`Work.Gen.whitneySumFormulaPar_one_N`, proved in this area; so the *whole* input of the deliverable
`Work.Gen.generators8` reduces to `hLH` alone. -/

/-- **The paracompact Whitney sum formula, from the Leray--Hirsch theorem.**  This is
`whitneySumFormulaPar_of_lerayHirsch` with its `(1,N)` input discharged by
`Work.Gen.whitneySumFormulaPar_one_N`, so that only the Leray--Hirsch theorem remains. -/
theorem whitneySumFormulaPar_of_lerayHirsch'
    (hLH : ∀ {m : ℕ} {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]
      (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι), Work.LerayHirsch.LerayHirschFull Z) :
    ∀ m₁ m₂ : ℕ, Work.LerayHirsch.WhitneySumFormulaPar m₁ m₂ :=
  Work.LerayHirsch.whitneySumFormulaPar_of_lerayHirsch hLH
    Work.Gen.whitneySumFormulaPar_one_N

/-- The same from `Work.LerayHirsch.KunnethCP` (the form in which the Leray--Hirsch chapter states
its remaining input). -/
theorem whitneySumFormulaPar_of_kunnethCP'
    (hK : Work.LerayHirsch.KunnethCP) :
    ∀ m₁ m₂ : ℕ, Work.LerayHirsch.WhitneySumFormulaPar m₁ m₂ :=
  Work.LerayHirsch.whitneySumFormulaPar_of_kunnethCP hK
    Work.Gen.whitneySumFormulaPar_one_N

/-! ## The last input, discharged

`Work.Kunneth.kunnethCP` (`Submission/Work/Kunneth/kunnethCP.lean`) proves
`Work.LerayHirsch.KunnethCP`, and `Work.LerayHirsch.lerayHirschFull_of_kunnethCP` converts it into
the Leray--Hirsch decomposition of an arbitrary bundle.  So the `hLH` hypothesis of
`whitneySumFormulaPar_of_lerayHirsch'` — and with it the input of the whole GEN chain — is
available. -/

/-- **The Leray--Hirsch decomposition for every complex gluing-data bundle**, from the KUNNETH
area's `Work.Kunneth.kunnethCP`. -/
theorem lerayHirschFull_all {m : ℕ} {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    Work.LerayHirsch.LerayHirschFull Z :=
  Work.LerayHirsch.lerayHirschFull_of_kunnethCP Work.Kunneth.kunnethCP Z

end

end Work.Gen
