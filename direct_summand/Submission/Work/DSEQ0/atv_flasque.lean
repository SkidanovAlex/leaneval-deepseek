import Mathlib
import Submission.Work.DSF1.Sheaf.AcycDefs
import Submission.Work.DSF1.Sheaf.CechSheafTerm
import Submission.Work.DSF1.Sheaf.CechSheafRestr
import Submission.Work.DSF1.Sheaf.SSEBasic
import Submission.Work.DSF1.Sheaf.CechAug
import Submission.Work.DSF1.Sheaf.CechAugNat
import Submission.Work.DSF1.Sheaf.cechAugNat_exact_v2
import Submission.Work.DSF1.Sheaf.cechAugNat_injective
import Submission.Work.DSF1.Sheaf.cechAugNat_comp_cechSheafD
import Submission.Work.DSF1.Sheaf.isFlasque_restrL
import Submission.Work.DSF1.Sheaf.isFlasque_cechSheafTerm
import Submission.Work.DSF1.Sheaf.isSheaf_cechSheafTerm
import Submission.Work.DSF1.Sheaf.cechTrivAll_local
import Submission.Work.DSF1.Sheaf.cechTrivAt_of_flasque_terms
import Submission.Work.DSF1.Sheaf.cechTrivAll_of_restrP

/-!
# Flasque sheaves of modules have trivial Čech cocycles

`Work.DSEQ0.exists_cechAug'` and `Work.DSEQ0.flasque_hasCechCohomology'` are private copies of
`Work.DSF1.Sheaf.exists_cechAug` and `Work.DSF1.Sheaf.flasque_hasCechCohomology`.

The originals live in files whose import closure contains
`Submission/Work/DSF1/Sheaf/cechAugNat_exact.lean`, which is currently under construction and does
not compile; the same statement is available, fully proved, as
`Work.DSF1.Sheaf.cechAugNat_exact_v2`, so the two results are re-derived here from the
`_v2` statement.  The proofs are the same as in the originals.

The mathematical content of `flasque_hasCechCohomology'` is: if `F` is a flasque sheaf of
`𝒪_X`-modules, then for every finite family of opens `U` the Čech cocycles of `U` with
coefficients in `F` trivialise (`Work.DSF1.Sheaf.HasCechCohomology F`).
-/

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Simplicial BigOperators

namespace Work.DSEQ0

universe u

/-- **The augmentation of the sheaf-level Čech complex.**  For a sheaf `P` of abelian groups, a
family of opens `U` and an open `W ≤ ⨆ U`, the degree-zero cocycles of the Čech complex of `U`
over `W` are exactly the sections of `P` over `⨆ U ⊓ W` (pushed forward by the augmentation).
This is `Work.DSF1.Sheaf.exists_cechAug`, re-derived from the fully proved
`Work.DSF1.Sheaf.cechAugNat_exact_v2`. -/
theorem exists_cechAug' {X : AlgebraicGeometry.Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    (P : CategoryTheory.Functor (Opposite (X.Opens)) (AddCommGrpCat.{u}))
    (hP : TopCat.Presheaf.IsSheaf P) :
    ∃ aug : Work.DSF1.Sheaf.restrL P (iSup U) ⟶ Work.DSF1.Sheaf.cechSheafTerm U P 0,
      (∀ (W : X.Opens), W ≤ iSup U → Function.Injective
        (fun x : (Work.DSF1.Sheaf.restrL P (iSup U)).obj (Opposite.op W) =>
          (aug.app (Opposite.op W)) x)) ∧
      (∀ (W : X.Opens), W ≤ iSup U →
        ∀ x : (Work.DSF1.Sheaf.cechSheafTerm U P 0).obj (Opposite.op W),
        ((Work.DSF1.Sheaf.cechSheafD U P 0).app (Opposite.op W)) x = 0 ↔
          ∃ y : (Work.DSF1.Sheaf.restrL P (iSup U)).obj (Opposite.op W),
            (aug.app (Opposite.op W)) y = x) ∧
      (CategoryTheory.CategoryStruct.comp aug (Work.DSF1.Sheaf.cechSheafD U P 0) = 0) := by
  refine ⟨Work.DSF1.Sheaf.cechAugNat U P, ?_, ?_, ?_⟩
  · intro W hW
    exact Work.DSF1.Sheaf.cechAugNat_injective U P hP (Opposite.op W) hW
  · intro W hW x
    exact Work.DSF1.Sheaf.cechAugNat_exact_v2 U P hP (Opposite.op W) hW x
  · exact Work.DSF1.Sheaf.cechAugNat_comp_cechSheafD U P

/-- **Flasque sheaves of `𝒪_X`-modules have trivial Čech cocycles.**  Copy of
`Work.DSF1.Sheaf.flasque_hasCechCohomology`, with `Work.DSEQ0.exists_cechAug'` in place of
`Work.DSF1.Sheaf.exists_cechAug`. -/
theorem flasque_hasCechCohomology' {X : AlgebraicGeometry.Scheme.{u}}
    (F : SheafOfModules X.ringCatSheaf)
    (hF : TopCat.Presheaf.IsFlasque ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj F).obj) :
    Work.DSF1.Sheaf.HasCechCohomology F := by
  intro ι _ U
  classical
  let P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u} := ((SheafOfModules.toSheaf X.ringCatSheaf).obj F).obj
  have hPsh : TopCat.Presheaf.IsSheaf P :=
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj F).property
  obtain ⟨aug, hmono, hexact0, hzero⟩ := exists_cechAug' (X := X) U P hPsh
  have hfl : ∀ n : ℕ, TopCat.Presheaf.IsFlasque (Work.DSF1.Sheaf.cechSheafTerm U P n) :=
    fun n => Work.DSF1.Sheaf.isFlasque_cechSheafTerm U P hF n
  have hsh : ∀ n : ℕ, TopCat.Presheaf.IsSheaf (Work.DSF1.Sheaf.cechSheafTerm U P n) :=
    fun n => Work.DSF1.Sheaf.isSheaf_cechSheafTerm U P hPsh n
  haveI : Fintype ι := Fintype.ofFinite ι
  -- Local triviality of cocycles, on the cover `W ⊓ U i` of `W` (`W ≤ ⨆ U`).
  have hloc : ∀ (n : ℕ) (W : X.Opens), W ≤ iSup U →
      ∀ x : (Work.DSF1.Sheaf.cechSheafTerm U P (n+1)).obj (op W),
      (Work.DSF1.Sheaf.cechSheafD U P (n+1)).app (op W) x = 0 →
      ∃ (m : ℕ) (W' : Fin m → X.Opens) (hW' : ∀ i, W' i ≤ W), iSup W' = W ∧
        ∀ i : Fin m, ∃ y : (Work.DSF1.Sheaf.cechSheafTerm U P n).obj (op (W' i)),
          (Work.DSF1.Sheaf.cechSheafD U P n).app (op (W' i)) y =
            (Work.DSF1.Sheaf.cechSheafTerm U P (n+1)).map (homOfLE (hW' i)).op x := by
    intro n W hW x hx
    refine ⟨Fintype.card ι, fun j => W ⊓ U ((Fintype.equivFin ι).symm j),
      fun j => inf_le_left, ?_, ?_⟩
    · have hsup : (⨆ j : Fin (Fintype.card ι), U ((Fintype.equivFin ι).symm j)) = iSup U := by
        apply le_antisymm
        · exact iSup_le (fun j => le_iSup U ((Fintype.equivFin ι).symm j))
        · refine iSup_le (fun i => ?_)
          simpa using le_iSup (fun j : Fin (Fintype.card ι) => U ((Fintype.equivFin ι).symm j))
            ((Fintype.equivFin ι) i)
      rw [← inf_iSup_eq W (fun j : Fin (Fintype.card ι) => U ((Fintype.equivFin ι).symm j)),
        hsup, inf_eq_left.mpr hW]
    · intro j
      have hcyc : (Work.DSF1.Sheaf.cechSheafD U P (n+1)).app
          (op (W ⊓ U ((Fintype.equivFin ι).symm j)))
          ((Work.DSF1.Sheaf.cechSheafTerm U P (n+1)).map
            (homOfLE (inf_le_left : W ⊓ U _ ≤ W)).op x) = 0 := by
        rw [← AddCommGrpCat.comp_apply,
          (Work.DSF1.Sheaf.cechSheafD U P (n+1)).naturality (homOfLE (inf_le_left : W ⊓ U _ ≤ W)).op,
          AddCommGrpCat.comp_apply, hx, map_zero]
      exact (Work.DSF1.Sheaf.cechTrivAll_local U ((Fintype.equivFin ι).symm j)
        (W ⊓ U ((Fintype.equivFin ι).symm j)) inf_le_right P) n _ hcyc
  -- The flasque dévissage.
  have hdev := Work.DSF1.Sheaf.cechTrivAt_of_flasque_terms (V := iSup U)
    (K := Work.DSF1.Sheaf.cechSheafTerm U P)
    (d := Work.DSF1.Sheaf.cechSheafD U P) (hcomp := Work.DSF1.Sheaf.cechSheafD_comp U P)
    (F := Work.DSF1.Sheaf.restrL P (iSup U))
    (aug := aug) (hF := Work.DSF1.Sheaf.isFlasque_restrL P hF (iSup U)) (hzero := hzero)
    (hexact0 := hexact0) (hsh := hsh) (hfl := hfl) (hmono := hmono) (hlocal := hloc)
  refine Work.DSF1.Sheaf.cechTrivAll_of_restrP U P (iSup U) rfl fun p => ?_
  exact hdev p (iSup U) le_rfl

end Work.DSEQ0
