import Mathlib
import Submission.Work.OROneRel.twoLetter_treeData_of_F2treeData
import Submission.Work.OROneRel.hnnConjMap_injective_of_tree
import Submission.Work.OROneRel.twoLetter_generation
import Submission.Work.OROneRel.winAssembly
import Submission.Work.OROneRel.tlWindowHalvesDefs
import Submission.Work.OROneRel.hnnConjSplit
import Submission.Work.OROneRel.isTree_coset_of_hnnConjMap_injective
import Submission.Work.OROneRel.graded_hnn_coset
import Submission.Work.OROneRel.winRhoRange_tree
import Submission.Work.OROneRel.bandComparison_freeTree

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.OROneRel

/-- **The two-letter target from the F₂-level crux.**  If the canonical comparison map of the band
pair *inside the free group* `F₂` is injective, then the target
`Work.OROneRel.twoLetter_hnnConjMap_injective` holds.  Route: the F₂-level injectivity together with
the (proved) F₂-level generation `tlH p q Wt ⊔ ⟪tlLowTau⟫ = ⊤` of
`Work.OROneRel.twoLetter_F2_generation` makes `IsTree (GradedHNN.Coset (tlH p q Wt) (tlLowTau p q))`
(`Work.OROneRel.isTree_coset_of_hnnConjMap_injective`), and
`Work.OROneRel.hnnConjMap_injective_of_tree` (with `stabilizer_baseC_eq'` and
`stabilizer_baseC_eq`/`actsWithoutInversions_coset`) turns that coset tree into the F₂-tree data;
`Work.OROneRel.twoLetter_treeData_of_F2treeData` descends it to a `G`-tree with vertex stabiliser
`winVertex = tlH · N / N`, and `Work.OROneRel.hnnConjMap_injective_of_treeData` gives the
conclusion. -/
theorem twoLetter_target_of_F2crux (p q l : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hl : 1 ≤ l)
    (hcop : Nat.Coprime p q)
    (Wt : ℤ → FreeGroup (Fin 2)) (hW0 : Wt 0 = 1)
    (hcoh : ∀ i : ℤ, Work.OROneRel.cohom (Work.OROneRel.tlW p q) (Wt i) = Multiplicative.ofAdd i)
    (hwin : ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0
        (Work.OROneRel.wordOf (Work.OROneRel.tlU p q)),
      Work.OROneRel.coverEdge e ∈ Work.OROneRel.winE (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ)))
    (htree : ∀ i : ℤ, 0 ≤ i → i ≤ (p : ℤ) * (q : ℤ) →
      ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0 (Work.OROneRel.wordOf (Wt i)),
        Work.OROneRel.coverEdge e ∈
          Work.OROneRel.winTree Wt (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ)))
    (hA : ∀ x : FreeGroup (Work.OROneRel.winBeta Wt (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ))),
      Work.OROneRel.winRho Wt (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ)) x ∈
          Subgroup.normalClosure ({Work.OROneRel.tlU p q ^ l} : Set (FreeGroup (Fin 2))) →
        x ∈ Subgroup.normalClosure
          ({Work.OROneRel.winRoot Wt (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ))
              (Work.OROneRel.tlU p q) ^ l} :
            Set (FreeGroup (Work.OROneRel.winBeta Wt (Work.OROneRel.tlW p q) 0
              ((p : ℤ) * (q : ℤ))))))
    (hgen : Work.OROneRel.winVertex Wt (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ))
        (Work.OROneRel.tlU p q) l ⊔
      Subgroup.closure (singleton (PresentedGroup.mk ({Work.OROneRel.tlU p q ^ l} : Set (FreeGroup (Fin 2)))
        (Work.OROneRel.tlLowTau p q hp hq hcop))) = ⊤)
    (hcrux : Function.Injective (Work.OROneRel.hnnConjMap
      (Work.OROneRel.tlH p q Wt) (Work.OROneRel.tlLowTau p q hp hq hcop))) :
    Function.Injective (Work.OROneRel.hnnConjMap
      (Work.OROneRel.winVertex Wt (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ))
        (Work.OROneRel.tlU p q) l)
      (PresentedGroup.mk ({Work.OROneRel.tlU p q ^ l} : Set (FreeGroup (Fin 2)))
        (Work.OROneRel.tlLowTau p q hp hq hcop))) := by
  classical
  -- ### Step 1: the F₂-level generation, and the coset tree of the band pair `(tlH, tlLowTau)`
  have hgenF2 : tlH p q Wt ⊔ Subgroup.closure {tlLowTau p q hp hq hcop} = ⊤ :=
    twoLetter_F2_generation p q hp hq hcop Wt hW0 hcoh hwin htree
  have hT : Work.ORBassSerre.IsTree
      (GradedHNN.Coset (tlH p q Wt) (tlLowTau p q hp hq hcop)) :=
    isTree_coset_of_hnnConjMap_injective (tlH p q Wt) (tlLowTau p q hp hq hcop) hgenF2 hcrux
  -- ### Step 2: the F₂-tree data (an `F₂`-tree with vertex stabiliser `tlH` and the closing edge)
  obtain ⟨V, hQ, hrev, hM, hGA, v, z, e, hTree, hninv, hstab, hclose⟩ :=
    winRhoRange_tree_of_cosetTree p q hp hq hcop Wt hW0 hcoh hwin htree hT
  letI : Quiver V := hQ
  letI : Quiver.HasInvolutiveReverse V := hrev
  letI : MulAction (FreeGroup (Fin 2)) V := hM
  letI : Work.ORBassSerre.GraphAction (FreeGroup (Fin 2)) V := hGA
  -- ### Step 3: descend to the quotient by the normal closure `N = ⟪⟪tlU p q ^ l⟫⟫`
  obtain ⟨hTq, hninvq, hstabq, hcloseq⟩ :=
    twoLetter_treeData_of_F2treeData p q l hp hq hcop Wt hW0 hwin hTree hninv v e hstab hclose
  -- ### Step 4: the edge of the quotient tree and the Bass--Serre injectivity criterion
  have hedge : (Quotient.mk'' v : Work.ORBassSerre.orbitV
        ↥(Subgroup.normalClosure ({tlU p q ^ l} : Set (FreeGroup (Fin 2)))) V) ⟶ Quotient.mk'' z :=
    Work.ORBassSerre.orbitArrow
      (G := ↥(Subgroup.normalClosure ({tlU p q ^ l} : Set (FreeGroup (Fin 2))))) e
  refine @hnnConjMap_injective_of_treeData p q l hp hq hl hcop Wt hW0 hcoh hwin
    (Work.ORBassSerre.orbitV ↥(Subgroup.normalClosure ({tlU p q ^ l} : Set (FreeGroup (Fin 2)))) V)
    _ _
    (Work.ORBassSerre.instMulActionQuotientOrbit (X := V)
      (Subgroup.normalClosure ({tlU p q ^ l} : Set (FreeGroup (Fin 2)))))
    (Work.ORDunwoody.instGraphActionQuotientOrbit (G := FreeGroup (Fin 2)) (V := V)
      (Subgroup.normalClosure ({tlU p q ^ l} : Set (FreeGroup (Fin 2)))))
    hTq hninvq (Quotient.mk'' v) (Quotient.mk'' z) hedge hstabq hcloseq

end Work.OROneRel
