import Mathlib
import Submission.Work.Whitney.CupDefs
import Submission.Work.Whitney.capTransferPrep
import Submission.Work.Whitney.cupSide_final
import Submission.Work.Whitney.Signed.CapFull
import Submission.Work.Whitney.relCycleKron
import Submission.Work.Whitney.RankTwo.RepDefs
import Submission.Work.Whitney.tcmSuspAux.kronecker_tcmRelCup_apply
import Submission.Work.Whitney.cupFillerAux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# The cup-side evaluation of the rank-one model product formula

Given a **filler** `Z` of the pair `(tcmX Y k 1, tcmA ∪ tcmC)` whose boundary is `U + L`
(`U = capX_*B` the cap image of a ball chain `B`, `L` carried by the cover `(tcmA, LowerOpenTcm)`),
the pairing of any representative of the relative-relative cup
`tcmRelCup(A,C)(pr1^*Mpun k Y, pr2^*Mpun 1 Y)` with `Z` is `(-1)^k` times the pairing of `B` with
any representative of the disc model class `stepDisc Y k (Mn k Y)`.

The `(-1)^k` is the Leibniz sign of `alpha ⌣ dgamma = (-1)^k d(alpha ⌣ gamma)`; the cap transfer
`cap^*(alpha⌣gamma) = cap^*alpha` (`cap_pullback_cup_gammaSharp`) and the GAP lemma
(`kronecker_relComplex_eq_of_homology_eq`) supply the rest.  No orientation comparison occurs.
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Simplicial

namespace Work.Whitney

open Work.Thom
open Work.Cohomology

noncomputable section




theorem cupFiller (Y : Type) [TopologicalSpace Y] (k : ℕ) (hk : 1 ≤ k)
    (B : (Work.Cohomology.singularChains ℤ (TopCat.of (Y × Work.Thom.MBall k))).X k)
    (hB : Work.Cohomology.IsSmallChain (Work.Thom.DiscB Y k) (∅ : Set (Y × Work.Thom.MBall k))
      ((Work.Cohomology.singularChains ℤ (TopCat.of (Y × Work.Thom.MBall k))).d k (k - 1) B))
    (L : (Work.Cohomology.singularChains ℤ (TopCat.of (Work.Whitney.tcmX Y k 1))).X k)
    (hL : Work.Cohomology.IsSmallChain (Work.Whitney.tcmA Y k 1) (Work.Whitney.LowerOpenTcm Y k) L)
    (Z : (Work.Cohomology.singularChains ℤ (TopCat.of (Work.Whitney.tcmX Y k 1))).X (k + 1))
    (hZ : (Work.Cohomology.singularChains ℤ (TopCat.of (Work.Whitney.tcmX Y k 1))).d (k + 1) k Z
      = Work.Cohomology.pushChain (TopCat.of (Y × Work.Thom.MBall k))
          (TopCat.of (Work.Whitney.tcmX Y k 1)) (TopCat.ofHom (Work.Whitney.capX Y k)) k B + L)
    (hfin : Work.Cohomology.IsSmallChain (Work.Whitney.tcmA Y k 1) (Work.Whitney.tcmC Y k 1)
      ((Work.Cohomology.singularChains ℤ (TopCat.of (Work.Whitney.tcmX Y k 1))).d (k + 1) k Z))
    (w : ↥(Work.Cohomology.relKern ℤ (TopCat.of (Work.Whitney.tcmX Y k 1))
      (Work.Whitney.tcmA Y k 1 ∪ Work.Whitney.tcmC Y k 1) (k + 1)))
    (hw : Work.Cohomology.relDiffLM ℤ (TopCat.of (Work.Whitney.tcmX Y k 1))
      (Work.Whitney.tcmA Y k 1 ∪ Work.Whitney.tcmC Y k 1) (k + 1) w = 0)
    (hwc : Work.Cohomology.relClassOf ℤ (TopCat.of (Work.Whitney.tcmX Y k 1))
      (Work.Whitney.tcmA Y k 1 ∪ Work.Whitney.tcmC Y k 1) w hw
      = Work.Whitney.tcmRelCup (Work.Whitney.tcmA Y k 1) (Work.Whitney.tcmC Y k 1)
          (Work.Whitney.isOpen_tcmA Y k 1) (Work.Whitney.isOpen_tcmC Y k 1) k 1
          ((Work.Thom.relCohMap (Work.Whitney.tcmPr1 Y k 1) (Work.Whitney.tcmA Y k 1)
            (Work.Thom.Punct Y k) (fun x hx => hx) ℤ k).hom (Work.Thom.Mpun k Y))
          ((Work.Thom.relCohMap (Work.Whitney.tcmPr2 Y k 1) (Work.Whitney.tcmC Y k 1)
            (Work.Thom.Punct Y 1) (fun x hx => hx) ℤ 1).hom (Work.Thom.Mpun 1 Y)))
    (b : ↥(Work.Cohomology.relKern ℤ (TopCat.of (Y × Work.Thom.MBall k)) (Work.Thom.DiscB Y k) k))
    (hb : Work.Cohomology.relDiffLM ℤ (TopCat.of (Y × Work.Thom.MBall k))
      (Work.Thom.DiscB Y k) k b = 0)
    (hbc : Work.Cohomology.relClassOf ℤ (TopCat.of (Y × Work.Thom.MBall k))
      (Work.Thom.DiscB Y k) b hb = Work.Thom.stepDisc Y k (Work.Thom.Mn k Y)) :
    Work.Cohomology.kronecker ℤ (Work.Whitney.ssB (Work.Whitney.tcmX Y k 1)) w.1 Z
      = ((-1 : ℤ) ^ k) * Work.Cohomology.kronecker ℤ (Work.Whitney.ssB (Y × Work.Thom.MBall k)) b.1 B := by
  rcases k with _ | n
  · exact absurd hk (by simp)
  have hB' : IsSmallChain (DiscB Y (Nat.succ n)) ∅
      ((singularChains ℤ (TopCat.of (Y × MBall (Nat.succ n)))).d (Nat.succ n) n B) := by
    simpa only [Nat.succ_sub_one] using hB
  obtain ⟨s, hs, hsr⟩ := exists_relClassOf ℤ
    (TopCat.of (Y × EuclideanSpace ℝ (Fin (Nat.succ n)))) (Punct Y (Nat.succ n)) (Nat.succ n)
    (Mpun (Nat.succ n) Y)
  have hα : relDiffLM ℤ (TopCat.of (tcmX Y (Nat.succ n) 1)) (tcmA Y (Nat.succ n) 1) (Nat.succ n)
      (relMapLM ℤ (tcmA Y (Nat.succ n) 1) (Punct Y (Nat.succ n))
        (TopCat.ofHom (tcmPr1 Y (Nat.succ n) 1)) (fun x hx => hx) (Nat.succ n) s) = 0 :=
    relDiffLM_relMapLM (R := ℤ) (X₁ := TopCat.of (tcmX Y (Nat.succ n) 1))
      (X₂ := TopCat.of (Y × EuclideanSpace ℝ (Fin (Nat.succ n))))
      (tcmA Y (Nat.succ n) 1) (Punct Y (Nat.succ n))
      (TopCat.ofHom (tcmPr1 Y (Nat.succ n) 1)) (fun x hx => hx) (n := Nat.succ n) s hs
  have hαr : relClassOf ℤ (TopCat.of (tcmX Y (Nat.succ n) 1)) (tcmA Y (Nat.succ n) 1)
        (relMapLM ℤ (tcmA Y (Nat.succ n) 1) (Punct Y (Nat.succ n))
          (TopCat.ofHom (tcmPr1 Y (Nat.succ n) 1)) (fun x hx => hx) (Nat.succ n) s) hα
      = (relCohMap (tcmPr1 Y (Nat.succ n) 1) (tcmA Y (Nat.succ n) 1) (Punct Y (Nat.succ n))
          (fun x hx => hx) ℤ (Nat.succ n)).hom (Mpun (Nat.succ n) Y) := by
    refine (homologyMap_relComplexMap_relClassOf (R := ℤ)
      (X₁ := TopCat.of (tcmX Y (Nat.succ n) 1))
      (X₂ := TopCat.of (Y × EuclideanSpace ℝ (Fin (Nat.succ n))))
      (tcmA Y (Nat.succ n) 1) (Punct Y (Nat.succ n))
      (TopCat.ofHom (tcmPr1 Y (Nat.succ n) 1)) (fun x hx => hx) s hs).symm.trans ?_
    rw [hsr]
  have hmain := kronecker_tcmRelCup_gammaSharp (Y := Y) (Nat.succ n)
    (relMapLM ℤ (tcmA Y (Nat.succ n) 1) (Punct Y (Nat.succ n))
      (TopCat.ofHom (tcmPr1 Y (Nat.succ n) 1)) (fun x hx => hx) (Nat.succ n) s) hα hαr
    w hw hwc Z (signed_hZac Y n Z hfin)
  rw [hmain]
  rw [hZ]
  have hsplit : kronecker ℤ (ssB (tcmX Y (Nat.succ n) 1))
        (cup ℤ (ssB (tcmX Y (Nat.succ n) 1))
          (show Cochain ℤ (ssB (tcmX Y (Nat.succ n) 1)) (Nat.succ n) from
            (relMapLM ℤ (tcmA Y (Nat.succ n) 1) (Punct Y (Nat.succ n))
              (TopCat.ofHom (tcmPr1 Y (Nat.succ n) 1)) (fun x hx => hx) (Nat.succ n) s).1)
          (gammaSharp Y (Nat.succ n)))
        (pushChain (TopCat.of (Y × MBall (Nat.succ n))) (TopCat.of (tcmX Y (Nat.succ n) 1))
          (TopCat.ofHom (capX Y (Nat.succ n))) (Nat.succ n) B + L)
      = kronecker ℤ (ssB (tcmX Y (Nat.succ n) 1))
          (cup ℤ (ssB (tcmX Y (Nat.succ n) 1))
            (show Cochain ℤ (ssB (tcmX Y (Nat.succ n) 1)) (Nat.succ n) from
              (relMapLM ℤ (tcmA Y (Nat.succ n) 1) (Punct Y (Nat.succ n))
                (TopCat.ofHom (tcmPr1 Y (Nat.succ n) 1)) (fun x hx => hx) (Nat.succ n) s).1)
            (gammaSharp Y (Nat.succ n)))
          (pushChain (TopCat.of (Y × MBall (Nat.succ n))) (TopCat.of (tcmX Y (Nat.succ n) 1))
            (TopCat.ofHom (capX Y (Nat.succ n))) (Nat.succ n) B)
        + kronecker ℤ (ssB (tcmX Y (Nat.succ n) 1))
            (cup ℤ (ssB (tcmX Y (Nat.succ n) 1))
              (show Cochain ℤ (ssB (tcmX Y (Nat.succ n) 1)) (Nat.succ n) from
                (relMapLM ℤ (tcmA Y (Nat.succ n) 1) (Punct Y (Nat.succ n))
                  (TopCat.ofHom (tcmPr1 Y (Nat.succ n) 1)) (fun x hx => hx) (Nat.succ n) s).1)
              (gammaSharp Y (Nat.succ n))) L :=
    map_add _ _ _
  rw [hsplit, smul_add]
  rw [signed_L_eval Y n
      (relMapLM ℤ (tcmA Y (Nat.succ n) 1) (Punct Y (Nat.succ n))
        (TopCat.ofHom (tcmPr1 Y (Nat.succ n) 1)) (fun x hx => hx) (Nat.succ n) s) L hL]
  simp only [smul_zero, add_zero]
  rw [signed_capEval Y n B
    (relMapLM ℤ (tcmA Y (Nat.succ n) 1) (Punct Y (Nat.succ n))
      (TopCat.ofHom (tcmPr1 Y (Nat.succ n) 1)) (fun x hx => hx) (Nat.succ n) s)]
  rw [signed_gap Y n B hB' b
    (signedPα Y n (relMapLM ℤ (tcmA Y (Nat.succ n) 1) (Punct Y (Nat.succ n))
      (TopCat.ofHom (tcmPr1 Y (Nat.succ n) 1)) (fun x hx => hx) (Nat.succ n) s))
    hb
    (signedPα_cocycle Y n (relMapLM ℤ (tcmA Y (Nat.succ n) 1) (Punct Y (Nat.succ n))
      (TopCat.ofHom (tcmPr1 Y (Nat.succ n) 1)) (fun x hx => hx) (Nat.succ n) s) hα)
    (signed_capEval_class Y n (relMapLM ℤ (tcmA Y (Nat.succ n) 1) (Punct Y (Nat.succ n))
      (TopCat.ofHom (tcmPr1 Y (Nat.succ n) 1)) (fun x hx => hx) (Nat.succ n) s) hα hαr
      (signedPα_cocycle Y n (relMapLM ℤ (tcmA Y (Nat.succ n) 1) (Punct Y (Nat.succ n))
        (TopCat.ofHom (tcmPr1 Y (Nat.succ n) 1)) (fun x hx => hx) (Nat.succ n) s) hα) b hb hbc)]
  rw [zsmul_eq_mul]
  simp only [Int.cast_id, Nat.succ_eq_add_one]


end

end Work.Whitney
