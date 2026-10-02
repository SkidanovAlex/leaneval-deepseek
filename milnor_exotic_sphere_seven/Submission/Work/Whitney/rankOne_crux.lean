import Mathlib
import Submission.Work.Whitney.CupDefs
import Submission.Work.Whitney.TCMDefs
import Submission.Work.Whitney.cupFiller
import Submission.Work.Whitney.modelFiller
import Submission.Work.Whitney.pairClass
import Submission.Work.Whitney.rankOneFiller
import Submission.Work.Whitney.pdAB_generated_succ
import Submission.Work.Whitney.pdABKernKron
import Submission.Work.Whitney.RelABComplex

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace Work.Whitney

open Work.Thom Work.Cohomology
open CategoryTheory AlgebraicTopology CategoryTheory.Limits

noncomputable section

/-- **The crux of the rank-one model product formula, in the `tcmF`-form**: the relative–relative
cup of the two pulled-back model classes is `(-1)^n` times the `tcmF`-pullback of `Mpun (n+1) Y`. -/
theorem rankOne_crux (Y : Type) [TopologicalSpace Y] [Subsingleton Y] [Nonempty Y] (n : ℕ)
    (hn : 1 ≤ n) :
    tcmRelCup (tcmA Y n 1) (tcmC Y n 1) (isOpen_tcmA Y n 1) (isOpen_tcmC Y n 1) n 1
      ((relCohMap (tcmPr1 Y n 1) (tcmA Y n 1) (Punct Y n) (fun x hx => hx) ℤ n).hom (Mpun n Y))
      ((relCohMap (tcmPr2 Y n 1) (tcmC Y n 1) (Punct Y 1) (fun x hx => hx) ℤ 1).hom (Mpun 1 Y))
    = ((-1 : ℤ) ^ n) •
      (relCohMap (tcmF Y n 1) (tcmA Y n 1 ∪ tcmC Y n 1) (Punct Y (n + 1))
        (tcmF_mem Y n 1) ℤ (n + 1)).hom (Mpun (n + 1) Y) := by
  obtain ⟨B, L, Z, hB, hLcov, hLband, hZ, hZsm, b, hb, hbl, hnonvan⟩ :=
    RankOneFiller.fillerData Y n hn
  obtain ⟨γ, hγ, hγr⟩ := exists_relClassOf ℤ (TopCat.of (tcmX Y n 1))
    (tcmA Y n 1 ∪ tcmC Y n 1) (n + 1)
    (tcmRelCup (tcmA Y n 1) (tcmC Y n 1) (isOpen_tcmA Y n 1) (isOpen_tcmC Y n 1) n 1
      ((relCohMap (tcmPr1 Y n 1) (tcmA Y n 1) (Punct Y n) (fun x hx => hx) ℤ n).hom (Mpun n Y))
      ((relCohMap (tcmPr2 Y n 1) (tcmC Y n 1) (Punct Y 1) (fun x hx => hx) ℤ 1).hom (Mpun 1 Y)))
  obtain ⟨s, hs, hsr⟩ := exists_relClassOf ℤ
    (TopCat.of (Y × EuclideanSpace ℝ (Fin (n + 1)))) (Punct Y (n + 1)) (n + 1) (Mpun (n + 1) Y)
  obtain ⟨k, hk⟩ := pdAB_generated_succ Y n
    (tcmRelCup (tcmA Y n 1) (tcmC Y n 1) (isOpen_tcmA Y n 1) (isOpen_tcmC Y n 1) n 1
      ((relCohMap (tcmPr1 Y n 1) (tcmA Y n 1) (Punct Y n) (fun x hx => hx) ℤ n).hom (Mpun n Y))
      ((relCohMap (tcmPr2 Y n 1) (tcmC Y n 1) (Punct Y 1) (fun x hx => hx) ℤ 1).hom (Mpun 1 Y)))
  have hac : ∀ ξ : (pdABCohR (R := ℤ) (TopCat.of (tcmX Y n 1)) (tcmA Y n 1) (tcmC Y n 1)).X n,
      kronecker ℤ (ssB (tcmX Y n 1)) ξ.1
        (((singularChains ℤ (TopCat.of (tcmX Y n 1))).d (n + 1) n) Z) = 0 :=
    fun ξ => kronecker_eq_zero_of_pdABKern_of_isSmallChain (TopCat.of (tcmX Y n 1))
      (tcmA Y n 1) (tcmC Y n 1) ξ
      (((singularChains ℤ (TopCat.of (tcmX Y n 1))).d (n + 1) n) Z) hZsm
  have hp := pairClass Y n k hk γ hγ hγr s hs hsr Z hac
  have hcu := cupFiller Y n hn B hB L hLcov Z hZ hZsm γ hγ hγr b hb hbl
  have hmo := modelFiller Y n B hB L hLband Z hZ s hs hsr b hb hbl
  have hkey : k = (-1 : ℤ) ^ n := by
    have hsm : k • kronecker ℤ (ssB (tcmX Y n 1))
        (show Cochain ℤ (ssB (tcmX Y n 1)) (n + 1) from
          (ModuleCat.Hom.hom ((dualChainMap ℤ (TopCat.of (tcmX Y n 1))
            (TopCat.of (Y × EuclideanSpace ℝ (Fin (n + 1))))
            (TopCat.ofHom (tcmF Y n 1))).f (n + 1))) s.1) Z
        = k • kronecker ℤ (ssB (Y × MBall n)) b.1 B := by
      rw [hmo]
    have hcu' : kronecker ℤ (ssB (tcmX Y n 1)) γ.1 Z
        = ((-1 : ℤ) ^ n) • kronecker ℤ (ssB (Y × MBall n)) b.1 B := by
      rw [hcu, smul_eq_mul]
    have heq : ((-1 : ℤ) ^ n) • kronecker ℤ (ssB (Y × MBall n)) b.1 B
        = k • kronecker ℤ (ssB (Y × MBall n)) b.1 B := by
      rw [← hcu', hp, hsm]
    have h2 : (k - (-1 : ℤ) ^ n) • kronecker ℤ (ssB (Y × MBall n)) b.1 B = 0 := by
      rw [sub_smul, heq, sub_self]
    have h3 : (k - (-1 : ℤ) ^ n) * kronecker ℤ (ssB (Y × MBall n)) b.1 B = 0 := by
      rw [← smul_eq_mul]; exact h2
    rcases mul_eq_zero.mp h3 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hnonvan
  rw [hk, hkey]

end

end Work.Whitney
