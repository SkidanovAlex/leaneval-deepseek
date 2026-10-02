import Mathlib
import Submission.Work.Whitney.tcmPunctCore_signed
import Submission.Work.Whitney.RankOneLHS
import Submission.Work.Whitney.pdAB_generated_succ
import Submission.Work.Whitney.pdABKernKron
import Submission.Work.Whitney.rankOneFiller
import Submission.Work.Whitney.pairClass
import Submission.Work.Whitney.cupFiller
import Submission.Work.Whitney.modelFiller
import Submission.Work.Whitney.tcmProd_rankOne_zero

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The rank-one case of the model product formula, in spherical form

See the docstring of the target below.  The proof assembles the cochain-level computation of the
Whitney chapter:

* `Work.Whitney.RankOneFiller.fillerData` supplies the chains `B, L, Z` (cap, lower chain and
  filler) with all their smallness and non-vanishing properties;
* `Work.Whitney.cupFiller` evaluates any representative of the relative–relative cup
  `tcmRelCup (pr1^* Mpun n) (pr2^* Mpun 1)` on `Z`, giving `(-1)^n` times the pairing of `B` with a
  representative of `stepDisc (Mn n)`;
* `Work.Whitney.modelFiller` evaluates the pullback `tcmF^* (Mpun (n+1))` on `Z`, giving the same
  number;
* `Work.Whitney.pairClass` converts the class identity `tcmRelCup … = k • tcmF^* (Mpun (n+1))`
  (which is `Work.Whitney.pdAB_generated_succ`) into the corresponding identity of pairings with
  `Z`.

Comparing the two evaluations of the same integer against the non-vanishing of `⟨b, B⟩` determines
the coefficient as `(-1)^n`; the transport along the coordinate identification
(`Work.Whitney.tcmF_tcmF_inv_transport`) and `Work.Whitney.jMap_tcmProd`, `Work.Thom.Mpun_spec`
give the spherical form.
-/

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open Work.Thom Work.Cohomology
open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Whitney

noncomputable section

/-- **The rank-one case of the model product formula, in spherical form**: over a subsingleton base
`Y`, the spherical side `Work.Whitney.tcmRankOneLHS Y n` (the `jMap`-image of the external product
`tcmProd Y n 1 (Mpun n Y) (Mpun 1 Y)`, see `Work.Whitney.tcmRankOneLHS_eq_prod`) equals
`(-1)^n • Mn (n+1) Y` in `H^{n+1}(Y × ℝ^{n+1}, Sph Y (n+1))`.

This is the single remaining input of the Whitney chapter's crux
(`Work.Whitney.tcmProd_rankOne_signed`, the `q = 1` case of the Koszul-signed model product formula,
equivalently `Work.Whitney.tcmProd_suspRule`): by `Work.Whitney.tcmProd_eq_of_tcmRankOneLHS` the
punctured form follows from this spherical form.  The Koszul sign `(-1)^n` is genuine -- the
*unsigned* statement is false (the `(n,1) = (1,1)` case gives `-Mpun 2 Y`, see the sign analysis in
`Submission/Work/Whitney/_o/NOTES_sign_11.md`, `NOTES_rankOne_signed.md`,
`NOTES_tcmRankOneSusp.md`).

The workspace already contains the cochain-level apparatus for this computation.  Note in particular
`Work.Whitney.rankOne_cup_model` (whose only missing ingredient is this very statement: it is
currently a placeholder there), `Work.Whitney.Signed.tcmRelCup_kronecker_filler`,
`Work.Whitney.cupSide_final`, `Work.Whitney.capCycle`, and the `Signed/` directory. -/
theorem tcmRankOneLHS_eq_Mn (Y : Type) [TopologicalSpace Y] [Subsingleton Y] (n : ℕ) :
    Work.Whitney.tcmRankOneLHS Y n = ((-1 : ℤ) ^ n) • (Work.Thom.Mn (n + 1) Y) := by
  by_cases hY : Nonempty Y
  · haveI : Nonempty Y := hY
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · -- the `n = 0` case is the left unit law
      subst h0
      rw [← jMap_tcmProd Y 0, tcmProd_rankOne_zero Y, Mpun_spec]
      simp
    · -- the general case
      obtain ⟨B, L, Z, hB, hL, hLband, hZ, hfin, b, hb, hbc, hbne⟩ :=
        RankOneFiller.fillerData Y n hpos
      -- the cyclicity of the `A∪C`-group
      obtain ⟨k, hk⟩ := pdAB_generated_succ Y n
        (tcmRelCup (tcmA Y n 1) (tcmC Y n 1) (isOpen_tcmA Y n 1) (isOpen_tcmC Y n 1) n 1
          ((relCohMap (tcmPr1 Y n 1) (tcmA Y n 1) (Punct Y n) (fun x hx => hx) ℤ n).hom
            (Mpun n Y))
          ((relCohMap (tcmPr2 Y n 1) (tcmC Y n 1) (Punct Y 1) (fun x hx => hx) ℤ 1).hom
            (Mpun 1 Y)))
      -- representatives of the two classes
      obtain ⟨γ, hγ, hγr⟩ := exists_relClassOf ℤ (TopCat.of (tcmX Y n 1))
        (tcmA Y n 1 ∪ tcmC Y n 1) (n + 1)
        (tcmRelCup (tcmA Y n 1) (tcmC Y n 1) (isOpen_tcmA Y n 1) (isOpen_tcmC Y n 1) n 1
          ((relCohMap (tcmPr1 Y n 1) (tcmA Y n 1) (Punct Y n) (fun x hx => hx) ℤ n).hom
            (Mpun n Y))
          ((relCohMap (tcmPr2 Y n 1) (tcmC Y n 1) (Punct Y 1) (fun x hx => hx) ℤ 1).hom
            (Mpun 1 Y)))
      obtain ⟨s, hs, hsr⟩ := exists_relClassOf ℤ
        (TopCat.of (Y × EuclideanSpace ℝ (Fin (n + 1)))) (Punct Y (n + 1)) (n + 1)
        (Mpun (n + 1) Y)
      -- the `A+C`-cycle condition
      have hac : ∀ ξ : ↥(pdABKernR (R := ℤ) (TopCat.of (tcmX Y n 1)) (tcmA Y n 1)
          (tcmC Y n 1) n),
          kronecker ℤ (ssB (tcmX Y n 1)) ξ.1
            ((singularChains ℤ (TopCat.of (tcmX Y n 1))).d (n + 1) n Z) = 0 :=
        fun ξ => kronecker_eq_zero_of_pdABKern_of_isSmallChain (TopCat.of (tcmX Y n 1))
          (tcmA Y n 1) (tcmC Y n 1) ξ _ hfin
      -- the two evaluations and the pairing identity
      have hcup := cupFiller Y n hpos B hB L hL Z hZ hfin γ hγ hγr b hb hbc
      have hmod := modelFiller Y n B hB L hLband Z hZ s hs hsr b hb hbc
      have hpair := pairClass Y n k hk γ hγ hγr s hs hsr Z hac
      -- the coefficient is `(-1)^n`
      have hkey : ((-1 : ℤ) ^ n) * kronecker ℤ (ssB (Y × MBall n)) b.1 B
          = k * kronecker ℤ (ssB (Y × MBall n)) b.1 B := by
        rw [← hcup, hpair, hmod, zsmul_eq_mul]
        simp only [Int.cast_id]
      have hkval : k = (-1 : ℤ) ^ n :=
        (mul_right_cancel₀ hbne hkey).symm
      -- the class identity in the `A∪C`-group
      have hc : tcmRelCup (tcmA Y n 1) (tcmC Y n 1) (isOpen_tcmA Y n 1) (isOpen_tcmC Y n 1) n 1
          ((relCohMap (tcmPr1 Y n 1) (tcmA Y n 1) (Punct Y n) (fun x hx => hx) ℤ n).hom
            (Mpun n Y))
          ((relCohMap (tcmPr2 Y n 1) (tcmC Y n 1) (Punct Y 1) (fun x hx => hx) ℤ 1).hom
            (Mpun 1 Y))
          = ((-1 : ℤ) ^ n) •
            ((relCohMap (tcmF Y n 1) (tcmA Y n 1 ∪ tcmC Y n 1) (Punct Y (n + 1))
              (tcmF_mem Y n 1) ℤ (n + 1)).hom (Mpun (n + 1) Y)) := by
        rw [hk, hkval]
      -- the punctured form
      have htcmProd : tcmProd Y n 1 (Mpun n Y) (Mpun 1 Y)
          = ((-1 : ℤ) ^ n) • Mpun (n + 1) Y := by
        show (relCohMap (Fib.tcmF_inv Y n 1) (Punct Y (n + 1)) (tcmA Y n 1 ∪ tcmC Y n 1)
            (tcmF_inv_mem_punct_union Y n 1) ℤ (n + 1)).hom
            (tcmRelCup (tcmA Y n 1) (tcmC Y n 1) (isOpen_tcmA Y n 1) (isOpen_tcmC Y n 1) n 1
              ((relCohMap (tcmPr1 Y n 1) (tcmA Y n 1) (Punct Y n) (fun x hx => hx) ℤ n).hom
                (Mpun n Y))
              ((relCohMap (tcmPr2 Y n 1) (tcmC Y n 1) (Punct Y 1) (fun x hx => hx) ℤ 1).hom
                (Mpun 1 Y)))
          = ((-1 : ℤ) ^ n) • Mpun (n + 1) Y
        rw [hc, map_zsmul]
        congr 1
        rw [show (relCohMap (Fib.tcmF_inv Y n 1) (Punct Y (n + 1))
              (tcmA Y n 1 ∪ tcmC Y n 1) (tcmF_inv_mem_punct_union Y n 1) ℤ (n + 1))
            = relCohMap (Fib.tcmF_inv Y n 1) (Punct Y (n + 1)) (tcmA Y n 1 ∪ tcmC Y n 1)
                (tcmF_inv_mem_punct Y n) ℤ (n + 1) from
          relCohMap_hcongrA (Fib.tcmF_inv Y n 1) (Punct Y (n + 1))
            (tcmA Y n 1 ∪ tcmC Y n 1) (tcmF_inv_mem_punct_union Y n 1)
            (tcmF_inv_mem_punct Y n) ℤ (n + 1)]
        exact tcmF_tcmF_inv_transport Y n (Mpun (n + 1) Y)
      -- the spherical form
      rw [← jMap_tcmProd Y n, htcmProd, map_zsmul, Mpun_spec]
  · haveI : IsEmpty Y := not_nonempty_iff.mp hY
    haveI : IsEmpty (Y × EuclideanSpace ℝ (Fin (n + 1))) := ⟨fun x => isEmptyElim x.1⟩
    haveI : Subsingleton
        (RelCoh ℤ (n + 1) (Y × EuclideanSpace ℝ (Fin (n + 1))) (Sph Y (n + 1))) :=
      subsingleton_relCoh_of_isEmpty (Sph Y (n + 1)) (n + 1)
    exact Subsingleton.elim _ _

end

end Work.Whitney
