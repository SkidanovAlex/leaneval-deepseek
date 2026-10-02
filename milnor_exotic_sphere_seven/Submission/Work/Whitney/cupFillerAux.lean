import Mathlib
import Submission.Work.Whitney.CupDefs
import Submission.Work.Whitney.capTransferPrep
import Submission.Work.Whitney.cupSide_final
import Submission.Work.Whitney.Signed.CapFull
import Submission.Work.Whitney.Signed.KronAdj
import Submission.Work.Whitney.relCycleKron
import Submission.Work.Whitney.RankTwo.RepDefs
import Submission.Work.Whitney.tcmSuspAux.kronecker_tcmRelCup_apply

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Simplicial

namespace Work.Whitney

open Work.Thom
open Work.Cohomology

noncomputable section

/-! ## The two-set small-chain vanishing -/

theorem signed_kronecker_eq_zero_of_genEval_small {X : TopCat} (U V : Set X) {n : ℕ}
    (u : Cochain ℤ (TopCat.toSSet.obj X) n)
    (h : ∀ σ : (TopCat.toSSet.obj X) _⦋n⦌, IsSmall U V σ →
      genEval ℤ (TopCat.toSSet.obj X) u σ = 0)
    {c : (singularChains ℤ X).X n} (hc : IsSmallChain U V c) :
    kronecker ℤ (TopCat.toSSet.obj X) u c = 0 := by
  classical
  obtain ⟨c', hc'⟩ := hc
  let Q : Submodule ℤ ↥((smallChains U V).X n) :=
    Submodule.comap ((smallToSing U V).f n).hom
      (LinearMap.ker (show Cochain ℤ (TopCat.toSSet.obj X) n from u))
  have hQ : Q = ⊤ := by
    refine mem_of_genSSet (smallSSet U V) n Q ?_
    intro τ
    show ((smallToSing U V).f n).hom (genSSet (smallSSet U V) n τ)
      ∈ LinearMap.ker (show Cochain ℤ (TopCat.toSSet.obj X) n from u)
    rw [smallToSing_gen τ, LinearMap.mem_ker]
    exact h τ.1 τ.2
  have hmem : c' ∈ Q := by rw [hQ]; exact Submodule.mem_top
  have hval : u (((smallToSing U V).f n).hom c') = 0 := hmem
  rw [← hc']
  exact hval

/-! ## The back vertex of a simplex -/

theorem signed_point_backFace {X : TopCat} (n : ℕ) (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    (TopCat.toSSetObjEquivOld X (Opposite.op ⦋0⦌))
        ((Work.Cohomology.backFace (TopCat.toSSet.obj X) n 0) σ) default
      = sdMap n σ (stdSimplex.map (Work.Cohomology.backIncl n 0) default) := by
  have h := TopCat.toSSetObjEquivOld_naturality_apply (X := X) (n := ⦋0⦌) (m := ⦋n + 0⦌)
    (Work.Cohomology.backIncl n 0) σ default
  exact h

theorem signed_gammaSharp_backFace_eq_zero {Y : Type} [TopologicalSpace Y] (n : ℕ)
    (σ : (TopCat.toSSet.obj (TopCat.of (tcmX Y n 1))) _⦋n⦌)
    (hσ : ∀ z : (Delta n : TopCat), sdMap n σ z ∈ LowerOpenTcm Y n) :
    genEval ℤ (ssB (tcmX Y n 1)) (gammaSharp Y n)
        ((Work.Cohomology.backFace (ssB (tcmX Y n 1)) n 0) σ) = 0 := by
  rw [Work.Whitney.genEval_gammaSharp]
  rw [signed_point_backFace]
  have hlt : lastCoord Y n (sdMap n σ (stdSimplex.map (Work.Cohomology.backIncl n 0) default)) < 0 :=
    hσ _
  rw [if_neg (not_le.mpr hlt)]

theorem signed_cup_gammaSharp_genEval_zero {Y : Type} [TopologicalSpace Y] (n : ℕ)
    (α : ↥(relKern ℤ (TopCat.of (tcmX Y n 1)) (tcmA Y n 1) n))
    (σ : (TopCat.toSSet.obj (TopCat.of (tcmX Y n 1))) _⦋n⦌)
    (hσ : IsSmall (tcmA Y n 1) (LowerOpenTcm Y n) σ) :
    genEval ℤ (ssB (tcmX Y n 1))
        (cup ℤ (ssB (tcmX Y n 1))
          (show Cochain ℤ (ssB (tcmX Y n 1)) n from α.1) (gammaSharp Y n)) σ = 0 := by
  rw [cup_apply]
  rw [Work.Cohomology.frontFace_self]
  rcases hσ with hA | hC
  · rw [genEval_eq_zero_of_mem_relKern_of_isSmall (TopCat.of (tcmX Y n 1)) α (Or.inl hA),
      zero_mul]
  · rw [signed_gammaSharp_backFace_eq_zero n σ (fun z => hC ⟨(stdSimplexHomeomorph _).symm z, rfl⟩), mul_zero]

/-! ## The four pieces of the filler computation -/

abbrev signedPα (Y : Type) [TopologicalSpace Y] (n : ℕ)
    (α : ↥(relKern ℤ (TopCat.of (tcmX Y (Nat.succ n) 1)) (tcmA Y (Nat.succ n) 1) (Nat.succ n))) :
    ↥(relKern ℤ (TopCat.of (Y × MBall (Nat.succ n))) (DiscB Y (Nat.succ n)) (Nat.succ n)) :=
  relMapLM ℤ (DiscB Y (Nat.succ n)) (tcmA Y (Nat.succ n) 1) (TopCat.ofHom (capX Y (Nat.succ n)))
    (capX_mem_tcmA Y (Nat.succ n)) (Nat.succ n) α

theorem signedPα_coe (Y : Type) [TopologicalSpace Y] (n : ℕ)
    (α : ↥(relKern ℤ (TopCat.of (tcmX Y (Nat.succ n) 1)) (tcmA Y (Nat.succ n) 1) (Nat.succ n))) :
    (signedPα Y n α).1
      = ((dualChainMap ℤ (TopCat.of (Y × MBall (Nat.succ n))) (TopCat.of (tcmX Y (Nat.succ n) 1))
          (TopCat.ofHom (capX Y (Nat.succ n)))).f (Nat.succ n)).hom α.1 := rfl

theorem signedPα_cocycle (Y : Type) [TopologicalSpace Y] (n : ℕ)
    (α : ↥(relKern ℤ (TopCat.of (tcmX Y (Nat.succ n) 1)) (tcmA Y (Nat.succ n) 1) (Nat.succ n)))
    (hα : relDiffLM ℤ (TopCat.of (tcmX Y (Nat.succ n) 1)) (tcmA Y (Nat.succ n) 1) (Nat.succ n) α = 0) :
    relDiffLM ℤ (TopCat.of (Y × MBall (Nat.succ n))) (DiscB Y (Nat.succ n)) (Nat.succ n)
      (signedPα Y n α) = 0 :=
  relDiffLM_relMapLM (R := ℤ) (X₁ := TopCat.of (Y × MBall (Nat.succ n)))
    (X₂ := TopCat.of (tcmX Y (Nat.succ n) 1))
    (DiscB Y (Nat.succ n)) (tcmA Y (Nat.succ n) 1)
    (TopCat.ofHom (capX Y (Nat.succ n))) (capX_mem_tcmA Y (Nat.succ n)) (n := Nat.succ n) α hα

theorem signed_hZac (Y : Type) [TopologicalSpace Y] (n : ℕ)
    (Z : (singularChains ℤ (TopCat.of (tcmX Y (Nat.succ n) 1))).X (Nat.succ n + 1))
    (hfin : IsSmallChain (tcmA Y (Nat.succ n) 1) (tcmC Y (Nat.succ n) 1)
      ((singularChains ℤ (TopCat.of (tcmX Y (Nat.succ n) 1))).d (Nat.succ n + 1) (Nat.succ n) Z)) :
    ∀ ξ : (pdABCohR (R := ℤ) (TopCat.of (tcmX Y (Nat.succ n) 1))
        (tcmA Y (Nat.succ n) 1) (tcmC Y (Nat.succ n) 1)).X (Nat.succ n),
      kronecker ℤ (ssB (tcmX Y (Nat.succ n) 1)) ξ.1
        ((singularChains ℤ (TopCat.of (tcmX Y (Nat.succ n) 1))).d (Nat.succ n + 1) (Nat.succ n) Z) = 0 := by
  intro ξ
  refine signed_kronecker_eq_zero_of_genEval_small
    (X := TopCat.of (tcmX Y (Nat.succ n) 1)) (n := Nat.succ n)
    (tcmA Y (Nat.succ n) 1) (tcmC Y (Nat.succ n) 1)
    (show Cochain ℤ (ssB (tcmX Y (Nat.succ n) 1)) (Nat.succ n) from ξ.1) ?_ hfin
  intro σ hσ
  rcases hσ with hA | hC
  · exact genEval_eq_zero_of_mem_relKern_of_isSmall (TopCat.of (tcmX Y (Nat.succ n) 1))
      (A := tcmA Y (Nat.succ n) 1) ⟨ξ.1, (Submodule.mem_inf.mp ξ.2).1⟩ (Or.inl hA)
  · exact genEval_eq_zero_of_mem_relKern_of_isSmall (TopCat.of (tcmX Y (Nat.succ n) 1))
      (A := tcmC Y (Nat.succ n) 1) ⟨ξ.1, (Submodule.mem_inf.mp ξ.2).2⟩ (Or.inl hC)

theorem signed_L_eval (Y : Type) [TopologicalSpace Y] (n : ℕ)
    (α : ↥(relKern ℤ (TopCat.of (tcmX Y (Nat.succ n) 1)) (tcmA Y (Nat.succ n) 1) (Nat.succ n)))
    (L : (singularChains ℤ (TopCat.of (tcmX Y (Nat.succ n) 1))).X (Nat.succ n))
    (hL : IsSmallChain (tcmA Y (Nat.succ n) 1) (LowerOpenTcm Y (Nat.succ n)) L) :
    kronecker ℤ (ssB (tcmX Y (Nat.succ n) 1))
      (cup ℤ (ssB (tcmX Y (Nat.succ n) 1)) α.1 (gammaSharp Y (Nat.succ n))) L = 0 :=
  signed_kronecker_eq_zero_of_genEval_small
    (X := TopCat.of (tcmX Y (Nat.succ n) 1)) (n := Nat.succ n)
    (tcmA Y (Nat.succ n) 1) (LowerOpenTcm Y (Nat.succ n))
    (cup ℤ (ssB (tcmX Y (Nat.succ n) 1)) α.1 (gammaSharp Y (Nat.succ n)))
    (fun σ hσ => signed_cup_gammaSharp_genEval_zero (Nat.succ n) α σ hσ) hL

abbrev pullCochain {X Z : TopCat} (f : X ⟶ Z) (n : ℕ) (γ : Cochain ℤ (ssB Z) n) :
    Cochain ℤ (ssB X) n :=
  ((dualChainMap ℤ X Z f).f n).hom γ

theorem kronecker_pushChain {X Z : TopCat} (f : X ⟶ Z) (n : ℕ)
    (γ : Cochain ℤ (ssB Z) n) (c : (singularChains ℤ X).X n) :
    kronecker ℤ (ssB Z) γ (pushChain X Z f n c)
      = kronecker ℤ (ssB X) (pullCochain f n γ) c :=
  cochain_push_apply f n γ c

theorem signed_capEval (Y : Type) [TopologicalSpace Y] (n : ℕ)
    (B : (singularChains ℤ (TopCat.of (Y × MBall (Nat.succ n)))).X (Nat.succ n))
    (α : ↥(relKern ℤ (TopCat.of (tcmX Y (Nat.succ n) 1)) (tcmA Y (Nat.succ n) 1) (Nat.succ n))) :
    kronecker ℤ (ssB (tcmX Y (Nat.succ n) 1))
      (cup ℤ (ssB (tcmX Y (Nat.succ n) 1)) α.1 (gammaSharp Y (Nat.succ n)))
      (pushChain (TopCat.of (Y × MBall (Nat.succ n))) (TopCat.of (tcmX Y (Nat.succ n) 1))
        (TopCat.ofHom (capX Y (Nat.succ n))) (Nat.succ n) B)
      = kronecker ℤ (ssB (Y × MBall (Nat.succ n))) (signedPα Y n α).1 B := by
  have hpush := kronecker_pushChain (TopCat.ofHom (capX Y (Nat.succ n))) (Nat.succ n + 0)
    (cup ℤ (ssB (tcmX Y (Nat.succ n) 1)) α.1 (gammaSharp Y (Nat.succ n))) B
  exact hpush.trans (congrArg (fun g : Cochain ℤ (ssB (Y × MBall (Nat.succ n))) (Nat.succ n + 0) =>
      kronecker ℤ (ssB (Y × MBall (Nat.succ n))) g B)
    ((cap_pullback_cup_gammaSharp Y (Nat.succ n) α.1).trans (signedPα_coe Y n α).symm))

theorem signed_capEval_class (Y : Type) [TopologicalSpace Y] (n : ℕ)
    (α : ↥(relKern ℤ (TopCat.of (tcmX Y (Nat.succ n) 1)) (tcmA Y (Nat.succ n) 1) (Nat.succ n)))
    (hα : relDiffLM ℤ (TopCat.of (tcmX Y (Nat.succ n) 1)) (tcmA Y (Nat.succ n) 1) (Nat.succ n) α = 0)
    (hαr : relClassOf ℤ (TopCat.of (tcmX Y (Nat.succ n) 1)) (tcmA Y (Nat.succ n) 1) α hα
      = (relCohMap (tcmPr1 Y (Nat.succ n) 1) (tcmA Y (Nat.succ n) 1) (Punct Y (Nat.succ n))
          (fun x hx => hx) ℤ (Nat.succ n)).hom (Mpun (Nat.succ n) Y))
    (hp : relDiffLM ℤ (TopCat.of (Y × MBall (Nat.succ n))) (DiscB Y (Nat.succ n)) (Nat.succ n)
      (signedPα Y n α) = 0)
    (b : ↥(relKern ℤ (TopCat.of (Y × MBall (Nat.succ n))) (DiscB Y (Nat.succ n)) (Nat.succ n)))
    (hb : relDiffLM ℤ (TopCat.of (Y × MBall (Nat.succ n))) (DiscB Y (Nat.succ n)) (Nat.succ n) b = 0)
    (hbc : relClassOf ℤ (TopCat.of (Y × MBall (Nat.succ n))) (DiscB Y (Nat.succ n)) b hb
      = stepDisc Y (Nat.succ n) (Mn (Nat.succ n) Y)) :
    relClassOf ℤ (TopCat.of (Y × MBall (Nat.succ n))) (DiscB Y (Nat.succ n)) (signedPα Y n α) hp
      = relClassOf ℤ (TopCat.of (Y × MBall (Nat.succ n))) (DiscB Y (Nat.succ n)) b hb := by
  have h1 : relClassOf ℤ (TopCat.of (Y × MBall (Nat.succ n))) (DiscB Y (Nat.succ n))
        (signedPα Y n α) hp
      = (relCohMap (capX Y (Nat.succ n)) (DiscB Y (Nat.succ n)) (tcmA Y (Nat.succ n) 1)
          (capX_mem_tcmA Y (Nat.succ n)) ℤ (Nat.succ n)).hom
          (relClassOf ℤ (TopCat.of (tcmX Y (Nat.succ n) 1)) (tcmA Y (Nat.succ n) 1) α hα) :=
    (relClassOf_proof_irrel ℤ (TopCat.of (Y × MBall (Nat.succ n))) (DiscB Y (Nat.succ n))
      (signedPα Y n α) hp (signedPα_cocycle Y n α hα)).trans
      ((homologyMap_relComplexMap_relClassOf (R := ℤ)
        (X₁ := TopCat.of (Y × MBall (Nat.succ n))) (X₂ := TopCat.of (tcmX Y (Nat.succ n) 1))
        (DiscB Y (Nat.succ n)) (tcmA Y (Nat.succ n) 1) (TopCat.ofHom (capX Y (Nat.succ n)))
        (capX_mem_tcmA Y (Nat.succ n)) α hα).symm)
  rw [h1, hαr, capX_pr1_Mpun Y (Nat.succ n)]
  exact hbc.symm

theorem signed_gap (Y : Type) [TopologicalSpace Y] (n : ℕ)
    (B : (singularChains ℤ (TopCat.of (Y × MBall (Nat.succ n)))).X (Nat.succ n))
    (hB : IsSmallChain (DiscB Y (Nat.succ n)) ∅
      ((singularChains ℤ (TopCat.of (Y × MBall (Nat.succ n)))).d (Nat.succ n) n B))
    (b p : ↥(relKern ℤ (TopCat.of (Y × MBall (Nat.succ n))) (DiscB Y (Nat.succ n)) (Nat.succ n)))
    (hb : relDiffLM ℤ (TopCat.of (Y × MBall (Nat.succ n))) (DiscB Y (Nat.succ n)) (Nat.succ n) b = 0)
    (hp : relDiffLM ℤ (TopCat.of (Y × MBall (Nat.succ n))) (DiscB Y (Nat.succ n)) (Nat.succ n) p = 0)
    (hcl : relClassOf ℤ (TopCat.of (Y × MBall (Nat.succ n))) (DiscB Y (Nat.succ n)) p hp
      = relClassOf ℤ (TopCat.of (Y × MBall (Nat.succ n))) (DiscB Y (Nat.succ n)) b hb) :
    kronecker ℤ (ssB (Y × MBall (Nat.succ n))) p.1 B
      = kronecker ℤ (ssB (Y × MBall (Nat.succ n))) b.1 B := by
  have hpc : (ModuleCat.Hom.hom ((relComplex ℤ (TopCat.of (Y × MBall (Nat.succ n)))
      (DiscB Y (Nat.succ n))).d (Nat.succ n) (Nat.succ n + 1))) p = 0 :=
    (relDiffLM_eq_zero_iff (TopCat.of (Y × MBall (Nat.succ n))) (DiscB Y (Nat.succ n))
      (Nat.succ n) p).mpr hp
  have hbc : (ModuleCat.Hom.hom ((relComplex ℤ (TopCat.of (Y × MBall (Nat.succ n)))
      (DiscB Y (Nat.succ n))).d (Nat.succ n) (Nat.succ n + 1))) b = 0 :=
    (relDiffLM_eq_zero_iff (TopCat.of (Y × MBall (Nat.succ n))) (DiscB Y (Nat.succ n))
      (Nat.succ n) b).mpr hb
  have hEq : (relComplex ℤ (TopCat.of (Y × MBall (Nat.succ n)))
        (DiscB Y (Nat.succ n))).homologyπ (Nat.succ n)
      (cocycleOfK (relComplex ℤ (TopCat.of (Y × MBall (Nat.succ n))) (DiscB Y (Nat.succ n)))
        p hpc)
      = (relComplex ℤ (TopCat.of (Y × MBall (Nat.succ n)))
          (DiscB Y (Nat.succ n))).homologyπ (Nat.succ n)
        (cocycleOfK (relComplex ℤ (TopCat.of (Y × MBall (Nat.succ n))) (DiscB Y (Nat.succ n)))
          b hbc) := by
    rw [← relClassOf_eq_homologyπ_cocycleOfK ℤ (TopCat.of (Y × MBall (Nat.succ n)))
        (DiscB Y (Nat.succ n)) p hp hpc,
      ← relClassOf_eq_homologyπ_cocycleOfK ℤ (TopCat.of (Y × MBall (Nat.succ n)))
        (DiscB Y (Nat.succ n)) b hb hbc, hcl]
  exact kronecker_relComplex_eq_of_homology_eq (X := TopCat.of (Y × MBall (Nat.succ n)))
    (DiscB Y (Nat.succ n)) n p b hpc hbc hEq B hB

end

end Work.Whitney
