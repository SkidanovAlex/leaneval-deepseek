import Mathlib
import Submission.Work.Cohomology.sphere3DiscPairDefs
import Submission.Work.Cohomology.CupRing
import Submission.Work.Cohomology.Pullback
import Submission.Work.Cohomology.Kronecker
import Submission.Work.Sph3Disc.pairDelta_mixedCup_general

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Functoriality and Kronecker bookkeeping for the Künneth evaluation

This file collects the (defeq-fragile) lemmas identifying the pullback of a cocycle with the
pullback of a cohomology class, and the lemma turning a nonzero class of `H⁶(S³ × S³; ℤ)` into a
`6`-cycle on which a representing cocycle is nonzero.  It is kept separate from
`Submission/Work/Cohomology/Kunneth/prodSph33Kunneth_chain_eval_ne_zero.lean` so that the latter
can be compiled without the `backward.isDefEq.respectTransparency` option needed here.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology.Kunneth

noncomputable section

open Work.Cohomology


/-! ## Pullback of cochains and of cohomology classes -/

/-- Pullback along a continuous map commutes with the coboundary. -/
theorem cochainPullbackHom_cochainDiff (X Y : TopCat) (f : X ⟶ Y) (n : ℕ)
    (φ : Cochain ℤ (TopCat.toSSet.obj Y) n) :
    (cochainPullbackHom ℤ X Y f (n+1)).hom (cochainDiff ℤ (TopCat.toSSet.obj Y) φ)
      = cochainDiff ℤ (TopCat.toSSet.obj X) ((cochainPullbackHom ℤ X Y f n).hom φ) := by
  have hcomm := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    ((dualChainMap ℤ X Y f).comm n (n+1))) φ
  simp only [ModuleCat.hom_comp] at hcomm
  rw [show (ModuleCat.Hom.hom ((singularCochainComplex ℤ Y).d n (n+1)))
        = cochainDiffLM ℤ (TopCat.toSSet.obj Y) n from singularCochain_d_eq ℤ Y n,
      show (ModuleCat.Hom.hom ((singularCochainComplex ℤ X).d n (n+1)))
        = cochainDiffLM ℤ (TopCat.toSSet.obj X) n from singularCochain_d_eq ℤ X n] at hcomm
  change cochainDiff ℤ (TopCat.toSSet.obj X) ((cochainPullbackHom ℤ X Y f n).hom φ)
    = (cochainPullbackHom ℤ X Y f (n+1)).hom (cochainDiff ℤ (TopCat.toSSet.obj Y) φ) at hcomm
  exact hcomm.symm

/-- The pullback of a cocycle is a cocycle. -/
theorem pullback_cocycle (X Y : TopCat) (f : X ⟶ Y) (n : ℕ)
    (φ : Cochain ℤ (TopCat.toSSet.obj Y) n) (hφ : cochainDiff ℤ (TopCat.toSSet.obj Y) φ = 0) :
    cochainDiff ℤ (TopCat.toSSet.obj X) ((cochainPullbackHom ℤ X Y f n).hom φ) = 0 := by
  rw [← cochainPullbackHom_cochainDiff X Y f n φ, hφ, map_zero]

/-- Any two proofs of the cocycle condition give the same cohomology class. -/
theorem cohomologyClassOf_proof_irrel (X : SSet) {n : ℕ} (α : Cochain ℤ X n)
    (h1 h2 : cochainDiff ℤ X α = 0) :
    cohomologyClassOf ℤ X α h1 = cohomologyClassOf ℤ X α h2 :=
  congrArg _ (Subsingleton.elim h1 h2)

/-- **The pullback of the cohomology class of a cocycle is the class of the pullback.** -/
theorem pullback_class_eq (X Y : TopCat) (f : X ⟶ Y) (n : ℕ)
    (φ : Cochain ℤ (TopCat.toSSet.obj Y) n) (hφ : cochainDiff ℤ (TopCat.toSSet.obj Y) φ = 0)
    (h : cochainDiff ℤ (TopCat.toSSet.obj X) ((cochainPullbackHom ℤ X Y f n).hom φ) = 0) :
    (singularCohomologyMap ℤ X Y f n).hom (cohomologyClassOf ℤ (TopCat.toSSet.obj Y) φ hφ)
      = cohomologyClassOf ℤ (TopCat.toSSet.obj X) ((cochainPullbackHom ℤ X Y f n).hom φ) h := by
  rw [cohomologyClassOf_proof_irrel (TopCat.toSSet.obj X) _ h (pullback_cocycle X Y f n φ hφ)]
  have hφ' : (ModuleCat.Hom.hom ((singularCochainComplex ℤ Y).d n (n+1))) φ = 0 := by
    rw [singularCochain_d_apply ℤ Y]; exact hφ
  have hcanon : (ModuleCat.Hom.hom ((singularCochainComplex ℤ X).d n (n+1)))
      (((cochainPullbackHom ℤ X Y f n)).hom φ) = 0 := by
    rw [singularCochain_d_apply ℤ X]
    exact pullback_cocycle X Y f n φ hφ
  change (HomologicalComplex.homologyMap (dualChainMap ℤ X Y f) n)
      (((singularCochainComplex ℤ Y).homologyπ n).hom (cocycleOfK (singularCochainComplex ℤ Y) φ hφ'))
    = ((singularCochainComplex ℤ X).homologyπ n).hom
        (cocycleOfK (singularCochainComplex ℤ X) (((cochainPullbackHom ℤ X Y f n)).hom φ) hcanon)
  have hnat := congrArg (fun (g : (singularCochainComplex ℤ Y).cycles n ⟶
        (singularCochainComplex ℤ X).homology n) => g.hom
      (cocycleOfK (singularCochainComplex ℤ Y) φ hφ'))
    (HomologicalComplex.homologyπ_naturality (dualChainMap ℤ X Y f) n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hnat
  rw [hnat, Work.Sph3Disc.pdmc_cyclesMap_cocycleOfK _ _ (dualChainMap ℤ X Y f) φ hφ' hcanon]
  rfl

end

end Work.Cohomology.Kunneth
