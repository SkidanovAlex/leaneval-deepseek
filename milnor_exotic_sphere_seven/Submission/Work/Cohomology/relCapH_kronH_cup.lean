import Mathlib
import Submission.Work.Cohomology.RelCapHTransfer
import Submission.Work.Cohomology.RelCupTransfer
import Submission.Work.Cohomology.KroneckerH
import Submission.Work.Cohomology.RelCap
import Submission.Work.Cohomology.relIncl_relCupH

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-- Chain-complex version of `homologyMap_homologyπ`: a chain map sends the homology class of a
cycle to the class of the image cycle. -/
lemma homologyMap_homologyπ_chain {K L : ChainComplex (ModuleCat ℤ) ℕ} (φ : K ⟶ L) (n : ℕ)
    (z : K.cycles n) :
    (HomologicalComplex.homologyMap φ n).hom ((K.homologyπ n).hom z) =
      (L.homologyπ n).hom ((HomologicalComplex.cyclesMap φ n).hom z) := by
  have h := HomologicalComplex.homologyπ_naturality φ n
  have h2 := congrArg (fun (g : K.cycles n ⟶ L.homology n) => g.hom z) h
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h2

/-- `kronH_apply` with the cycle explicitly in the singular chain complex of a topological
space. -/
lemma kronH_apply_sing (X : TopCat) {n : ℕ} (α : Cochain ℤ (TopCat.toSSet.obj X) n)
    (hα : cochainDiff ℤ (TopCat.toSSet.obj X) α = 0) (z : (singularChains ℤ X).cycles n) :
    kronH ℤ (TopCat.toSSet.obj X) n (cohomologyClassOf ℤ (TopCat.toSSet.obj X) α hα)
        (((singularChains ℤ X).homologyπ n) z)
      = α (((singularChains ℤ X).iCycles n) z) :=
  kronH_apply ℤ (TopCat.toSSet.obj X) α hα z

theorem relCapH_kronH_cup (X : TopCat) (A : Set X) (n m : ℕ)
    (alpha : Work.Cohomology.relCohomology ℤ X A n)
    (beta : Work.Cohomology.relCohomology ℤ X A m)
    (c : (Work.Cohomology.relChains X A).homology (n + m))
    (c' : (Work.Cohomology.singularChains ℤ X).homology (n + m))
    (hc : HomologicalComplex.homologyMap
        (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains X A)) (n + m) c' = c) :
    Work.Cohomology.kronH ℤ (TopCat.toSSet.obj X) m
        (HomologicalComplex.homologyMap (Work.Cohomology.relIncl ℤ X A) m beta)
        (Work.Cohomology.relCapPair X A n m alpha c)
      = Work.Cohomology.kronH ℤ (TopCat.toSSet.obj X) (n + m)
          (HomologicalComplex.homologyMap (Work.Cohomology.relIncl ℤ X A) (n + m)
            (Work.Cohomology.relCupH' ℤ X A n m alpha beta)) c' := by
  obtain ⟨a, ha, rfl⟩ := exists_relClassOf ℤ X A n alpha
  obtain ⟨b, hb, rfl⟩ := exists_relClassOf ℤ X A m beta
  obtain ⟨z', rfl⟩ :=
    (ModuleCat.epi_iff_surjective ((singularChains ℤ X).homologyπ (n + m))).mp inferInstance c'
  let zα : (relComplex ℤ X A).cycles n := relCocycleOf ℤ X A a ha
  let zβ : (relComplex ℤ X A).cycles m := relCocycleOf ℤ X A b hb
  let cc : (relChains X A).cycles (n + m) :=
    (HomologicalComplex.cyclesMap (cokernel.π (inclChains X A)) (n + m)).hom z'
  have hαc : relClassOf ℤ X A a ha = ((relComplex ℤ X A).homologyπ n) zα := rfl
  have hza : ((relComplex ℤ X A).iCycles n) zα = a := iCycles_relCocycleOf ℤ X A a ha
  have hc_eq : c = ((relChains X A).homologyπ (n + m)) cc := by
    rw [← hc]
    exact homologyMap_homologyπ_chain (cokernel.π (inclChains X A)) (n + m) z'
  have hcyc : ((relChains X A).iCycles (n + m)) cc
      = ((cokernel.π (inclChains X A)).f (n + m)) (((singularChains ℤ X).iCycles (n + m)) z') := by
    have h := congrArg
      (fun (g : (singularChains ℤ X).cycles (n + m) ⟶ (relChains X A).X (n + m)) => g.hom z')
      (HomologicalComplex.cyclesMap_i (cokernel.π (inclChains X A)) (n + m))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    exact h
  have hcap : ((singularChains ℤ X).iCycles m) (relCapPairZ X A n m zα cc)
      = (cap ℤ (TopCat.toSSet.obj X) (a.1 : Cochain ℤ (TopCat.toSSet.obj X) n) m)
          (((singularChains ℤ X).iCycles (n + m)) z') := by
    rw [relCapPairZ_iCycles X A n m zα cc]
    rw [hza, hcyc, relChains_cokernelIso_canon_apply X A (n + m)
      (((singularChains ℤ X).iCycles (n + m)) z')]
    exact relCapHalf_apply_incl X A (m := m) a (((singularChains ℤ X).iCycles (n + m)) z')
  have hL : kronH ℤ (TopCat.toSSet.obj X) m
      ((HomologicalComplex.homologyMap (relIncl ℤ X A) m) (relClassOf ℤ X A b hb))
      (relCapPair X A n m (relClassOf ℤ X A a ha)
        (((relChains X A).homologyπ (n + m)) cc))
      = kronecker ℤ (TopCat.toSSet.obj X) (b.1 : Cochain ℤ (TopCat.toSSet.obj X) m)
          ((cap ℤ (TopCat.toSSet.obj X) (a.1 : Cochain ℤ (TopCat.toSSet.obj X) n) m)
            (((singularChains ℤ X).iCycles (n + m)) z')) := by
    rw [hαc]
    rw [relIncl_homologyMap_relClassOf ℤ X A b hb]
    rw [relCapPair_apply X A n m zα cc]
    rw [kronH_apply_sing X (b.1 : Cochain ℤ (TopCat.toSSet.obj X) m)
      (relClassOf_cochainDiff ℤ X A b hb) (relCapPairZ X A n m zα cc)]
    rw [hcap]
    rfl
  have hR : kronH ℤ (TopCat.toSSet.obj X) (n + m)
      ((HomologicalComplex.homologyMap (relIncl ℤ X A) (n + m))
        (relCupH' ℤ X A n m (relClassOf ℤ X A a ha) (relClassOf ℤ X A b hb)))
      (((singularChains ℤ X).homologyπ (n + m)) z')
      = kronecker ℤ (TopCat.toSSet.obj X)
          ((relCup ℤ X A n m a b).1 : Cochain ℤ (TopCat.toSSet.obj X) (n + m))
          (((singularChains ℤ X).iCycles (n + m)) z') := by
    rw [relCupH'_apply ℤ X A a b ha hb]
    rw [relIncl_homologyMap_relClassOf ℤ X A (relCup ℤ X A n m a b)
      (relDiffLM_relCup_of_cocycles ℤ X A a b ha hb)]
    rw [kronH_apply_sing X ((relCup ℤ X A n m a b).1 : Cochain ℤ (TopCat.toSSet.obj X) (n + m))
      (relClassOf_cochainDiff ℤ X A (relCup ℤ X A n m a b)
        (relDiffLM_relCup_of_cocycles ℤ X A a b ha hb)) z']
    rfl
  rw [hc_eq, hL, hR]
  exact relKronecker_cap_cup ℤ X A a b (((singularChains ℤ X).iCycles (n + m)) z')

end

end Work.Cohomology
