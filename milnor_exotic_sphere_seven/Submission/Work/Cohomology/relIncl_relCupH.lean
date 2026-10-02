import Mathlib
import Submission.Work.Cohomology.RelCupTransfer
import Submission.Work.Cohomology.relCupH
import Submission.Work.Cohomology.CupRing

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The relative cup product is compatible with the inclusion `H^*(X,A) ⟶ H^*(X)`

`Work.Cohomology.relCupH'` is a chosen bilinear pairing on the relative cohomology
`H^*(X,A;R)`, and `Work.Cohomology.cupH'` the chosen pairings on the absolute cohomology
`H^*(X;R)`.  Since `relCup` is by construction the restriction of the absolute cup product `cup`
to the relative cochains (`relCup_coe`), the map

  `relIncl_* : H^*(X,A;R) ⟶ H^*(X;R)`

induced by the inclusion of cochain complexes `relIncl` is a ring homomorphism:

  `relIncl_*(x ⌣_rel y) = (relIncl_* x) ⌣ (relIncl_* y)`.

This is proved by reducing both sides to the level of relative cocycles:

* every relative cohomology class is the class of a relative cocycle (`exists_relClassOf`),
  because the projection `cycles → homology` is surjective;
* on the class of a relative cocycle `a`, the inclusion `relIncl` sends it to the absolute class
  of the underlying cochain `a.1` (`relIncl_homologyMap_relClassOf`);
* the computation rules `relCupH'_apply` and `cupH'_apply'`, together with `relCup_coe`, then
  identify both sides with the class of the absolute cup product `a.1 ⌣ b.1`.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

variable (R : Type) [CommRing R]

/-- **The inclusion `relIncl` on the class of a relative cocycle.**  The image under
`relIncl_* : H^n(X,A;R) ⟶ H^n(X;R)` of the class of a relative cocycle `a` is the absolute
cohomology class of the underlying cochain `a.1`. -/
theorem relIncl_homologyMap_relClassOf (X : TopCat) (A : Set X) {n : ℕ}
    (a : relKern R X A n) (ha : relDiffLM R X A n a = 0) :
    (HomologicalComplex.homologyMap (relIncl R X A) n).hom (relClassOf R X A a ha) =
      cohomologyClassOf R (TopCat.toSSet.obj X) a.1 (relClassOf_cochainDiff R X A a ha) := by
  have hnat := congrArg
    (fun (g : (relComplex R X A).cycles n ⟶ (singularCochainComplex R X).homology n) =>
      g.hom (relCocycleOf R X A a ha))
    (HomologicalComplex.homologyπ_naturality (relIncl R X A) n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hnat
  rw [show relClassOf R X A a ha
      = ((relComplex R X A).homologyπ n).hom (relCocycleOf R X A a ha) from rfl, hnat]
  rw [show cohomologyClassOf R (TopCat.toSSet.obj X) a.1 (relClassOf_cochainDiff R X A a ha)
      = ((SSetCochainComplex R (TopCat.toSSet.obj X)).homologyπ n).hom
          (cocycleOf R (TopCat.toSSet.obj X) a.1 (relClassOf_cochainDiff R X A a ha)) from rfl]
  apply congrArg ((SSetCochainComplex R (TopCat.toSSet.obj X)).homologyπ n)
  apply iCycles_injective R (TopCat.toSSet.obj X) n
  have hci := congrArg
    (fun (g : (relComplex R X A).cycles n ⟶ (singularCochainComplex R X).X n) =>
      g.hom (relCocycleOf R X A a ha))
    (HomologicalComplex.cyclesMap_i (relIncl R X A) n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hci
  erw [hci, iCycles_relCocycleOf R X A a ha,
    iCycles_cocycleOf R (TopCat.toSSet.obj X) a.1 (relClassOf_cochainDiff R X A a ha)]
  rfl

/-- **Every relative cohomology class is the class of a relative cocycle.** -/
theorem exists_relClassOf (X : TopCat) (A : Set X) (n : ℕ) (x : relCohomology R X A n) :
    ∃ (a : relKern R X A n) (ha : relDiffLM R X A n a = 0), relClassOf R X A a ha = x := by
  obtain ⟨z, hz⟩ :=
    (ModuleCat.epi_iff_surjective ((relComplex R X A).homologyπ n)).mp inferInstance x
  refine ⟨(relComplex R X A).iCycles n z, ?_, ?_⟩
  · rw [← relComplex_d_apply R X A]
    exact iCycles_d_apply_K (relComplex R X A) n z
  · have hz' : relCocycleOf R X A ((relComplex R X A).iCycles n z)
        (by rw [← relComplex_d_apply R X A]; exact iCycles_d_apply_K (relComplex R X A) n z) = z := by
      apply iCycles_injective_K (relComplex R X A) n
      rw [iCycles_relCocycleOf]
    rw [show relClassOf R X A ((relComplex R X A).iCycles n z) _
        = ((relComplex R X A).homologyπ n).hom
            (relCocycleOf R X A ((relComplex R X A).iCycles n z) _) from rfl, hz']
    exact hz

end

/-- **`relIncl_*` is a ring homomorphism for the cup products**: the inclusion of the relative
cohomology of `(X,A)` into the absolute cohomology of `X` sends the relative cup product to the
absolute cup product of the images. -/
theorem relIncl_relCupH (R : Type) [CommRing R] (X : TopCat) (A : Set X) (n m : ℕ)
    (x : Work.Cohomology.relCohomology R X A n) (y : Work.Cohomology.relCohomology R X A m) :
    (HomologicalComplex.homologyMap (Work.Cohomology.relIncl R X A) (n + m)).hom
        (Work.Cohomology.relCupH' R X A n m x y) =
      Work.Cohomology.cupH' R (TopCat.toSSet.obj X) n m
        ((HomologicalComplex.homologyMap (Work.Cohomology.relIncl R X A) n).hom x)
        ((HomologicalComplex.homologyMap (Work.Cohomology.relIncl R X A) m).hom y) := by
  obtain ⟨a, ha, rfl⟩ := exists_relClassOf R X A n x
  obtain ⟨b, hb, rfl⟩ := exists_relClassOf R X A m y
  rw [relCupH'_apply R X A a b ha hb]
  rw [relIncl_homologyMap_relClassOf R X A a ha,
    relIncl_homologyMap_relClassOf R X A b hb]
  rw [cupH'_apply' R (TopCat.toSSet.obj X) a.1 b.1
    (relClassOf_cochainDiff R X A a ha) (relClassOf_cochainDiff R X A b hb)]
  rw [relIncl_homologyMap_relClassOf R X A (relCup R X A n m a b)
    (relDiffLM_relCup_of_cocycles R X A a b ha hb)]
  exact cohomologyClassOf_congr R (TopCat.toSSet.obj X) (relCup_coe R X A a b) _ _

end Work.Cohomology
