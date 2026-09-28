import Mathlib
import Submission.Work.Cohomology.CupRing
import Submission.Work.Cohomology.Pullback
import Submission.Work.Cohomology.cupNatural

/-!
# Naturality of the cup product on singular cohomology

This file proves that the Alexander–Whitney cup product on singular cohomology is natural with
respect to continuous maps: for `f : X ⟶ Y`, `n m : ℕ` and classes `x ∈ Hⁿ(Y;R)`, `y ∈ Hᵐ(Y;R)`,

`f*(x ⌣ y) = f*x ⌣ f*y`,

where `f* = singularCohomologyMap R X Y f` and `⌣ = cupH'` is the product on cohomology packaged in
`Submission/Work/Cohomology/CupRing.lean`.

The proof reduces, via `CupRing.exists_cohomologyClassOf`, to the case where `x` and `y` are the
classes of cocycles `α` and `β` on the singular simplicial set of `Y`.  Both sides are then
computed with the defining rule `CupRing.cupH'_apply'` of `cupH'` and at the cochain level the two
are identified by `cupNatural` (naturality of the Alexander–Whitney product for maps of simplicial
sets).

The reduction of `f*` to the cochain level is the lemma `singularCohomologyMap_classOf`: pulling
back the cohomology *class* of a cocycle `α` along `f` is the class of the transpose of the
induced chain map applied to `α`.  This is `HomologicalComplex.homologyπ_naturality` together with
the fact that the cochain pullback of a cocycle is again a cocycle,
`cochainDiff_dualMap_chainComplexMap`.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-! ## The cochain level

The pullback of a cocycle along the chain map induced by a map of simplicial sets is again a
cocycle: this is just the commutativity of the induced chain map with the differential. -/

theorem cochainDiff_dualMap_chainComplexMap (R : Type) [CommRing R] {X Y : SSet} (g : X ⟶ Y)
    {n : ℕ} (α : (Y.chainComplex (ModuleCat.of R R)).X n →ₗ[R] R)
    (hα : cochainDiff R Y α = 0) :
    cochainDiff R X (((SSet.chainComplexMap g (ModuleCat.of R R)).f n).hom.dualMap α) = 0 := by
  have hcomm := HomologicalComplex.Hom.comm (SSet.chainComplexMap g (ModuleCat.of R R)) (n+1) n
  have hc := congrArg ModuleCat.Hom.hom hcomm
  simp only [ModuleCat.hom_comp] at hc
  apply LinearMap.ext
  intro c
  have hc' : ((Y.chainComplex (ModuleCat.of R R)).d (n+1) n).hom
        (((SSet.chainComplexMap g (ModuleCat.of R R)).f (n+1)).hom c) =
      ((SSet.chainComplexMap g (ModuleCat.of R R)).f n).hom
        (((X.chainComplex (ModuleCat.of R R)).d (n+1) n).hom c) := by
    simpa only [LinearMap.comp_apply] using LinearMap.congr_fun hc c
  simp only [cochainDiff, LinearMap.dualMap_apply, LinearMap.comp_apply, LinearMap.zero_apply]
  rw [← hc']
  show (cochainDiff R Y α) (((SSet.chainComplexMap g (ModuleCat.of R R)).f (n+1)).hom c) = 0
  rw [hα, LinearMap.zero_apply]

/-! ## The cohomology level

We record the standard fact that a morphism of cochain complexes acts on the class of a cycle by
sending it to the class of the image cycle, together with the two "bridge" lemmas that let us
identify the singular cochain complex of a topological space with the cochain complex of its
singular simplicial set. -/

/-- The singular cochain complex of a topological space is (definitionally) the cochain complex of
its singular simplicial set, so `iCycles` may be used interchangeably. -/
theorem iCycles_cocycleOf_sing (R : Type) [CommRing R] (X : TopCat) {n : ℕ}
    (α : ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of R R)).X n →ₗ[R] R)
    (h : cochainDiff R (TopCat.toSSet.obj X) α = 0) :
    (HomologicalComplex.iCycles (singularCochainComplex R X) n).hom
      (cocycleOf R (TopCat.toSSet.obj X) α h) = α :=
  iCycles_cocycleOf R (TopCat.toSSet.obj X) α h

/-- A morphism of cochain complexes sends the class of a cycle to the class of its image:
`homologyMap` is computed on `homologyπ` by `cyclesMap`. -/
theorem homologyMap_homologyπ (R : Type) [CommRing R] {K L : CochainComplex (ModuleCat R) ℕ}
    (φ : K ⟶ L) (n : ℕ) (z : K.cycles n) :
    (HomologicalComplex.homologyMap φ n).hom ((K.homologyπ n).hom z) =
      (L.homologyπ n).hom ((HomologicalComplex.cyclesMap φ n).hom z) := by
  have h := HomologicalComplex.homologyπ_naturality φ n
  have h2 := congrArg (fun (g : K.cycles n ⟶ L.homology n) => g.hom z) h
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h2

/-- The pullback morphism on cochain complexes (`dualChainMap`) sends the cycle associated with a
cocycle `α` on `Y` to the cycle associated with the pullback of `α` on `X`. -/
theorem cyclesMap_cocycleOf (R : Type) [CommRing R] {X Y : TopCat} (f : X ⟶ Y) {n : ℕ}
    (α : (SSetCochainComplex R (TopCat.toSSet.obj Y)).X n)
    (hα : cochainDiff R (TopCat.toSSet.obj Y) α = 0) :
    (HomologicalComplex.cyclesMap (dualChainMap R X Y f) n).hom
        (cocycleOf R (TopCat.toSSet.obj Y) α hα) =
      cocycleOf R (TopCat.toSSet.obj X)
        (((SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of R R)).f n).hom.dualMap α)
        (cochainDiff_dualMap_chainComplexMap R (TopCat.toSSet.map f) α hα) := by
  apply iCycles_injective R (TopCat.toSSet.obj X) n
  have hci := congrArg (fun (g : (singularCochainComplex R Y).cycles n ⟶
      (singularCochainComplex R X).X n) => g.hom
        (cocycleOf R (TopCat.toSSet.obj Y) α hα))
    (HomologicalComplex.cyclesMap_i (dualChainMap R X Y f) n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hci
  show ((HomologicalComplex.iCycles (singularCochainComplex R X) n).hom)
      (((HomologicalComplex.cyclesMap (dualChainMap R X Y f) n).hom)
        (cocycleOf R (TopCat.toSSet.obj Y) α hα)) =
    ((HomologicalComplex.iCycles (singularCochainComplex R X) n).hom)
      (cocycleOf R (TopCat.toSSet.obj X)
        (((SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of R R)).f n).hom.dualMap α)
        (cochainDiff_dualMap_chainComplexMap R (TopCat.toSSet.map f) α hα))
  rw [hci]
  rw [iCycles_cocycleOf_sing R X]
  rw [iCycles_cocycleOf_sing R Y]
  rfl

/-- **`f*` on the class of a cocycle.**  The pullback along `f` of the cohomology class of a
cocycle `α` on `Y` is the class of the transpose of the induced chain map applied to `α`. -/
theorem singularCohomologyMap_classOf (R : Type) [CommRing R] {X Y : TopCat} (f : X ⟶ Y) {n : ℕ}
    (α : (SSetCochainComplex R (TopCat.toSSet.obj Y)).X n)
    (hα : cochainDiff R (TopCat.toSSet.obj Y) α = 0) :
    (HomologicalComplex.homologyMap (dualChainMap R X Y f) n).hom
        (cohomologyClassOf R (TopCat.toSSet.obj Y) α hα) =
      cohomologyClassOf R (TopCat.toSSet.obj X)
        (((SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of R R)).f n).hom.dualMap α)
        (cochainDiff_dualMap_chainComplexMap R (TopCat.toSSet.map f) α hα) := by
  rw [show cohomologyClassOf R (TopCat.toSSet.obj Y) α hα =
      ((singularCochainComplex R Y).homologyπ n).hom
        (cocycleOf R (TopCat.toSSet.obj Y) α hα) from rfl]
  rw [homologyMap_homologyπ R (dualChainMap R X Y f) n
    (cocycleOf R (TopCat.toSSet.obj Y) α hα)]
  rw [cyclesMap_cocycleOf R f α hα]
  rfl

/-! ## Naturality -/

/-- **Naturality of the cup product on singular cohomology.**  For a continuous map `f : X ⟶ Y`
and cohomology classes `x ∈ Hⁿ(Y;R)`, `y ∈ Hᵐ(Y;R)`, pulling back the product `x ⌣ y` is the
product of the pullbacks. -/
theorem cupNaturalH (R : Type) [CommRing R] {X Y : TopCat} (f : X ⟶ Y) (n m : ℕ)
    (x : (SSetCochainComplex R (TopCat.toSSet.obj Y)).homology n)
    (y : (SSetCochainComplex R (TopCat.toSSet.obj Y)).homology m) :
    (singularCohomologyMap R X Y f (n + m)).hom
        (cupH' R (TopCat.toSSet.obj Y) n m x y) =
      cupH' R (TopCat.toSSet.obj X) n m
        ((singularCohomologyMap R X Y f n).hom x)
        ((singularCohomologyMap R X Y f m).hom y) := by
  change (HomologicalComplex.homologyMap (dualChainMap R X Y f) (n + m)).hom
        (cupH' R (TopCat.toSSet.obj Y) n m x y) =
      cupH' R (TopCat.toSSet.obj X) n m
        ((HomologicalComplex.homologyMap (dualChainMap R X Y f) n).hom x)
        ((HomologicalComplex.homologyMap (dualChainMap R X Y f) m).hom y)
  obtain ⟨α, hα, rfl⟩ := exists_cohomologyClassOf R (TopCat.toSSet.obj Y) n x
  obtain ⟨β, hβ, rfl⟩ := exists_cohomologyClassOf R (TopCat.toSSet.obj Y) m y
  rw [cupH'_apply' R (TopCat.toSSet.obj Y) α β hα hβ]
  rw [singularCohomologyMap_classOf R f (cup R (TopCat.toSSet.obj Y) α β)
    (cochainDiff_cup_of_cocycles R (TopCat.toSSet.obj Y) α β hα hβ)]
  rw [singularCohomologyMap_classOf R f α hα, singularCohomologyMap_classOf R f β hβ]
  rw [cupH'_apply' R (TopCat.toSSet.obj X) _ _ _ _]
  exact cohomologyClassOf_congr R (TopCat.toSSet.obj X)
    (cupNatural R (TopCat.toSSet.map f) α β).symm _ _

end

end Work.Cohomology
