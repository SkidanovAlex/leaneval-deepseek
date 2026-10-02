import Mathlib
import Submission.Work.Serre.B1Rel.Assembly
import Submission.Work.Serre.relKronEquiv

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# From the rational pair comparison to the surjectivity of the relative edge map

Given the rational pair comparison `relPairMapRat p b` at degree `r` and the **naturality of the
relative Kronecker pairing over `ℚ`** for the pair `(E, p⁻¹{b}) → (B, {b})`, the cohomological edge
map `H^r(B,{b};ℚ) → H^r(E,p⁻¹{b};ℚ)` is surjective: by naturality it is the transpose of the
homology map, whose transpose is surjective because the homology map is injective.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Serre.B1Rel

noncomputable section

/-- **The relative edge map is surjective, from the pair comparison and the naturality of the
relative Kronecker pairing.** -/
theorem fibrePairMapSurj_aux (r N : ℕ) (hr : 1 ≤ r) (hrN : r ≤ N)
    {B : Type} [TopologicalSpace B] (hB : PathConnectedSpace B)
    {E : Type} [TopologicalSpace E] (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p)
    (hvan : ∀ b : B, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p b)) t))
    (hpc : ∀ b : B, PathConnectedSpace (Work.StemsB.fibre p b))
    (hgen : ∀ b : B, Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p b)) r
      ≅ ModuleCat.of ℚ ℚ))
    (b : B)
    (hnat : ∀ (β : (Work.Cohomology.relComplex ℚ (TopCat.of B) ({b} : Set B)).homology r)
        (c : (Work.StemsB.relChainsR ℚ (TopCat.of E) (p ⁻¹' {b})).homology r),
      (Work.Serre.relKronMapR ℚ (TopCat.of E) (p ⁻¹' {b}) r).hom
          ((HomologicalComplex.homologyMap (Work.Cohomology.relComplexMap ℚ (p ⁻¹' {b})
            ({b} : Set B) (TopCat.ofHom p) (fun x hx => hx)) r).hom β) c
        = (Work.Serre.relKronMapR ℚ (TopCat.of B) ({b} : Set B) r).hom β
            ((HomologicalComplex.homologyMap (Work.Serre.relPairMapRat p b) r).hom c)) :
    Function.Surjective (Work.Thom.relCohMap p (p ⁻¹' {b}) {b} (fun x hx => hx) ℚ r).hom := by
  haveI := hB
  -- the sharp fibre hypotheses
  have hfib : ∀ y : B, ∀ j : ℕ, 0 < j → j < r →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p y)) j) :=
    fun y j hj hjr => hvan y j hj (by omega) (le_trans (le_of_lt hjr) hrN)
  have h0 : ∀ y : B, Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p y)) 0
      ≅ ModuleCat.of ℚ ℚ) := fun y => by
    haveI := hpc y
    exact Work.Serre.ratH_zero_of_pathConnected (Work.StemsB.fibre p y)
  -- the rational pair comparison at degree `r`
  haveI hiso : IsIso (HomologicalComplex.homologyMap (Work.Serre.relPairMapRat p b) r) :=
    relPairMapRat_isIso p hp b (r + 1) r (by omega) hfib h0 r (by omega)
  have hinj : Function.Injective
      (HomologicalComplex.homologyMap (Work.Serre.relPairMapRat p b) r).hom :=
    (ModuleCat.mono_iff_injective _).mp (IsIso.mono_of_iso _)
  have hdual : Function.Surjective
      (LinearMap.dualMap (HomologicalComplex.homologyMap (Work.Serre.relPairMapRat p b) r).hom) :=
    (LinearMap.dualMap_surjective_iff
      (f := (HomologicalComplex.homologyMap (Work.Serre.relPairMapRat p b) r).hom)).mpr hinj
  -- naturality of the relative Kronecker pairing, as an equation of morphisms
  have hnat' : (Work.Thom.relCohMap p (p ⁻¹' {b}) {b} (fun x hx => hx) ℚ r)
        ≫ Work.Serre.relKronMapR ℚ (TopCat.of E) (p ⁻¹' {b}) r
      = Work.Serre.relKronMapR ℚ (TopCat.of B) ({b} : Set B) r
        ≫ ModuleCat.ofHom (LinearMap.dualMap
            (HomologicalComplex.homologyMap (Work.Serre.relPairMapRat p b) r).hom) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro β
    apply LinearMap.ext
    intro c
    exact hnat β c
  -- the composite with the pairing on `(E, p⁻¹b)` is surjective
  have hfun : (Work.Serre.relKronMapR ℚ (TopCat.of E) (p ⁻¹' {b}) r).hom
        ∘ (Work.Thom.relCohMap p (p ⁻¹' {b}) {b} (fun x hx => hx) ℚ r).hom
      = (ModuleCat.ofHom (LinearMap.dualMap
            (HomologicalComplex.homologyMap (Work.Serre.relPairMapRat p b) r).hom)).hom
        ∘ (Work.Serre.relKronMapR ℚ (TopCat.of B) ({b} : Set B) r).hom := by
    funext y
    have h := congrArg (fun (m : Work.Thom.RelCoh ℚ r B ({b} : Set B) ⟶
        ModuleCat.of ℚ ((Work.StemsB.relChainsR ℚ (TopCat.of E) (p ⁻¹' {b})).homology r
          →ₗ[ℚ] ℚ)) => m.hom y) hnat'
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, Function.comp_apply] using h
  have hsurj : Function.Surjective
      ((Work.Serre.relKronMapR ℚ (TopCat.of E) (p ⁻¹' {b}) r).hom
        ∘ (Work.Thom.relCohMap p (p ⁻¹' {b}) {b} (fun x hx => hx) ℚ r).hom) := by
    rw [hfun]
    exact hdual.comp (Work.Serre.relKronMapRSurjective (TopCat.of B) ({b} : Set B) r)
  intro y
  obtain ⟨z, hz⟩ := hsurj ((Work.Serre.relKronMapR ℚ (TopCat.of E) (p ⁻¹' {b}) r).hom y)
  exact ⟨z, Work.Serre.relKronMapRInjective (TopCat.of E) (p ⁻¹' {b}) r
    (by simpa only [Function.comp_apply] using hz)⟩

end

end Work.Serre.B1Rel
