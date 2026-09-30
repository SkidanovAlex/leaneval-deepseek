import Mathlib
import Submission.Work.Serre.cubeRelIso
import Submission.Work.Serre.cubeBdry_isZero

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option synthInstance.maxHeartbeats 400000


/-!
# The strong form of the cube statement `(P_D)`

`Work.Serre.cubeRelIso` gives the isomorphism in degrees `< D + f`.  The *strong* form adds the
surjectivity in degree `D + f`, which is what the cell step of the Serre comparison needs:

* for `f ≥ 1` the target `H_{D+f}(I^D, ∂I^D)` vanishes (the cube pair has homology only in degree
  `D`), so surjectivity is automatic;
* for `f = 0` the target is `ℤ` and the *section* of the pullback over the contractible cube
  (`Work.Serre.exists_section_cubePullback`, whose existence only needs `H₀` of the fibre to be `ℤ`)
  splits the pair map on homology in every degree: `cubeSectionMap ≫ cubePairMap = 𝟙`.
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre.SPC

noncomputable section

/-- **Strong form of `(P_D)`.**  For a Serre fibration `p : E → B`, a map `τ : I^D → B` and a fibre
which is homologically `f`-connected over every point of the cube, the map of pairs
`(τ^*E, τ^*E|_{∂I^D}) → (I^D, ∂I^D)` induced by the fibration is an isomorphism on homology in
degrees `< D + f` and surjective in degree `D + f`. -/
theorem cubePairStrong (D : ℕ) :
    ∀ (E : Type) [TopologicalSpace E] (B : Type) [TopologicalSpace B] (p : C(E, B))
      (hp : Work.StemsB.IsSerreFibration p) (τ : C(Work.Stems.Cubical.IC D, B)) (f : ℕ),
      (∀ y : Work.Stems.Cubical.IC D, ∀ j : ℕ, 0 < j → j < f →
        IsZero ((Work.Cohomology.singularChains ℤ
          (TopCat.of (Work.StemsB.fibre p (τ y)))).homology j)) →
      (∀ y : Work.Stems.Cubical.IC D,
        IsIso (TopCat.singularHomology₀ε
          (TopCat.of (Work.StemsB.fibre p (τ y))) (ModuleCat.of ℤ ℤ))) →
      (∀ i : ℕ, i < D + f →
        IsIso (HomologicalComplex.homologyMap (Work.Serre.cubePairMap D p τ) i)) ∧
      Function.Surjective
        (HomologicalComplex.homologyMap (Work.Serre.cubePairMap D p τ) (D + f)).hom := by
  intro E _ B _ p hp τ f h1 h2
  refine ⟨fun i hi => Work.Serre.cubeRelIso D E B p hp τ f h1 h2 i hi, ?_⟩
  rcases Nat.eq_zero_or_pos f with hf0 | hfpos
  · -- `f = 0`: the section of the pullback splits the pair map
    subst hf0
    have hne' : Nonempty (Work.StemsB.fibre p (τ (fun _ => 0))) :=
      Work.Serre.nonempty_of_isIso_singularHomology₀ε (h2 (fun _ => 0))
    obtain ⟨e₀⟩ := hne'
    obtain ⟨s, hs⟩ := Work.Serre.exists_section_cubePullback D p hp τ
      (⟨(e₀.1, fun _ => 0), e₀.2⟩ : Work.StemsB.Pullback p τ)
    have hcomp : HomologicalComplex.homologyMap (Work.Serre.cubeSectionMap D p τ s hs) (D + 0) ≫
        HomologicalComplex.homologyMap (Work.Serre.cubePairMap D p τ) (D + 0) = 𝟙 _ := by
      rw [← HomologicalComplex.homologyMap_comp (Work.Serre.cubeSectionMap D p τ s hs)
        (Work.Serre.cubePairMap D p τ) (D + 0), Work.Serre.cubeSectionMap_comp,
        HomologicalComplex.homologyMap_id]
    intro y
    refine ⟨(HomologicalComplex.homologyMap (Work.Serre.cubeSectionMap D p τ s hs) (D + 0)).hom
      y, ?_⟩
    have h := congrArg (fun φ => ModuleCat.Hom.hom φ y) hcomp
    simp only [ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply,
      LinearMap.id_apply] at h
    exact h
  · -- `f ≥ 1`: the target vanishes
    have hne : D + f ≠ D := by omega
    have hZ := Work.Serre.cubeBdry_isZero D (D + f) hne
    haveI : Subsingleton ((Work.Cohomology.relChains (TopCat.of (Work.Stems.Cubical.IC D))
      (Work.Serre.cubeBdryS D)).homology (D + f)) := ModuleCat.subsingleton_of_isZero hZ
    intro y
    exact ⟨0, Subsingleton.elim _ _⟩

end

end Work.Serre.SPC
