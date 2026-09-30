import Mathlib
import Submission.Work.StemsB.RatBaseNaturality
import Submission.Work.StemsB.RelChainsR
import Submission.Work.StemsB.SerreExact
import Submission.Work.Cohomology.localHomology
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Area SRANGE: vocabulary for the Serre exact sequence with arbitrary coefficients

This file contains only *definitions* and the easy compatibility lemmas that do not need the
base-change naturality chapter.  The mathematical statements about them live in the sibling files.

* `Work.Pi6.SRANGE.IntR R` — extension of scalars along `ℤ → R`;
* `Work.Pi6.SRANGE.baseChange R C` — the base change of a chain complex of `ℤ`-modules;
* `Work.Pi6.SRANGE.baseChangeChainsIso R X` — the comparison `C_*(X;ℤ) ⊗ R ≅ C_*(X;R)`;
* `Work.Pi6.SRANGE.relChainsRMapOf`, `Work.Pi6.SRANGE.relPairMapR` — the map of relative chain
  complexes over `R` induced by a map of pairs (the `R`-coefficient analogue of
  `Work.Cohomology.relChainsMapOf` / `Work.StemsB.relPairMap`).
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped TensorProduct

namespace Work.Pi6.SRANGE

noncomputable section

variable (R : Type) [CommRing R]

/-- Extension of scalars along `ℤ → R`, as a functor on `ℤ`-modules. -/
abbrev IntR : ModuleCat.{0} ℤ ⥤ ModuleCat.{0} R :=
  ModuleCat.extendScalars (Int.castRingHom R)

/-- `ℤ` as a `ℤ`-module (the coefficient object of the integral singular chains). -/
abbrev ZModZ : ModuleCat.{0} ℤ := ModuleCat.of ℤ ℤ

/-- `R` as an `R`-module (the coefficient object of the `R`-singular chains). -/
abbrev RMod : ModuleCat.{0} R := ModuleCat.of R R

/-- **Base change of a chain complex along `ℤ → R`.** -/
abbrev baseChange (C : ChainComplex (ModuleCat.{0} ℤ) ℕ) : ChainComplex (ModuleCat.{0} R) ℕ :=
  ((IntR R).mapHomologicalComplex (ComplexShape.down ℕ)).obj C

/-- The map of base-changed chain complexes induced by a chain map. -/
abbrev baseChangeMap {C D : ChainComplex (ModuleCat.{0} ℤ) ℕ} (f : C ⟶ D) :
    baseChange R C ⟶ baseChange R D :=
  ((IntR R).mapHomologicalComplex (ComplexShape.down ℕ)).map f

/-! ## The relative chain complex over `R` -/

/-- **The map of relative chain complexes over `R` induced by a map of pairs.**

A map `f : X ⟶ Y` and a map `g : A ⟶ B` on the subspaces, compatible in the sense that
`subtypeIncl X A ≫ f = g ≫ subtypeIncl Y B`, induce a chain map of the `R`-coefficient relative
chain complexes.  This is the `R`-coefficient analogue of `Work.Cohomology.relChainsMapOf`. -/
def relChainsRMapOf (X Y : TopCat) (A : Set X) (B : Set Y)
    (f : X ⟶ Y) (g : TopCat.of A ⟶ TopCat.of B)
    (w : Work.Cohomology.subtypeIncl X A ≫ f = g ≫ Work.Cohomology.subtypeIncl Y B) :
    Work.StemsB.relChainsR R X A ⟶ Work.StemsB.relChainsR R Y B :=
  cokernel.map (Work.StemsB.relChainsRIncl R X A) (Work.StemsB.relChainsRIncl R Y B)
    (Work.Cohomology.chainMap R (TopCat.of A) (TopCat.of B) g)
    (Work.Cohomology.chainMap R X Y f) (by
      have h1 : Work.Cohomology.chainMap R (TopCat.of A) (TopCat.of B) g
            ≫ Work.Cohomology.chainMap R (TopCat.of B) Y
              (Work.Cohomology.subtypeIncl Y B)
          = Work.Cohomology.chainMap R (TopCat.of A) Y
              (g ≫ Work.Cohomology.subtypeIncl Y B) := by
        simp only [Work.Cohomology.chainMap, Functor.map_comp]
      have h2 : Work.Cohomology.chainMap R (TopCat.of A) X
              (Work.Cohomology.subtypeIncl X A)
            ≫ Work.Cohomology.chainMap R X Y f
          = Work.Cohomology.chainMap R (TopCat.of A) Y
              (Work.Cohomology.subtypeIncl X A ≫ f) := by
        simp only [Work.Cohomology.chainMap, Functor.map_comp]
      rw [Work.StemsB.relChainsRIncl, Work.StemsB.relChainsRIncl, h2, h1, w])

/-- The compatibility of `relChainsRMapOf` with the projections to the relative chain complexes. -/
theorem cokernel_π_relChainsRMapOf (X Y : TopCat) (A : Set X) (B : Set Y)
    (f : X ⟶ Y) (g : TopCat.of A ⟶ TopCat.of B)
    (w : Work.Cohomology.subtypeIncl X A ≫ f = g ≫ Work.Cohomology.subtypeIncl Y B) :
    cokernel.π (Work.StemsB.relChainsRIncl R X A) ≫ relChainsRMapOf R X Y A B f g w
      = Work.Cohomology.chainMap R X Y f ≫ cokernel.π (Work.StemsB.relChainsRIncl R Y B) := by
  rw [relChainsRMapOf]
  exact Work.Cohomology.cokernel_π_map _ _ _ _ _

/-- **The map of relative chain complexes over `R`** `C_*(E, p⁻¹(b₀);R) → C_*(B, {b₀};R)`
induced by a map `p : E → B`: the `R`-coefficient analogue of `Work.StemsB.relPairMap`. -/
def relPairMapR {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) (b₀ : B) :
    Work.StemsB.relChainsR R (TopCat.of E) (p ⁻¹' {b₀})
      ⟶ Work.StemsB.relChainsR R (TopCat.of B) ({b₀} : Set B) :=
  relChainsRMapOf R (TopCat.of E) (TopCat.of B) (p ⁻¹' {b₀}) {b₀}
    (TopCat.ofHom p) (Work.StemsB.fibreMap p b₀) (by ext x; exact x.2)

/-- The compatibility of `relPairMapR` with the projections. -/
theorem cokernel_π_relPairMapR {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (b₀ : B) :
    cokernel.π (Work.StemsB.relChainsRIncl R (TopCat.of E) (p ⁻¹' {b₀}))
        ≫ relPairMapR R p b₀
      = Work.Cohomology.chainMap R (TopCat.of E) (TopCat.of B) (TopCat.ofHom p)
        ≫ cokernel.π (Work.StemsB.relChainsRIncl R (TopCat.of B) ({b₀} : Set B)) :=
  cokernel_π_relChainsRMapOf R _ _ _ _ _ _ _

end

end Work.Pi6.SRANGE
