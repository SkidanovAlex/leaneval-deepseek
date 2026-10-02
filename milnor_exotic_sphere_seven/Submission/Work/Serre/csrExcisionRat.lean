import Mathlib
import Submission.Work.Serre.csrDefs
import Submission.Work.StemsB.RelChainsBaseChangeRat
import Submission.Work.Cohomology.localHomology
import Submission.Work.Serre.C1Rat

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Excision for relative singular homology with rational coefficients

The rational analogue of `Work.Cohomology.excision_relChainsMap_isIso` (the integral excision
theorem of `Submission/Work/Cohomology/localHomology.lean`).

The route is flat base change `- ⊗[ℤ] ℚ`.  The comparison isomorphism
`Φ_X : (C_*(X;ℤ) ⊗[ℤ] ℚ) ≅ C_*(X;ℚ)` of `Submission/Work/SphRat/sphRatHomology.lean` is natural in
the space (`Work.StemsB.RatBC.Phi_naturality`), it is compatible with the *relative* chain complexes
(`Work.StemsB.relChainsBaseChangeRat`, reproduced here as an explicitly unfoldable isomorphism
`Work.Serre.bcRat`), and `- ⊗[ℤ] ℚ` carries quasi-isomorphisms to quasi-isomorphisms
(`Work.Serre.isIso_homologyMap_mapHomologicalComplex`).  The only new ingredient is the
*compatibility of the base change with a map of pairs*, `Work.Serre.bcRat_relChainsMapOf`: the two
ways of comparing `C_*(U,U∩A)` with `C_*(X,A)` — first base change then compose with the map of
relative chain complexes, or first take the map of pairs over `ℤ` and then base change — agree.

The proof of `bcRat_relChainsMapOf` isolates the categorical content in `cokernelMap_baseChange`,
whose proof cancels the epimorphism `cokernel.π` and uses the universal property of the cokernel
(`Work.Cohomology.cokernel_π_map`); the rest is the naturality of `Φ` at the two continuous maps
`A → B` and `X → Y`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace Work.Serre

noncomputable section

/-! ## Two elementary facts about cokernel maps -/

/-- Two consecutive `cokernel.map`s compose: `f ⟶ m ⟶ g` in the "arrow category" gives
`cokernel f ⟶ cokernel g`, and the two ways of expressing it agree. -/
theorem cokernel_map_comp_map {C : Type*} [Category C] [HasZeroMorphisms C]
    {X₀ X₁ M₀ M₁ Y₀ Y₁ : C}
    (f : X₀ ⟶ X₁) [HasCokernel f] (m : M₀ ⟶ M₁) [HasCokernel m] (g : Y₀ ⟶ Y₁) [HasCokernel g]
    (p : X₀ ⟶ M₀) (q : X₁ ⟶ M₁) (p' : M₀ ⟶ Y₀) (q' : M₁ ⟶ Y₁)
    (h₁ : f ≫ q = p ≫ m) (h₂ : m ≫ q' = p' ≫ g)
    (W : f ≫ (q ≫ q') = (p ≫ p') ≫ g) :
    cokernel.map f m p q h₁ ≫ cokernel.map m g p' q' h₂
      = cokernel.map f g (p ≫ p') (q ≫ q') W := by
  apply (cancel_epi (cokernel.π f)).1
  rw [← Category.assoc, Work.Cohomology.cokernel_π_map f m p q h₁, Category.assoc,
    Work.Cohomology.cokernel_π_map m g p' q' h₂, ← Category.assoc,
    Work.Cohomology.cokernel_π_map f g (p ≫ p') (q ≫ q') W]

/-- `cokernel.map` depends only on the two horizontal maps. -/
theorem cokernel_map_congr {C : Type*} [Category C] [HasZeroMorphisms C]
    {X Y X' Y' : C} (f : X ⟶ Y) [HasCokernel f] (f' : X' ⟶ Y') [HasCokernel f']
    {p₁ p₂ : X ⟶ X'} {q₁ q₂ : Y ⟶ Y'} (hp : p₁ = p₂) (hq : q₁ = q₂)
    (w₁ : f ≫ q₁ = p₁ ≫ f') (w₂ : f ≫ q₂ = p₂ ≫ f') :
    cokernel.map f f' p₁ q₁ w₁ = cokernel.map f f' p₂ q₂ w₂ := by
  cases hp; cases hq; rfl

/-! ## Naturality of the `ℤ → ℚ` comparison -/

/-- Naturality of `Φ` at the inclusion `A ⊆ X`. -/
theorem phi_naturality_incl (X : TopCat) (A : Set X) :
    Work.StemsB.IntRatCM.map (Work.Cohomology.inclChains X A)
        ≫ (Work.StemsB.RatBC.Phi (TopCat.toSSet.obj X)).hom
      = (Work.StemsB.RatBC.Phi (TopCat.toSSet.obj (TopCat.of ↥A))).hom
        ≫ Work.StemsB.relChainsRIncl ℚ X A :=
  (Work.StemsB.RatBC.Phi_naturality (TopCat.toSSet.map (Work.Cohomology.subtypeIncl X A))).symm

/-- Naturality of `Φ` at an arbitrary continuous map. -/
theorem phi_naturality_map (X Y : TopCat) (f : X ⟶ Y) :
    (Work.StemsB.RatBC.Phi (TopCat.toSSet.obj X)).hom ≫ Work.Cohomology.chainMap ℚ X Y f
      = Work.StemsB.IntRatCM.map (Work.Cohomology.chainMap ℤ X Y f)
        ≫ (Work.StemsB.RatBC.Phi (TopCat.toSSet.obj Y)).hom :=
  Work.StemsB.RatBC.Phi_naturality (TopCat.toSSet.map f)

/-! ## The base change of the relative chain complex, as an unfoldable isomorphism -/

/-- The base change isomorphism `C_*(X,A;ℤ) ⊗[ℤ] ℚ ≅ C_*(X,A;ℚ)` (the same construction as
`Work.StemsB.relChainsBaseChangeRat`, but as an explicit isomorphism so that its composite with
`cokernel.π` can be unfolded in the proof below). -/
noncomputable def bcRat (X : TopCat) (A : Set X) :
    Work.StemsB.IntRatCM.obj (Work.Cohomology.relChains X A) ≅ Work.StemsB.relChainsR ℚ X A := by
  haveI : PreservesFiniteLimits Work.StemsB.IntRatF :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat (by rw [RingHom.Flat]; infer_instance)
  haveI : PreservesFiniteColimits Work.StemsB.IntRatF := inferInstance
  haveI : Work.StemsB.IntRatF.PreservesHomology := inferInstance
  haveI : PreservesFiniteColimits Work.StemsB.IntRatCM := inferInstance
  haveI : PreservesFiniteLimits Work.StemsB.IntRatCM := inferInstance
  exact Limits.PreservesCokernel.iso Work.StemsB.IntRatCM (Work.Cohomology.inclChains X A) ≪≫
    Limits.cokernel.mapIso (Work.StemsB.IntRatCM.map (Work.Cohomology.inclChains X A))
      (Work.StemsB.relChainsRIncl ℚ X A)
      (Work.StemsB.RatBC.Phi (TopCat.toSSet.obj (TopCat.of ↥A)))
      (Work.StemsB.RatBC.Phi (TopCat.toSSet.obj X)) (phi_naturality_incl X A)

theorem bcRat_hom (X : TopCat) (A : Set X) :
    (bcRat X A).hom
      = (Limits.PreservesCokernel.iso Work.StemsB.IntRatCM (Work.Cohomology.inclChains X A)).hom
        ≫ cokernel.map (Work.StemsB.IntRatCM.map (Work.Cohomology.inclChains X A))
            (Work.StemsB.relChainsRIncl ℚ X A)
            (Work.StemsB.RatBC.Phi (TopCat.toSSet.obj (TopCat.of ↥A))).hom
            (Work.StemsB.RatBC.Phi (TopCat.toSSet.obj X)).hom (phi_naturality_incl X A) := by
  rw [bcRat, Iso.trans_hom, cokernel.mapIso_hom]

/-! ## The square: base change commutes with a map of pairs -/

/-- The categorical content of the compatibility of the base change with a cokernel map. -/
theorem cokernelMap_baseChange {C D : Type*} [Category C] [Category D]
    [HasZeroMorphisms C] [HasZeroMorphisms D]
    (G : C ⥤ D) [G.PreservesZeroMorphisms]
    {X₀ X₁ Y₀ Y₁ : C} (a : X₀ ⟶ X₁) [HasCokernel a] [HasCokernel (G.map a)]
    [PreservesColimit (parallelPair a 0) G]
    (a' : Y₀ ⟶ Y₁) [HasCokernel a'] [HasCokernel (G.map a')]
    [PreservesColimit (parallelPair a' 0) G]
    {M₀ M₁ N₀ N₁ : D} (b : M₀ ⟶ M₁) [HasCokernel b] (b' : N₀ ⟶ N₁) [HasCokernel b']
    (Φ₀ : G.obj X₀ ≅ M₀) (Φ₁ : G.obj X₁ ≅ M₁) (Ψ₀ : G.obj Y₀ ≅ N₀) (Ψ₁ : G.obj Y₁ ≅ N₁)
    (p : X₀ ⟶ Y₀) (q : X₁ ⟶ Y₁) (p' : M₀ ⟶ N₀) (q' : M₁ ⟶ N₁)
    (hX : G.map a ≫ Φ₁.hom = Φ₀.hom ≫ b) (hY : G.map a' ≫ Ψ₁.hom = Ψ₀.hom ≫ b')
    (hp : Φ₀.hom ≫ p' = G.map p ≫ Ψ₀.hom) (hq : Φ₁.hom ≫ q' = G.map q ≫ Ψ₁.hom)
    (wZ : a ≫ q = p ≫ a') (wQ : b ≫ q' = p' ≫ b')
    (wG : G.map a ≫ G.map q = G.map p ≫ G.map a') :
    (PreservesCokernel.iso G a).hom
        ≫ (cokernel.map (G.map a) b Φ₀.hom Φ₁.hom hX ≫ cokernel.map b b' p' q' wQ)
      = G.map (cokernel.map a a' p q wZ)
        ≫ ((PreservesCokernel.iso G a').hom ≫ cokernel.map (G.map a') b' Ψ₀.hom Ψ₁.hom hY) := by
  have hnat : (PreservesCokernel.iso G a).hom
        ≫ cokernel.map (G.map a) (G.map a') (G.map p) (G.map q) wG
      = G.map (cokernel.map a a' p q wZ) ≫ (PreservesCokernel.iso G a').hom :=
    preserves_cokernel_iso_comp_cokernel_map G a a' p q wZ
  have hcomp : cokernel.map (G.map a) b Φ₀.hom Φ₁.hom hX ≫ cokernel.map b b' p' q' wQ
      = cokernel.map (G.map a) (G.map a') (G.map p) (G.map q) wG
        ≫ cokernel.map (G.map a') b' Ψ₀.hom Ψ₁.hom hY := by
    rw [cokernel_map_comp_map (G.map a) b b' Φ₀.hom Φ₁.hom p' q' hX wQ
          (by rw [← Category.assoc, hX, Category.assoc, wQ, Category.assoc]),
        cokernel_map_comp_map (G.map a) (G.map a') b' (G.map p) (G.map q) Ψ₀.hom Ψ₁.hom wG hY
          (by rw [← Category.assoc, wG, Category.assoc, hY, Category.assoc])]
    exact cokernel_map_congr _ _ hp hq _ _
  rw [hcomp, ← Category.assoc, hnat, Category.assoc]

/-- **Base change commutes with a map of pairs.** -/
theorem bcRat_relChainsMapOf (X Y : TopCat) (A : Set X) (B : Set Y) (f : X ⟶ Y)
    (g : TopCat.of A ⟶ TopCat.of B)
    (wZ : Work.Cohomology.subtypeIncl X A ≫ f = g ≫ Work.Cohomology.subtypeIncl Y B)
    (wQ : g ≫ Work.Cohomology.subtypeIncl Y B = Work.Cohomology.subtypeIncl X A ≫ f) :
    (bcRat X A).hom ≫ Work.Serre.csrRelMapOf X Y A B f g wZ
      = Work.StemsB.IntRatCM.map (Work.Cohomology.relChainsMapOf X Y A B f g wZ)
        ≫ (bcRat Y B).hom := by
  have wZc : Work.Cohomology.inclChains X A ≫ Work.Cohomology.chainMap ℤ X Y f
      = Work.Cohomology.chainMap ℤ (TopCat.of A) (TopCat.of B) g
        ≫ Work.Cohomology.inclChains Y B := by
    simp only [Work.Cohomology.inclChains, Work.Cohomology.chainMap, ← Functor.map_comp]
    rw [wZ]
  have wQc : Work.StemsB.relChainsRIncl ℚ X A ≫ Work.Cohomology.chainMap ℚ X Y f
      = Work.Cohomology.chainMap ℚ (TopCat.of A) (TopCat.of B) g
        ≫ Work.StemsB.relChainsRIncl ℚ Y B := by
    simp only [Work.StemsB.relChainsRIncl, Work.Cohomology.chainMap, ← Functor.map_comp]
    rw [wZ]
  have wG : Work.StemsB.IntRatCM.map (Work.Cohomology.inclChains X A)
        ≫ Work.StemsB.IntRatCM.map (Work.Cohomology.chainMap ℤ X Y f)
      = Work.StemsB.IntRatCM.map (Work.Cohomology.chainMap ℤ (TopCat.of A) (TopCat.of B) g)
        ≫ Work.StemsB.IntRatCM.map (Work.Cohomology.inclChains Y B) := by
    rw [← Functor.map_comp, wZc, Functor.map_comp]
  simp only [Work.Serre.csrRelMapOf, Work.Cohomology.relChainsMapOf, bcRat_hom]
  exact cokernelMap_baseChange (G := Work.StemsB.IntRatCM)
    (a := Work.Cohomology.inclChains X A) (a' := Work.Cohomology.inclChains Y B)
    (b := Work.StemsB.relChainsRIncl ℚ X A) (b' := Work.StemsB.relChainsRIncl ℚ Y B)
    (Φ₀ := Work.StemsB.RatBC.Phi (TopCat.toSSet.obj (TopCat.of ↥A)))
    (Φ₁ := Work.StemsB.RatBC.Phi (TopCat.toSSet.obj X))
    (Ψ₀ := Work.StemsB.RatBC.Phi (TopCat.toSSet.obj (TopCat.of ↥B)))
    (Ψ₁ := Work.StemsB.RatBC.Phi (TopCat.toSSet.obj Y))
    (p := Work.Cohomology.chainMap ℤ (TopCat.of A) (TopCat.of B) g)
    (q := Work.Cohomology.chainMap ℤ X Y f)
    (p' := Work.Cohomology.chainMap ℚ (TopCat.of A) (TopCat.of B) g)
    (q' := Work.Cohomology.chainMap ℚ X Y f)
    (hX := phi_naturality_incl X A) (hY := phi_naturality_incl Y B)
    (hp := phi_naturality_map (TopCat.of A) (TopCat.of B) g) (hq := phi_naturality_map X Y f)
    wZc wQc wG

/-! ## Excision over `ℚ` -/

/-- Excision for relative singular homology with rational coefficients: if `U, A ⊆ X` are open and
`U ∪ A = X`, then the inclusion of pairs `(U, U ∩ A) → (X, A)` induces an isomorphism on relative
homology in every degree.  Rational analogue of `Work.Cohomology.excision_relChainsMap_isIso`
(which is stated over `ℤ`); the file `Submission/Work/Serre/csrDefs.lean` defines the map
`relChainsRInclPairMap`. -/
theorem csrExcisionRat (X : TopCat) (U A : Set X) (hU : IsOpen U) (hA : IsOpen A)
    (hcov : U ∪ A = Set.univ) (m : ℕ) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRInclPairMap X U A) m) := by
  -- the integral excision theorem
  have hZ : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.relChainsMap X U A) m) :=
    Work.Cohomology.excision_relChainsMap_isIso X U A hU hA hcov m
  -- base change commutes with the map of pairs
  have hsq : (bcRat (TopCat.of ↥U) {x : ↥U | (x : X) ∈ A}).hom
        ≫ Work.Serre.relChainsRInclPairMap X U A
      = Work.StemsB.IntRatCM.map (Work.Cohomology.relChainsMap X U A)
        ≫ (bcRat X A).hom := by
    rw [show Work.Serre.relChainsRInclPairMap X U A
        = Work.Serre.csrRelMapOf (TopCat.of ↥U) X {x : ↥U | (x : X) ∈ A} A
            (Work.Cohomology.subtypeIncl X U) (Work.Cohomology.inclInterA X U A)
            (by ext x; rfl) from rfl,
      show Work.Cohomology.relChainsMap X U A
        = Work.Cohomology.relChainsMapOf (TopCat.of ↥U) X {x : ↥U | (x : X) ∈ A} A
            (Work.Cohomology.subtypeIncl X U) (Work.Cohomology.inclInterA X U A)
            (by ext x; rfl) from rfl]
    exact bcRat_relChainsMapOf (TopCat.of ↥U) X {x : ↥U | (x : X) ∈ A} A
      (Work.Cohomology.subtypeIncl X U) (Work.Cohomology.inclInterA X U A)
      (by ext x; rfl) (by ext x; rfl)
  -- express the rational inclusion of pairs as the base change of the integral one
  have hψ : Work.Serre.relChainsRInclPairMap X U A
      = (bcRat (TopCat.of ↥U) {x : ↥U | (x : X) ∈ A}).inv
        ≫ Work.StemsB.IntRatCM.map (Work.Cohomology.relChainsMap X U A)
        ≫ (bcRat X A).hom := by
    rw [← hsq, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rw [hψ, HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp]
  haveI : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (bcRat (TopCat.of ↥U) {x : ↥U | (x : X) ∈ A}).inv m) := inferInstance
  haveI : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.StemsB.IntRatCM.map (Work.Cohomology.relChainsMap X U A)) m) :=
    Work.Serre.isIso_homologyMap_mapHomologicalComplex (Work.Cohomology.relChainsMap X U A) m hZ
  haveI : CategoryTheory.IsIso (HomologicalComplex.homologyMap (bcRat X A).hom m) := inferInstance
  infer_instance

end

end Work.Serre
