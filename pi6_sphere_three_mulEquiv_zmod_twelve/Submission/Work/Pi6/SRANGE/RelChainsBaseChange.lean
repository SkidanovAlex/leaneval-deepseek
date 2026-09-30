import Mathlib
import Submission.Work.Pi6.SRANGE.Defs
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Base change of the relative singular chain complex, `ℤ → R`

`Work.Pi6.SRANGE.BaseChange` supplies, for every commutative ring `R`, a **natural** isomorphism
`e X : C_*(X;ℤ) ⊗[ℤ] R ≅ C_*(X;R)` of the simplicial chain complexes.  This file transports that
base change to the *relative* chain complexes of a pair: `C_*(X,A;ℤ)` is the cokernel of the
inclusion `C_*(A;ℤ) ⟶ C_*(X;ℤ)`, base change is right exact, hence carries that cokernel to
`cokernel (C_*(A;R) ⟶ C_*(X;R)) = C_*(X,A;R)`, and the resulting isomorphism is natural with
respect to the maps of relative chain complexes induced by a map of pairs
(`Work.StemsB.relPairMap`, `Work.Pi6.SRANGE.relPairMapR`).

The two ingredients of the construction are

* `PreservesCokernel.iso` — the base change functor `- ⊗[ℤ] R` preserves cokernels (it is a left
  adjoint), giving `baseChange R (cokernel f) ≅ cokernel (baseChangeMap R f)`;
* `cokernel.mapIso` — an isomorphism of cokernels induced by a commuting square, which here
  identifies `cokernel (baseChangeMap R f)` with `cokernel (f ⊗ R)` using the naturality of `e`.

Naturality is reduced to the two identities
`cokernel.π f ≫ cokernel.map f g p q w = q ≫ cokernel.π g` and the coherence
`e X ≫ (f ⊗ R) = (baseChangeMap R f) ≫ e Y`.
-/

set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

namespace Work.Pi6.SRANGE

noncomputable section

variable (R : Type) [CommRing R]

/-- The base change functor `- ⊗[ℤ] R` on chain complexes of `ℤ`-modules. -/
abbrev bcF : ChainComplex (ModuleCat.{0} ℤ) ℕ ⥤ ChainComplex (ModuleCat.{0} R) ℕ :=
  (IntR R).mapHomologicalComplex (ComplexShape.down ℕ)

/-- Base change of a composite is the composite of the base changes. -/
lemma bcMap_comp {A B C : ChainComplex (ModuleCat.{0} ℤ) ℕ} (f : A ⟶ B) (g : B ⟶ C) :
    baseChangeMap R f ≫ baseChangeMap R g = baseChangeMap R (f ≫ g) :=
  (Functor.map_comp (self := bcF R) f g).symm

end

/-- The compatibility at the level of `ℤ`-coefficient chains of a commuting square of simplicial
sets. -/
theorem wZ {X0 XA XE XB : SSet.{0}} (σE : XA ⟶ XE) (σB : X0 ⟶ XB) (a : XA ⟶ X0) (x : XE ⟶ XB)
    (w : σE ≫ x = a ≫ σB) :
    SSet.chainComplexMap σE ZModZ ≫ SSet.chainComplexMap x ZModZ
      = SSet.chainComplexMap a ZModZ ≫ SSet.chainComplexMap σB ZModZ := by
  rw [← Functor.map_comp, ← Functor.map_comp, w]

/-- The compatibility at the level of `R`-coefficient chains of a commuting square of simplicial
sets. -/
theorem wR {R : Type} [CommRing R] {X0 XA XE XB : SSet.{0}} (σE : XA ⟶ XE) (σB : X0 ⟶ XB)
    (a : XA ⟶ X0) (x : XE ⟶ XB) (w : σE ≫ x = a ≫ σB) :
    SSet.chainComplexMap σE (RMod R) ≫ SSet.chainComplexMap x (RMod R)
      = SSet.chainComplexMap a (RMod R) ≫ SSet.chainComplexMap σB (RMod R) := by
  rw [← Functor.map_comp, ← Functor.map_comp, w]

noncomputable section

variable (R : Type) [CommRing R]
variable (e : ∀ X : SSet.{0}, baseChange R (SSet.chainComplex X ZModZ) ≅ SSet.chainComplex X (RMod R))
variable (he : ∀ (X Y : SSet.{0}) (σ : X ⟶ Y),
    (e X).hom ≫ SSet.chainComplexMap σ (RMod R)
      = baseChangeMap R (SSet.chainComplexMap σ ZModZ) ≫ (e Y).hom)

/-- **Base change of the cokernel of the chain map of a morphism of simplicial sets.**  The
cokernel of the inclusion over `R` is canonically identified with the base change of the cokernel
of the inclusion over `ℤ`, using the naturality of the comparison `e`. -/
def spanIso {X Y : SSet.{0}} (σ : X ⟶ Y) :
    (bcF R).obj (cokernel (SSet.chainComplexMap σ ZModZ))
      ≅ cokernel (SSet.chainComplexMap σ (RMod R)) :=
  PreservesCokernel.iso (bcF R) (SSet.chainComplexMap σ ZModZ) ≪≫
    cokernel.mapIso (baseChangeMap R (SSet.chainComplexMap σ ZModZ))
      (SSet.chainComplexMap σ (RMod R)) (e X) (e Y) ((he X Y σ).symm)

/-- The composite of the projection to the cokernel with `spanIso` is the projection to the
cokernel over `R`, composed with the coefficient comparison. -/
lemma key_π {X Y : SSet.{0}} (σ : X ⟶ Y) :
    baseChangeMap R (cokernel.π (SSet.chainComplexMap σ ZModZ)) ≫ (spanIso R e he σ).hom
      = (e Y).hom ≫ cokernel.π (SSet.chainComplexMap σ (RMod R)) := by
  rw [spanIso, Iso.trans_hom, cokernel.mapIso_hom, ← Category.assoc,
    PreservesCokernel.π_iso_hom]
  simp only [cokernel.map, cokernel.π_desc]

/-- `baseChangeMap R (cokernel.π f)` is an epimorphism (base change preserves the cokernel
projection, which is an epimorphism). -/
lemma epi_cokerπ {X Y : SSet.{0}} (σ : X ⟶ Y) :
    Epi (baseChangeMap R (cokernel.π (SSet.chainComplexMap σ ZModZ))) := by
  have h : baseChangeMap R (cokernel.π (SSet.chainComplexMap σ ZModZ))
      = cokernel.π (baseChangeMap R (SSet.chainComplexMap σ ZModZ))
        ≫ (PreservesCokernel.iso (bcF R) (SSet.chainComplexMap σ ZModZ)).inv := by
    rw [← PreservesCokernel.π_iso_hom (bcF R) (SSet.chainComplexMap σ ZModZ)]
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [h]
  infer_instance

/-- **Naturality of `spanIso`** with respect to a morphism of spans (= a square of simplicial
sets). -/
theorem spanIso_naturality {X0 XA XE XB : SSet.{0}}
    (σE : XA ⟶ XE) (σB : X0 ⟶ XB) (a : XA ⟶ X0) (x : XE ⟶ XB)
    (w : σE ≫ x = a ≫ σB) :
    baseChangeMap R (cokernel.map (SSet.chainComplexMap σE ZModZ)
        (SSet.chainComplexMap σB ZModZ) (SSet.chainComplexMap a ZModZ)
        (SSet.chainComplexMap x ZModZ) (wZ σE σB a x w))
      ≫ (spanIso R e he σB).hom
    = (spanIso R e he σE).hom
      ≫ cokernel.map (SSet.chainComplexMap σE (RMod R)) (SSet.chainComplexMap σB (RMod R))
          (SSet.chainComplexMap a (RMod R)) (SSet.chainComplexMap x (RMod R)) (wR σE σB a x w) := by
  have hstep : cokernel.π (SSet.chainComplexMap σE ZModZ)
      ≫ cokernel.map (SSet.chainComplexMap σE ZModZ) (SSet.chainComplexMap σB ZModZ)
          (SSet.chainComplexMap a ZModZ) (SSet.chainComplexMap x ZModZ) (wZ σE σB a x w)
      = SSet.chainComplexMap x ZModZ ≫ cokernel.π (SSet.chainComplexMap σB ZModZ) := by
    simp only [cokernel.map, cokernel.π_desc]
  have hstepR : cokernel.π (SSet.chainComplexMap σE (RMod R))
      ≫ cokernel.map (SSet.chainComplexMap σE (RMod R)) (SSet.chainComplexMap σB (RMod R))
          (SSet.chainComplexMap a (RMod R)) (SSet.chainComplexMap x (RMod R)) (wR σE σB a x w)
      = SSet.chainComplexMap x (RMod R) ≫ cokernel.π (SSet.chainComplexMap σB (RMod R)) := by
    simp only [cokernel.map, cokernel.π_desc]
  haveI := epi_cokerπ R σE
  have hL : baseChangeMap R (cokernel.π (SSet.chainComplexMap σE ZModZ))
        ≫ (baseChangeMap R (cokernel.map (SSet.chainComplexMap σE ZModZ)
              (SSet.chainComplexMap σB ZModZ) (SSet.chainComplexMap a ZModZ)
              (SSet.chainComplexMap x ZModZ) (wZ σE σB a x w))
            ≫ (spanIso R e he σB).hom)
      = (e XE).hom ≫ SSet.chainComplexMap x (RMod R)
          ≫ cokernel.π (SSet.chainComplexMap σB (RMod R)) := by
    conv_lhs => rw [← Category.assoc, bcMap_comp, hstep, ← bcMap_comp, Category.assoc,
      key_π, ← Category.assoc, ← he XE XB x, Category.assoc]
  have hR : baseChangeMap R (cokernel.π (SSet.chainComplexMap σE ZModZ))
        ≫ ((spanIso R e he σE).hom
            ≫ cokernel.map (SSet.chainComplexMap σE (RMod R)) (SSet.chainComplexMap σB (RMod R))
                (SSet.chainComplexMap a (RMod R)) (SSet.chainComplexMap x (RMod R))
                (wR σE σB a x w))
      = (e XE).hom ≫ SSet.chainComplexMap x (RMod R)
          ≫ cokernel.π (SSet.chainComplexMap σB (RMod R)) := by
    conv_lhs => rw [← Category.assoc, key_π, Category.assoc, hstepR]
  rw [← cancel_epi (baseChangeMap R (cokernel.π (SSet.chainComplexMap σE ZModZ))), hL, hR]

end

end Work.Pi6.SRANGE

namespace Work.Pi6.SRANGE

theorem RelChainsBaseChange (R : Type) [CommRing R] (e : forall X : SSet.{0}, Work.Pi6.SRANGE.baseChange R (SSet.chainComplex X Work.Pi6.SRANGE.ZModZ) ≅ SSet.chainComplex X (Work.Pi6.SRANGE.RMod R)) (he : forall (X Y : SSet.{0}) (sigma : X ⟶ Y), CategoryTheory.CategoryStruct.comp (e X).hom (SSet.chainComplexMap sigma (Work.Pi6.SRANGE.RMod R)) = CategoryTheory.CategoryStruct.comp (Work.Pi6.SRANGE.baseChangeMap R (SSet.chainComplexMap sigma Work.Pi6.SRANGE.ZModZ)) (e Y).hom) : ∃ f : (forall (X : TopCat) (A : Set X), Work.Pi6.SRANGE.baseChange R (Work.Cohomology.relChains X A) ≅ Work.StemsB.relChainsR R X A), (forall (E B : Type) [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) (b0 : B), CategoryTheory.CategoryStruct.comp (Work.Pi6.SRANGE.baseChangeMap R (Work.StemsB.relPairMap p b0)) (f (TopCat.of B) {b0}).hom = CategoryTheory.CategoryStruct.comp (f (TopCat.of E) (p ⁻¹' {b0})).hom (Work.Pi6.SRANGE.relPairMapR R p b0)) := by
  refine ⟨fun X A => spanIso R e he (TopCat.toSSet.map (Work.Cohomology.subtypeIncl X A)), ?_⟩
  intro E B _ _ p b0
  exact spanIso_naturality R e he
    (TopCat.toSSet.map (Work.Cohomology.subtypeIncl (TopCat.of E) (p ⁻¹' {b0})))
    (TopCat.toSSet.map (Work.Cohomology.subtypeIncl (TopCat.of B) ({b0} : Set B)))
    (TopCat.toSSet.map (Work.StemsB.fibreMap p b0))
    (TopCat.toSSet.map (TopCat.ofHom p))
    (by
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
      ext x
      exact x.2)

end Work.Pi6.SRANGE
