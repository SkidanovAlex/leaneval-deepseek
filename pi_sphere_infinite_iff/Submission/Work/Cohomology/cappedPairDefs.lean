import Mathlib
import Submission.Work.Cohomology.exists_relComplexMap
import Submission.Work.Cohomology.relComplexIsoDualZ
import Submission.Work.Cohomology.excisionDualZ
import Submission.Work.Cohomology.localHomology
import Submission.Work.Cohomology.cokerSmallOfU_iso_relChains_compat
import Submission.Work.Cohomology.PairSequence
import Submission.Work.Cohomology.homotopyEquiv
import Submission.Work.Milnor.Model8
import Submission.Work.Milnor.Collar
import Submission.Work.Milnor.collar_homotopyEquiv_Mk
import Submission.Work.Milnor.mk_to_vk

/-!
# Functoriality of the relative cochain pair map, and the duality identification

Supporting definitions and lemmas for `Work.Cohomology.cappedPairMapIso`:
the relative pair map `relComplexMap` is contravariantly functorial in the pair
(`relComplexMap_id`, `relComplexMap_comp`, `relComplexMap_congr`), and the relative cochain complex
is (canonically, via `relZIso`) the `ℤ`-dual of the relative chain complex (`relZIsoComplex`).
-/

set_option backward.isDefEq.respectTransparency false

namespace Work.Cohomology

open CategoryTheory AlgebraicTopology Limits

noncomputable section

variable (R : Type) [CommRing R]

/-- The value of the pair map on a relative cochain: the underlying cochain is the pullback
`dualChainMap`. -/
theorem relComplexMap_f_coe {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂) (f : X₁ ⟶ X₂)
    (h : ∀ x ∈ A₁, f x ∈ A₂) (n : ℕ) (x : relKern R X₂ A₂ n) :
    ((relComplexMap R A₁ A₂ f h).f n x).1 = ((dualChainMap R X₁ X₂ f).f n).hom x.1 := by
  rw [relComplexMap_f R A₁ A₂ f h n]
  rfl

/-- The pair map only depends on the map of spaces, not on the proof that it carries `A₁` into
`A₂`. -/
theorem relComplexMap_congr {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂) {f f' : X₁ ⟶ X₂}
    (hf : f = f') (h : ∀ x ∈ A₁, f x ∈ A₂) (h' : ∀ x ∈ A₁, f' x ∈ A₂) :
    relComplexMap R A₁ A₂ f h = relComplexMap R A₁ A₂ f' h' := by
  subst hf
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rfl

/-- **The pair map is functorial: the identity.** -/
theorem relComplexMap_id {X : TopCat} (A : Set X) (h : ∀ x ∈ A, (𝟙 X : X ⟶ X) x ∈ A) :
    relComplexMap R A A (𝟙 X) h = 𝟙 (relComplex R X A) := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [relComplexMap_f R A A (𝟙 X) h n]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp only [ModuleCat.hom_ofHom, relMapLM_coe, dualChainMap_id,
    HomologicalComplex.id_f, ModuleCat.hom_id, LinearMap.id_apply]
  rfl

/-- **The pair map is functorial: composition.**  This is what allows the identification of the
pair `(Vk(-2), Mk(-2))` with `(X, D⁸)` to be assembled from a homeomorphism of pairs and an
excision. -/
theorem relComplexMap_comp {X₀ X₁ X₂ : TopCat} (A₀ : Set X₀) (A₁ : Set X₁) (A₂ : Set X₂)
    (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (hf : ∀ x ∈ A₀, f x ∈ A₁) (hg : ∀ y ∈ A₁, g y ∈ A₂) :
    relComplexMap R A₀ A₂ (f ≫ g) (fun x hx => hg (f x) (hf x hx))
      = relComplexMap R A₁ A₂ g hg ≫ relComplexMap R A₀ A₁ f hf := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, relComplexMap_f R A₀ A₂ (f ≫ g) _ n,
    relComplexMap_f R A₁ A₂ g hg n, relComplexMap_f R A₀ A₁ f hf n]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp only [ModuleCat.hom_ofHom, ModuleCat.hom_comp, LinearMap.comp_apply, relMapLM_coe,
    dualChainMap_comp, HomologicalComplex.comp_f]
  rfl

/-- **The duality identification of the relative cochain complex with the `ℤ`-dual of the relative
chain complex**, as a chosen isomorphism: the components are `relZIso`. -/
def relZIsoComplex (X : TopCat) (A : Set X) :
    dualZ R (relChains X A) ≅ relComplex R X A :=
  HomologicalComplex.Hom.isoOfComponents (fun n => relZIso R X A n)
    (fun i j hij => by rw [← hij]; exact relZIso_comm R X A i)

/-- The components of `relZIsoComplex`. -/
@[simp] theorem relZIsoComplex_hom_f (X : TopCat) (A : Set X) (n : ℕ) :
    (relZIsoComplex R X A).hom.f n = (relZIso R X A n).hom :=
  HomologicalComplex.Hom.isoOfComponents_hom_f _ _ n

/-- The components of the inverse of `relZIsoComplex`. -/
@[simp] theorem relZIsoComplex_inv_f (X : TopCat) (A : Set X) (n : ℕ) :
    (relZIsoComplex R X A).inv.f n = (relZIso R X A n).inv :=
  HomologicalComplex.Hom.isoOfComponents_inv_f _ _ n

end

end Work.Cohomology
