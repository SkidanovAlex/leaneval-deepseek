import Mathlib
import Submission.Work.DSM5c.Lp.PiHelpers

/-!
# Products of surjective maps of `W`-modules are surjective

If `p i : Z i ⟶ Z' i` is a family of surjective morphisms of `W`-modules, then the induced map
`∏ᶜ Z ⟶ ∏ᶜ Z'` on the categorical products is surjective on underlying sets.

The proof identifies both categorical products with the concrete products `∀ i, Z i` and
`∀ i, Z' i` through `ModuleCat.piIsoPi`, produces a termwise preimage, and closes with the
compatibility of `Pi.map` with the projections `Pi.π` (`Pi.map_π`).
-/

namespace Work.DSM5c.Lp

open CategoryTheory Limits

/-- The product of a family of surjective morphisms of `W`-modules is surjective. -/
theorem surjective_Pi_map {W : Type*} [CommRing W] {ι : Type*}
    (Z Z' : ι → ModuleCat W) (p : ∀ i, Z i ⟶ Z' i)
    (h : ∀ i, Function.Surjective (p i).hom) :
    Function.Surjective ((CategoryTheory.Limits.Pi.map p).hom) := by
  intro y
  -- A termwise preimage of `y`, read through the concrete product `∀ i, Z' i`.
  choose x hx using fun i => h i ((ModuleCat.piIsoPi Z').hom y i)
  -- The element of `∏ᶜ Z` whose `i`-th projection is `x i`.
  refine ⟨(ModuleCat.piIsoPi Z).inv (fun i => x i), ?_⟩
  -- `Pi.map p` on the `i`-th projection.
  have hπ : ∀ i (w : ↥(∏ᶜ Z)),
      (CategoryTheory.Limits.Pi.π Z' i).hom ((CategoryTheory.Limits.Pi.map p).hom w) =
      (p i).hom ((CategoryTheory.Limits.Pi.π Z i).hom w) := by
    intro i w
    have h1 := congrArg ModuleCat.Hom.hom (CategoryTheory.Limits.Pi.map_π p i)
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at h1
    simpa only [LinearMap.comp_apply] using LinearMap.congr_fun h1 w
  -- The `i`-th coordinate of `(piIsoPi Z').hom z` is the `i`-th projection of `z`.
  have H1 : ∀ i (z : ↥(∏ᶜ Z')), (ModuleCat.piIsoPi Z').hom z i =
      (CategoryTheory.Limits.Pi.π Z' i).hom z := by
    intro i z
    simpa using ModuleCat.piIsoPi_hom_ker_subtype_apply Z' i z
  -- The `i`-th projection of `(piIsoPi Z).inv z` is `z i`.
  have H2 : ∀ i (z : (j : ι) → ↥(Z j)),
      (CategoryTheory.Limits.Pi.π Z i).hom ((ModuleCat.piIsoPi Z).inv z) = z i := by
    intro i z
    simpa using ModuleCat.piIsoPi_inv_kernel_ι_apply Z i z
  -- `(piIsoPi Z').hom` is injective, being an isomorphism.
  have hinj : Function.Injective (ModuleCat.piIsoPi Z').hom.hom := by
    have hb := CategoryTheory.ConcreteCategory.bijective_of_isIso (ModuleCat.piIsoPi Z').hom
    exact hb.injective
  apply hinj
  funext i
  rw [H1 i, hπ i, H2 i]
  rw [hx i]

end Work.DSM5c.Lp
