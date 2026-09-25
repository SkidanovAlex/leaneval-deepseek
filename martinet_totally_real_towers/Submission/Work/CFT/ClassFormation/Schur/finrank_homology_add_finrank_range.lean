import Mathlib
import Submission.Work.CFT.ClassFormation.Schur.DualityDefs

namespace Work.CFT.ClassFormation.Schur

theorem finrank_homology_add_finrank_range {k : Type} [Field k]
    {X₁ X₂ X₃ : Type} [AddCommGroup X₁] [Module k X₁] [AddCommGroup X₂] [Module k X₂]
    [AddCommGroup X₃] [Module k X₃]
    [Module.Finite k X₁] [Module.Finite k X₂]
    (f : X₁ →ₗ[k] X₂) (g : X₂ →ₗ[k] X₃) (hfg : g.comp f = 0) :
    Module.finrank k ↥(CategoryTheory.ShortComplex.homology
        (CategoryTheory.ShortComplex.moduleCatMk f g hfg)) +
      Module.finrank k ↥(LinearMap.range f) = Module.finrank k ↥(LinearMap.ker g) := by
  have hh : ∀ x, f x ∈ LinearMap.ker g := fun x => LinearMap.ext_iff.mp hfg x
  -- The homology of the complex `X₁ → X₂ → X₃` is `ker g ⧸ range (f codRestricted to ker g)`.
  have e : (CategoryTheory.ShortComplex.moduleCatMk f g hfg).homology ≅
      ModuleCat.of k (↥(LinearMap.ker g) ⧸ (LinearMap.range
        (f.codRestrict (LinearMap.ker g) hh))) :=
    CategoryTheory.ShortComplex.moduleCatHomologyIso _
  have h1 : Module.finrank k
        ↥((CategoryTheory.ShortComplex.moduleCatMk f g hfg).homology) =
      Module.finrank k (↥(LinearMap.ker g) ⧸ LinearMap.range
        (f.codRestrict (LinearMap.ker g) hh)) :=
    LinearEquiv.finrank_eq e.toLinearEquiv
  -- Rank-nullity for the submodule `range (f codRestricted to ker g)` of `ker g`.
  have h2 : Module.finrank k (↥(LinearMap.ker g) ⧸ LinearMap.range
        (f.codRestrict (LinearMap.ker g) hh)) +
      Module.finrank k ↥(LinearMap.range (f.codRestrict (LinearMap.ker g) hh)) =
      Module.finrank k ↥(LinearMap.ker g) :=
    Submodule.finrank_quotient_add_finrank _
  -- The codomain-restricted copy of `range f` inside `ker g` has the same dimension:
  -- the subtype of `ker g` maps it bijectively onto `range f`.
  have hkerle : LinearMap.range f ≤ LinearMap.ker g := LinearMap.range_le_ker_iff.mpr hfg
  have hφr : LinearMap.range ((LinearMap.ker g).subtype.domRestrict
        (LinearMap.range (f.codRestrict (LinearMap.ker g) hh))) = LinearMap.range f := by
    rw [LinearMap.range_domRestrict, LinearMap.range_codRestrict, Submodule.map_comap_subtype,
      inf_eq_right.mpr hkerle]
  have hφinj : Function.Injective ((LinearMap.ker g).subtype.domRestrict
      (LinearMap.range (f.codRestrict (LinearMap.ker g) hh))) := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact h
  have h3 : Module.finrank k ↥(LinearMap.range (f.codRestrict (LinearMap.ker g) hh)) =
      Module.finrank k ↥(LinearMap.range f) := by
    rw [← hφr]
    exact LinearEquiv.finrank_eq (LinearEquiv.ofInjective _ hφinj)
  rw [h1, ← h3]
  exact h2

end Work.CFT.ClassFormation.Schur
