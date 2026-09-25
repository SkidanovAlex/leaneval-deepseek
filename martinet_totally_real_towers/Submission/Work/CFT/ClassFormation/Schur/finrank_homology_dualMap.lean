import Mathlib
import Submission.Work.CFT.ClassFormation.Schur.DualityDefs

/-!
# The `k`-dimension of the homology of a complex and of its dual

Over a field `k`, dualization is exact, so the dual of the homology of a complex
`A --f--> B --g--> C` (with `g ∘ f = 0`) is the homology of the dual complex
`C* --g*--> B* --f*--> A*`.  Equivalently, in finite dimension the two homologies have the
same dimension.  This file proves that equality by the elementary dimension count

`dim ker g - dim im f = dim B - rank g - rank f`,

together with `dim B* = dim B` (`Subspace.dual_finrank_eq`) and
`rank f* = rank f` (`LinearMap.finrank_range_dualMap_eq_finrank_range`).

The first ingredient is `finrank_homology_add_ranks`, which identifies the `k`-dimension of the
homology of a short complex of `k`-modules as
`dim X₂ - rank f - rank g` (in additive form), via the concrete description
`ShortComplex.moduleCatHomologyIso` of the homology as
`ker g ⧸ range (S.moduleCatToCycles)`.
-/

namespace Work.CFT.ClassFormation.Schur

open CategoryTheory

set_option linter.style.haveILetI false

universe u v w

/-- The range of a `codRestrict` has the same dimension as the range of the original map. -/
theorem finrank_range_codRestrict {k : Type u} [Field k] {A : Type v} {B : Type w}
    [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
    (f : A →ₗ[k] B) (p : Submodule k B) (h : ∀ x, f x ∈ p) :
    Module.finrank k (LinearMap.range (f.codRestrict p h)) = Module.finrank k (LinearMap.range f) := by
  have hle : LinearMap.range f ≤ p := by rintro _ ⟨x, rfl⟩; exact h x
  have hmap : (LinearMap.range (f.codRestrict p h)).map p.subtype = LinearMap.range f := by
    rw [LinearMap.range_codRestrict, Submodule.map_comap_subtype, inf_eq_right.mpr hle]
  rw [← hmap]
  exact LinearEquiv.finrank_eq
    (Submodule.equivMapOfInjective p.subtype p.injective_subtype (LinearMap.range (f.codRestrict p h)))

/-- For a short complex `S` of `k`-modules with finite dimensional middle term,
`dim H(S) + dim im(S.f) + dim im(S.g) = dim S.X₂`. -/
theorem finrank_homology_add_ranks {k : Type u} [Field k]
    (S : CategoryTheory.ShortComplex (ModuleCat.{v} k)) [FiniteDimensional k ↥S.X₂] :
    Module.finrank k ↥S.homology + Module.finrank k (LinearMap.range S.f.hom)
      + Module.finrank k (LinearMap.range S.g.hom) = Module.finrank k ↥S.X₂ := by
  haveI : FiniteDimensional k ↥(LinearMap.ker S.g.hom) :=
    FiniteDimensional.of_injective (LinearMap.ker S.g.hom).subtype
      (LinearMap.ker S.g.hom).injective_subtype
  have hH : Module.finrank k ↥S.homology =
      Module.finrank k (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) :=
    LinearEquiv.finrank_eq (CategoryTheory.Iso.toLinearEquiv S.moduleCatHomologyIso)
  have hc : Module.finrank k (LinearMap.range S.moduleCatToCycles) =
      Module.finrank k (LinearMap.range S.f.hom) :=
    finrank_range_codRestrict S.f.hom (LinearMap.ker S.g.hom) S.moduleCat_zero_apply
  rw [hH, ← hc, Submodule.finrank_quotient_add_finrank,
    add_comm (Module.finrank k (LinearMap.ker S.g.hom)),
    LinearMap.finrank_range_add_finrank_ker]

/-- For linear maps `f : A → B`, `g : B → C` with `g ∘ f = 0`, all spaces finite dimensional,
`dim H + dim im f + dim im g = dim B` where `H` is the homology of the two-term complex. -/
theorem finrank_homology_moduleCatMk {k : Type u} [Field k] {A B C : Type v}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module k A] [Module k B] [Module k C] [FiniteDimensional k B]
    (f : A →ₗ[k] B) (g : B →ₗ[k] C) (hfg : g.comp f = 0) :
    Module.finrank k ↥(CategoryTheory.ShortComplex.homology
        (CategoryTheory.ShortComplex.moduleCatMk f g hfg))
      + Module.finrank k (LinearMap.range f) + Module.finrank k (LinearMap.range g)
      = Module.finrank k B := by
  haveI : FiniteDimensional k ↥(CategoryTheory.ShortComplex.moduleCatMk f g hfg).X₂ :=
    (inferInstance : FiniteDimensional k B)
  have h := finrank_homology_add_ranks (k := k)
    (S := CategoryTheory.ShortComplex.moduleCatMk f g hfg)
  have hf : (CategoryTheory.ShortComplex.moduleCatMk f g hfg).f.hom = f := rfl
  have hg : (CategoryTheory.ShortComplex.moduleCatMk f g hfg).g.hom = g := rfl
  rw [hf, hg] at h
  exact h

/-- **Duality of the homology of a two-term complex over a field.**  For linear maps
`f : A →ₗ[k] B`, `g : B →ₗ[k] C` over a field `k` with `g ∘ f = 0` and finite dimensional
`A`, `B`, `C`, the homology of `A --f--> B --g--> C` and the homology of its dual
`C* --g*--> B* --f*--> A*` have the same `k`-dimension. -/
theorem finrank_homology_dualMap {k : Type} [Field k]
    {A B C : Type} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module k A] [Module k B] [Module k C]
    [FiniteDimensional k A] [FiniteDimensional k B] [FiniteDimensional k C]
    (f : A →ₗ[k] B) (g : B →ₗ[k] C) (hfg : g.comp f = 0) :
    Module.finrank k ↥(CategoryTheory.ShortComplex.homology
        (CategoryTheory.ShortComplex.moduleCatMk f g hfg)) =
      Module.finrank k ↥(CategoryTheory.ShortComplex.homology
        (CategoryTheory.ShortComplex.moduleCatMk g.dualMap f.dualMap
          (dualMap_comp_dualMap_eq_zero f g hfg))) := by
  have h1 := finrank_homology_moduleCatMk f g hfg
  have h2 := finrank_homology_moduleCatMk (k := k) g.dualMap f.dualMap
    (dualMap_comp_dualMap_eq_zero f g hfg)
  rw [LinearMap.finrank_range_dualMap_eq_finrank_range g,
    LinearMap.finrank_range_dualMap_eq_finrank_range f, Subspace.dual_finrank_eq] at h2
  omega

end Work.CFT.ClassFormation.Schur
