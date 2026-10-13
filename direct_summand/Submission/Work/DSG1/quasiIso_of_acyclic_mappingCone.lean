import Mathlib

/-!
# A morphism whose mapping cone is acyclic is a quasi-isomorphism

For a morphism `f : K ⟶ L` of cochain complexes of `A`-modules, the standard triangle

`K --f--> L --inr--> mappingCone f --δ--> K⟦1⟧`

in the homotopy category becomes a distinguished triangle in the derived category
(`DerivedCategory.mappingCone_triangle_distinguished`).  Its long exact homology sequence is
available in Mathlib through `CochainComplex.homologyMap_exact₂_of_distTriang` and
`CochainComplex.homologyMap_exact₁_of_distTriang`:

`H^n(K) --H^n(f)--> H^n(L) --> H^n(mappingCone f) --> H^{n+1}(K) --H^{n+1}(f)--> H^{n+1}(L)`.

If `mappingCone f` is acyclic, the middle terms of this sequence vanish, so exactness
at `H^n(L)` forces `H^n(f)` to be an epimorphism while exactness at `H^{n+1}(K)` forces
`H^{n+1}(f)` to be a monomorphism.  Hence every `H^n(f)` is an isomorphism, i.e. `f` is a
quasi-isomorphism.

The only point that is not a direct application of the library is the supply of the
derived category of `ModuleCat A` (the statement carries no `HasDerivedCategory`
hypothesis): we use the canonical `HasDerivedCategory.standard` instance.
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace Work.DSG1

set_option linter.style.haveILetI false in
theorem quasiIso_of_acyclic_mappingCone {A : Type u} [CommRing A]
    {K L : CochainComplex (ModuleCat A) ℤ} (f : K ⟶ L)
    (h : (CochainComplex.mappingCone f).Acyclic) : QuasiIso f := by
  haveI : HasDerivedCategory (ModuleCat A) := HasDerivedCategory.standard _
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  -- the mapping cone triangle is distinguished in the derived category
  have hT := DerivedCategory.mappingCone_triangle_distinguished f
  -- the homology of the (acyclic) mapping cone vanishes in every degree
  have hz : ∀ m, IsZero ((CochainComplex.mappingCone f).homology m) := fun m =>
    (HomologicalComplex.exactAt_iff_isZero_homology _ m).mp (h m)
  -- exactness at `H^n(L)` makes `H^n(f)` an epimorphism
  have hepi : Epi (HomologicalComplex.homologyMap f n) := by
    have h₁ := CochainComplex.homologyMap_exact₂_of_distTriang
      (CochainComplex.mappingCone.triangle f) hT n
    have h₂ : Epi (HomologicalComplex.homologyMap
        (CochainComplex.mappingCone.triangle f).mor₁ n) :=
      (ShortComplex.exact_iff_epi _ ((hz n).eq_zero_of_tgt _)).mp h₁
    rw [CochainComplex.mappingCone.triangle_mor₁] at h₂
    exact h₂
  -- exactness at `H^{n+1}(K)` makes `H^n(f)` a monomorphism
  have hmono : Mono (HomologicalComplex.homologyMap f n) := by
    have h₁ := CochainComplex.homologyMap_exact₁_of_distTriang
      (CochainComplex.mappingCone.triangle f) hT (n - 1) n (by lia)
    have h₂ : Mono (HomologicalComplex.homologyMap
        (CochainComplex.mappingCone.triangle f).mor₁ n) :=
      (ShortComplex.exact_iff_mono _ ((hz (n - 1)).eq_zero_of_src _)).mp h₁
    rw [CochainComplex.mappingCone.triangle_mor₁] at h₂
    exact h₂
  exact isIso_of_mono_of_epi _

end Work.DSG1
