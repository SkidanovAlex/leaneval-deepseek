import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CY3Stab.Prod

open CategoryTheory AlgebraicGeometry

/-- Two morphisms out of the spectrum of a local ring which have the same composite with
`Spec K → Spec A` (for an injective map `A → K` into a field) and the same value at the closed
point are equal.

Proof route: first prove that for a local ring `A`, any open `U` of `Spec A` (i.e. of
`PrimeSpectrum A`) containing the closed point is `⊤` — an open is a union of basic opens
`PrimeSpectrum.basicOpen f`, and `basicOpen f ∋ closedPoint ↔ f ∉ IsLocalRing.maximalIdeal A ↔
IsUnit f` (`IsLocalRing.notMem_maximalIdeal`) so `basicOpen f = ⊤`.
Let `q := f (IsLocalRing.closedPoint A)`; pick an affine open `U : Y.Opens` with `q ∈ U`
(`Y.isBasis_affineOpens.exists_subset_of_mem_open`). Then `f ⁻¹ᵁ U = ⊤` and `g ⁻¹ᵁ U = ⊤`, so both
factor through `U.ι : U.toScheme ⟶ Y` (`IsOpenImmersion.lift`). Composing with the affine iso
`hU.isoSpec : U.toScheme ≅ Spec Γ(Y,U)` gives `f'', g'' : Spec (CommRingCat.of A) ⟶
Spec Γ(Y,U)`; the corresponding ring maps `φ ψ : Γ(Y,U) → A` satisfy
`φ ≫ algebraMap A K = ψ ≫ algebraMap A K` (from `h₁`, using that `Spec.map (algebraMap A K)`
composed with the factorisation is the same on both sides) and `hK` gives `φ = ψ`, so `f = g`. -/
theorem eq_of_specMap_algebraMap_eq_of_apply_closedPoint_eq {A : Type} [CommRing A] [IsLocalRing A]
    {K : Type} [Field K] [Algebra A K]
    (hK : Function.Injective (algebraMap A K))
    {Y : AlgebraicGeometry.Scheme.{0}}
    (f g : AlgebraicGeometry.Spec (CommRingCat.of A) ⟶ Y)
    (h₁ : CategoryTheory.CategoryStruct.comp
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap A K))) f =
      CategoryTheory.CategoryStruct.comp
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap A K))) g)
    (h₂ : f (IsLocalRing.closedPoint A) = g (IsLocalRing.closedPoint A)) : f = g := by
  -- An affine open neighbourhood of `q = f (closedPoint A) = g (closedPoint A)`.
  obtain ⟨W, hWaff, hqW, -⟩ := AlgebraicGeometry.exists_isAffineOpen_mem_and_subset
    (U := ⊤) (x := f (IsLocalRing.closedPoint A)) (by trivial)
  -- The closed point lies in every open neighbourhood in `Spec A`, so `f` and `g` land in `W`.
  have hfW : f ⁻¹ᵁ W = ⊤ := (IsLocalRing.closedPoint_mem_iff (f ⁻¹ᵁ W)).mp hqW
  have hqW' : g (IsLocalRing.closedPoint A) ∈ W := by
    rw [show g (IsLocalRing.closedPoint A) = f (IsLocalRing.closedPoint A) from h₂.symm]
    exact hqW
  have hgW : g ⁻¹ᵁ W = ⊤ := (IsLocalRing.closedPoint_mem_iff (g ⁻¹ᵁ W)).mp hqW'
  have hfr : Set.range ⇑f ⊆ Set.range ⇑W.ι := by
    rw [Scheme.Opens.range_ι]
    rintro - ⟨x, rfl⟩
    have : x ∈ f ⁻¹ᵁ W := by rw [hfW]; trivial
    exact this
  have hgr : Set.range ⇑g ⊆ Set.range ⇑W.ι := by
    rw [Scheme.Opens.range_ι]
    rintro - ⟨x, rfl⟩
    have : x ∈ g ⁻¹ᵁ W := by rw [hgW]; trivial
    exact this
  -- Both morphisms factor through the open immersion `W.ι`.
  let f' := IsOpenImmersion.lift W.ι f hfr
  let g' := IsOpenImmersion.lift W.ι g hgr
  have hf'_fac : f' ≫ W.ι = f := IsOpenImmersion.lift_fac W.ι f hfr
  have hg'_fac : g' ≫ W.ι = g := IsOpenImmersion.lift_fac W.ι g hgr
  have h₁' : Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ f' =
      Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ g' := by
    rw [← cancel_mono W.ι]
    rw [Category.assoc, Category.assoc, hf'_fac, hg'_fac, h₁]
  -- Transport along the affine iso `W ≅ Spec Γ(Y, W)`.
  let F : Spec (CommRingCat.of A) ⟶ Spec Γ(Y, W) := f' ≫ hWaff.isoSpec.hom
  let G : Spec (CommRingCat.of A) ⟶ Spec Γ(Y, W) := g' ≫ hWaff.isoSpec.hom
  have hFG : Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ F =
      Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ G := by
    dsimp only [F, G]
    rw [← Category.assoc, ← Category.assoc, h₁']
  -- Compare the corresponding ring maps `Γ(Y, W) → A` after pushing forward to `K`.
  have hpre : Spec.preimage F ≫ CommRingCat.ofHom (algebraMap A K) =
      Spec.preimage G ≫ CommRingCat.ofHom (algebraMap A K) := by
    have h := congrArg Spec.preimage hFG
    simpa using h
  have hpre' : Spec.preimage F = Spec.preimage G := by
    apply CommRingCat.hom_ext
    ext x
    apply hK
    have h2 := congrArg
      (fun (u : Γ(Y, W) ⟶ CommRingCat.of K) => (ConcreteCategory.hom u) x) hpre
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at h2
    exact h2
  have hFG' : F = G := by
    rw [← Spec.map_preimage F, ← Spec.map_preimage G, hpre']
  have hf'g' : f' = g' := by
    have h := hFG'
    dsimp only [F, G] at h
    exact (cancel_mono hWaff.isoSpec.hom).mp h
  rw [← hf'_fac, ← hg'_fac, hf'g']

end Work.CY3Stab.Prod
