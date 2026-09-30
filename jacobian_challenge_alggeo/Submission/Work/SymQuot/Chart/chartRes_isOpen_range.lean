/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The chart restriction `chart V ⟶ chart U` has open range (area SY)

For a scheme `X` with an action of a finite group `G`, and `G`-invariant affine opens `V ≤ U`,
the induced morphism of charts `chart V ⟶ chart U` (the restriction map on rings of invariants)
identifies `chart V` with an open subscheme of `chart U`.

Here we prove only that its set-theoretic range is open (the missing `IsOpenImmersion` statement is
proved separately).  The proof does not need any ring theory: the chart map
`U ⟶ chart U = Spec Γ(X,U)^G` is a topological quotient map (it is surjective, continuous and
closed, being `Spec` of an integral ring extension composed with an isomorphism), its fibres are
exactly the `G`-orbits (`chartMap_fiber_orbit`), and `V` is invariant.  Consequently
`range (chartRes V U) = chartMap U '' V` is the image of a saturated open set under a quotient map.
-/
import Mathlib
import Submission.Work.SymQuot.Chart
import Submission.Work.SymQuot.Invariants.surjective_specMap_fixedPoints
import Submission.Work.SymQuot.Chart.chartRes_chartMap
import Submission.Work.SymQuot.Chart.chartMap_fiber_orbit

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.SymQuot.Chart

variable {G : Type*} [Group G] [Finite G] {X : AlgebraicGeometry.Scheme}

/-- For a `G`-invariant affine open `U ⊆ X`, the chart map `U ⟶ chart U = Spec Γ(X,U)^G` is
surjective: it is `Spec` of the injective inclusion `Γ(X,U)^G ↪ Γ(X,U)` (surjective on spectra,
`surjective_specMap_fixedPoints`) composed with the isomorphism `U ≅ Spec Γ(X,U)`. -/
theorem chartMap_surjective_of_affine (A : Work.SymQuot.GAction G X) {U : X.Opens}
    (hU : AlgebraicGeometry.IsAffineOpen U) (hUi : A.IsInvariantOpen U) :
    Function.Surjective ⇑(A.chartMap U hUi) := by
  rw [Work.SymQuot.GAction.chartMap]
  haveI : IsAffine U := hU
  have h1 : Function.Surjective ⇑(U.toSpecΓ) := by
    rw [← IsAffineOpen.isoSpec_hom (hU := hU)]
    exact fun y => ⟨(IsAffineOpen.isoSpec hU).inv y, by simp⟩
  have h2 : Function.Surjective ⇑(Spec.map (CommRingCat.ofHom
      (Subring.subtype (Work.SymQuot.GAction.invariants A U hUi)))) :=
    @Work.SymQuot.Invariants.surjective_specMap_fixedPoints G _ _ (Γ(X, U)) _
      (A.sectionMulSemiringAction U hUi)
  rw [show ⇑(U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
      (Subring.subtype (Work.SymQuot.GAction.invariants A U hUi)))) =
      ⇑(Spec.map (CommRingCat.ofHom
        (Subring.subtype (Work.SymQuot.GAction.invariants A U hUi)))) ∘ ⇑(U.toSpecΓ) from rfl]
  exact h2.comp h1

/-- The chart map `U ⟶ chart U` of an invariant affine open is a closed map: it is the composite
of `U ≅ Spec Γ(X,U)` (a homeomorphism) with `Spec` of the integral ring extension
`Γ(X,U)^G ↪ Γ(X,U)`. -/
theorem isClosedMap_chartMap (A : Work.SymQuot.GAction G X) {U : X.Opens}
    (hU : AlgebraicGeometry.IsAffineOpen U) (hUi : A.IsInvariantOpen U) :
    IsClosedMap ⇑(A.chartMap U hUi) := by
  letI : MulSemiringAction G Γ(X, U) := A.sectionMulSemiringAction U hUi
  haveI : IsIso U.toSpecΓ := by
    rw [← IsAffineOpen.isoSpec_hom hU]
    exact hU.isoSpec.isIso_hom
  have hcl₁ : IsClosedMap ⇑(Spec.map (CommRingCat.ofHom
      (Subring.subtype (Work.SymQuot.GAction.invariants A U hUi)))) := by
    have hcoe : ⇑(Spec.map (CommRingCat.ofHom
        (Subring.subtype (Work.SymQuot.GAction.invariants A U hUi))))
        = PrimeSpectrum.comap (Subring.subtype (Work.SymQuot.GAction.invariants A U hUi)) := by
      funext x
      exact Spec.map_apply _ x
    rw [hcoe]
    refine PrimeSpectrum.isClosedMap_comap_of_isIntegral _ ?_
    have h := Work.SymQuot.Invariants.instIsIntegralFixedPoints (G := G) (B := Γ(X, U))
    exact fun x => h.isIntegral x
  have hcl₂ : IsClosedMap ⇑(U.toSpecΓ) := by
    have hcoe2 : ⇑(U.toSpecΓ) = ⇑((U.toSpecΓ).homeomorph) :=
      funext fun x => (Scheme.Hom.homeomorph_apply _ x).symm
    rw [hcoe2]
    exact (U.toSpecΓ).homeomorph.isClosedMap
  have hcoe : ⇑(A.chartMap U hUi) = ⇑(Spec.map (CommRingCat.ofHom
      (Subring.subtype (Work.SymQuot.GAction.invariants A U hUi)))) ∘ ⇑(U.toSpecΓ) := by
    rw [Work.SymQuot.GAction.chartMap]
    rfl
  rw [hcoe]
  exact IsClosedMap.comp hcl₁ hcl₂

/-- The range of the chart restriction is the image of the open subscheme `V` under the chart map
of `U`: this is the naturality of the chart map, together with the surjectivity of the chart map
of the affine open `V`. -/
theorem range_chartRes_eq_image_homOfLE (A : Work.SymQuot.GAction G X) {V U : X.Opens}
    (h : V ≤ U) (hUi : A.IsInvariantOpen U)
    (hVa : AlgebraicGeometry.IsAffineOpen V) (hVi : A.IsInvariantOpen V) :
    Set.range ⇑(A.chartRes V U h hUi hVi) = ⇑(A.chartMap U hUi) '' Set.range ⇑(X.homOfLE h) := by
  have hsurj : Function.Surjective ⇑(A.chartMap V hVi) := chartMap_surjective_of_affine A hVa hVi
  have key : ⇑(A.chartRes V U h hUi hVi) ∘ ⇑(A.chartMap V hVi) =
      ⇑(A.chartMap U hUi) ∘ ⇑(X.homOfLE h) := by
    have hh := congrArg (fun f : V.toScheme ⟶ A.chart U hUi => ⇑f)
      (Work.SymQuot.Chart.chartRes_chartMap (A := A) h hUi hVi)
    simpa [Function.comp_def] using hh.symm
  calc Set.range ⇑(A.chartRes V U h hUi hVi)
      = Set.range (⇑(A.chartRes V U h hUi hVi) ∘ ⇑(A.chartMap V hVi)) :=
        (hsurj.range_comp _).symm
    _ = Set.range (⇑(A.chartMap U hUi) ∘ ⇑(X.homOfLE h)) := by rw [key]
    _ = ⇑(A.chartMap U hUi) '' Set.range ⇑(X.homOfLE h) := Set.range_comp _ _

/-- The points of an open subscheme `V ≤ U` are exactly the range of the inclusion
`V ⟶ U`: a point `x` of `U` lies in `V` if and only if it is in the range of `X.homOfLE`. -/
lemma mem_range_homOfLE {U V : X.Opens} (h : U ≤ V) {x : V.toScheme} :
    x ∈ Set.range ⇑(X.homOfLE h) ↔ V.ι x ∈ U := by
  rw [← Scheme.Hom.coe_opensRange (X.homOfLE h), Scheme.opensRange_homOfLE]
  exact Iff.rfl

/-- The image of `V` under the chart map of `U` is saturated for the chart map of `U`: the
preimage of the image of `V` is `V`.  This is where the finite group enters: the fibres of the
chart map are the `G`-orbits (`chartMap_fiber_orbit`) and `V` is `G`-invariant, so a point is
carried into `V` by some group element if and only if it already lies in `V`. -/
lemma chartMap_preimage_image_homOfLE (A : Work.SymQuot.GAction G X) {V U : X.Opens}
    (h : V ≤ U) (hU : AlgebraicGeometry.IsAffineOpen U) (hUi : A.IsInvariantOpen U)
    (hVi : A.IsInvariantOpen V) :
    ⇑(A.chartMap U hUi) ⁻¹' (⇑(A.chartMap U hUi) '' Set.range ⇑(X.homOfLE h)) =
      Set.range ⇑(X.homOfLE h) := by
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    have hy' : U.ι y ∈ V := (mem_range_homOfLE h).mp hy
    obtain ⟨g, hg⟩ := Work.SymQuot.Chart.chartMap_fiber_orbit A hU hUi
      (x := x) (y := y) hxy.symm
    rw [mem_range_homOfLE h, ← hg]
    exact (hVi.mem_iff g (U.ι y)).mpr hy'
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem chartRes_isOpen_range {G : Type*} [Group G] [Finite G] {X : AlgebraicGeometry.Scheme}
    (A : Work.SymQuot.GAction G X) {V U : X.Opens} (hVU : V ≤ U)
    (hU : AlgebraicGeometry.IsAffineOpen U) (hV : AlgebraicGeometry.IsAffineOpen V)
    (hUi : A.IsInvariantOpen U) (hVi : A.IsInvariantOpen V) :
    IsOpen (Set.range ⇑(Work.SymQuot.GAction.chartRes A V U hVU hUi hVi)) := by
  rw [range_chartRes_eq_image_homOfLE A hVU hUi hV hVi]
  have hquot : Topology.IsQuotientMap ⇑(A.chartMap U hUi) :=
    IsClosedMap.isQuotientMap (isClosedMap_chartMap A hU hUi)
      (Scheme.Hom.continuous _) (chartMap_surjective_of_affine A hU hUi)
  rw [← hquot.isCoinducing.isOpen_preimage]
  rw [chartMap_preimage_image_homOfLE A hVU hU hUi hVi, ← Scheme.Hom.coe_opensRange (X.homOfLE hVU)]
  exact (X.homOfLE hVU).opensRange.isOpen

end Work.SymQuot.Chart
