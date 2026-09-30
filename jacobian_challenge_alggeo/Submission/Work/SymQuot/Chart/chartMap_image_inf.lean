import Mathlib
import Submission.Work.SymQuot.Chart
import Submission.Work.SymQuot.Invariants.fixedPoints_isIntegral

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Images of invariant opens under the chart map (area SY)

Let `G` be a finite group acting on a scheme `X` and let `U ⊆ X` be a `G`-invariant affine open
subscheme.  The chart map `chartMap U : U ⟶ chart U = Spec Γ(X, U)^G` is `G`-invariant, and two
points of `U` have the same image under it exactly when they lie in the same `G`-orbit.

Consequently, for `G`-invariant opens `W₁, W₂ ⊆ U` the images of `W₁` and `W₂` in `chart U`
intersect exactly in the image of `W₁ ⊓ W₂`:

  `chartMap '' W₁ ∩ chartMap '' W₂ = chartMap '' (W₁ ⊓ W₂)`.

The nontrivial inclusion (from left to right) is the fibre–orbit statement: if `chartMap x =
chartMap y` with `x ∈ W₁` and `y ∈ W₂`, then some group element carries `y` into `W₁`; since `W₂`
is invariant it even carries `y` into `W₁ ⊓ W₂`, giving a common preimage of the two points.
-/

namespace Work.SymQuot.Chart

open CategoryTheory Limits AlgebraicGeometry
open scoped Pointwise

universe u

variable {G : Type*} [Group G] {X : AlgebraicGeometry.Scheme}

/-- Membership in the range of the inclusion `W ≤ U` of open subschemes: a point of `U` lies in
the range of `X.homOfLE h` exactly when its underlying point of `X` lies in `W`. -/
lemma range_homOfLE_eq {W U : X.Opens} (h : W ≤ U) (y : U.toScheme) :
    y ∈ Set.range ⇑(X.homOfLE (U := W) (V := U) h) ↔ U.ι y ∈ W := by
  constructor
  · rintro ⟨w, rfl⟩
    have h1 : U.ι ((X.homOfLE h) w) = W.ι w := by
      simpa only [Scheme.Hom.comp_apply] using
        congrArg (fun (f : W.toScheme ⟶ X) => f w) (Scheme.homOfLE_ι X h)
    rw [h1]
    exact w.2
  · intro hy
    refine ⟨⟨U.ι y, hy⟩, Subtype.ext ?_⟩
    rw [Scheme.homOfLE_apply]
    rfl

/-- Two points of a `G`-invariant affine open subscheme `U` have the same image under the chart
map if and only if they lie in the same `G`-orbit: if `chartMap U x = chartMap U y` then some
`g : G` carries `y` to `x` inside `U`. -/
theorem chartMap_fiber_orbit_aux [Finite G] (A : GAction G X) {U : X.Opens}
    (hU : IsAffineOpen U) (hUi : A.IsInvariantOpen U) {x y : U.toScheme}
    (h : A.chartMap U hUi x = A.chartMap U hUi y) :
    ∃ g : G, A.hom g (U.ι y) = U.ι x := by
  letI : MulSemiringAction G Γ(X, U) := A.sectionMulSemiringAction U hUi
  -- The primes attached to `x` and `y` have the same contraction along `Γ(X,U)^G ↪ Γ(X,U)`.
  let P : PrimeSpectrum Γ(X, U) := hU.isoSpec.hom x
  let Q : PrimeSpectrum Γ(X, U) := hU.isoSpec.hom y
  have hpq : Ideal.under (FixedPoints.subring Γ(X, U) G) Q.asIdeal =
             Ideal.under (FixedPoints.subring Γ(X, U) G) P.asIdeal := by
    have h1 : PrimeSpectrum.comap (Subring.subtype (FixedPoints.subring Γ(X, U) G))
        (hU.isoSpec.hom x) = PrimeSpectrum.comap (Subring.subtype (FixedPoints.subring Γ(X, U) G))
          (hU.isoSpec.hom y) := by
      have h2 := h
      rw [Work.SymQuot.GAction.chartMap] at h2
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at h2
      rw [Spec.map_apply, Spec.map_apply] at h2
      rwa [← IsAffineOpen.isoSpec_hom hU] at h2
    have h3 := congrArg PrimeSpectrum.asIdeal h1
    simp only [Ideal.under_def]
    exact h3.symm
  -- The fibres of `Spec Γ(X,U) → Spec Γ(X,U)^G` are the orbits.
  obtain ⟨g, hg⟩ :=
    Algebra.IsInvariant.exists_smul_of_under_eq (FixedPoints.subring Γ(X, U) G) Γ(X, U) G
      Q.asIdeal P.asIdeal hpq
  refine ⟨g, ?_⟩
  -- Naturality of the chart map with respect to the action.
  have h_appLE : CommRingCat.ofHom (A.sectionHom U hUi g) =
      Scheme.Hom.appLE (A.hom g) U U (le_of_eq (hUi g).symm) := by
    rw [← CommRingCat.ofHom_hom (Scheme.Hom.appLE (A.hom g) U U (le_of_eq (hUi g).symm))]
    rfl
  have nat : U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (A.sectionHom U hUi g)) =
      (A.hom g).resLE U U (le_of_eq (hUi g).symm) ≫ U.toSpecΓ := by
    rw [h_appLE]
    exact Scheme.Opens.toSpecΓ_SpecMap_appLE (A.hom g) U U (le_of_eq (hUi g).symm)
  have hpt := congrArg (fun (f : U.toScheme ⟶ Spec Γ(X, U)) => f y) nat
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hpt
  rw [← IsAffineOpen.isoSpec_hom hU] at hpt
  -- The section-level description of the action of `g` on the prime `Q`.
  have hcomap : Ideal.comap (A.sectionHom U hUi g) (hU.isoSpec.hom y).asIdeal
      = g • (hU.isoSpec.hom y).asIdeal := by
    ext s
    rw [Ideal.mem_comap, Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    rw [show g⁻¹ • s = A.sectionHom U hUi (g⁻¹)⁻¹ s from rfl, inv_inv]
  have hmap : PrimeSpectrum.comap (A.sectionHom U hUi g) Q
      = (Spec.map (CommRingCat.ofHom (A.sectionHom U hUi g)) (hU.isoSpec.hom y)) := by
    rw [Spec.map_apply]
    simp only [CommRingCat.hom_ofHom]
    rfl
  have hchain : PrimeSpectrum.comap (A.sectionHom U hUi g) Q
      = hU.isoSpec.hom ((A.hom g).resLE U U (le_of_eq (hUi g).symm) y) :=
    hmap.trans hpt
  have hkey : (hU.isoSpec.hom ((A.hom g).resLE U U (le_of_eq (hUi g).symm) y)).asIdeal
      = (hU.isoSpec.hom x).asIdeal := by
    rw [← hchain, PrimeSpectrum.comap_asIdeal]
    exact hcomap.trans hg.symm
  -- `isoSpec` is injective, so the two points of `U` are related by `g`.
  have hinj : Function.Injective (hU.isoSpec.hom : U.toScheme → Spec Γ(X, U)) := by
    intro a b hab
    simpa using congrArg (fun z => hU.isoSpec.inv z) hab
  have hxy : x = (A.hom g).resLE U U (le_of_eq (hUi g).symm) y :=
    (hinj (PrimeSpectrum.ext hkey)).symm
  have hres : U.ι ((A.hom g).resLE U U (le_of_eq (hUi g).symm) y) = A.hom g (U.ι y) := by
    have h := congrArg (fun (f : U.toScheme ⟶ X) => f y)
      (Scheme.Hom.resLE_comp_ι (A.hom g) (le_of_eq (hUi g).symm))
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at h
    exact h
  rw [← hres, hxy]

theorem chartMap_image_inf {G : Type*} [Group G] [Finite G] {X : AlgebraicGeometry.Scheme}
    (A : Work.SymQuot.GAction G X) {W₁ W₂ U : X.Opens} (h₁ : W₁ ≤ U) (h₂ : W₂ ≤ U)
    (hU : AlgebraicGeometry.IsAffineOpen U) (hUi : A.IsInvariantOpen U)
    (hW₁i : A.IsInvariantOpen W₁) (hW₂i : A.IsInvariantOpen W₂) :
    ⇑(A.chartMap U hUi) '' Set.range ⇑(X.homOfLE (U := W₁) (V := U) h₁) ∩
        ⇑(A.chartMap U hUi) '' Set.range ⇑(X.homOfLE (U := W₂) (V := U) h₂)
      = ⇑(A.chartMap U hUi) '' Set.range ⇑(X.homOfLE (U := W₁ ⊓ W₂) (V := U) (inf_le_left.trans h₁)) := by
  ext z
  constructor
  · intro hz
    obtain ⟨hz₁, hz₂⟩ := hz
    obtain ⟨a, ha, rfl⟩ := hz₁
    obtain ⟨b, hb, hb₂⟩ := hz₂
    -- `chartMap a = chartMap b`, so `a` and `b` are in the same orbit.
    obtain ⟨g, hg⟩ := chartMap_fiber_orbit_aux A hU hUi hb₂.symm
    have haW₁ : U.ι a ∈ W₁ := (range_homOfLE_eq h₁ a).mp ha
    have hbW₂ : U.ι b ∈ W₂ := (range_homOfLE_eq h₂ b).mp hb
    -- invariance of `W₂` puts `a` into `W₂` as well
    have haW₂ : U.ι a ∈ W₂ := hg ▸ (hW₂i.mem_iff g (U.ι b)).mpr hbW₂
    have haW₁₂ : U.ι a ∈ W₁ ⊓ W₂ := ⟨haW₁, haW₂⟩
    exact ⟨a, (range_homOfLE_eq (inf_le_left.trans h₁) a).mpr haW₁₂, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    have hcW : U.ι c ∈ W₁ ⊓ W₂ := (range_homOfLE_eq (inf_le_left.trans h₁) c).mp hc
    exact ⟨⟨c, (range_homOfLE_eq h₁ c).mpr hcW.1, rfl⟩,
      ⟨c, (range_homOfLE_eq h₂ c).mpr hcW.2, rfl⟩⟩

end Work.SymQuot.Chart
