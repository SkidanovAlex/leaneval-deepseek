import Mathlib
import Submission.Work.SymQuot.Chart
import Submission.Work.SymQuot.Chart.chartMap_fiber_orbit
import Submission.Work.SymQuot.Chart.chartRes_chartMap
import Submission.Work.SymQuot.Invariants.surjective_specMap_fixedPoints

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

namespace Work.SymQuot.Chart

variable {G : Type*} [Group G] [Finite G] {X : AlgebraicGeometry.Scheme}

/-- The chart map `U ⟶ chart U` of an affine invariant open `U` is surjective: it displays
`chart U = Spec Γ(X,U)^G` as the quotient of `U` by `G` (on points). -/
lemma chartMap_surjective (A : Work.SymQuot.GAction G X) {U : X.Opens}
    (hU : IsAffineOpen U) (hUi : A.IsInvariantOpen U) :
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
  exact h2.comp h1

/-- The action of `g` on sections over an invariant open fixes the invariants. -/
lemma sectionHom_subtype (A : Work.SymQuot.GAction G X) (U : X.Opens)
    (hU : A.IsInvariantOpen U) (g : G) :
    (A.sectionHom U hU g).comp (Subring.subtype (Work.SymQuot.GAction.invariants A U hU)) =
      Subring.subtype (Work.SymQuot.GAction.invariants A U hU) := by
  apply RingHom.ext
  intro s
  have h := (Work.SymQuot.GAction.mem_invariants_iff A hU (s : Γ(X, U))).mp s.2 g⁻¹
  simpa using h

/-- The chart map `U ⟶ chart U` is invariant under the action of `G` on `U`. -/
lemma chartMap_resLE_apply (A : Work.SymQuot.GAction G X) (U : X.Opens)
    (hU : A.IsInvariantOpen U) (g : G) (x : ↑U.toScheme) :
    A.chartMap U hU ((A.hom g).resLE U U (le_of_eq (hU g).symm) x) = A.chartMap U hU x := by
  have hmap : ∀ z : ↑U.toScheme,
      A.chartMap U hU z =
        PrimeSpectrum.comap (Subring.subtype (Work.SymQuot.GAction.invariants A U hU))
          (U.toSpecΓ z) := by
    intro z
    exact AlgebraicGeometry.Spec.map_apply (CommRingCat.ofHom (Subring.subtype
      (Work.SymQuot.GAction.invariants A U hU))) (U.toSpecΓ z)
  have hh : U.toSpecΓ ((A.hom g).resLE U U (le_of_eq (hU g).symm) x) =
      ⇑(Spec.map (Scheme.Hom.appLE (A.hom g) U U (le_of_eq (hU g).symm))) (U.toSpecΓ x) := by
    have h := congrFun (congrArg (fun φ : ↑U.toScheme ⟶ Spec Γ(X, U) => ⇑φ)
      (Scheme.Opens.toSpecΓ_SpecMap_appLE (A.hom g) U U (le_of_eq (hU g).symm))) x
    simpa only [Scheme.Hom.comp_apply] using h.symm
  have h2 := AlgebraicGeometry.Spec.map_apply (Scheme.Hom.appLE (A.hom g) U U
    (le_of_eq (hU g).symm)) (U.toSpecΓ x)
  have h1 : U.toSpecΓ ((A.hom g).resLE U U (le_of_eq (hU g).symm) x) =
      PrimeSpectrum.comap (Scheme.Hom.appLE (A.hom g) U U (le_of_eq (hU g).symm)).hom
        (U.toSpecΓ x) := hh.trans h2
  have h3 : PrimeSpectrum.comap (Subring.subtype (Work.SymQuot.GAction.invariants A U hU))
        (PrimeSpectrum.comap (Scheme.Hom.appLE (A.hom g) U U (le_of_eq (hU g).symm)).hom
          (U.toSpecΓ x))
      = PrimeSpectrum.comap ((Scheme.Hom.appLE (A.hom g) U U (le_of_eq (hU g).symm)).hom.comp
          (Subring.subtype (Work.SymQuot.GAction.invariants A U hU))) (U.toSpecΓ x) :=
    (PrimeSpectrum.comap_comp_apply (Subring.subtype (Work.SymQuot.GAction.invariants A U hU))
      (Scheme.Hom.appLE (A.hom g) U U (le_of_eq (hU g).symm)).hom (U.toSpecΓ x)).symm
  have h4 : PrimeSpectrum.comap ((Scheme.Hom.appLE (A.hom g) U U (le_of_eq (hU g).symm)).hom.comp
        (Subring.subtype (Work.SymQuot.GAction.invariants A U hU))) (U.toSpecΓ x)
      = PrimeSpectrum.comap (Subring.subtype (Work.SymQuot.GAction.invariants A U hU))
        (U.toSpecΓ x) :=
    congrArg (fun φ => PrimeSpectrum.comap φ (U.toSpecΓ x)) (sectionHom_subtype A U hU g)
  exact (hmap ((A.hom g).resLE U U (le_of_eq (hU g).symm) x)).trans
    ((congrArg (fun y => PrimeSpectrum.comap
        (Subring.subtype (Work.SymQuot.GAction.invariants A U hU)) y) h1).trans
      (h3.trans (h4.trans (hmap x).symm)))

/-- The fibres of the chart map are the `G`-orbits, in the form needed for the open map
property: two points of `U` with the same image differ by an element of `G`. -/
lemma chartMap_fiber (A : Work.SymQuot.GAction G X) {U : X.Opens} (hU : IsAffineOpen U)
    (hUi : A.IsInvariantOpen U) {x y : ↑U.toScheme}
    (h : A.chartMap U hUi x = A.chartMap U hUi y) :
    ∃ g : G, (A.hom g).resLE U U (le_of_eq (hUi g).symm) y = x := by
  obtain ⟨g, hg⟩ := chartMap_fiber_orbit A hU hUi h
  refine ⟨g, ?_⟩
  refine (Scheme.Hom.isOpenEmbedding U.ι).isEmbedding.injective ?_
  calc U.ι ((A.hom g).resLE U U (le_of_eq (hUi g).symm) y)
      = A.hom g (U.ι y) := by
        rw [← Scheme.Hom.comp_apply, Scheme.Hom.resLE_comp_ι, Scheme.Hom.comp_apply]
    _ = U.ι x := hg

/-- `Spec` of the inclusion of the invariants `B^G ↪ B` is a closed map: `B` is integral
over `B^G` for a finite group `G`. -/
lemma isClosedMap_specMap_subringSubtype {G : Type*} [Group G] [Finite G] {B : Type*}
    [CommRing B] [MulSemiringAction G B] :
    IsClosedMap ⇑(Spec.map (CommRingCat.ofHom (Subring.subtype (FixedPoints.subring B G)))) := by
  have hInt : (Subring.subtype (FixedPoints.subring B G)).IsIntegral := by
    rw [show Subring.subtype (FixedPoints.subring B G) = algebraMap (FixedPoints.subring B G) B
      from RingHom.ext fun x => rfl]
    exact algebraMap_isIntegral_iff.mpr inferInstance
  exact PrimeSpectrum.isClosedMap_comap_of_isIntegral _ hInt

/-- The chart map is a closed map (the quotient map `U ⟶ U/G` in the affine case). -/
lemma chartMap_isClosedMap (A : Work.SymQuot.GAction G X) {U : X.Opens}
    (hU : IsAffineOpen U) (hUi : A.IsInvariantOpen U) :
    IsClosedMap ⇑(A.chartMap U hUi) := by
  letI : MulSemiringAction G Γ(X, U) := A.sectionMulSemiringAction U hUi
  have hS : IsClosedMap ⇑(Spec.map (CommRingCat.ofHom
      (Subring.subtype (Work.SymQuot.GAction.invariants A U hUi)))) :=
    isClosedMap_specMap_subringSubtype (G := G) (B := Γ(X, U))
  have hid : IsClosedMap ⇑(𝟙 (Spec Γ(X, U))) := by
    intro s hs
    simpa using hs
  have hto : IsClosedMap ⇑(U.toSpecΓ) := by
    have h2 := (MorphismProperty.cancel_left_of_respectsIso (P := topologically @IsClosedMap)
      (IsAffineOpen.isoSpec hU).hom (𝟙 (Spec Γ(X, U)))).mpr hid
    rw [IsAffineOpen.isoSpec_hom (hU := hU), Category.comp_id] at h2
    exact h2
  rw [Work.SymQuot.GAction.chartMap]
  exact hS.comp hto

/-- The chart map `U ⟶ chart U` is an open map.  Since it is a closed surjection it is a
quotient map, and the preimage of the image of an open set `W` is the union of the
`G`-translates of `W`, which is again open. -/
lemma chartMap_isOpenMap (A : Work.SymQuot.GAction G X) {U : X.Opens}
    (hU : IsAffineOpen U) (hUi : A.IsInvariantOpen U) :
    IsOpenMap ⇑(A.chartMap U hUi) := by
  have hcl : IsClosedMap ⇑(A.chartMap U hUi) := chartMap_isClosedMap A hU hUi
  have hsurj : Function.Surjective ⇑(A.chartMap U hUi) := chartMap_surjective A hU hUi
  have hq : Topology.IsQuotientMap ⇑(A.chartMap U hUi) :=
    hcl.isQuotientMap (Scheme.Hom.continuous _) hsurj
  intro W hW
  refine hq.isCoinducing.isOpen_preimage.mp ?_
  have key : ⇑(A.chartMap U hUi) ⁻¹' (⇑(A.chartMap U hUi) '' W)
      = ⋃ g : G, ⇑((A.hom g).resLE U U (le_of_eq (hUi g).symm)) ⁻¹' W := by
    ext z
    simp only [Set.mem_preimage, Set.mem_image, Set.mem_iUnion]
    constructor
    · rintro ⟨y, hyW, hyz⟩
      obtain ⟨g, hg⟩ := chartMap_fiber A hU hUi (x := y) (y := z) hyz
      exact ⟨g, hg ▸ hyW⟩
    · rintro ⟨g, hg⟩
      exact ⟨_, hg, chartMap_resLE_apply A U hUi g z⟩
  rw [key]
  exact isOpen_iUnion fun g => hW.preimage (Scheme.Hom.continuous _)

/-- The restriction maps between the charts of `G`-invariant affine opens are topological
embeddings. -/
theorem chartRes_isEmbedding {G : Type*} [Group G] [Finite G] {X : AlgebraicGeometry.Scheme}
    (A : Work.SymQuot.GAction G X) {V U : X.Opens} (hVU : V ≤ U)
    (hU : AlgebraicGeometry.IsAffineOpen U) (hV : AlgebraicGeometry.IsAffineOpen V)
    (hUi : A.IsInvariantOpen U) (hVi : A.IsInvariantOpen V) :
    Topology.IsEmbedding ⇑(Work.SymQuot.GAction.chartRes A V U hVU hUi hVi) := by
  -- naturality of the chart map in the open subscheme
  have hnat : ∀ z : ↑V.toScheme,
      A.chartMap U hUi (X.homOfLE hVU z) =
        A.chartRes V U hVU hUi hVi (A.chartMap V hVi z) := by
    intro z
    have hh := congrFun (congrArg (fun φ : ↑V.toScheme ⟶ A.chart U hUi => ⇑φ)
      (chartRes_chartMap (A := A) hVU hUi hVi)) z
    simpa only [Scheme.Hom.comp_apply] using hh
  -- injectivity
  have hinj : Function.Injective ⇑(A.chartRes V U hVU hUi hVi) := by
    intro x y hxy
    obtain ⟨x', rfl⟩ := chartMap_surjective A hV hVi x
    obtain ⟨y', rfl⟩ := chartMap_surjective A hV hVi y
    have h1 : A.chartMap U hUi (X.homOfLE hVU x') = A.chartMap U hUi (X.homOfLE hVU y') := by
      rw [hnat x', hnat y', hxy]
    obtain ⟨g, hg⟩ := chartMap_fiber_orbit A hU hUi h1
    have hmapV : U.ι (X.homOfLE hVU y') = V.ι y' := by
      have h := congrFun (congrArg (fun φ : ↑V.toScheme ⟶ X => ⇑φ) (Scheme.homOfLE_ι X hVU)) y'
      simpa only [Scheme.Hom.comp_apply] using h
    have hmapV' : U.ι (X.homOfLE hVU x') = V.ι x' := by
      have h := congrFun (congrArg (fun φ : ↑V.toScheme ⟶ X => ⇑φ) (Scheme.homOfLE_ι X hVU)) x'
      simpa only [Scheme.Hom.comp_apply] using h
    have hg' : A.hom g (V.ι y') = V.ι x' := by
      rw [hmapV, hmapV'] at hg
      exact hg
    have hy'' : (A.hom g).resLE V V (le_of_eq (hVi g).symm) y' = x' := by
      refine (Scheme.Hom.isOpenEmbedding (V.ι)).isEmbedding.injective ?_
      calc V.ι ((A.hom g).resLE V V (le_of_eq (hVi g).symm) y')
          = A.hom g (V.ι y') := by
            rw [← Scheme.Hom.comp_apply, Scheme.Hom.resLE_comp_ι, Scheme.Hom.comp_apply]
        _ = V.ι x' := hg'
    rw [← hy'']
    exact chartMap_resLE_apply A V hVi g y'
  -- openness
  have hopen : IsOpenMap ⇑(A.chartRes V U hVU hUi hVi) := by
    intro s hs
    have hps : IsOpen (⇑(A.chartMap V hVi) ⁻¹' s) := hs.preimage (Scheme.Hom.continuous _)
    have himg : IsOpen (⇑(X.homOfLE hVU) '' (⇑(A.chartMap V hVi) ⁻¹' s)) :=
      (Scheme.Hom.isOpenEmbedding (X.homOfLE hVU)).isOpenMap _ hps
    have hset : ⇑(A.chartRes V U hVU hUi hVi) '' s
        = ⇑(A.chartMap U hUi) '' (⇑(X.homOfLE hVU) '' (⇑(A.chartMap V hVi) ⁻¹' s)) := by
      ext z
      constructor
      · rintro ⟨a, ha, rfl⟩
        obtain ⟨b, hb⟩ := chartMap_surjective A hV hVi a
        subst hb
        exact ⟨X.homOfLE hVU b, ⟨b, ha, rfl⟩, hnat b⟩
      · rintro ⟨u, ⟨b, hb, rfl⟩, hu⟩
        exact ⟨A.chartMap V hVi b, hb, by rw [← hnat b]; exact hu⟩
    rw [hset]
    exact chartMap_isOpenMap A hU hUi _ himg
  exact (Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    (Scheme.Hom.continuous _) hinj hopen).isEmbedding

end Work.SymQuot.Chart
