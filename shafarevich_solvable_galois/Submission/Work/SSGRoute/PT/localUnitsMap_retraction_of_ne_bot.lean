import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.E9c.TransportDefs
import Submission.Work.SSGRoute.e7comega_defs
import Submission.Work.SSGRoute.PT.archYoneda_perfect
import Submission.Work.SSGRoute.localUnitsMap_exists
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT

open CategoryTheory SSGRoute.PTExt

/-- **A `Rep`-morphism with a bijective underlying map admits a retraction.**  If the underlying
linear map of `ι : A ⟶ B` is bijective, then `ι` has a (two-sided, hence in particular left)
inverse: the inverse of the underlying `LinearEquiv` is automatically intertwining, because `ι`
is.  This is the abstract form of "an isomorphism of coefficient modules has a retraction". -/
theorem rep_retraction_of_bijective {R : Type} [Ring R] {G : Type} [Group G]
    {A B : Rep.{0} R G} (ι : A ⟶ B) (h : Function.Bijective ⇑ι.hom) :
    ∃ ρ : B ⟶ A, ι ≫ ρ = 𝟙 A := by
  let e : A.V ≃ₗ[R] B.V := LinearEquiv.ofBijective ι.hom.toLinearMap h
  have he : ∀ x : A.V, e x = ι.hom x :=
    fun x => LinearEquiv.ofBijective_apply ι.hom.toLinearMap x
  refine ⟨Rep.ofHom ⟨e.symm.toLinearMap, ?_⟩, ?_⟩
  · intro g
    apply LinearMap.ext
    intro x
    show e.symm (B.ρ g x) = A.ρ g (e.symm x)
    apply e.injective
    rw [e.apply_symm_apply, he,
      Representation.IntertwiningMap.isIntertwining A.ρ B.ρ ι.hom g (e.symm x),
      ← he (e.symm x), e.apply_symm_apply]
  · apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    show e.symm (ι.hom x) = x
    rw [← he x]
    exact e.symm_apply_apply x

/-- **The local algebra map at an infinite place is the units map of the completion map**, for an
arbitrary proof of the `LiesOver` relation.  (`NK.GlobalCFT.Galois.localAlgebraMapUnits_ofInfinite_eq`
states the same for the specific proof `Place.liesOver_ofInfinite h`; the definition of
`Place.localAlgebraMapUnits` does not depend on the proof, so the general form follows by unfolding
and `dif_pos`.) -/
theorem localAlgebraMapUnits_ofInfinite_eq'
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    {v : NumberField.InfinitePlace K} {w : NumberField.InfinitePlace L}
    (h : NumberField.InfinitePlace.LiesOver w v)
    (hu : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofInfinite w)
      (NK.GlobalCFT.Place.ofInfinite v)) :
    NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofInfinite w)
        (NK.GlobalCFT.Place.ofInfinite v) hu
      = Units.map (NumberField.LiesOver.completionMap (v := v) (w := w)).toMonoidHom := by
  simp only [NK.GlobalCFT.Place.localAlgebraMapUnits]
  rw [dif_pos h]

/-- **The archimedean local units map has a retraction when `D_w ≠ ⊥`.**  For a tower
`k ⊆ K ⊆ L` of number fields with `K/k`, `L/k` finite Galois, an infinite place `w` of `K` with
`decompK w ≠ ⊥` and a place `u | w` of `L`, the local units map
`localUnitsMap k ↥K ↥L w u hu : res f K_wˣ ⟶ L_uˣ` admits a retraction `ρ`.

Route: `decompK w ≠ ⊥` forces `w` complex (`Work.SSGRoute.PT.isComplex_of_place_ne_bot`, via
`isUnramified_iff_stabilizer_eq_bot`), so `u` (which lies over `w`) is complex as well, and
`u.IsUnramified ↥K` follows from `NumberField.InfinitePlace.isUnramified_iff`
(`IsReal u ∨ IsComplex (u.comap (algebraMap ↥K ↥L))`, and the place below `u` is `w`).  Hence
`NumberField.LiesOver.completionMap : K_w → L_u` is surjective
(`NumberField.LiesOver.completionMap_surjective_of_isUnramified`) as well as injective (ring hom of
fields), i.e. bijective.  By `Work.SSGRoute.localUnitsMap_spec` and
`Work.SSGRoute.localUnitsMap_ext` (`localAlgebraMapUnits_ofInfinite_eq` identifies the values with
`Units.map completionMap`), `localUnitsMap` is the units map of that isomorphism, so its inverse
gives the retraction: `LinearEquiv.ofBijective` on the coerced `LinearMap` (the inverse is
automatically intertwining because `ι` is); `ι ≫ ρ = 𝟙` is checked pointwise with `Rep.hom_ext`,
using that every element of the source is `Additive.ofMul u`. -/
theorem localUnitsMap_retraction_of_ne_bot {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] {K L : IntermediateField k Ω} [FiniteDimensional k K]
    [IsGalois k K] [FiniteDimensional k L] [IsGalois k L] [Algebra ↥K ↥L]
    [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (w : NK.GlobalCFT.Place ↥K)
    (hw : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K),
      w ≠ NK.GlobalCFT.Place.ofFinite q)
    (u : NK.GlobalCFT.Place ↥L) (hu : NK.GlobalCFT.Place.LiesOver u w)
    (hD : SSGRoute.PTExt.decompK (k := k) w ≠ ⊥) :
    ∃ ρ : NK.HassePrinciple.localUnitsRep k ↥L u ⟶
        Rep.res (Work.SSGRoute.decompKRestrict k ↥K ↥L w u hu)
          (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) w),
      Work.SSGRoute.localUnitsMap k ↥K ↥L w u hu ≫ ρ
        = 𝟙 (Rep.res (Work.SSGRoute.decompKRestrict k ↥K ↥L w u hu)
            (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) w)) := by
  rcases w with v | q
  · -- `w` is the archimedean place attached to `v : InfinitePlace ↥K`
    rcases u with w' | q'
    · -- `u` is the archimedean place attached to `w' : InfinitePlace ↥L`
      -- the place `w'` lies over `v`
      have hLies : NumberField.InfinitePlace.LiesOver w' v := by
        rcases hu with ⟨w'', v'', h1, h2, h3⟩ | ⟨q'', Q'', h1, h2, h3⟩
        · obtain rfl := Sum.inl_injective h2
          obtain rfl := Sum.inl_injective h1
          exact h3
        · exact (Sum.inl_ne_inr h1).elim
      -- `v` is complex because its decomposition group is non-trivial
      have hvC : v.IsComplex :=
        Work.SSGRoute.SSGStage.isComplex_of_decompK_ofInfinite_ne_bot (k := k) (K := ↥K) hD
      -- hence `w'` is unramified over `↥K`: the place below it is the complex place `v`
      have hUnram : w'.IsUnramified ↥K := by
        rw [NumberField.InfinitePlace.isUnramified_iff]
        exact Or.inr (by rw [NumberField.InfinitePlace.LiesOver.comap_eq w' v]; exact hvC)
      -- the completion map `↥K_v → ↥L_{w'}` is bijective
      have hbij : Function.Bijective (NumberField.LiesOver.completionMap (v := v) (w := w')) :=
        ⟨RingHom.injective _, NK.GlobalCFT.Galois.completionMap_surjective_of_isUnramified
          (K := ↥K) (L := ↥L) hUnram⟩
      -- the values of `localUnitsMap` are those of `Units.map completionMap`
      have hval : ∀ y : (NK.GlobalCFT.Place.localField ↥K (NK.GlobalCFT.Place.ofInfinite v))ˣ,
          (Work.SSGRoute.localUnitsMap k ↥K ↥L (NK.GlobalCFT.Place.ofInfinite v)
            (NK.GlobalCFT.Place.ofInfinite w') hu).hom (Additive.ofMul y)
          = Additive.ofMul (Units.map (NumberField.LiesOver.completionMap (v := v) (w := w')).toMonoidHom y) := by
        intro y
        rw [Work.SSGRoute.localUnitsMap_spec k ↥K ↥L (NK.GlobalCFT.Place.ofInfinite v)
          (NK.GlobalCFT.Place.ofInfinite w') hu y]
        rw [localAlgebraMapUnits_ofInfinite_eq' hLies hu]
      -- hence `localUnitsMap` is bijective on underlying types
      have hbi : Function.Bijective (⇑(Work.SSGRoute.localUnitsMap k ↥K ↥L
          (NK.GlobalCFT.Place.ofInfinite v) (NK.GlobalCFT.Place.ofInfinite w') hu)) := by
        have hfun : ⇑(Work.SSGRoute.localUnitsMap k ↥K ↥L (NK.GlobalCFT.Place.ofInfinite v)
            (NK.GlobalCFT.Place.ofInfinite w') hu)
            = fun x : Additive ((NK.GlobalCFT.Place.localField ↥K
                (NK.GlobalCFT.Place.ofInfinite v))ˣ) =>
              Additive.ofMul (Units.map (NumberField.LiesOver.completionMap (v := v) (w := w')).toMonoidHom
                (Additive.toMul x)) := by
          funext x
          obtain ⟨y, rfl⟩ := Additive.ofMul.surjective x
          exact hval y
        rw [hfun]
        exact (Additive.ofMul.bijective.comp
          ((Units.map_bijective hbij).comp Additive.toMul.bijective))
      exact rep_retraction_of_bijective _ hbi
    · -- `u` finite, but it lies over the archimedean place `w`: impossible
      exfalso
      rcases hu with ⟨w'', v'', h1, h2, h3⟩ | ⟨q'', Q'', h1, h2, h3⟩
      · exact Sum.inr_ne_inl h1
      · exact Sum.inl_ne_inr h2
  · -- `w` finite contradicts `hw`
    exact absurd rfl (hw q)

end Work.SSGRoute.PT
