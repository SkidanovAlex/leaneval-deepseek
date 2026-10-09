import Mathlib
import Submission.NK.GlobalCFT.Place
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Galois action on the places of an extension preserves the places below

For a finite extension `L / K` of number fields, `Gal(L/K)` acts on the places of `L` (both
archimedean and nonarchimedean ones).  Since the action is by `K`-algebra automorphisms, a place
`w` of `L` and its image `σ • w` lie over the *same* place `v` of `K`:

`NK.GlobalCFT.Place.LiesOver (σ • w) v ↔ NK.GlobalCFT.Place.LiesOver w v`.

This is the geometric input for the action of `Gal(L/K)` on the decomposition subgroups of the
places of `L` and hence on the idèle class group `C_L`.
-/

open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFT.Galois

/-- Unfolding `Place.LiesOver` at two archimedean places. -/
theorem globalCFT_liesOver_ofInfinite_iff {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (w : NumberField.InfinitePlace L)
    (v : NumberField.InfinitePlace K) :
    NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofInfinite w)
      (NK.GlobalCFT.Place.ofInfinite v) ↔ w.LiesOver v := by
  constructor
  · rintro (⟨w', v', h1, h2, h3⟩ | ⟨q, Q, h1, h2, _⟩)
    · rw [Sum.inl.injEq] at h1 h2
      rw [h1, h2]
      exact h3
    · exact absurd h1 (Sum.inl_ne_inr)
  · intro h
    exact Or.inl ⟨w, v, rfl, rfl, h⟩

/-- Unfolding `Place.LiesOver` at two nonarchimedean places. -/
theorem globalCFT_liesOver_ofFinite_iff {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (q : HeightOneSpectrum (𝓞 L))
    (Q : HeightOneSpectrum (𝓞 K)) :
    NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q)
      (NK.GlobalCFT.Place.ofFinite Q) ↔ q.asIdeal.LiesOver Q.asIdeal := by
  constructor
  · rintro (⟨w', v', h1, h2, _⟩ | ⟨q', Q', h1, h2, h3⟩)
    · exact absurd h1 (Sum.inr_ne_inl)
    · rw [Sum.inr.injEq] at h1 h2
      rw [h1, h2]
      exact h3
  · intro h
    exact Or.inr ⟨q, Q, rfl, rfl, h⟩

/-- The Galois action on the archimedean places of `L` preserves the place of `K` below. -/
theorem globalCFT_infinitePlace_smul_liesOver {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L) (w : NumberField.InfinitePlace L)
    (v : NumberField.InfinitePlace K) : (σ • w).LiesOver v ↔ w.LiesOver v := by
  have key : ∀ (w : NumberField.InfinitePlace L) (v : NumberField.InfinitePlace K),
      w.LiesOver v ↔ w.comap (algebraMap K L) = v := by
    intro w v
    refine ⟨fun _ => NumberField.InfinitePlace.LiesOver.comap_eq w v, fun h => ?_⟩
    refine ⟨?_⟩
    have hh : (w.comap (algebraMap K L)).1 = v.1 := congrArg Subtype.val h
    rw [← hh]
    rfl
  rw [key (σ • w) v, key w v]
  have h : (σ • w).comap (algebraMap K L) = w.comap (algebraMap K L) := by
    rw [NumberField.InfinitePlace.comap_smul]
    congr 1
    ext x
    simp
  rw [h]

/-- The Galois action on the nonarchimedean places of `L` preserves the place of `K` below. -/
theorem globalCFT_finitePlace_smul_liesOver {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L) (q : HeightOneSpectrum (𝓞 L))
    (Q : HeightOneSpectrum (𝓞 K)) :
    (NK.GlobalCFT.Place.smulHeightOneSpectrum σ q).asIdeal.LiesOver Q.asIdeal ↔
      q.asIdeal.LiesOver Q.asIdeal := by
  have key : ∀ (q : HeightOneSpectrum (𝓞 L)) (Q : HeightOneSpectrum (𝓞 K)),
      q.asIdeal.LiesOver Q.asIdeal ↔
        Q.asIdeal = Ideal.comap (algebraMap (𝓞 K) (𝓞 L)) q.asIdeal := by
    intro q Q
    exact ⟨fun _ => Ideal.LiesOver.over, fun h => ⟨h⟩⟩
  have hcom : ∀ (q : HeightOneSpectrum (𝓞 L)),
      Ideal.comap (algebraMap (𝓞 K) (𝓞 L))
          (Ideal.map (NK.GlobalCFT.Place.ringOfIntegersEquiv σ) q.asIdeal) =
        Ideal.comap (algebraMap (𝓞 K) (𝓞 L)) q.asIdeal := by
    intro q
    let f : 𝓞 L →+* 𝓞 L := (NK.GlobalCFT.Place.ringOfIntegersEquiv σ : 𝓞 L →+* 𝓞 L)
    change Ideal.comap (algebraMap (𝓞 K) (𝓞 L)) (Ideal.map f q.asIdeal) =
      Ideal.comap (algebraMap (𝓞 K) (𝓞 L)) q.asIdeal
    have hφ : f.comp (algebraMap (𝓞 K) (𝓞 L)) = algebraMap (𝓞 K) (𝓞 L) := by
      change ((NK.GlobalCFT.Place.ringOfIntegersEquiv σ : 𝓞 L →+* 𝓞 L)).comp
          (algebraMap (𝓞 K) (𝓞 L)) = algebraMap (𝓞 K) (𝓞 L)
      ext x
      simp [NK.GlobalCFT.Place.ringOfIntegersEquiv]
    calc Ideal.comap (algebraMap (𝓞 K) (𝓞 L)) (Ideal.map f q.asIdeal)
        = Ideal.comap (f.comp (algebraMap (𝓞 K) (𝓞 L))) (Ideal.map f q.asIdeal) := by rw [hφ]
      _ = Ideal.comap (algebraMap (𝓞 K) (𝓞 L)) (Ideal.comap f (Ideal.map f q.asIdeal)) := by
            rw [Ideal.comap_comap]
      _ = Ideal.comap (algebraMap (𝓞 K) (𝓞 L)) q.asIdeal := by
            rw [Ideal.comap_map_of_bijective f (RingEquiv.bijective _)]
  rw [key ((NK.GlobalCFT.Place.smulHeightOneSpectrum σ q)) Q, key q Q,
    NK.GlobalCFT.Place.smulHeightOneSpectrum_asIdeal, hcom q]

theorem globalCFT_place_smul_liesOver {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L) (w : NK.GlobalCFT.Place L)
    (v : NK.GlobalCFT.Place K) :
    NK.GlobalCFT.Place.LiesOver (σ • w) v ↔ NK.GlobalCFT.Place.LiesOver w v := by
  cases w with
  | inl w' =>
    cases v with
    | inl v' =>
      rw [NK.GlobalCFT.Place.smul_ofInfinite, globalCFT_liesOver_ofInfinite_iff,
        globalCFT_liesOver_ofInfinite_iff]
      exact globalCFT_infinitePlace_smul_liesOver σ w' v'
    | inr Q =>
      rw [NK.GlobalCFT.Place.smul_ofInfinite]
      simp only [NK.GlobalCFT.Place.LiesOver, NK.GlobalCFT.Place.ofFinite,
        NK.GlobalCFT.Place.ofInfinite, Sum.inl_ne_inr, false_and,
        exists_false, or_false, Sum.inr_ne_inl, and_false]
  | inr q =>
    cases v with
    | inl v' =>
      rw [NK.GlobalCFT.Place.smul_ofFinite]
      simp only [NK.GlobalCFT.Place.LiesOver, NK.GlobalCFT.Place.ofFinite,
        NK.GlobalCFT.Place.ofInfinite, Sum.inr_ne_inl, false_and,
        exists_false, or_false, Sum.inl_ne_inr, and_false]
    | inr Q =>
      rw [NK.GlobalCFT.Place.smul_ofFinite, globalCFT_liesOver_ofFinite_iff,
        globalCFT_liesOver_ofFinite_iff]
      exact globalCFT_finitePlace_smul_liesOver σ q Q

end NK.GlobalCFT.Galois
