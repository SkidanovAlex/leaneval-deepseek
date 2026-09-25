import Mathlib
import Submission.NK.GlobalCFTdeep.Transport.PlaceDefs

/-!
# The "lies over" relation is transported by `placeEquiv`

Given a ring equivalence `eK : K ≃+* K'` of number fields, `placeEquiv eK` identifies the
archimedean places of `K` and `K'` and the nonzero primes of `𝓞 K` and `𝓞 K'`.  If moreover
`eL : L ≃+* L'` is a ring equivalence of number fields which is compatible with the algebra
structures (`hcomp`), then the *geometry* of the two extensions is the same: the place `w` of `L`
lies over the place `v` of `K` if and only if the transported place `placeEquiv eL w` lies over
`placeEquiv eK v`.

This is the index-level input for the transport of the local data (local fields, local units,
local norms) along a ring equivalence, and hence for the transport of the norm subgroup
`N_{L/K} C_L`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFTdeep.Transport

open NK.GlobalCFT

/-! ### Auxiliary lemmas -/

/-- Unfolding `Place.LiesOver` at two archimedean places. -/
theorem liesOver_ofInfinite_iff {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] {w : InfinitePlace L} {v : InfinitePlace K} :
    Place.LiesOver (Place.ofInfinite w) (Place.ofInfinite v) ↔ w.LiesOver v := by
  rw [Place.liesOver_iff]
  constructor
  · rintro (⟨w', v', h1, h2, h⟩ | ⟨q, Q, h1, h2, h⟩)
    · rw [Place.ofInfinite_inj] at h1 h2
      rw [← h1, ← h2] at h; exact h
    · exact absurd h1 (Place.ofInfinite_ne_ofFinite w q)
  · intro h; exact Or.inl ⟨w, v, rfl, rfl, h⟩

/-- Unfolding `Place.LiesOver` at two nonarchimedean places. -/
theorem liesOver_ofFinite_iff {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] {q : HeightOneSpectrum (𝓞 L)} {Q : HeightOneSpectrum (𝓞 K)} :
    Place.LiesOver (Place.ofFinite q) (Place.ofFinite Q) ↔ q.asIdeal.LiesOver Q.asIdeal := by
  rw [Place.liesOver_iff]
  constructor
  · rintro (⟨w', v', h1, h2, h⟩ | ⟨q', Q', h1, h2, h⟩)
    · exact absurd h1 (Place.ofInfinite_ne_ofFinite w' q).symm
    · rw [Place.ofFinite_inj] at h1 h2
      rw [← h1, ← h2] at h; exact h
  · intro h; exact Or.inr ⟨q, Q, rfl, rfl, h⟩

/-- The relation `w.LiesOver v` between infinite places is equivalent to the equality
`w.comap (algebraMap k K) = v` of the place of `k` obtained by restriction. -/
theorem infinitePlace_liesOver_iff {k K : Type*} [Field k] [Field K] [Algebra k K]
    (w : InfinitePlace K) (v : InfinitePlace k) :
    w.LiesOver v ↔ w.comap (algebraMap k K) = v := by
  constructor
  · intro h; exact InfinitePlace.LiesOver.comap_eq w v
  · intro h; exact ⟨by rw [← h]; rfl⟩

/-- `RingOfIntegers.mapRingEquiv` intertwines the algebra maps `𝓞 K → 𝓞 L` and
`𝓞 K' → 𝓞 L'`: the ring-of-integers analogue of the compatibility `hcomp`. -/
theorem mapRingEquiv_algebraMap {K L K' L' : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [Field K'] [NumberField K'] [Field L'] [NumberField L']
    [Algebra K' L'] (eK : K ≃+* K') (eL : L ≃+* L')
    (hcomp : ∀ x : K, eL (algebraMap K L x) = algebraMap K' L' (eK x)) :
    ∀ x : 𝓞 K, (RingOfIntegers.mapRingEquiv eL) (algebraMap (𝓞 K) (𝓞 L) x) =
      algebraMap (𝓞 K') (𝓞 L') ((RingOfIntegers.mapRingEquiv eK) x) := by
  intro x
  apply RingOfIntegers.ext
  have h1 : ((RingOfIntegers.mapRingEquiv eL) (algebraMap (𝓞 K) (𝓞 L) x) : L')
      = eL (algebraMap K L (x : K)) := rfl
  rw [h1]
  have h2 : ((algebraMap (𝓞 K') (𝓞 L') ((RingOfIntegers.mapRingEquiv eK) x) : 𝓞 L') : L')
      = algebraMap K' L' (eK (x : K)) := rfl
  rw [h2, hcomp]

/-- Transport of the preimage of an ideal: the two ways of moving an ideal `J` of `𝓞 L` to an
ideal of `𝓞 K'` -- first take the image under `eL` and then the preimage along `𝓞 K' → 𝓞 L'`, or
first take the preimage along `𝓞 K → 𝓞 L` and then the image under `eK` -- agree. -/
theorem ideal_comap_map_transport {K L K' L' : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [Field K'] [NumberField K'] [Field L'] [NumberField L']
    [Algebra K' L'] (eK : K ≃+* K') (eL : L ≃+* L')
    (hcomp : ∀ x : K, eL (algebraMap K L x) = algebraMap K' L' (eK x)) :
    ∀ J : Ideal (𝓞 L),
      (J.map (RingOfIntegers.mapRingEquiv eL)).comap (algebraMap (𝓞 K') (𝓞 L')) =
      (J.comap (algebraMap (𝓞 K) (𝓞 L))).map (RingOfIntegers.mapRingEquiv eK) := by
  have hcomp_int := mapRingEquiv_algebraMap eK eL hcomp
  intro J
  apply Ideal.ext
  intro x
  rw [Ideal.mem_comap, Ideal.mem_map_of_equiv, Ideal.mem_map_of_equiv]
  constructor
  · rintro ⟨y, hy, hyx⟩
    refine ⟨(RingOfIntegers.mapRingEquiv eK).symm x, ?_, ?_⟩
    · rw [Ideal.mem_comap]
      have heq : (RingOfIntegers.mapRingEquiv eL)
          (algebraMap (𝓞 K) (𝓞 L) ((RingOfIntegers.mapRingEquiv eK).symm x)) =
          (RingOfIntegers.mapRingEquiv eL) y := by
        rw [hcomp_int, RingEquiv.apply_symm_apply, hyx]
      exact (RingOfIntegers.mapRingEquiv eL).injective heq ▸ hy
    · rw [RingEquiv.apply_symm_apply]
  · rintro ⟨y, hy, hyx⟩
    refine ⟨algebraMap (𝓞 K) (𝓞 L) y, ?_, ?_⟩
    · exact Ideal.mem_comap.mp hy
    · rw [hcomp_int, hyx]

/-- The "lies over" relation for infinite places is preserved by `infinitePlaceEquiv`. -/
theorem infinitePlaceEquiv_liesOver_iff {K L K' L' : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [Field K'] [NumberField K'] [Field L'] [NumberField L']
    [Algebra K' L'] (eK : K ≃+* K') (eL : L ≃+* L')
    (hcomp : ∀ x : K, eL (algebraMap K L x) = algebraMap K' L' (eK x))
    (w : InfinitePlace L) (v : InfinitePlace K) :
    w.LiesOver v ↔ (infinitePlaceEquiv eL w).LiesOver (infinitePlaceEquiv eK v) := by
  have hsymm : ((eL.symm : L' →+* L).comp (algebraMap K' L')) =
      ((algebraMap K L).comp (eK.symm : K' →+* K)) := by
    ext y
    rw [RingHom.comp_apply, RingHom.comp_apply]
    rw [show y = eK (eK.symm y) from (eK.apply_symm_apply y).symm]
    rw [← hcomp (eK.symm y)]
    simp
  rw [infinitePlaceEquiv_apply, infinitePlaceEquiv_apply]
  rw [infinitePlace_liesOver_iff, infinitePlace_liesOver_iff]
  rw [← InfinitePlace.comap_comp w (eL.symm : L' →+* L) (algebraMap K' L'), hsymm,
      InfinitePlace.comap_comp w (algebraMap K L) (eK.symm : K' →+* K)]
  constructor
  · intro h; rw [h]
  · intro h
    have h' := congrArg (fun z : InfinitePlace K' => z.comap (eK : K →+* K')) h
    rw [← InfinitePlace.comap_comp (w.comap (algebraMap K L)) (eK.symm : K' →+* K) (eK : K →+* K'),
        ← InfinitePlace.comap_comp v (eK.symm : K' →+* K) (eK : K →+* K'),
        RingEquiv.symm_comp, InfinitePlace.comap_id] at h'
    exact h'

/-- The "lies over" relation for nonarchimedean places is preserved by `finitePlaceEquiv`. -/
theorem finitePlaceEquiv_liesOver_iff {K L K' L' : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [Field K'] [NumberField K'] [Field L'] [NumberField L']
    [Algebra K' L'] (eK : K ≃+* K') (eL : L ≃+* L')
    (hcomp : ∀ x : K, eL (algebraMap K L x) = algebraMap K' L' (eK x))
    (q : HeightOneSpectrum (𝓞 L)) (Q : HeightOneSpectrum (𝓞 K)) :
    q.asIdeal.LiesOver Q.asIdeal ↔
      (finitePlaceEquiv eL q).asIdeal.LiesOver (finitePlaceEquiv eK Q).asIdeal := by
  have key := ideal_comap_map_transport eK eL hcomp
  rw [finitePlaceEquiv_asIdeal eL q, finitePlaceEquiv_asIdeal eK Q]
  rw [Ideal.liesOver_iff, Ideal.liesOver_iff, Ideal.under_def, Ideal.under_def]
  rw [show Ideal.comap (algebraMap (𝓞 K') (𝓞 L'))
        (Ideal.map (RingOfIntegers.mapRingEquiv eL : 𝓞 L →+* 𝓞 L') q.asIdeal) =
      Ideal.map (RingOfIntegers.mapRingEquiv eK : 𝓞 K →+* 𝓞 K')
        (Ideal.comap (algebraMap (𝓞 K) (𝓞 L)) q.asIdeal) from key q.asIdeal]
  constructor
  · intro h; rw [h]
  · intro h
    have h' := congrArg (fun I : Ideal (𝓞 K') =>
      Ideal.map ((RingOfIntegers.mapRingEquiv eK).symm : 𝓞 K' →+* 𝓞 K) I) h
    simp only [Ideal.map_of_equiv] at h'
    exact h'

/-! ### The theorem -/

theorem liesOver_placeEquiv {K L K' L' : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [Field K'] [NumberField K'] [Field L'] [NumberField L'] [Algebra K' L'] [FiniteDimensional K' L'] (eK : K ≃+* K') (eL : L ≃+* L') (hcomp : ∀ x : K, eL (algebraMap K L x) = algebraMap K' L' (eK x)) (w : NK.GlobalCFT.Place L) (v : NK.GlobalCFT.Place K) : (NK.GlobalCFT.Place.LiesOver w v ↔ NK.GlobalCFT.Place.LiesOver (NK.GlobalCFTdeep.Transport.placeEquiv eL w) (NK.GlobalCFTdeep.Transport.placeEquiv eK v)) := by
  cases w with
  | inl w' =>
    cases v with
    | inl v' =>
      rw [placeEquiv_ofInfinite, placeEquiv_ofInfinite]
      rw [liesOver_ofInfinite_iff, liesOver_ofInfinite_iff]
      exact infinitePlaceEquiv_liesOver_iff eK eL hcomp w' v'
    | inr Q =>
      rw [placeEquiv_ofInfinite, placeEquiv_ofFinite]
      simp only [NK.GlobalCFT.Place.LiesOver, NK.GlobalCFT.Place.ofFinite,
        NK.GlobalCFT.Place.ofInfinite, Sum.inl_ne_inr, false_and,
        exists_false, or_false, Sum.inr_ne_inl, and_false]
  | inr q =>
    cases v with
    | inl v' =>
      rw [placeEquiv_ofFinite, placeEquiv_ofInfinite]
      simp only [NK.GlobalCFT.Place.LiesOver, NK.GlobalCFT.Place.ofFinite,
        NK.GlobalCFT.Place.ofInfinite, Sum.inr_ne_inl, false_and,
        exists_false, or_false, Sum.inl_ne_inr, and_false]
    | inr Q =>
      rw [placeEquiv_ofFinite, placeEquiv_ofFinite]
      rw [liesOver_ofFinite_iff, liesOver_ofFinite_iff]
      exact finitePlaceEquiv_liesOver_iff eK eL hcomp q Q

end NK.GlobalCFTdeep.Transport
