import Mathlib

namespace Work.DSF1.Cech

/-- If `S` is the localization of `R` away from `g` and `T` is the localization of `R` away from
`g * f`, then `T` is the localization of `S` away from the image of `f` in `S`.

This is the "away away" statement `R_{gf} = (R_g)_f`.  There are two structural inputs:

* `IsLocalization.Away.commutes` applied with the intermediate ring `T` itself: since the image of
  `g` is a unit in `T`, the ring `T` is the localization of itself away from that image, hence
  `T` is a localization of `S` away from the image of `g * f`;
* `g` is a unit in `S = R_g`, so that localizing `S` at `g * f` is the same as localizing `S`
  at `f`. -/
theorem away_away_isLocalization {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T] (g f : R)
    [IsLocalization.Away g S] [IsLocalization.Away (g * f) T] :
    IsLocalization.Away (algebraMap R S f) T := by
  -- `T` is the localization of itself away from the image of `g`, since that image is a unit.
  have hgt : IsLocalization.Away (algebraMap R T g) T :=
    IsLocalization.away_of_isUnit_of_bijective T
      (IsLocalization.Away.isUnit_of_dvd (g * f) ⟨f, by ring⟩) Function.bijective_id
  -- `IsLocalization.Away.commutes` with `S₂ = T` identifies `T` with the localization of `S`
  -- away from the image of `g * f`.
  have hbig : IsLocalization.Away (algebraMap R S (g * f)) T :=
    IsLocalization.Away.commutes S T T g (g * f)
  -- The image of `g` is a unit in `S`, so `algebraMap R S (g * f)` is associated to
  -- `algebraMap R S f`, and localizing away from associated elements is the same.
  have hsg : IsUnit (algebraMap R S g) := IsLocalization.Away.algebraMap_isUnit g
  refine (IsLocalization.Away.iff_of_associated
    (associated_unit_mul_left (algebraMap R S f) (algebraMap R S g) hsg)).mp ?_
  simpa only [map_mul] using hbig

theorem away_away_surj_ker {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T] (g f : R)
    [IsLocalization.Away g S] [IsLocalization.Away (g * f) T] :
    (∀ z : T, ∃ (k : ℕ) (t : S), z * (algebraMap R T f) ^ k = algebraMap S T t) ∧
      (∀ t : S, algebraMap S T t = 0 → ∃ k : ℕ, t * (algebraMap R S f) ^ k = 0) := by
  have hmain : IsLocalization.Away (algebraMap R S f) T := away_away_isLocalization g f
  constructor
  · intro z
    obtain ⟨k, t', ht⟩ := IsLocalization.Away.surj (algebraMap R S f) z
    exact ⟨k, t', by rw [IsScalarTower.algebraMap_apply R S T f]; exact ht⟩
  · intro t' ht
    obtain ⟨k, hk⟩ := IsLocalization.Away.exists_of_eq (R := S) (S := T)
      (algebraMap R S f) (a := t') (b := 0) (by simpa using ht)
    exact ⟨k, by simpa [mul_comm] using hk⟩

end Work.DSF1.Cech
