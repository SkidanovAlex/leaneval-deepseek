import Submission.Work.DSM5b.awayComplex

/-!
# `Submission.Work.DSM5b.awayIn_eq_zero_pow_mul`

The kernel of the localisation map `awayIn : R_{t_S} → R_{t_S}[1/T] = R[1/(T · t_S)]` is the
`T`-power-torsion: if `awayIn t T S a = 0` then `∃ m, (algebraMap R _ T) ^ m * a = 0`.

Proof.  Write `a` over a common denominator of the localisation `R_{t_S}`:
`a * (algebraMap (tS t S)) ^ N = algebraMap b`.  Applying `awayIn` and using `awayIn a = 0` gives
`algebraMap b = 0` in `R[1/(T · tS S)]`, i.e. `(T · tS S) ^ m * b = 0` in `R`
(`IsLocalization.Away.exists_of_eq`).  Mapping back to `R_{t_S}` gives
`(algebraMap (T · tS S)) ^ m * algebraMap b = 0`; substituting `algebraMap b = a · s ^ N` and
`algebraMap (T · tS S) = (algebraMap T) · s` (`s = algebraMap (tS S)`) yields
`(algebraMap T) ^ m · a · s ^ (m + N) = 0`.  Since `s` is a unit in `R_{t_S}`, cancelling
`s ^ (m + N)` gives `(algebraMap T) ^ m · a = 0`.
-/

namespace Work.DSM5b

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2

universe a

theorem awayIn_eq_zero_pow_mul {R : Type a} [CommRing R] {ι : Type a} [DecidableEq ι]
    (t : ι → R) (T : R) (S : Finset ι) (a : Localization.Away (tS t S))
    (h : awayIn t T S a = 0) :
    ∃ m : ℕ, (algebraMap R (Localization.Away (tS t S)) T) ^ m * a = 0 := by
  obtain ⟨N, b, hb⟩ := IsLocalization.Away.surj (tS t S) a
  have hbM : (algebraMap R (Localization.Away (T * tS t S))) b = 0 := by
    have h1 := congrArg (awayIn t T S) hb
    simp only [map_mul, map_pow, h, zero_mul] at h1
    rw [show awayIn t T S (algebraMap R (Localization.Away (tS t S)) b)
        = algebraMap R (Localization.Away (T * tS t S)) b from
        liftAway_algebraMap (dvd_mul_left (tS t S) T) b] at h1
    exact h1.symm
  obtain ⟨m, hm⟩ := IsLocalization.Away.exists_of_eq
    (S := Localization.Away (T * tS t S)) (T * tS t S) (a := b) (b := 0)
    (by simpa using hbM)
  rw [mul_zero] at hm
  have hL0 : (algebraMap R (Localization.Away (tS t S)) (T * tS t S)) ^ m *
      algebraMap R (Localization.Away (tS t S)) b = 0 := by
    have h2 := congrArg (algebraMap R (Localization.Away (tS t S))) hm
    simpa only [map_mul, map_pow, map_zero] using h2
  have hmain : (algebraMap R (Localization.Away (tS t S)) T) ^ m * a *
      (algebraMap R (Localization.Away (tS t S)) (tS t S)) ^ (m + N) = 0 := by
    have key : (algebraMap R (Localization.Away (tS t S)) T) ^ m * a *
        (algebraMap R (Localization.Away (tS t S)) (tS t S)) ^ (m + N)
        = (algebraMap R (Localization.Away (tS t S)) (T * tS t S)) ^ m *
          algebraMap R (Localization.Away (tS t S)) b := by
      rw [pow_add, map_mul, mul_pow, ← hb]
      ring
    rw [key, hL0]
  obtain ⟨u, hu⟩ : ∃ u : (Localization.Away (tS t S))ˣ,
      (u : Localization.Away (tS t S)) = algebraMap R (Localization.Away (tS t S)) (tS t S) :=
    ⟨(IsLocalization.Away.algebraMap_isUnit (tS t S)).unit,
      (IsLocalization.Away.algebraMap_isUnit (tS t S)).unit_spec⟩
  refine ⟨m, ?_⟩
  set v : (Localization.Away (tS t S))ˣ := u ^ (m + N) with hv
  have hvval : (v : Localization.Away (tS t S))
      = (algebraMap R (Localization.Away (tS t S)) (tS t S)) ^ (m + N) := by
    rw [hv, Units.val_pow_eq_pow_val, hu]
  rw [← hvval] at hmain
  have h5 : (algebraMap R (Localization.Away (tS t S)) T) ^ m * a
      = (algebraMap R (Localization.Away (tS t S)) T) ^ m * a * (v : Localization.Away (tS t S))
        * ((v⁻¹ : (Localization.Away (tS t S))ˣ) : Localization.Away (tS t S)) := by
    rw [mul_assoc, Units.mul_inv, mul_one]
  rw [h5, hmain, zero_mul]

end Work.DSM5b
