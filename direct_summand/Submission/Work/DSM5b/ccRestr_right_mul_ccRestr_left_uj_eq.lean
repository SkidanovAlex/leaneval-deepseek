import Mathlib
import Submission.Work.DSM5b.CycleDefs

namespace Work.DSM5b

universe a

open DSMap DSMap.Mix2

theorem ccRestr_right_mul_ccRestr_left_uj_eq {R : Type a} [CommRing R] {ι : Type a} [DecidableEq ι]
    (t : ι → R) (i j : ι) (u : ι → ↥(DSMap.Mix2.chartRing t {i}))
    (hu : ∀ l : ι, (u l : Localization.Away (DSMap.Mix2.tS t {i}))
        * algebraMap R (Localization.Away (DSMap.Mix2.tS t {i})) (t i)
      = algebraMap R (Localization.Away (DSMap.Mix2.tS t {i})) (t l))
    (n : ℕ) (c : R) (z : ↥(DSMap.Mix2.chartRing t {j}))
    (hz : algebraMap R (Localization.Away (DSMap.Mix2.tS t {j})) c
        = (algebraMap R (Localization.Away (DSMap.Mix2.tS t {j})) (DSMap.Mix2.tS t {j})) ^ n
          * (z : Localization.Away (DSMap.Mix2.tS t {j})))
    (w : ↥(DSMap.Mix2.chartRing t {i}))
    (hw : (w : Localization.Away (DSMap.Mix2.tS t {i}))
        * (algebraMap R (Localization.Away (DSMap.Mix2.tS t {i})) (DSMap.Mix2.tS t {i})) ^ n
        = algebraMap R (Localization.Away (DSMap.Mix2.tS t {i})) c) :
    ccRestr t (Finset.subset_union_right) z * (ccRestr t (Finset.subset_union_left) (u j)) ^ n
      = ccRestr t (Finset.subset_union_left) w := by
  -- The two restriction maps land in the overlap chart `W[J/t_i t_j]`, i.e. the
  -- localisation `C = Localization.Away (tS t ({i} ∪ {j}))`, and both are read as `locRes`.
  let C := Localization.Away (DSMap.Mix2.tS t ({i} ∪ {j}))
  let h1 : ({j} : Finset ι) ⊆ {i} ∪ {j} := Finset.subset_union_right
  let h2 : ({i} : Finset ι) ⊆ {i} ∪ {j} := Finset.subset_union_left
  -- on a singleton, `tS` is the generator itself
  have hti : DSMap.Mix2.tS t {i} = t i := Finset.prod_singleton t i
  have htj : DSMap.Mix2.tS t {j} = t j := Finset.prod_singleton t j
  -- `t i` divides the localised element `tS t ({i} ∪ {j})`, hence `algebraMap (t i)` is a unit
  have hunit : IsUnit (algebraMap R C (t i)) := by
    refine isUnit_of_dvd_unit ?_
      (IsLocalization.Away.algebraMap_isUnit (DSMap.Mix2.tS t ({i} ∪ {j})))
    exact map_dvd _ (Finset.dvd_prod_of_mem t (by simp))
  -- `u j` is `t j / t i` in the target
  have hu' : locRes t h2 (u j).1 * algebraMap R C (t i) = algebraMap R C (t j) := by
    have h := congrArg (locRes t h2) (hu j)
    simpa only [map_mul, AlgHom.commutes] using h
  -- `c = t j ^ n * z` in the target
  have hz' : algebraMap R C c = (algebraMap R C (t j)) ^ n * locRes t h1 z.1 := by
    have h := congrArg (locRes t h1) hz
    simp only [map_mul, map_pow, AlgHom.commutes] at h
    rw [show algebraMap R C (DSMap.Mix2.tS t {j}) = algebraMap R C (t j) from by rw [htj]] at h
    exact h
  -- `w * t i ^ n = c` in the target
  have hw' : locRes t h2 w.1 * (algebraMap R C (t i)) ^ n = algebraMap R C c := by
    have h := congrArg (locRes t h2) hw
    simp only [map_mul, map_pow, AlgHom.commutes] at h
    rw [show algebraMap R C (DSMap.Mix2.tS t {i}) = algebraMap R C (t i) from by rw [hti]] at h
    exact h
  apply Subtype.ext
  simp only [Subalgebra.coe_mul, Subalgebra.coe_pow, ccRestr_coe]
  change locRes t h1 z.1 * (locRes t h2 (u j).1) ^ n = locRes t h2 w.1
  -- multiply both sides by `(algebraMap (t i)) ^ n` and cancel the unit
  have hkey : locRes t h1 z.1 * (locRes t h2 (u j).1) ^ n * (algebraMap R C (t i)) ^ n
      = locRes t h2 w.1 * (algebraMap R C (t i)) ^ n := by
    calc locRes t h1 z.1 * (locRes t h2 (u j).1) ^ n * (algebraMap R C (t i)) ^ n
        = locRes t h1 z.1 * ((locRes t h2 (u j).1) * algebraMap R C (t i)) ^ n := by
          rw [mul_pow, mul_assoc]
        _ = locRes t h1 z.1 * (algebraMap R C (t j)) ^ n := by rw [hu']
        _ = (algebraMap R C (t j)) ^ n * locRes t h1 z.1 := by rw [mul_comm]
        _ = algebraMap R C c := hz'.symm
        _ = locRes t h2 w.1 * (algebraMap R C (t i)) ^ n := hw'.symm
  exact (hunit.pow n).mul_right_cancel hkey

end Work.DSM5b
