import Mathlib
import Submission.Work.DSM5c.Basic

namespace Work.DSM5c

universe a

open DSMap DSMap.Mix2

/-- If the index type `ι` is a subsingleton, then for any `i ∈ S` the only generator of the chart
ring is `t_k/t_i` with `k = i`, i.e. `1` (as `t_i` is a unit in the localisation `W_{t_S}`); hence
`chartRing t S` is the bottom subalgebra of `W_{t_S}`. -/
theorem chartRing_eq_bot_of_subsingleton {W : Type a} [CommRing W] {ι : Type a} [Subsingleton ι] [DecidableEq ι] (t : ι → W) (S : Finset ι) :
    DSMap.Mix2.chartRing t S = ⊥ := by
  rw [DSMap.Mix2.chartRing, eq_bot_iff]
  apply Algebra.adjoin_le
  rintro x ⟨i, hi, k, hk⟩
  have hki : k = i := Subsingleton.elim k i
  rw [hki] at hk
  have hdvd : t i ∣ tS t S := Finset.dvd_prod_of_mem t hi
  have hunit : IsUnit (algebraMap W (Localization.Away (tS t S)) (t i)) :=
    isUnit_of_dvd_unit (map_dvd (algebraMap W _) hdvd)
      (IsLocalization.Away.algebraMap_isUnit (tS t S))
  have hx1 : x = 1 := by
    refine (IsUnit.mul_right_inj hunit).mp ?_
    rw [mul_comm, hk, mul_one]
  rw [hx1]
  exact Subalgebra.one_mem _

end Work.DSM5c
