import Mathlib
import Submission.Work.DSM5b.CycleDefs
import Submission.Work.DSM5b.locResAwayKernel
import Submission.Work.DSM5b.chartRing_gen_mul_eq

namespace Work.DSM5b

open DSMap DSMap.Mix2

universe a

set_option maxHeartbeats 800000

/-- **Elements of the `i`-chart that agree on the overlap differ by a power of `t j / t i`.**

File `Submission/Work/DSM5b/chartRing_overlap_pow_mul_eq.lean`, namespace `Work.DSM5b` (with
`universe a`); suggested imports: `Submission.Work.DSM5b.CycleDefs`,
`Submission.Work.DSM5b.locResAwayKernel`, `Submission.Work.DSM5b.chartRing_gen_mul_eq`.

Let `R` be a commutative ring, `t : ι → R`, `W_i = Localization.Away (tS t {i})`,
`W_ij = Localization.Away (tS t ({i} ∪ {j}))` and `chartRing t {i} ⊆ W_i` the blowup chart ring,
with `locRes t hST : W_i →ₐ[R] W_ij` the localisation map for `hST : {i} ⊆ {i} ∪ {j}`.  Let
`u ∈ chartRing t {i}` satisfy `u * algebraMap R W_i (t i) = algebraMap R W_i (t j)` (so
`u = t j / t i`; such a `u` exists by `Work.DSM5b.chartRing_gen_mul_eq`).  Then two elements `x, y`
of the `i`-chart with the same image in the overlap chart agree after multiplication by a power of
`u`.

Route: `Work.DSM5b.locResAwayKernel t hST hj x.1 y.1 h` (`hj : {i} ∪ {j} ⊆ insert j {i}`, which is
`Finset.insert_eq` together with `Finset.union_comm`) gives `n` with
`(algebraMap R W_i (t j)) ^ n * x.1 = (algebraMap R W_i (t j)) ^ n * y.1` in `W_i` (the hypothesis
`h` must first be transported to the underlying elements, e.g. via `congrArg Subtype.val`).  Then
raising `hu` to the `n`-th power gives `u ^ n * (algebraMap R W_i (t i)) ^ n
= (algebraMap R W_i (t j)) ^ n`, so
`(u ^ n * x.1) * A = (u ^ n * y.1) * A` with `A := (algebraMap R W_i (t i)) ^ n`, a unit in `W_i`
(`t i ∣ tS t {i}`, so `IsLocalization.Away.isUnit_of_dvd`; cancel with
`IsUnit.mul_right_cancel`).  Conclude `u ^ n * x = u ^ n * y` in `↥(chartRing t {i})` by
`Subtype.ext`.

Do not use the frozen sorried declarations of `DSMap.Mix2`. -/
theorem chartRing_overlap_pow_mul_eq {R : Type a} [CommRing R] {ι : Type a} [DecidableEq ι]
    (t : ι → R) (i j : ι) (u : ↥(DSMap.Mix2.chartRing t {i}))
    (hu : (u : Localization.Away (DSMap.Mix2.tS t {i}))
        * algebraMap R (Localization.Away (DSMap.Mix2.tS t {i})) (t i)
      = algebraMap R (Localization.Away (DSMap.Mix2.tS t {i})) (t j))
    {x y : ↥(DSMap.Mix2.chartRing t {i})}
    (h : DSMap.Mix2.locRes t (Finset.subset_union_left : ({i} : Finset ι) ⊆ {i} ∪ {j})
          (x : Localization.Away (DSMap.Mix2.tS t {i}))
       = DSMap.Mix2.locRes t (Finset.subset_union_left : ({i} : Finset ι) ⊆ {i} ∪ {j})
          (y : Localization.Away (DSMap.Mix2.tS t {i}))) :
    ∃ n : ℕ, u ^ n * x = u ^ n * y := by
  -- `{i} ∪ {j} ⊆ insert j {i}`
  have hj : ({i} ∪ {j} : Finset ι) ⊆ insert j {i} := by
    intro a ha
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert] at ha ⊢
    tauto
  -- `locResAwayKernel` gives `(algebraMap R W_i (t j)) ^ n * x = (algebraMap R W_i (t j)) ^ n * y`
  obtain ⟨n, hn⟩ :=
    locResAwayKernel (W := R) (t := t) (S := {i}) (T := {i} ∪ {j})
      (Finset.subset_union_left) (k := j) hj
      (x : Localization.Away (DSMap.Mix2.tS t {i}))
      (y : Localization.Away (DSMap.Mix2.tS t {i})) h
  -- raising `hu` to the `n`-th power
  have hu_pow : (↑u : Localization.Away (DSMap.Mix2.tS t {i})) ^ n
      * (algebraMap R (Localization.Away (DSMap.Mix2.tS t {i})) (t i)) ^ n
      = (algebraMap R (Localization.Away (DSMap.Mix2.tS t {i})) (t j)) ^ n := by
    have hh := congrArg (fun z : Localization.Away (DSMap.Mix2.tS t {i}) => z ^ n) hu
    simpa only [mul_pow] using hh
  -- `algebraMap R W_i (t i)` is a unit
  have hunit_i : IsUnit (algebraMap R (Localization.Away (DSMap.Mix2.tS t {i})) (t i)) :=
    isUnit_of_dvd_unit
      (map_dvd (algebraMap R (Localization.Away (DSMap.Mix2.tS t {i})))
        (show t i ∣ DSMap.Mix2.tS t {i} from ⟨1, by simp [tS_singleton_eq t i]⟩))
      (IsLocalization.Away.algebraMap_isUnit (DSMap.Mix2.tS t {i}))
  refine ⟨n, ?_⟩
  apply Subtype.ext
  simp only [Subalgebra.coe_mul, Subalgebra.coe_pow]
  -- cancel the unit `A = (algebraMap R W_i (t i)) ^ n`
  have hx : ((↑u : Localization.Away (DSMap.Mix2.tS t {i})) ^ n
        * (x : Localization.Away (DSMap.Mix2.tS t {i})))
        * (algebraMap R (Localization.Away (DSMap.Mix2.tS t {i})) (t i)) ^ n
      = (x : Localization.Away (DSMap.Mix2.tS t {i}))
        * (algebraMap R (Localization.Away (DSMap.Mix2.tS t {i})) (t j)) ^ n := by
    calc ((↑u : Localization.Away (DSMap.Mix2.tS t {i})) ^ n
            * (x : Localization.Away (DSMap.Mix2.tS t {i})))
            * (algebraMap R (Localization.Away (DSMap.Mix2.tS t {i})) (t i)) ^ n
        = (x : Localization.Away (DSMap.Mix2.tS t {i}))
            * ((↑u : Localization.Away (DSMap.Mix2.tS t {i})) ^ n
              * (algebraMap R (Localization.Away (DSMap.Mix2.tS t {i})) (t i)) ^ n) := by ring
      _ = (x : Localization.Away (DSMap.Mix2.tS t {i}))
            * (algebraMap R (Localization.Away (DSMap.Mix2.tS t {i})) (t j)) ^ n := by rw [hu_pow]
  have hy : ((↑u : Localization.Away (DSMap.Mix2.tS t {i})) ^ n
        * (y : Localization.Away (DSMap.Mix2.tS t {i})))
        * (algebraMap R (Localization.Away (DSMap.Mix2.tS t {i})) (t i)) ^ n
      = (y : Localization.Away (DSMap.Mix2.tS t {i}))
        * (algebraMap R (Localization.Away (DSMap.Mix2.tS t {i})) (t j)) ^ n := by
    calc ((↑u : Localization.Away (DSMap.Mix2.tS t {i})) ^ n
            * (y : Localization.Away (DSMap.Mix2.tS t {i})))
            * (algebraMap R (Localization.Away (DSMap.Mix2.tS t {i})) (t i)) ^ n
        = (y : Localization.Away (DSMap.Mix2.tS t {i}))
            * ((↑u : Localization.Away (DSMap.Mix2.tS t {i})) ^ n
              * (algebraMap R (Localization.Away (DSMap.Mix2.tS t {i})) (t i)) ^ n) := by ring
      _ = (y : Localization.Away (DSMap.Mix2.tS t {i}))
            * (algebraMap R (Localization.Away (DSMap.Mix2.tS t {i})) (t j)) ^ n := by rw [hu_pow]
  refine IsUnit.mul_right_cancel (hunit_i.pow n) ?_
  rw [hx, hy]
  calc (x : Localization.Away (DSMap.Mix2.tS t {i}))
        * (algebraMap R (Localization.Away (DSMap.Mix2.tS t {i})) (t j)) ^ n
      = (algebraMap R (Localization.Away (DSMap.Mix2.tS t {i})) (t j)) ^ n
        * (x : Localization.Away (DSMap.Mix2.tS t {i})) := mul_comm _ _
    _ = (algebraMap R (Localization.Away (DSMap.Mix2.tS t {i})) (t j)) ^ n
        * (y : Localization.Away (DSMap.Mix2.tS t {i})) := hn
    _ = (y : Localization.Away (DSMap.Mix2.tS t {i}))
        * (algebraMap R (Localization.Away (DSMap.Mix2.tS t {i})) (t j)) ^ n := mul_comm _ _

end Work.DSM5b
