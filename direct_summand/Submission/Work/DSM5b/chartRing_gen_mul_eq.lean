import Mathlib
import Submission.Work.DSM5b.CycleDefs

namespace Work.DSM5b

open DSMap DSMap.Mix2

universe a

/-- The product of the generators over a singleton chart is the generator: `tS t {i} = t i`. -/
lemma tS_singleton_eq {R : Type a} [CommRing R] {ι : Type a} (t : ι → R) (i : ι) :
    tS t {i} = t i :=
  Finset.prod_singleton t i

theorem chartRing_gen_mul_eq {R : Type a} [CommRing R] {ι : Type a} [DecidableEq ι]
    (t : ι → R) (i l : ι) :
    ∃ u : ↥(DSMap.Mix2.chartRing t {i}),
      (u : Localization.Away (DSMap.Mix2.tS t {i})) * algebraMap R _ (t i)
        = algebraMap R _ (t l) := by
  obtain ⟨σ, hσ⟩ :
      ∃ σ : (Localization.Away (DSMap.Mix2.tS t {i}))ˣ,
        (↑σ : Localization.Away (DSMap.Mix2.tS t {i}))
          = algebraMap R (Localization.Away (DSMap.Mix2.tS t {i})) (t i) :=
    ⟨(IsLocalization.Away.algebraMap_isUnit
        (S := Localization.Away (DSMap.Mix2.tS t {i})) (DSMap.Mix2.tS t {i})).unit,
      by rw [IsUnit.unit_spec, tS_singleton_eq t i]⟩
  refine ⟨⟨↑(σ⁻¹) * algebraMap R (Localization.Away (DSMap.Mix2.tS t {i})) (t l), ?_⟩, ?_⟩
  · apply Algebra.subset_adjoin
    refine ⟨i, Finset.mem_singleton_self i, l, ?_⟩
    show (↑(σ⁻¹) * algebraMap R (Localization.Away (DSMap.Mix2.tS t {i})) (t l))
          * algebraMap R (Localization.Away (DSMap.Mix2.tS t {i})) (t i)
        = algebraMap R (Localization.Away (DSMap.Mix2.tS t {i})) (t l)
    rw [← hσ]
    rw [mul_assoc, mul_comm (algebraMap R (Localization.Away (DSMap.Mix2.tS t {i})) (t l)),
      ← mul_assoc, Units.inv_mul, one_mul]
  · show (↑(σ⁻¹) * algebraMap R (Localization.Away (DSMap.Mix2.tS t {i})) (t l))
          * algebraMap R (Localization.Away (DSMap.Mix2.tS t {i})) (t i)
        = algebraMap R (Localization.Away (DSMap.Mix2.tS t {i})) (t l)
    rw [← hσ]
    rw [mul_assoc, mul_comm (algebraMap R (Localization.Away (DSMap.Mix2.tS t {i})) (t l)),
      ← mul_assoc, Units.inv_mul, one_mul]

end Work.DSM5b
