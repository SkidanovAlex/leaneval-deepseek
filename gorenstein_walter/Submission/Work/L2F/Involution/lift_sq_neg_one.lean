import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.Mat2.pslMap_eq_one_iff
import Submission.Work.L2F.Mat2.sq_eq_one_of_mem_sl

namespace Work.L2F.Involution

/-- An involution `t` of `PSL(2,F)` (`F` of odd characteristic) lifts to `x ∈ SL(2,F)` with
`x² = -1`.  Proof: pick any lift `x` of `t` (surjectivity of `pslMap`); `t² = 1` gives
`pslMap (x * x) = 1`, so `x * x = 1` or `x * x = -1` (`pslMap_eq_one_iff`); the first case forces
`x = ±1` (`sq_eq_one_of_mem_sl`), hence `t = 1`, contradicting `orderOf t = 2`. -/
theorem lift_sq_neg_one (F : Type*) [Field F] (h2 : (2 : F) ≠ 0)
    (t : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) (ht : orderOf t = 2) :
    ∃ x : Matrix.SpecialLinearGroup (Fin 2) F, Work.PSL2.pslMap F x = t ∧
      (x : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F) = -1 := by
  -- `pslMap` is the quotient map modulo the centre, hence surjective: lift `t` to `x ∈ SL(2,F)`.
  have hsurj : Function.Surjective (Work.PSL2.pslMap F) := QuotientGroup.mk'_surjective _
  obtain ⟨x, hx⟩ := hsurj t
  -- `orderOf t = 2` gives `t ^ 2 = 1`, hence `pslMap (x * x) = 1`.
  have ht2 : t ^ 2 = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht] at this
  have hsq : Work.PSL2.pslMap F (x * x) = 1 := by rw [map_mul, hx, ← pow_two, ht2]
  refine ⟨x, hx, ?_⟩
  -- `t ≠ 1` because `orderOf t = 2`.
  have hne : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    exact absurd ht (by norm_num)
  -- The kernel of `pslMap` is `{1, -1}`, so `x * x = 1` or `x * x = -1`.
  rcases (Work.L2F.Mat2.pslMap_eq_one_iff F h2 (x * x)).mp hsq with hsq1 | hsq1
  · -- `x * x = 1` forces `x = ±1`, hence `t = 1`: excluded.
    rcases Work.L2F.Mat2.sq_eq_one_of_mem_sl F h2 x (by
        have h := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) hsq1
        rw [Matrix.SpecialLinearGroup.coe_mul] at h
        simpa using h) with hx1 | hx1
    · exact absurd (by rw [← hx, hx1, map_one] : t = 1) hne
    · exact absurd ((Work.L2F.Mat2.pslMap_eq_one_iff F h2 x).mpr (Or.inr hx1))
        (by rw [hx]; exact hne)
  · -- `x * x = -1` as elements of `SL(2,F)`, i.e. the matrix product is `-1`.
    have h := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) hsq1
    rw [Matrix.SpecialLinearGroup.coe_mul] at h
    simpa [Work.L2F.negOne] using h

end Work.L2F.Involution
