import Mathlib
import Submission.Work.KT.D2.mZero
import Submission.Work.KT.D2.mZero_add
import Submission.Work.KT.D2.mZero_zero
import Submission.Work.KT.D2.mZero_conj
import Submission.Work.KT.Dim2.mvN_similar_zero

/-!
# `Work.KT.D2.mZero_descent` — `mZero` descends to a homomorphism `K₀(Kpair ℝ²) → ℤ`

The winding invariant `Work.KT.D2.mZero` is an invariant of idempotent matrices over `Kpair ℝ²`
satisfying the three defining relations of `K₀(Kpair ℝ²)`: additivity under block sum
(`Work.KT.D2.mZero_add`), invariance under Murray–von Neumann equivalence, and vanishing on
non-idempotents (by definition).  It therefore descends to an additive homomorphism
`K₀(Kpair ℝ²) →+ ℤ` with `m (cls P) = mZero y0 hy0 P`.

The only ingredient not already available as a primitive is Murray–von Neumann invariance, which is
assembled here from conjugation invariance (`Work.KT.D2.mZero_conj`), additivity, and the explicit
Morita matrix realising MvN equivalent idempotents as conjugate idempotents after adding zero blocks
(`Work.KT.Dim2.mvN_similar_zero`).
-/

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace Work.KT.D2

open Matrix
open Classical

noncomputable section

/-! ## 1. Adding a zero block does not change `mZero` -/

/-- `mZero` is unchanged by adding a zero block on the right. -/
theorem mZero_sum_zero_right_desc (y0 : Ball (Euc 2)) (hy0 : y0 ∈ bdry (Euc 2)) (k : ℕ)
    (P : Mat (Kpair (Euc 2))) (hP : P.IsIdem) :
    mZero y0 hy0 (Mat.sum P (⟨k, (0 : Matrix (Fin k) (Fin k) (Kpair (Euc 2)))⟩ :
        Mat (Kpair (Euc 2)))) = mZero y0 hy0 P := by
  have hz : Mat.IsIdem (⟨k, (0 : Matrix (Fin k) (Fin k) (Kpair (Euc 2)))⟩ :
      Mat (Kpair (Euc 2))) := by
    show (0 : Matrix (Fin k) (Fin k) (Kpair (Euc 2))) * 0 = 0
    simp
  rw [mZero_add y0 hy0 P _ hP hz, mZero_zero y0 hy0 k, add_zero]

/-- `mZero` is unchanged by adding a zero block on the left. -/
theorem mZero_zero_sum_left_desc (y0 : Ball (Euc 2)) (hy0 : y0 ∈ bdry (Euc 2)) (k : ℕ)
    (P : Mat (Kpair (Euc 2))) (hP : P.IsIdem) :
    mZero y0 hy0 (Mat.sum (⟨k, (0 : Matrix (Fin k) (Fin k) (Kpair (Euc 2)))⟩ :
        Mat (Kpair (Euc 2))) P) = mZero y0 hy0 P := by
  have hz : Mat.IsIdem (⟨k, (0 : Matrix (Fin k) (Fin k) (Kpair (Euc 2)))⟩ :
      Mat (Kpair (Euc 2))) := by
    show (0 : Matrix (Fin k) (Fin k) (Kpair (Euc 2))) * 0 = 0
    simp
  rw [mZero_add y0 hy0 _ P hz hP, mZero_zero y0 hy0 k, zero_add]

/-! ## 2. Murray–von Neumann invariance of `mZero` -/

/-- The winding invariant `mZero` only depends on the Murray–von Neumann class of an idempotent. -/
theorem mZero_mvN_free (y0 : Ball (Euc 2)) (hy0 : y0 ∈ bdry (Euc 2))
    (p q : Mat (Kpair (Euc 2))) (hp : p.IsIdem) (hq : q.IsIdem) (h : p.MvN q) :
    mZero y0 hy0 p = mZero y0 hy0 q := by
  obtain ⟨a, b, hba, hab⟩ := h
  obtain ⟨u, hu, hudu⟩ := Work.KT.Dim2.mvN_similar_zero p.2 q.2 hp hq a b hba hab
  have hDq : Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (0 : Matrix (Fin p.1) (Fin p.1) (Kpair (Euc 2))) 0 0 q.2)
      * Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (0 : Matrix (Fin p.1) (Fin p.1) (Kpair (Euc 2))) 0 0 q.2)
      = Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (0 : Matrix (Fin p.1) (Fin p.1) (Kpair (Euc 2))) 0 0 q.2) := by
    have hBB : Matrix.fromBlocks (0 : Matrix (Fin p.1) (Fin p.1) (Kpair (Euc 2))) 0 0 q.2
        * Matrix.fromBlocks (0 : Matrix (Fin p.1) (Fin p.1) (Kpair (Euc 2))) 0 0 q.2
        = Matrix.fromBlocks (0 : Matrix (Fin p.1) (Fin p.1) (Kpair (Euc 2))) 0 0 q.2 := by
      rw [Matrix.fromBlocks_multiply]
      simp only [Matrix.zero_mul, Matrix.mul_zero, zero_add]
      rw [hq]
    rw [← Matrix.coe_reindexRingEquiv (R := Kpair (Euc 2)) (e := finSumFinEquiv), ← map_mul, hBB]
  have hconj := mZero_conj y0 hy0 (p.1 + q.1)
    (Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (0 : Matrix (Fin p.1) (Fin p.1) (Kpair (Euc 2))) 0 0 q.2)) hDq u u hu hu
  rw [hudu] at hconj
  have hpadR : mZero y0 hy0 (⟨p.1 + q.1,
        Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks p.2 0 0 0)⟩ :
        Mat (Kpair (Euc 2))) = mZero y0 hy0 p :=
    mZero_sum_zero_right_desc y0 hy0 q.1 p hp
  have hpadL : mZero y0 hy0 (⟨p.1 + q.1,
        Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 0 0 0 q.2)⟩ :
        Mat (Kpair (Euc 2))) = mZero y0 hy0 q :=
    mZero_zero_sum_left_desc y0 hy0 p.1 q hq
  rw [← hpadR, hconj, hpadL]

/-! ## 3. Descent to `K₀` -/

theorem mZero_descent (y0 : Work.KT.Ball (EuclideanSpace ℝ (Fin 2)))
    (hy0 : y0 ∈ Work.KT.bdry (EuclideanSpace ℝ (Fin 2))) :
    ∃ m : Work.KT.K0 (Work.KT.Kpair (EuclideanSpace ℝ (Fin 2))) →+ ℤ,
      ∀ P : Work.KT.Mat (Work.KT.Kpair (EuclideanSpace ℝ (Fin 2))),
        m (Work.KT.cls P) = Work.KT.D2.mZero y0 hy0 P := by
  classical
  have hker : Work.KT.K0Rel (Kpair (Euc 2)) ≤
      (FreeAbelianGroup.lift (fun P : Mat (Kpair (Euc 2)) => mZero y0 hy0 P)).ker := by
    rw [Work.KT.K0Rel, AddSubgroup.closure_le]
    rintro x ((⟨p, q, hp, hq, rfl⟩ | ⟨p, q, hp, hq, hmv, rfl⟩) | ⟨p, hp, rfl⟩)
    · -- block sums
      simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub,
        FreeAbelianGroup.lift_apply_of]
      rw [mZero_add y0 hy0 p q hp hq]
      abel
    · -- Murray–von Neumann equivalence
      simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub,
        FreeAbelianGroup.lift_apply_of]
      rw [mZero_mvN_free y0 hy0 p q hp hq hmv]
      abel
    · -- non-idempotents
      simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, FreeAbelianGroup.lift_apply_of]
      exact mZero_of_not_idem y0 hy0 p hp
  refine ⟨QuotientAddGroup.lift (Work.KT.K0Rel (Kpair (Euc 2)))
    (FreeAbelianGroup.lift (fun P : Mat (Kpair (Euc 2)) => mZero y0 hy0 P)) hker, ?_⟩
  intro P
  rw [Work.KT.cls, QuotientAddGroup.lift_mk, FreeAbelianGroup.lift_apply_of]

end

end Work.KT.D2
