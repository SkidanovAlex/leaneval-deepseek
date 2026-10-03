import Mathlib
import Submission.Work.ORP311.P311Defs
import Submission.Work.ORP311.exists_common_denom

set_option synthInstance.maxHeartbeats 200000

namespace Work.ORP311

theorem map_numG_denom {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] (N : Subgroup G) (t : G) {n : ℕ} (A : Matrix (Fin n) (Fin n) (Work.ORP311.concreteEnvelope G).U) (e : ↥(Work.ORVonNeumann.groupVonNeumann ↥N)) (B : Matrix (Fin n) (Fin n) ↥(Work.ORVonNeumann.groupVonNeumann ↥N)) (hB : ∀ i j, Work.ORP311.P311.numG G (Work.ORP311.P311.PhiN N e) * A i j = Work.ORP311.P311.numG G (Work.ORP311.P311.PhiN N (B i j))) : (Matrix.scalar (Fin n) (Work.ORP311.P311.PhiN N e) + B.map (Work.ORP311.P311.PhiN N) * Matrix.scalar (Fin n) (⟨Work.ORVonNeumann.Rep.leftRegOp t, Work.ORVonNeumann.Rep.leftRegOp_mem_groupVonNeumann t⟩ : ↥(Work.ORVonNeumann.groupVonNeumann G))).map (Work.ORP311.P311.numG G) = Matrix.scalar (Fin n) (Work.ORP311.P311.numG G (Work.ORP311.P311.PhiN N e)) * (1 + A * Matrix.scalar (Fin n) (Work.ORP311.P311.numG G (⟨Work.ORVonNeumann.Rep.leftRegOp t, Work.ORVonNeumann.Rep.leftRegOp_mem_groupVonNeumann t⟩ : ↥(Work.ORVonNeumann.groupVonNeumann G)))) := by
  -- Everything is entrywise: expand the matrix operations and reduce the
  -- `Fin n` sums, which are supported on the diagonal because
  -- `Matrix.scalar n a = Matrix.diagonal (fun _ => a)`.
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.one_apply,
    Matrix.scalar_apply, Matrix.diagonal_apply, map_add, map_mul,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, mul_ite, ite_mul,
    zero_mul, mul_zero, ↓reduceIte]
  -- Split on `i = j` and use the hypothesis `hB` to replace the `(i, j)` entry of
  -- `(B.map Φ_N).map numG` by `numG (Φ_N e) * A i j`.
  by_cases h : i = j
  · simp only [if_pos h, mul_add, mul_one]
    rw [← hB i j]
    simp only [mul_assoc]
  · simp only [if_neg h, map_zero, mul_add]
    rw [← hB i j]
    simp only [mul_zero, zero_add, mul_assoc]

end Work.ORP311
