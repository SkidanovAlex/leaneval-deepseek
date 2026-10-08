import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.Conic.exists_sq_add_sq

namespace Work.L2F.Involution

/-- There is `w ∈ SL(2,F)` with `w * z * w⁻¹ = -z` and `w * w = -1`: the matrices
`!![a, b; b, -a]` with `a² + b² = -1` all satisfy `w * z = -z * w` and `w * w = (a²+b²) • 1 = -1`,
and such `a, b` exist by `exists_sq_add_sq` applied to `c = -1` (they also have `det w = 1`). -/
theorem exists_inverting_z (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0) :
    ∃ w : Matrix.SpecialLinearGroup (Fin 2) F,
      w * Work.L2F.z F * w⁻¹ = Work.L2F.negOne F * Work.L2F.z F ∧
        w * w = Work.L2F.negOne F := by
  -- `a² + b² = -1` for suitable `a, b`.
  obtain ⟨a, b, hab⟩ := Work.L2F.Conic.exists_sq_add_sq F h2 (-1)
  -- `W = !![a, b; b, -a]` has determinant `-(a²+b²) = 1`.
  have hdet : (!![a, b; b, -a] : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    rw [Matrix.det_fin_two]
    show a * (-a) - b * b = 1
    linear_combination -hab
  -- Matrix level identities: `W` anticommutes with `!![0,1;-1,0]` and `W² = (a²+b²) • 1`.
  have hAZ : (!![a, b; b, -a] : Matrix (Fin 2) (Fin 2) F) * !![0, 1; -1, 0] =
      - (!![0, 1; -1, 0] * !![a, b; b, -a]) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hAA : (!![a, b; b, -a] : Matrix (Fin 2) (Fin 2) F) * !![a, b; b, -a] =
      (a ^ 2 + b ^ 2) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    rw [Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring
  let W : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![a, b; b, -a], hdet⟩
  have hW : (W : Matrix (Fin 2) (Fin 2) F) = !![a, b; b, -a] := rfl
  refine ⟨W, ?_, ?_⟩
  · -- `W * z = -z * W` is `W * z = (-1) * z * W` at the matrix level (`hAZ`).
    have hmain : W * Work.L2F.z F = Work.L2F.negOne F * Work.L2F.z F * W := by
      apply Subtype.ext
      show (W : Matrix (Fin 2) (Fin 2) F) * !![0, 1; -1, 0] =
        (-1 : Matrix (Fin 2) (Fin 2) F) * !![0, 1; -1, 0] * (W : Matrix (Fin 2) (Fin 2) F)
      rw [hW, neg_one_mul, neg_mul]
      exact hAZ
    calc W * Work.L2F.z F * W⁻¹
        = (Work.L2F.negOne F * Work.L2F.z F * W) * W⁻¹ := by rw [hmain]
      _ = Work.L2F.negOne F * Work.L2F.z F := by group
  · -- `W² = (a²+b²) • 1 = (-1) • 1 = -1`.
    apply Subtype.ext
    show (W : Matrix (Fin 2) (Fin 2) F) * (W : Matrix (Fin 2) (Fin 2) F) = -1
    rw [hW, hAA, hab]
    simp

end Work.L2F.Involution
