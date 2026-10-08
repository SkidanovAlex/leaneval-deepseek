import Mathlib
import Submission.Work.L2F.Torus.commute_iff_mem_algSpan
import Submission.Work.L2F.Mat2.trace_eq_zero_of_sq_eq_neg_one
import Submission.Work.L2F.Mat2.det_smul_one_add_smul

namespace Work.L2F.Props

/-- The sign dichotomy for a lift `S : GL(2,F)` of an involution of `PGL(2,F)` commuting with the lift `T ∈ SL(2,F)` of an involution `t ∈ L₂(F)`: if in fact `S` *commutes* with `T` (`T² = -1`, `(2:F) ≠ 0`), then `det S` is a square.
Reason: `T` is traceless (`tr T = 0`, from `T² = -1` and `det T = 1`) with `det T = 1 ≠ 0`, so `S` lies in the algebra `F·1 + F·T`; write `S = a • 1 + b • T`. Then `S * S = (a² - b²) • 1 + (2ab) • T = lam • 1`, and taking traces (`tr T = 0`, `h2`) gives `a² - b² = lam`, whence `2ab = 0`, so `a = 0` or `b = 0`; and `det S = a² + b²·det T = a² + b²`, which is `a²` or `b²`, a square. -/
theorem isSquare_det_of_commute_sq_neg_one (F : Type*) [Field F] (h2 : (2 : F) ≠ 0)
    (T : Matrix.SpecialLinearGroup (Fin 2) F) (S : Matrix.GeneralLinearGroup (Fin 2) F)
    (lam : F)
    (hT : (T : Matrix (Fin 2) (Fin 2) F) * (T : Matrix (Fin 2) (Fin 2) F) = -1)
    (hS : (S : Matrix (Fin 2) (Fin 2) F) * (S : Matrix (Fin 2) (Fin 2) F) = lam • 1)
    (hcomm : Matrix.SpecialLinearGroup.toGL T * S = S * Matrix.SpecialLinearGroup.toGL T) :
    IsSquare ((S : Matrix (Fin 2) (Fin 2) F).det) := by
  -- `T` has determinant `1` (it lies in `SL(2,F)`), hence trace `0` (from `T * T = -1`).
  have hdetT : (T : Matrix (Fin 2) (Fin 2) F).det = 1 := Matrix.SpecialLinearGroup.det_coe T
  have htrT : (T : Matrix (Fin 2) (Fin 2) F).trace = 0 :=
    Work.L2F.Mat2.trace_eq_zero_of_sq_eq_neg_one F _ hdetT hT
  -- Rewrite `T * T = -1` as `T * T = (-1) • 1`, the shape expected by `commute_iff_mem_algSpan`.
  have hT2 : (T : Matrix (Fin 2) (Fin 2) F) * (T : Matrix (Fin 2) (Fin 2) F) =
      (-1 : F) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    rw [hT]; simp
  -- `T ≠ 0`, since `T * T = -1 ≠ 0`.
  have hTm_ne : (T : Matrix (Fin 2) (Fin 2) F) ≠ 0 := by
    intro h
    have hz : (T : Matrix (Fin 2) (Fin 2) F) * (T : Matrix (Fin 2) (Fin 2) F) = 0 := by
      rw [h, Matrix.mul_zero]
    rw [hz] at hT
    exact one_ne_zero (neg_eq_zero.mp hT.symm)
  -- Coerce the `GL`-commutation hypothesis to a matrix-level commutation.
  have hcommm : (S : Matrix (Fin 2) (Fin 2) F) * (T : Matrix (Fin 2) (Fin 2) F) =
      (T : Matrix (Fin 2) (Fin 2) F) * (S : Matrix (Fin 2) (Fin 2) F) := by
    have h := congrArg (fun x : Matrix.GeneralLinearGroup (Fin 2) F =>
      (x : Matrix (Fin 2) (Fin 2) F)) hcomm
    simpa [Matrix.GeneralLinearGroup.coe_mul] using h.symm
  -- `T` has non-zero determinant, so its commutant is the algebra `F·1 + F·T`: `S = a • 1 + b • T`.
  have hmem : (S : Matrix (Fin 2) (Fin 2) F) ∈
      Work.L2F.Torus.algSpan F (T : Matrix (Fin 2) (Fin 2) F) :=
    (Work.L2F.Torus.commute_iff_mem_algSpan F h2 _ _ (-1) htrT hT2
      (neg_ne_zero.mpr one_ne_zero)).mp hcommm
  obtain ⟨a, b, hab⟩ := hmem
  -- Expand `S * S = (a² - b²) • 1 + (2ab) • T`.
  have hexpand : (S : Matrix (Fin 2) (Fin 2) F) * (S : Matrix (Fin 2) (Fin 2) F) =
      (a ^ 2 - b ^ 2) • (1 : Matrix (Fin 2) (Fin 2) F) +
        (2 * a * b) • (T : Matrix (Fin 2) (Fin 2) F) := by
    rw [hab]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, hT2]
    module
  -- Combine with `S * S = lam • 1` and move `lam • 1` to the left.
  have hbase : (a ^ 2 - b ^ 2) • (1 : Matrix (Fin 2) (Fin 2) F) +
      (2 * a * b) • (T : Matrix (Fin 2) (Fin 2) F) = lam • (1 : Matrix (Fin 2) (Fin 2) F) := by
    rw [← hexpand, hS]
  have hE : (a ^ 2 - b ^ 2 - lam) • (1 : Matrix (Fin 2) (Fin 2) F) +
      (2 * a * b) • (T : Matrix (Fin 2) (Fin 2) F) = 0 := by
    have h' := hbase
    rw [sub_smul]
    rw [← h']
    abel
  -- Taking traces kills the `T`-part, giving `a² - b² = lam`.
  have hP : a ^ 2 - b ^ 2 - lam = 0 := by
    have htr := congrArg Matrix.trace hE
    simp only [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_zero, Matrix.trace_one,
      Fintype.card_fin, htrT, smul_eq_mul, mul_zero, add_zero] at htr
    rcases mul_eq_zero.mp htr with h | h
    · exact h
    · exact absurd h h2
  -- Hence the `T`-part vanishes: `(2ab) • T = 0`, and `T ≠ 0` forces `2ab = 0`.
  have hQ : 2 * a * b = 0 := by
    have hE' : (2 * a * b) • (T : Matrix (Fin 2) (Fin 2) F) = 0 := by
      have h := hE
      rw [hP] at h
      simpa using h
    rcases smul_eq_zero.mp hE' with h | h
    · exact h
    · exact absurd h hTm_ne
  have hab0 : a * b = 0 := by
    have hq : (2 : F) * (a * b) = 0 := by rw [← mul_assoc]; exact hQ
    exact (mul_eq_zero.mp hq).resolve_left h2
  -- `det S = a² + b²·det T = a² + b²` (using `tr T = 0`, `det T = 1`).
  have hdetS : (S : Matrix (Fin 2) (Fin 2) F).det = a ^ 2 + b ^ 2 := by
    rw [hab, Work.L2F.Mat2.det_smul_one_add_smul F (T : Matrix (Fin 2) (Fin 2) F) a b,
      htrT, hdetT]
    ring
  rw [hdetS]
  -- `a * b = 0` means `S` is a scalar multiple of `1` or of `T`, so `a² + b²` is `a²` or `b²`.
  rcases mul_eq_zero.mp hab0 with ha | hb
  · exact ⟨b, by rw [ha]; ring⟩
  · exact ⟨a, by rw [hb]; ring⟩

end Work.L2F.Props
