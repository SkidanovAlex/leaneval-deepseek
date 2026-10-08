import Mathlib
import Submission.Work.L2F.Mat2.sq_eq_trace_smul_sub_det
import Submission.Work.L2F.Mat2.commute_entries
import Submission.Work.L2F.Mat2.det_smul_one_add_smul

namespace Work.L2F.Mat2

/-- The commutant of a non-scalar `2×2` matrix `S` with `S * S = lam • 1` (`lam ≠ 0`) is the
two-dimensional algebra `F·1 + F·S`: any `Y` commuting with `S` is `a • 1 + b • S`.

This is the standard fact that a matrix whose minimal polynomial has degree equal to its size is
cyclic.  It holds in every characteristic (the analogous Lemma 2.13 computation in the odd
characteristic case needed `(2 : F) ≠ 0`; here nothing is divided by `2` except in the trivial
case `S = diag(p, -p)`, where `(2 : F) ≠ 0` follows from `S` being non-scalar). -/
theorem commutant_sq_scalar (F : Type*) [Field F] (S Y : Matrix (Fin 2) (Fin 2) F) (lam : F)
    (hS : S * S = lam • 1) (hlam : lam ≠ 0) (hns : ∀ c : F, S ≠ c • 1)
    (hcomm : Y * S = S * Y) :
    ∃ a b : F, Y = a • 1 + b • S := by
  -- The hypothesis `hlam : lam ≠ 0` is in fact not needed for the commutant computation
  -- (`tr S = 0` and non-scalarity of `S` already pin down the centralizer); record it so that
  -- the argument below can refer to it.
  have _hlam : lam ≠ 0 := hlam
  -- Cayley–Hamilton `S * S = tr S • S - det S • 1` together with `S * S = lam • 1` shows that
  -- `tr S • S` is scalar; non-scalarity of `S` forces `tr S = 0`.
  have htr : S.trace = 0 := by
    by_contra h
    have hCH := sq_eq_trace_smul_sub_det F S
    rw [hS, eq_sub_iff_add_eq] at hCH
    have h1 : S.trace • S = (lam + S.det) • 1 := by
      rw [add_smul]; exact hCH.symm
    exact hns ((S.trace)⁻¹ * (lam + S.det)) (by
      calc S = (S.trace)⁻¹ • (S.trace • S) := by rw [smul_smul, inv_mul_cancel₀ h, one_smul]
        _ = (S.trace)⁻¹ • ((lam + S.det) • 1) := by rw [h1]
        _ = ((S.trace)⁻¹ * (lam + S.det)) • 1 := by rw [smul_smul])
  -- With `tr S = 0` we have `S 1 1 = - S 0 0`, so `S = !![p, q; r, -p]`.
  have hX11 : S 1 1 = - S 0 0 := by
    have h := htr
    rw [Matrix.trace_fin_two] at h
    exact eq_neg_of_add_eq_zero_right h
  -- Entry relations from `Y * S = S * Y` for the traceless matrix `S`.
  obtain ⟨hC, hD, hE⟩ := commute_entries F S Y htr hcomm
  -- We solve for `b` using whichever of `q = S 0 1`, `r = S 1 0`, `2 * p = 2 * S 0 0` is nonzero.
  by_cases hq : S 0 1 = 0
  · by_cases hr : S 1 0 = 0
    · -- Case `q = r = 0`: `S = diag(p, -p)`; non-scalarity gives `2 * p ≠ 0`.
      have h2p : 2 * S 0 0 ≠ 0 := by
        intro h2
        have h2' : S 0 0 + S 0 0 = 0 := by rw [← two_mul]; exact h2
        have hself : S 0 0 = - S 0 0 := by rw [eq_neg_iff_add_eq_zero]; exact h2'
        apply hns (S 0 0)
        ext i j
        fin_cases i <;> fin_cases j
        · simp [Matrix.smul_apply]
        · simp [Matrix.smul_apply, hq]
        · simp [Matrix.smul_apply, hr]
        · simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
          exact hX11.trans hself.symm
      have hY01 : Y 0 1 = 0 := by
        have h := hD
        rw [hq, zero_mul] at h
        exact (mul_eq_zero.mp h.symm).resolve_left h2p
      have hY10 : Y 1 0 = 0 := by
        have h := hE
        rw [hr, zero_mul] at h
        exact (mul_eq_zero.mp h.symm).resolve_left h2p
      refine ⟨Y 0 0 - ((Y 0 0 - Y 1 1) / (2 * S 0 0)) * S 0 0,
        (Y 0 0 - Y 1 1) / (2 * S 0 0), ?_⟩
      have hb2 : 2 * (((Y 0 0 - Y 1 1) / (2 * S 0 0)) * S 0 0) = Y 0 0 - Y 1 1 := by
        rw [show 2 * (((Y 0 0 - Y 1 1) / (2 * S 0 0)) * S 0 0)
            = ((Y 0 0 - Y 1 1) / (2 * S 0 0)) * (2 * S 0 0) from by ring]
        exact div_mul_cancel₀ _ h2p
      ext i j
      fin_cases i <;> fin_cases j
      · simp [Matrix.add_apply, Matrix.smul_apply]
      · simp [Matrix.add_apply, Matrix.smul_apply, hq]
        exact hY01
      · simp [Matrix.add_apply, Matrix.smul_apply, hr]
        exact hY10
      · simp [Matrix.add_apply, Matrix.smul_apply]
        rw [hX11]
        rw [show (Y 0 0 - (Y 0 0 - Y 1 1) / (2 * S 0 0) * S 0 0)
              + (Y 0 0 - Y 1 1) / (2 * S 0 0) * (- S 0 0)
            = Y 0 0 - 2 * (((Y 0 0 - Y 1 1) / (2 * S 0 0)) * S 0 0) from by ring]
        rw [hb2]
        ring
    · -- Case `q = 0`, `r ≠ 0`: solve with `b = Y 1 0 / S 1 0`.
      have hY01 : Y 0 1 = 0 := by
        have h := hC
        rw [hq, zero_mul] at h
        exact (mul_eq_zero.mp h).resolve_right hr
      refine ⟨Y 0 0 - (Y 1 0 / S 1 0) * S 0 0, Y 1 0 / S 1 0, ?_⟩
      have hb10 : (Y 1 0 / S 1 0) * S 1 0 = Y 1 0 := div_mul_cancel₀ _ hr
      have hb2 : 2 * ((Y 1 0 / S 1 0) * S 0 0) = Y 0 0 - Y 1 1 := by
        apply mul_right_cancel₀ hr
        rw [mul_comm (Y 0 0 - Y 1 1) (S 1 0), hE]
        field_simp
      ext i j
      fin_cases i <;> fin_cases j
      · simp [Matrix.add_apply, Matrix.smul_apply]
      · simp [Matrix.add_apply, Matrix.smul_apply, hq]
        exact hY01
      · simp [Matrix.add_apply, Matrix.smul_apply]
        exact hb10.symm
      · simp [Matrix.add_apply, Matrix.smul_apply]
        rw [hX11]
        rw [show (Y 0 0 - Y 1 0 / S 1 0 * S 0 0) + Y 1 0 / S 1 0 * (- S 0 0)
            = Y 0 0 - 2 * ((Y 1 0 / S 1 0) * S 0 0) from by ring]
        rw [hb2]
        ring
  · -- Case `q ≠ 0`: solve with `b = Y 0 1 / S 0 1`.
    refine ⟨Y 0 0 - (Y 0 1 / S 0 1) * S 0 0, Y 0 1 / S 0 1, ?_⟩
    have hb01 : (Y 0 1 / S 0 1) * S 0 1 = Y 0 1 := div_mul_cancel₀ _ hq
    have hb10 : (Y 0 1 / S 0 1) * S 1 0 = Y 1 0 := by
      rw [div_mul_eq_mul_div, hC, mul_div_cancel_left₀ _ hq]
    have hb2 : 2 * ((Y 0 1 / S 0 1) * S 0 0) = Y 0 0 - Y 1 1 := by
      apply mul_right_cancel₀ hq
      rw [mul_comm (Y 0 0 - Y 1 1) (S 0 1), hD]
      field_simp
    ext i j
    fin_cases i <;> fin_cases j
    · simp [Matrix.add_apply, Matrix.smul_apply]
    · simp [Matrix.add_apply, Matrix.smul_apply]
      exact hb01.symm
    · simp [Matrix.add_apply, Matrix.smul_apply]
      exact hb10.symm
    · simp [Matrix.add_apply, Matrix.smul_apply]
      rw [hX11]
      rw [show (Y 0 0 - Y 0 1 / S 0 1 * S 0 0) + Y 0 1 / S 0 1 * (- S 0 0)
          = Y 0 0 - 2 * ((Y 0 1 / S 0 1) * S 0 0) from by ring]
      rw [hb2]
      ring

end Work.L2F.Mat2
