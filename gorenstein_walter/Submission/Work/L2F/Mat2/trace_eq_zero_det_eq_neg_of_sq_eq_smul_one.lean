import Mathlib
import Submission.Work.L2F.Mat2.sq_eq_trace_smul_sub_det

namespace Work.L2F.Mat2

/-- **Trace and determinant of a non-scalar square root of a scalar matrix.**  If a `2×2` matrix
`S` over a field satisfies `S * S = lam • 1` and is not a scalar matrix, then `tr S = 0` and
`det S = -lam`.

Proof: Cayley–Hamilton (`Work.L2F.Mat2.sq_eq_trace_smul_sub_det`) reads
`S * S = S.trace • S - S.det • 1`; comparing with `lam • 1` gives
`S.trace • S = (lam + S.det) • 1`.  If `S.trace ≠ 0` this exhibits `S` as a scalar matrix,
contradicting the hypothesis, so `S.trace = 0`; Cayley–Hamilton then reads
`S * S = -(S.det) • 1`, and comparing with `lam • 1` entrywise gives `S.det = -lam`.

Note `lam ≠ 0` is *not* needed (both statements are also correct for `lam = 0`). -/
theorem trace_eq_zero_det_eq_neg_of_sq_eq_smul_one (F : Type*) [Field F]
    (S : Matrix (Fin 2) (Fin 2) F) (lam : F)
    (hS : S * S = lam • 1) (hns : ∀ c : F, S ≠ c • 1) :
    S.trace = 0 ∧ S.det = -lam := by
  -- Cayley–Hamilton: `S * S = S.trace • S - S.det • 1`; compare with `S * S = lam • 1`.
  have hCH := sq_eq_trace_smul_sub_det F S
  rw [hCH] at hS
  have hkey : S.trace • S = (lam + S.det) • 1 := by
    rw [sub_eq_iff_eq_add] at hS
    rw [hS, add_smul]
  -- If `S.trace ≠ 0`, then `S` is a scalar matrix, contradicting `hns`.
  have htrace : S.trace = 0 := by
    by_contra h
    have hc : S = (S.trace⁻¹ * (lam + S.det)) • 1 := by
      calc S = S.trace⁻¹ • (S.trace • S) := by
                rw [smul_smul, inv_mul_cancel₀ h, one_smul]
           _ = S.trace⁻¹ • ((lam + S.det) • 1) := by rw [hkey]
           _ = (S.trace⁻¹ * (lam + S.det)) • 1 := by rw [smul_smul]
    exact hns _ hc
  -- With `S.trace = 0`, the equation `(lam + S.det) • 1 = 0` gives `S.det = -lam`.
  have hdet : S.det = -lam := by
    have h2 := hkey
    rw [htrace] at h2
    simp only [zero_smul] at h2
    have h3 := congrFun (congrFun h2.symm 0) 0
    simp at h3
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact h3
  exact ⟨htrace, hdet⟩

end Work.L2F.Mat2
