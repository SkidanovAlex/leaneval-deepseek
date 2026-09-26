import Mathlib
import Submission.Work.SGsep.hand.HandDefs2
import Submission.Work.SGsep.PairAux
import Submission.Work.SGsep.det_trace_conj
import Submission.Work.SGsep.hand.conj_pow_invMat

namespace Work.SGsep.hand

open Work.SG Work.SG.Data Work.SGsep.Hand Work.SGsep.Hand.Data

/-! ### Bridges between the flat order `M3.ord` / determinant and the matrix ones

`M3.ord A` is the *truncated* order of `A`: the first `k + 1 ≤ 12` with `A ^ (k+1) = 1`,
and `0` if there is none; `mOrd` is the genuine multiplicative order of an integer matrix
(`0` if there is none).  The two therefore agree whenever `M3.ord` is nonzero, and both
are invariant under conjugation by a unimodular integer matrix. -/

/-- `A.toIMat ^ m = 1` says the same thing as `A.pow m = M3.one`. -/
theorem toIMat_pow_eq_one_iff (A : M3) (m : ℕ) : A.toIMat ^ m = 1 ↔ A.pow m = M3.one := by
  rw [← PSep.toIMat_pow, ← M3.toIMat_one]
  exact M3.toIMat_injective.eq_iff

/-- Conjugation by a unimodular integer matrix preserves the flat powers: `B.pow m = 1` iff
`A.pow m = 1` when `B.toIMat = U * A.toIMat * invMat U`. -/
theorem pow_conj_iff {A B : M3} {U : IMat} (hU : IsUnit U.det)
    (hB : B.toIMat = U * A.toIMat * invMat U) (m : ℕ) :
    B.pow m = M3.one ↔ A.pow m = M3.one := by
  rw [← toIMat_pow_eq_one_iff B m, ← toIMat_pow_eq_one_iff A m, hB]
  exact (conj_pow_invMat hU A.toIMat).2 m

/-- The flat order is invariant under conjugation by a unimodular matrix: both sides are
`(List.find? ...).map (· + 1) |>.getD 0` for the *same* predicate. -/
theorem ord_conj {A B : M3} {U : IMat} (hU : IsUnit U.det)
    (hB : B.toIMat = U * A.toIMat * invMat U) : B.ord = A.ord := by
  have hp : (fun k : ℕ => B.pow (k + 1) == M3.one) =
      (fun k : ℕ => A.pow (k + 1) == M3.one) := by
    funext k
    exact Bool.eq_iff_iff.mpr
      (by rw [beq_iff_eq, beq_iff_eq]; exact pow_conj_iff hU hB (k + 1))
  unfold M3.ord
  rw [hp]

/-- The flat determinant is invariant under conjugation by a unimodular matrix. -/
theorem det_conj {A B : M3} {U : IMat} (hU : IsUnit U.det)
    (hB : B.toIMat = U * A.toIMat * invMat U) : B.det = A.det := by
  rw [← M3.toIMat_det B, hB, (Work.SGsep.det_trace_conj hU A.toIMat).1, M3.toIMat_det A]

/-- The flat order `M3.ord` is the multiplicative order `mOrd` of the integer matrix (when it is
nonzero), and both order and determinant are invariant under conjugation by a unimodular matrix. -/
theorem ord_bridges :
    (∀ (A : M3), 1 ≤ A.ord → A.toIMat ^ A.ord = 1) ∧
    (∀ (A : M3), 1 ≤ A.ord → mOrd A.toIMat = A.ord) ∧
    (∀ {A B : M3} {U : IMat}, IsUnit U.det → B.toIMat = U * A.toIMat * invMat U →
      B.ord = A.ord ∧ B.det = A.det) := by
  refine ⟨?_, ?_, ?_⟩
  · intro A h
    have hne : A.ord ≠ 0 := by omega
    obtain ⟨-, -, hp⟩ := PSep.ord_spec hne
    rw [← PSep.toIMat_pow A A.ord, hp, M3.toIMat_one]
  · intro A h
    have hne : A.ord ≠ 0 := by omega
    exact (PSep.ord_eq_mOrd hne).symm
  · rintro A B U hU hB
    exact ⟨ord_conj hU hB, det_conj hU hB⟩

end Work.SGsep.hand
