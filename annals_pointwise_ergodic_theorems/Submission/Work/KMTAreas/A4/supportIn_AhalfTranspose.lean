import Mathlib
import Submission.Work.Analysis.InverseTheory.Transpose

namespace Work.KMTAreas.A4

/-- Support of the first dual function: if `h` is supported in `[-M, M]` then `Ã_N^*(h,g)` is
supported in `[-(M+N), M+N]` (only the support of the first argument `h` is used). -/
theorem supportIn_AhalfTranspose {N M : ℕ} {P : Polynomial ℤ} {h g : ℤ → ℂ}
    (hh : Work.Analysis.InverseTheory.SupportIn h M) :
    Work.Analysis.InverseTheory.SupportIn
      (Work.Analysis.InverseTheory.AhalfTranspose N P h g) (M + N) := by
  intro x hx
  rw [Work.Analysis.InverseTheory.AhalfTranspose]
  refine mul_eq_zero_of_right _ ?_
  refine Finset.sum_eq_zero fun n hn => ?_
  rw [Finset.mem_Ioc] at hn
  have hfn : h (x - (n : ℤ)) = 0 := by
    apply hh
    have h1 : x.natAbs ≤ (x - (n : ℤ)).natAbs + n := by
      have := Int.natAbs_add_le (x - (n : ℤ)) (n : ℤ)
      simpa using this
    omega
  rw [hfn, zero_mul]

end Work.KMTAreas.A4
