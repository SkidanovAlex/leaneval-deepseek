import Mathlib
import Submission.Work.BMF.mr_direct.primePoly_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

/-- If `powCoeff c P k n` is non-zero, its defining sum has a non-empty index set:
there is a `k`-tuple `f` of primes in `primeSet P` whose product is `n`. -/
theorem powCoeff_support (P : ℝ) (c : ℕ → ℂ) (k n : ℕ)
    (h : Work.BMF.mr_direct.primePoly.powCoeff c P k n ≠ 0) :
    ∃ f ∈ Fintype.piFinset (fun _ : Fin k => Work.BMF.mr_direct.primePoly.primeSet P),
      ∏ j, f j = n := by
  rw [Work.BMF.mr_direct.primePoly.powCoeff] at h
  obtain ⟨f, hf, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact ⟨f, (Finset.mem_filter.mp hf).1, (Finset.mem_filter.mp hf).2⟩

end Work.BMF.mr_direct
