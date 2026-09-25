import Submission.NK.Ramification.Herbrand
import Submission.NK.Ramification.herbrandInv_le_iff

namespace NK.Ramification

/-- **The inverse Herbrand function `ψ` is monotone**: the sets `{i | v ≤ φ(i)}` decrease as `v`
increases. -/
theorem herbrandInv_monotone {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) [Finite ↥(A.decompositionSubgroup K)] :
    Monotone (NK.Ramification.herbrandInv (K := K) A) := by
  intro v w hvw
  rw [herbrandInv_le_iff]
  have h1 : (w : ℚ) ≤ herbrand (K := K) A (herbrandInv (K := K) A w) :=
    (herbrandInv_le_iff A w (herbrandInv (K := K) A w)).mp le_rfl
  exact le_trans (by exact_mod_cast hvw) h1

end NK.Ramification
