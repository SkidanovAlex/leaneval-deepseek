import Mathlib
import Submission.Work.Tower.Unramified.SplitsCompletelyNF
import Submission.Work.Tower.Unramified.SplitsCompletelyIn_ncard
import Submission.Work.Tower.Unramified.SplitsCompletelyIn_descent

namespace Work.Tower.Unramified

open NumberField

/-- **The explicit family description of complete splitting implies the counting normal form.**
If `𝔭` splits completely in `L/F` in the sense of `Work.Tower.SplitsCompletelyIn`, then the
primes of `𝓞 L` above `𝔭` are exactly `[L : F]` in number (this is
`Work.Tower.Unramified.SplitsCompletelyIn_ncard`) and each has ramification index `1` and
inertia degree `1` over `𝓞 F` (this is
`Work.Tower.Unramified.ef_eq_one_of_splitsCompletelyIn`). -/
theorem splitsCompletelyIn_imp_NF {F L : Type*} [Field F] [Field L] [NumberField F] [NumberField L]
    [Algebra F L] [FiniteDimensional F L] {𝔭 : Ideal (NumberField.RingOfIntegers F)}
    (h𝔭 : 𝔭.IsPrime) (h0 : 𝔭 ≠ ⊥)
    (h : Work.Tower.SplitsCompletelyIn F L 𝔭) :
    Work.Tower.Unramified.SplitsCompletelyInNF F L 𝔭 := by
  refine ⟨?_, ef_eq_one_of_splitsCompletelyIn h0 h⟩
  rw [Nat.card_coe_set_eq]
  exact SplitsCompletelyIn_ncard h

end Work.Tower.Unramified
