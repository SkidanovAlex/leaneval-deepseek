import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MDCommon
import Submission.Work.HP.MDBasic.finite_sets
import Submission.Work.HP.MDReduction.Dglob_eq_Omega

/-!
# The `μ`-split of the second moment

`Dglob = Σ^{(1)} + Σ^{(2)}`, i.e. the pair sum `(1/4)Σ_{p∈Ω(B)} 𝓢*₀(Γ_p; B_N(A))` is split at
`μ(x,y) = A` into the "small `μ`" part `Sigma1` and the "large `μ`" part `Sigma2`.
-/

set_option autoImplicit false

noncomputable section

open MvPolynomial Finset
open scoped BigOperators

namespace Work.HP

/-- The `μ`-split of the second moment: `Dglob = Sigma1 + Sigma2`. -/
theorem Dglob_eq_Sigma1_add_Sigma2 (d n : ℕ) (A B : ℝ) :
    Dglob d n A B = Sigma1 d n A B + Sigma2 d n A B := by
  have hΩ : (Omega d n B).Finite := (MDBasic.finite_sets d n A B (fun _ => True)).2.2
  rw [MDReduction.Dglob_eq_Omega, Sigma1, Sigma2, ← mul_add]
  congr 1
  exact (finsum_mem_inter_add_sdiff {p : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ) |
      muXY n p.1 p.2 ≤ A} hΩ).symm

end Work.HP
