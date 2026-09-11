import Submission.MulCompute

open UnitConjecture

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Submission

open scoped Classical
open MonoidAlgebra
open Finset

/-- coefficient of U0 at an arbitrary monomial, in terms of the four part memberships -/
lemma U0_coeff (m : HW) : U0.coeff m =
    (if m ∈ Qp then (1 : ZMod 2) else 0) + (if m ∈ PqA then (1 : ZMod 2) else 0)
      + (if m ∈ PrB then (1 : ZMod 2) else 0) + (if m ∈ PsAB then (1 : ZMod 2) else 0) := by
  rw [U0]
  simp [Finsupp.add_apply, Finsupp.single_apply]

-- coefficients of U0 at two distinct points -/
lemma coeff_U0_1 : U0.coeff (m 0 0 0 q0) = (1 : ZMod 2) := by
  rw [U0_coeff]
  decide

lemma coeff_U0_2 : U0.coeff (m 1 0 0 q0) = (1 : ZMod 2) := by
  rw [U0_coeff]
  decide

lemma m_ne : m 0 0 0 q0 ≠ m 1 0 0 q0 := by
  decide

/-- U0 is not a single (group) element -/
lemma U0_not_single : ¬ ∃ g : HW, U0 = single g (1 : ZMod 2) := by
  intro ⟨g, hg⟩
  have h1 := congrArg (fun f : MonoidAlgebra (ZMod 2) HW => f.coeff (m 0 0 0 q0)) hg
  have h2 := congrArg (fun f : MonoidAlgebra (ZMod 2) HW => f.coeff (m 1 0 0 q0)) hg
  rw [coeff_U0_1] at h1
  rw [coeff_U0_2] at h2
  rw [coeff_single'] at h1 h2
  by_cases hg0 : g = m 0 0 0 q0
  · have hg100 : g ≠ m 1 0 0 q0 := by
      rw [hg0]
      exact m_ne
    rw [if_neg hg100] at h2
    norm_num at h2
  · rw [if_neg hg0] at h1
    norm_num at h1

end Submission
