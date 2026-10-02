import Mathlib
import Submission.Work.Whitney.chernClass_whitneySum_rank_zero
import Submission.Work.Whitney.cupChern_one_right
import Submission.Work.Thom.chernClass_zero_eq_oneH

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

/-!
# The top Chern class of a Whitney sum with a rank-`0` second summand

The boundary case `m₂ = 0` of the headline `Work.Whitney.chernClass_whitneySum_top`.  Since `Nat.add`
recurses on its second argument, `m₁ + 0` *is* definitionally `m₁`, so this case is the one where no
index transport is needed; the two inputs are the rank-zero result
`Work.Whitney.chernClass_whitneySum_rank_zero` (`chernClass` does not see a rank-`0` summand) and the
right unit law `Work.Whitney.cupChern_one_right` of the graded product, together with
`Work.Thom.chernClass_zero_eq_oneH`.
-/

namespace Work.Whitney

open Work.Thom
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

variable {B : Type} [TopologicalSpace B] {m₁ : ℕ} {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]

/-- **The top Chern class of a Whitney sum with a rank-`0` second summand.** -/
theorem chernClass_whitneySum_top_rank_zero_right
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 0)) ι₂) :
    chernClass (m₁ + 0) (m₁ + 0) (whitneySum Z₁ Z₂)
      = cupChern m₁ 0 (chernClass m₁ m₁ Z₁) (chernClass 0 0 Z₂) := by
  have h1 : chernClass (m₁ + 0) (m₁ + 0) (whitneySum Z₁ Z₂) = chernClass m₁ m₁ Z₁ :=
    chernClass_whitneySum_rank_zero Z₁ Z₂ (m₁ + 0)
  have h2 : chernClass 0 0 Z₂
      = cohTransport (by rfl : (2 : ℕ) * 0 = 0) (Work.Cohomology.oneH ℤ (ssB B)) := by
    rw [chernClass_zero_eq_oneH Z₂]
    exact (cohTransport_rfl _).symm
  rw [h1, h2, cupChern_one_right (B := B) m₁ (chernClass m₁ m₁ Z₁)]
  exact (cohTransport_rfl _).symm

end

end Work.Whitney
