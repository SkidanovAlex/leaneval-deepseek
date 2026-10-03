import Mathlib
import Submission.Work.FIArea4.A6R2.Defs
import Submission.Work.FIArea4.A6psi.pDng6_le_EvarG
import Submission.Work.FIArea4.A6psi.Defs

namespace Work.FIArea4.A6R2

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The unfiltered per-modulus round-6 sum `A6R2.pD6ng` of this file is *the same sum* as
`A6psi.S15pDng6`: the two definitions differ only in the names of the round-6 coefficient
(`coef6`/`w6` here, `S15coef6`/`S15w6` there), whose bodies are identical. -/
lemma pD6ng_eq_S15pDng6 (Pa : Work.FITop.Params) (X j d : ℕ) (β : GaussianInt → ℂ) (ℓ : ℤ)
    (u t : ℝ) :
    pD6ng Pa X j d β ℓ u t = Work.FIArea4.A6psi.S15pDng6 Pa X j d β ℓ u t := by
  simp only [pD6ng, Work.FIArea4.A6psi.S15pDng6, coef6, Work.FIArea4.A6psi.S15coef6, w6,
    Work.FIArea4.A6psi.S15w6]

/-- **The per-modulus `e`-stratified class Cauchy–Schwarz for the round-6 sum** (the target
`pD6ngStratum`), transferred from the `A6psi` version `pDng6_le_EvarG` of the same statement: the
two sums `pD6ng` and `A6psi.S15pDng6` are the same object. -/
theorem pD6ngStratumBound : Work.FIArea4.A6R2.pD6ngStratum := by
  intro Pa X j d φ β ℓ u t hβ hd
  rw [pD6ng_eq_S15pDng6]
  exact Work.FIArea4.A6psi.pDng6_le_EvarG Pa X j d φ β ℓ u t hβ hd

end

end Work.FIArea4.A6R2
