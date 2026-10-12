import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Defs
import Submission.Work.BoseB4.AntiNormal
import Submission.Work.BoseB4.DGamma_diag
import Submission.Work.BoseB4.DGamma_one
import Submission.Work.BoseB4.DGamma_quadform
import Submission.Work.BoseB4.Kafz_lower_bound_H2nd
import Submission.Work.BoseB4.Kafz_lower_bound_pointwise
import Submission.Work.BoseB4.TildeDataInst
import Submission.Work.BoseB4.a0_comp_a0d_sq
import Submission.Work.BoseB4.annC_creC_ccr
import Submission.Work.BoseB4.dGamma_diag_nonneg
import Submission.Work.BoseB4.monoOp_11_00_numOp
import Submission.Work.BoseB4.monoOp_lift_basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

/-- `monoOp p q` is *real*-linear in its spectator operator over a weighted finite
sum: the ℝ-coefficients `c k` on the right are the complex coefficients
`((c k : ℝ) : ℂ)` of the left, read through the restriction of scalars
`ℝ → ℂ` on the space of ℂ-linear endomorphisms of the Fock core.

This is the ℝ-coefficient companion of `Work.BoseB4.monoOp_sum_smul` (which
handles ℂ-coefficients): it lets a finite sum of anti-normal monomials with real
physical coefficients be assembled term by term, exactly the situation of the
box Hamiltonian of FS §8–§11, where the spectator operators carry real coupling
constants. -/
theorem monoOp_sum_real_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {ι : Type*} [DecidableEq ι] (p q : ℕ) (s : Finset ι) (c : ι → ℝ)
    (B : ι → E →ₗ[ℂ] E) :
    Work.BoseB4.monoOp p q (∑ k ∈ s, ((c k : ℝ) : ℂ) • B k)
      = ∑ k ∈ s, c k • Work.BoseB4.monoOp p q (B k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Work.BoseB4.monoOp_add, ih,
        Work.BoseB4.monoOp_smul]
      -- `↑(c a) • X = c a • X`: the ℝ-smul on `FockCore E →ₗ[ℂ] FockCore E` is the
      -- restriction of scalars of the ℂ-smul, so the two sides are definitionally equal.
      rfl

end Work.BoseBoxFock
