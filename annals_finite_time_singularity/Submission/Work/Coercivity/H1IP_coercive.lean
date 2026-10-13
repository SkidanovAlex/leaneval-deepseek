/-
# The coercivity clause of `IsHkIP α 1 (H1IP α)`

The requested statement `IsHkIP α 1 (H1IP α)` is false — its first (additivity) conjunct
fails, see `Submission/Work/Coercivity/H1IP_isHkIP_false.lean` for a machine-checked
refutation.  This file records that the *coercivity* conjunct, i.e. the paper's Corollary
`FirstDerivativeCoercivity`, does hold for every admissible `f`: it is
`Work.Coercivity.FirstDerivativeCoercivity` combined with `Eztheta1 = HkSq α 1`
(`Eztheta1_eq_HkSq_one`), with the constant `c = 1`.
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Order.Filter.Defs
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Basic
import Submission.Work.Coercivity.FirstDerivativeCoercivity
import Submission.Work.Coercivity.Eztheta1_eq_HkSq_one

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-- The coercivity clause of `IsHkIP α 1 (H1IP α)`, in the hypothesis package in which the
`ℋ¹` coercivity chain of the paper is available. -/
theorem H1IP_coercive (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 10 ^ 14)
    (hIBP : ∀ f : ℝ → ℝ → ℝ, HkAdm α 1 f → IBP f)
    (hHH : ∀ f : ℝ → ℝ → ℝ, HkAdm α 1 f → HardyHyp f)
    (hCD : ∀ f : ℝ → ℝ → ℝ, HkAdm α 1 f → CoerciveData α f)
    (hG : GammaL2Bnd α) (hG2 : GammaPointwiseBnd α) :
    ∃ c : ℝ, 0 < c ∧ ∀ f : ℝ → ℝ → ℝ, HkAdm α 1 f →
      c * Spaces.HkSq α 1 f ≤ H1IP α (LGammaT α f) f := by
  refine ⟨1, one_pos, ?_⟩
  intro f hf
  have hsm : Spaces.SmoothNbhd f := hf.1
  have hmem : ∀ a b : ℕ, a + b ≤ 1 → Spaces.HkMem α 1 (Spaces.mixed b a f) := hf.2.1
  have hmemf : Spaces.HkMem α 1 f := hmem 0 0 (by norm_num)
  rw [one_mul, (Eztheta1_eq_HkSq_one α f hmemf hsm).symm]
  exact FirstDerivativeCoercivity α hα hα1 f (hIBP f hf) (hHH f hf) hG hG2
    (hCD f hf) hmemf hsm

end Work.Coercivity
