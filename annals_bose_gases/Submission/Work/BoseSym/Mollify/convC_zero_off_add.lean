import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseSym.Interface
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseSym.Mollify.convC_zero_off_add`

If no decomposition `x = a + b` with `a` in the topological support of `f` and
`b` in the topological support of `ρ` exists, then the convolution
`convC N f ρ x = ∫ t, f t • ρ (x - t)` vanishes: the integrand is identically
zero, because `f t ≠ 0` forces `t ∈ tsupport f` while `ρ (x - t) ≠ 0` forces
`x - t ∈ tsupport ρ`, and `t + (x - t) = x`.
-/

namespace Work.BoseSym.Mollify

open MeasureTheory

theorem convC_zero_off_add {N : ℕ} {f ρ : Work.BoseSym.Conf N → ℝ} {x : Work.BoseSym.Conf N}
    (hx : ∀ a ∈ tsupport f, ∀ b ∈ tsupport ρ, a + b ≠ x) :
    Work.BoseSym.convC N f ρ x = 0 := by
  rw [Work.BoseSym.convC, convolution_lsmul]
  have hpoint : ∀ t : Conf N, f t • ρ (x - t) = 0 := by
    intro t
    rw [smul_eq_mul]
    by_cases ht : t ∈ tsupport f
    · by_cases hxt : x - t ∈ tsupport ρ
      · exact absurd (by abel : t + (x - t) = x) (hx t ht (x - t) hxt)
      · rw [image_eq_zero_of_notMem_tsupport hxt, mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport ht, zero_mul]
  rw [show (fun t : Conf N => f t • ρ (x - t)) = fun _ => (0 : ℝ) from funext hpoint]
  simp

end Work.BoseSym.Mollify
