import Mathlib
import Submission.Work.PSU3.StageB.NotFpfStep4.step4_algebra

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageB.NotFpfStep4

/-- **Peterfalvi II, Ch. VII §4, relation (10) ⟹ `μ²` fixes the `σE`-fixed field.**

With `c = ζ + ζ⁻¹` and `μ` the field automorphism of `E = GF(q²)` induced by `η`, the
source's relation (10),
`(c + X^μ) X = (c + X^{μ²}) X^μ` for `X` in the fixed field `F` of `σE` (`X = a^{-2}`),
is stated here uniformly for every `σE`-fixed `X`.  Writing it also for `X + 1` (which is again
`σE`-fixed, and whose `μ`-image is `X^μ + 1` because `μ` fixes `1`) and adding the two
instances in characteristic two collapses both sides to `X + X^{μ²} = 0`, whence
`μ (μ X) = X`.  This is exactly the step "subtracting the instances at `X + 1` and `X`" of the
proof of Theorem B. -/
theorem step4_mu_sq_fix_of_relation {n : ℕ}
    (μ : Work.PSU3.E n ≃+* Work.PSU3.E n) (c : Work.PSU3.E n)
    (hrel : ∀ X : Work.PSU3.E n, Work.PSU3.σE X = X →
      (c + μ X) * X = (c + μ (μ X)) * μ X) :
    ∀ X : Work.PSU3.E n, Work.PSU3.σE X = X → μ (μ X) = X
  := by
  intro X hX
  -- `X + 1` is again fixed by `σE`.
  have hX1 : Work.PSU3.σE (X + 1) = X + 1 := by rw [map_add, map_one, hX]
  -- The relation at `X` and at `X + 1`.
  have e1 : (c + μ X) * X = (c + μ (μ X)) * μ X := hrel X hX
  have e2 : (c + μ (X + 1)) * (X + 1) = (c + μ (μ (X + 1))) * μ (X + 1) :=
    hrel (X + 1) hX1
  -- `μ` is additive and fixes `1`, so `μ (X+1) = μ X + 1` and `μ (μ (X+1)) = μ (μ X) + 1`.
  rw [map_add, map_one, map_add, map_one] at e2
  -- Add the two instances: in characteristic two the sum of the two left/right sides
  -- reduces to `X + μ (μ X)`.
  have hkey : (c + (μ X + 1)) * (X + 1) + (c + μ X) * X
      = (c + (μ (μ X) + 1)) * (μ X + 1) + (c + μ (μ X)) * μ X := by rw [e1, e2]
  have h2 : X + μ (μ X) = 0 := by
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) hkey
  exact (CharTwo.add_eq_zero.mp h2).symm

end Work.PSU3.StageB.NotFpfStep4
