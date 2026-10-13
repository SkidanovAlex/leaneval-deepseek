import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic

theorem seg_second_order_bound (N N' : ℝ → ℝ) (K b : ℝ) (hK : 0 ≤ K) (hb : 0 ≤ b)
    (hd : ∀ x ∈ Set.Icc 0 b, HasDerivWithinAt N (N' x) (Set.Icc 0 b) x)
    (hbd : ∀ x ∈ Set.Icc 0 b, ‖N' x‖ ≤ K * x) :
    ∀ x ∈ Set.Icc 0 b, ‖N x - N 0‖ ≤ K * x ^ 2 := by
  intro x hx
  have hx0 : 0 ≤ x := hx.1
  have hxb : x ≤ b := hx.2
  have hsub : Set.Icc 0 x ⊆ Set.Icc 0 b := Set.Icc_subset_Icc le_rfl hxb
  have hderiv : ∀ y ∈ Set.Icc 0 x, HasDerivWithinAt N (N' y) (Set.Icc 0 x) y := by
    intro y hy
    exact (hd y (hsub hy)).mono hsub
  have hbound : ∀ y ∈ Set.Ico 0 x, ‖N' y‖ ≤ K * x := by
    intro y hy
    have hyb : y ∈ Set.Icc 0 b := ⟨hy.1, le_trans hy.2.le hxb⟩
    have h1 : ‖N' y‖ ≤ K * y := hbd y hyb
    have h2 : K * y ≤ K * x := mul_le_mul_of_nonneg_left hy.2.le hK
    linarith
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound x ⟨hx0, le_rfl⟩
  simpa [pow_two, mul_assoc] using h

end Work.Elliptic
