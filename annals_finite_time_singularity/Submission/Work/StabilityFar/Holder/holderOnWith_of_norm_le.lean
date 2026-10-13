import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.StabilityFar.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.StabilityFar.Holder

/-- The norm-coordinate form of the Hölder condition implies the `edist`-coordinate form
used by `HolderOnWith`.  Since `edist` on a (pseudo)metric space is `ENNReal.ofReal` of the
distance, this is just `ENNReal.ofReal` applied to the hypothesis, together with
`ENNReal.ofReal_mul` and `ENNReal.ofReal_rpow_of_nonneg`. -/
theorem holderOnWith_of_norm_le {X Y : Type*} [PseudoMetricSpace X] [NormedAddCommGroup Y]
    {C r : NNReal} {f : X → Y} {s : Set X}
    (h : ∀ x ∈ s, ∀ y ∈ s, ‖f x - f y‖ ≤ (C : ℝ) * dist x y ^ (r : ℝ)) :
    HolderOnWith C r f s := by
  intro x hx y hy
  rw [edist_dist, edist_dist, dist_eq_norm]
  calc ENNReal.ofReal ‖f x - f y‖
      ≤ ENNReal.ofReal ((C : ℝ) * dist x y ^ (r : ℝ)) := ENNReal.ofReal_le_ofReal (h x hx y hy)
    _ = ENNReal.ofReal (C : ℝ) * ENNReal.ofReal (dist x y ^ (r : ℝ)) :=
        ENNReal.ofReal_mul (by positivity)
    _ = ↑C * ENNReal.ofReal (dist x y) ^ (r : ℝ) := by
        rw [ENNReal.ofReal_rpow_of_nonneg dist_nonneg (by positivity), ENNReal.ofReal_coe_nnreal]

end Work.StabilityFar.Holder
