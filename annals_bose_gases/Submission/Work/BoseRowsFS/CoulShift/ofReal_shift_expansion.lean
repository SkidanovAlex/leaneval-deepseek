import Mathlib.Analysis.InnerProductSpace.PiL2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseRowsFS.CoulShift

/-- Distributivity of `ENNReal.ofReal` over the expansion of the product
`(W x + W (x + a)) * (W y + W (y + a))`, using that all factors are non-negative.
The single division by `‖x - y‖` is factored out via `ring`. -/
theorem ofReal_shift_expansion {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hW0 : ∀ x, 0 ≤ W x)
    (a x y : EuclideanSpace ℝ (Fin 3)) :
    ENNReal.ofReal ((W x + W (x + a)) * (W y + W (y + a)) / ‖x - y‖)
      = ENNReal.ofReal (W x * W y / ‖x - y‖) + ENNReal.ofReal (W x * W (y + a) / ‖x - y‖)
        + ENNReal.ofReal (W (x + a) * W y / ‖x - y‖) + ENNReal.ofReal (W (x + a) * W (y + a) / ‖x - y‖) := by
  have hkey : (W x + W (x + a)) * (W y + W (y + a)) / ‖x - y‖
      = W x * W y / ‖x - y‖ + W x * W (y + a) / ‖x - y‖
        + W (x + a) * W y / ‖x - y‖ + W (x + a) * W (y + a) / ‖x - y‖ := by ring
  have h1 : 0 ≤ W x * W y / ‖x - y‖ :=
    div_nonneg (mul_nonneg (hW0 x) (hW0 y)) (norm_nonneg _)
  have h2 : 0 ≤ W x * W (y + a) / ‖x - y‖ :=
    div_nonneg (mul_nonneg (hW0 x) (hW0 (y + a))) (norm_nonneg _)
  have h3 : 0 ≤ W (x + a) * W y / ‖x - y‖ :=
    div_nonneg (mul_nonneg (hW0 (x + a)) (hW0 y)) (norm_nonneg _)
  have h4 : 0 ≤ W (x + a) * W (y + a) / ‖x - y‖ :=
    div_nonneg (mul_nonneg (hW0 (x + a)) (hW0 (y + a))) (norm_nonneg _)
  rw [hkey, ENNReal.ofReal_add (add_nonneg (add_nonneg h1 h2) h3) h4,
    ENNReal.ofReal_add (add_nonneg h1 h2) h3, ENNReal.ofReal_add h1 h2]

end Work.BoseRowsFS.CoulShift
