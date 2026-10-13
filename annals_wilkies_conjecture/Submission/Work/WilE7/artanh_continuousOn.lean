import Mathlib

namespace Work.WilE7

/-- `Real.artanh` is continuous on the open interval `(-1,1)`.  It is the inverse of
`Real.tanh` there, and Mathlib has `Real.tanh_artanh` but no continuity statement for `artanh`.
On `(-1,1)` one has `artanh x = 1/2 * log ((1+x)/(1-x))` (`Real.artanh_eq_half_log`), the
argument of the logarithm being positive, so continuity follows from continuity of `log` on
`{0}ᶜ` and of the rational function `x ↦ (1+x)/(1-x)` at points where `1 - x ≠ 0`. -/
theorem artanh_continuousOn : ContinuousOn Real.artanh (Set.Ioo (-1) 1) := by
  have hcont : ContinuousOn (fun x : ℝ => (1 / 2 : ℝ) * Real.log ((1 + x) / (1 - x)))
      (Set.Ioo (-1) 1) := by
    refine ContinuousOn.const_mul ?_ _
    refine ContinuousOn.log ?_ ?_
    · refine ContinuousOn.div ?_ ?_ ?_
      · exact continuousOn_const.add continuousOn_id
      · exact continuousOn_const.sub continuousOn_id
      · intro x hx
        linarith [hx.2]
    · intro x hx
      exact div_ne_zero (by linarith [hx.1]) (by linarith [hx.2])
  refine ContinuousOn.congr_mono hcont ?_ (Set.Subset.refl _)
  intro x hx
  exact Real.artanh_eq_half_log (Set.Ioo_subset_Icc_self hx)

end Work.WilE7
