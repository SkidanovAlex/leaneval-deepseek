import Mathlib

namespace Work.BourgainPlan.Maximal

/-- If a real polynomial `q` has, on `[U, ∞)` with `U ≥ 1`, a derivative that dominates
`c * u ^ (q.natDegree - 1)` for some `c > 0`, then `q` is strictly increasing on `[U, ∞)`.

Indeed the hypothesis forces `q' > 0` on `(U, ∞)`, so the mean value theorem applies. -/
theorem strictMonoOn_eval_of_deriv_lower (q : Polynomial ℝ) {U c : ℝ} (hU : 1 ≤ U) (hc : 0 < c)
    (hderiv : ∀ u : ℝ, U ≤ u → c * u ^ (q.natDegree - 1) ≤ q.derivative.eval u) :
    StrictMonoOn (fun u : ℝ => q.eval u) (Set.Ici U) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici U) ?_ fun x hx => ?_
  · exact q.continuous.continuousOn
  · rw [interior_Ici] at hx
    have hxU : U ≤ x := le_of_lt hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one (le_of_lt (lt_of_le_of_lt hU hx))
    have hpos : 0 < q.derivative.eval x :=
      lt_of_lt_of_le (mul_pos hc (pow_pos hx0 _)) (hderiv x hxU)
    simpa using hpos

end Work.BourgainPlan.Maximal
