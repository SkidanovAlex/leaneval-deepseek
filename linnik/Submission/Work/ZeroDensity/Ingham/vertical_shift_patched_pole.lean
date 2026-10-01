import Mathlib

namespace Work.ZeroDensity.Ingham

/-- **Patched vertical contour shift across a simple pole.**

Let `p < q` be real, `u` a point of the open vertical strip `p < Re u < q`, `a` a constant, and
`F H : ℂ → ℂ` two functions such that
* `H` is complex differentiable on every closed rectangle `[p,q] × [-R,R]` (`R ≥ 0`);
* off the pole `u` and off the single point `0`, `F = a/(s-u) + H` on the closed rectangle
  (`s ≠ 0` is needed because in the intended application `F` has a *removable* singularity at `0`:
  the literal function value there differs from the value of the holomorphic extension, by exactly
  one point, which all four edge integrals are insensitive to);
* the horizontal edge integrals of `H` over `[p,q]` at height `±R` tend to `0`;
* `F` is integrable on the two vertical lines `Re s = p` and `Re s = q`.
Then `∫_{Re s = q} F = ∫_{Re s = p} F + 2π a`.

Proof: for `R` large, `rectInt` over the rectangle `[p,q] × [-R,R]` equals
`a·2πi + rectInt H = a·2πi` (`rectInt_const_div_sub_inside`, `rectInt_eq_zero_of_differentiableOn`);
on each of the four edges `F` agrees with `a/(s-u) + H` except possibly at the single point `0`, so
`intervalIntegral.integral_congr_ae'` (plus `∀ᵐ y, y ≠ 0`) transfers the decomposition to the edge
integrals. Expanding `rectInt` into its four sides and letting `R → ∞` (using `hpint`/`hqint`,
`intervalIntegral_tendsto_integral`, and the vanishing of the horizontal edges — for the kernel
`a/(s-u)` that vanishing is the elementary bound `|∫_p^q a/((x±iR)-u) dx| ≤ |q-p||a|/(R-‖u‖)`)
gives `i(∫_{Re s=q} F - ∫_{Re s=p} F) = 2πi a`. -/
theorem vertical_shift_patched_pole (F H : ℂ → ℂ) (p q : ℝ) (hpq : p < q) (u a : ℂ)
    (hu : p < u.re ∧ u.re < q)
    (hH : ∀ R : ℝ, DifferentiableOn ℂ H (Set.uIcc p q ×ℂ Set.uIcc (-R) R))
    (hdec : ∀ R : ℝ, 1 ≤ R → ∀ s ∈ (Set.uIcc p q ×ℂ Set.uIcc (-R) R), s ≠ u → s ≠ 0 →
      F s = a / (s - u) + H s)
    (htop : Filter.Tendsto (fun R : ℝ => ∫ x in p..q, H ((x : ℂ) + (R : ℂ) * Complex.I))
      Filter.atTop (nhds 0))
    (hbot : Filter.Tendsto (fun R : ℝ => ∫ x in p..q, H ((x : ℂ) - (R : ℂ) * Complex.I))
      Filter.atTop (nhds 0))
    (hpint : MeasureTheory.Integrable (fun t : ℝ => F ((p : ℂ) + (t : ℂ) * Complex.I)))
    (hqint : MeasureTheory.Integrable (fun t : ℝ => F ((q : ℂ) + (t : ℂ) * Complex.I))) :
    (∫ t : ℝ, F ((q : ℂ) + (t : ℂ) * Complex.I))
      = (∫ t : ℝ, F ((p : ℂ) + (t : ℂ) * Complex.I)) + 2 * Real.pi * a := by
  sorry

end Work.ZeroDensity.Ingham
