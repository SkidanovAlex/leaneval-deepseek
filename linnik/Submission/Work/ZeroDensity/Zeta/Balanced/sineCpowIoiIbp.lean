import Mathlib
import Submission.Work.ZeroDensity.Zeta.Balanced.sinCpowIoiIntegrable
import Submission.Work.ZeroDensity.Zeta.Balanced.cosCpowIoiIntegrable
import Submission.Work.ZeroDensity.Zeta.Balanced.tendstoNegCosCpowDiv
import Submission.Work.ZeroDensity.Zeta.Balanced.hasDerivAtNegCosCpowDiv

namespace Work.ZeroDensity.Zeta.Balanced

/-- **Integration by parts for `sin(a u) u^{-s-1}` over `(N, ∞)`.**
For `Re s > 0`, `a = 2π(k+1)` and `N ≥ 1`,
`∫_N^∞ sin(au) u^{-s-1} du = cos(aN) N^{-s-1}/a - (s+1)/a · ∫_N^∞ cos(au) u^{-s-2} du`.

This is the boundary term of the integration by parts applied to the antiderivative
`u ↦ -cos(au) u^{-s-1}/a`, whose derivative is `sin(au) u^{-s-1} + (s+1)/a · cos(au) u^{-s-2}`;
the boundary term at `∞` vanishes because `|u^{-s-1}| = u^{-Re s - 1} → 0`. -/
theorem sineCpowIoiIbp {s : ℂ} (hs : 0 < s.re) (N : ℕ) (hN : 1 ≤ N) (k : ℕ) :
    ∫ u in Set.Ioi (N : ℝ), ((Real.sin (2 * Real.pi * ((k : ℝ) + 1) * u) : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)
      = ((Real.cos (2 * Real.pi * ((k : ℝ) + 1) * (N : ℝ)) : ℝ) : ℂ) * (N : ℂ) ^ (-s - 1)
          / (2 * Real.pi * ((k : ℝ) + 1))
        - (s + 1) / (2 * Real.pi * ((k : ℝ) + 1)) *
            ∫ u in Set.Ioi (N : ℝ),
              ((Real.cos (2 * Real.pi * ((k : ℝ) + 1) * u) : ℝ) : ℂ) * (u : ℂ) ^ (-s - 2) := by
  -- Put the constant `a = 2π(k+1)` in the form `↑(real expression)` so that the
  -- helper lemmas (which are stated for a real parameter `a`) apply directly.
  have hcast : (((2 * Real.pi * ((k : ℝ) + 1) : ℝ)) : ℂ) = (2 : ℂ) * Real.pi * ((k : ℝ) + 1) := by
    push_cast; ring
  rw [← hcast]
  have ha_ne : (2 * Real.pi * ((k : ℝ) + 1)) ≠ 0 := by positivity
  -- Integrability of the two pieces of the integrand.
  have hA : MeasureTheory.IntegrableOn
      (fun u : ℝ => ((Real.sin (2 * Real.pi * ((k : ℝ) + 1) * u) : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1))
      (Set.Ioi (N : ℝ)) :=
    sinCpowIoiIntegrable s hs N hN (2 * Real.pi * ((k : ℝ) + 1))
  have hB : MeasureTheory.IntegrableOn
      (fun u : ℝ => ((Real.cos (2 * Real.pi * ((k : ℝ) + 1) * u) : ℝ) : ℂ) * (u : ℂ) ^ (-s - 2))
      (Set.Ioi (N : ℝ)) :=
    cosCpowIoiIntegrable s hs N hN (2 * Real.pi * ((k : ℝ) + 1))
  -- The derivative of the antiderivative, and its integrability.
  have hF : MeasureTheory.IntegrableOn
      (fun u : ℝ => ((Real.sin (2 * Real.pi * ((k : ℝ) + 1) * u) : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)
        + (s + 1) / ((2 * Real.pi * ((k : ℝ) + 1) : ℝ) : ℂ) *
          (((Real.cos (2 * Real.pi * ((k : ℝ) + 1) * u) : ℝ) : ℂ) * (u : ℂ) ^ (-s - 2)))
      (Set.Ioi (N : ℝ)) :=
    hA.add (MeasureTheory.Integrable.const_mul hB
      ((s + 1) / ((2 * Real.pi * ((k : ℝ) + 1) : ℝ) : ℂ)))
  have hderiv : ∀ x ∈ Set.Ici (N : ℝ),
      HasDerivAt
        (fun u : ℝ => -(((Real.cos (2 * Real.pi * ((k : ℝ) + 1) * u) : ℝ) : ℂ)
            * (u : ℂ) ^ (-s - 1)) / ((2 * Real.pi * ((k : ℝ) + 1) : ℝ) : ℂ))
        (((Real.sin (2 * Real.pi * ((k : ℝ) + 1) * x) : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)
          + (s + 1) / ((2 * Real.pi * ((k : ℝ) + 1) : ℝ) : ℂ) *
            (((Real.cos (2 * Real.pi * ((k : ℝ) + 1) * x) : ℝ) : ℂ) * (x : ℂ) ^ (-s - 2))) x := by
    intro x hx
    have hxpos : 0 < x := by
      have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      have hx' : (N : ℝ) ≤ x := hx
      linarith
    exact hasDerivAtNegCosCpowDiv s (2 * Real.pi * ((k : ℝ) + 1)) ha_ne hxpos
  have htow : Filter.Tendsto
      (fun u : ℝ => -(((Real.cos (2 * Real.pi * ((k : ℝ) + 1) * u) : ℝ) : ℂ)
          * (u : ℂ) ^ (-s - 1)) / ((2 * Real.pi * ((k : ℝ) + 1) : ℝ) : ℂ))
      Filter.atTop (nhds 0) :=
    tendstoNegCosCpowDiv s hs (2 * Real.pi * ((k : ℝ) + 1)) ha_ne
  -- Fundamental theorem of calculus for the improper integral over `(N, ∞)`.
  have key := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hF htow
  -- Linearity of the integral splits the derivative into the two pieces.
  have hsplit : (∫ u in Set.Ioi (N : ℝ),
        (((Real.sin (2 * Real.pi * ((k : ℝ) + 1) * u) : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)
          + (s + 1) / ((2 * Real.pi * ((k : ℝ) + 1) : ℝ) : ℂ) *
            (((Real.cos (2 * Real.pi * ((k : ℝ) + 1) * u) : ℝ) : ℂ) * (u : ℂ) ^ (-s - 2))))
      = (∫ u in Set.Ioi (N : ℝ),
            ((Real.sin (2 * Real.pi * ((k : ℝ) + 1) * u) : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1))
        + (s + 1) / ((2 * Real.pi * ((k : ℝ) + 1) : ℝ) : ℂ) *
            (∫ u in Set.Ioi (N : ℝ),
              ((Real.cos (2 * Real.pi * ((k : ℝ) + 1) * u) : ℝ) : ℂ) * (u : ℂ) ^ (-s - 2)) := by
    rw [MeasureTheory.integral_add hA
      (MeasureTheory.Integrable.const_mul hB _), MeasureTheory.integral_const_mul]
  have hval : (∫ u in Set.Ioi (N : ℝ),
            ((Real.sin (2 * Real.pi * ((k : ℝ) + 1) * u) : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1))
        + (s + 1) / ((2 * Real.pi * ((k : ℝ) + 1) : ℝ) : ℂ) *
            (∫ u in Set.Ioi (N : ℝ),
              ((Real.cos (2 * Real.pi * ((k : ℝ) + 1) * u) : ℝ) : ℂ) * (u : ℂ) ^ (-s - 2))
      = ((Real.cos (2 * Real.pi * ((k : ℝ) + 1) * (N : ℝ)) : ℝ) : ℂ) * (N : ℂ) ^ (-s - 1)
          / ((2 * Real.pi * ((k : ℝ) + 1) : ℝ) : ℂ) := by
    rw [← hsplit, key]
    simp only [zero_sub, neg_div, neg_neg, Complex.ofReal_natCast]
  rw [eq_sub_iff_add_eq]
  exact hval

end Work.ZeroDensity.Zeta.Balanced
