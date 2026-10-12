import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Integrability of `u ↦ u^{-1/2} e^{-u}` on `(c, ∞)`

For `c > 0` the function `u ^ (-(1/2) : ℝ) * Real.exp (-u)` is integrable on `Set.Ioi c`:
on `(c, ∞)` the factor `u^{-1/2}` is bounded by the constant `c^{-1/2}` (the map
`u ↦ u^{-1/2}` is antitone on the positives), so the function is dominated by the
integrable function `c^{-1/2} e^{-u}`; the domination is applied through
`Integrable.mono'` against the restricted measure `volume.restrict (Ioi c)`, and the
almost-everywhere bound is obtained from the pointwise bound on `Ioi c` via
`ae_restrict_iff'`.

This is the one-dimensional tail estimate used in the continuum/heat-kernel
localisation of the lattice Green's function.
-/

open MeasureTheory Real Set

namespace Work.BoseFixR.LatGreen

theorem heatK3_rpow_half_mul_exp_integrable {c : ℝ} (hc : 0 < c) :
    MeasureTheory.IntegrableOn (fun u : ℝ => u ^ (-(1 / 2 : ℝ)) * Real.exp (-u)) (Set.Ioi c) := by
  -- the dominating function `c^{-1/2} e^{-u}` is integrable on `(c, ∞)`
  have hg : IntegrableOn (fun u : ℝ => c ^ (-(1 / 2 : ℝ)) * Real.exp (-u)) (Set.Ioi c) := by
    have h0 : IntegrableOn (fun u : ℝ => Real.exp (-u)) (Set.Ioi c) :=
      integrableOn_exp_neg_Ioi c
    rw [MeasureTheory.IntegrableOn] at h0 ⊢
    exact h0.const_mul _
  -- the integrand is continuous (hence a.e. strongly measurable) on `(c, ∞)`
  have hcont : ContinuousOn (fun u : ℝ => u ^ (-(1 / 2 : ℝ)) * Real.exp (-u)) (Set.Ioi c) := by
    refine ContinuousOn.mul ?_ ?_
    · exact continuousOn_id.rpow_const (fun u hu => Or.inl (ne_of_gt (lt_trans hc hu)))
    · exact Real.continuous_exp.comp_continuousOn continuousOn_id.neg
  rw [MeasureTheory.IntegrableOn] at hg ⊢
  refine MeasureTheory.Integrable.mono' hg
    (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
  refine Filter.Eventually.of_forall fun u hu => ?_
  have hcu : c < u := hu
  rw [Real.norm_of_nonneg (mul_nonneg
    (Real.rpow_nonneg (le_of_lt (lt_trans hc hcu)) _) (Real.exp_nonneg _))]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_nonpos hc (le_of_lt hcu) (by norm_num : -(1 / 2 : ℝ) ≤ 0))
    (Real.exp_nonneg _)

end Work.BoseFixR.LatGreen
