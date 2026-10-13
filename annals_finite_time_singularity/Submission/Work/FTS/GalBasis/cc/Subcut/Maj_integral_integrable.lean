import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.GalBasis.cc.Subcut.MajDefs
import Submission.Work.FTS.GalBasis.cc.Subcut.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongLWP.Xn6Limit.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalBasis.cc.Subcut

/-- **The `z`-marginal `z ↦ ∫_{Iθ} Maj α C κN N f z θ` is integrable on `Iz`.**

`hae` is the a.e. strong measurability of the uncurried majorant for
`(volume.restrict Iz).prod (volume.restrict Iθ)` (supplied by `Subcut.Maj_aesm`), so
`MeasureTheory.AEStronglyMeasurable.integral_prod_right'` makes the marginal a.e. strongly
measurable.  The dominating function is `D z = ∫_{Iθ} C (1 + κN) HkIntegrand α 4 f z θ`, integrable
by `hmem.2` and `MeasureTheory.integral_const_mul`; the a.e. bound
`‖∫_{Iθ} Maj … z θ‖ ≤ D z` follows from `MeasureTheory.norm_integral_le_integral_norm` followed by
`MeasureTheory.integral_mono_of_nonneg` applied with `f = fun θ => ‖Maj … z θ‖` (nonnegative),
`g = fun θ => C (1 + κN) * HkIntegrand α 4 f z θ` (integrable by `hmem.1 z hz.le` for `0 ≤ z`) and
the a.e. bound `‖Maj … z θ‖ ≤ C (1 + κN) * HkIntegrand α 4 f z θ` for `θ ∈ Iθ`, which uses `hcap`
and the pointwise nonnegativity of `Maj` (`hC : 0 < C` and `Work.Spaces.HkIntegrand_nonneg`).  Work
on the full-measure subset `{z | 0 < z} ⊆ Iz` (`MeasureTheory.Ioi_ae_eq_Ici`,
`MeasureTheory.Measure.restrict_congr_set`, `MeasureTheory.ae_restrict_iff'`), then
`MeasureTheory.Integrable.mono'`. -/
theorem Maj_integral_integrable {α : ℝ} {f : Work.FTS.Galerkin.Fn}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    {C κN : ℝ} (N : ℕ) (hC : 0 < C)
    (hae : MeasureTheory.AEStronglyMeasurable
        (Function.uncurry (Work.FTS.GalBasis.cc.Maj α C κN N f))
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hcap : ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
      Work.FTS.GalBasis.cc.Maj α C κN N f z θ
        ≤ C * (1 + κN) * Work.Spaces.HkIntegrand α 4 f z θ) :
    MeasureTheory.Integrable
        (fun z => ∫ θ in Work.Spaces.Iθ, Work.FTS.GalBasis.cc.Maj α C κN N f z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hMajnneg : ∀ z θ : ℝ, 0 ≤ Work.FTS.GalBasis.cc.Maj α C κN N f z θ := by
    intro z θ
    rw [Work.FTS.GalBasis.cc.Maj_apply]
    refine mul_nonneg hC.le
      (add_nonneg (mul_nonneg ?_ (Work.Spaces.HkIntegrand_nonneg α 4 f z θ))
        (mul_nonneg ?_ (Finset.sum_nonneg fun b _ => sq_nonneg _)))
    · exact Set.indicator_nonneg (fun _ _ => zero_le_one) (z, θ)
    · exact Set.indicator_nonneg (fun _ _ => zero_le_one) θ
  have hzpos : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 < z := by
    have hset : Set.Ioi (0 : ℝ) =ᵐ[MeasureTheory.volume] Work.Spaces.Iz :=
      MeasureTheory.Ioi_ae_eq_Ici
    rw [← MeasureTheory.Measure.restrict_congr_set hset]
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall fun z hz => hz
  have hmarg : MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.FTS.GalBasis.cc.Maj α C κN N f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have h := hae.integral_prod_right' (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
        (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    simpa only [Function.uncurry] using h
  have hDint : MeasureTheory.Integrable
      (fun z => ∫ θ in Work.Spaces.Iθ, C * (1 + κN) * Work.Spaces.HkIntegrand α 4 f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    refine (hmem.2.const_mul (C * (1 + κN))).congr ?_
    filter_upwards with z
    exact (MeasureTheory.integral_const_mul (C * (1 + κN))
      (fun θ => Work.Spaces.HkIntegrand α 4 f z θ)).symm
  refine MeasureTheory.Integrable.mono' hDint hmarg ?_
  filter_upwards [hzpos] with z hz
  refine le_trans (MeasureTheory.norm_integral_le_integral_norm _) ?_
  refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun θ => norm_nonneg _
  · exact (hmem.1 z (show z ∈ Work.Spaces.Iz from le_of_lt hz)).const_mul (C * (1 + κN))
  · filter_upwards [MeasureTheory.ae_restrict_mem (show MeasurableSet Work.Spaces.Iθ
        from measurableSet_Icc)] with θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (hMajnneg z θ)]
    exact hcap z θ hz hθ

end Work.FTS.GalBasis.cc.Subcut
