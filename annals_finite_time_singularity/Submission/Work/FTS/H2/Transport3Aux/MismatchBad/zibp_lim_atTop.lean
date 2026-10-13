import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.Transport3Aux.MismatchBad

/-- Boundary vanishing at `+∞` for the weighted `z`-integration by parts: if `ψ` is
differentiable on `(0,∞)` with integrable derivative `ψ'` and `|ψ z| ≤ C·z·G(z)²` on `z ≥ 0`
with `C > 0` and `G² ∈ L¹(0,∞)`, then `ψ z → 0` as `z → +∞`.

Route (all pieces are in Mathlib): `hderiv`+`hint` give the FTC on `[a,b]`, so
`|ψ z - ψ z₀| ≤ ∫_{min}^{max}|ψ'|`; `ψ' ∈ L¹` makes the tail integral `∫_{Ioi R}|ψ'|`
tend to `0` (e.g. `Antitone.tendsto_setIntegral` with `s n = Ioi n`).  Assume for
contradiction that `¬(ψ → 0)`; then for every `R` there is `z₀ ≥ R` with `|ψ z₀| ≥ ε`; with
`R` so large that `∫_{Ioi R}|ψ'| < ε/2` the oscillation bound gives `|ψ z| ≥ ε/2` for all
`z ≥ R`, hence `G(z)² ≥ (ε/(2C))/z` on `(R,∞)`, contradicting `hG` since `z ↦ c/z` is not
integrable on `(R,∞)` (`not_integrableOn_Ioi_inv`, or directly
`not_integrableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter` with `Real.log`). -/
theorem zibp_lim_atTop {ψ ψ' G : ℝ → ℝ} {C : ℝ} (hC : 0 < C)
    (hderiv : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt ψ (ψ' z) z)
    (hint : MeasureTheory.IntegrableOn ψ' (Set.Ioi (0 : ℝ)))
    (hbd : ∀ z, 0 ≤ z → |ψ z| ≤ C * (z * (G z) ^ 2))
    (hG : MeasureTheory.IntegrableOn (fun z => (G z) ^ 2) (Set.Ioi (0 : ℝ))) :
    Filter.Tendsto ψ Filter.atTop (nhds 0) := by
  -- `ψ` has a limit at `+∞`, because its derivative is integrable there.
  have hlim : Filter.Tendsto ψ Filter.atTop (nhds (Filter.atTop.limUnder ψ)) :=
    MeasureTheory.tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi hderiv hint
  -- That limit is `0`: otherwise `|ψ|` stays away from `0` at infinity, forcing
  -- `G z ^ 2 ≥ c / z` on a half-line, contradicting `G ^ 2 ∈ L¹`.
  have hlim0 : Filter.atTop.limUnder ψ = 0 := by
    by_contra hne
    have hpos : 0 < |Filter.atTop.limUnder ψ| / 2 := half_pos (abs_pos.mpr hne)
    obtain ⟨R, hR⟩ :=
      Metric.tendsto_atTop.mp hlim (|Filter.atTop.limUnder ψ| / 2) hpos
    set R' : ℝ := max R 1 with hR'def
    have hR'1 : (1 : ℝ) ≤ R' := le_max_right R 1
    have hR'0 : (0 : ℝ) ≤ R' := le_trans zero_le_one hR'1
    have hRR' : R ≤ R' := le_max_left R 1
    -- the pointwise lower bound on `G ^ 2` on `(R', ∞)`
    have hkey : ∀ z, R' ≤ z → ((|Filter.atTop.limUnder ψ| / 2) / C) * z⁻¹ ≤ G z ^ 2 := by
      intro z hz
      have hz1 : 0 < z := lt_of_lt_of_le one_pos (le_trans hR'1 hz)
      have hdist : dist (ψ z) (Filter.atTop.limUnder ψ) < |Filter.atTop.limUnder ψ| / 2 :=
        hR z (le_trans hRR' hz)
      have hosc : |Filter.atTop.limUnder ψ| / 2 ≤ |ψ z| := by
        have h := abs_sub_abs_le_abs_sub (Filter.atTop.limUnder ψ) (ψ z)
        rw [abs_sub_comm (Filter.atTop.limUnder ψ) (ψ z)] at h
        rw [Real.dist_eq] at hdist
        linarith
      have h2 : |Filter.atTop.limUnder ψ| / 2 ≤ C * (z * G z ^ 2) :=
        le_trans hosc (hbd z (le_of_lt hz1))
      have hCz : 0 < C * z := mul_pos hC hz1
      have hdiv : (|Filter.atTop.limUnder ψ| / 2) / (C * z) ≤ G z ^ 2 := by
        rw [div_le_iff₀ hCz]
        nlinarith [h2]
      have heq : (|Filter.atTop.limUnder ψ| / 2) / (C * z)
          = ((|Filter.atTop.limUnder ψ| / 2) / C) * z⁻¹ := by
        rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]
        ring
      rwa [heq] at hdiv
    -- hence `z ↦ c / z` is integrable on `(R', ∞)`, which is false
    have hgint : MeasureTheory.IntegrableOn (fun z => G z ^ 2) (Set.Ioi R') :=
      hG.mono_set (Set.Ioi_subset_Ioi hR'0)
    have hcpos : 0 < (|Filter.atTop.limUnder ψ| / 2) / C := div_pos hpos hC
    have hsmall : MeasureTheory.IntegrableOn
        (fun z => ((|Filter.atTop.limUnder ψ| / 2) / C) * z⁻¹) (Set.Ioi R') := by
      refine hgint.mono' ((measurable_const.mul measurable_inv).aestronglyMeasurable) ?_
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
      refine Filter.Eventually.of_forall (fun z hz => ?_)
      have hz0 : R' ≤ z := le_of_lt hz
      have hz1 : 0 < z := by linarith [hR'1, hz0]
      have hnorm : ‖((|Filter.atTop.limUnder ψ| / 2) / C) * z⁻¹‖
          = ((|Filter.atTop.limUnder ψ| / 2) / C) * z⁻¹ := by
        rw [Real.norm_eq_abs, abs_of_pos (mul_pos hcpos (inv_pos.mpr hz1))]
      rw [hnorm]
      exact hkey z (le_of_lt hz)
    have hone : MeasureTheory.IntegrableOn (fun z => z⁻¹) (Set.Ioi R') := by
      have h' : MeasureTheory.Integrable
          (fun z : ℝ => (((|Filter.atTop.limUnder ψ| / 2) / C) : ℝ) • z⁻¹) _ := hsmall
      exact (MeasureTheory.integrable_smul_iff hcpos.ne' (fun z : ℝ => z⁻¹)).mp h'
    exact not_integrableOn_Ioi_inv hone
  simpa [hlim0] using hlim

end Work.FTS.H2.Transport3Aux.MismatchBad
