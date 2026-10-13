import Mathlib
import Submission.Work.WilC4aP.complexify_coeff

open Filter Function
open scoped Topology

namespace Work.WilE3.Taylor.Arc

/-- For an analytic function given by a *nonzero* formal power series `p` at `z₀`, the order of
vanishing equals the order of the power series. -/
theorem analyticOrderAt_eq_order_coe {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {f : 𝕜 → E} {p : FormalMultilinearSeries 𝕜 𝕜 E} {z₀ : 𝕜}
    (hp : HasFPowerSeriesAt f p z₀) (h : p ≠ 0) :
    analyticOrderAt f z₀ = (p.order : ℕ∞) := by
  rw [hp.analyticAt.analyticOrderAt_eq_natCast]
  refine ⟨(swap dslope z₀)^[p.order] f, ?_, ?_, ?_⟩
  · exact (hp.has_fpower_series_iterate_dslope_fslope p.order).analyticAt
  · exact hp.iterate_dslope_fslope_ne_zero h
  · filter_upwards with z
    exact hp.eq_pow_order_mul_iterate_dslope z

/-- For an analytic function whose formal power series at `z₀` vanishes identically, the order of
vanishing is infinite. -/
theorem analyticOrderAt_eq_top_of_series_eq_zero {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {f : 𝕜 → E} {p : FormalMultilinearSeries 𝕜 𝕜 E} {z₀ : 𝕜}
    (hp : HasFPowerSeriesAt f p z₀) (h : p = 0) :
    analyticOrderAt f z₀ = ⊤ := by
  rw [analyticOrderAt_eq_top]
  exact hp.locally_zero_iff.mpr h

/-- Every real analytic function germ at `0` is the restriction to the reals of a holomorphic
function on a complex disk, and the order of vanishing at `0` is preserved. -/
theorem complexify_order (g : ℝ → ℝ) (hg : AnalyticAt ℝ g 0) :
    ∃ (F : ℂ → ℂ) (ρ : ℝ), 0 < ρ ∧ AnalyticOnNhd ℂ F (Metric.ball 0 ρ) ∧
      (∀ x : ℝ, |x| < ρ → F (x : ℂ) = (g x : ℂ)) ∧
      analyticOrderAt F 0 = analyticOrderAt g 0 := by
  obtain ⟨p, s, hs⟩ := hg
  obtain ⟨r, hrpos, hrlt⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hs.r_pos
  have hrR : 0 < (r : ℝ) := NNReal.coe_pos.mpr (ENNReal.coe_pos.mp hrpos)
  -- The complexified formal power series, obtained from the real one by extending scalars.
  let q : FormalMultilinearSeries ℂ ℂ ℂ :=
    fun n => ContinuousMultilinearMap.mkPiRing ℂ (Fin n) ((p.coeff n : ℂ))
  have hqcoeff : ∀ n, q.coeff n = (p.coeff n : ℂ) := by
    intro n
    simp only [FormalMultilinearSeries.coeff, q, ContinuousMultilinearMap.mkPiRing_apply,
      Pi.one_apply, Finset.prod_const_one, one_smul]
  have hqnorm : ∀ n, ‖q n‖ = ‖p n‖ := by
    intro n
    rw [FormalMultilinearSeries.norm_apply_eq_norm_coef (p := q), hqcoeff n,
      FormalMultilinearSeries.norm_apply_eq_norm_coef (p := p)]
    simp
  have hqradius : q.radius = p.radius := by
    apply le_antisymm
    · exact FormalMultilinearSeries.radius_le_of_le (fun n => le_of_eq (hqnorm n).symm)
    · exact FormalMultilinearSeries.radius_le_of_le (fun n => le_of_eq (hqnorm n))
  have hpr : 0 < p.radius := lt_of_lt_of_le (lt_trans hrpos hrlt) hs.r_le
  have hqr : 0 < q.radius := by rw [hqradius]; exact hpr
  have hp : HasFPowerSeriesAt g p 0 := hs.hasFPowerSeriesAt
  have hq : HasFPowerSeriesAt q.sum q 0 :=
    (FormalMultilinearSeries.hasFPowerSeriesOnBall q hqr).hasFPowerSeriesAt
  -- The complexified series vanishes exactly in the same degrees as the real one.
  have hiff : ∀ n, q n = 0 ↔ p n = 0 := by
    intro n
    rw [← norm_eq_zero, hqnorm n, norm_eq_zero]
  have horder : q.order = p.order := by
    have hset : {n : ℕ | q n ≠ 0} = {n : ℕ | p n ≠ 0} := by
      ext n; exact not_congr (hiff n)
    simp only [FormalMultilinearSeries.order]
    rw [hset]
  refine ⟨q.sum, (r : ℝ), hrR, ?_, ?_, ?_⟩
  · -- Analyticity of the sum on the complex disk.
    rw [← Metric.eball_ofReal (x := (0 : ℂ)) (ε := (r : ℝ))]
    refine (FormalMultilinearSeries.analyticOnNhd (p := q)).mono ?_
    refine Metric.eball_subset_eball ?_
    rw [ENNReal.ofReal_coe_nnreal, hqradius]
    exact hrlt.le.trans hs.r_le
  · -- Agreement with `g` on real points.
    intro x hx
    have hxs : x ∈ Metric.eball (0 : ℝ) s := by
      rw [Metric.mem_eball, edist_zero_right, Real.enorm_eq_ofReal_abs]
      have h1 : ENNReal.ofReal |x| < ENNReal.ofReal (r : ℝ) :=
        (ENNReal.ofReal_lt_ofReal_iff (q := (r : ℝ)) hrR).mpr hx
      rw [ENNReal.ofReal_coe_nnreal] at h1
      exact h1.trans hrlt
    have hreal : HasSum (fun n => x ^ n * p.coeff n) (g x) := by
      have h := hs.hasSum hxs
      simpa only [zero_add, FormalMultilinearSeries.apply_eq_pow_smul_coeff (p := p),
        smul_eq_mul] using h
    have hqtsum : q.sum (x : ℂ) = ∑' n, (x : ℂ) ^ n * (p.coeff n : ℂ) := by
      simp only [FormalMultilinearSeries.sum]
      apply tsum_congr
      intro n
      rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff, hqcoeff n, smul_eq_mul]
    have hcsum : ∑' n, (x : ℂ) ^ n * (p.coeff n : ℂ) = ((g x : ℝ) : ℂ) := by
      have h1 : Complex.ofRealCLM (∑' n, x ^ n * p.coeff n)
          = ∑' n, (x : ℂ) ^ n * (p.coeff n : ℂ) := by
        rw [ContinuousLinearMap.map_tsum Complex.ofRealCLM hreal.summable]
        apply tsum_congr
        intro n
        simp only [Complex.ofRealCLM_apply, Complex.ofReal_mul, Complex.ofReal_pow]
      rw [← h1, hreal.tsum_eq, Complex.ofRealCLM_apply]
    rw [hqtsum, hcsum]
  · -- Equality of the orders of vanishing at `0`.
    by_cases hp0 : p = 0
    · have hq0 : q = 0 := funext fun n => (hiff n).mpr (by rw [hp0]; rfl)
      rw [analyticOrderAt_eq_top_of_series_eq_zero hp hp0,
        analyticOrderAt_eq_top_of_series_eq_zero hq hq0]
    · have hq0 : q ≠ 0 := by
        intro h
        exact hp0 (funext fun n => (hiff n).mp (by rw [h]; rfl))
      rw [analyticOrderAt_eq_order_coe hp hp0, analyticOrderAt_eq_order_coe hq hq0, horder]

end Work.WilE3.Taylor.Arc
