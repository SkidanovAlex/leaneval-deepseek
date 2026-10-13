import Mathlib
import Submission.Work.WilC4aP.Basic

set_option autoImplicit false

open scoped BigOperators

namespace Work.WilC4aP

/-- Every real-analytic function at `0` is the restriction of a holomorphic function on a
complex disk.

PROOF HINT: `AnalyticAt ℝ c 0` unfolds to `HasFPowerSeriesAt c p 0` for a real formal
multilinear series `p`; the coefficients `p n (fun _ => 1)` are real, the series
`Σ n, p n (fun _ => 1) * z ^ n` converges on the disk of convergence (compare
`‖p n (fun _ => 1)‖ * ‖x‖ ^ n = ‖p n (fun _ => x)‖`), giving `F`; use
`HasFPowerSeriesAt.analyticAt`. -/
theorem complexify_coeff (c : ℝ → ℝ) (hc : AnalyticAt ℝ c 0) :
    ∃ (F : ℂ → ℂ) (ρ : ℝ), 0 < ρ ∧ AnalyticOnNhd ℂ F (Metric.ball 0 ρ) ∧
      ∀ x : ℝ, |x| < ρ → F (x : ℂ) = (c x : ℂ) := by
  obtain ⟨p, s, hs⟩ := hc
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
  refine ⟨q.sum, (r : ℝ), hrR, ?_, ?_⟩
  · rw [← Metric.eball_ofReal (x := (0 : ℂ)) (ε := (r : ℝ))]
    refine (FormalMultilinearSeries.analyticOnNhd (p := q)).mono ?_
    refine Metric.eball_subset_eball ?_
    rw [ENNReal.ofReal_coe_nnreal, hqradius]
    exact hrlt.le.trans hs.r_le
  · intro x hx
    have hxs : x ∈ Metric.eball (0 : ℝ) s := by
      rw [Metric.mem_eball, edist_zero_right, Real.enorm_eq_ofReal_abs]
      have h1 : ENNReal.ofReal |x| < ENNReal.ofReal (r : ℝ) :=
        (ENNReal.ofReal_lt_ofReal_iff (q := (r : ℝ)) hrR).mpr hx
      rw [ENNReal.ofReal_coe_nnreal] at h1
      exact h1.trans hrlt
    have hreal : HasSum (fun n => x ^ n * p.coeff n) (c x) := by
      have h := hs.hasSum hxs
      simpa only [zero_add, FormalMultilinearSeries.apply_eq_pow_smul_coeff (p := p),
        smul_eq_mul] using h
    have hqtsum : q.sum (x : ℂ) = ∑' n, (x : ℂ) ^ n * (p.coeff n : ℂ) := by
      simp only [FormalMultilinearSeries.sum]
      apply tsum_congr
      intro n
      rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff, hqcoeff n, smul_eq_mul]
    have hcsum : ∑' n, (x : ℂ) ^ n * (p.coeff n : ℂ) = ((c x : ℝ) : ℂ) := by
      have h1 : Complex.ofRealCLM (∑' n, x ^ n * p.coeff n)
          = ∑' n, (x : ℂ) ^ n * (p.coeff n : ℂ) := by
        rw [ContinuousLinearMap.map_tsum Complex.ofRealCLM hreal.summable]
        apply tsum_congr
        intro n
        simp only [Complex.ofRealCLM_apply, Complex.ofReal_mul, Complex.ofReal_pow]
      rw [← h1, hreal.tsum_eq, Complex.ofRealCLM_apply]
    rw [hqtsum, hcsum]

end Work.WilC4aP
