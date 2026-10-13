import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.le_zero_of_tendsto_nhdsGT_zero_of_integrableOn_div
import Submission.Work.FTS.EllipticEst.remov.coerc.inv_sq_lower_sq_not_integrable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov.coerc

/-- If `φ θ = O(θ)` as `θ → 0⁺`, `f²` is integrable near `0` and `φ θ * f θ` has a limit
`d` as `θ → 0⁺`, then `d = 0`.

Indeed, if `d ≠ 0` then `|φ θ * f θ| ≥ |d|/2` and `|φ θ| ≤ C θ` on a small interval
`(0, δ)`, so `(f θ)² ≥ k / θ²` there with `k = d²/(4C²) > 0`.  This contradicts the
integrability of `f²` on `(0, δ)` (via
`Work.FTS.EllipticEst.remov.coerc.inv_sq_lower_sq_not_integrable`). -/
theorem mul_sq_vanishing {f φ : ℝ → ℝ} {C d : ℝ} (hC : 0 < C)
    (hφ : ∀ᶠ θ in nhdsWithin (0 : ℝ) (Set.Ioi 0), |φ θ| ≤ C * θ)
    (hf : MeasureTheory.IntegrableOn (fun θ => (f θ) ^ 2) (Set.Ioo 0 1))
    (hw : Filter.Tendsto (fun θ => φ θ * f θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds d)) :
    d = 0 := by
  by_contra hd
  set k : ℝ := d ^ 2 / (4 * C ^ 2) with hkdef
  have hkpos : 0 < k := by
    rw [hkdef]
    exact div_pos (sq_pos_of_ne_zero hd) (by positivity)
  -- Extract the two eventual bounds as explicit thresholds.
  have hφ' := hφ
  rw [eventually_nhdsWithin_iff] at hφ'
  rw [Metric.eventually_nhds_iff] at hφ'
  obtain ⟨ε₁, hε₁, hε₁'⟩ := hφ'
  have hw1 : ∀ᶠ θ in nhdsWithin (0 : ℝ) (Set.Ioi 0), |d| / 2 < |φ θ * f θ| :=
    hw.abs.eventually (Ioi_mem_nhds (by have := abs_pos.mpr hd; linarith))
  rw [eventually_nhdsWithin_iff] at hw1
  rw [Metric.eventually_nhds_iff] at hw1
  obtain ⟨ε₂, hε₂, hε₂'⟩ := hw1
  set ε : ℝ := min ε₁ (min ε₂ 1) with hεdef
  have hεle₁ : ε ≤ ε₁ := by rw [hεdef]; exact min_le_left _ _
  have hεle₂ : ε ≤ ε₂ := by rw [hεdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hεle1 : ε ≤ 1 := by rw [hεdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hεpos : 0 < ε := by rw [hεdef]; exact lt_min hε₁ (lt_min hε₂ one_pos)
  set δ : ℝ := ε / 2 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; linarith
  have hδltε : δ < ε := by rw [hδdef]; linarith
  have hδle1 : δ ≤ 1 := by rw [hδdef]; linarith
  -- The lower bound for `f²` on `(0, δ)`.
  have hlow : ∀ θ ∈ Set.Ioo (0 : ℝ) δ, k / θ ^ 2 ≤ (f θ) ^ 2 := by
    intro θ hθ
    have hθpos : 0 < θ := hθ.1
    have hθltε : θ < ε := lt_trans hθ.2 hδltε
    have hdist₁ : dist θ 0 < ε₁ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hθpos]; exact lt_of_lt_of_le hθltε hεle₁
    have hdist₂ : dist θ 0 < ε₂ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hθpos]; exact lt_of_lt_of_le hθltε hεle₂
    have hφb : |φ θ| ≤ C * θ := hε₁' hdist₁ hθpos
    have hprod : |d| / 2 < |φ θ * f θ| := hε₂' hdist₂ hθpos
    rw [abs_mul] at hprod
    have hd2pos : 0 < |d| / 2 := by have := abs_pos.mpr hd; linarith
    have hmul : 0 < |φ θ| * |f θ| := lt_trans hd2pos hprod
    have habsφ : 0 < |φ θ| := pos_of_mul_pos_left hmul (abs_nonneg _)
    have hCθpos : 0 < C * θ := lt_of_lt_of_le habsφ hφb
    have hstep1 : (|d| / 2) / (C * θ) ≤ (|d| / 2) / |φ θ| :=
      div_le_div_of_nonneg_left (by positivity) habsφ hφb
    have hstep2 : (|d| / 2) / |φ θ| < |f θ| := by
      have h := div_lt_div_of_pos_right hprod habsφ
      rwa [mul_div_cancel_left₀ (|f θ|) (ne_of_gt habsφ)] at h
    have hfz : (|d| / 2) / (C * θ) ≤ |f θ| := le_of_lt (lt_of_le_of_lt hstep1 hstep2)
    have hsq : ((|d| / 2) / (C * θ)) ^ 2 ≤ (f θ) ^ 2 := by
      have h0 : (0 : ℝ) ≤ (|d| / 2) / (C * θ) := div_nonneg (by positivity) hCθpos.le
      have h2 : ((|d| / 2) / (C * θ)) ^ 2 ≤ (|f θ|) ^ 2 := by
        rw [sq, sq]; exact mul_self_le_mul_self h0 hfz
      rwa [sq_abs] at h2
    have hsqeq : ((|d| / 2) / (C * θ)) ^ 2 = k / θ ^ 2 := by
      rw [hkdef]
      have habs : (|d| / 2) ^ 2 = d ^ 2 / 4 := by rw [div_pow, sq_abs]; norm_num
      rw [div_pow, mul_pow, habs, div_div, div_div]
      ring
    rw [← hsqeq]
    exact hsq
  have hfδ : MeasureTheory.IntegrableOn (fun θ => (f θ) ^ 2) (Set.Ioo 0 δ) :=
    hf.mono_set (fun θ hθ => ⟨hθ.1, lt_of_lt_of_le hθ.2 hδle1⟩)
  exact inv_sq_lower_sq_not_integrable hδpos hkpos hfδ hlow

end Work.FTS.EllipticEst.remov.coerc
