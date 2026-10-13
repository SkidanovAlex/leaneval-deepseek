import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.remov.coerc.not_integrableOn_of_le_div_sub_pow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology
set_option maxHeartbeats 800000

namespace Work.FTS.EllipticEst.remov.coerc

theorem mul_sq_vanishing_right {f φ : ℝ → ℝ} {b C d : ℝ} (hC : 0 < C)
    (hφ : ∀ᶠ θ in nhdsWithin b (Set.Iio b), |φ θ| ≤ C * (b - θ))
    (hf : MeasureTheory.IntegrableOn (fun θ => (f θ) ^ 2) (Set.Ioo (b - 1) b))
    (hw : Filter.Tendsto (fun θ => φ θ * f θ) (nhdsWithin b (Set.Iio b)) (nhds d)) :
    d = 0 := by
  by_contra hd
  have hdabs : 0 < |d| := abs_pos.mpr hd
  have hε2 : 0 < |d| / 2 := by linarith
  have h2 : ∀ᶠ θ in nhdsWithin b (Set.Iio b), |φ θ * f θ - d| < |d| / 2 := by
    have hh := (Metric.tendsto_nhds.mp hw) (|d| / 2) hε2
    filter_upwards [hh] with θ hθ
    rwa [Real.dist_eq] at hθ
  have h3 : ∀ᶠ θ in nhdsWithin b (Set.Iio b),
      |φ θ| ≤ C * (b - θ) ∧ |φ θ * f θ - d| < |d| / 2 := hφ.and h2
  rw [eventually_nhdsWithin_iff] at h3
  rw [Metric.eventually_nhds_iff] at h3
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := h3
  set δ : ℝ := min δ₀ 1 with hδdef
  have hδpos : 0 < δ := lt_min hδ₀pos one_pos
  have hδle : δ ≤ δ₀ := min_le_left _ _
  have hδle1 : δ ≤ 1 := min_le_right _ _
  have hmem : Set.Ioo (b - δ) b ⊆ Set.Ioo (b - 1) b :=
    fun x hx => ⟨by linarith [hx.1, hδle1], hx.2⟩
  have hpt : ∀ θ ∈ Set.Ioo (b - δ) b,
      (|d| / (2 * C)) ^ 2 / (b - θ) ^ 2 ≤ (f θ) ^ 2 := by
    intro θ hθ
    have hbθ : 0 < b - θ := by linarith [hθ.2]
    have hdb : dist θ b < δ₀ := by
      rw [Real.dist_eq, abs_of_neg (by linarith [hθ.2] : θ - b < 0)]
      linarith [hθ.1, hδle]
    obtain ⟨hφθ, hwθ⟩ := hδ₀ hdb hθ.2
    have habs : |d| / 2 < |φ θ| * |f θ| := by
      have h1 : |d| ≤ |φ θ * f θ| + |φ θ * f θ - d| := by
        calc |d| = |φ θ * f θ + (d - φ θ * f θ)| := by
              rw [show φ θ * f θ + (d - φ θ * f θ) = d from by ring]
          _ ≤ |φ θ * f θ| + |d - φ θ * f θ| := abs_add_le _ _
          _ = |φ θ * f θ| + |φ θ * f θ - d| := by rw [abs_sub_comm]
      rw [abs_mul] at h1
      linarith
    have hfb : (|d| / 2) / (C * (b - θ)) < |f θ| := by
      rw [div_lt_iff₀ (mul_pos hC hbθ)]
      have h3' : |φ θ| * |f θ| ≤ |f θ| * (C * (b - θ)) := by
        calc |φ θ| * |f θ| ≤ (C * (b - θ)) * |f θ| :=
              mul_le_mul_of_nonneg_right hφθ (abs_nonneg _)
          _ = |f θ| * (C * (b - θ)) := by ring
      linarith
    have hsq : ((|d| / 2) / (C * (b - θ))) ^ 2 ≤ (f θ) ^ 2 := by
      have hnn : 0 ≤ (|d| / 2) / (C * (b - θ)) := by positivity
      have h := pow_le_pow_left₀ hnn (le_of_lt hfb) 2
      rwa [sq_abs] at h
    have halg : ((|d| / 2) / (C * (b - θ))) ^ 2 = (|d| / (2 * C)) ^ 2 / (b - θ) ^ 2 := by
      rw [div_pow, div_pow, mul_pow]
      field_simp
    rw [halg] at hsq
    exact hsq
  have hfδ : MeasureTheory.IntegrableOn (fun θ => (f θ) ^ 2) (Set.Ioo (b - δ) b) :=
    hf.mono_set hmem
  have hcpos : 0 < (|d| / (2 * C)) ^ 2 :=
    pow_pos (div_pos hdabs (by linarith)) 2
  exact (not_integrableOn_of_le_div_sub_pow (f := fun θ => (f θ) ^ 2) (c := (|d| / (2 * C)) ^ 2)
      (b := b) (ε := δ) hcpos hδpos (k := 2) (by norm_num) hpt) hfδ

end Work.FTS.EllipticEst.remov.coerc
