import Mathlib
import Submission.UnifDeps
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.H0_regular_aux
import Submission.Work.EQ.cayley_homeomorph_uhp
import Submission.Work.Covering.exists_tendsto_of_isCoveringMap_comp

/-!
# The hyperbolic case of Rychlik's Theorems 10–11: disc cover and rays

If a component `S` of `H0` is uniformised by the upper half plane, composing with the Cayley
homeomorphism gives a covering of `S` by the open unit disc `𝔻`.  The radius
`r ↦ r e^{iθ}` of `𝔻` has no limit as `r → 1⁻`; since a covering does not create limits
(`exists_tendsto_of_isCoveringMap_comp`), neither has its image in `S`.  This is the
"path lifting" input to Rychlik's Theorem 11.
-/

noncomputable section

open Filter _root_.Topology Complex Metric

namespace Work.EQ

/-- The open unit disc, as a type. -/
abbrev Disc : Type := ↥(Metric.ball (0 : ℂ) 1)

/-- The radius of the unit disc in direction `θ`, as a path `ℝ → 𝔻` (constant off `(0,1)`, where
the values are anyway irrelevant). -/
noncomputable def discRay (θ : ℝ) : ℝ → Disc :=
  fun r => if hr : r ∈ Set.Ioo (0 : ℝ) 1 then
    ⟨(r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I), by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero, norm_mul, Complex.norm_exp_ofReal_mul_I,
        mul_one]
      have hnorm : ‖(r : ℂ)‖ = |r| := RCLike.norm_ofReal r
      rw [hnorm, abs_of_pos hr.1]
      exact hr.2⟩
    else ⟨0, by simp [Metric.mem_ball]⟩

theorem discRay_coe {θ r : ℝ} (hr : r < 1) :
    ((discRay θ r : Disc) : ℂ) = ((max r 0 : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
  rw [discRay]
  by_cases h : r ∈ Set.Ioo (0 : ℝ) 1
  · rw [dif_pos h, max_eq_left (le_of_lt h.1)]
  · have hr0 : r ≤ 0 := by
      by_contra hlt
      exact h ⟨not_le.mp hlt, hr⟩
    rw [dif_neg h, max_eq_right hr0]
    simp

theorem continuousOn_discRay (θ : ℝ) : ContinuousOn (discRay θ) (Set.Iio (1 : ℝ)) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hmaxℝ : Continuous fun r : ↥(Set.Iio (1 : ℝ)) => max (r : ℝ) (0 : ℝ) :=
    continuous_subtype_val.max continuous_const
  have hmax : Continuous fun r : ↥(Set.Iio (1 : ℝ)) => ((max (r : ℝ) (0 : ℝ) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp hmaxℝ
  have hcoer : Continuous fun r : ↥(Set.Iio (1 : ℝ)) => (((discRay θ r : Disc)) : ℂ) := by
    refine (hmax.mul continuous_const :
      Continuous fun r : ↥(Set.Iio (1 : ℝ)) =>
        ((max (r : ℝ) 0 : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)).congr fun r => ?_
    exact (discRay_coe (θ := θ) r.2).symm
  exact Continuous.subtype_mk (f := fun r : ↥(Set.Iio (1 : ℝ)) => ((discRay θ r : Disc) : ℂ))
    hcoer (fun r => (discRay θ r).2)

/-- **The radius of the disc has no limit at `1⁻`.** -/
theorem not_tendsto_discRay (θ : ℝ) :
    ¬ ∃ x : Disc, Tendsto (discRay θ) (nhdsWithin 1 (Set.Iio (1 : ℝ))) (nhds x) := by
  rintro ⟨x, hx⟩
  haveI : NeBot (nhdsWithin 1 (Set.Iio (1 : ℝ))) := nhdsWithin_Iio_neBot le_rfl
  have h1 : Tendsto (fun r : ℝ => ((discRay θ r : Disc) : ℂ)) (nhdsWithin 1 (Set.Iio (1 : ℝ)))
      (nhds (x : ℂ)) := tendsto_subtype_rng.mp hx
  have h2 : Tendsto (fun r : ℝ => r * Complex.exp ((θ : ℂ) * Complex.I))
      (nhdsWithin 1 (Set.Iio (1 : ℝ))) (nhds (1 * Complex.exp ((θ : ℂ) * Complex.I))) := by
    have hc : Continuous fun r : ℝ => (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) :=
      Complex.continuous_ofReal.mul continuous_const
    exact (hc.continuousAt (x := (1 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have heq : (fun r : ℝ => ((discRay θ r : Disc) : ℂ))
      =ᶠ[nhdsWithin 1 (Set.Iio (1 : ℝ))] fun r : ℝ => (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
    filter_upwards [(nhdsLT_basis (1 : ℝ)).mem_iff.mpr ⟨0, zero_lt_one, fun t ht => ht⟩]
      with r hr
    rw [discRay_coe hr.2, max_eq_left (le_of_lt hr.1)]
  have h3 := h2.congr' heq.symm
  have h4 : (x : ℂ) = Complex.exp ((θ : ℂ) * Complex.I) :=
    tendsto_nhds_unique h1 (by simpa using h3)
  have h5 : ‖(x : ℂ)‖ < 1 := by
    have := x.2
    rwa [Metric.mem_ball, dist_eq_norm, sub_zero] at this
  rw [h4, Complex.norm_exp_ofReal_mul_I] at h5
  exact lt_irrefl 1 h5

/-- A covering does not create limits, so the image of a radius in the base has no limit. -/
theorem not_tendsto_comp_discRay {S : Type*} [TopologicalSpace S] {q : Disc → S}
    (hq : IsCoveringMap q) (θ : ℝ) :
    ¬ ∃ x : S, Tendsto (fun r : ℝ => q (discRay θ r)) (nhdsWithin 1 (Set.Iio (1 : ℝ))) (nhds x) := by
  rintro ⟨x, hx⟩
  exact not_tendsto_discRay θ
    (exists_tendsto_of_isCoveringMap_comp hq (continuousOn_discRay θ) hx)

/-- A covering of `S` by the upper half plane gives a covering of `S` by the unit disc. -/
theorem exists_disc_covering_of_uhp {S : Type*} [TopologicalSpace S] {p : UpperHalfPlane → S}
    (hp : IsCoveringMap p) : ∃ q : Disc → S, IsCoveringMap q := by
  obtain ⟨e, -, -⟩ := cayley_homeomorph_uhp
  exact ⟨p ∘ (⇑e), hp.comp_homeomorph e⟩

end Work.EQ
