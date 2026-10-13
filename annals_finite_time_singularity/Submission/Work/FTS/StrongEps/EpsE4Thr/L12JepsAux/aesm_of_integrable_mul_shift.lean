import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Measure.Haar.Unique

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.L12JepsAux

open MeasureTheory Filter Set

/-- **Measurability by convolution inversion.**

Let `k : ℝ × ℝ → ℝ` be continuous and positive at some point, and let `g : ℝ × ℝ → ℝ` be such
that for every shift `x` the function `p ↦ k p * g (x - p)` is integrable. Then `g` is almost
everywhere strongly measurable.

The point is that `k` does not vanish on a ball `B(c, r)`; on that ball one recovers
`g (x - p) = (k p)⁻¹ * (k p * g (x - p))`, so `g ∘ (x - ·)` is a.e. strongly measurable on the
ball, and — the map `y ↦ x - y` being a measure preserving involution — `g` is a.e. strongly
measurable on the translate `{y | k (x - y) ≠ 0}` of that ball.  Countably many translates of
the ball cover the plane, and a.e. strong measurability is local with respect to countable
unions. -/
theorem aesm_of_integrable_mul_shift {k g : ℝ × ℝ → ℝ} (hk : Continuous k)
    (hpos : ∃ p : ℝ × ℝ, 0 < k p)
    (h : ∀ x : ℝ × ℝ, MeasureTheory.Integrable (fun p : ℝ × ℝ => k p * g (x - p))
      MeasureTheory.volume) :
    MeasureTheory.AEStronglyMeasurable g MeasureTheory.volume := by
  -- A ball on which `k` does not vanish.
  obtain ⟨c, r, hr, hrK⟩ :
      ∃ c : ℝ × ℝ, ∃ r : ℝ, 0 < r ∧ Metric.ball c r ⊆ {p : ℝ × ℝ | k p ≠ 0} := by
    have hKopen : IsOpen {p : ℝ × ℝ | k p ≠ 0} :=
      (isOpen_compl_singleton (x := (0 : ℝ))).preimage hk
    obtain ⟨c, hc⟩ : ∃ c : ℝ × ℝ, k c ≠ 0 := by
      obtain ⟨p, hp⟩ := hpos
      exact ⟨p, ne_of_gt hp⟩
    obtain ⟨r, hr, hrK⟩ := Metric.isOpen_iff.mp hKopen c hc
    exact ⟨c, r, hr, hrK⟩
  -- For every shift `x`, `g` is a.e. strongly measurable where `k (x - ·)` does not vanish.
  have key : ∀ x : ℝ × ℝ,
      AEStronglyMeasurable g (volume.restrict {y : ℝ × ℝ | k (x - y) ≠ 0}) := by
    intro x
    obtain ⟨m, hm_strong, hm_ae⟩ := (h x).aestronglyMeasurable
    have hm_meas : Measurable m := hm_strong.measurable
    let m' : ℝ × ℝ → ℝ := fun p => (k p)⁻¹ * m p
    have hm'_meas : Measurable m' := (hk.measurable.inv).mul hm_meas
    -- pointwise recovery of `g (x - p)` from the a.e. representative of `k · g (x - ·)`
    have hglob : ∀ᵐ p ∂volume, k p ≠ 0 → m' p = g (x - p) := by
      filter_upwards [hm_ae] with p hp hpK
      simp only [m']
      rw [← hp, inv_mul_cancel_left₀ hpK]
    -- transport along the measure preserving involution `y ↦ x - y`
    have hTmeas : Measurable (fun y : ℝ × ℝ => x - y) :=
      (by fun_prop : Continuous (fun y : ℝ × ℝ => x - y)).measurable
    have hT : MeasurePreserving (fun y : ℝ × ℝ => x - y) volume volume :=
      ⟨hTmeas, Measure.map_sub_left_eq_self volume x⟩
    have hglob' := hT.quasiMeasurePreserving.ae hglob
    have hAmeas : MeasurableSet {y : ℝ × ℝ | k (x - y) ≠ 0} :=
      ((isOpen_compl_singleton (x := (0 : ℝ))).preimage
        (by fun_prop : Continuous (fun y : ℝ × ℝ => k (x - y)))).measurableSet
    refine AEStronglyMeasurable.congr (f := fun y : ℝ × ℝ => m' (x - y)) ?_ ?_
    · exact (hm'_meas.comp hTmeas).aestronglyMeasurable.restrict
    · change ∀ᵐ y ∂(volume.restrict {y : ℝ × ℝ | k (x - y) ≠ 0}), m' (x - y) = g y
      rw [ae_restrict_iff' hAmeas]
      filter_upwards [hglob'] with y hy
      intro hyK
      have := hy hyK
      rwa [sub_sub_self] at this
  -- countably many translates of the ball already cover the plane
  have hcover :
      (⋃ q : ℚ × ℚ, {y : ℝ × ℝ | k ((((q.1 : ℝ), (q.2 : ℝ)) + c) - y) ≠ 0}) = univ := by
    rw [eq_univ_iff_forall]
    intro y
    simp only [mem_iUnion]
    have h₁ : ∃ q : ℚ, |(q : ℝ) - y.1| < r / 2 := by
      obtain ⟨q, hq⟩ := exists_rat_btwn (x := y.1 - r / 2) (y := y.1 + r / 2) (by linarith)
      exact ⟨q, by rw [abs_lt]; exact ⟨by linarith, by linarith⟩⟩
    have h₂ : ∃ q : ℚ, |(q : ℝ) - y.2| < r / 2 := by
      obtain ⟨q, hq⟩ := exists_rat_btwn (x := y.2 - r / 2) (y := y.2 + r / 2) (by linarith)
      exact ⟨q, by rw [abs_lt]; exact ⟨by linarith, by linarith⟩⟩
    obtain ⟨q₁, hq₁⟩ := h₁
    obtain ⟨q₂, hq₂⟩ := h₂
    refine ⟨(q₁, q₂), ?_⟩
    have hd : dist (((q₁ : ℝ), (q₂ : ℝ)) : ℝ × ℝ) y < r := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      exact max_lt (by linarith) (by linarith)
    have hmem : ((((q₁ : ℝ), (q₂ : ℝ)) + c) - y) ∈ Metric.ball c r := by
      rw [Metric.mem_ball]
      have hdist : dist ((((q₁ : ℝ), (q₂ : ℝ)) + c) - y) c
          = dist (((q₁ : ℝ), (q₂ : ℝ)) : ℝ × ℝ) y := by
        rw [dist_eq_norm, dist_eq_norm]
        congr 1
        abel
      rw [hdist]
      exact hd
    exact hrK hmem
  have hU := AEStronglyMeasurable.iUnion
    (s := fun q : ℚ × ℚ => {y : ℝ × ℝ | k ((((q.1 : ℝ), (q.2 : ℝ)) + c) - y) ≠ 0})
    (fun q => key (((q.1 : ℝ), (q.2 : ℝ)) + c))
  rwa [hcover, Measure.restrict_univ] at hU

end Work.FTS.StrongEps.EpsE4Thr.L12JepsAux
