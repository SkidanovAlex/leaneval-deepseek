import Mathlib
import Submission.Commons.Geometry.Ulam.integrable_ball_section_affine_of_intervalIntegrable

namespace Commons.Geometry.Ulam

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

lemma integral_fin_ball_section_affine_not_integrable {m : ℕ} [Nonempty (Fin m)] {a b s h : ℝ} {f : ℝ → ℝ}
    {A B C : ℝ}
    (hab : a ≤ b) (hf_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ f t) (hf_meas : Measurable f)
    (h_int : ¬ Integrable (({p : ℝ × (ℝ × (Fin m → ℝ)) | p.1 ∈ Set.Icc a b ∧ p.2.1 ≤ s * p.1 + h ∧
        p.2.1 ^ 2 + ∑ j : Fin m, (p.2.2 j)^2 ≤ f p.1 ^ 2}).indicator (fun p : ℝ × (ℝ × (Fin m → ℝ)) => A * p.1 + B * p.2.1 + C))
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))))) :
    let S : Set (ℝ × (ℝ × (Fin m → ℝ))) :=
      {p | p.1 ∈ Set.Icc a b ∧ p.2.1 ≤ s * p.1 + h ∧
        p.2.1 ^ 2 + ∑ j : Fin m, (p.2.2 j)^2 ≤ f p.1 ^ 2}
    let Bset : ℝ → ℝ → Set (Fin m → ℝ) := fun t z => {y : Fin m → ℝ | ∑ j : Fin m, (y j)^2 ≤ f t ^ 2 - z ^ 2}
    (∫ p : ℝ × (ℝ × (Fin m → ℝ)) in S, (A * p.1 + B * p.2.1 + C) ∂((volume : Measure ℝ).prod ((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))))) = 0 ∧
    (∫ t in a..b, ∫ z in (-f t)..(min (f t) (s * t + h)),
        (A * t + B * z + C) * volume.real (Bset t z)) = 0 := by
  classical
  intro S Bset
  let μ : Measure (ℝ × (ℝ × (Fin m → ℝ))) :=
    (volume : Measure ℝ).prod ((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ)))
  let g : ℝ × (ℝ × (Fin m → ℝ)) → ℝ := fun p => A * p.1 + B * p.2.1 + C
  have h_int' : ¬ Integrable (S.indicator g) μ := by
    simpa [S, g, μ] using h_int
  have hS_meas : MeasurableSet S := by
    dsimp [S]
    have h1 : MeasurableSet {p : ℝ × (ℝ × (Fin m → ℝ)) | p.1 ∈ Set.Icc a b} := by
      exact (measurableSet_Icc : MeasurableSet (Set.Icc (a : ℝ) b)).preimage measurable_fst
    have h2 : MeasurableSet {p : ℝ × (ℝ × (Fin m → ℝ)) | p.2.1 ≤ s * p.1 + h} := by
      apply measurableSet_le
      · exact measurable_fst.comp measurable_snd
      · exact (measurable_const.mul measurable_fst).add measurable_const
    have h3 : MeasurableSet {p : ℝ × (ℝ × (Fin m → ℝ)) |
        p.2.1 ^ 2 + ∑ j : Fin m, (p.2.2 j)^2 ≤ f p.1 ^ 2} := by
      apply measurableSet_le
      · have hz : Measurable (fun p : ℝ × (ℝ × (Fin m → ℝ)) => p.2.1 ^ 2) :=
          (measurable_fst.comp measurable_snd).pow measurable_const
        have hsum : Measurable (fun p : ℝ × (ℝ × (Fin m → ℝ)) => ∑ j : Fin m, (p.2.2 j)^2) := by
          refine Finset.measurable_sum (Finset.univ : Finset (Fin m)) ?_
          intro j hj
          have hpj : Measurable (fun p : ℝ × (ℝ × (Fin m → ℝ)) => p.2.2 j) :=
            (measurable_pi_apply j).comp (measurable_snd.comp measurable_snd)
          exact hpj.pow measurable_const
        exact hz.add hsum
      · exact (hf_meas.comp measurable_fst).pow measurable_const
    exact h1.inter (h2.inter h3)
  have hleft : (∫ p : ℝ × (ℝ × (Fin m → ℝ)) in S, g p ∂μ) = 0 := by
    rw [← MeasureTheory.integral_indicator hS_meas]
    exact MeasureTheory.integral_undef h_int'
  have hleft' : (∫ p : ℝ × (ℝ × (Fin m → ℝ)) in S, (A * p.1 + B * p.2.1 + C) ∂μ) = 0 := by
    simpa [g] using hleft
  let G : ℝ → ℝ := fun t => ∫ z in (-f t)..(min (f t) (s * t + h)),
      (A * t + B * z + C) * volume.real (Bset t z)
  have hGnot : ¬ IntervalIntegrable G volume a b := by
    intro hGint
    have hfull := integrable_ball_section_affine_of_intervalIntegrable (m := m) (a := a) (b := b)
      (s := s) (h := h) (f := f) (A := A) (B := B) (C := C)
      hab hf_nonneg hf_meas hGint
    exact h_int' hfull
  have hright : (∫ t in a..b, G t) = 0 := intervalIntegral.integral_undef hGnot
  have hright' : (∫ t in a..b, ∫ z in (-f t)..(min (f t) (s * t + h)),
        (A * t + B * z + C) * volume.real (Bset t z)) = 0 := by
    simpa [G] using hright
  exact ⟨hleft', hright'⟩

end Commons.Geometry.Ulam
