import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Commons.Analysis.Fourier.heat_triple_integrable_large
import Submission.Commons.Analysis.Fourier.heat_triple_integrable_small
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.Analysis.Fourier

open MeasureTheory

/-- For a measurable, bounded, integrable real function `u` on `V = EuclideanSpace ℝ (Fin 3)`,
the function
`(p, s) ↦ u p.1 * (u p.2 * s^(−3/2)·exp(−π‖p.1 − p.2‖²/s))` on `(V × V) × ℝ`
is integrable w.r.t. `((volume.prod volume).prod (volume.restrict (Set.Ioi (0 : ℝ))))`.

Strategy: it suffices (dominated / Tonelli) to bound the absolute value. Split the `s` domain:
For `s > 1` bound the kernel by `s^(−3/2)` (exp ≤ 1), giving a product of
`|u(p.1)||u(p.2)|` (integrable by `MeasureTheory.Integrable.mul_prod`) and `s^(−3/2)` on `(1,∞)`
(integrable by `MeasureTheory.integrableOn_Ioi_rpow_of_lt`, exponent −3/2 < −1; use
`MeasureTheory.Integrable.indicator` + `MeasureTheory.integrable_indicator_iff` to move between
`IntegrableOn` and `Integrable`).
For `0 < s ≤ 1` change variables `w = (p.1 − p.2)/√s` in the `p.2` integration
(`∫_y g(x − √s·w) dy = s^{3/2} ∫_w g(w)` from linear rescaling / `MeasureTheory.Measure.map` and
`MeasurePreserving.integral_comp` for `(fun w => x - √s * w)`), use `GaussianFourier.integral_rexp_neg_mul_sq_norm`
to get `∫_w exp(−π‖w‖²) = 1`, and boundedness of `u`, so the contribution is `≤ M·(∫|u|)`; the
indicator `0 < s ≤ 1` keeps this a finite measure. Combine the two pieces with
`MeasureTheory.Integrable.add` and integral-splitting lemmas. -/
theorem heat_triple_integrable (u : EuclideanSpace ℝ (Fin 3) → ℝ) (hmu : Measurable u)
    (hu_bdd : ∃ C : ℝ, ∀ x : EuclideanSpace ℝ (Fin 3), |u x| ≤ C)
    (hui : MeasureTheory.Integrable u) :
    MeasureTheory.Integrable
      (fun z : (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) × ℝ =>
        u z.1.1 * (u z.1.2 *
          (z.2 ^ (-(3 / 2 : ℝ)) * Real.exp (-(Real.pi * ‖z.1.1 - z.1.2‖ ^ 2) / z.2))))
      (((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))).prod
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Ioi (0 : ℝ)))) := by
  classical
  let V := EuclideanSpace ℝ (Fin 3)
  let μ12 : Measure (V × V) := (volume : Measure V).prod (volume : Measure V)
  let μs1 : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioi (1 : ℝ))
  let μs2 : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)
  let μs : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))
  let M1 : Measure ((V × V) × ℝ) := μ12.prod μs1
  let M2 : Measure ((V × V) × ℝ) := μ12.prod μs2
  let M : Measure ((V × V) × ℝ) := μ12.prod μs
  change MeasureTheory.Integrable
    (fun z : (V × V) × ℝ =>
      u z.1.1 * (u z.1.2 *
        (z.2 ^ (-(3 / 2 : ℝ)) * Real.exp (-(Real.pi * ‖z.1.1 - z.1.2‖ ^ 2) / z.2)))) M
  have hsplit : μs = μs1 + μs2 := by
    dsimp [μs, μs1, μs2]
    have hunion : Set.Ioi (0 : ℝ) = Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) := by
      ext s
      constructor
      · intro hs
        by_cases h : s ≤ 1
        · exact Or.inl ⟨hs, h⟩
        · exact Or.inr (lt_of_not_ge h)
      · intro hs
        rcases hs with h | h
        · exact h.1
        · exact lt_trans (show (0 : ℝ) < 1 by norm_num) h
    rw [hunion]
    rw [Measure.restrict_union]
    · rw [add_comm]
    · rw [Set.disjoint_left]
      intro s hs
      exact not_lt_of_ge hs.2
    · exact measurableSet_Ioi
  have hM : M = M1 + M2 := by
    dsimp [M, M1, M2]
    rw [hsplit]
    rw [Measure.prod_add]
  have h1 : MeasureTheory.Integrable
      (fun z : (V × V) × ℝ =>
        u z.1.1 * (u z.1.2 *
          (z.2 ^ (-(3 / 2 : ℝ)) * Real.exp (-(Real.pi * ‖z.1.1 - z.1.2‖ ^ 2) / z.2)))) M1 := by
    exact heat_triple_integrable_large u hmu hu_bdd hui
  have h2 : MeasureTheory.Integrable
      (fun z : (V × V) × ℝ =>
        u z.1.1 * (u z.1.2 *
          (z.2 ^ (-(3 / 2 : ℝ)) * Real.exp (-(Real.pi * ‖z.1.1 - z.1.2‖ ^ 2) / z.2)))) M2 := by
    exact heat_triple_integrable_small u hmu hu_bdd hui
  have hsum : MeasureTheory.Integrable
      (fun z : (V × V) × ℝ =>
        u z.1.1 * (u z.1.2 *
          (z.2 ^ (-(3 / 2 : ℝ)) * Real.exp (-(Real.pi * ‖z.1.1 - z.1.2‖ ^ 2) / z.2))))
      (M1 + M2) := h1.add_measure h2
  rw [hM]
  exact hsum

end Commons.Analysis.Fourier
