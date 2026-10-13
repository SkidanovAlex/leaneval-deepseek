import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.L12Sub4

open MeasureTheory

/-- **The `ε`-error of a probability kernel on a smooth `ζ`-independent weight** (generic, Mathlib
only).  For a nonnegative integrable kernel `k` of mass `1`, supported in the strip `|p₂| ≤ ε ≤ 1`,
and a continuous weight `G` whose relative oscillation on the unit interval is bounded by `B`
(`|G (ζ+q) - G ζ| ≤ B|q| G ζ` for `|q| ≤ 1`),

  `|∫ p, k p · G (ζ + p.2) - G ζ| ≤ B ε G ζ`  for every `ζ`.

Hints: `∫ p, k p G(ζ+p.2) - G ζ = ∫ p, k p (G(ζ+p.2) - G ζ)` (using `∫ k = 1` and
`MeasureTheory.integral_sub`).  Integrability: on the strip `|p₂| ≤ ε` the factor `G(ζ+p₂)` is bounded
by its maximum `M` on the compact interval `[ζ-ε, ζ+ε]` (continuity), so `|k p · G(ζ+p₂)| ≤ M ‖k p‖`
which is integrable; and `p ↦ k p * G ζ` is a constant multiple of `k`.  Then `‖∫‖ ≤ ∫‖·‖` and the
pointwise bound `|G(ζ+p.2) - G ζ| ≤ B |p.2| G ζ ≤ B ε G ζ` valid wherever `k p ≠ 0`. -/
theorem KernelWeightSub (k : ℝ × ℝ → ℝ) (G : ℝ → ℝ) {ε B : ℝ}
    (hknn : ∀ p, 0 ≤ k p) (hki : MeasureTheory.Integrable k) (hk1 : ∫ p : ℝ × ℝ, k p = 1)
    (hksupp : ∀ p, k p ≠ 0 → |p.2| ≤ ε)
    (hGcont : Continuous G) (hB : 0 ≤ B)
    (hGdiff : ∀ ζ q : ℝ, |q| ≤ 1 → |G (ζ + q) - G ζ| ≤ B * |q| * G ζ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ ζ : ℝ, |(∫ p : ℝ × ℝ, k p * G (ζ + p.2)) - G ζ| ≤ B * ε * G ζ := by
  have hεnn : (0 : ℝ) ≤ ε := le_of_lt hε0
  intro ζ
  by_cases hB0 : B = 0
  · -- `B = 0`: `G` is constant on `[ζ-1, ζ+1]`, so on the support of `k` the factor `G (ζ+p.2)`
    -- equals `G ζ`; the two integrals coincide and the claim reads `0 ≤ 0`.
    have hconst : ∀ p : ℝ × ℝ, k p * G (ζ + p.2) = k p * G ζ := by
      intro p
      by_cases hp : k p = 0
      · rw [hp, zero_mul, zero_mul]
      · have hp2 : |p.2| ≤ 1 := le_trans (hksupp p hp) hε1
        have h2 : |G (ζ + p.2) - G ζ| ≤ 0 := by simpa [hB0] using hGdiff ζ p.2 hp2
        have hEq : G (ζ + p.2) = G ζ :=
          sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h2 (abs_nonneg _)))
        rw [hEq]
    have hI : (∫ p : ℝ × ℝ, k p * G (ζ + p.2)) = G ζ := by
      rw [integral_congr_ae (Filter.Eventually.of_forall hconst),
        MeasureTheory.integral_mul_const, hk1, one_mul]
    rw [hI, sub_self, abs_zero, hB0]
    simp
  · have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
    -- The oscillation hypothesis forces `G ζ ≥ 0` (evaluate at `q = 1/2`).
    have hGζ : 0 ≤ G ζ := by
      have h := hGdiff ζ (1 / 2) (by norm_num)
      have h1 : |(1 : ℝ) / 2| = (1 : ℝ) / 2 := by norm_num
      rw [h1] at h
      exact nonneg_of_mul_nonneg_right (le_trans (abs_nonneg _) h)
        (mul_pos hBpos (by norm_num))
    -- Pointwise domination of the difference integrand on the support of `k`.
    have hpt : ∀ p : ℝ × ℝ, k p * |G (ζ + p.2) - G ζ| ≤ (B * ε * G ζ) * k p := by
      intro p
      by_cases hp : k p = 0
      · rw [hp, zero_mul, mul_zero]
      · have hp2 : |p.2| ≤ ε := hksupp p hp
        have hp2' : |p.2| ≤ 1 := le_trans hp2 hε1
        have h1 : |G (ζ + p.2) - G ζ| ≤ B * |p.2| * G ζ := hGdiff ζ p.2 hp2'
        have h2 : B * |p.2| * G ζ ≤ B * ε * G ζ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp2 hB) hGζ
        have h3 : |G (ζ + p.2) - G ζ| ≤ B * ε * G ζ := le_trans h1 h2
        calc k p * |G (ζ + p.2) - G ζ| ≤ k p * (B * ε * G ζ) :=
              mul_le_mul_of_nonneg_left h3 (hknn p)
          _ = (B * ε * G ζ) * k p := by ring
    have hInt : MeasureTheory.Integrable (fun p : ℝ × ℝ => (B * ε * G ζ) * k p) :=
      hki.const_mul _
    have hInt2 : MeasureTheory.Integrable (fun p : ℝ × ℝ => k p * (G (ζ + p.2) - G ζ)) := by
      refine MeasureTheory.Integrable.mono' hInt ?_ ?_
      · have hc : Continuous (fun p : ℝ × ℝ => G (ζ + p.2) - G ζ) :=
          (hGcont.comp (continuous_const.add continuous_snd)).sub continuous_const
        exact hki.aestronglyMeasurable.mul hc.aestronglyMeasurable
      · filter_upwards with p
        have := hpt p
        rwa [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hknn p)]
    have hInt3 : MeasureTheory.Integrable (fun p : ℝ × ℝ => k p * G (ζ + p.2)) := by
      have h := hInt2.add (hki.mul_const (G ζ))
      refine h.congr ?_
      filter_upwards with p
      simp only [Pi.add_apply]
      ring
    -- Subtract `G ζ = ∫ p, k p * G ζ` and rewrite the difference as a single integral.
    have hI : (∫ p : ℝ × ℝ, k p * G (ζ + p.2)) - G ζ
        = ∫ p : ℝ × ℝ, k p * (G (ζ + p.2) - G ζ) := by
      have h2 : (∫ p : ℝ × ℝ, k p * G ζ) = G ζ := by
        rw [MeasureTheory.integral_mul_const, hk1, one_mul]
      calc (∫ p : ℝ × ℝ, k p * G (ζ + p.2)) - G ζ
          = (∫ p : ℝ × ℝ, k p * G (ζ + p.2)) - ∫ p : ℝ × ℝ, k p * G ζ := by rw [h2]
        _ = ∫ p : ℝ × ℝ, (k p * G (ζ + p.2) - k p * G ζ) := by
              rw [MeasureTheory.integral_sub hInt3 (hki.mul_const (G ζ))]
        _ = ∫ p : ℝ × ℝ, k p * (G (ζ + p.2) - G ζ) := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with p
              ring
    rw [hI]
    have h1 : ‖∫ p : ℝ × ℝ, k p * (G (ζ + p.2) - G ζ)‖
        ≤ ∫ p : ℝ × ℝ, ‖k p * (G (ζ + p.2) - G ζ)‖ :=
      MeasureTheory.norm_integral_le_integral_norm _
    have h2 : ∫ p : ℝ × ℝ, ‖k p * (G (ζ + p.2) - G ζ)‖
        ≤ ∫ p : ℝ × ℝ, (B * ε * G ζ) * k p := by
      refine MeasureTheory.integral_mono_ae hInt2.norm hInt ?_
      filter_upwards with p
      have := hpt p
      rwa [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hknn p)]
    have h3 : ∫ p : ℝ × ℝ, (B * ε * G ζ) * k p = B * ε * G ζ := by
      rw [MeasureTheory.integral_const_mul, hk1, mul_one]
    rw [← Real.norm_eq_abs]
    exact le_trans h1 (le_trans h2 (le_of_eq h3))

end Work.FTS.StrongEps.L12Sub4
