import Mathlib
import Submission.Work.Analysis.Interpolation.eLpNorm_analyticFamily_re_zero
import Submission.Work.Analysis.Interpolation.eLpNorm_analyticFamily_re_one
import Submission.Work.Analysis.Interpolation.differentiable_of_decomposition
import Submission.Work.Analysis.Interpolation.ofReal_toReal_const_eq
import Submission.Work.Analysis.Interpolation.rpow_interp_arith
import Submission.Work.Analysis.Interpolation.analyticFamily_eq_sum

/-!
# Stein's bilinear interpolation: the three-lines core

This module proves the core three-lines argument for the interpolation of a *bilinear* pairing
`Λ` between functions on two measure spaces: given the two endpoint estimates for `Λ`, and given
that `Λ` expands over the finite level-set decompositions of two simple functions `f`, `g`
(hypothesis `hΛ` below, which holds for every genuinely bilinear `Λ` and for the integral pairings
used in Riesz--Thorin), the interpolated estimate holds for `f`, `g`.

The two analytic inputs of Hadamard's three-lines theorem (entireness and boundedness on the strip
of the family `z ↦ Λ (f_z) (g_z)`) are hypotheses here; they are discharged for genuinely bilinear
`Λ` in the companion modules `differentiable_of_decomposition` and `bddAbove_bilinear_family`,
and the resulting theorem is `Work.Analysis.Interpolation.stein_bilinear`.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace Work.Analysis.Interpolation

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}

/-- Hadamard's three-lines theorem in the form used for interpolation. -/
lemma norm_le_interp_of_strip_edges {F : ℂ → ℂ} {a b θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1)
    (hd : Differentiable ℂ F)
    (hB : BddAbove ((norm ∘ F) '' Complex.HadamardThreeLines.verticalClosedStrip 0 1))
    (ha : ∀ z ∈ Complex.re ⁻¹' {0}, ‖F z‖ ≤ a) (hb : ∀ z ∈ Complex.re ⁻¹' {1}, ‖F z‖ ≤ b) :
    ‖F (θ : ℂ)‖ ≤ a ^ (1 - θ) * b ^ θ := by
  have hz : (θ : ℂ) ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1 := by
    simp only [Complex.HadamardThreeLines.verticalClosedStrip, Set.mem_preimage, Set.mem_Icc,
      Complex.ofReal_re]
    exact ⟨hθ₀, hθ₁⟩
  have h := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁'
    F hz hd.diffContOnCl hB ha hb
  simpa using h

/-- The `ofReal`/`toReal` conversion of the interpolated constant: the real product
`m₀^(1-θ) m₁^θ U.toReal V.toReal` of finite extended nonnegative reals corresponds to the
extended product `(ofReal m₀)^(1-θ) (ofReal m₁)^θ U V`. -/
lemma ofReal_arith_convert {m₀ m₁ : ℝ} (hm₀ : 0 ≤ m₀) (hm₁ : 0 ≤ m₁) {U V : ℝ≥0∞}
    (hU : U < ⊤) (hV : V < ⊤) {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    ENNReal.ofReal (m₀ ^ (1 - θ) * m₁ ^ θ * U.toReal * V.toReal)
      = (ENNReal.ofReal m₀) ^ (1 - θ) * (ENNReal.ofReal m₁) ^ θ * U * V := by
  have h1 : ENNReal.ofReal (m₀ ^ (1 - θ) * m₁ ^ θ * U.toReal * V.toReal)
      = ENNReal.ofReal (m₀ ^ (1 - θ)) * ENNReal.ofReal (m₁ ^ θ)
        * ENNReal.ofReal U.toReal * ENNReal.ofReal V.toReal := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by positivity)]
  rw [h1, ENNReal.ofReal_rpow_of_nonneg hm₀ (by linarith),
    ENNReal.ofReal_rpow_of_nonneg hm₁ hθ₀, ENNReal.ofReal_toReal (ne_top_of_lt hU),
    ENNReal.ofReal_toReal (ne_top_of_lt hV)]

/-- **Stein's bilinear interpolation, three-lines form.**  Given a "bilinear" pairing `Λ` whose
values on the level sets of two simple functions are known, and two endpoint estimates for `Λ`,
the interpolated estimate holds for the simple functions themselves. -/
theorem stein_bilinear_of_decomposition
    (Λ : (α → ℂ) → (β → ℂ) → ℂ) (f : SimpleFunc α ℂ) (g : SimpleFunc β ℂ)
    {p₀ p₁ q₀ q₁ p q θ : ℝ} (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hq₀ : 0 < q₀) (hq₁ : 0 < q₁)
    (hp : 0 < p) (hq : 0 < q) (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (hpθ : 1 / p = (1 - θ) / p₀ + θ / p₁) (hqθ : 1 / q = (1 - θ) / q₀ + θ / q₁)
    {M₀ M₁ : ℝ≥0}
    (h₀ : ∀ u v, ‖Λ u v‖ₑ ≤ (M₀ : ℝ≥0∞) * eLpNorm u (ENNReal.ofReal p₀) μ
      * eLpNorm v (ENNReal.ofReal q₀) ν)
    (h₁ : ∀ u v, ‖Λ u v‖ₑ ≤ (M₁ : ℝ≥0∞) * eLpNorm u (ENNReal.ofReal p₁) μ
      * eLpNorm v (ENNReal.ofReal q₁) ν)
    (hΛ : ∀ z : ℂ,
      bilinearFamily Λ (f : α → ℂ) (g : β → ℂ) ((p / p₀ : ℝ) : ℂ) ((p / p₁ : ℝ) : ℂ)
          ((q / q₀ : ℝ) : ℂ) ((q / q₁ : ℝ) : ℂ) z
        = ∑ c ∈ f.range, ∑ d ∈ g.range,
            (phasePow c (expFamily ((p / p₀ : ℝ) : ℂ) ((p / p₁ : ℝ) : ℂ) z)
              * phasePow d (expFamily ((q / q₀ : ℝ) : ℂ) ((q / q₁ : ℝ) : ℂ) z))
              * (Λ (Set.indicator (f ⁻¹' {c}) (fun _ => (1 : ℂ)))
                  (Set.indicator (g ⁻¹' {d}) (fun _ => (1 : ℂ)))))
    (hB : BddAbove ((norm ∘ bilinearFamily Λ (f : α → ℂ) (g : β → ℂ) ((p / p₀ : ℝ) : ℂ)
        ((p / p₁ : ℝ) : ℂ) ((q / q₀ : ℝ) : ℂ) ((q / q₁ : ℝ) : ℂ))
        '' Complex.HadamardThreeLines.verticalClosedStrip 0 1)) :
    ‖Λ (f : α → ℂ) (g : β → ℂ)‖ₑ ≤ (M₀ : ℝ≥0∞) ^ (1 - θ) * (M₁ : ℝ≥0∞) ^ θ
      * eLpNorm (f : α → ℂ) (ENNReal.ofReal p) μ * eLpNorm (g : β → ℂ) (ENNReal.ofReal q) ν := by
  set U : ℝ≥0∞ := eLpNorm (f : α → ℂ) (ENNReal.ofReal p) μ with hUdef
  set V : ℝ≥0∞ := eLpNorm (g : β → ℂ) (ENNReal.ofReal q) ν with hVdef
  set F : ℂ → ℂ := bilinearFamily Λ (f : α → ℂ) (g : β → ℂ) ((p / p₀ : ℝ) : ℂ)
    ((p / p₁ : ℝ) : ℂ) ((q / q₀ : ℝ) : ℂ) ((q / q₁ : ℝ) : ℂ) with hFdef
  -- the trivial cases where one of the constants vanishes
  rcases eq_or_ne M₀ 0 with hM₀ | hM₀
  · have h0 : (M₀ : ℝ≥0∞) = 0 := by rw [hM₀]; rfl
    have h := h₀ (f : α → ℂ) (g : β → ℂ)
    rw [h0, zero_mul, zero_mul] at h
    exact le_trans h bot_le
  rcases eq_or_ne M₁ 0 with hM₁ | hM₁
  · have h1 : (M₁ : ℝ≥0∞) = 0 := by rw [hM₁]; rfl
    have h := h₁ (f : α → ℂ) (g : β → ℂ)
    rw [h1, zero_mul, zero_mul] at h
    exact le_trans h bot_le
  have hM₀pos : (0 : ℝ≥0∞) < (M₀ : ℝ≥0∞) := pos_iff_ne_zero.mpr (by simpa using hM₀)
  have hM₁pos : (0 : ℝ≥0∞) < (M₁ : ℝ≥0∞) := pos_iff_ne_zero.mpr (by simpa using hM₁)
  -- the case where the right-hand side is automatically `⊤`
  by_cases htop : (U = ⊤ ∧ V ≠ 0) ∨ (V = ⊤ ∧ U ≠ 0)
  · have hpos₀ : (0 : ℝ≥0∞) < (M₀ : ℝ≥0∞) ^ (1 - θ) :=
      ENNReal.rpow_pos hM₀pos ENNReal.coe_ne_top
    have hpos₁ : (0 : ℝ≥0∞) < (M₁ : ℝ≥0∞) ^ θ :=
      ENNReal.rpow_pos hM₁pos ENNReal.coe_ne_top
    have hpos : (0 : ℝ≥0∞) < (M₀ : ℝ≥0∞) ^ (1 - θ) * (M₁ : ℝ≥0∞) ^ θ :=
      ENNReal.mul_pos (ne_of_gt hpos₀) (ne_of_gt hpos₁)
    have hRHS : (M₀ : ℝ≥0∞) ^ (1 - θ) * (M₁ : ℝ≥0∞) ^ θ * U * V = ⊤ := by
      rcases htop with ⟨hU, hV⟩ | ⟨hV, hU⟩
      · rw [hU, ENNReal.mul_top (ne_of_gt hpos), ENNReal.top_mul hV]
      · rw [hV, ENNReal.mul_top (mul_ne_zero (ne_of_gt hpos) hU)]
    rw [hRHS]
    exact le_top
  push_neg at htop
  have hUopen : U < ⊤ ∨ V = 0 := by
    by_cases h : U = ⊤
    · exact Or.inr (htop.1 h)
    · exact Or.inl (lt_top_iff_ne_top.mpr h)
  have hVopen : V < ⊤ ∨ U = 0 := by
    by_cases h : V = ⊤
    · exact Or.inr (htop.2 h)
    · exact Or.inl (lt_top_iff_ne_top.mpr h)
  -- the analytic inputs
  have hΛraw : ∀ z : ℂ, Λ (analyticFamily (f : α → ℂ) ((p / p₀ : ℝ) : ℂ) ((p / p₁ : ℝ) : ℂ) z)
      (analyticFamily (g : β → ℂ) ((q / q₀ : ℝ) : ℂ) ((q / q₁ : ℝ) : ℂ) z)
      = ∑ c ∈ f.range, ∑ d ∈ g.range,
          (phasePow c (expFamily ((p / p₀ : ℝ) : ℂ) ((p / p₁ : ℝ) : ℂ) z)
            * phasePow d (expFamily ((q / q₀ : ℝ) : ℂ) ((q / q₁ : ℝ) : ℂ) z))
            * (Λ (Set.indicator (f ⁻¹' {c}) (fun _ => (1 : ℂ)))
                (Set.indicator (g ⁻¹' {d}) (fun _ => (1 : ℂ)))) := by
    intro z
    have hz := hΛ z
    rwa [hFdef, bilinearFamily_apply] at hz
  have hFdiff : Differentiable ℂ F := by
    rw [hFdef]
    exact differentiable_of_decomposition Λ f g _ _ _ _ hΛraw
  -- the boundary estimates
  have hedge0 : ∀ z ∈ Complex.re ⁻¹' {0},
      ‖F z‖ ≤ (M₀ : ℝ) * U.toReal ^ (p / p₀) * V.toReal ^ (q / q₀) := by
    intro z hz
    have hz' : z.re = 0 := hz
    have h1 : ‖F z‖ₑ ≤ (M₀ : ℝ≥0∞)
        * eLpNorm (analyticFamily (f : α → ℂ) ((p / p₀ : ℝ) : ℂ) ((p / p₁ : ℝ) : ℂ) z)
            (ENNReal.ofReal p₀) μ
        * eLpNorm (analyticFamily (g : β → ℂ) ((q / q₀ : ℝ) : ℂ) ((q / q₁ : ℝ) : ℂ) z)
            (ENNReal.ofReal q₀) ν := by
      rw [hFdef, bilinearFamily_apply]
      exact h₀ _ _
    rw [eLpNorm_analyticFamily_re_zero (μ := μ) hp₀ hp₁ hp hz'
        (aemeasurable_analyticFamily f ((p / p₀ : ℝ) : ℂ) ((p / p₁ : ℝ) : ℂ) z).aestronglyMeasurable
        f.aestronglyMeasurable,
      eLpNorm_analyticFamily_re_zero (μ := ν) hq₀ hq₁ hq hz'
        (aemeasurable_analyticFamily g ((q / q₀ : ℝ) : ℂ) ((q / q₁ : ℝ) : ℂ) z).aestronglyMeasurable
        g.aestronglyMeasurable] at h1
    rw [← hUdef, ← hVdef] at h1
    have h2 : (M₀ : ℝ≥0∞) * U ^ (p / p₀) * V ^ (q / q₀)
        = ENNReal.ofReal ((M₀ : ℝ) * U.toReal ^ (p / p₀) * V.toReal ^ (q / q₀)) := by
      rw [← ENNReal.ofReal_coe_nnreal (p := M₀),
        ← ofReal_toReal_const_eq (M₀ : ℝ) (by positivity) U V (p / p₀) (q / q₀)
          (by positivity) (by positivity) hUopen hVopen]
    rw [h2, ← ofReal_norm] at h1
    rwa [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h1
  have hedge1 : ∀ z ∈ Complex.re ⁻¹' {1},
      ‖F z‖ ≤ (M₁ : ℝ) * U.toReal ^ (p / p₁) * V.toReal ^ (q / q₁) := by
    intro z hz
    have hz' : z.re = 1 := hz
    have h1 : ‖F z‖ₑ ≤ (M₁ : ℝ≥0∞)
        * eLpNorm (analyticFamily (f : α → ℂ) ((p / p₀ : ℝ) : ℂ) ((p / p₁ : ℝ) : ℂ) z)
            (ENNReal.ofReal p₁) μ
        * eLpNorm (analyticFamily (g : β → ℂ) ((q / q₀ : ℝ) : ℂ) ((q / q₁ : ℝ) : ℂ) z)
            (ENNReal.ofReal q₁) ν := by
      rw [hFdef, bilinearFamily_apply]
      exact h₁ _ _
    rw [eLpNorm_analyticFamily_re_one (μ := μ) hp₀ hp₁ hp hz'
        (aemeasurable_analyticFamily f ((p / p₀ : ℝ) : ℂ) ((p / p₁ : ℝ) : ℂ) z).aestronglyMeasurable
        f.aestronglyMeasurable,
      eLpNorm_analyticFamily_re_one (μ := ν) hq₀ hq₁ hq hz'
        (aemeasurable_analyticFamily g ((q / q₀ : ℝ) : ℂ) ((q / q₁ : ℝ) : ℂ) z).aestronglyMeasurable
        g.aestronglyMeasurable] at h1
    rw [← hUdef, ← hVdef] at h1
    have h2 : (M₁ : ℝ≥0∞) * U ^ (p / p₁) * V ^ (q / q₁)
        = ENNReal.ofReal ((M₁ : ℝ) * U.toReal ^ (p / p₁) * V.toReal ^ (q / q₁)) := by
      rw [← ENNReal.ofReal_coe_nnreal (p := M₁),
        ← ofReal_toReal_const_eq (M₁ : ℝ) (by positivity) U V (p / p₁) (q / q₁)
          (by positivity) (by positivity) hUopen hVopen]
    rw [h2, ← ofReal_norm] at h1
    rwa [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h1
  have hhad := norm_le_interp_of_strip_edges hθ₀.le hθ₁.le hFdiff hB hedge0 hedge1
  have hselfp : (1 - (θ : ℂ)) * ((p / p₀ : ℝ) : ℂ) + (θ : ℂ) * ((p / p₁ : ℝ) : ℂ) = 1 :=
    expFamily_interp_self (ne_of_gt hp) hpθ
  have hselfq : (1 - (θ : ℂ)) * ((q / q₀ : ℝ) : ℂ) + (θ : ℂ) * ((q / q₁ : ℝ) : ℂ) = 1 :=
    expFamily_interp_self (ne_of_gt hq) hqθ
  have hFθ : F (θ : ℂ) = Λ (f : α → ℂ) (g : β → ℂ) := by
    rw [hFdef]
    exact bilinearFamily_self hselfp hselfq
  -- the degenerate cases where one of the two norms vanishes
  rcases eq_or_ne U 0 with hU0 | hU0
  · have ha0 : (M₀ : ℝ) * U.toReal ^ (p / p₀) * V.toReal ^ (q / q₀) = 0 := by
      rw [hU0, ENNReal.toReal_zero, Real.zero_rpow (ne_of_gt (div_pos hp hp₀)), mul_zero, zero_mul]
    have hb0 : (M₁ : ℝ) * U.toReal ^ (p / p₁) * V.toReal ^ (q / q₁) = 0 := by
      rw [hU0, ENNReal.toReal_zero, Real.zero_rpow (ne_of_gt (div_pos hp hp₁)), mul_zero, zero_mul]
    have hzero : ‖F (θ : ℂ)‖ ≤ 0 := by
      have h := hhad
      rw [ha0, hb0, Real.zero_rpow (ne_of_gt (sub_pos.mpr hθ₁)),
        Real.zero_rpow (ne_of_gt hθ₀), mul_zero] at h
      exact h
    have hRHS : (M₀ : ℝ≥0∞) ^ (1 - θ) * (M₁ : ℝ≥0∞) ^ θ * U * V = 0 := by
      rw [hU0, mul_zero, zero_mul]
    have : ‖Λ (f : α → ℂ) (g : β → ℂ)‖ₑ ≤ 0 := by
      rw [← hFθ, ← ofReal_norm, ← ENNReal.ofReal_zero]
      exact ENNReal.ofReal_le_ofReal hzero
    rw [hRHS]
    exact this
  rcases eq_or_ne V 0 with hV0 | hV0
  · have ha0 : (M₀ : ℝ) * U.toReal ^ (p / p₀) * V.toReal ^ (q / q₀) = 0 := by
      rw [hV0, ENNReal.toReal_zero, Real.zero_rpow (ne_of_gt (div_pos hq hq₀)), mul_zero]
    have hb0 : (M₁ : ℝ) * U.toReal ^ (p / p₁) * V.toReal ^ (q / q₁) = 0 := by
      rw [hV0, ENNReal.toReal_zero, Real.zero_rpow (ne_of_gt (div_pos hq hq₁)), mul_zero]
    have hzero : ‖F (θ : ℂ)‖ ≤ 0 := by
      have h := hhad
      rw [ha0, hb0, Real.zero_rpow (ne_of_gt (sub_pos.mpr hθ₁)),
        Real.zero_rpow (ne_of_gt hθ₀), mul_zero] at h
      exact h
    have hRHS : (M₀ : ℝ≥0∞) ^ (1 - θ) * (M₁ : ℝ≥0∞) ^ θ * U * V = 0 := by
      rw [hV0, mul_zero]
    have : ‖Λ (f : α → ℂ) (g : β → ℂ)‖ₑ ≤ 0 := by
      rw [← hFθ, ← ofReal_norm, ← ENNReal.ofReal_zero]
      exact ENNReal.ofReal_le_ofReal hzero
    rw [hRHS]
    exact this
  -- the main case
  have hUpos : 0 < U := pos_iff_ne_zero.mpr hU0
  have hVpos : 0 < V := pos_iff_ne_zero.mpr hV0
  have hUfin : U < ⊤ := hUopen.resolve_right hV0
  have hVfin : V < ⊤ := hVopen.resolve_right hU0
  have hα : (1 - θ) * (p / p₀) + θ * (p / p₁) = 1 := interp_self (ne_of_gt hp) hpθ
  have hβ : (1 - θ) * (q / q₀) + θ * (q / q₁) = 1 := interp_self (ne_of_gt hq) hqθ
  have harith : ((M₀ : ℝ) * U.toReal ^ (p / p₀) * V.toReal ^ (q / q₀)) ^ (1 - θ)
      * ((M₁ : ℝ) * U.toReal ^ (p / p₁) * V.toReal ^ (q / q₁)) ^ θ
      = (M₀ : ℝ) ^ (1 - θ) * (M₁ : ℝ) ^ θ * U.toReal * V.toReal :=
    rpow_interp_arith (by positivity) (by positivity) (ENNReal.toReal_pos hU0 (ne_top_of_lt hUfin))
      (ENNReal.toReal_pos hV0 (ne_top_of_lt hVfin)) hα hβ
  have hconv : ENNReal.ofReal (((M₀ : ℝ) * U.toReal ^ (p / p₀) * V.toReal ^ (q / q₀)) ^ (1 - θ)
      * ((M₁ : ℝ) * U.toReal ^ (p / p₁) * V.toReal ^ (q / q₁)) ^ θ)
      = (M₀ : ℝ≥0∞) ^ (1 - θ) * (M₁ : ℝ≥0∞) ^ θ * U * V := by
    rw [harith, ofReal_arith_convert (by positivity) (by positivity) hUfin hVfin hθ₀.le hθ₁.le,
      ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal]
  calc ‖Λ (f : α → ℂ) (g : β → ℂ)‖ₑ
      = ENNReal.ofReal ‖F (θ : ℂ)‖ := by rw [hFθ, ofReal_norm]
    _ ≤ ENNReal.ofReal (((M₀ : ℝ) * U.toReal ^ (p / p₀) * V.toReal ^ (q / q₀)) ^ (1 - θ)
          * ((M₁ : ℝ) * U.toReal ^ (p / p₁) * V.toReal ^ (q / q₁)) ^ θ) :=
        ENNReal.ofReal_le_ofReal hhad
    _ = (M₀ : ℝ≥0∞) ^ (1 - θ) * (M₁ : ℝ≥0∞) ^ θ * U * V := hconv

end Work.Analysis.Interpolation
