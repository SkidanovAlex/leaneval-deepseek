import Mathlib
import Submission.Work.Analysis.Interpolation.stein_trilinear
import Submission.Work.KMTAreas.A5.ofReal_toReal_const_eq3_nn
import Submission.Work.KMTAreas.A5.eLpNorm_analyticFamily_re_of_ne_zero

/-!
# Stein's trilinear interpolation with an `L^∞` endpoint

`Work.KMTAreas.A5.stein_trilinear_top` is the three-variable companion of
`Work.Analysis.Interpolation.stein_trilinear` in the form in which the third *endpoint*
estimate is at the exponent `⊤`: the analytic family of the third function is
`analyticFamily h 0 ((r / (r - 1)) / r₁) z`, whose exponent at `z.re = 0` is `0` (a pure phase,
so the `L^∞` boundary estimate is the trivial bound by `1`) and whose exponent at `z = θ` equals
`1` exactly when `1 / r = 1 - θ / r₁`; the interpolated seminorm is then `‖h‖_{L^{r/(r-1)}}`.
This is the `ℓ¹` endpoint of §5-and-the-interpolation-step of Krause--Mirek--Tao, *Pointwise
ergodic theorems for non-conventional bilinear polynomial averages*, Annals 195 (2022).

The proof is the same Hadamard three-lines argument as in
`Work.Analysis.Interpolation.stein_trilinear_of_decomposition`, run with the exponent `0` in the
first slot of the third family: the third exponent relation becomes `(1-θ) · 0 + θ · (r/((r-1) r₁)) = 1`
(equivalent to `1 / r = 1 - θ / r₁`), and the two auxiliary facts used are the boundary estimate
`Work.KMTAreas.A5.eLpNorm_analyticFamily_re_of_ne_zero` (which needs only `s ≠ 0`, not `1 ≤ s`
-- the case `r₁ < 1` occurs here) and the `ofReal`/`toReal` conversion
`Work.KMTAreas.A5.ofReal_toReal_const_eq3_nn`.

## Main result

* `Work.KMTAreas.A5.stein_trilinear_top`.
-/

namespace Work.KMTAreas.A5

open MeasureTheory
open scoped ENNReal NNReal BigOperators

theorem stein_trilinear_top {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] {μ : Measure α} {ν : Measure β} {ρ : Measure γ}
    (Λ : (α → ℂ) → (β → ℂ) → (γ → ℂ) → ℂ) (f : SimpleFunc α ℂ) (g : SimpleFunc β ℂ)
    (h : SimpleFunc γ ℂ)
    {p₀ p₁ q₀ q₁ r₁ p q r θ : ℝ} (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hq₀ : 0 < q₀)
    (hq₁ : 0 < q₁) (hr₁ : 0 < r₁) (hp : 0 < p) (hq : 0 < q) (hr : 1 < r)
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (hpθ : 1 / p = (1 - θ) / p₀ + θ / p₁) (hqθ : 1 / q = (1 - θ) / q₀ + θ / q₁)
    (hrθ : 1 / r = 1 - θ / r₁)
    {M₀ M₁ : ℝ≥0}
    (h₀ : ∀ u v w, ‖Λ u v w‖ₑ ≤ (M₀ : ℝ≥0∞) * eLpNorm u (ENNReal.ofReal p₀) μ
      * eLpNorm v (ENNReal.ofReal q₀) ν * eLpNorm w ⊤ ρ)
    (h₁ : ∀ u v w, ‖Λ u v w‖ₑ ≤ (M₁ : ℝ≥0∞) * eLpNorm u (ENNReal.ofReal p₁) μ
      * eLpNorm v (ENNReal.ofReal q₁) ν * eLpNorm w (ENNReal.ofReal r₁) ρ)
    (hΛ : ∀ z : ℂ,
      Λ (Work.Analysis.Interpolation.analyticFamily (f : α → ℂ) ((p / p₀ : ℝ) : ℂ) ((p / p₁ : ℝ) : ℂ) z)
          (Work.Analysis.Interpolation.analyticFamily (g : β → ℂ) ((q / q₀ : ℝ) : ℂ) ((q / q₁ : ℝ) : ℂ) z)
          (Work.Analysis.Interpolation.analyticFamily (h : γ → ℂ) (0 : ℂ) (((r / (r - 1)) / r₁ : ℝ) : ℂ) z)
        = ∑ e ∈ h.range, ∑ d ∈ g.range, ∑ c ∈ f.range,
            (Work.Analysis.Interpolation.phasePow c (Work.Analysis.Interpolation.expFamily ((p / p₀ : ℝ) : ℂ) ((p / p₁ : ℝ) : ℂ) z)
              * Work.Analysis.Interpolation.phasePow d (Work.Analysis.Interpolation.expFamily ((q / q₀ : ℝ) : ℂ) ((q / q₁ : ℝ) : ℂ) z)
              * Work.Analysis.Interpolation.phasePow e (Work.Analysis.Interpolation.expFamily (0 : ℂ) (((r / (r - 1)) / r₁ : ℝ) : ℂ) z))
            * (Λ (Set.indicator (f ⁻¹' {c}) (fun _ => (1 : ℂ)))
                (Set.indicator (g ⁻¹' {d}) (fun _ => (1 : ℂ)))
                (Set.indicator (h ⁻¹' {e}) (fun _ => (1 : ℂ)))))
    (hB : BddAbove ((norm ∘ fun z : ℂ =>
        Λ (Work.Analysis.Interpolation.analyticFamily (f : α → ℂ) ((p / p₀ : ℝ) : ℂ) ((p / p₁ : ℝ) : ℂ) z)
          (Work.Analysis.Interpolation.analyticFamily (g : β → ℂ) ((q / q₀ : ℝ) : ℂ) ((q / q₁ : ℝ) : ℂ) z)
          (Work.Analysis.Interpolation.analyticFamily (h : γ → ℂ) (0 : ℂ) (((r / (r - 1)) / r₁ : ℝ) : ℂ) z))
        '' Complex.HadamardThreeLines.verticalClosedStrip 0 1)) :
    ‖Λ (f : α → ℂ) (g : β → ℂ) (h : γ → ℂ)‖ₑ
      ≤ (M₀ : ℝ≥0∞) ^ (1 - θ) * (M₁ : ℝ≥0∞) ^ θ
        * eLpNorm (f : α → ℂ) (ENNReal.ofReal p) μ
        * eLpNorm (g : β → ℂ) (ENNReal.ofReal q) ν
        * eLpNorm (h : γ → ℂ) (ENNReal.ofReal (r / (r - 1))) ρ := by
  set U : ℝ≥0∞ := eLpNorm (f : α → ℂ) (ENNReal.ofReal p) μ with hUdef
  set V : ℝ≥0∞ := eLpNorm (g : β → ℂ) (ENNReal.ofReal q) ν with hVdef
  set W : ℝ≥0∞ := eLpNorm (h : γ → ℂ) (ENNReal.ofReal (r / (r - 1))) ρ with hWdef
  set F : ℂ → ℂ := fun z : ℂ =>
    Λ (Work.Analysis.Interpolation.analyticFamily (f : α → ℂ) ((p / p₀ : ℝ) : ℂ) ((p / p₁ : ℝ) : ℂ) z)
      (Work.Analysis.Interpolation.analyticFamily (g : β → ℂ) ((q / q₀ : ℝ) : ℂ) ((q / q₁ : ℝ) : ℂ) z)
      (Work.Analysis.Interpolation.analyticFamily (h : γ → ℂ) (0 : ℂ) (((r / (r - 1)) / r₁ : ℝ) : ℂ) z)
    with hFdef
  have hRpos : 0 < r / (r - 1) := div_pos (lt_trans one_pos hr) (sub_pos.mpr hr)
  have hγexp : θ * (r / (r - 1) / r₁) = 1 := by
    have hr0 : r ≠ 0 := ne_of_gt (lt_trans one_pos hr)
    have hr1 : r - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hr)
    have hr10 : r₁ ≠ 0 := ne_of_gt hr₁
    have hh := hrθ
    field_simp at hh ⊢
    linarith
  -- the two trivial cases where a constant vanishes
  rcases eq_or_ne M₀ 0 with hM₀ | hM₀
  · have h00 : (M₀ : ℝ≥0∞) = 0 := by rw [hM₀]; rfl
    have hh := h₀ (f : α → ℂ) (g : β → ℂ) (h : γ → ℂ)
    rw [h00, zero_mul, zero_mul, zero_mul] at hh
    exact le_trans hh bot_le
  rcases eq_or_ne M₁ 0 with hM₁ | hM₁
  · have h11 : (M₁ : ℝ≥0∞) = 0 := by rw [hM₁]; rfl
    have hh := h₁ (f : α → ℂ) (g : β → ℂ) (h : γ → ℂ)
    rw [h11, zero_mul, zero_mul, zero_mul] at hh
    exact le_trans hh bot_le
  have hM₀pos : (0 : ℝ≥0∞) < (M₀ : ℝ≥0∞) := pos_iff_ne_zero.mpr (by simpa using hM₀)
  have hM₁pos : (0 : ℝ≥0∞) < (M₁ : ℝ≥0∞) := pos_iff_ne_zero.mpr (by simpa using hM₁)
  -- the cases where one of the three seminorms vanishes
  rcases eq_or_ne U 0 with hU0 | hU0
  · have hae : (f : α → ℂ) =ᵐ[μ] 0 :=
      (eLpNorm_eq_zero_iff (ENNReal.ofReal_ne_zero_iff.mpr hp)).mp
        (by rw [← hUdef]; exact hU0)
    have hz : eLpNorm (f : α → ℂ) (ENNReal.ofReal p₀) μ = 0 := by
      rw [eLpNorm_congr_ae hae, eLpNorm_zero]
    have hh := h₀ (f : α → ℂ) (g : β → ℂ) (h : γ → ℂ)
    rw [hz, mul_zero, zero_mul, zero_mul] at hh
    refine le_trans hh ?_
    rw [hU0]; simp
  rcases eq_or_ne V 0 with hV0 | hV0
  · have hae : (g : β → ℂ) =ᵐ[ν] 0 :=
      (eLpNorm_eq_zero_iff (ENNReal.ofReal_ne_zero_iff.mpr hq)).mp
        (by rw [← hVdef]; exact hV0)
    have hz : eLpNorm (g : β → ℂ) (ENNReal.ofReal q₀) ν = 0 := by
      rw [eLpNorm_congr_ae hae, eLpNorm_zero]
    have hh := h₀ (f : α → ℂ) (g : β → ℂ) (h : γ → ℂ)
    rw [hz, mul_zero, zero_mul] at hh
    refine le_trans hh ?_
    rw [hV0]; simp
  rcases eq_or_ne W 0 with hW0 | hW0
  · have hae : (h : γ → ℂ) =ᵐ[ρ] 0 :=
      (eLpNorm_eq_zero_iff (ENNReal.ofReal_ne_zero_iff.mpr hRpos)).mp
        (by rw [← hWdef]; exact hW0)
    have hz : eLpNorm (h : γ → ℂ) ⊤ ρ = 0 := by
      rw [eLpNorm_congr_ae hae, eLpNorm_zero]
    have hh := h₀ (f : α → ℂ) (g : β → ℂ) (h : γ → ℂ)
    rw [hz, mul_zero] at hh
    refine le_trans hh ?_
    rw [hW0]; simp
  -- the case where the right-hand side is automatically `⊤`
  by_cases htop : (U = ⊤ ∧ V ≠ 0 ∧ W ≠ 0) ∨ (V = ⊤ ∧ U ≠ 0 ∧ W ≠ 0)
      ∨ (W = ⊤ ∧ U ≠ 0 ∧ V ≠ 0)
  · have hpos₀ : (0 : ℝ≥0∞) < (M₀ : ℝ≥0∞) ^ (1 - θ) :=
      ENNReal.rpow_pos hM₀pos ENNReal.coe_ne_top
    have hpos₁ : (0 : ℝ≥0∞) < (M₁ : ℝ≥0∞) ^ θ :=
      ENNReal.rpow_pos hM₁pos ENNReal.coe_ne_top
    have hpos : (0 : ℝ≥0∞) < (M₀ : ℝ≥0∞) ^ (1 - θ) * (M₁ : ℝ≥0∞) ^ θ :=
      ENNReal.mul_pos (ne_of_gt hpos₀) (ne_of_gt hpos₁)
    have hRHS : (M₀ : ℝ≥0∞) ^ (1 - θ) * (M₁ : ℝ≥0∞) ^ θ * U * V * W = ⊤ := by
      rcases htop with ⟨hU, hV, hW⟩ | ⟨hV, hU, hW⟩ | ⟨hW, hU, hV⟩
      · rw [hU, ENNReal.mul_top (ne_of_gt hpos), ENNReal.top_mul hV, ENNReal.top_mul hW]
      · rw [hV, ENNReal.mul_top (mul_ne_zero (ne_of_gt hpos) hU), ENNReal.top_mul hW]
      · rw [hW, ENNReal.mul_top (mul_ne_zero (mul_ne_zero (ne_of_gt hpos) hU) hV)]
    rw [hRHS]
    exact le_top
  have hUfin : U < ⊤ := by
    by_contra hcon
    exact htop (Or.inl ⟨eq_top_iff.mpr (not_lt.mp hcon), hV0, hW0⟩)
  have hVfin : V < ⊤ := by
    by_contra hcon
    exact htop (Or.inr (Or.inl ⟨eq_top_iff.mpr (not_lt.mp hcon), hU0, hW0⟩))
  have hWfin : W < ⊤ := by
    by_contra hcon
    exact htop (Or.inr (Or.inr ⟨eq_top_iff.mpr (not_lt.mp hcon), hU0, hV0⟩))
  -- the analytic inputs
  have hFdiff : Differentiable ℂ F := by
    rw [hFdef]
    exact Work.Analysis.Interpolation.differentiable_trilinear_of_decomposition Λ f g h
      ((p / p₀ : ℝ) : ℂ) ((p / p₁ : ℝ) : ℂ) ((q / q₀ : ℝ) : ℂ) ((q / q₁ : ℝ) : ℂ)
      (0 : ℂ) (((r / (r - 1)) / r₁ : ℝ) : ℂ) hΛ
  have hBdd : BddAbove ((norm ∘ F) '' Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
    rw [hFdef]
    exact hB
  -- the boundary estimate on the left edge
  have hedge0 : ∀ z ∈ Complex.re ⁻¹' {0},
      ‖F z‖ ≤ (M₀ : ℝ) * U.toReal ^ (p / p₀) * V.toReal ^ (q / q₀) := by
    intro z hz
    have hz' : z.re = 0 := hz
    have h1 : ‖F z‖ₑ ≤ (M₀ : ℝ≥0∞)
        * eLpNorm (Work.Analysis.Interpolation.analyticFamily (f : α → ℂ) ((p / p₀ : ℝ) : ℂ)
            ((p / p₁ : ℝ) : ℂ) z) (ENNReal.ofReal p₀) μ
        * eLpNorm (Work.Analysis.Interpolation.analyticFamily (g : β → ℂ) ((q / q₀ : ℝ) : ℂ)
            ((q / q₁ : ℝ) : ℂ) z) (ENNReal.ofReal q₀) ν
        * eLpNorm (Work.Analysis.Interpolation.analyticFamily (h : γ → ℂ) (0 : ℂ)
            (((r / (r - 1)) / r₁ : ℝ) : ℂ) z) ⊤ ρ := by
      rw [hFdef]
      exact h₀ _ _ _
    rw [Work.Analysis.Interpolation.eLpNorm_analyticFamily_re_zero (μ := μ) hp₀ hp₁ hp hz'
        (hF := (Work.Analysis.Interpolation.aemeasurable_analyticFamily f _ _ _).aestronglyMeasurable)
        (hf := f.aestronglyMeasurable),
      Work.Analysis.Interpolation.eLpNorm_analyticFamily_re_zero (μ := ν) hq₀ hq₁ hq hz'
        (hF := (Work.Analysis.Interpolation.aemeasurable_analyticFamily g _ _ _).aestronglyMeasurable)
        (hf := g.aestronglyMeasurable)] at h1
    rw [← hUdef, ← hVdef] at h1
    have hb3 : eLpNorm (Work.Analysis.Interpolation.analyticFamily (h : γ → ℂ) (0 : ℂ)
        (((r / (r - 1)) / r₁ : ℝ) : ℂ) z) ⊤ ρ ≤ 1 := by
      have hre : (Work.Analysis.Interpolation.expFamily ((0 : ℝ) : ℂ)
          (((r / (r - 1)) / r₁ : ℝ) : ℂ) z).re = 0 := by
        rw [Work.Analysis.Interpolation.expFamily_ofReal_re, hz']
        ring
      have h' := eLpNorm_analyticFamily_re_of_ne_zero (μ := ρ) (f := (h : γ → ℂ)) (P := r / (r - 1))
        (t₀ := 0) (t := 0) (s := ⊤) hRpos (by simp) (by simp) hre (hF := (Work.Analysis.Interpolation.aemeasurable_analyticFamily h _ _ _).aestronglyMeasurable)
        (hf := h.aestronglyMeasurable)
      simpa [← hWdef] using h'
    have h2 : ‖F z‖ₑ ≤ (M₀ : ℝ≥0∞) * U ^ (p / p₀) * V ^ (q / q₀) := by
      refine le_trans h1 ?_
      simpa using mul_le_mul_right hb3 ((M₀ : ℝ≥0∞) * U ^ (p / p₀) * V ^ (q / q₀))
    have h3 : (M₀ : ℝ≥0∞) * U ^ (p / p₀) * V ^ (q / q₀)
        = ENNReal.ofReal ((M₀ : ℝ) * U.toReal ^ (p / p₀) * V.toReal ^ (q / q₀)) := by
      rw [← ENNReal.ofReal_coe_nnreal (p := M₀),
        ← Work.Analysis.Interpolation.ofReal_toReal_const_eq (M₀ : ℝ) (by positivity) U V
          (p / p₀) (q / q₀) (by positivity) (by positivity) (Or.inl hUfin) (Or.inl hVfin)]
    rw [h3, ← ofReal_norm] at h2
    rwa [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h2
  -- the boundary estimate on the right edge
  have hedge1 : ∀ z ∈ Complex.re ⁻¹' {1},
      ‖F z‖ ≤ (M₁ : ℝ) * U.toReal ^ (p / p₁) * V.toReal ^ (q / q₁)
        * W.toReal ^ ((r / (r - 1)) / r₁) := by
    intro z hz
    have hz' : z.re = 1 := hz
    have h1 : ‖F z‖ₑ ≤ (M₁ : ℝ≥0∞)
        * eLpNorm (Work.Analysis.Interpolation.analyticFamily (f : α → ℂ) ((p / p₀ : ℝ) : ℂ)
            ((p / p₁ : ℝ) : ℂ) z) (ENNReal.ofReal p₁) μ
        * eLpNorm (Work.Analysis.Interpolation.analyticFamily (g : β → ℂ) ((q / q₀ : ℝ) : ℂ)
            ((q / q₁ : ℝ) : ℂ) z) (ENNReal.ofReal q₁) ν
        * eLpNorm (Work.Analysis.Interpolation.analyticFamily (h : γ → ℂ) (0 : ℂ)
            (((r / (r - 1)) / r₁ : ℝ) : ℂ) z) (ENNReal.ofReal r₁) ρ := by
      rw [hFdef]
      exact h₁ _ _ _
    rw [Work.Analysis.Interpolation.eLpNorm_analyticFamily_re_one (μ := μ) hp₀ hp₁ hp hz'
        (hF := (Work.Analysis.Interpolation.aemeasurable_analyticFamily f _ _ _).aestronglyMeasurable)
        (hf := f.aestronglyMeasurable),
      Work.Analysis.Interpolation.eLpNorm_analyticFamily_re_one (μ := ν) hq₀ hq₁ hq hz'
        (hF := (Work.Analysis.Interpolation.aemeasurable_analyticFamily g _ _ _).aestronglyMeasurable)
        (hf := g.aestronglyMeasurable)] at h1
    rw [← hUdef, ← hVdef] at h1
    have hb1 : eLpNorm (Work.Analysis.Interpolation.analyticFamily (h : γ → ℂ) (0 : ℂ)
        (((r / (r - 1)) / r₁ : ℝ) : ℂ) z) (ENNReal.ofReal r₁) ρ
        ≤ W ^ ((r / (r - 1)) / r₁) := by
      have hre : (Work.Analysis.Interpolation.expFamily ((0 : ℝ) : ℂ)
          (((r / (r - 1)) / r₁ : ℝ) : ℂ) z).re = (r / (r - 1)) / r₁ := by
        rw [Work.Analysis.Interpolation.expFamily_ofReal_re, hz']
        ring
      have h' := eLpNorm_analyticFamily_re_of_ne_zero (μ := ρ) (f := (h : γ → ℂ)) (P := r / (r - 1))
        (t₀ := 0) (t := (r / (r - 1)) / r₁) (s := ENNReal.ofReal r₁) hRpos
        (ENNReal.ofReal_ne_zero_iff.mpr hr₁) ?_ hre (hF := (Work.Analysis.Interpolation.aemeasurable_analyticFamily h _ _ _).aestronglyMeasurable)
        (hf := h.aestronglyMeasurable)
      · simpa only [← hWdef, Complex.ofReal_zero] using h'
      · rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal hr₁.le, div_eq_mul_inv]
    have h2 : ‖F z‖ₑ ≤ (M₁ : ℝ≥0∞) * U ^ (p / p₁) * V ^ (q / q₁)
        * W ^ ((r / (r - 1)) / r₁) :=
      le_trans h1 (mul_le_mul_right hb1 ((M₁ : ℝ≥0∞) * U ^ (p / p₁) * V ^ (q / q₁)))
    have h3 : (M₁ : ℝ≥0∞) * U ^ (p / p₁) * V ^ (q / q₁) * W ^ ((r / (r - 1)) / r₁)
        = ENNReal.ofReal ((M₁ : ℝ) * U.toReal ^ (p / p₁) * V.toReal ^ (q / q₁)
            * W.toReal ^ ((r / (r - 1)) / r₁)) := by
      rw [← ENNReal.ofReal_coe_nnreal (p := M₁),
        ← ofReal_toReal_const_eq3_nn (m := (M₁ : ℝ)) (U := U) (V := V) (W := W)
          (α := p / p₁) (β := q / q₁) (γ := (r / (r - 1)) / r₁)
          (by positivity) hUfin hVfin hWfin (by positivity) (by positivity) (by positivity)]
    rw [h3, ← ofReal_norm] at h2
    rwa [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h2
  have hhad := Work.Analysis.Interpolation.norm_le_interp_of_strip_edges hθ₀.le hθ₁.le hFdiff
    hBdd hedge0 hedge1
  have hselfp : (1 - (θ : ℂ)) * ((p / p₀ : ℝ) : ℂ) + (θ : ℂ) * ((p / p₁ : ℝ) : ℂ) = 1 :=
    Work.Analysis.Interpolation.expFamily_interp_self (ne_of_gt hp) hpθ
  have hselfq : (1 - (θ : ℂ)) * ((q / q₀ : ℝ) : ℂ) + (θ : ℂ) * ((q / q₁ : ℝ) : ℂ) = 1 :=
    Work.Analysis.Interpolation.expFamily_interp_self (ne_of_gt hq) hqθ
  have hselfh : (1 - (θ : ℂ)) * (0 : ℂ) + (θ : ℂ) * (((r / (r - 1)) / r₁ : ℝ) : ℂ) = 1 := by
    rw [mul_zero, zero_add, ← Complex.ofReal_mul, hγexp, Complex.ofReal_one]
  have hFθ : F (θ : ℂ) = Λ (f : α → ℂ) (g : β → ℂ) (h : γ → ℂ) := by
    rw [hFdef]
    simp only [Work.Analysis.Interpolation.analyticFamily_self hselfp,
      Work.Analysis.Interpolation.analyticFamily_self hselfq,
      Work.Analysis.Interpolation.analyticFamily_self hselfh]
  have hα : (1 - θ) * (p / p₀) + θ * (p / p₁) = 1 :=
    Work.Analysis.Interpolation.interp_self (ne_of_gt hp) hpθ
  have hβ : (1 - θ) * (q / q₀) + θ * (q / q₁) = 1 :=
    Work.Analysis.Interpolation.interp_self (ne_of_gt hq) hqθ
  have hγ' : (1 - θ) * 0 + θ * ((r / (r - 1)) / r₁) = 1 := by
    rw [mul_zero, zero_add]; exact hγexp
  have harith : ((M₀ : ℝ) * U.toReal ^ (p / p₀) * V.toReal ^ (q / q₀)) ^ (1 - θ)
      * ((M₁ : ℝ) * U.toReal ^ (p / p₁) * V.toReal ^ (q / q₁)
        * W.toReal ^ ((r / (r - 1)) / r₁)) ^ θ
      = (M₀ : ℝ) ^ (1 - θ) * (M₁ : ℝ) ^ θ * U.toReal * V.toReal * W.toReal := by
    have hkey := Work.Analysis.Interpolation.rpow_interp_arith3 (m₀ := (M₀ : ℝ)) (m₁ := (M₁ : ℝ))
      (x := U.toReal) (y := V.toReal) (w := W.toReal) (α₀ := p / p₀) (α₁ := p / p₁)
      (β₀ := q / q₀) (β₁ := q / q₁) (γ₀ := 0) (γ₁ := (r / (r - 1)) / r₁) (θ := θ)
      (by positivity) (by positivity)
      (ENNReal.toReal_pos hU0 (ne_top_of_lt hUfin)) (ENNReal.toReal_pos hV0 (ne_top_of_lt hVfin))
      (ENNReal.toReal_pos hW0 (ne_top_of_lt hWfin)) hα hβ hγ'
    simpa using hkey
  have hconv : ENNReal.ofReal (((M₀ : ℝ) * U.toReal ^ (p / p₀) * V.toReal ^ (q / q₀)) ^ (1 - θ)
      * ((M₁ : ℝ) * U.toReal ^ (p / p₁) * V.toReal ^ (q / q₁)
        * W.toReal ^ ((r / (r - 1)) / r₁)) ^ θ)
      = (M₀ : ℝ≥0∞) ^ (1 - θ) * (M₁ : ℝ≥0∞) ^ θ * U * V * W := by
    rw [harith, Work.Analysis.Interpolation.ofReal_arith_convert3 (by positivity) (by positivity)
      hUfin hVfin hWfin hθ₀.le hθ₁.le, ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal]
  calc ‖Λ (f : α → ℂ) (g : β → ℂ) (h : γ → ℂ)‖ₑ
      = ENNReal.ofReal ‖F (θ : ℂ)‖ := by rw [hFθ, ofReal_norm]
    _ ≤ ENNReal.ofReal (((M₀ : ℝ) * U.toReal ^ (p / p₀) * V.toReal ^ (q / q₀)) ^ (1 - θ)
          * ((M₁ : ℝ) * U.toReal ^ (p / p₁) * V.toReal ^ (q / q₁)
            * W.toReal ^ ((r / (r - 1)) / r₁)) ^ θ) := ENNReal.ofReal_le_ofReal hhad
    _ = (M₀ : ℝ≥0∞) ^ (1 - θ) * (M₁ : ℝ≥0∞) ^ θ * U * V * W := hconv

end Work.KMTAreas.A5
