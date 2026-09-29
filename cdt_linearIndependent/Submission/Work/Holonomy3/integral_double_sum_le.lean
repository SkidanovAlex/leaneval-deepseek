import Mathlib
import Submission.Work.Holonomy3.expectation_max_blocked
import Submission.Work.Holonomy3.mv_lex_defs

/-!
# The holonomy double-sum bound with the diagonal term removed

`Work.Holonomy3.expectation_max_blocked` bounds the expectation of
`Σ_{a,b} max (g_{κ a}(t_a), g_{κ b}(t_b))` over the torus `[0,1]^d` by
`d² · rearrInt w φ + 8 (l+1)² (d+1) G₀`.

Here we bound the difference of that expectation with the expectation of the *single* sum
`Σ_a g_{κ a}(t_a)`, i.e. exactly the quantity that the paper's STEP 5 produces after the
diagonal `a = b` has been thrown away, with the slightly larger error term
`(8 (l+1)² (d+1) + d) G₀`.

The extra `d · G₀` is precisely what is needed to control the single sum: since
`|g_p| ≤ G₀` on `[0,1]` and the product measure is supported on `[0,1]^d`, the single sum has
absolute value at most `d G₀` almost everywhere, so `- ∫ Σ_a g_{κ a}(t_a) ≤ d G₀` by
`MeasureTheory.norm_integral_le_of_norm_le_const` (no integrability hypothesis needed).
-/

namespace Work.Holonomy3

open MeasureTheory
open scoped BigOperators

theorem integral_double_sum_le {l d : ℕ} (hd : 0 < d) (φ : Fin (l + 1) → ℂ → ℂ)
    (κ : Fin d → Fin (l + 1)) (w : Fin (l + 1) → ℝ)
    (hc : ∀ p, |((Finset.univ.filter (fun a : Fin d => κ a = p)).card : ℝ) / (d : ℝ) - w p|
      ≤ 2 / (d : ℝ))
    {G₀ : ℝ} (hG0 : 0 ≤ G₀)
    (hcont : ∀ p, ContinuousOn (Submission.CDTPlan.circleLog (φ p)) (Set.Icc 0 1))
    (hg : ∀ p t, t ∈ Set.Icc 0 1 → |Submission.CDTPlan.circleLog (φ p) t| ≤ G₀) :
    (∫ t : Fin d → ℝ, (∑ a, ∑ b, max (Submission.CDTPlan.circleLog (φ (κ a)) (t a))
        (Submission.CDTPlan.circleLog (φ (κ b)) (t b))) ∂(Work.Holonomy3.torMeasure d))
      - (∫ t : Fin d → ℝ, ∑ a, Submission.CDTPlan.circleLog (φ (κ a)) (t a) ∂(Work.Holonomy3.torMeasure d))
      ≤ (d : ℝ) ^ 2 * Submission.CDTPlan.rearrInt w φ
        + (8 * ((l : ℝ) + 1) ^ 2 * ((d : ℝ) + 1) + (d : ℝ)) * G₀ := by
  -- The double sum, by `expectation_max_blocked` (its error term `8 (l+1)² d + 8 (l+1)²` is
  -- `8 (l+1)² (d+1)`).
  have h1 : (∫ t : Fin d → ℝ, (∑ a, ∑ b, max (Submission.CDTPlan.circleLog (φ (κ a)) (t a))
        (Submission.CDTPlan.circleLog (φ (κ b)) (t b))) ∂(Work.Holonomy3.torMeasure d))
      ≤ (d : ℝ) ^ 2 * Submission.CDTPlan.rearrInt w φ
        + (8 * ((l : ℝ) + 1) ^ 2 * ((d : ℝ) + 1)) * G₀ := by
    have h := expectation_max_blocked (l := l) (d := d) hd w φ κ hG0 hcont
      (fun p t ht => hg p t ht) hc
    have hconst : 8 * ((l : ℝ) + 1) ^ 2 * (d : ℝ) + 8 * ((l : ℝ) + 1) ^ 2
        = 8 * ((l : ℝ) + 1) ^ 2 * ((d : ℝ) + 1) := by ring
    rw [hconst] at h
    exact h
  -- The single sum is bounded by `d G₀` in absolute value, almost everywhere on the cube.
  have h2 : -(∫ t : Fin d → ℝ,
        (∑ a, Submission.CDTPlan.circleLog (φ (κ a)) (t a)) ∂(Work.Holonomy3.torMeasure d))
      ≤ (d : ℝ) * G₀ := by
    have hb : |∫ t : Fin d → ℝ,
        (∑ a, Submission.CDTPlan.circleLog (φ (κ a)) (t a)) ∂(Work.Holonomy3.torMeasure d)|
        ≤ (d : ℝ) * G₀ := by
      have h := MeasureTheory.norm_integral_le_of_norm_le_const (μ := Work.Holonomy3.torMeasure d)
        (f := fun t : Fin d → ℝ => ∑ a, Submission.CDTPlan.circleLog (φ (κ a)) (t a))
        (C := (d : ℝ) * G₀) ?_
      · have huniv : (Work.Holonomy3.torMeasure d).real Set.univ = 1 := by
          simp [Measure.real, measure_univ]
        simpa [Real.norm_eq_abs, huniv] using h
      · have hall : ∀ᵐ t ∂(Work.Holonomy3.torMeasure d), ∀ a : Fin d, t a ∈ Set.Icc 0 1 := by
          rw [Filter.eventually_all]
          exact fun a => ae_eval_mem_Icc a
        filter_upwards [hall] with t ht
        rw [Real.norm_eq_abs]
        calc |∑ a, Submission.CDTPlan.circleLog (φ (κ a)) (t a)|
            ≤ ∑ a, |Submission.CDTPlan.circleLog (φ (κ a)) (t a)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _a : Fin d, G₀ := Finset.sum_le_sum (fun a _ => hg (κ a) (t a) (ht a))
          _ = (d : ℝ) * G₀ := by simp [Finset.card_univ, Fintype.card_fin]
    linarith [neg_le_abs (∫ t : Fin d → ℝ,
      (∑ a, Submission.CDTPlan.circleLog (φ (κ a)) (t a)) ∂(Work.Holonomy3.torMeasure d)), hb]
  linarith [h1, h2]

end Work.Holonomy3
