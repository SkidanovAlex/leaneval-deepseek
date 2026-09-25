import Mathlib
import Submission.Work.BourgainPlan.Maximal.dilation_hl

/-!
# Helpers for `piece_le_hlMax_of_deriv_pos`

Elementary facts about a polynomial `q` whose derivative is positive on a half-open interval
`(a,b]` (so `q` is strictly increasing there), together with a pointwise `ℝ≥0∞` comparison
lemma used to insert a weight into a lower Lebesgue integral.
-/

namespace Work.BourgainPlan.Maximal

open MeasureTheory Set
open scoped ENNReal

open Commons.Analysis.Maximal (hlMax)

/-- If the derivative of `q` is positive on `(a,b]`, then `u ↦ q.eval u` is strictly increasing
on `[a,b]`. -/
lemma poly_strictMonoOn_Icc_of_deriv_pos (q : Polynomial ℝ) {a b : ℝ}
    (hderiv : ∀ u ∈ Set.Ioc a b, 0 < q.derivative.eval u) :
    StrictMonoOn (fun u => q.eval u) (Set.Icc a b) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc a b) q.continuous.continuousOn ?_
  intro x hx
  rw [interior_Icc] at hx
  rw [(Polynomial.hasDerivAt (𝕜 := ℝ) q x).deriv]
  exact hderiv x ⟨hx.1, hx.2.le⟩

/-- The image of `(a,b]` under a polynomial map which is strictly increasing on `[a,b]` is the
half-open interval `(q a, q b]`. -/
lemma image_Ioc_poly_eval (q : Polynomial ℝ) {a b : ℝ} (hab : a ≤ b)
    (hmono : StrictMonoOn (fun u => q.eval u) (Set.Icc a b)) :
    (fun u => q.eval u) '' Set.Ioc a b = Set.Ioc (q.eval a) (q.eval b) := by
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hum : u ∈ Set.Icc a b := ⟨le_of_lt hu.1, hu.2⟩
    have ham : a ∈ Set.Icc a b := ⟨le_refl a, hab⟩
    have hbm : b ∈ Set.Icc a b := ⟨hab, le_refl b⟩
    exact ⟨hmono ham hum hu.1, hmono.monotoneOn hum hbm hu.2⟩
  · rintro ⟨hv1, hv2⟩
    have hmem : v ∈ (fun u => q.eval u) '' Set.Icc a b :=
      intermediate_value_Icc hab q.continuous.continuousOn ⟨hv1.le, hv2⟩
    obtain ⟨u, hu, hqu⟩ := hmem
    refine ⟨u, ⟨?_, hu.2⟩, hqu⟩
    rcases lt_or_eq_of_le hu.1 with h | h
    · exact h
    · exfalso
      rw [← h] at hqu
      exact absurd hqu (ne_of_lt hv1)

/-- On `(a,b]` the polynomial map strictly increasing on `[a,b]` takes values strictly above
its value at `a`. -/
lemma poly_eval_lt_of_mem_Ioc (q : Polynomial ℝ) {a b : ℝ} (hab : a < b)
    (hmono : StrictMonoOn (fun u => q.eval u) (Set.Icc a b)) {u : ℝ} (hu : u ∈ Set.Ioc a b) :
    q.eval a < q.eval u :=
  hmono ⟨le_refl a, hab.le⟩ ⟨hu.1.le, hu.2⟩ hu.1

/-- For a polynomial with positive derivative on `(a,b]` with `a < b`, one has
`q a < q b`. -/
lemma poly_eval_sub_pos (q : Polynomial ℝ) {a b : ℝ} (hab : a < b)
    (hderiv : ∀ u ∈ Set.Ioc a b, 0 < q.derivative.eval u) :
    0 < q.eval b - q.eval a := by
  have hmono := poly_strictMonoOn_Icc_of_deriv_pos q hderiv
  have := hmono ⟨le_refl a, hab.le⟩ ⟨hab.le, le_refl b⟩ hab
  linarith

/-- **Inserting a weight bounded below into a lower Lebesgue integral.**  If `c ≤ W u` for all
`u ∈ s` with `c > 0`, then the integral of `g` over `s` is at most `c⁻¹` times the integral of
`g * W`. -/
theorem setLIntegral_le_inv_mul_of_le_weight {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {s : Set α} (hs : MeasurableSet s) {c : ℝ} (hc : 0 < c) (g : α → ENNReal) (W : α → ℝ)
    (hW : ∀ u ∈ s, c ≤ W u) :
    ∫⁻ u in s, g u ∂μ
      ≤ (ENNReal.ofReal c)⁻¹ * ∫⁻ u in s, g u * ENNReal.ofReal (W u) ∂μ := by
  have hc0 : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.mpr hc).ne'
  have hctop : ENNReal.ofReal c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmain : ENNReal.ofReal c * ∫⁻ u in s, g u ∂μ
      ≤ ∫⁻ u in s, g u * ENNReal.ofReal (W u) ∂μ := by
    calc ENNReal.ofReal c * ∫⁻ u in s, g u ∂μ
        = ENNReal.ofReal c * ∫⁻ u, s.indicator g u ∂μ := by rw [lintegral_indicator hs g]
      _ = ∫⁻ u, ENNReal.ofReal c * s.indicator g u ∂μ :=
            (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ ≤ ∫⁻ u, s.indicator (fun u => g u * ENNReal.ofReal (W u)) u ∂μ := by
            refine lintegral_mono fun u => ?_
            by_cases hu : u ∈ s
            · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu, mul_comm (g u)]
              exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (hW u hu)) _
            · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu, mul_zero]
      _ = ∫⁻ u in s, g u * ENNReal.ofReal (W u) ∂μ :=
            lintegral_indicator hs (fun u => g u * ENNReal.ofReal (W u))
  exact Commons.Analysis.Maximal.le_inv_mul_of_mul_le hc hmain
