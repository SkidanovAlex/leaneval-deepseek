/-
Copyright: work module for the Elgindi finite-time singularity project.

Auxiliary real-analysis facts for the angular estimates of
T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
incompressible Euler equations on ℝ³*, Annals of Math. 194 (3) 2021.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The fundamental theorem of calculus on a compact sub-interval of `(0, π/2)`

The hypothesis of the main lemma `integral_deriv_eq_sub` provides the derivative of `g` only on
the *open* interval `(0, π/2)`, together with the integrability of `g'^2 · sin(2θ)^{2-γ}`
(with `γ > 1`).

On a compact sub-interval `[a,b] ⊂ (0, π/2)` the angular weight `θ ↦ sin(2θ)^{2-γ}` is bounded
below by a positive constant `c` (`sin_two_rpow_lower_bound`), so the given integrability
yields that `g'` itself is integrable on `[a,b]` (via `integrableOn_sq_of_integrableOn_sq_mul`
and `integrableOn_of_integrableOn_sq`, the latter requiring only that `g'` be a.e. strongly
measurable — here it is a derivative, so `measurable_deriv`/`aestronglyMeasurable_deriv`
apply).  Since `g` is differentiable, hence continuous, on the open interval, the fundamental
theorem of calculus applies in the form
`intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`.
-/

noncomputable section

open MeasureTheory Set

-- style only: `haveI` is used for a local finite-measure instance below, and the hypothesis
-- `hγ` of the source statement is not needed for the argument (a compact sub-interval of
-- `(0, π/2)` bounds the weight away from `0` for every exponent)
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.FTS_RXTPieces.Angular

/-- On a compact sub-interval `[a,b] ⊂ (0, π/2)` the angular weight `θ ↦ sin(2θ)^{2-γ}` is
bounded below by a positive constant. -/
theorem sin_two_rpow_lower_bound {γ : ℝ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b < Real.pi / 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ θ ∈ Set.Icc a b, c ≤ (Real.sin (2 * θ)) ^ (2 - γ) := by
  have hne : (Set.Icc a b).Nonempty := ⟨a, le_rfl, hab⟩
  have hcont : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 - γ)) (Set.Icc a b) := by
    refine ContinuousOn.rpow_const ?_ ?_
    · exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
    · intro θ hθ
      left
      apply ne_of_gt
      exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, ha]) (by linarith [hθ.2, hb])
  obtain ⟨θ₀, hθ₀, hmin⟩ := isCompact_Icc.exists_isMinOn hne hcont
  refine ⟨(Real.sin (2 * θ₀)) ^ (2 - γ), ?_, fun θ hθ => hmin hθ⟩
  apply Real.rpow_pos_of_pos
  exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ₀.1, ha]) (by linarith [hθ₀.2, hb])

/-- If `∫ θ in s, f θ ^ 2 * w θ` is finite and `w ≥ c > 0` on `s`, then `∫ θ in s, f θ ^ 2` is
finite (strong measurability of `f ^ 2` being assumed). -/
theorem integrableOn_sq_of_integrableOn_sq_mul {f w : ℝ → ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    (hmeas : AEStronglyMeasurable (fun θ => f θ ^ 2) (volume.restrict s))
    (h : IntegrableOn (fun θ => f θ ^ 2 * w θ) s volume) {c : ℝ} (hc : 0 < c)
    (hw : ∀ θ ∈ s, c ≤ w θ) :
    IntegrableOn (fun θ => f θ ^ 2) s volume := by
  refine Integrable.mono' (h.const_mul c⁻¹) hmeas ?_
  refine ae_restrict_of_forall_mem hs fun θ hθ => ?_
  have hwc : 1 ≤ c⁻¹ * w θ := by
    have h1 : c⁻¹ * c = 1 := inv_mul_cancel₀ (ne_of_gt hc)
    calc (1 : ℝ) = c⁻¹ * c := h1.symm
      _ ≤ c⁻¹ * w θ := mul_le_mul_of_nonneg_left (hw θ hθ) (le_of_lt (inv_pos.mpr hc))
  calc ‖f θ ^ 2‖ = f θ ^ 2 := by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    _ ≤ f θ ^ 2 * (c⁻¹ * w θ) := le_mul_of_one_le_right (sq_nonneg _) hwc
    _ = c⁻¹ * (f θ ^ 2 * w θ) := by ring

/-- On a set of finite measure, a measurable function with integrable square is integrable:
`|f θ| ≤ f θ ^ 2 + 1`, and the constant function `1` is integrable on a finite measure space. -/
theorem integrableOn_of_integrableOn_sq {f : ℝ → ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    (hmeas : AEStronglyMeasurable f (volume.restrict s))
    (h : IntegrableOn (fun θ => f θ ^ 2) s volume) (hfin : volume s ≠ ⊤) :
    IntegrableOn f s volume := by
  haveI : IsFiniteMeasure (volume.restrict s) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr hfin⟩
  refine Integrable.mono' (h.add (MeasureTheory.integrable_const (1 : ℝ))) hmeas ?_
  refine ae_restrict_of_forall_mem hs fun θ _ => ?_
  have habs : |f θ| ≤ f θ ^ 2 + 1 := by
    rw [abs_le']
    constructor <;> nlinarith [sq_nonneg (f θ + 1), sq_nonneg (f θ - 1)]
  simpa [Pi.add_apply, Real.norm_eq_abs] using habs

/-- **Fundamental theorem of calculus**, on a compact sub-interval of `(0, π/2)`, for a function
whose derivative is known on the *open* interval `(0, π/2)` and whose derivative is
square-integrable against the weight `sin(2θ)^{2-γ}`. -/
theorem integral_deriv_eq_sub {γ : ℝ} (hγ : 1 < γ) {g g' : ℝ → ℝ}
    (hg : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt g (g' θ) θ)
    (hint2 : MeasureTheory.IntegrableOn
      (fun θ => g' θ ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ)) Work.Spaces.Iθ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < Real.pi / 2) :
    ∫ x in a..b, g' x = g b - g a := by
  -- the hypotheses force `g'` to agree with the everywhere-defined `deriv g` on `(a,b)`
  have hderiv_eq : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), deriv g θ = g' θ :=
    fun θ hθ => (hg θ hθ).deriv
  have hmem : ∀ θ ∈ Set.Ioc a b, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    intro θ hθ
    rw [Set.mem_Ioc] at hθ
    exact ⟨lt_trans ha hθ.1, lt_of_le_of_lt hθ.2 hb⟩
  -- `g' ^ 2` is a.e. strongly measurable (it is a square of a derivative)
  have hmeas_sq : AEStronglyMeasurable (fun θ => g' θ ^ 2) (volume.restrict (Set.Ioc a b)) := by
    have h1 : AEStronglyMeasurable (fun θ => deriv g θ ^ 2)
        (volume.restrict (Set.Ioc a b)) :=
      (aestronglyMeasurable_deriv g (volume.restrict (Set.Ioc a b))).pow 2
    refine h1.congr (ae_restrict_of_forall_mem measurableSet_Ioc fun θ hθ => ?_)
    show deriv g θ ^ 2 = g' θ ^ 2
    rw [hderiv_eq θ (hmem θ hθ)]
  have hmeas_g' : AEStronglyMeasurable g' (volume.restrict (Set.Ioc a b)) := by
    have h1 : AEStronglyMeasurable (fun θ => deriv g θ) (volume.restrict (Set.Ioc a b)) :=
      aestronglyMeasurable_deriv g _
    refine h1.congr (ae_restrict_of_forall_mem measurableSet_Ioc fun θ hθ => ?_)
    exact hderiv_eq θ (hmem θ hθ)
  -- the compact sub-interval sits inside `Iθ = [0, π/2]`, so the weighted integrability restricts
  have hsub : Set.Ioc a b ⊆ Work.Spaces.Iθ := by
    intro θ hθ
    rw [Set.mem_Ioc] at hθ
    change θ ∈ Set.Icc 0 (Real.pi / 2)
    rw [Set.mem_Icc]
    exact ⟨le_of_lt (lt_trans ha hθ.1), le_of_lt (lt_of_le_of_lt hθ.2 hb)⟩
  -- the weight has a positive lower bound on `[a,b]`, hence `(g')²` is integrable there
  obtain ⟨c, hc, hcw⟩ := sin_two_rpow_lower_bound (γ := γ) ha hab hb
  have hw : ∀ θ ∈ Set.Ioc a b, c ≤ (Real.sin (2 * θ)) ^ (2 - γ) :=
    fun θ hθ => hcw θ (Set.Ioc_subset_Icc_self hθ)
  have hsq_int : IntegrableOn (fun θ => g' θ ^ 2) (Set.Ioc a b) :=
    integrableOn_sq_of_integrableOn_sq_mul measurableSet_Ioc hmeas_sq
      (hint2.mono_set hsub) hc hw
  -- and on the finite measure set `(a,b]` this gives the integrability of `g'` itself
  have hg'_int : IntegrableOn g' (Set.Ioc a b) :=
    integrableOn_of_integrableOn_sq measurableSet_Ioc hmeas_g' hsq_int measure_Ioc_lt_top.ne
  have hint : IntervalIntegrable g' volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr hg'_int
  -- `g` is differentiable, hence continuous, on a neighbourhood of `[a,b]`
  have hcont : ContinuousOn g (Set.Icc a b) := by
    have hdiff : DifferentiableOn ℝ g (Set.Ioo 0 (Real.pi / 2)) :=
      fun θ hθ => (hg θ hθ).differentiableAt.differentiableWithinAt
    refine (hdiff.continuousOn).mono ?_
    intro θ hθ
    rw [Set.mem_Icc] at hθ
    exact ⟨lt_of_lt_of_le ha hθ.1, lt_of_le_of_lt hθ.2 hb⟩
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont
    (fun θ hθ => hg θ (hmem θ ⟨hθ.1, le_of_lt hθ.2⟩)) hint

end Work.FTS_RXTPieces.Angular
