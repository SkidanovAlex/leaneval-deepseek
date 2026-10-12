import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB3.Split.lowSlotBound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.CS.Pieces.integrable_ind_mul_lowMult`

The box-indicator times the low-momentum multiplier is integrable:

`x ↦ 1_{acube ℓ}(x) · lowMult fc κ ℓ ψ x ∈ L¹(ℝ³)` for `κ > 0`, `ℓ > 0` and continuous `ψ`.

The function is supported on the compact cube `acube ℓ` and uniformly bounded there, so the
statement reduces to two facts about `Work.BoseBoxFix.lowMult` that are already available:

* the uniform bound `|lowMult fc κ ℓ ψ y| ≤ (2π)⁻³·(Mℓ³)·vol(B(0,2κ))`
  (`Work.BoseFixB3.Split.lowMult_abs_le`, with `M` a bound for `ψ` on the cube and
  `Work.BoseFixB3.Split.integral_indicator_norm_le` giving the `L¹`-mass of the localised fibre);
* strong measurability of `x ↦ lowMult fc κ ℓ ψ x`, proved here by exhibiting it as a
  `p`-integral with a jointly strongly measurable integrand
  (`MeasureTheory.StronglyMeasurable.integral_prod_right`) — the same device as
  `Submission/Work/BoseFixB3/Split/lowSlotStronglyMeasurable.lean` uses for `lowSlot`.
-/

namespace Work.BoseFixB3.CS.Pieces

open MeasureTheory Filter Metric
open scoped Real Topology

noncomputable section

local notation "𝔼" => EuclideanSpace ℝ (Fin 3)

/-- `x ↦ lowMult fc κ ℓ ψ x` is strongly measurable for continuous `ψ` (in fact the argument
is a `p`-integral of the jointly strongly measurable function
`(x,p) ↦ e^{i⟪p,x⟫} f(‖p‖/κ) (1_{acube ℓ}ψ)^^(p)`). -/
private theorem stronglyMeasurable_lowMult {fc : Work.BoseBoxFix.LowCut} {κ ℓ : ℝ}
    {ψ : 𝔼 → ℝ} (hcont : Continuous ψ) :
    StronglyMeasurable (fun x : 𝔼 => Work.BoseBoxFix.lowMult fc κ ℓ ψ x) := by
  set u : 𝔼 → ℂ := fun z => (((Submission.BoseGases.acube ℓ).indicator ψ z : ℝ) : ℂ) with hu
  -- `kinFT u` is strongly measurable, being the `y`-integral of a jointly strongly
  -- measurable integrand (no integrability is needed).
  have hkin : StronglyMeasurable (fun p : 𝔼 => Submission.BoseGases.kinFT u p) := by
    have hjoint : StronglyMeasurable (fun w : 𝔼 × 𝔼 =>
        Complex.exp (-(Complex.I * (inner ℝ w.1 w.2 : ℂ))) * u w.2) := by
      have h1 : Continuous (fun w : 𝔼 × 𝔼 =>
          Complex.exp (-(Complex.I * (inner ℝ w.1 w.2 : ℂ)))) :=
        Complex.continuous_exp.comp (continuous_neg.comp (continuous_const.mul
          (Complex.continuous_ofReal.comp continuous_inner)))
      have h2 : StronglyMeasurable (fun w : 𝔼 × 𝔼 => u w.2) :=
        (Complex.continuous_ofReal.measurable.comp
          ((hcont.measurable.indicator (Submission.BoseGases.acube_measurable ℓ)))).stronglyMeasurable.comp_measurable
          measurable_snd
      exact h1.stronglyMeasurable.mul h2
    exact hjoint.integral_prod_right (ν := volume)
  -- the full `(x,p)`-integrand of `lowMult`
  have hjoint2 : StronglyMeasurable (fun w : 𝔼 × 𝔼 =>
      Complex.exp (Complex.I * (inner ℝ w.2 w.1 : ℂ)) * ((fc.f (‖w.2‖ / κ) : ℝ) : ℂ) *
        Submission.BoseGases.kinFT u w.2) := by
    have hA : StronglyMeasurable (fun w : 𝔼 × 𝔼 =>
        Complex.exp (Complex.I * (inner ℝ w.2 w.1 : ℂ))) :=
      (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
        (continuous_inner.comp (continuous_snd.prodMk continuous_fst))))).measurable.stronglyMeasurable
    have hB : StronglyMeasurable (fun w : 𝔼 × 𝔼 =>
        ((fc.f (‖w.2‖ / κ) : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.comp
        (fc.smooth.continuous.comp ((continuous_norm.comp continuous_snd).div_const κ))).measurable.stronglyMeasurable
    have hC : StronglyMeasurable (fun w : 𝔼 × 𝔼 => Submission.BoseGases.kinFT u w.2) :=
      hkin.comp_measurable measurable_snd
    exact (hA.mul hB).mul hC
  have hint : StronglyMeasurable (fun x : 𝔼 =>
      ∫ p : 𝔼, Complex.exp (Complex.I * (inner ℝ p x : ℂ)) * ((fc.f (‖p‖ / κ) : ℝ) : ℂ) *
          Submission.BoseGases.kinFT u p) := hjoint2.integral_prod_right (ν := volume)
  have h1 : StronglyMeasurable (fun x : 𝔼 =>
      (∫ p : 𝔼, Complex.exp (Complex.I * (inner ℝ p x : ℂ)) * ((fc.f (‖p‖ / κ) : ℝ) : ℂ) *
          Submission.BoseGases.kinFT u p).re) :=
    Complex.continuous_re.comp_stronglyMeasurable hint
  have h2 : StronglyMeasurable (fun x : 𝔼 =>
      (((2 * Real.pi) ^ 3)⁻¹ : ℝ) * (∫ p : 𝔼,
        Complex.exp (Complex.I * (inner ℝ p x : ℂ)) * ((fc.f (‖p‖ / κ) : ℝ) : ℂ) *
          Submission.BoseGases.kinFT u p).re) := h1.const_mul _
  have hgoal : (fun x : 𝔼 =>
      (((2 * Real.pi) ^ 3)⁻¹ : ℝ) * (∫ p : 𝔼,
        Complex.exp (Complex.I * (inner ℝ p x : ℂ)) * ((fc.f (‖p‖ / κ) : ℝ) : ℂ) *
          Submission.BoseGases.kinFT u p).re)
      = fun x : 𝔼 => Work.BoseBoxFix.lowMult fc κ ℓ ψ x := by
    funext x
    rw [Work.BoseBoxFix.lowMult, ← hu, ← Complex.re_ofReal_mul]
  rw [← hgoal]
  exact h2

theorem integrable_ind_mul_lowMult {fc : Work.BoseBoxFix.LowCut} {κ ℓ : ℝ}
    (hκ : 0 < κ) (hℓ : 0 < ℓ) {ψ : EuclideanSpace ℝ (Fin 3) → ℝ} (hcont : Continuous ψ) :
    Integrable (fun x : EuclideanSpace ℝ (Fin 3) =>
      (Submission.BoseGases.acube ℓ).indicator (fun _ : EuclideanSpace ℝ (Fin 3) => (1 : ℝ)) x
        * Work.BoseBoxFix.lowMult fc κ ℓ ψ x) := by
  classical
  -- `ψ` is bounded on the compact cube
  obtain ⟨C₀, hC₀⟩ :=
    (Work.UBBInputs9.B.acube_isCompact ℓ).exists_bound_of_continuousOn hcont.continuousOn
  have hM : (0 : ℝ) ≤ max C₀ 0 := le_max_right _ _
  have hψb : ∀ z ∈ Submission.BoseGases.acube ℓ, |ψ z| ≤ max C₀ 0 := fun z hz =>
    le_trans (by simpa [Real.norm_eq_abs] using hC₀ z hz) (le_max_left _ _)
  -- the `L¹`-mass of the localised fibre
  have hD : ∫ z : 𝔼, ‖(((Submission.BoseGases.acube ℓ).indicator ψ z : ℝ) : ℂ)‖ ≤ max C₀ 0 * ℓ ^ 3 :=
    Work.BoseFixB3.Split.integral_indicator_norm_le hℓ hM hψb
  have hD0 : (0 : ℝ) ≤ max C₀ 0 * ℓ ^ 3 := mul_nonneg hM (by positivity)
  -- the uniform multiplier bound
  set C : ℝ := ((2 * π) ^ 3)⁻¹ * (max C₀ 0 * ℓ ^ 3)
    * (volume (Metric.closedBall (0 : 𝔼) (2 * κ))).toReal with hCdef
  have hCnn : 0 ≤ C := by
    rw [hCdef]
    exact mul_nonneg (mul_nonneg (by positivity) hD0) ENNReal.toReal_nonneg
  have hbound : ∀ y : 𝔼, |Work.BoseBoxFix.lowMult fc κ ℓ ψ y| ≤ C := fun y => by
    rw [hCdef]
    exact Work.BoseFixB3.Split.lowMult_abs_le (fc := fc) (κ := κ) (ℓ := ℓ)
      (D := max C₀ 0 * ℓ ^ 3) hκ hD0 hD y
  -- the dominating function `C · 1_{acube ℓ}` is integrable
  have hgint : Integrable (fun x : 𝔼 =>
      (Submission.BoseGases.acube ℓ).indicator (fun _ => C) x) volume := by
    rw [MeasureTheory.integrable_indicator_iff (Submission.BoseGases.acube_measurable ℓ)]
    refine MeasureTheory.IntegrableOn.of_bound (Submission.BoseGases.acube_lt_top ℓ hℓ.le)
      aestronglyMeasurable_const C ?_
    filter_upwards with z
    rw [Real.norm_of_nonneg hCnn]
  refine Integrable.mono' hgint ?_ (Eventually.of_forall ?_)
  · exact ((measurable_const.indicator (Submission.BoseGases.acube_measurable ℓ)).stronglyMeasurable.mul
      (stronglyMeasurable_lowMult (fc := fc) (κ := κ) (ℓ := ℓ) hcont)).aestronglyMeasurable
  · intro x
    by_cases hx : x ∈ Submission.BoseGases.acube ℓ
    · simp only [Set.indicator_of_mem hx, one_mul]
      simpa [Real.norm_eq_abs] using hbound x
    · simp only [Set.indicator_of_notMem hx, zero_mul, norm_zero, le_refl]

end

end Work.BoseFixB3.CS.Pieces
