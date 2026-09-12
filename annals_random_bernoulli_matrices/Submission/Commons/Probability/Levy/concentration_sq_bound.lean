import Mathlib
import Submission.Commons.Probability.Levy.levy_interval_mass_bound

set_option linter.style.haveILetI false

open MeasureTheory
open scoped ENNReal

namespace Commons.Probability.Levy

/-! # Squared Lévy-type bound

Derivation of `concentration_sq_bound` from `levy_interval_mass_bound`, applied to the law of
the difference of two independent copies of `μ`.  The square of the mass of any interval of
half-width `w` is at most the `ν`-mass of `Icc (-(2w)) (2w)` (two independent draws both landing
in the interval imply their difference has norm at most `2w`), and the characteristic function
of the difference law is `|charFun μ|²`.
-/

/-- Mass of a square under the product measure. -/
lemma measureReal_prod_self (μ : Measure ℝ) [IsProbabilityMeasure μ] (s : Set ℝ) :
    (μ.prod μ).real (s ×ˢ s) = (μ.real s) ^ 2 := by
  rw [measureReal_def, measureReal_def, Measure.prod_prod]
  rw [ENNReal.toReal_mul, pow_two]

/-- If both coordinates lie in `Icc (l-w) (l+w)`, their difference lies in `Icc (-(2w)) (2w)`. -/
lemma prod_subset_sub_preIcc (l w : ℝ) :
    Set.Icc (l - w) (l + w) ×ˢ Set.Icc (l - w) (l + w)
      ⊆ (fun p : ℝ × ℝ => p.1 - p.2) ⁻¹' Set.Icc (-(2 * w)) (2 * w) := by
  intro p hp
  rw [Set.mem_preimage]
  rw [Set.mem_Icc]
  constructor
  · have hp1 : l - w ≤ p.1 := (Set.mem_Icc.mp hp.1).1
    have hp2 : p.2 ≤ l + w := (Set.mem_Icc.mp hp.2).2
    nlinarith
  · have hp1 : p.1 ≤ l + w := (Set.mem_Icc.mp hp.1).2
    have hp2 : l - w ≤ p.2 := (Set.mem_Icc.mp hp.2).1
    nlinarith

/-- Square of an interval mass is bounded by the mass of the same interval under the law of the
difference of two independent copies. -/
lemma real_sq_le (μ : Measure ℝ) [IsProbabilityMeasure μ] (l w : ℝ) :
    (μ.real (Set.Icc (l - w) (l + w))) ^ 2 ≤
      ((μ.prod μ).map (fun p : ℝ × ℝ => p.1 - p.2)).real (Set.Icc (-(2 * w)) (2 * w)) := by
  have hprod : (μ.prod μ).real ((Set.Icc (l - w) (l + w)) ×ˢ (Set.Icc (l - w) (l + w))) =
      (μ.real (Set.Icc (l - w) (l + w))) ^ 2 :=
    measureReal_prod_self μ (Set.Icc (l - w) (l + w))
  rw [← hprod]
  have hsub : Measurable (fun p : ℝ × ℝ => p.1 - p.2) :=
    MeasurableSub₂.measurable_sub
  refine (measureReal_mono (s₁ := (Set.Icc (l - w) (l + w)) ×ˢ (Set.Icc (l - w) (l + w)))
      (s₂ := (fun p : ℝ × ℝ => p.1 - p.2) ⁻¹' Set.Icc (-(2 * w)) (2 * w))
      ?_ (measure_ne_top (μ.prod μ) _)).trans_eq ?_
  · exact prod_subset_sub_preIcc l w
  · exact (map_measureReal_apply hsub measurableSet_Icc).symm

/-- The characteristic function of the difference law is the product of the characteristic
function and its conjugate (i.e. `|φ|²` as a complex number). -/
lemma charFun_difference (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    charFun ((μ.prod μ).map (fun p : ℝ × ℝ => p.1 - p.2)) t =
      charFun μ t * (starRingEnd ℂ) (charFun μ t) := by
  have hsub : Measurable (fun p : ℝ × ℝ => p.1 - p.2) := MeasurableSub₂.measurable_sub
  calc
    charFun ((μ.prod μ).map (fun p : ℝ × ℝ => p.1 - p.2)) t
        = ∫ z : ℝ, Complex.exp (t * z * Complex.I)
            ∂((μ.prod μ).map (fun p : ℝ × ℝ => p.1 - p.2)) := by
            rw [charFun_apply_real]
    _ = ∫ p : ℝ × ℝ, Complex.exp (t * (p.1 - p.2) * Complex.I) ∂(μ.prod μ) := by
            rw [integral_map hsub.aemeasurable]
            · simp
            · fun_prop
    _ = (∫ x : ℝ, Complex.exp (t * x * Complex.I) ∂μ) *
          (∫ y : ℝ, Complex.exp (-(t * y) * Complex.I) ∂μ) := by
            have hrewrite : (fun p : ℝ × ℝ => Complex.exp (t * (p.1 - p.2) * Complex.I))
                = (fun p : ℝ × ℝ => Complex.exp (t * p.1 * Complex.I) *
                    Complex.exp (-(t * p.2) * Complex.I)) := by
              funext p
              have harg : t * (p.1 - p.2) * Complex.I =
                  t * p.1 * Complex.I + (-(t * p.2)) * Complex.I := by ring
              rw [harg, Complex.exp_add]
            rw [hrewrite]
            simpa [mul_comm, mul_left_comm, mul_assoc] using
              (MeasureTheory.integral_prod_mul (μ := μ) (ν := μ)
                (f := fun x : ℝ => Complex.exp (t * x * Complex.I))
                (g := fun y : ℝ => Complex.exp (-(t * y) * Complex.I)))
    _ = charFun μ t * (∫ y : ℝ, Complex.exp (-(t * y) * Complex.I) ∂μ) := by
            rw [← charFun_apply_real (μ := μ) (t := t)]
    _ = charFun μ t * (starRingEnd ℂ) (charFun μ t) := by
            congr 1
            calc
              (∫ y : ℝ, Complex.exp (-(t * y) * Complex.I) ∂μ) = charFun μ (-t) := by
                rw [show (fun y : ℝ => Complex.exp (-(t * y) * Complex.I))
                      = (fun y : ℝ => Complex.exp ((-t) * y * Complex.I)) by
                    funext y
                    congr 1
                    ring_nf]
                simpa using (charFun_apply_real (μ := μ) (t := -t)).symm
              _ = (starRingEnd ℂ) (charFun μ t) := by simp

/-- Norm of the characteristic function of the difference law is the squared norm of the
characteristic function of `μ`. -/
lemma norm_charFun_difference (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    ‖charFun ((μ.prod μ).map (fun p : ℝ × ℝ => p.1 - p.2)) t‖ = ‖charFun μ t‖ ^ 2 := by
  rw [charFun_difference]
  rw [norm_mul]
  rw [Complex.norm_conj]
  rw [← pow_two]

/-- Interval integral of the squared characteristic function over the dual window. -/
lemma intervalIntegral_norm_charFun_difference (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (w : ℝ) :
    (∫ t in (-(1 / w))..(1 / w),
        ‖charFun ((μ.prod μ).map (fun p : ℝ × ℝ => p.1 - p.2)) t‖)
      = ∫ t in (-(1 / w))..(1 / w), ‖charFun μ t‖ ^ 2 := by
  have hf : (fun t : ℝ => ‖charFun ((μ.prod μ).map (fun p : ℝ × ℝ => p.1 - p.2)) t‖)
          = (fun t : ℝ => ‖charFun μ t‖ ^ 2) := by
    funext t
    exact norm_charFun_difference μ t
  rw [hf]

/-- Lévy-type squared bound: square of any interval mass (half-width w) is at most a universal constant times w times the integral of |charFun|² over |t| ≤ 1/w. Derivable from `Commons.Probability.Levy.levy_interval_mass_bound` applied to the law of the difference of two independent copies. -/
theorem concentration_sq_bound (μ : Measure ℝ) [MeasureTheory.IsProbabilityMeasure μ]
    (w : ℝ) (hw : 0 < w) :
    ∀ l : ℝ,
      (μ.real (Set.Icc (l - w) (l + w))) ^ 2 ≤
        16 * w * ∫ t in (-(1 / w))..(1 / w), ‖charFun μ t‖ ^ 2 := by
  intro l
  let ν : Measure ℝ := (μ.prod μ).map (fun p : ℝ × ℝ => p.1 - p.2)
  haveI : IsProbabilityMeasure ν := by
    dsimp [ν]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  have h2w : 0 < 2 * w := by positivity
  have h1 : (μ.real (Set.Icc (l - w) (l + w))) ^ 2 ≤ ν.real (Set.Icc (-(2 * w)) (2 * w)) := by
    simpa [ν] using real_sq_le μ l w
  have hlev : ν.real (Set.Icc (0 - 2 * w) (0 + 2 * w)) ≤
      8 * (2 * w) * ∫ t in (-(2 / (2 * w)))..(2 / (2 * w)), ‖charFun ν t‖ :=
    levy_interval_mass_bound (μ := ν) (a := 0) (w := 2 * w) h2w
  have hJ : Set.Icc (-(2 * w)) (2 * w) = Set.Icc (0 - 2 * w) (0 + 2 * w) := by
    congr 1 <;> ring
  have hJ' : ν.real (Set.Icc (-(2 * w)) (2 * w)) = ν.real (Set.Icc (0 - 2 * w) (0 + 2 * w)) := by
    rw [hJ]
  have hb : 2 / (2 * w) = 1 / w := by field_simp [hw.ne']
  calc
    (μ.real (Set.Icc (l - w) (l + w))) ^ 2 ≤ ν.real (Set.Icc (-(2 * w)) (2 * w)) := h1
    _ = ν.real (Set.Icc (0 - 2 * w) (0 + 2 * w)) := hJ'
    _ ≤ 8 * (2 * w) * ∫ t in (-(2 / (2 * w)))..(2 / (2 * w)), ‖charFun ν t‖ := hlev
    _ = 8 * (2 * w) * ∫ t in (-(1 / w))..(1 / w), ‖charFun ν t‖ := by
      rw [hb]
    _ = 8 * (2 * w) * ∫ t in (-(1 / w))..(1 / w), ‖charFun μ t‖ ^ 2 := by
      rw [show (∫ t in (-(1 / w))..(1 / w), ‖charFun ν t‖) =
              ∫ t in (-(1 / w))..(1 / w), ‖charFun μ t‖ ^ 2 by
        simpa [ν] using intervalIntegral_norm_charFun_difference μ w]
    _ = 16 * w * ∫ t in (-(1 / w))..(1 / w), ‖charFun μ t‖ ^ 2 := by ring

end Commons.Probability.Levy
