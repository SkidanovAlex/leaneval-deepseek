import Mathlib
import Submission.Work.BourgainPlan.Maximal.l2_defs

/-!
# Smoothness of the polynomial profile `Φ_N(β) = ∫₀¹ e(β P(N s)) ds`

The profile `polyProfile P N β` is the integral over `s ∈ [0,1]` of an exponential whose phase is
*linear* in `β`.  Hence it is the characteristic function, evaluated at `2πβ`, of the pushforward
of Lebesgue measure on `(0,1]` under the compactly supported map `s ↦ P(N s)`.  As that pushforward
is a finite measure with all moments (its support is the image of `[0,1]` under a continuous map,
hence bounded), Mathlib's `MeasureTheory.contDiff_charFun'` gives `C^∞`-smoothness in `β`, and
composition with the linear map `β ↦ 2πβ` preserves it.

This is the polynomial analogue of `ppProf_contDiff` for the pure power `y^d`.
-/

namespace Work.BourgainPlan.Maximal

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The phase `s ↦ P(N s)` of the polynomial profile, as a real-valued function of `s`. -/
private noncomputable def polyProfilePhase (P : Polynomial ℤ) (N : ℕ) (s : ℝ) : ℝ :=
  (toRealPoly P).eval ((N : ℝ) * s)

private lemma continuous_polyProfilePhase (P : Polynomial ℤ) (N : ℕ) :
    Continuous (polyProfilePhase P N) :=
  (Polynomial.continuous (toRealPoly P)).comp (continuous_const.mul continuous_id)

/-- The pushforward of Lebesgue measure on `(0,1]` under the phase `s ↦ P(N s)`.  The profile is
the characteristic function of this finite measure, evaluated at `2πβ`. -/
private noncomputable def polyProfileMeasure (P : Polynomial ℤ) (N : ℕ) : Measure ℝ :=
  Measure.map (polyProfilePhase P N) (volume.restrict (Set.Ioc (0 : ℝ) 1))

private instance instIsFiniteMeasureRestrictIoc :
    IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
  isFiniteMeasure_restrict.mpr
    (by rw [Real.volume_Ioc, sub_zero]; exact ENNReal.ofReal_one ▸ ENNReal.one_ne_top)

private instance instIsFiniteMeasurePolyProfileMeasure (P : Polynomial ℤ) (N : ℕ) :
    IsFiniteMeasure (polyProfileMeasure P N) := by
  unfold polyProfileMeasure
  infer_instance

/-- Every moment of `polyProfileMeasure P N` is finite: the phase is bounded on `[0,1]`. -/
private lemma memLp_polyProfileMeasure (P : Polynomial ℤ) (N : ℕ) (k : ℕ) :
    MemLp (id : ℝ → ℝ) (k : ℝ≥0∞) (polyProfileMeasure P N) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuous_polyProfilePhase P N).continuousOn
  have hbdd : ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
      ‖polyProfilePhase P N t‖ ≤ max 1 C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact (hC t ⟨le_of_lt ht.1, ht.2⟩).trans (le_max_right _ _)
  have hmem : MemLp (fun t : ℝ => polyProfilePhase P N t) (k : ℝ≥0∞)
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    MemLp.of_bound (continuous_polyProfilePhase P N).aestronglyMeasurable (max 1 C) hbdd
  unfold polyProfileMeasure
  exact (memLp_map_measure_iff (μ := volume.restrict (Set.Ioc (0 : ℝ) 1))
    (f := polyProfilePhase P N) (g := (id : ℝ → ℝ)) (p := (k : ℝ≥0∞))
    (by fun_prop) (continuous_polyProfilePhase P N).aemeasurable).mpr (by simpa using hmem)

/-- The profile is the characteristic function of `polyProfileMeasure P N` at `2πβ`. -/
private lemma polyProfile_eq_charFun (P : Polynomial ℤ) (N : ℕ) (β : ℝ) :
    polyProfile P N β = MeasureTheory.charFun (polyProfileMeasure P N) (2 * Real.pi * β) := by
  rw [MeasureTheory.charFun_apply_real, polyProfile,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [polyProfileMeasure,
    integral_map (μ := volume.restrict (Set.Ioc (0 : ℝ) 1))
      (φ := polyProfilePhase P N)
      (f := fun v : ℝ => Complex.exp (↑(2 * Real.pi * β) * ↑v * Complex.I))
      (continuous_polyProfilePhase P N).aemeasurable (by fun_prop)]
  apply integral_congr_ae
  filter_upwards with s
  unfold polyProfilePhase
  congr 1
  push_cast
  ring

/-- **The polynomial profile `β ↦ ∫₀¹ e(β P(N s)) ds` is `C^∞`.** -/
theorem contDiff_polyProfile (P : Polynomial ℤ) (N : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun β : ℝ => polyProfile P N β) := by
  have hcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (MeasureTheory.charFun (polyProfileMeasure P N)) :=
    MeasureTheory.contDiff_charFun' (n := ⊤) (memLp_polyProfileMeasure P N)
  have hcomp := hcd.comp (by fun_prop : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun β : ℝ => 2 * Real.pi * β))
  rw [show (fun β : ℝ => polyProfile P N β)
      = (fun β : ℝ => MeasureTheory.charFun (polyProfileMeasure P N) (2 * Real.pi * β))
      from funext (polyProfile_eq_charFun P N)]
  exact hcomp

end

end Work.BourgainPlan.Maximal
