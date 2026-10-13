import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The "box" Tonelli lemma `ZBoxLintegral`

`ZBoxLintegral` compares a **slicewise** bound on a kernel `f u θ` with the **box** integral:
if for every `u ∈ [a,b]` the angular integral of `f u ·` is at most `c u`, then the angular
integral of the `u`-integral of `f` is at most the `u`-integral of `c`.  In symbols:

`∫⁻_θ (∫_u f u θ) ≤ ∫_u c u`, i.e. `"∫_θ ∫_u f ≤ ∫_u ∫_θ f ≤ ∫_u c"`.

The point is that the *first* inequality (`∫_θ ∫_u f ≤ ∫_u ∫_θ f`) is Tonelli for the
`θ`-then-`u` iterated integral, and the only joint measurability available is the one in the
order `(volume.restrict Iθ).prod (volume.restrict (Icc a b))` applied to the swapped function
`p ↦ f p.2 p.1` — exactly the hypothesis `haem` of the statement.  Mathlib's
`MeasureTheory.lintegral_lintegral_swap` is stated with precisely this measurability
hypothesis, so no separate "swap of almost-everywhere measurability" argument is needed.

The passage from the *Bochner* integral `∫ u in a..b, f u θ` to the `∫⁻`-integral is the
elementary inequality `ENNReal.ofReal (∫ f) ≤ ∫⁻ ENNReal.ofReal f` (`ofReal_integral_le_lintegral`
below), which holds for **every** real function: for a non-integrable function the Bochner
integral takes the junk value `0` while the right-hand side is at least `0`.  In particular the
statement does not need the nonnegativity hypothesis `hnn`, nor the slice measurability
`hslice_meas`; both are kept because the statement is fixed.
-/

namespace Work.FTS.EllipticEst.Honest

-- The nonnegativity `hnn` and the slice measurability `hslice_meas` of the statement are not
-- needed for the argument below (see the module docstring); they are kept because the statement
-- is fixed.
set_option linter.unusedVariables false

open MeasureTheory

/-- For any real-valued function, the `ENNReal.ofReal` of the Bochner integral is at most the
`∫⁻` of the `ofReal`s.  (For a non-integrable function the Bochner integral is the junk value
`0`, and for an integrable one the claim follows from
`integral_eq_lintegral_pos_part_sub_lintegral_neg_part` together with
`ENNReal.ofReal_toReal_le`.) -/
theorem ofReal_integral_le_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : α → ℝ) :
    ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  by_cases hf : Integrable f μ
  · rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf]
    refine (ENNReal.ofReal_le_ofReal ?_).trans ENNReal.ofReal_toReal_le
    exact sub_le_self _ ENNReal.toReal_nonneg
  · rw [integral_undef hf]
    simp

theorem ZBoxLintegral {f : ℝ → ℝ → ℝ} {c : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hnn : ∀ u θ, 0 ≤ f u θ)
    (hslice_meas : ∀ θ ∈ Work.Spaces.Iθ, MeasureTheory.AEStronglyMeasurable (fun u => f u θ)
      (MeasureTheory.volume.restrict (Set.Icc a b)))
    (haem : AEMeasurable (fun p : ℝ × ℝ => f p.2 p.1)
      ((MeasureTheory.volume.restrict Work.Spaces.Iθ).prod
        (MeasureTheory.volume.restrict (Set.Icc a b))))
    (hslice : ∀ u ∈ Set.Icc a b,
      MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iθ)
        (fun θ => ENNReal.ofReal (f u θ)) ≤ ENNReal.ofReal (c u))
    (hc0 : ∀ u ∈ Set.Icc a b, 0 ≤ c u)
    (hc : MeasureTheory.IntegrableOn c (Set.Icc a b)) :
    MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iθ)
        (fun θ => ENNReal.ofReal (∫ u in a..b, f u θ))
      ≤ ENNReal.ofReal (∫ u in Set.Icc a b, c u) := by
  -- Step 1: for every `θ`, the Bochner integral in `u` is dominated by the `∫⁻` in `u`.
  have hpt : ∀ θ : ℝ, ENNReal.ofReal (∫ u in a..b, f u θ)
      ≤ ∫⁻ u, ENNReal.ofReal (f u θ) ∂(MeasureTheory.volume.restrict (Set.Icc a b)) := by
    intro θ
    have h1 : ∫ u in a..b, f u θ
        = ∫ u, f u θ ∂(MeasureTheory.volume.restrict (Set.Ioc a b)) :=
      intervalIntegral.integral_of_le hab
    rw [h1]
    refine (ofReal_integral_le_lintegral (fun u => f u θ)
      (μ := MeasureTheory.volume.restrict (Set.Ioc a b))).trans_eq ?_
    rw [MeasureTheory.restrict_Ioc_eq_restrict_Icc]
  -- `haem` rewritten for `uncurry`, as `lintegral_lintegral_swap` wants it.
  have hjoint : AEMeasurable (Function.uncurry fun (θ : ℝ) (u : ℝ) => ENNReal.ofReal (f u θ))
      ((MeasureTheory.volume.restrict Work.Spaces.Iθ).prod
        (MeasureTheory.volume.restrict (Set.Icc a b))) := haem.ennreal_ofReal
  calc MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iθ)
        (fun θ => ENNReal.ofReal (∫ u in a..b, f u θ))
      ≤ ∫⁻ θ, (∫⁻ u, ENNReal.ofReal (f u θ) ∂(MeasureTheory.volume.restrict (Set.Icc a b)))
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) := lintegral_mono hpt
    -- Tonelli: swap the two iterated integrals (only the joint measurability `haem` is needed).
    _ = ∫⁻ u, (∫⁻ θ, ENNReal.ofReal (f u θ) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
          ∂(MeasureTheory.volume.restrict (Set.Icc a b)) :=
        lintegral_lintegral_swap (f := fun (θ : ℝ) (u : ℝ) => ENNReal.ofReal (f u θ)) hjoint
    -- Apply the slicewise hypothesis `hslice` for a.e. `u ∈ Icc a b`.
    _ ≤ ∫⁻ u, ENNReal.ofReal (c u) ∂(MeasureTheory.volume.restrict (Set.Icc a b)) := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
        exact hslice u hu
    -- Convert back from the `∫⁻` to the Bochner integral, using integrability of `c`.
    _ = ENNReal.ofReal (∫ u in Set.Icc a b, c u) := by
        rw [ofReal_integral_eq_lintegral_ofReal hc ?_]
        filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
        exact hc0 u hu

end Work.FTS.EllipticEst.Honest
