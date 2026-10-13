import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.FTS.StrongEps.E4R3.Chapters

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Integrability of the majorant profile `D * √z / (1+z)²` on `(0, ∞)`

The function `z ↦ √z / (1+z)²` is Lebesgue-integrable on `(0,∞)`: near `0` it is bounded by
`1` on the finite-measure set `(0,1]`, while on `(1,∞)` it is dominated by `z^{-3/2}`.
The factor `D` is irrelevant.  This is the "majorant profile" integrability used by the
`DecayChapter3` chain (`E4R3.Decay3`).
-/

namespace Work.FTS.StrongEps.E4R3.Decay3Aux

/-- `√z / (1+z)²` is Lebesgue-integrable on `(0, ∞)`. -/
theorem sqrt_div_sq_integrableOn :
    MeasureTheory.IntegrableOn (fun z : ℝ => Real.sqrt z / (1 + z) ^ 2) (Set.Ioi 0) := by
  -- The function is continuous on `(0,∞)`, hence a.e. strongly measurable there.
  have hcont : ContinuousOn (fun z : ℝ => Real.sqrt z / (1 + z) ^ 2) (Set.Ioi 0) := by
    apply ContinuousOn.div
    · exact Real.continuous_sqrt.continuousOn
    · fun_prop
    · intro z hz
      have hz' : (0 : ℝ) < z := hz
      positivity
  have hmeas : MeasureTheory.AEStronglyMeasurable (fun z : ℝ => Real.sqrt z / (1 + z) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    hcont.aestronglyMeasurable measurableSet_Ioi
  -- Split `(0,∞) = (0,1] ∪ (1,∞)`.
  have hsplit : Set.Ioi (0 : ℝ) = Set.Ioc 0 1 ∪ Set.Ioi 1 := by
    ext r; simp only [Set.mem_Ioi, Set.mem_Ioc, Set.mem_union]
    constructor
    · intro h; rcases lt_or_ge (1 : ℝ) r with h1 | h1
      · exact Or.inr h1
      · exact Or.inl ⟨h, h1⟩
    · rintro (⟨h, _⟩ | h)
      · exact h
      · linarith
  rw [hsplit]
  refine MeasureTheory.IntegrableOn.union ?_ ?_
  · -- On `(0,1]` the function is bounded by `1` and the measure is finite.
    refine MeasureTheory.IntegrableOn.of_bound (measure_Ioc_lt_top) ?_ 1 ?_
    · exact hmeas.mono_set (Set.Ioc_subset_Ioi_self)
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
      obtain ⟨hx0, hx1⟩ := hx
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [div_le_one (by positivity)]
      have h1 : Real.sqrt x ≤ 1 := Real.sqrt_le_one.mpr hx1
      have h2 : (1 : ℝ) ≤ (1 + x) ^ 2 := by
        have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) (by linarith : (1 : ℝ) ≤ 1 + x) 2
        simpa using this
      linarith
  · -- On `(1, ∞)` the function is dominated by `x ^ (-(3/2))`.
    have hg : MeasureTheory.IntegrableOn (fun x : ℝ => x ^ (-(3 : ℝ) / 2)) (Set.Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
    refine MeasureTheory.Integrable.mono' hg ?_ ?_
    · exact hmeas.mono_set (Set.Ioi_subset_Ioi (by norm_num))
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
      rw [Set.mem_Ioi] at hx
      have hx0 : (0 : ℝ) < x := by linarith
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hstep : Real.sqrt x / (1 + x) ^ 2 ≤ Real.sqrt x / x ^ 2 := by
        apply div_le_div_of_nonneg_left (Real.sqrt_nonneg x) (by positivity)
        exact pow_le_pow_left₀ (le_of_lt hx0) (by linarith) 2
      have hstep2 : Real.sqrt x / x ^ 2 = x ^ (-(3 : ℝ) / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast x 2, ← Real.rpow_sub hx0]
        norm_num
      rw [hstep2] at hstep
      exact hstep

theorem integrableOn_majProfile (D : ℝ) :
    MeasureTheory.IntegrableOn (fun z : ℝ => D * (Real.sqrt z / (1 + z) ^ 2)) (Set.Ioi 0) := by
  exact sqrt_div_sq_integrableOn.const_mul D

end Work.FTS.StrongEps.E4R3.Decay3Aux
