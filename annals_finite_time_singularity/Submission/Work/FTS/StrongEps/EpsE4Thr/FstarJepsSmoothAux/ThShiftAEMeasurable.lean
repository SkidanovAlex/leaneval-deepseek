import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# A.e. measurability of the angular shift on `Iθ × [-ε,ε]`

The angular shift `(θ, p) ↦ thShift θ p = arctan (tan θ · e^{-p})` of the log-coordinate
`ε`-mollifier is **not** continuous on `ℝ × ℝ` (at `θ = π/2` the `tan` has a pole, while Lean's
`tan (π/2) = 0`), but it *is* continuous on the conull set `{x | x.1 ∈ (0,π/2)}` for the product
measure `(volume.restrict Iθ).prod (volume.restrict (Icc (-ε) ε))`: with `Iθ = [0,π/2]`, the
complement of `(0,π/2)` inside `Iθ` is the two-point set `{0, π/2}`.

Following the pattern of `HkSqAux/aemeasurable_shift_slice.lean`, the composite is continuous on
that conull set, hence a.e. measurable there; multiplying by the indicator of the set and
removing it again with conullity gives a.e. measurability for the full measure.

This is the measurability input shared by `ThShiftPreimageNull` (the null-preimage statement) and
`LintegralProdThShift` (the product bound for `lintegral_thShift_le`).
-/

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux

set_option autoImplicit false

/-- `θ = 0` and `θ = π/2` are null for `volume.restrict Iθ` with `Iθ = [0, π/2]`. -/
theorem measure_Iθ_compl_Ioo_eq_zero :
    (volume.restrict Work.Spaces.Iθ) (Set.Ioo 0 (π / 2))ᶜ = 0 := by
  rw [Measure.restrict_apply measurableSet_Ioo.compl]
  refine measure_mono_null ?_ (measure_union_null (measure_singleton (0 : ℝ))
    (measure_singleton (π / 2)))
  intro x hx
  simp only [Work.Spaces.Iθ, Set.mem_inter_iff, Set.mem_Icc, Set.mem_compl_iff, Set.mem_Ioo,
    Set.mem_union, Set.mem_singleton_iff] at hx ⊢
  obtain ⟨hxn, hxI⟩ := hx
  rcases lt_or_ge (0 : ℝ) x with h | h
  · rcases lt_or_ge x (π / 2) with h2 | h2
    · exact absurd ⟨h, h2⟩ hxn
    · exact Or.inr (le_antisymm hxI.2 h2)
  · exact Or.inl (le_antisymm h hxI.1)

/-- **A.e. measurability of the angular shift** `x ↦ thShift x.1 x.2` for the product of the
angular measure on `Iθ = [0,π/2]` with the shift measure on `[-ε,ε]`. -/
theorem aemeasurable_thShift_prod {ε : ℝ} :
    AEMeasurable (fun x : ℝ × ℝ => Work.FTS.StrongEps.thShift x.1 x.2)
      ((volume.restrict Work.Spaces.Iθ).prod (volume.restrict (Set.Icc (-ε) ε))) := by
  classical
  set S : Set (ℝ × ℝ) := {x | x.1 ∈ Set.Ioo 0 (π / 2)} with hS
  have hSmeas : MeasurableSet S := measurableSet_Ioo.preimage measurable_fst
  have hSnull :
      ((volume.restrict Work.Spaces.Iθ).prod (volume.restrict (Set.Icc (-ε) ε))) Sᶜ = 0 := by
    rw [show Sᶜ = (Set.Ioo 0 (π / 2))ᶜ ×ˢ (Set.univ : Set ℝ) from by
      ext x; simp [S]]
    rw [Measure.prod_prod, measure_Iθ_compl_Ioo_eq_zero, zero_mul]
  have hcont : ContinuousOn (fun x : ℝ × ℝ => Work.FTS.StrongEps.thShift x.1 x.2) S := by
    have hcos : ∀ x ∈ S, Real.cos x.1 ≠ 0 := fun x hx =>
      (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hx.1], hx.2⟩).ne'
    have h1 : ContinuousOn (fun x : ℝ × ℝ => Real.tan x.1 * Real.exp (-x.2)) S :=
      (Real.continuousOn_tan.comp continuousOn_fst hcos).mul
        (Real.continuous_exp.comp_continuousOn (by fun_prop))
    simpa only [Work.FTS.StrongEps.thShift, Function.comp_def] using
      Real.continuous_arctan.comp_continuousOn h1
  have hA : AEMeasurable (fun x : ℝ × ℝ => Work.FTS.StrongEps.thShift x.1 x.2)
      (((volume.restrict Work.Spaces.Iθ).prod (volume.restrict (Set.Icc (-ε) ε))).restrict S) :=
    hcont.aemeasurable hSmeas
  have hind : AEMeasurable (S.indicator (fun x : ℝ × ℝ => Work.FTS.StrongEps.thShift x.1 x.2))
      ((volume.restrict Work.Spaces.Iθ).prod (volume.restrict (Set.Icc (-ε) ε))) :=
    (aemeasurable_indicator_iff hSmeas).mpr hA
  refine hind.congr ?_
  filter_upwards [compl_mem_ae_iff.mpr hSnull] with x hx
  simp only [Set.mem_compl_iff, not_not] at hx
  exact Set.indicator_of_mem hx (fun x : ℝ × ℝ => Work.FTS.StrongEps.thShift x.1 x.2)

end Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux
