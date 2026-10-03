import Mathlib
import Submission.Lib.Unif2.Work.UnitGreen.Defs
import Submission.Lib.Unif2.Work.Potential.logCoefficient_of_pos_harmonic
import Submission.Lib.Unif2.Work.Parabolic.unbounded_near_pole_of_isGreenFunctionAt

/-!
# Normalising a Green function to unit pole coefficient

`Work.Parabolic.IsGreenFunctionAt` does not normalise the logarithmic pole.  Bôcher's theorem
(`Work.Potential.logCoefficient_of_pos_harmonic`) produces a coefficient `c ≥ 0` with
`|E x + c·log ‖ξ x - ξ z₀‖| ≤ C` near `z₀`; `Work.Parabolic.unbounded_near_pole_of_isGreenFunctionAt`
shows `E` is unbounded at `z₀`, which forces `c > 0`; then `E / c` is a Green function with pole
coefficient exactly one.  So "there is a Green function" and "there is a unit-pole Green function"
are equivalent, and the case split of the Green-function route to uniformization is stable.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

noncomputable section

open Filter Set
open Classical

namespace Work.UnitGreen

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **Normalisation of the Green function.**  A Green function on a non-compact surface can be
rescaled so that its logarithmic pole has coefficient exactly one. -/
theorem exists_isUnitGreenFunctionAt_of_isGreenFunctionAt (hX : ¬ CompactSpace X) {z₀ : X}
    {E : X → ℝ} (hE : Work.Parabolic.IsGreenFunctionAt (X := X) z₀ E) :
    ∃ E' : X → ℝ, IsUnitGreenFunctionAt (X := X) z₀ E' := by
  obtain ⟨c, hc0, C, V, hV, hbound⟩ :=
    Work.Potential.logCoefficient_of_pos_harmonic hE.harmonic (fun x hx => hE.pos hx)
  have hcne : c ≠ 0 := by
    intro hc
    have hunb := Work.Parabolic.unbounded_near_pole_of_isGreenFunctionAt (X := X) hX hE
    obtain ⟨x, hxV, hxz, hxgt⟩ := hunb |C| V hV
    have hb := hbound x hxV hxz
    rw [hc, zero_mul, add_zero] at hb
    have hEC : E x ≤ C := (abs_le.mp hb).2
    have : E x ≤ |C| := le_trans hEC (le_abs_self C)
    linarith
  have hcpos : 0 < c := lt_of_le_of_ne hc0 (Ne.symm hcne)
  refine ⟨c⁻¹ • E, ⟨⟨?_, ?_, ?_⟩, |C| / c, V, hV, ?_⟩⟩
  · intro x hx
    rw [Pi.smul_apply, smul_eq_mul]
    exact mul_pos (inv_pos.mpr hcpos) (hE.pos hx)
  · intro x hx
    exact (hE.harmonic x hx).const_smul c⁻¹
  · intro ε hε
    have hset : {x : X | ε ≤ (c⁻¹ • E) x} = {x : X | c * ε ≤ E x} := by
      ext x
      rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, inv_mul_eq_div,
        le_div_iff₀ hcpos, mul_comm]
    rw [hset]
    exact hE.isCompact_closure_level (mul_pos hcpos hε)
  · intro x hxV hx
    have hb := hbound x hxV hx
    have h1 : (c⁻¹ • E) x + Real.log ‖(chartAt ℂ z₀) x - (chartAt ℂ z₀) z₀‖
        = (E x + c * Real.log ‖(chartAt ℂ z₀) x - (chartAt ℂ z₀) z₀‖) / c := by
      rw [Pi.smul_apply, smul_eq_mul]
      field_simp
    rw [h1, abs_div, abs_of_pos hcpos]
    exact div_le_div_of_nonneg_right (le_trans hb (le_abs_self C)) hc0

end Work.UnitGreen
