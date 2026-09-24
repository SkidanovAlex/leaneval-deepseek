import Mathlib
import Submission.Work.Mori.Defs
import Submission.Work.Parabolic.Basic
import Submission.Work.Parabolic.unbounded_near_pole_of_isGreenFunctionAt
import Submission.Work.UnitGreen.Defs
import Submission.Work.Potential.logCoefficient_of_pos_harmonic
import Submission.Work.Potential.removable_singularity_of_bounded_near

namespace Work.Mori

/-- **The normalisation of the logarithmic pole of a Green function.**  A Green function in the
relative-compactness sense (`Work.Parabolic.IsGreenFunctionAt`: positive and harmonic off `z₀`, with
the closures of all superlevel sets compact) can be rescaled so that the logarithmic pole at `z₀` has
coefficient exactly one: there is `E'` with `Work.UnitGreen.IsUnitGreenFunctionAt z₀ E'`.

Route: the logarithmic coefficient of a positive harmonic function
(`Work.Potential.logCoefficient_of_pos_harmonic`) gives `c ≥ 0` with
`E x + c log ‖ξ x - ξ z₀‖` bounded near `z₀`.  If `c = 0`, then `E` is bounded near `z₀`, so it
extends across `z₀` (`Work.Potential.removable_singularity_of_bounded_near`) to a harmonic `U ≥ 0` on
`X` which still has relatively compact non-negative superlevel sets; `U` attains its maximum on
`{U ≥ U p / 2}` and a harmonic function attaining its maximum on the connected `X` is constant
(`Submission.SubharmonicOnX.eq_of_isMaxOn`), which forces `X` to be compact, contradicting `hX`.
Hence `c > 0` and `E' = c⁻¹ • E` is a unit-pole Green function: positivity and harmonicity are
immediate, the superlevel sets rescale, and the growth bound is the boundedness above divided by `c`.
This is a close variant of the existing `Work.Potential.normalize_green_function` (which proves the
same statement for the unsatisfiable `Submission.HasGreenFunctionWeak`); the case analysis and the
rescaling arithmetic carry over, with the relative-compactness hypothesis used only through
`IsGreenFunctionAt.exists_isCompact_subset`.  The `c = 0` contradiction is also essentially already
proved in `Work/Parabolic/unbounded_near_pole_of_isGreenFunctionAt.lean`. -/
theorem exists_isUnitGreenFunctionAt_of_isGreenFunctionAt
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (hX : ¬ CompactSpace X) {z₀ : X} {E : X → ℝ}
    (hE : Work.Parabolic.IsGreenFunctionAt z₀ E) :
    ∃ E' : X → ℝ, Work.UnitGreen.IsUnitGreenFunctionAt z₀ E' := by
  classical
  obtain ⟨c, hc0, C, V, hV, hbound⟩ :=
    Work.Potential.logCoefficient_of_pos_harmonic (X := X) (z₀ := z₀) (u := E)
      hE.harmonic (fun x hx => hE.pos hx)
  -- ### The logarithmic coefficient `c` cannot vanish.
  have hcne : c ≠ 0 := by
    intro hc
    have hunb := Work.Parabolic.unbounded_near_pole_of_isGreenFunctionAt (X := X) hX hE
    obtain ⟨x, hxV, hxz, hxgt⟩ := hunb |C| V hV
    have hb := hbound x hxV hxz
    rw [hc, zero_mul, add_zero] at hb
    have hEC : E x ≤ C := (abs_le.mp hb).2
    have hle : E x ≤ |C| := le_trans hEC (le_abs_self C)
    linarith
  have hcpos : 0 < c := lt_of_le_of_ne hc0 (Ne.symm hcne)
  -- ### Rescale by `c⁻¹`.
  refine ⟨c⁻¹ • E, ⟨⟨?_, ?_, ?_⟩, |C| / c, V, hV, ?_⟩⟩
  · -- positivity
    intro x hx
    rw [Pi.smul_apply, smul_eq_mul]
    exact mul_pos (inv_pos.mpr hcpos) (hE.pos hx)
  · -- harmonicity off the pole
    intro x hx
    exact (hE.harmonic x hx).const_smul c⁻¹
  · -- relative compactness of the superlevel sets rescales
    intro ε hε
    have hset : {x : X | ε ≤ (c⁻¹ • E) x} = {x : X | c * ε ≤ E x} := by
      ext x
      rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, inv_mul_eq_div,
        le_div_iff₀ hcpos, mul_comm]
    rw [hset]
    exact hE.isCompact_closure_level (mul_pos hcpos hε)
  · -- the logarithmic growth bound, divided by `c`
    intro x hxV hx
    have hb := hbound x hxV hx
    have h1 : (c⁻¹ • E) x + Real.log ‖(chartAt ℂ z₀) x - (chartAt ℂ z₀) z₀‖
        = (E x + c * Real.log ‖(chartAt ℂ z₀) x - (chartAt ℂ z₀) z₀‖) / c := by
      rw [Pi.smul_apply, smul_eq_mul]
      field_simp
    rw [h1, abs_div, abs_of_pos hcpos]
    exact div_le_div_of_nonneg_right (le_trans hb (le_abs_self C)) hc0

end Work.Mori
