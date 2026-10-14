import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.AeS1.SigFirstOrderDefs
import Submission.Work.FTS.StrongEps.blocks.L12_Fstar_add_open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.Trunc

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false

/-! ## Notation for the truncation passage -/

/-- The open strip on which the data are assumed to be `C²`. -/
abbrev strip : Set (ℝ × ℝ) := (Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)




/-! ## Vanishing of the cutoff derivatives away from the transition region -/

theorem deriv_chi_eq_zero_of_gt {N t : ℝ} (hN : 0 < N) (ht : 2 * N < |t|) :
    deriv (chi N) t = 0 := by
  have hopen : IsOpen {s : ℝ | 2 * N < |s|} := isOpen_lt continuous_const continuous_abs
  have hev : (chi N) =ᶠ[𝓝 t] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [hopen.mem_nhds ht] with s hs
    exact chi_eq_zero hN (le_of_lt hs)
  rw [hev.deriv_eq, deriv_const]



/-! ## Measurability of strip-continuous integrands -/



/-! ## From a `lintegral` bound to an integral bound -/

theorem integral_le_of_lintegral_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    {b : ℝ} (h0 : 0 ≤ᵐ[μ] f) (hb : 0 ≤ b)
    (h : ∫⁻ a, ENNReal.ofReal (f a) ∂μ ≤ ENNReal.ofReal b) :
    ∫ a, f a ∂μ ≤ b := by
  by_cases hf : AEStronglyMeasurable f μ
  · rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae h0 hf]
    rw [← ENNReal.toReal_ofReal hb]
    exact (ENNReal.toReal_le_toReal (ne_of_lt (lt_of_le_of_lt h ENNReal.ofReal_lt_top))
      ENNReal.ofReal_ne_top).mpr h
  · rw [MeasureTheory.integral_undef]
    · exact hb
    · intro hint
      exact hf hint.aestronglyMeasurable

end

end Work.FTS.EllSol.Trunc
