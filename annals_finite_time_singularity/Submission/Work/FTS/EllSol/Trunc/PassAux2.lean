/-
Copyright: work module for the Elgindi finite-time singularity project (area `FTS.EllSol`).

Auxiliary facts for the truncation passage: support of the cutoff derivatives, measurability
of strip-continuous integrands, and the `lintegral`-to-`integral` comparison.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllSol.Trunc.PassAux
import Submission.Work.FTS.EllSol.Trunc.chiDeriv2

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

/-- The integration domain `ℝ × Iθ`. -/
abbrev SI : Set (ℝ × ℝ) := (Set.univ : Set ℝ) ×ˢ Work.Spaces.Iθ

/-- The window whose mass the cutoff controls: `[-2N,2N] × Iθ`. -/
abbrev win (N : ℝ) : Set (ℝ × ℝ) := Set.Icc (-(2 * N)) (2 * N) ×ˢ Work.Spaces.Iθ

/-- The cutoff multiple `g ↦ (t,θ) ↦ chi N t · g t θ`. -/
abbrev trun (N : ℝ) (g : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun t θ => chi N t * g t θ

/-! ## Vanishing of the cutoff derivatives away from the transition region -/

theorem deriv_chi_eq_zero_of_gt {N t : ℝ} (hN : 0 < N) (ht : 2 * N < |t|) :
    deriv (chi N) t = 0 := by
  have hopen : IsOpen {s : ℝ | 2 * N < |s|} := isOpen_lt continuous_const continuous_abs
  have hev : (chi N) =ᶠ[𝓝 t] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [hopen.mem_nhds ht] with s hs
    exact chi_eq_zero hN (le_of_lt hs)
  rw [hev.deriv_eq, deriv_const]

theorem deriv2_chi_eq_zero_of_gt {N t : ℝ} (hN : 0 < N) (ht : 2 * N < |t|) :
    deriv (deriv (chi N)) t = 0 := by
  have hopen : IsOpen {s : ℝ | 2 * N < |s|} := isOpen_lt continuous_const continuous_abs
  have hev : (deriv (chi N)) =ᶠ[𝓝 t] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [hopen.mem_nhds ht] with s hs
    exact deriv_chi_eq_zero_of_gt hN hs
  rw [hev.deriv_eq, deriv_const]

theorem deriv2_chi_eq_zero_of_lt {N t : ℝ} (hN : 0 < N) (ht : |t| < N) :
    deriv (deriv (chi N)) t = 0 := by
  have hopen : IsOpen {s : ℝ | |s| < N} := isOpen_lt continuous_abs continuous_const
  have hev : (deriv (chi N)) =ᶠ[𝓝 t] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [hopen.mem_nhds ht] with s hs
    have hc : (chi N) =ᶠ[𝓝 s] (fun _ : ℝ => (1 : ℝ)) := by
      filter_upwards [hopen.mem_nhds hs] with u hu
      exact chi_eq_one hN (le_of_lt hu)
    rw [hc.deriv_eq, deriv_const]
  rw [hev.deriv_eq, deriv_const]

/-! ## Measurability of strip-continuous integrands -/

theorem aesm_strip_mul {u v : ℝ × ℝ → ℝ}
    (hu : ContinuousOn u ((Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hv : ContinuousOn v ((Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2))) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => u p * v p)
      (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) :=
  aesm_strip (hu.mul hv)

theorem aemeasurable_ofReal_strip {u : ℝ × ℝ → ℝ}
    (hu : ContinuousOn u ((Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2))) :
    AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (u p))
      (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) :=
  ENNReal.measurable_ofReal.comp_aemeasurable (aesm_strip hu).aemeasurable

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
