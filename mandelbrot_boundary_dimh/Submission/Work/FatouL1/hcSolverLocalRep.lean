import Mathlib
import Submission.Work.FatouL1.solverKernel
import Submission.Work.FatouL1.cotContourIndep
import Submission.Work.FatouL1.cotContourSelf

/-!
# FATOU-L1: the solver as a single cotangent contour integral, locally

`Work.FatouL1.hcSolver h` is *locally* (near any `z` whose line `Re = Re z - 1/2` lies in the
strip `(a,b)` of holomorphy of `h`) equal to `-1/2` times the *cotangent* contour integral taken
on the fixed line `Re s = Re z - 1/2`:

  `hcSolver h w = -(1/2) * ∫ y, h (Re z - 1/2 + y*I) * cot (π (Re z - 1/2 + y*I - w))`.

Indeed, by the Cauchy–Heine principle the cotangent contour integral
`c ↦ ∫ y, h (c + y*I) * cot (π (c + y*I - w))` does not depend on the line `c` as long as
`c ∈ (Re w - 1, Re w) ∩ (a,b)` (`Work.FatouL1.cotContourIndep`), and on the line
`c = Re w - 1/2` it equals `-2 * hcSolver h w` (`Work.FatouL1.cotContourSelf`).  Near `z` the
fixed line `Re z - 1/2` is such an admissible line for `w`, giving the stated local representation.
-/

open MeasureTheory Filter
open scoped Topology ENNReal

namespace Work.FatouL1

theorem hcSolverLocalRep {a b m : ℝ} (hab : a < b) {h : ℂ → ℂ}
    (hhol : DifferentiableOn ℂ h {z : ℂ | a < z.re ∧ z.re < b})
    (hint : ∀ x ∈ Set.Ioo a b, MeasureTheory.Integrable (fun y : ℝ => h ((x : ℂ) + y * Complex.I)))
    (hmass : ∀ x ∈ Set.Ioo a b,
      ∫⁻ y : ℝ, ENNReal.ofReal ‖h ((x : ℂ) + y * Complex.I)‖ ≤ ENNReal.ofReal m)
    {z : ℂ} (hz1 : a + 1 / 2 < z.re) (hz2 : z.re < b + 1 / 2) :
    Work.FatouL1.hcSolver h =ᶠ[nhds z] fun w : ℂ => -(1 / 2) *
      ∫ y : ℝ, h (((z.re - 1 / 2 : ℝ) : ℂ) + y * Complex.I) *
        Complex.cot (Real.pi * (((z.re - 1 / 2 : ℝ) : ℂ) + y * Complex.I - w)) := by
  set c : ℝ := z.re - 1 / 2 with hc
  have hc_mem : c ∈ Set.Ioo a b := by
    refine ⟨?_, ?_⟩ <;> rw [hc] <;> linarith
  -- the open set of `w` near `z` on which the argument runs
  have hS : ∀ᶠ w : ℂ in nhds z,
      w.re - 1 / 2 ∈ Set.Ioo a b ∧ w.re ∈ Set.Ioo c (c + 1) := by
    have hcont : Continuous fun w : ℂ => w.re - 1 / 2 := Complex.continuous_re.sub continuous_const
    have h1 : ∀ᶠ w : ℂ in nhds z, w.re - 1 / 2 ∈ Set.Ioo a b :=
      (isOpen_Ioo.preimage hcont).mem_nhds (by exact ⟨by linarith, by linarith⟩)
    have h2 : ∀ᶠ w : ℂ in nhds z, w.re ∈ Set.Ioo c (c + 1) :=
      (isOpen_Ioo.preimage Complex.continuous_re).mem_nhds
        (by rw [hc]; exact ⟨by linarith, by linarith⟩)
    exact h1.and h2
  filter_upwards [hS] with w hw
  have hwmem : w.re - 1 / 2 ∈ Set.Ioo a b := hw.1
  have hwlo : c < w.re := hw.2.1
  have hwhi : w.re < c + 1 := hw.2.2
  -- integrability on the line `Re = Re w - 1/2`
  have hInt : MeasureTheory.Integrable
      (fun y : ℝ => h (((w.re - 1 / 2 : ℝ) : ℂ) + y * Complex.I)) :=
    hint (w.re - 1 / 2) hwmem
  -- on the line through `Re w - 1/2` the contour integral is `-2 * hcSolver h w`
  have hself := cotContourSelf (h := h) (z := w) hInt
  -- and by Cauchy–Heine it is the same on the fixed line `Re = c`
  have hInd : (∫ y : ℝ, h ((c : ℂ) + y * Complex.I) *
        Complex.cot (Real.pi * ((c : ℂ) + y * Complex.I - w)))
      = (∫ y : ℝ, h (((w.re - 1 / 2 : ℝ) : ℂ) + y * Complex.I) *
        Complex.cot (Real.pi * (((w.re - 1 / 2 : ℝ) : ℂ) + y * Complex.I - w))) := by
    rcases lt_trichotomy c (w.re - 1 / 2) with hlt | heq | hgt
    · exact cotContourIndep hab hhol hmass hc_mem hwmem hlt (by linarith) (by linarith)
    · rw [heq]
    · exact (cotContourIndep hab hhol hmass hwmem hc_mem hgt (by linarith) (by linarith)).symm
  rw [hInd, hself]
  ring

end Work.FatouL1
