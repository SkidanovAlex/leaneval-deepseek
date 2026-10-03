import Mathlib
import Submission.Work.FatouL1.hcSolver_deriv_le
import Submission.Work.FatouL1.solverKernel
import Submission.Work.FatouL1.hcSolverBound
import Submission.Work.FatouL1.hcDerivKernel
import Submission.Work.FatouL1.cotContourHasDeriv
import Submission.Work.FatouL1.hcSolverLocalRep

/-!
# FATOU-L1: the `π`-trick derivative bounds with an explicit sup bound `M`

Same route as `Work.FatouL1.hcSolver_deriv_le`, but the right-hand side is the explicit constant
`M` dominating `‖h‖` on the line through `z - 1/2` (`hM`).  The fixed-contour representation of
`hcSolver` near `z` (`hcSolverLocalRep`) turns the derivative into a cotangent contour integral on
the line `Re = Re z - 1/2`, whose two kernels are bounded by `π / cosh²` and
`2π²|sinh|/cosh³` (`hcDerivKernel`), giving `2M` and `2πM` for the two contour integrals, hence
`M` and `πM` after the factor `1/2`.
-/

open MeasureTheory Filter
open scoped Topology ENNReal

namespace Work.FatouL1

noncomputable section

theorem hcSolverDerivBoundM {a b m : ℝ} (hab : a < b) {h : ℂ → ℂ}
    (hhol : DifferentiableOn ℂ h {z : ℂ | a < z.re ∧ z.re < b})
    (hint : ∀ x ∈ Set.Ioo a b, MeasureTheory.Integrable (fun y : ℝ => h ((x : ℂ) + y * Complex.I)))
    (hmass : ∀ x ∈ Set.Ioo a b, ∫⁻ y : ℝ, ENNReal.ofReal ‖h ((x : ℂ) + y * Complex.I)‖ ≤ ENNReal.ofReal m)
    {z : ℂ} (hz1 : a + 1 / 2 < z.re) (hz2 : z.re < b - 1 / 2) {M : ℝ}
    (hMnn : 0 ≤ M) (hM : ∀ y : ℝ, ‖h (z - 1 / 2 + y * Complex.I)‖ ≤ M) :
    ‖deriv (Work.FatouL1.hcSolver h) z‖ ≤ M ∧
      ‖iteratedDeriv 2 (Work.FatouL1.hcSolver h) z‖ ≤ Real.pi * M := by
  set c : ℝ := z.re - 1 / 2 with hc
  have hca : a < c := by rw [hc]; linarith
  have hcb : c < b := by rw [hc]; linarith
  have hzc : z.re = c + 1 / 2 := by rw [hc]; ring
  have hband1 : c < z.re := by rw [hzc]; linarith
  have hband2 : z.re < c + 1 := by rw [hzc]; linarith
  -- the bound `hM` on the line through `z - 1/2`, in the parameterisation `c + y*I`
  have hle : ∀ y : ℝ, ‖h ((c : ℂ) + (y : ℂ) * Complex.I)‖ ≤ M := by
    intro y
    have hz_eq : z - 1 / 2 + ((y - z.im : ℝ) : ℂ) * Complex.I
        = (c : ℂ) + (y : ℂ) * Complex.I := by
      rw [hc]; apply Complex.ext <;> simp <;> ring
    rw [← hz_eq]
    exact hM (y - z.im)
  -- the two parametric derivatives of the fixed-contour cotangent integral
  obtain ⟨hD1, hD2⟩ := cotContourHasDeriv hab hint hmass hca hcb
  have hd1 := hD1 z hband1 hband2
  have hd2 := hD2 z hband1 hband2
  -- the solver equals `-1/2` times that integral near `z`
  have hev := hcSolverLocalRep hab hhol hint hmass hz1 (by linarith)
  have hev' : Work.FatouL1.hcSolver h =ᶠ[nhds z] fun w : ℂ => -(1 / 2) *
      ∫ y : ℝ, h ((c : ℂ) + (y : ℂ) * Complex.I) *
        Complex.cot (Real.pi * ((c : ℂ) + (y : ℂ) * Complex.I - w)) := by
    simpa only [← hc] using hev
  -- first derivative
  have hderiv1 : deriv (Work.FatouL1.hcSolver h) z = -(1 / 2) *
      (∫ y : ℝ, h ((c : ℂ) + (y : ℂ) * Complex.I) *
        ((Real.pi : ℂ) / (Complex.sin (Real.pi * ((c : ℂ) + (y : ℂ) * Complex.I - z))) ^ 2)) := by
    rw [hev'.deriv_eq]
    exact (hd1.const_mul (-(1 / 2))).deriv
  -- second derivative
  have hband_nhds : ∀ᶠ w in nhds z, c < w.re ∧ w.re < c + 1 := by
    have hopen : IsOpen {w : ℂ | c < w.re ∧ w.re < c + 1} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    exact hopen.mem_nhds ⟨hband1, hband2⟩
  have hFeq : deriv (fun w : ℂ => ∫ y : ℝ, h ((c : ℂ) + (y : ℂ) * Complex.I) *
        Complex.cot (Real.pi * ((c : ℂ) + (y : ℂ) * Complex.I - w))) =ᶠ[nhds z]
      (fun w : ℂ => ∫ y : ℝ, h ((c : ℂ) + (y : ℂ) * Complex.I) *
        ((Real.pi : ℂ) / (Complex.sin (Real.pi * ((c : ℂ) + (y : ℂ) * Complex.I - w))) ^ 2)) := by
    filter_upwards [hband_nhds] with w hw
    exact (hD1 w hw.1 hw.2).deriv
  obtain ⟨U, hUsub, hUopen, hzU⟩ := mem_nhds_iff.mp hev'
  have hderiv_eq : deriv (Work.FatouL1.hcSolver h) =ᶠ[nhds z] deriv (fun w : ℂ => -(1 / 2) *
      ∫ y : ℝ, h ((c : ℂ) + (y : ℂ) * Complex.I) *
        Complex.cot (Real.pi * ((c : ℂ) + (y : ℂ) * Complex.I - w))) := by
    filter_upwards [hUopen.mem_nhds hzU] with w hw
    have hwU : Work.FatouL1.hcSolver h =ᶠ[nhds w] fun w : ℂ => -(1 / 2) *
        ∫ y : ℝ, h ((c : ℂ) + (y : ℂ) * Complex.I) *
          Complex.cot (Real.pi * ((c : ℂ) + (y : ℂ) * Complex.I - w)) :=
      Filter.eventually_of_mem (hUopen.mem_nhds hw) hUsub
    exact hwU.deriv_eq
  have hderiv_chain : deriv (fun w : ℂ => -(1 / 2) *
      ∫ y : ℝ, h ((c : ℂ) + (y : ℂ) * Complex.I) *
        Complex.cot (Real.pi * ((c : ℂ) + (y : ℂ) * Complex.I - w)))
      =ᶠ[nhds z] (fun w : ℂ => -(1 / 2) * deriv (fun w : ℂ => ∫ y : ℝ,
        h ((c : ℂ) + (y : ℂ) * Complex.I) *
          Complex.cot (Real.pi * ((c : ℂ) + (y : ℂ) * Complex.I - w))) w) := by
    filter_upwards [hband_nhds] with w hw
    exact deriv_const_mul (-(1 / 2)) (hD1 w hw.1 hw.2).differentiableAt
  have hderiv2 : deriv (deriv (Work.FatouL1.hcSolver h)) z = -(1 / 2) *
      (∫ y : ℝ, h ((c : ℂ) + (y : ℂ) * Complex.I) *
        ((2 : ℂ) * (Real.pi : ℂ) ^ 2 * Complex.cos (Real.pi * ((c : ℂ) + (y : ℂ) * Complex.I - z)) /
          (Complex.sin (Real.pi * ((c : ℂ) + (y : ℂ) * Complex.I - z))) ^ 3)) := by
    rw [hderiv_eq.deriv_eq, hderiv_chain.deriv_eq]
    exact (((hFeq.hasDerivAt_iff).mpr hd2).const_mul (-(1 / 2))).deriv
  have hnorm : ‖(-(1 / 2) : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
  constructor
  · rw [hderiv1, norm_mul, hnorm]
    have hK := (hcDerivKernel).1 (c := c) (z := z) (S := M) (h := h) hzc hMnn hle
    calc (1 / 2 : ℝ) * ‖∫ y : ℝ, h ((c : ℂ) + (y : ℂ) * Complex.I) *
          ((Real.pi : ℂ) / (Complex.sin (Real.pi * ((c : ℂ) + (y : ℂ) * Complex.I - z))) ^ 2)‖
        ≤ (1 / 2) * (2 * M) := mul_le_mul_of_nonneg_left hK (by norm_num)
      _ = M := by ring
  · have hit : iteratedDeriv 2 (Work.FatouL1.hcSolver h) z =
        deriv (deriv (Work.FatouL1.hcSolver h)) z := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    rw [hit, hderiv2, norm_mul, hnorm]
    have hK := (hcDerivKernel).2 (c := c) (z := z) (S := M) (h := h) hzc hMnn hle
    calc (1 / 2 : ℝ) * ‖∫ y : ℝ, h ((c : ℂ) + (y : ℂ) * Complex.I) *
          ((2 : ℂ) * (Real.pi : ℂ) ^ 2 * Complex.cos (Real.pi * ((c : ℂ) + (y : ℂ) * Complex.I - z)) /
            (Complex.sin (Real.pi * ((c : ℂ) + (y : ℂ) * Complex.I - z))) ^ 3)‖
        ≤ (1 / 2) * (2 * Real.pi * M) := mul_le_mul_of_nonneg_left hK (by norm_num)
      _ = Real.pi * M := by ring

end

end Work.FatouL1
