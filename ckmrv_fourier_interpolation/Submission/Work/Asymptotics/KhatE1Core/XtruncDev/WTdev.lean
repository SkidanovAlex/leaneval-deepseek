import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.Bracket24XtruncDefs
import Submission.Work.Asymptotics.KhatE1Core.DSm1RowBound
import Submission.Work.Asymptotics.KhatE1.ZAtomsSecondOrder

namespace Work.Asymptotics.KhatE1Core.XtruncDev

open UpperHalfPlane

noncomputable section

/-- `q(z) = E(z)²`: the norm of `q = e^{2πiz}` is the square of the norm of `E = e^{πiz}`. -/
lemma norm_qParamFun_eq_norm_Ept_sq (z : ℍ) :
    ‖Work.Kernels.qParamFun z‖ = ‖Work.Residues.Ept z‖ ^ 2 := by
  have hsq : (Work.Residues.Ept z) ^ 2 = Work.Kernels.qParamFun z := by
    rw [Work.Residues.Ept, Work.Kernels.qParamFun, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [← hsq, norm_pow]

/-- `WT` is the `q²`-truncation of `W = θ₀₁⁴` in the variable `E = Ept z`: the sixth-order
expansion `WfunSixthH` of `KhatE1.ZAtomsSecondOrder` reads exactly
`‖W(z) - WT z‖ ≤ C ‖E(z)‖⁶`, and `‖E(z)‖⁶ = ‖q(z)‖³`. -/
theorem WTdev :
    Work.Asymptotics.KhatE1Core.Bound2
      (fun (_ : UpperHalfPlane) (z : UpperHalfPlane) =>
        Work.Kernels.WFun z - Work.Asymptotics.KhatE1Core.WT z) 0 3 := by
  obtain ⟨C, hC, hb⟩ := Work.Asymptotics.KhatE1.WfunSixthH
  refine Bound2.of_le_qz (K := 3) (C := C) (N := 0) (M := 0) hC le_rfl le_rfl ?_
  intro τ z t hF ht hz0 hz1 hzim
  have hz1' : (1 : ℝ) ≤ z.im := by
    have := hF.2; rw [hzim]; linarith
  have h := hb z hz1'
  have hW : Work.Kernels.WFun z - Work.Asymptotics.KhatE1Core.WT z
      = Work.Kernels.WFun z
        - (1 - 8 * Work.Residues.Ept z + 24 * (Work.Residues.Ept z) ^ 2
            - 32 * (Work.Residues.Ept z) ^ 3 + 24 * (Work.Residues.Ept z) ^ 4
            - 48 * (Work.Residues.Ept z) ^ 5) := by
    simp only [Work.Asymptotics.KhatE1Core.WT, Work.Asymptotics.KhatE1Core.Te]
  have hq3 : ‖Work.Kernels.qParamFun z‖ ^ (3 : ℕ) = ‖Work.Residues.Ept z‖ ^ 6 := by
    rw [norm_qParamFun_eq_norm_Ept_sq z]; ring
  simp only [Real.rpow_zero, mul_one, hW, hq3]
  exact h

end

end Work.Asymptotics.KhatE1Core.XtruncDev
