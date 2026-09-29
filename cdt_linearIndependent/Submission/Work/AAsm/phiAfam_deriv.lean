import Mathlib
import Submission.Work.AAsm.defs

namespace Work.AAsm

open Complex Metric
open Submission.CDTPlan

/-- Derivatives at `0` of the three Theorem-A maps `φ_A(z/10⁴)`, `φ_A(283z/500)`, `φ_A(z)`, in
terms of `deriv ψ_A 0`.  Since `φ_A = h ∘ ψ_A`, `ψ_A 0 = 0`, `h'(0) = -256` (`HauptFacts`) and
`ψ_A` is holomorphic near `0` (`PsiAFacts`), the chain rule gives `φ_A'(0) = -256·ψ_A'(0)`; the
linear rescalings of the argument multiply the derivative by their slopes, and the norms add the
factors `1/10⁴`, `283/500`, `1`. -/
theorem phiAfam_deriv (hP : Submission.CDTPlan.PsiAFacts) (hM : Submission.CDTPlan.HauptFacts) :
    deriv Submission.CDTPlan.phiA 0 = -256 * deriv Submission.CDTPlan.psiA 0 ∧
    ‖deriv (Submission.CDTPlan.phiAfam 0) 0‖ = (1 / 10000 : ℝ) * (256 * ‖deriv Submission.CDTPlan.psiA 0‖) ∧
    ‖deriv (Submission.CDTPlan.phiAfam 1) 0‖ = (283 / 500 : ℝ) * (256 * ‖deriv Submission.CDTPlan.psiA 0‖) ∧
    ‖deriv (Submission.CDTPlan.phiAfam 2) 0‖ = 256 * ‖deriv Submission.CDTPlan.psiA 0‖ := by
  obtain ⟨hPcont, hPdiff, hP0, hPbound, hPinj⟩ := hP
  obtain ⟨hMdiff, hMderiv, hMnz, k, hkdiff, hksq⟩ := hM
  -- `ψ_A` and `h` are holomorphic at the germ point `0`, so `φ_A = h ∘ ψ_A` is too.
  have hpsi_da : DifferentiableAt ℂ psiA 0 := hPdiff.differentiableAt (ball_mem_nhds _ zero_lt_one)
  have hhaupt_da : DifferentiableAt ℂ hauptH (psiA 0) := by
    rw [hP0]; exact hMdiff.differentiableAt (ball_mem_nhds _ zero_lt_one)
  have hphiA_da : DifferentiableAt ℂ phiA 0 := by
    show DifferentiableAt ℂ (hauptH ∘ psiA) 0
    exact hhaupt_da.comp 0 hpsi_da
  -- chain rule: `φ_A'(0) = h'(ψ_A 0)·ψ_A'(0) = h'(0)·ψ_A'(0) = -256·ψ_A'(0)`.
  have hphiA_deriv : deriv phiA 0 = -256 * deriv psiA 0 := by
    show deriv (hauptH ∘ psiA) 0 = -256 * deriv psiA 0
    rw [deriv_comp (x := (0:ℂ)) hhaupt_da hpsi_da, hP0, hMderiv]
  -- chain rule with the linear rescaling `z ↦ c·z`.
  have hcomp : ∀ c : ℂ, deriv (fun z : ℂ => phiA (c * z)) 0 = deriv phiA 0 * c := by
    intro c
    have hd : DifferentiableAt ℂ (fun z : ℂ => c * z) 0 := (differentiableAt_id (x := 0)).const_mul c
    have hder : deriv (fun z : ℂ => c * z) 0 = c := by
      rw [show (fun z : ℂ => c * z) = fun z => c * id z from rfl,
          deriv_const_mul c (differentiableAt_id)]
      simp
    rw [show (fun z : ℂ => phiA (c * z)) = phiA ∘ (fun z : ℂ => c * z) from rfl]
    rw [deriv_comp (x := (0:ℂ)) (by simpa using hphiA_da) hd, hder]
    simp
  refine ⟨hphiA_deriv, ?_, ?_, ?_⟩
  · -- `φ_A(z/10⁴)`
    have hderiv : deriv (phiAfam 0) 0 = deriv phiA 0 * (1/10000 : ℂ) := by
      rw [show phiAfam 0 = (fun z => phiA (z / 10000)) from rfl]
      rw [show (fun z : ℂ => phiA (z / 10000)) = (fun z => phiA (((10000:ℂ))⁻¹ * z)) from by
        funext z; rw [div_eq_inv_mul]]
      rw [hcomp ((10000:ℂ))⁻¹]
      norm_num
    rw [hderiv, norm_mul, hphiA_deriv, norm_mul]
    norm_num
    ring
  · -- `φ_A(283z/500)`
    have hderiv : deriv (phiAfam 1) 0 = deriv phiA 0 * (283/500 : ℂ) := by
      rw [show phiAfam 1 = (fun z => phiA (283 * z / 500)) from rfl]
      rw [show (fun z : ℂ => phiA (283 * z / 500)) = (fun z => phiA ((283/500:ℂ) * z)) from by
        funext z; rw [show (283 * z / 500) = ((283/500:ℂ) * z) from by ring]]
      rw [hcomp (283/500 : ℂ)]
    rw [hderiv, norm_mul, hphiA_deriv, norm_mul]
    norm_num
    ring
  · -- `φ_A`
    rw [show phiAfam 2 = phiA from rfl, hphiA_deriv, norm_mul]
    norm_num

end Work.AAsm
