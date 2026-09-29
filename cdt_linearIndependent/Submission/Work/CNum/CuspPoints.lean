import Mathlib
import Submission.Work.CNum.CpxSound
import Submission.Work.CNum.NrmSpec
import Submission.Work.CNum.C2_setup
import Submission.Work.CNum.exp_phi_eq
import Submission.Work.CNum.Wfun_exp
import Submission.Work.CNum.C2_mem
import Submission.Work.CNum.ratIvMem

/-!
# `Work.CNum.CuspPoints`

The two cusp images of the Theorem-C contour map `ψ_C` on the unit circle lie in the
certified boxes `ptCuspA`, `ptCuspB`.

With `c = 23/10`, `γ = gamR = cos α` and `α = alpR = arccos γ`, the two cusps of `ψ_C` lie at
`z = e^{±iα}`: there the radicand `Ra` vanishes, the principal square root is `0`, and

* `ψ_C (e^{iα}) = (3/4)(429/629 - (460/629) i)`,
* `ψ_C (e^{-iα}) = (3/4)(429/629 + (460/629) i)`,

using the exact half-angle values `cos(α/2) = 460/629` (`C2C`), `sin(α/2) = 429/629` (`C2σ`).
-/

namespace Work.CNum

open Complex

/-- `ψ_C = (3/4)·Wfun`, definitionally (from `√z = z^{1/2}`). -/
lemma psiC_eq_threequarters_Wfun (z : ℂ) : Submission.CDTPlan.psiC z = (3 / 4) * Wfun z := by
  unfold Submission.CDTPlan.psiC Submission.CDTPlan.lune Wfun Ra AR BR dR cR
  rw [Complex.sqrt]
  push_cast
  ring_nf

/-- The cusp point `429/629 - (460/629) i`. -/
noncomputable def zCuspA : ℂ := (429/629 : ℂ) + (-(460/629) : ℂ) * Complex.I
/-- The cusp point `429/629 + (460/629) i`. -/
noncomputable def zCuspB : ℂ := (429/629 : ℂ) + (460/629 : ℂ) * Complex.I

/-- At the cusp `θ = α` the radicand vanishes and `Wfun (e^{iα}) = -i·e^{iα/2}`. -/
lemma Wfun_cuspA : Wfun (Complex.exp (Complex.I * (alpR : ℂ))) =
    -(Complex.I * ((C2C : ℂ) + (C2σ : ℂ) * Complex.I)) := by
  have hw : Complex.exp (Complex.I * (((alpR / 2 : ℝ)) : ℂ)) =
      (C2C : ℂ) + (C2σ : ℂ) * Complex.I := by
    rw [mul_comm, Complex.exp_ofReal_mul_I, cos_half_alpR, sin_half_alpR]
  have hsub : Complex.exp (Complex.I * (alpR : ℂ)) - 1 =
      2 * Complex.I * (C2σ : ℂ) * ((C2C : ℂ) + (C2σ : ℂ) * Complex.I) := by
    rw [ExpPhi.exp_I_sub_one alpR, sin_half_alpR, hw]
  have hRa : Ra (Complex.exp (Complex.I * (alpR : ℂ))) = 0 := by
    rw [Ra_exp, cos_alpR]; simp
  rw [Wfun, hsub, hRa, Complex.sqrt_zero, add_zero]
  have h1 : (cR : ℂ) = (23/10 : ℂ) := by rw [cR]; norm_num
  have h2 : (C2σ : ℂ) = (429/629 : ℂ) := by rw [C2σ]; norm_num
  have hCC : (C2C : ℂ) = (460/629 : ℂ) := by rw [C2C]; norm_num
  have h3 : (dR : ℂ) = (429/50 : ℂ) := by norm_num [dR, cR]
  rw [h1, h2, hCC, h3]
  ring

/-- At the cusp `θ = -α` the radicand vanishes and `Wfun (e^{-iα}) = i·e^{-iα/2}`. -/
lemma Wfun_cuspB : Wfun (Complex.exp (Complex.I * ((2 * Real.pi - alpR : ℝ) : ℂ))) =
    Complex.I * ((C2C : ℂ) - (C2σ : ℂ) * Complex.I) := by
  have hwB : Complex.exp (Complex.I * ((((2 * Real.pi - alpR) / 2 : ℝ)) : ℂ)) =
      -((C2C : ℂ) - (C2σ : ℂ) * Complex.I) := by
    rw [show ((2 * Real.pi - alpR) / 2 : ℝ) = Real.pi - alpR / 2 by ring, mul_comm,
      Complex.exp_ofReal_mul_I, Real.cos_pi_sub, Real.sin_pi_sub, cos_half_alpR, sin_half_alpR]
    push_cast; ring
  have hsinB : Real.sin ((2 * Real.pi - alpR) / 2) = C2σ := by
    rw [show ((2 * Real.pi - alpR) / 2 : ℝ) = Real.pi - alpR / 2 by ring, Real.sin_pi_sub,
      sin_half_alpR]
  have hsub : Complex.exp (Complex.I * ((2 * Real.pi - alpR : ℝ) : ℂ)) - 1 =
      -(2 * Complex.I * (C2σ : ℂ) * ((C2C : ℂ) - (C2σ : ℂ) * Complex.I)) := by
    rw [ExpPhi.exp_I_sub_one (2 * Real.pi - alpR), hsinB, hwB]
    ring
  have hRa : Ra (Complex.exp (Complex.I * ((2 * Real.pi - alpR : ℝ) : ℂ))) = 0 := by
    rw [Ra_exp, show Real.cos (2 * Real.pi - alpR) = gamR by rw [Real.cos_two_pi_sub, cos_alpR]]
    simp
  rw [Wfun, hsub, hRa, Complex.sqrt_zero, add_zero]
  have h1 : (cR : ℂ) = (23/10 : ℂ) := by rw [cR]; norm_num
  have h2 : (C2σ : ℂ) = (429/629 : ℂ) := by rw [C2σ]; norm_num
  have hCC : (C2C : ℂ) = (460/629 : ℂ) := by rw [C2C]; norm_num
  have h3 : (dR : ℂ) = (429/50 : ℂ) := by norm_num [dR, cR]
  rw [h1, h2, hCC, h3]
  ring

/-- The value of `ψ_C` at the cusp `θ = α`. -/
lemma psiC_cuspA : Submission.CDTPlan.psiC (Complex.exp (Complex.I * (alpR : ℂ))) =
    zCuspA * (((3 : ℝ) / 4 : ℝ) : ℂ) := by
  rw [psiC_eq_threequarters_Wfun, Wfun_cuspA,
    show ((((3 : ℝ) / 4 : ℝ)) : ℂ) = (3 / 4 : ℂ) by norm_num]
  have h2 : (C2σ : ℂ) = (429/629 : ℂ) := by rw [C2σ]; norm_num
  have hCC : (C2C : ℂ) = (460/629 : ℂ) := by rw [C2C]; norm_num
  rw [h2, hCC]
  unfold zCuspA
  ring_nf
  rw [pow_two, Complex.I_mul_I]
  ring

/-- The value of `ψ_C` at the cusp `θ = 2π - α`. -/
lemma psiC_cuspB :
    Submission.CDTPlan.psiC (Complex.exp (Complex.I * (2 * (Real.pi : ℂ) - (alpR : ℂ)))) =
      zCuspB * (((3 : ℝ) / 4 : ℝ) : ℂ) := by
  rw [show (2 * (Real.pi : ℂ) - (alpR : ℂ)) = ((2 * Real.pi - alpR : ℝ) : ℂ) by
        push_cast; ring]
  rw [psiC_eq_threequarters_Wfun, Wfun_cuspB,
    show ((((3 : ℝ) / 4 : ℝ)) : ℂ) = (3 / 4 : ℂ) by norm_num]
  have h2 : (C2σ : ℂ) = (429/629 : ℂ) := by rw [C2σ]; norm_num
  have hCC : (C2C : ℂ) = (460/629 : ℂ) := by rw [C2C]; norm_num
  rw [h2, hCC]
  unfold zCuspB
  ring_nf
  rw [pow_two, Complex.I_mul_I]
  ring

/-- `zCuspA` lies in the box `ptCuspA`. -/
lemma mem_zCuspA : (⟨ratIv 429 629, ratIv (-460) 629⟩ : Cpx).Mem zCuspA := by
  refine ⟨?_, ?_⟩
  · show (ratIv 429 629).Mem _
    rw [show zCuspA.re = (429 : ℝ) / 629 by
      unfold zCuspA; norm_num [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]]
    exact ratIvMem 429 (by norm_num)
  · show (ratIv (-460) 629).Mem _
    rw [show zCuspA.im = -(460 : ℝ) / 629 by
      unfold zCuspA; norm_num [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]]
    have h := ratIvMem (-460) (by norm_num : (0 : ℕ) < 629)
    simpa using h

/-- `zCuspB` lies in the box `ptCuspB`. -/
lemma mem_zCuspB : (⟨ratIv 429 629, ratIv 460 629⟩ : Cpx).Mem zCuspB := by
  refine ⟨?_, ?_⟩
  · show (ratIv 429 629).Mem _
    rw [show zCuspB.re = (429 : ℝ) / 629 by
      unfold zCuspB; norm_num [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]]
    exact ratIvMem 429 (by norm_num)
  · show (ratIv 460 629).Mem _
    rw [show zCuspB.im = (460 : ℝ) / 629 by
      unfold zCuspB; norm_num [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]]
    exact ratIvMem 460 (by norm_num)

theorem CuspPoints : Work.CNum.Cpx.Mem Work.CNum.ptCuspA (Submission.CDTPlan.psiC (Complex.exp (Complex.I * (Work.CNum.alpR : ℂ)))) ∧ Work.CNum.Cpx.Mem Work.CNum.ptCuspB (Submission.CDTPlan.psiC (Complex.exp (Complex.I * (2 * (Real.pi : ℂ) - (Work.CNum.alpR : ℂ))))) := by
  refine ⟨?_, ?_⟩
  · rw [psiC_cuspA]
    unfold ptCuspA
    exact mem_mulr mem_zCuspA (ratIvMem 3 (by norm_num))
  · rw [psiC_cuspB]
    unfold ptCuspB
    exact mem_mulr mem_zCuspB (ratIvMem 3 (by norm_num))

end Work.CNum
