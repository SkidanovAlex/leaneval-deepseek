/-
# The coincidence set of the CKMRV middle range

For `τ ∈ 𝒟` and `z = it` on the imaginary axis with `j τ = j z`, the two points are related by
`z = τ` or `z = S τ`.  This is what makes the coincidence set of the middle-range estimate
`Work.Asymptotics.Kaxis_local_middle` the union of the two curves `z = τ`, `z = S τ`, on which the
*cleared* kernel `KfunClear` vanishes (`Work.Residues.KPlusClear_diag`,
`Work.Asymptotics.KClear_S_vanishing`).

The proof is the combination of the classical Hauptmodul property of `j`
(`Work.Asymptotics.jInvariantFun_eq_smul_of_eq`), the two orbit statements
`Work.Asymptotics.orbit_imagAxis_of_mem_DomainD` and
`Work.Asymptotics.eq_one_or_neg_one_or_S_of_smul_imagAxis`.
-/
import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.Theorem31
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Asymptotics.orbit_imagAxis_of_mem_DomainD
import Submission.Work.Asymptotics.eq_one_or_neg_one_or_S_of_smul_imagAxis
import Submission.Work.Asymptotics.jInvariantFun_eq_smul_of_eq

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped Topology MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Asymptotics

open Work.Kernels

/-- A point of the imaginary axis is `i` times its imaginary part. -/
lemma eq_imagAxis_of_re_eq_zero {z : ℍ} (hz : (z : ℂ).re = 0) :
    z = imagAxis z.im z.im_pos := by
  apply UpperHalfPlane.ext
  show (z : ℂ) = (z.im : ℂ) * Complex.I
  have h := Complex.re_add_im (z : ℂ)
  rw [hz, UpperHalfPlane.coe_im] at h
  rw [← h]
  simp

/-- **The coincidence set on the middle range.**  If `τ ∈ 𝒟`, `z` lies on the imaginary axis and
`j τ = j z`, then `z = τ` or `z = S τ`. -/
theorem eq_or_eq_S_of_re_eq_zero {τ z : ℍ} (hτ : τ ∈ DomainD) (hz : (z : ℂ).re = 0)
    (h : jInvariantFun τ = jInvariantFun z) : z = τ ∨ z = ModularGroup.S • τ := by
  -- the two points are conjugate under `SL(2,ℤ)`
  obtain ⟨γ, hγ⟩ := jInvariantFun_eq_smul_of_eq h
  have hzγ : z = γ⁻¹ • τ := by rw [← hγ, inv_smul_smul]
  -- hence `τ` has real part `0`
  have hτre : τ.re = 0 := by
    refine orbit_imagAxis_of_mem_DomainD τ hτ γ⁻¹ ?_
    rw [← hzγ]
    exact hz
  have hτ' : τ = imagAxis τ.im τ.im_pos := eq_imagAxis_of_re_eq_zero hτre
  have hz' : z = imagAxis z.im z.im_pos := eq_imagAxis_of_re_eq_zero hz
  -- the stabiliser classification
  have hsz : γ⁻¹ • imagAxis τ.im τ.im_pos = imagAxis z.im z.im_pos := by
    rw [← hτ', ← hz', hzγ]
  rcases eq_one_or_neg_one_or_S_of_smul_imagAxis τ.im_pos z.im_pos hsz with h1 | h1 | h1 | h1
  · left
    rw [hzγ, h1]; simp
  · left
    rw [hzγ, h1]
    simpa using ModularGroup.SL_neg_smul (g := (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) τ
  · right
    rw [hzγ, h1]
  · right
    rw [hzγ, h1,
      show (-(ModularGroup.S) : Matrix.SpecialLinearGroup (Fin 2) ℤ)
        = (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) * ModularGroup.S from (neg_one_mul _).symm,
      mul_smul]
    simpa using ModularGroup.SL_neg_smul (g := (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))
      (ModularGroup.S • τ)

end Work.Asymptotics
