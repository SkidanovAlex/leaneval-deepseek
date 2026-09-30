import Mathlib.Analysis.Fourier.ZMod

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Complex DirichletCharacter
open scoped Real
set_option autoImplicit false

namespace Commons.NumberTheory.DirichletCharacter

/-- Complex conjugation commutes with the standard additive character:
`conj (e a) = e (-a)` for `e = ZMod.stdAddChar`. -/
lemma stdAddChar_star {N : ℕ} [NeZero N] (a : ZMod N) :
    star (ZMod.stdAddChar a) = ZMod.stdAddChar (-a) := by
  have hR : 0 < ringChar (ZMod N) := by
    rw [ZMod.ringChar_zmod_n]
    exact NeZero.pos N
  rw [← starRingEnd_apply]
  rw [AddChar.starComp_apply hR (φ := ZMod.stdAddChar (N := N)) a]
  rw [AddChar.inv_mulShift]
  simp

/-- The conjugate of the Gauss sum of `χ` equals the sum over `k` of
`χ⁻¹ (-k) * e k`; this is the expansion of `conj (gaussSum χ e)` used to
identify it with the discrete Fourier transform of `χ`. -/
lemma star_gaussSum_eq_sum {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    star (gaussSum χ (ZMod.stdAddChar (N := N))) =
      ∑ k : ZMod N, χ⁻¹ (-k) * ZMod.stdAddChar k := by
  calc
    star (gaussSum χ (ZMod.stdAddChar (N := N)))
        = ∑ j : ZMod N, star (χ j * ZMod.stdAddChar j) := by
          simp [gaussSum, star_mul]
    _ = ∑ j : ZMod N, χ⁻¹ j * ZMod.stdAddChar (-j) := by
          simp [MulChar.star_apply', stdAddChar_star]
    _ = ∑ k : ZMod N, χ⁻¹ (-k) * ZMod.stdAddChar k := by
          simpa [neg_neg] using
            (Equiv.sum_comp (Equiv.neg (ZMod N))
              (fun k : ZMod N => χ⁻¹ (-k) * ZMod.stdAddChar k))

/-- Applying the discrete Fourier transform twice to `χ` and evaluating at `-1`
gives `N`. -/
lemma dft_dft_neg_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    ZMod.dft (ZMod.dft (χ : ZMod N → ℂ)) (-1) = (N : ℂ) := by
  rw [ZMod.dft_dft]
  simp [map_one]

/-- The Gauss sum `gaussSum χ stdAddChar` is the discrete Fourier transform of
`χ` evaluated at `-1`. -/
lemma gaussSum_eq_dft_neg_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    gaussSum χ (ZMod.stdAddChar (N := N)) = ZMod.dft (χ : ZMod N → ℂ) (-1) := by
  rw [DirichletCharacter.fourierTransform_eq_gaussSum_mulShift χ (-1)]
  congr 1
  ext j
  simp

/-- For a primitive character `χ` of modulus `N`, the Gauss sum against the standard
additive character has squared norm `N`: `‖τ(χ)‖² = N`. -/
theorem gaussSum_norm_sq_of_isPrimitive {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) :
    ‖gaussSum χ (ZMod.stdAddChar (N := N))‖ ^ 2 = (N : ℝ) := by
  classical
  let τ : ℂ := gaussSum χ (ZMod.stdAddChar (N := N))
  have hτ_mul_star : τ * star τ = (N : ℂ) := by
    have hddN : ZMod.dft (ZMod.dft (χ : ZMod N → ℂ)) (-1) = (N : ℂ) := dft_dft_neg_one χ
    have hdd_expand : ZMod.dft (ZMod.dft (χ : ZMod N → ℂ)) (-1) = τ * star τ := by
      calc
        ZMod.dft (ZMod.dft (χ : ZMod N → ℂ)) (-1)
            = ∑ j : ZMod N, ZMod.stdAddChar (-(j * (-1))) • ZMod.dft (χ : ZMod N → ℂ) j := by
                rw [ZMod.dft_apply (Φ := ZMod.dft (χ : ZMod N → ℂ)) (-1)]
        _ = ∑ j : ZMod N, ZMod.stdAddChar j * (χ⁻¹ (-j) * gaussSum χ (ZMod.stdAddChar (N := N))) := by
                simp_rw [DirichletCharacter.IsPrimitive.fourierTransform_eq_inv_mul_gaussSum hχ]
                congr 1
                ext j
                simp [smul_eq_mul, mul_comm, mul_left_comm]
        _ = (∑ j : ZMod N, ZMod.stdAddChar j * χ⁻¹ (-j)) * gaussSum χ (ZMod.stdAddChar (N := N)) := by
                simp [Finset.mul_sum, mul_comm, mul_left_comm]
        _ = gaussSum χ (ZMod.stdAddChar (N := N)) * star (gaussSum χ (ZMod.stdAddChar (N := N))) := by
                rw [mul_comm]
                congr 1
                rw [star_gaussSum_eq_sum]
                congr 1
                ext j
                ring
        _ = τ * star τ := by
                simp [τ]
    rw [← hdd_expand]
    exact hddN
  change ‖τ‖ ^ 2 = (N : ℝ)
  rw [← Complex.normSq_eq_norm_sq τ]
  have hc : (Complex.normSq τ : ℂ) = (N : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]
    simpa [mul_comm, τ] using hτ_mul_star
  exact_mod_cast hc

end Commons.NumberTheory.DirichletCharacter