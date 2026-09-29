import Mathlib
import Submission.Work.CPsi.psiC_deps

/-!
# `ψ_C'(0) = -1287/2516`

The contour map `ψ_C = -(3/4)·lune (23/10)` of Calegari--Dimitrov--Tang
(arXiv:2408.15403, §"contour choiceC") fixes the origin and its derivative there is the
conformal radius of the lune: `lune(23/10,·)'(0) = (c²-1)/(c²+1) = 429/629`, whence
`ψ_C'(0) = -(3/4)·429/629 = -1287/2516`.

The proof works with the explicit algebraic model `gobL` of the lune map (from
`Submission.Work.CPsi.psiC_base`), which is `lune (23/10)` after unfolding the numerical
constants.  All the derivative work is on `gobL`; only the last step renames it back to `ψ_C`.
-/

namespace Work.CPsi

open Submission.CDTPlan Complex

theorem psiC_deriv_zero : deriv Submission.CDTPlan.psiC 0 = -(1287 / 2516) := by
  -- `R(0) = B²` lies in the slit plane, so the principal square root is holomorphic there
  have hmem : gobR 0 ∈ Complex.slitPlane := by
    rw [gobR_zero, Complex.slitPlane]
    exact Or.inl (by simp only [gB, gBr]; norm_num)
  -- `(B²)^{-1/2} = B^{-1}`
  have hkey : (gB ^ 2) ^ (1 / 2 - 1 : ℂ) = (gB)⁻¹ := by
    rw [Complex.cpow_sub (1 / 2) 1 (pow_ne_zero 2 gB_ne_zero), cpow_half_gB_sq,
      Complex.cpow_one]
    field_simp
  -- the radicand is a quadratic polynomial: `gobR' 0 = 2B² - 16c²`
  have hR : HasDerivAt gobR (2 * gB ^ 2 - 16 * gC2) 0 := by
    unfold gobR
    have hb : HasDerivAt (fun z : ℂ => (1 + z) ^ 2) 2 0 := by
      have h : HasDerivAt (fun z : ℂ => 1 + z) 1 0 :=
        (hasDerivAt_id (0 : ℂ)).const_add (1 : ℂ)
      have h2 := h.pow 2
      rw [show ((2 : ℕ) : ℂ) * (1 + 0) ^ (2 - 1) * 1 = 2 by norm_num] at h2
      exact h2
    have h1 := hb.const_mul (gB ^ 2)
    have h2 : HasDerivAt (fun y : ℂ => 16 * gC2 * y) (16 * gC2) 0 := by
      have hh := (hasDerivAt_id (0 : ℂ)).const_mul (16 * gC2)
      rw [mul_one] at hh
      exact hh
    exact (h1.sub h2).congr_deriv (by ring)
  -- derivative of the principal square root of `gobR`
  have hS : HasDerivAt (fun z : ℂ => (gobR z) ^ (1 / 2 : ℂ))
      ((1 / 2 : ℂ) * (gB)⁻¹ * (2 * gB ^ 2 - 16 * gC2)) 0 := by
    have h0 := hR.cpow_const (c := (1 / 2 : ℂ)) hmem
    rw [gobR_zero, hkey] at h0
    exact h0
  -- numerator of the lune map
  have hlin : HasDerivAt (fun z : ℂ => gB * z - gB) gB 0 := by
    have hh := (hasDerivAt_id (0 : ℂ)).const_mul gB
    rw [mul_one] at hh
    exact hh.sub_const gB
  have hN := hlin.add hS
  -- the lune map itself
  have hgobL : HasDerivAt gobL
      ((gB + ((1 / 2 : ℂ) * (gB)⁻¹ * (2 * gB ^ 2 - 16 * gC2))) / (2 * gC)) 0 := by
    have h := hN.div_const (2 * gC)
    exact h
  -- `ψ_C = -(3/4)·lune (23/10)` and `lune (23/10) = gobL`
  have hpsi : HasDerivAt Submission.CDTPlan.psiC
      (-(3 / 4) * ((gB + ((1 / 2 : ℂ) * (gB)⁻¹ * (2 * gB ^ 2 - 16 * gC2))) / (2 * gC)))
      0 := by
    have h := hgobL.const_mul (-(3 / 4))
    have he : Submission.CDTPlan.psiC = fun z => -(3 / 4) * gobL z := by
      funext z
      simp only [Submission.CDTPlan.psiC]
      rw [lune_eq]
    rw [he]
    exact h
  rw [hpsi.deriv]
  simp only [gB, gC, gC2, gBr, gCr]
  push_cast
  norm_num

end Work.CPsi
