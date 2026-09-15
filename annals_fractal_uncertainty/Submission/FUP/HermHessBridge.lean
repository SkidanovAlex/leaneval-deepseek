import Submission.FUP.KohnMorrey

open MeasureTheory
open scoped BigOperators ContDiff
set_option autoImplicit false
variable {d : ℕ}

/-!
# Towards the bridge between the Hermitian and the real Hessian

This module collects the (self-contained) calculus lemmas needed to identify the Hermitian pairing
`∑_{j,k} Re((∂_j∂̄_kφ)(z) w_j conj(w_k))` of the Kohn--Morrey layer with the real Hessian form
`(D²φ(z))[w,w] + (D²φ(z))[Iw,Iw]` used in `Submission.FUP.DbarDbarPos`.

The full bridge (`four_hermHess` and `hermHess_pairing`, described in `ROADMAP.md`) is not yet
formalised: the algebraic step
`4 ∂_j∂̄_kφ(z) = (∂²_{x_jx_k} + ∂²_{y_jy_k})φ(z) + i(∂²_{x_jy_k} - ∂²_{y_jx_k})φ(z)`
requires threading the eta-expanded/eta-reduced forms of `fun w => fderiv ℝ (phiC φ) w v` through
`fderiv_partialZbar_apply`.
-/

namespace Submission.FUP

/-- The mixed second directional derivative of a `C²` function, in terms of `iteratedFDeriv`. -/
lemma fderiv_fderiv_eq_iteratedFDeriv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {h : (Fin d → ℂ) → F} (hh : ContDiff ℝ 2 h)
    (z a b : (Fin d → ℂ)) :
    fderiv ℝ (fun w => fderiv ℝ h w a) z b = (iteratedFDeriv ℝ 2 h z) ![b, a] := by
  rw [iteratedFDeriv_two_apply]
  have hF : DifferentiableAt ℝ (fderiv ℝ h) z :=
    (hh.fderiv_right (m := 1) (by norm_num)).contDiffAt.differentiableAt (by norm_num)
  rw [fderiv_clm_apply (c := fderiv ℝ h) (u := fun _ : (Fin d → ℂ) => a) (x := z) hF
    (differentiableAt_const a)]
  simp

/-- The chain rule for the complexification of a real-valued function. -/
lemma fderiv_ofReal_comp {g : (Fin d → ℂ) → ℝ} {z : (Fin d → ℂ)}
    (hg : DifferentiableAt ℝ g z) :
    fderiv ℝ (fun w => ((g w : ℝ) : ℂ)) z = Complex.ofRealCLM.comp (fderiv ℝ g z) := by
  have h := Complex.ofRealCLM.hasFDerivAt.comp z hg.hasFDerivAt
  have h2 : fderiv ℝ (fun w => ((g w : ℝ) : ℂ)) z = Complex.ofRealCLM.comp (fderiv ℝ g z) := by
    rw [show (fun w => ((g w : ℝ) : ℂ)) = Complex.ofRealCLM ∘ g from rfl]
    exact h.fderiv
  exact h2

/-- The mixed second derivative of the complexification of a real-valued `C²` function. -/
lemma fderiv_fderiv_phiC_eq {φ : (Fin d → ℂ) → ℝ} (hφ : ContDiff ℝ 2 φ)
    (z u v : (Fin d → ℂ)) :
    fderiv ℝ (fun w => fderiv ℝ (phiC φ) w v) z u
      = (((iteratedFDeriv ℝ 2 φ z) ![u, v] : ℝ) : ℂ) := by
  have h1 : (fun w => fderiv ℝ (phiC φ) w v) = fun w => ((fderiv ℝ φ w v : ℝ) : ℂ) := by
    funext w
    have hw : DifferentiableAt ℝ φ w :=
      (hφ.contDiffAt (x := w)).differentiableAt (by norm_num)
    change (fderiv ℝ (fun y => ((φ y : ℝ) : ℂ)) w) v = ((fderiv ℝ φ w v : ℝ) : ℂ)
    rw [fderiv_ofReal_comp hw]
    rfl
  rw [h1]
  have h2 : fderiv ℝ (fun w => ((fderiv ℝ φ w v : ℝ) : ℂ)) z u
      = (((fderiv ℝ (fun w => fderiv ℝ φ w v) z u : ℝ)) : ℂ) := by
    have hg : DifferentiableAt ℝ (fun w => fderiv ℝ φ w v) z :=
      ((hφ.fderiv_right (m := 1) (by norm_num)).contDiffAt.differentiableAt
        (by norm_num)).clm_apply (differentiableAt_const v)
    rw [fderiv_ofReal_comp (g := fun w => fderiv ℝ φ w v) hg]
    rfl
  rw [h2]
  congr 1
  exact fderiv_fderiv_eq_iteratedFDeriv hφ z v u

/-- `Re((P + iQ) a) = P Re a - Q Im a` for real `P Q`. -/
lemma re_mul_ofReal_add_I_mul (P Q : ℝ) (a : ℂ) :
    ((((P : ℂ) + Complex.I * ((Q : ℂ))) * a).re) = P * a.re - Q * a.im := by
  simp only [add_mul, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
    sub_zero, zero_add]
  ring

lemma four_hermHess {φ : (Fin d → ℂ) → ℝ} (hφ : ContDiff ℝ 2 φ) (j k : Fin d)
    (z : (Fin d → ℂ)) :
    (4 : ℂ) * hermHess j k φ z
      = ((((iteratedFDeriv ℝ 2 φ z) ![Pi.single j 1, Pi.single k 1]
          + (iteratedFDeriv ℝ 2 φ z) ![Pi.single j Complex.I, Pi.single k Complex.I] : ℝ)) : ℂ)
        + Complex.I * ((((iteratedFDeriv ℝ 2 φ z) ![Pi.single j 1, Pi.single k Complex.I]
          - (iteratedFDeriv ℝ 2 φ z) ![Pi.single j Complex.I, Pi.single k 1] : ℝ)) : ℂ) := by
  have hψ : ContDiff ℝ 2 (phiC φ) := contDiff_phiC hφ
  have hZ : hermHess j k φ z
      = ((fderiv ℝ (fun w => partialZbar k (phiC φ) w) z (Pi.single j 1))
          - Complex.I * (fderiv ℝ (fun w => partialZbar k (phiC φ) w) z
            (Pi.single j Complex.I))) / 2 := by
    rw [hermHess, partialZ]
    rfl
  have hA := fderiv_partialZbar_apply hψ k z (Pi.single j 1)
  have hB := fderiv_partialZbar_apply hψ k z (Pi.single j Complex.I)
  rw [hZ, hA, hB,
    fderiv_fderiv_phiC_eq hφ z (Pi.single j 1) (Pi.single k 1),
    fderiv_fderiv_phiC_eq hφ z (Pi.single j 1) (Pi.single k Complex.I),
    fderiv_fderiv_phiC_eq hφ z (Pi.single j Complex.I) (Pi.single k 1),
    fderiv_fderiv_phiC_eq hφ z (Pi.single j Complex.I) (Pi.single k Complex.I)]
  push_cast
  ring_nf
  rw [show Complex.I ^ 2 = (-1 : ℂ) from by rw [pow_two, Complex.I_mul_I]]
  ring

/-- The Hermitian pairing of `∂∂̄φ` equals `(1/4)` of the real Hessian form. -/
theorem hermHess_pairing {φ : (Fin d → ℂ) → ℝ} (hφ : ContDiff ℝ 2 φ)
    (z w : (Fin d → ℂ)) :
    (∑ j, ∑ k, (hermHess j k φ z * w j * star (w k)).re)
      = (1 / 4) * ((iteratedFDeriv ℝ 2 φ z) ![w, w]
          + (iteratedFDeriv ℝ 2 φ z) ![Complex.I • w, Complex.I • w]) := by
  rw [Commons.Analysis.Calculus.realHessian_expansion_corrected]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  set P : ℝ := (iteratedFDeriv ℝ 2 φ z) ![Pi.single j 1, Pi.single k 1]
      + (iteratedFDeriv ℝ 2 φ z) ![Pi.single j Complex.I, Pi.single k Complex.I] with hP
  set Q : ℝ := (iteratedFDeriv ℝ 2 φ z) ![Pi.single j 1, Pi.single k Complex.I]
      - (iteratedFDeriv ℝ 2 φ z) ![Pi.single j Complex.I, Pi.single k 1] with hQ
  have h4 := four_hermHess hφ j k z
  rw [← hP, ← hQ] at h4
  push_cast at h4
  have h2 : (4 : ℂ) * (hermHess j k φ z * w j * star (w k))
      = ((P : ℂ) + Complex.I * (Q : ℂ)) * (w j * star (w k)) := by
    rw [← h4]
    ring
  have h3 : ((4 : ℂ) * (hermHess j k φ z * w j * star (w k))).re
      = 4 * (hermHess j k φ z * w j * star (w k)).re := by
    rw [Complex.mul_re]
    norm_num
  rw [h2, re_mul_ofReal_add_I_mul] at h3
  linarith


/-- **The Kohn--Morrey estimate from the pointwise Hessian bound.**
This is the form in which the estimate is applied: the hypothesis is exactly the pointwise part of
`dbarDbarPos_of_hessian`. -/
theorem kohn_morrey_estimate_of_hessian {u : (Fin d → ℂ) → (Fin d → ℂ)} {φ : (Fin d → ℂ) → ℝ}
    {κ : (Fin d → ℂ) → ℝ}
    (hu : ∀ j, ContDiff ℝ 2 (fComp u j)) (hφ : ContDiff ℝ 2 φ)
    (hsu : ∀ j, HasCompactSupport (fComp u j))
    (hκc : Continuous κ)
    (hhess : ∀ z (w : Fin d → ℂ), 4 * (κ z * (∑ j, ‖w j‖ ^ 2))
      ≤ (iteratedFDeriv ℝ 2 φ z) ![w, w]
        + (iteratedFDeriv ℝ 2 φ z) ![Complex.I • w, Complex.I • w]) :
    (∫ z, κ z * (∑ j, ‖u z j‖ ^ 2) * Real.exp (-(φ z)))
      ≤ (∫ z, ((1 / 2 : ℝ) * ∑ j, ∑ k, ‖dbComp u k j z - dbComp u j k z‖ ^ 2)
            * Real.exp (-(φ z)))
        + (∫ z, (‖∑ j, covComp u φ j z‖ ^ 2) * Real.exp (-(φ z))) := by
  refine kohn_morrey_estimate hu hφ hsu hκc fun z w => ?_
  have h := hermHess_pairing hφ z w
  have h2 := hhess z w
  linarith [h, h2]

end Submission.FUP
