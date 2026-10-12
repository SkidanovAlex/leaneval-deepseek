import Mathlib.Tactic.Have
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.OneBodyKin.famSym_zero
import Submission.Work.OneBodyKin.kinFT_chiScale
import Submission.Work.OneBodyKin.kinFT_comp_sub
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.OneBodyKin.bsPair_const_eq`

The cross form `bsPair ℓ F u ψ = (2π)⁻³ ∫_p F(‖p‖)·Re[kinFT χ_u p · conj(kinFT (χ_u ψ) p)]`
(FS's `⟨χ_u, F(√−Δ)(χ_uψ)⟩`) at the **constant state** `ψ ≡ 1`:

    `bsPair ℓ F u 1 = symA ℓ F 0 · ℓ³`,

i.e. the off-diagonal companion of the unprojected family form, evaluated at the constant, is
`ℓ³` times the *anchored* (`u = 0`, `q = 0`) unprojected symbol `symA ℓ F 0`.  This is the
`u`-independence input of the mean-correction term of the projected family form
(`bsMean_bsPair_eq_symbol`): the mean term of FS's expansion is `m_u·bsPair ℓ F u ψ`, and for the
constant `ψ` the cross form reduces to the diagonal form `⟨χ_u, F(√−Δ)χ_u⟩`, which is
translation invariant.

## Computation

With `ψ ≡ 1` the second `kinFT` factor is the first one, so
`bsPair ℓ F u 1 = (2π)⁻³ ∫_p F(‖p‖)·‖kinFT χ_u p‖²`, and the whole content is

    `‖kinFT χ_u p‖² = ℓ⁶·profHat(ℓp)²`,

which is the two Fourier identities of the chapter (both independent of `u`):

* `kinFT_comp_sub` — translation: `kinFT (g(· − a)) p = e^{−i⟪p,a⟫}·kinFT g p`, whose modulus
  is `‖kinFT g p‖` (the phase has modulus one), so the shift `χ_u = χ_{u=0}(· − ℓu)` drops out;
* `kinFT_chiScale` — dilation: `kinFT (χ(·/ℓ)) p = ℓ³·profHat(ℓp)`.

`ℓ⁶ = ℓ³·ℓ³` and `∫_p F(‖p‖)·profHat(ℓp)²` is exactly the Haar-scaled form of `symA ℓ F 0`
(`famSym_zero.symA_zero`), which closes the identity.
-/

noncomputable section

open MeasureTheory

namespace Work.OneBodyKin

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

theorem bsPair_const_eq {ℓ : ℝ} (hℓ : 0 < ℓ) {F : ℝ → ℝ}
    (hFi : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => F ‖p‖))
    (u : EuclideanSpace ℝ (Fin 3)) :
    Work.OneBodyKin.bsPair ℓ F u (fun _ => (1 : ℝ)) = Work.OneBodyKin.symA ℓ F 0 * ℓ ^ 3 := by
  -- `χ_u` is the anchored window translated by `ℓ•u`
  have hW : (fun z : ℝ³ => (Work.BSKinetic.bsWin ℓ u z : ℂ))
      = (fun z : ℝ³ => (Submission.BoseGases.chiScale ℓ (z - ℓ • u) : ℂ)) := rfl
  -- the modulus of the Fourier transform of the window, squared
  have hnorm : ∀ p : ℝ³, ‖Submission.BoseGases.kinFT
      (fun z : ℝ³ => (Work.BSKinetic.bsWin ℓ u z : ℂ)) p‖ ^ 2
      = ℓ ^ 6 * (profHat (ℓ • p)) ^ 2 := by
    intro p
    rw [hW]
    change ‖Submission.BoseGases.kinFT
      (fun z : ℝ³ => (fun w : ℝ³ => (Submission.BoseGases.chiScale ℓ w : ℂ))
        (z - (ℓ • u))) p‖ ^ 2 = ℓ ^ 6 * (profHat (ℓ • p)) ^ 2
    rw [kinFT_comp_sub (fun w : ℝ³ => (Submission.BoseGases.chiScale ℓ w : ℂ)) (ℓ • u) p]
    rw [kinFT_chiScale (ℓ := ℓ) hℓ p]
    -- the phase `e^{-i⟪p,ℓu⟫}` has modulus one
    have hexp : ‖Complex.exp (-(Complex.I * ((inner ℝ p (ℓ • u) : ℝ) : ℂ)))‖ = 1 := by
      rw [Complex.norm_exp]
      have hre : (-(Complex.I * ((inner ℝ p (ℓ • u) : ℝ) : ℂ))).re = 0 := by simp
      rw [hre, Real.exp_zero]
    rw [norm_mul, hexp, one_mul]
    rw [← Complex.ofReal_pow ℓ 3]
    rw [Complex.sq_norm, Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_ofReal]
    ring
  -- step 1: `ψ = 1` makes the cross form diagonal
  have hpair : bsPair ℓ F u (fun _ => (1 : ℝ))
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, F ‖p‖ * ‖Submission.BoseGases.kinFT
          (fun z : ℝ³ => (Work.BSKinetic.bsWin ℓ u z : ℂ)) p‖ ^ 2 := by
    unfold bsPair
    congr 1
    refine MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ (fun p => ?_))
    have hfun : (fun z : ℝ³ => (Work.BSKinetic.bsWin ℓ u z : ℂ) * (((fun _ => (1:ℝ)) z : ℂ)))
        = (fun z : ℝ³ => (Work.BSKinetic.bsWin ℓ u z : ℂ)) := by
      funext z; simp
    rw [hfun]
    have hz : (Submission.BoseGases.kinFT (fun z : ℝ³ => (Work.BSKinetic.bsWin ℓ u z : ℂ)) p *
        star (Submission.BoseGases.kinFT (fun z : ℝ³ => (Work.BSKinetic.bsWin ℓ u z : ℂ)) p)).re
        = ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (Work.BSKinetic.bsWin ℓ u z : ℂ)) p‖ ^ 2 := by
      rw [← starRingEnd_apply, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    show F ‖p‖ * (Submission.BoseGases.kinFT (fun z : ℝ³ => (Work.BSKinetic.bsWin ℓ u z : ℂ)) p *
        star (Submission.BoseGases.kinFT (fun z : ℝ³ => (Work.BSKinetic.bsWin ℓ u z : ℂ)) p)).re
        = F ‖p‖ * ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (Work.BSKinetic.bsWin ℓ u z : ℂ)) p‖ ^ 2
    rw [hz]
  -- step 2: substitute the modulus-squared identity
  have hcongr : (∫ p : ℝ³, F ‖p‖ * ‖Submission.BoseGases.kinFT
        (fun z : ℝ³ => (Work.BSKinetic.bsWin ℓ u z : ℂ)) p‖ ^ 2)
      = ∫ p : ℝ³, F ‖p‖ * (ℓ ^ 6 * (profHat (ℓ • p)) ^ 2) := by
    refine MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ (fun p => ?_))
    simp only [hnorm p]
  -- step 3: pull the constant `ℓ⁶` out of the integral
  have hI : (∫ p : ℝ³, F ‖p‖ * (ℓ ^ 6 * (profHat (ℓ • p)) ^ 2))
      = ℓ ^ 6 * (∫ p : ℝ³, F ‖p‖ * (profHat (ℓ • p)) ^ 2) := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ (fun p => ?_))
    ring
  -- step 4: `∫_p F(‖p‖)profHat(ℓp)²` is the Haar-scaled anchored symbol
  rw [hpair, hcongr, hI, symA_zero (ℓ := ℓ) hℓ F]
  ring

end Work.OneBodyKin
