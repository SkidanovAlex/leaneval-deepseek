import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB2.Polar.fsT_parallelogram
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB2.DvApriori

set_option maxHeartbeats 4000000

open MeasureTheory

/-!
# Integrability of the polarised one-body spectral integrand

The polarised `p`-integrand of the one-body spectral word is

`p ↦ [‖p‖ − c]₊² · Re( star(kinFT(χ₀Q₀f)(p)) · kinFT(χ₀Q₀g)(p) )`,

with `χ₀ = bsWin ℓ 0` the box window and `Q₀ = Qfree ℓ 0` the box mean-free projection.

Each of the two factors is the `p`-convention Fourier transform of a **smooth compactly supported**
state (the window `χ₀` is smooth and compactly supported, and `Q₀h = h − const` is smooth as soon as
`h` is), so each of the two diagonal integrands
`p ↦ [‖p‖ − c]₊²·‖kinFT(χ₀Q₀h)(p)‖²` is integrable (`Work.BSKinetic.Decomp`'s
`integrable_fsKinCoeff_mul_bsPsi_sq`, here re-exported in the form
`Work.BoseFixB2.Polar.FsTAux.integrable_fsKinCoeff_kinFT_sq`).

The cross term is then controlled by the **polarisation identity**
`Re(star z · w) = (‖z+w‖² − ‖z−w‖²)/4`, the two combinations `z ± w` being — by linearity of
`kinFT` (`Work.BoseFixB2.Polar.FsTAux.kinFT_add`/`kinFT_sub`) — the Fourier transforms of the
windowed states `χ₀Q₀(f±g)`, hence again covered by the diagonal statement.
-/

/-- **Polarisation of a hermitian product**: for complex numbers `z, w`,
`Re(star z · w) = (‖z + w‖² − ‖z − w‖²)/4`. -/
lemma re_star_mul_eq (z w : ℂ) : (star z * w).re = (‖z + w‖ ^ 2 - ‖z - w‖ ^ 2) / 4 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.star_def,
    Complex.conj_re, Complex.conj_im]
  ring

/-- The polarised `p`-integrand of the one-body spectral word is integrable: the two factors
are the windowed Fourier transforms of the smooth compactly supported states `χ₀Q₀f`, `χ₀Q₀g`,
so each `∫_p [‖p‖−c]₊²‖·‖²` is finite. -/
theorem integrable_fsKinCoeff_polar {ℓ : ℝ} (hℓ : 0 < ℓ) {c : ℝ}
    {f g : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.fsKinCoeff c ‖p‖ *
          (star (Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) =>
              (Work.BSKinetic.bsWin ℓ 0 z : ℂ) * (Work.BoseKinLoc.Qfree ℓ 0 f z : ℂ)) p)
            * Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) =>
              (Work.BSKinetic.bsWin ℓ 0 z : ℂ) * (Work.BoseKinLoc.Qfree ℓ 0 g z : ℂ)) p).re)
      MeasureTheory.volume := by
  have hℓ' : ℓ ≠ 0 := ne_of_gt hℓ
  -- ## Smoothness and compact support of the window `χ₀ = bsWin ℓ 0`
  have hwin_d : ContDiff ℝ (⊤ : ℕ∞) (Work.BSKinetic.bsWin ℓ 0) := by
    have h' : Work.BSKinetic.bsWin ℓ 0 = fun z : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.chiScale ℓ (z - ℓ • (0 : EuclideanSpace ℝ (Fin 3))) := rfl
    rw [h']
    exact (Submission.BoseGases.chiScale_contDiff hℓ').comp (contDiff_id.sub contDiff_const)
  have hwin_c : HasCompactSupport (Work.BSKinetic.bsWin ℓ 0) :=
    Work.BSKinetic.bsWin_hasCompactSupport hℓ 0
  -- ## Smoothness of the mean-free states `Q₀h = h − ⨍`
  have hQf : ContDiff ℝ (⊤ : ℕ∞) (Work.BoseKinLoc.Qfree ℓ 0 f) := by
    have h' : Work.BoseKinLoc.Qfree ℓ 0 f = fun z : EuclideanSpace ℝ (Fin 3) =>
        f z - Work.BSKinetic.bsMean ℓ 0 f := rfl
    rw [h']
    exact hf.sub contDiff_const
  have hQg : ContDiff ℝ (⊤ : ℕ∞) (Work.BoseKinLoc.Qfree ℓ 0 g) := by
    have h' : Work.BoseKinLoc.Qfree ℓ 0 g = fun z : EuclideanSpace ℝ (Fin 3) =>
        g z - Work.BSKinetic.bsMean ℓ 0 g := rfl
    rw [h']
    exact hg.sub contDiff_const
  -- ## The two windowed states `χ₀Q₀(f ± g)` (real valued, smooth, compactly supported)
  set P : EuclideanSpace ℝ (Fin 3) → ℝ := fun z =>
    Work.BSKinetic.bsWin ℓ 0 z * (Work.BoseKinLoc.Qfree ℓ 0 f z + Work.BoseKinLoc.Qfree ℓ 0 g z)
    with hP
  set M : EuclideanSpace ℝ (Fin 3) → ℝ := fun z =>
    Work.BSKinetic.bsWin ℓ 0 z * (Work.BoseKinLoc.Qfree ℓ 0 f z - Work.BoseKinLoc.Qfree ℓ 0 g z)
    with hM
  have hPd : ContDiff ℝ (⊤ : ℕ∞) P := by
    rw [hP]; exact hwin_d.mul (hQf.add hQg)
  have hPc : HasCompactSupport P := by
    rw [hP]; exact hwin_c.mul_right
  have hMd : ContDiff ℝ (⊤ : ℕ∞) M := by
    rw [hM]; exact hwin_d.mul (hQf.sub hQg)
  have hMc : HasCompactSupport M := by
    rw [hM]; exact hwin_c.mul_right
  -- ## Integrability of the two diagonal `p`-integrands
  have hIntP := Work.BoseFixB2.Polar.FsTAux.integrable_fsKinCoeff_kinFT_sq (c := c) hPd hPc
  have hIntM := Work.BoseFixB2.Polar.FsTAux.integrable_fsKinCoeff_kinFT_sq (c := c) hMd hMc
  -- ## The complex windowed states are integrable (continuous, compactly supported)
  have hUcs : HasCompactSupport (fun z : EuclideanSpace ℝ (Fin 3) =>
      ((Work.BSKinetic.bsWin ℓ 0 z : ℝ) : ℂ)) :=
    hwin_c.comp_left Complex.ofReal_zero
  have hIntUf : Integrable (fun z : EuclideanSpace ℝ (Fin 3) =>
      (Work.BSKinetic.bsWin ℓ 0 z : ℂ) * (Work.BoseKinLoc.Qfree ℓ 0 f z : ℂ)) :=
    ((Complex.continuous_ofReal.comp hwin_d.continuous).mul
      (Complex.continuous_ofReal.comp hQf.continuous)).integrable_of_hasCompactSupport
      hUcs.mul_right
  have hIntUg : Integrable (fun z : EuclideanSpace ℝ (Fin 3) =>
      (Work.BSKinetic.bsWin ℓ 0 z : ℂ) * (Work.BoseKinLoc.Qfree ℓ 0 g z : ℂ)) :=
    ((Complex.continuous_ofReal.comp hwin_d.continuous).mul
      (Complex.continuous_ofReal.comp hQg.continuous)).integrable_of_hasCompactSupport
      hUcs.mul_right
  -- ## Linearity of `kinFT` identifies the two combinations
  have hplus : ∀ p : EuclideanSpace ℝ (Fin 3),
      Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) => (P z : ℂ)) p
        = Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) =>
              (Work.BSKinetic.bsWin ℓ 0 z : ℂ) * (Work.BoseKinLoc.Qfree ℓ 0 f z : ℂ)) p
          + Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) =>
              (Work.BSKinetic.bsWin ℓ 0 z : ℂ) * (Work.BoseKinLoc.Qfree ℓ 0 g z : ℂ)) p := by
    intro p
    have hfun : (fun z : EuclideanSpace ℝ (Fin 3) => (P z : ℂ))
        = fun z : EuclideanSpace ℝ (Fin 3) =>
            (Work.BSKinetic.bsWin ℓ 0 z : ℂ) * (Work.BoseKinLoc.Qfree ℓ 0 f z : ℂ)
            + (Work.BSKinetic.bsWin ℓ 0 z : ℂ) * (Work.BoseKinLoc.Qfree ℓ 0 g z : ℂ) := by
      funext z
      rw [hP]
      push_cast
      ring
    rw [hfun]
    exact Work.BoseFixB2.Polar.FsTAux.kinFT_add hIntUf hIntUg p
  have hminus : ∀ p : EuclideanSpace ℝ (Fin 3),
      Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) => (M z : ℂ)) p
        = Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) =>
              (Work.BSKinetic.bsWin ℓ 0 z : ℂ) * (Work.BoseKinLoc.Qfree ℓ 0 f z : ℂ)) p
          - Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) =>
              (Work.BSKinetic.bsWin ℓ 0 z : ℂ) * (Work.BoseKinLoc.Qfree ℓ 0 g z : ℂ)) p := by
    intro p
    have hfun : (fun z : EuclideanSpace ℝ (Fin 3) => (M z : ℂ))
        = fun z : EuclideanSpace ℝ (Fin 3) =>
            (Work.BSKinetic.bsWin ℓ 0 z : ℂ) * (Work.BoseKinLoc.Qfree ℓ 0 f z : ℂ)
            - (Work.BSKinetic.bsWin ℓ 0 z : ℂ) * (Work.BoseKinLoc.Qfree ℓ 0 g z : ℂ) := by
      funext z
      rw [hM]
      push_cast
      ring
    rw [hfun]
    exact Work.BoseFixB2.Polar.FsTAux.kinFT_sub hIntUf hIntUg p
  -- ## The pointwise polarisation identity
  have hkey : ∀ p : EuclideanSpace ℝ (Fin 3),
      Submission.BoseGases.fsKinCoeff c ‖p‖ *
        (star (Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) =>
            (Work.BSKinetic.bsWin ℓ 0 z : ℂ) * (Work.BoseKinLoc.Qfree ℓ 0 f z : ℂ)) p)
          * Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) =>
            (Work.BSKinetic.bsWin ℓ 0 z : ℂ) * (Work.BoseKinLoc.Qfree ℓ 0 g z : ℂ)) p).re
      = (1 / 4) * (Submission.BoseGases.fsKinCoeff c ‖p‖ *
            ‖Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) => (P z : ℂ)) p‖ ^ 2
          - Submission.BoseGases.fsKinCoeff c ‖p‖ *
            ‖Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) => (M z : ℂ))
              p‖ ^ 2) := by
    intro p
    rw [hplus p, hminus p]
    rw [re_star_mul_eq]
    ring
  -- ## Assembly
  refine ((hIntP.sub hIntM).const_mul (1 / 4)).congr
    (Filter.Eventually.of_forall (fun p => (hkey p).symm))

end Work.BoseFixB2.DvApriori
