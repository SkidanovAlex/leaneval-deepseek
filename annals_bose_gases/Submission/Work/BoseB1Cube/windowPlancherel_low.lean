import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.gradient_plancherel_of_contDiff_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The windowed Plancherel identity at `C¹` regularity

`Work.BoseB1Cube.windowPlancherel_low`: for a `C¹` window `W` with
`tsupport W ⊆ acube a` and an arbitrary `C¹` function `ψ`,

    (2π)⁻³ ∫_p ‖p‖²‖kinFT (Wψ) p‖²
      = ∫_{acube a} ∑_k (∂_k (Wψ))² .

This is the low-regularity (`C¹`) version of the companion identity
`Work.SmallBoxTBWord.windowPlancherel` (which requires `C^∞` data): the only
regularity the identity needs is exactly enough to run Plancherel for each of
the three partial derivatives, so the `C¹` gradient Plancherel
`Work.BoseFixB1S.gradient_plancherel_of_contDiff_one` suffices.

The proof: the product `Wψ` is `C¹` with compact support (`hWcs.mul_right`; no
support hypothesis on `ψ` is needed), so gradient Plancherel applies to it.  What
remains is bookkeeping:

* `(W z : ℂ) * (ψ z : ℂ) = ((W z * ψ z : ℝ) : ℂ)`, so the Fourier sides agree;
* `∑_k (∂_k f z)² = ‖gradient f z‖²` (`inner_gradient_left` +
  `sum_inner_kcStdBasis_sq`);
* `Wψ` vanishes in a *neighbourhood* of every point outside `acube a`
  (`tsupport W ⊆ acube a` is closed and `tsupport (Wψ) ⊆ tsupport W`), so
  `fderiv ℝ (Wψ) z = 0` there and the integrand vanishes off the cube, whence the
  integral over `acube a` equals the integral over `ℝ³`.

None of this uses `0 < a`; the hypothesis is carried because the caller states the
identity at a genuine box.
-/

set_option linter.unusedVariables false

namespace Work.BoseB1Cube

open MeasureTheory

/-- `kinFT` only sees the function pointwise. -/
private lemma kinFT_congr {g h : EuclideanSpace ℝ (Fin 3) → ℂ} (hgh : ∀ z, g z = h z)
    (p : EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.kinFT g p = Submission.BoseGases.kinFT h p := by
  simp only [Submission.BoseGases.kinFT]
  apply integral_congr_ae
  filter_upwards with y
  rw [hgh y]

theorem windowPlancherel_low {a : ℝ} {W ψ : EuclideanSpace ℝ (Fin 3) → ℝ} (ha : 0 < a)
    (hW : ContDiff ℝ 1 W) (hWcs : HasCompactSupport W)
    (htsupp : tsupport W ⊆ Submission.BoseGases.acube a) (hψ : ContDiff ℝ 1 ψ) :
    ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3), ‖p‖ ^ 2 *
        ‖Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) => (W z : ℂ) * (ψ z : ℂ)) p‖ ^ 2
      = ∫ z in Submission.BoseGases.acube a, ∑ k : Fin 3,
          (fderiv ℝ (fun w : EuclideanSpace ℝ (Fin 3) => W w * ψ w) z (Submission.BoseGases.kcStdBasis k)) ^ 2 := by
  -- The product is `C¹` with compact support; this is the only use of the compact
  -- support of `W`, so `ψ` needs no support hypothesis.
  have hprod_cd : ContDiff ℝ 1 (fun z : EuclideanSpace ℝ (Fin 3) => W z * ψ z) := hW.mul hψ
  have hprod_cs : HasCompactSupport (fun z : EuclideanSpace ℝ (Fin 3) => W z * ψ z) := hWcs.mul_right
  -- Gradient Plancherel at `C¹` regularity.
  have hkey := Work.BoseFixB1S.gradient_plancherel_of_contDiff_one hprod_cd hprod_cs
  -- The two Fourier-side integrands only differ by `↑(W z * ψ z) = ↑(W z) * ↑(ψ z)`.
  have hkin : ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3), ‖p‖ ^ 2 *
        ‖Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) => (W z : ℂ) * (ψ z : ℂ)) p‖ ^ 2
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3), ‖p‖ ^ 2 *
        ‖Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) => ((W z * ψ z : ℝ) : ℂ)) p‖ ^ 2 := by
    congr 1
    apply integral_congr_ae
    filter_upwards with p
    rw [kinFT_congr (fun z => (Complex.ofReal_mul (W z) (ψ z)).symm) p]
  -- `∑_k (∂_k f z)² = ‖gradient f z‖²`.
  have hsum : ∀ z : EuclideanSpace ℝ (Fin 3),
      (∑ k : Fin 3, (fderiv ℝ (fun w : EuclideanSpace ℝ (Fin 3) => W w * ψ w) z
          (Submission.BoseGases.kcStdBasis k)) ^ 2)
        = ‖gradient (fun w : EuclideanSpace ℝ (Fin 3) => W w * ψ w) z‖ ^ 2 := by
    intro z
    have hpt : ∀ k : Fin 3,
        fderiv ℝ (fun w : EuclideanSpace ℝ (Fin 3) => W w * ψ w) z (Submission.BoseGases.kcStdBasis k)
          = inner ℝ (gradient (fun w : EuclideanSpace ℝ (Fin 3) => W w * ψ w) z)
              (Submission.BoseGases.kcStdBasis k) := by
      intro k
      rw [inner_gradient_left]
    rw [Finset.sum_congr rfl (fun k _ => by rw [hpt k])]
    exact Submission.BoseGases.sum_inner_kcStdBasis_sq _
  -- `Wψ` vanishes in a neighbourhood of every point outside the cube, so its
  -- derivative does too.
  have hzero : ∀ z : EuclideanSpace ℝ (Fin 3), z ∉ Submission.BoseGases.acube a →
      (∑ k : Fin 3, (fderiv ℝ (fun w : EuclideanSpace ℝ (Fin 3) => W w * ψ w) z
          (Submission.BoseGases.kcStdBasis k)) ^ 2) = 0 := by
    intro z hz
    have hzW : z ∉ tsupport W := fun h => hz (htsupp h)
    have hsub : tsupport (fun w : EuclideanSpace ℝ (Fin 3) => W w * ψ w) ⊆ tsupport W := by
      apply closure_mono
      intro w hw
      simp only [Function.mem_support, ne_eq] at hw ⊢
      exact fun hW0 => hw (by simp [hW0])
    have hzv : z ∉ tsupport (fun w : EuclideanSpace ℝ (Fin 3) => W w * ψ w) :=
      fun h => hzW (hsub h)
    have hfd : fderiv ℝ (fun w : EuclideanSpace ℝ (Fin 3) => W w * ψ w) z = 0 :=
      (HasFDerivAt.of_notMem_tsupport ℝ hzv).fderiv
    simp [hfd]
  rw [hkin, hkey]
  -- Replace the `acube a`-integral by the full-space integral and apply `hsum`.
  have hiff : ∫ z : EuclideanSpace ℝ (Fin 3),
        ‖gradient (fun w : EuclideanSpace ℝ (Fin 3) => W w * ψ w) z‖ ^ 2
      = ∫ z in Submission.BoseGases.acube a, ∑ k : Fin 3,
          (fderiv ℝ (fun w : EuclideanSpace ℝ (Fin 3) => W w * ψ w) z
            (Submission.BoseGases.kcStdBasis k)) ^ 2 := by
    rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := Submission.BoseGases.acube a) hzero]
    apply integral_congr_ae
    filter_upwards with z
    exact (hsum z).symm
  exact hiff

end Work.BoseB1Cube
