/-
Copyright: Work.MRMT (mandelbar) subproject.

# Change of variables for `∫⁻ ‖∂̄g‖` under a `C¹` diffeomorphism

This file proves `Work.MRMT.Found.lintegralAbsDbar_comp_eq`:

for a homeomorphism `F : ℂ ≃ₜ ℂ` that is a `C¹` diffeomorphism (both `F` and `F.symm` are
`ContDiff ℝ 1`) whose complex dilatation is `μF` (`∂̄F = μF · ∂F` pointwise), and a function `H`
that is Lipschitz on a compact set `K`,

`∫⁻_{F '' K} ‖∂̄(H ∘ F.symm)‖ = ∫⁻_K ‖∂̄H − μF ∂H‖ · ‖∂F‖`.

The mathematical content is the standard change of variables formula for a `C¹`
diffeomorphism, combined with the chain rule `∂̄(H ∘ F.symm) = (∂̄H − μF ∂H)/(∂̄... )`:

* `key_pointwise` establishes, at every point `z`,
  `‖det (fderiv ℝ F z)‖ · ‖∂̄(H ∘ F.symm)(F z)‖ = ‖∂̄H z − μF z ∂H z‖ · ‖∂F z‖`.
  This is an *everywhere* identity: if `H` is differentiable at `z` it is the chain rule
  together with the algebraic inversion of the Beltrami relation; if not, both `H` and
  `H ∘ F.symm` are non-differentiable (at `z` resp. `F z`) so both sides are `0`.
  Here we use that `F` is a genuine diffeomorphism, so `det (fderiv ℝ F z) ≠ 0`; the inverse
  Wirtinger derivative is expressed through `∂F` and `μF`.
* Mathlib's `MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul` performs the
  change of variables `∫⁻_{F '' K} = ∫⁻_K ‖det (fderiv ℝ F ·)‖`, and the pointwise identity
  converts the resulting integrand to `‖∂̄H − μF ∂H‖ · ‖∂F‖`.
-/
import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Wirtinger.dzbar_comp
import Submission.Work.MRMT.Wirtinger.dz_comp
import Submission.Work.MRMT.Sobolev.QCCompAux

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Complex Function Filter
open scoped Topology ENNReal

namespace Work.MRMT.Found

/-- **Pointwise change of variables.** For a `C¹` diffeomorphism `F : ℂ ≃ₜ ℂ` with Beltrami
relation `∂̄F = μF · ∂F` (pointwise) and an arbitrary `H`, at every `z`

`‖det (fderiv ℝ F z)‖ · ‖∂̄(H ∘ F.symm)(F z)‖ = ‖∂̄H z − μF z · ∂H z‖ · ‖∂F z‖`.

If `H` is differentiable at `z` this is the chain rule for `H = (H ∘ F.symm) ∘ F` combined
with the algebraic identity `∂̄H z − μF z ∂H z = ∂̄(H∘F.symm)(F z) · conj(∂F z) · (1 − |μF z|²)`
and `det (fderiv ℝ F z) = ‖∂F z‖² (1 − |μF z|²)`; if `H` is not differentiable at `z`, then
neither is `H ∘ F.symm` at `F z` (as `F` is differentiable), so all Wirtinger derivatives
involved take the junk value `0` and both sides vanish. -/
private theorem key_pointwise (F : ℂ ≃ₜ ℂ) (μF H : ℂ → ℂ)
    (hF : ContDiff ℝ 1 (F : ℂ → ℂ)) (hFs : ContDiff ℝ 1 ((F.symm : ℂ → ℂ)))
    (hrel : ∀ z : ℂ, Work.MRMT.dzbar (F : ℂ → ℂ) z = μF z * Work.MRMT.dz (F : ℂ → ℂ) z)
    (z : ℂ) :
    ‖(fderiv ℝ (F : ℂ → ℂ) z).det‖ * ‖Work.MRMT.dzbar (H ∘ (F.symm : ℂ → ℂ)) (F z)‖
      = ‖Work.MRMT.dzbar H z - μF z * Work.MRMT.dz H z‖ * ‖Work.MRMT.dz (F : ℂ → ℂ) z‖ := by
  by_cases hd : DifferentiableAt ℝ H z
  · -- `H` is differentiable at `z`: the chain rule and the Beltrami relation
    have hFs_at : DifferentiableAt ℝ (F.symm : ℂ → ℂ) (F z) :=
      hFs.contDiffAt.differentiableAt (by norm_num)
    have hF_at : DifferentiableAt ℝ (F : ℂ → ℂ) z :=
      hF.contDiffAt.differentiableAt (by norm_num)
    have hg : DifferentiableAt ℝ (H ∘ (F.symm : ℂ → ℂ)) (F z) := by
      have hd' : DifferentiableAt ℝ H ((F.symm : ℂ → ℂ) (F z)) := by
        rwa [Homeomorph.symm_apply_apply]
      exact hd'.comp (F z) hFs_at
    have hdzbar := Work.MRMT.Wirtinger.dzbar_comp (f := (F : ℂ → ℂ))
      (g := H ∘ (F.symm : ℂ → ℂ)) hg hF_at
    have hdz := Work.MRMT.Wirtinger.dz_comp (f := (F : ℂ → ℂ))
      (g := H ∘ (F.symm : ℂ → ℂ)) hg hF_at
    have hfun : ((H ∘ (F.symm : ℂ → ℂ)) ∘ (F : ℂ → ℂ)) = H := by
      funext w; simp [Function.comp_apply, Homeomorph.symm_apply_apply]
    rw [hfun] at hdzbar hdz
    -- the algebraic identity `∂̄H z − μF z ∂H z = ∂̄(H∘F.symm)(F z) · conj(∂F z) · (1 − |μF z|²)`
    have hkey : Work.MRMT.dzbar H z - μF z * Work.MRMT.dz H z
        = Work.MRMT.dzbar (H ∘ (F.symm : ℂ → ℂ)) (F z) * star (Work.MRMT.dz (F : ℂ → ℂ) z)
            * (1 - μF z * star (μF z)) := by
      rw [hdzbar, hdz, hrel z, star_mul]
      ring
    -- `det (fderiv ℝ F z) = ‖∂F z‖² (1 − |μF z|²)`
    have hdet_eq : (fderiv ℝ (F : ℂ → ℂ) z).det
        = ‖Work.MRMT.dz (F : ℂ → ℂ) z‖^2 * (1 - ‖μF z‖^2) := by
      rw [Work.MRMT.Sobolev.det_fderiv_eq, hrel z, norm_mul]
      ring
    have hmm_norm : ‖(1 : ℂ) - μF z * star (μF z)‖ = |1 - ‖μF z‖^2| := by
      have hmm : μF z * star (μF z) = ((‖μF z‖^2 : ℝ) : ℂ) := by
        rw [← starRingEnd_apply (μF z), Complex.mul_conj, Complex.normSq_eq_norm_sq]
      rw [show (1 : ℂ) - μF z * star (μF z) = ((1 - ‖μF z‖^2 : ℝ) : ℂ) from by
        rw [hmm, ← Complex.ofReal_one, ← Complex.ofReal_sub]]
      rw [Complex.norm_real, Real.norm_eq_abs]
    calc ‖(fderiv ℝ (F : ℂ → ℂ) z).det‖ * ‖Work.MRMT.dzbar (H ∘ (F.symm : ℂ → ℂ)) (F z)‖
        = (‖Work.MRMT.dz (F : ℂ → ℂ) z‖^2 * |1 - ‖μF z‖^2|)
            * ‖Work.MRMT.dzbar (H ∘ (F.symm : ℂ → ℂ)) (F z)‖ := by
          rw [Real.norm_eq_abs, hdet_eq, abs_mul, abs_of_nonneg (sq_nonneg _)]
      _ = ‖Work.MRMT.dzbar H z - μF z * Work.MRMT.dz H z‖ * ‖Work.MRMT.dz (F : ℂ → ℂ) z‖ := by
          rw [hkey]
          simp only [norm_mul, norm_star, hmm_norm]
          ring
  · -- `H` is not differentiable at `z`: both sides vanish
    have hndg : ¬ DifferentiableAt ℝ (H ∘ (F.symm : ℂ → ℂ)) (F z) := by
      intro h
      have hF_at : DifferentiableAt ℝ (F : ℂ → ℂ) z :=
        hF.contDiffAt.differentiableAt (by norm_num)
      have hc := h.comp z hF_at
      have hfun : ((H ∘ (F.symm : ℂ → ℂ)) ∘ (F : ℂ → ℂ)) = H := by
        funext w; simp [Function.comp_apply, Homeomorph.symm_apply_apply]
      rw [hfun] at hc
      exact hd hc
    have hq : Work.MRMT.dzbar (H ∘ (F.symm : ℂ → ℂ)) (F z) = 0 := by
      rw [Work.MRMT.dzbar, fderiv_zero_of_not_differentiableAt (𝕜 := ℝ) hndg]
      simp
    have hA : Work.MRMT.dzbar H z = 0 := by
      rw [Work.MRMT.dzbar, fderiv_zero_of_not_differentiableAt (𝕜 := ℝ) hd]; simp
    have hB : Work.MRMT.dz H z = 0 := by
      rw [Work.MRMT.dz, fderiv_zero_of_not_differentiableAt (𝕜 := ℝ) hd]; simp
    rw [hq, hA, hB]
    simp

theorem lintegralAbsDbar_comp_eq {F : ℂ ≃ₜ ℂ} {μF H : ℂ → ℂ} {K : Set ℂ} (hK : IsCompact K)
    (hF : ContDiff ℝ 1 (F : ℂ → ℂ)) (hFs : ContDiff ℝ 1 ((F.symm : ℂ → ℂ)))
    (hrel : ∀ z : ℂ, dzbar (F : ℂ → ℂ) z = μF z * dz (F : ℂ → ℂ) z)
    (C : NNReal) (hH : LipschitzOnWith C H K) :
    lintegralAbsDbar (H ∘ (F.symm : ℂ → ℂ)) (F '' K) = lintegralAbsBeltrami H μF (F : ℂ → ℂ) K := by
  unfold lintegralAbsDbar lintegralAbsBeltrami
  have hKmeas : MeasurableSet K := hK.measurableSet
  have hderiv : ∀ x ∈ K, HasFDerivWithinAt (F : ℂ → ℂ) (fderiv ℝ (F : ℂ → ℂ) x) K x :=
    fun x _ => (hF.contDiffAt.differentiableAt (by norm_num)).hasFDerivAt.hasFDerivWithinAt
  have hinj : Set.InjOn (F : ℂ → ℂ) K := F.injective.injOn
  -- change of variables `w = F z`, `dw = ‖det (fderiv ℝ F z)‖ dz`
  have hcov := MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hKmeas hderiv hinj
      (fun w => ENNReal.ofReal ‖dzbar (H ∘ (F.symm : ℂ → ℂ)) w‖)
  rw [hcov]
  -- the pointwise identity makes the two integrands agree
  refine MeasureTheory.lintegral_congr (fun z => ?_)
  rw [← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  rw [← Real.norm_eq_abs]
  exact key_pointwise F μF H hF hFs hrel z

end Work.MRMT.Found
