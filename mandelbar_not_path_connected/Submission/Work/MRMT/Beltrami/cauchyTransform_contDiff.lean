import Mathlib
import Submission.Work.MRMT.Cauchy.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Beltrami

open MeasureTheory Complex Function Filter
open scoped Distributions Topology ENNReal

/-- The Cauchy kernel `t ↦ t⁻¹` is locally integrable on `ℂ`: `ℂ` has real dimension `2`, so the
bound `‖t⁻¹‖ = ‖t‖ ^ (-1)` has exponent `-1 < 0 = 2 - 2`, and functions dominated by a negative
power of the norm of exponent larger than `-dim` are locally integrable. -/
lemma locallyIntegrable_inv_complex :
    LocallyIntegrable (fun t : ℂ => t⁻¹) (volume : Measure ℂ) := by
  refine locallyIntegrable_of_norm_le_rpow (E := ℂ) (F := ℂ) (by norm_num) (C := 1) (α := 1)
    (by norm_num) ?_ ?_
  · filter_upwards with x
    rw [norm_inv, Real.rpow_neg_one, one_mul]
  · exact measurable_inv.aestronglyMeasurable

/-- **The Cauchy integral as a convolution integral.**  For every `z`,
`∫ ζ, ψ ζ / (ζ - z) = - ∫ t, t⁻¹ * ψ (z - t)`.  Indeed, translating the integration variable by
`z` turns the left hand side into `∫ w, ψ (z + w) / w`, and negating the integration variable
(`integral_neg_eq_self`) turns this into `- ∫ t, t⁻¹ * ψ (z - t)`.  This holds for *every* `ψ`,
no measurability or integrability assumption being needed, since both sides are Bochner integrals
and the two identifications are the unconditional identities `integral_add_left_eq_self` and
`integral_neg_eq_self` for the Haar measure `volume` on `ℂ`. -/
lemma integral_div_sub_eq_neg_integral_inv_mul (ψ : ℂ → ℂ) (z : ℂ) :
    ∫ ζ, ψ ζ / (ζ - z) = - ∫ t, t⁻¹ * ψ (z - t) := by
  have h1 : ∫ ζ, ψ ζ / (ζ - z) = ∫ x, ψ (z + x) / x := by
    simpa [add_sub_cancel_left] using
      (integral_add_left_eq_self (fun ζ : ℂ => ψ ζ / (ζ - z)) z).symm
  rw [h1]
  rw [← integral_neg_eq_self (fun w : ℂ => ψ (z + w) / w) volume]
  rw [show (fun x : ℂ => ψ (z + -x) / -x) = fun x => -(x⁻¹ * ψ (z + -x)) by
    funext x; rw [div_eq_mul_inv, inv_neg, mul_neg, mul_comm]]
  rw [integral_neg]
  simp only [sub_eq_add_neg]

/-- **The Cauchy transform is a convolution with the locally integrable kernel `t ↦ t⁻¹`.**
`Work.MRMT.cauchyTransform ψ = -cauchyConst • (ψ ⋆ t⁻¹)`, where the convolution is the
Bochner convolution over `volume` on `ℂ` with the `ℝ`-bilinear product as pairing. -/
lemma cauchyTransform_eq_neg_const_mul_convolution (ψ : ℂ → ℂ) :
    Work.MRMT.cauchyTransform ψ =
      fun z => (- Work.MRMT.cauchyConst) *
        MeasureTheory.convolution (fun t : ℂ => t⁻¹) ψ (ContinuousLinearMap.mul ℝ ℂ) volume z := by
  funext z
  simp only [Work.MRMT.cauchyTransform]
  rw [integral_div_sub_eq_neg_integral_inv_mul ψ z]
  rw [convolution_def]
  simp only [ContinuousLinearMap.mul_apply']
  ring

/-- **The Cauchy transform of a `C^∞` compactly supported function is `C^∞`.**

`Work.MRMT.cauchyTransform ψ z = -(1/π) * ∫ ζ, ψ ζ / (ζ - z)` (absolutely convergent for
compactly supported `ψ`).

Route.  Write `ψ = ψ·η(· - ζ) + ψ·(1 - η(· - ζ))` for a smooth cutoff `η` with `η ≡ 1` near `0`
(a `ContDiffBump`).  The second term is a parametric integral whose integrand extends smoothly
across the diagonal (`1 - η w` vanishes to infinite order at `w = 0`), so it is `C^∞` in `ζ` by
differentiating under the integral sign.  In the first term substitute `w = z - ζ` (translation
invariance of Lebesgue measure) to get `∫ w, ψ (ζ + w) * η w / w`, and write
`ψ (ζ + w) = ψ ζ + (∂ψ ζ) * w + (∂̄ψ ζ) * w̄ + R (ζ, w)` with `R` smooth in `(ζ, w)` and
`R (ζ, w) = O(‖w‖^2)`.  The first three terms give constants times `ψ ζ`, `∂ψ ζ`, `∂̄ψ ζ`
(absolutely convergent integrals, e.g. `∫ w, η w / w`), and `R (ζ,w) * η w / w` is again a
smooth parametric integral with `w`-support compact, so `C^∞` in `ζ`.  Mathlib's tool for the
parametric differentiation is
`MeasureTheory.hasFDerivAt_integral_of_dominated_loc_of_lip`.  Each differentiation under the
integral costs one order of smoothness of `ψ`, so `ψ ∈ C^∞` gives `C^∞`; for the consumer it
would already be enough to know `ContDiff ℝ n (cauchyTransform ψ)` for all `n ≤ 2`.

Formalised as follows.  By translation and negation invariance of Lebesgue measure on `ℂ`
(`integral_add_left_eq_self`, `integral_neg_eq_self`) the Cauchy integral is *exactly* the
convolution of `ψ` with the single locally integrable kernel `t ↦ t⁻¹`:
`cauchyTransform ψ z = -cauchyConst * (t⁻¹ ⋆ ψ) z`
(`cauchyTransform_eq_neg_const_mul_convolution`).  This needs no cutoff and no Taylor expansion
because `t ↦ t⁻¹` is locally integrable on `ℂ` (real dimension `2 > 1`,
`locallyIntegrable_inv_complex`), so the convolution is absolutely convergent.  The
smoothing statement `HasCompactSupport.contDiff_convolution_right` (`f` locally integrable, `g`
`C^n` with compact support) then gives `ContDiff ℝ n` of the convolution for every `n`, in
particular for `n = ∞`. -/
theorem cauchyTransform_contDiff (ψ : ℂ → ℂ)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hs : HasCompactSupport ψ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.MRMT.cauchyTransform ψ) := by
  have hconv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (MeasureTheory.convolution (fun t : ℂ => t⁻¹) ψ (ContinuousLinearMap.mul ℝ ℂ) volume) :=
    hs.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℂ) locallyIntegrable_inv_complex hψ
  rw [cauchyTransform_eq_neg_const_mul_convolution ψ]
  exact hconv.const_smul (- Work.MRMT.cauchyConst)

end Work.MRMT.Beltrami
