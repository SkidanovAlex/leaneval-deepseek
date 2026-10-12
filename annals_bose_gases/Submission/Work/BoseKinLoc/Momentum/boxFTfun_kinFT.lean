import Mathlib.Analysis.Fourier.Convolution
import Submission.Work.BoseKinLoc.Momentum.momDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Momentum.boxFTfun_kinFT` — the `q`-Fourier transform of `boxFTfun`

`boxFTfun ℓ p ψ x = ∫_{z ∈ acube ℓ} e^{−i⟪p,z⟫} ψ(x+z) dz` is the `p`-Fourier transform of
`ψ` localised to the box `x + acube ℓ` (`momDefs`).  This module computes its `q`-Fourier
transform:

  `kinFT (boxFTfun ℓ p ψ) q = fhat ψ q · θ̂(q − p)`,

where `kinFT u q = ∫_x e^{−i⟪q,x⟫}u(x)dx` (`Submission.BoseGases.kinFT`), `fhat ψ` is the
`p`-convention transform of `ψ` and `boxHat ℓ k = ∫_{acube ℓ} cos⟪k,z⟫ dz`
(`Work.OneBodyKin.boxHat`) is the transform of the box indicator.

## Route

`boxFTfun ℓ p ψ` is the convolution of `ψ` with the `p`-modulated box indicator
`boxTheta ℓ p = 1_{acube ℓ}·e^{i⟪p,·⟫}` (`boxFTfun_eq_conv`, reflection of the symmetric
cube plus the set-integral form of the convolution).  The Fourier convolution theorem
(`Real.fourier_mul_convolution_eq`, applied through the identification
`kinFT u p = 𝓕u((2π)⁻¹•p)` of `Work.SmallBoxBridge.Resolve.kinFT_eq_fourier`) therefore
factors the transform into `kinFT (boxTheta ℓ p) q · fhat ψ q`, and the symbol is

  `kinFT (boxTheta ℓ p) q = ∫_{z ∈ acube ℓ} e^{−i⟪q,z⟫}e^{i⟪p,z⟫}dz
                           = ∫_{z ∈ acube ℓ} e^{−i⟪q−p,z⟫}dz = boxHat ℓ (q−p)`

(`kinFT_boxTheta`, using the corpus's `Work.OneBodyKin.kinFT_bsMeanBoxInd` via
`integral_exp_acube`).

The identity holds for every `ℓ : ℝ` (no positivity of the box side is used; the cube's
symmetry under negation is what matters).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal FourierTransform Convolution

namespace Work.BoseKinLoc.Momentum

open Submission.BoseGases

set_option linter.unusedVariables false

/-! ## 1. The `p`-modulated box indicator -/

/-- `boxTheta ℓ p = 1_{acube ℓ}·e^{i⟪p,·⟫}`: the convolution partner of `ψ` whose
convolution with `ψ` is `boxFTfun ℓ p ψ`. -/
noncomputable def boxTheta (ℓ : ℝ) (p : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) → ℂ :=
  (acube ℓ).indicator (fun z => Complex.exp (Complex.I * (inner ℝ p z : ℂ)))

lemma boxTheta_of_mem {ℓ : ℝ} {p z : EuclideanSpace ℝ (Fin 3)} (hz : z ∈ acube ℓ) :
    boxTheta ℓ p z = Complex.exp (Complex.I * (inner ℝ p z : ℂ)) :=
  Set.indicator_of_mem hz _

lemma boxTheta_of_notMem {ℓ : ℝ} {p z : EuclideanSpace ℝ (Fin 3)} (hz : z ∉ acube ℓ) :
    boxTheta ℓ p z = 0 :=
  Set.indicator_of_notMem hz _

/-- `boxTheta ℓ p (−z) = 1_{acube ℓ}(z)·e^{-i⟪p,z⟫}`: the cube is symmetric under negation. -/
lemma boxTheta_neg (ℓ : ℝ) (p z : EuclideanSpace ℝ (Fin 3)) :
    boxTheta ℓ p (-z)
      = (acube ℓ).indicator (fun z => Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))) z := by
  by_cases hz : z ∈ acube ℓ
  · have hz' : -z ∈ acube ℓ := (Work.OneBodyKin.neg_mem_acube_iff ℓ z).mpr hz
    rw [boxTheta, Set.indicator_of_mem hz', Set.indicator_of_mem hz]
    congr 1
    rw [inner_neg_right, Complex.ofReal_neg, mul_neg]
  · have hz' : -z ∉ acube ℓ := fun h => hz ((Work.OneBodyKin.neg_mem_acube_iff ℓ z).mp h)
    rw [boxTheta, Set.indicator_of_notMem hz', Set.indicator_of_notMem hz]

/-- `boxTheta ℓ p` is integrable: it is bounded by `1` and supported in the finite-measure
cube `acube ℓ`. -/
lemma integrable_boxTheta (ℓ : ℝ) (p : EuclideanSpace ℝ (Fin 3)) :
    Integrable (boxTheta ℓ p) volume := by
  rw [boxTheta, MeasureTheory.integrable_indicator_iff (acube_measurable ℓ)]
  refine IntegrableOn.of_bound ((Work.UBBInputs9.B.acube_isCompact ℓ).measure_lt_top) ?_ 1 ?_
  · exact (Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp (continuous_const.inner continuous_id)))).aestronglyMeasurable
  · filter_upwards with z
    have h1 : Complex.I * (inner ℝ p z : ℂ) = ((inner ℝ p z : ℝ) : ℂ) * Complex.I := by
      ring
    rw [h1, Complex.norm_exp_ofReal_mul_I]

/-- `(ψ(·) : ℂ)` is integrable for smooth compactly supported real `ψ`. -/
lemma integrable_psiCe (ψ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    Integrable (fun y : EuclideanSpace ℝ (Fin 3) => (ψ y : ℂ)) volume :=
  (Complex.continuous_ofReal.comp hψ.continuous).integrable_of_hasCompactSupport
    (hcs.comp_left (by simp))

/-! ## 2. `boxFTfun` as a convolution -/

/-- **`boxFTfun ℓ p ψ` is the convolution of `ψ` with the `p`-modulated box indicator.**
The convolution `(boxTheta ⋆ ψℂ)(x) = ∫_t e^{i⟪p,t⟫}1_{acube ℓ}(t)ψ(x−t)dt` is turned into the
set integral `∫_{z ∈ acube ℓ}e^{−i⟪p,z⟫}ψ(x+z)dz` by the reflection `t ↦ −t`. -/
lemma boxFTfun_eq_conv (ℓ : ℝ) (p : EuclideanSpace ℝ (Fin 3))
    (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) :
    boxFTfun ℓ p ψ
      = boxTheta ℓ p ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
          (fun y : EuclideanSpace ℝ (Fin 3) => (ψ y : ℂ)) := by
  funext x
  rw [MeasureTheory.convolution_mul]
  rw [← MeasureTheory.integral_neg_eq_self
        (f := fun t : EuclideanSpace ℝ (Fin 3) => boxTheta ℓ p t * (ψ (x - t) : ℂ))]
  rw [show (∫ t : EuclideanSpace ℝ (Fin 3), boxTheta ℓ p (-t) * (ψ (x - -t) : ℂ))
        = ∫ t : EuclideanSpace ℝ (Fin 3), (acube ℓ).indicator
            (fun t : EuclideanSpace ℝ (Fin 3) =>
              Complex.exp (-(Complex.I * (inner ℝ p t : ℂ))) * (ψ (x + t) : ℂ)) t from by
    apply integral_congr_ae
    filter_upwards with t
    rw [boxTheta_neg, sub_neg_eq_add]
    by_cases ht : t ∈ acube ℓ
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, zero_mul]]
  rw [MeasureTheory.integral_indicator (acube_measurable ℓ)]
  rfl

/-! ## 3. The symbol integral and the transform of `boxTheta` -/

/-- **The exponential integral over the box**:
`∫_{z ∈ acube ℓ} e^{−i⟪k,z⟫}dz = boxHat ℓ k` (for every `ℓ`, via the corpus's computation
`Work.OneBodyKin.kinFT_bsMeanBoxInd` for the box indicator). -/
lemma integral_exp_acube (ℓ : ℝ) (k : EuclideanSpace ℝ (Fin 3)) :
    (∫ t in acube ℓ, Complex.exp (-(Complex.I * (inner ℝ k t : ℂ))))
      = (Work.OneBodyKin.boxHat ℓ k : ℂ) := by
  have h := Work.OneBodyKin.kinFT_bsMeanBoxInd ℓ k
  rw [kinFT] at h
  rw [← h]
  rw [show (fun y : EuclideanSpace ℝ (Fin 3) => Complex.exp (-(Complex.I * (inner ℝ k y : ℂ)))
        * (Work.OneBodyKin.bsMeanBoxInd ℓ y : ℂ))
      = (acube ℓ).indicator
          (fun y : EuclideanSpace ℝ (Fin 3) =>
            Complex.exp (-(Complex.I * (inner ℝ k y : ℂ)))) from by
    funext y
    by_cases hy : y ∈ acube ℓ
    · rw [Set.indicator_of_mem hy, Work.OneBodyKin.bsMeanBoxInd_of_mem hy]; simp
    · rw [Set.indicator_of_notMem hy, Work.OneBodyKin.bsMeanBoxInd_of_notMem hy]; simp]
  rw [MeasureTheory.integral_indicator (acube_measurable ℓ)]

/-- **The `q`-Fourier transform of the modulated box indicator**:
`kinFT (boxTheta ℓ p) q = boxHat ℓ (q − p)`. -/
lemma kinFT_boxTheta (ℓ : ℝ) (p q : EuclideanSpace ℝ (Fin 3)) :
    kinFT (boxTheta ℓ p) q = (Work.OneBodyKin.boxHat ℓ (q - p) : ℂ) := by
  rw [kinFT]
  rw [show (fun t : EuclideanSpace ℝ (Fin 3) =>
          Complex.exp (-(Complex.I * (inner ℝ q t : ℂ))) * boxTheta ℓ p t)
      = (acube ℓ).indicator (fun t : EuclideanSpace ℝ (Fin 3) =>
          Complex.exp (-(Complex.I * (inner ℝ q t : ℂ)))
            * Complex.exp (Complex.I * (inner ℝ p t : ℂ))) from by
    funext t
    rw [boxTheta]
    by_cases ht : t ∈ acube ℓ
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, mul_zero]]
  rw [MeasureTheory.integral_indicator (acube_measurable ℓ)]
  rw [show (∫ t in acube ℓ, Complex.exp (-(Complex.I * (inner ℝ q t : ℂ)))
        * Complex.exp (Complex.I * (inner ℝ p t : ℂ)))
      = ∫ t in acube ℓ, Complex.exp (-(Complex.I * (inner ℝ (q - p) t : ℂ))) from by
    apply MeasureTheory.setIntegral_congr_fun (acube_measurable ℓ)
    intro t _
    show Complex.exp (-(Complex.I * (inner ℝ q t : ℂ)))
        * Complex.exp (Complex.I * (inner ℝ p t : ℂ))
      = Complex.exp (-(Complex.I * (inner ℝ (q - p) t : ℂ)))
    rw [← Complex.exp_add]
    congr 1
    rw [inner_sub_left]
    push_cast
    ring]
  exact integral_exp_acube ℓ (q - p)

/-! ## 4. The main identity -/

theorem boxFTfun_kinFT (ℓ : ℝ) (p : EuclideanSpace ℝ (Fin 3)) (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) (q : EuclideanSpace ℝ (Fin 3)) : Submission.BoseGases.kinFT (Work.BoseKinLoc.Momentum.boxFTfun ℓ p ψ) q = Work.BoseKinLoc.fhat ψ q * (Work.OneBodyKin.boxHat ℓ (q - p) : ℂ) := by
  rw [boxFTfun_eq_conv ℓ p ψ]
  rw [Work.SmallBoxBridge.Resolve.kinFT_eq_fourier
    (boxTheta ℓ p ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
      (fun y : EuclideanSpace ℝ (Fin 3) => (ψ y : ℂ))) q]
  rw [Real.fourier_mul_convolution_eq (integrable_boxTheta ℓ p) (integrable_psiCe ψ hψ hcs)
    ((2 * Real.pi)⁻¹ • q)]
  rw [← Work.SmallBoxBridge.Resolve.kinFT_eq_fourier (boxTheta ℓ p) q]
  rw [show FourierTransform.fourier (fun y : EuclideanSpace ℝ (Fin 3) => (ψ y : ℂ))
        ((2 * Real.pi)⁻¹ • q)
      = fhat ψ q from by
    rw [fhat]; exact (Work.SmallBoxBridge.Resolve.kinFT_eq_fourier _ _).symm]
  rw [kinFT_boxTheta ℓ p q, mul_comm]

end Work.BoseKinLoc.Momentum
