import Mathlib
import Submission.Work.Drive.N2.modelBall

/-!
# The saddle coordinate `Z` of a chart adapted to a saddle point

If a chart `φ` of a surface realises the function `f` as `f y = c + s₁ * (φ y 0)^2 + s₂ * (φ y 1)^2`
with `s₁ = -s₂ = ±1`, then `f - c` is the real part of the square of a smooth, injective, immersive
`ℂ`-valued coordinate `Z` on `φ.source`:

* `s₁ = 1, s₂ = -1`:  `Z y = φ y 0 + i · φ y 1`,  and `Re ((φ₀ + i φ₁)²) = φ₀² - φ₁²`;
* `s₁ = -1, s₂ = 1`:  `Z y = φ y 1 + i · φ y 0`,  and `Re ((φ₁ + i φ₀)²) = φ₁² - φ₀²`.

`Z` is the composite of the chart with the linear isomorphism `ℝ² → ℂ` (`saddleCoordCLM` and its
transpose `saddleCoordCLM'`), hence smooth, injective and immersive whenever `φ` is.

This is the "saddle coordinate" of the `n = 2` movie: the flow lines of `Re z²` are the level lines
`Im z² = const`, so `Z` puts the level structure of `f` near the saddle into the standard form.
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology
open Set Function

/-- The `ℂ`-coordinate `(u₀, u₁) ↦ u₀ + i u₁` as a continuous linear map (real-linear). -/
noncomputable def saddleCoordCLM : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℂ :=
  (Complex.ofRealCLM.comp (EuclideanSpace.proj (0 : Fin 2)))
    + (Complex.ofRealCLM.comp (EuclideanSpace.proj (1 : Fin 2))).smulRight Complex.I

/-- The transposed `ℂ`-coordinate `(u₀, u₁) ↦ u₁ + i u₀` as a continuous linear map. -/
noncomputable def saddleCoordCLM' : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℂ :=
  (Complex.ofRealCLM.comp (EuclideanSpace.proj (1 : Fin 2)))
    + (Complex.ofRealCLM.comp (EuclideanSpace.proj (0 : Fin 2))).smulRight Complex.I

lemma saddleCoordCLM_apply (u : EuclideanSpace ℝ (Fin 2)) :
    saddleCoordCLM u = (u 0 : ℂ) + (u 1 : ℂ) * Complex.I := by
  simp [saddleCoordCLM]

lemma saddleCoordCLM'_apply (u : EuclideanSpace ℝ (Fin 2)) :
    saddleCoordCLM' u = (u 1 : ℂ) + (u 0 : ℂ) * Complex.I := by
  simp [saddleCoordCLM']

lemma saddleCoordCLM_injective : Function.Injective saddleCoordCLM := by
  intro u v h
  rw [saddleCoordCLM_apply u, saddleCoordCLM_apply v] at h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_add,
    sub_zero] at hre him
  ext i
  fin_cases i
  · exact hre
  · exact him

lemma saddleCoordCLM'_injective : Function.Injective saddleCoordCLM' := by
  intro u v h
  rw [saddleCoordCLM'_apply u, saddleCoordCLM'_apply v] at h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_add,
    sub_zero] at hre him
  ext i
  fin_cases i
  · exact him
  · exact hre

theorem exists_saddleCoord {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M] (f : M → ℝ) (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (s₁ s₂ c : ℝ) (hs : (s₁ = 1 ∧ s₂ = -1) ∨ (s₁ = -1 ∧ s₂ = 1)) (hφ : ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => φ y) φ.source) (hφimm : ∀ x ∈ φ.source, Function.Injective (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (fun y => φ y) x)) (hlev : ∀ y ∈ φ.source, f y = c + Work.Drive.N2.chartQ φ s₁ s₂ y) : ∃ Z : M → ℂ, ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (modelWithCornersSelf ℝ ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) Z φ.source ∧ Set.InjOn Z φ.source ∧ (∀ x ∈ φ.source, Function.Injective (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (modelWithCornersSelf ℝ ℂ) Z x)) ∧ (∀ y ∈ φ.source, f y = c + (Z y ^ 2).re) := by
  rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- `s₁ = 1`, `s₂ = -1`: use `Z y = φ y 0 + i * φ y 1`.
    refine ⟨⇑saddleCoordCLM ∘ ⇑φ, ?_, ?_, ?_, ?_⟩
    · exact saddleCoordCLM.contMDiff.comp_contMDiffOn hφ
    · intro y hy y' hy' h
      exact φ.injOn hy hy' (saddleCoordCLM_injective h)
    · intro x hx v w hvw
      have hg : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
          (modelWithCornersSelf ℝ ℂ) (⇑saddleCoordCLM) (φ x) :=
        saddleCoordCLM.mdifferentiableAt
      have hf : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (fun y => φ y) x :=
        (hφ.contMDiffAt (φ.open_source.mem_nhds hx)).mdifferentiableAt (by simp)
      rw [mfderiv_comp_apply x hg hf v, mfderiv_comp_apply x hg hf w,
        ContinuousLinearMap.mfderiv_eq] at hvw
      exact (hφimm x hx) (saddleCoordCLM_injective hvw)
    · intro y hy
      rw [hlev y hy]
      have hz : ((saddleCoordCLM (φ y)) ^ 2).re = (φ y 0) ^ 2 - (φ y 1) ^ 2 := by
        rw [saddleCoordCLM_apply, pow_two]
        simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im]
        ring
      simp only [Function.comp_apply]
      rw [hz, Work.Drive.N2.chartQ]
      ring
  · -- `s₁ = -1`, `s₂ = 1`: use `Z y = φ y 1 + i * φ y 0`.
    refine ⟨⇑saddleCoordCLM' ∘ ⇑φ, ?_, ?_, ?_, ?_⟩
    · exact saddleCoordCLM'.contMDiff.comp_contMDiffOn hφ
    · intro y hy y' hy' h
      exact φ.injOn hy hy' (saddleCoordCLM'_injective h)
    · intro x hx v w hvw
      have hg : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
          (modelWithCornersSelf ℝ ℂ) (⇑saddleCoordCLM') (φ x) :=
        saddleCoordCLM'.mdifferentiableAt
      have hf : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (fun y => φ y) x :=
        (hφ.contMDiffAt (φ.open_source.mem_nhds hx)).mdifferentiableAt (by simp)
      rw [mfderiv_comp_apply x hg hf v, mfderiv_comp_apply x hg hf w,
        ContinuousLinearMap.mfderiv_eq] at hvw
      exact (hφimm x hx) (saddleCoordCLM'_injective hvw)
    · intro y hy
      rw [hlev y hy]
      have hz : ((saddleCoordCLM' (φ y)) ^ 2).re = (φ y 1) ^ 2 - (φ y 0) ^ 2 := by
        rw [saddleCoordCLM'_apply, pow_two]
        simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im]
        ring
      simp only [Function.comp_apply]
      rw [hz, Work.Drive.N2.chartQ]
      ring

end Work.Drive.N2
