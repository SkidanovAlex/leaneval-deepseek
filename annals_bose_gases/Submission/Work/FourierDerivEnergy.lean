import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Submission.Commons.Analysis.Fourier.integral_norm_sq_fourier_l1l2
import Submission.KineticChild
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Fourier form of the kinetic energy (the symbol step of the kinetic bridge)

For a Schwartz function `f : ℝ³ → ℂ` and a direction `m : ℝ³`,

    ∫_x ‖∂_m f(x)‖² = (2π)² ∫_ξ ⟨ξ,m⟩² ‖𝓕f(ξ)‖²

(`𝓕` the `2π`-convention `𝓕f(ξ) = ∫ f(x)e^{−2πi⟨ξ,x⟩}dx`).  This is the analytic core of the
kinetic bridge: it converts a p-space kinetic symbol into the position-space Dirichlet energy
`Σ_k∫(∂_k f)²` (= the corpus's `kinWord`); the pointwise symbol bound `F(‖ξ‖) ≤ ‖ξ‖²` then gives
`(2π)⁻³∫F(‖q‖)‖𝓕f(q/(2π))‖²dq ≤ ∫Σ_k(∂_kf)²` for any radial symbol `F`.

Ingredients: Plancherel for Schwartz maps (`SchwartzMap.integral_norm_sq_fourier`) and the
Fourier transform of a line derivative (`SchwartzMap.fourier_lineDerivOp_eq`).
-/

noncomputable section

open MeasureTheory
open scoped FourierTransform ContDiff SchwartzMap

namespace Submission
open _root_.BoseGases
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open LineDeriv in
/-- **Fourier form of the kinetic energy, one direction**: for `f : 𝓢(ℝ³, ℂ)` and `m : ℝ³`,

    ∫_x ‖∂_m f(x)‖² = (2π)² ∫_ξ ⟨ξ,m⟩² ‖𝓕f(ξ)‖² . -/
theorem integral_lineDeriv_sq_eq (f : 𝓢(ℝ³, ℂ)) (m : ℝ³) :
    (∫ x : ℝ³, ‖∂_{m} f x‖ ^ 2)
      = (2 * Real.pi) ^ 2 * ∫ ξ : ℝ³, (inner ℝ ξ m) ^ 2 * ‖(𝓕 f) ξ‖ ^ 2 := by
  have htg : Function.HasTemperateGrowth (fun x : ℝ³ => inner ℝ x m) :=
    ((innerSL ℝ).flip m).hasTemperateGrowth
  have happly : ∀ ξ : ℝ³,
      ((2 * Real.pi * Complex.I) • SchwartzMap.smulLeftCLM ℂ (inner ℝ · m) (𝓕 f)) ξ
        = (2 * Real.pi * Complex.I * ((inner ℝ ξ m : ℝ) : ℂ)) • (𝓕 f) ξ := by
    intro ξ
    rw [smul_apply, SchwartzMap.smulLeftCLM_apply htg]
    simp only []
    rw [Complex.real_smul]
    ring
  have hnorm : ∀ ξ : ℝ³,
      ‖(2 * Real.pi * Complex.I * ((inner ℝ ξ m : ℝ) : ℂ) : ℂ)‖ ^ 2
        = (2 * Real.pi) ^ 2 * (inner ℝ ξ m) ^ 2 := by
    intro ξ
    have hreal : ∀ r : ℝ, ‖((r : ℝ) : ℂ)‖ ^ 2 = r ^ 2 := by
      intro r
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
      ring
    rw [show (2 * Real.pi * Complex.I * ((inner ℝ ξ m : ℝ) : ℂ))
        = ((2 * Real.pi : ℝ) : ℂ) * Complex.I * ((inner ℝ ξ m : ℝ) : ℂ) by
      push_cast
      ring]
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, mul_pow,
      hreal (2 * Real.pi), hreal (inner ℝ ξ m)]
  have h1 : (∫ x : ℝ³, ‖∂_{m} f x‖ ^ 2)
      = ∫ ξ : ℝ³, ‖(𝓕 (∂_{m} f)) ξ‖ ^ 2 :=
    (SchwartzMap.integral_norm_sq_fourier (∂_{m} f)).symm
  have h2 : (∫ ξ : ℝ³, ‖(𝓕 (∂_{m} f)) ξ‖ ^ 2)
      = ∫ ξ : ℝ³,
          ‖((2 * Real.pi * Complex.I) • SchwartzMap.smulLeftCLM ℂ (inner ℝ · m) (𝓕 f)) ξ‖ ^ 2 := by
    rw [SchwartzMap.fourier_lineDerivOp_eq f m]
  have h3 : (∫ ξ : ℝ³,
          ‖((2 * Real.pi * Complex.I) • SchwartzMap.smulLeftCLM ℂ (inner ℝ · m) (𝓕 f)) ξ‖ ^ 2)
      = ∫ ξ : ℝ³, (2 * Real.pi) ^ 2 * ((inner ℝ ξ m) ^ 2 * ‖(𝓕 f) ξ‖ ^ 2) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun ξ : ℝ³ => ?_))
    simp only []
    rw [happly ξ, norm_smul, mul_pow, hnorm ξ]
    ring
  have h4 : (∫ ξ : ℝ³, (2 * Real.pi) ^ 2 * ((inner ℝ ξ m) ^ 2 * ‖(𝓕 f) ξ‖ ^ 2))
      = (2 * Real.pi) ^ 2 * ∫ ξ : ℝ³, (inner ℝ ξ m) ^ 2 * ‖(𝓕 f) ξ‖ ^ 2 :=
    MeasureTheory.integral_const_mul ((2 * Real.pi) ^ 2)
      (fun ξ : ℝ³ => (inner ℝ ξ m) ^ 2 * ‖(𝓕 f) ξ‖ ^ 2)
  exact h1.trans (h2.trans (h3.trans h4))

/-- **The orthonormal-basis identity** `Σ_k ⟨ξ, e_k⟩² = ‖ξ‖²` for the coordinate directions. -/
lemma sum_inner_kcStdBasis_sq (ξ : ℝ³) :
    (∑ k : Fin 3, (inner ℝ ξ (kcStdBasis k)) ^ 2) = ‖ξ‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [kcStdBasis, EuclideanSpace.inner_single_right]
  simp [Real.norm_eq_abs, sq_abs]

/-- **Fourier form of the kinetic energy** (the coordinate-sum form, i.e. the corpus's
`kinWord` in the p-space): the `Σ_k` is exchanged with the `x`-integral only in the LHS
(whose integrability is `SchwartzMap.memLp`); the `ξ`-side combination uses
`sum_inner_kcStdBasis_sq` pointwise. -/
theorem integral_fderiv_sq_eq_fourier (f : 𝓢(ℝ³, ℂ)) :
    (∫ x : ℝ³, ∑ k : Fin 3, ‖fderiv ℝ (f : ℝ³ → ℂ) x (kcStdBasis k)‖ ^ 2)
      = (2 * Real.pi) ^ 2 * ∑ k : Fin 3,
          ∫ ξ : ℝ³, (inner ℝ ξ (kcStdBasis k)) ^ 2 * ‖(𝓕 f) ξ‖ ^ 2 := by
  have hInt : ∀ k : Fin 3,
      MeasureTheory.Integrable
        (fun x : ℝ³ => ‖fderiv ℝ (f : ℝ³ → ℂ) x (kcStdBasis k)‖ ^ 2) := by
    intro k
    have hm : MeasureTheory.MemLp (LineDeriv.lineDerivOp (kcStdBasis k) f : ℝ³ → ℂ) 2
        (MeasureTheory.volume : MeasureTheory.Measure ℝ³) :=
      SchwartzMap.memLp _ 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ³)
    rw [MeasureTheory.memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable] at hm
    simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv] using hm
  have hk : ∀ k : Fin 3,
      (∫ x : ℝ³, ‖fderiv ℝ (f : ℝ³ → ℂ) x (kcStdBasis k)‖ ^ 2)
        = (2 * Real.pi) ^ 2 * ∫ ξ : ℝ³,
            (inner ℝ ξ (kcStdBasis k)) ^ 2 * ‖(𝓕 f) ξ‖ ^ 2 := by
    intro k
    simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv] using
      integral_lineDeriv_sq_eq f (kcStdBasis k)
  rw [MeasureTheory.integral_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  exact hk k
  · intro k _
    exact hInt k

end BoseGases
end Submission
