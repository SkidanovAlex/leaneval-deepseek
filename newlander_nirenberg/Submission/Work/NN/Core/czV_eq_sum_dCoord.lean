/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The adjoint field `V` as a sum of `∂`-derivatives of Bochner–Martinelli potentials

The `C⁰`-data `L²` bound `Work.NN.Core.czB_L2_bounded_C0` is proved by duality, and the dual
(adjoint) field of the pairing `φ ↦ Σ_i ∫ z, ∂_i u z * star (φ_i z)` is

  `V_l(w) = ∫ ζ, bmKernel l (ζ - w) * star (θ ζ)`,  `θ = Σ_i ∂̄_i φ_i = czTheta φ`.

The point of this file is the structural description of `V` used to feed the *already proved*
`L²` bound in the `C¹` case: `V_l` is a sum of `∂`-derivatives of Bochner–Martinelli potentials
of the single-component `C¹` compactly supported data `star ∘ φ_i`:

  `czV φ z l = Σ_i ∂_i (bmPotential (singleFam l (star ∘ φ_i))) z`.

The proof combines three ingredients.

* `Work.NN.Core.bmPotential_dCoord_eq` (differentiation of a Bochner–Martinelli potential under
  the integral sign, compactly supported case) applied to the single-component family
  `singleFam l (star ∘ φ_i)`, together with the reduction of the resulting sum to its `l`-th term.
* `czV_dCoord_star_comp`, the identity `∂_i (star ∘ g) = star ∘ ∂̄_i g` (complex conjugation
  intertwines `∂` and `∂̄`).
* Linearity of the Bochner integral over the finite sum `i ↦ bmKernel l · * star (∂̄_i φ_i ·)`,
  which requires the integrability of each summand (`czV_integrable_summand`, from the local
  integrability of the Bochner–Martinelli kernel and the compact support of the data), and the
  translation invariance of Lebesgue measure to pass between `∫ x, … (z + x)` and `∫ ζ, … (ζ - z)`.
-/
import Mathlib
import Submission.Work.NN.Core.czB_C0_defs

noncomputable section

open MeasureTheory Set

namespace Work.NN.Core

open Work.CR.Flat.Cauchy

/-- Complex conjugation intertwines the `(1,0)`- and `(0,1)`-derivatives:
`∂_i (star ∘ g) = star ∘ ∂̄_i g`.  (Version of `Work.NN.Core.dCoord_star_comp` without a
differentiability hypothesis on `g`.) -/
lemma czV_dCoord_star_comp {n : ℕ} (i : Fin n) (g : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) :
    Work.CR.Flat.dCoord i (fun w => star (g w)) z = star (Work.CR.Flat.dbarCoord i g z) := by
  rw [Work.CR.Flat.dCoord, Work.CR.Flat.dbarCoord, fderiv_star]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
  simp only [ContinuousLinearEquiv.coe_coe]
  simp only [starL'_apply]
  have hI : star (Complex.I) = -Complex.I := by
    rw [← starRingEnd_apply, Complex.conj_I]
  have h2 : star (1 / 2 : ℂ) = 1 / 2 := by norm_num
  simp only [star_mul, star_add, hI, h2]
  ring

/-- The conjugate of a `C¹` function is `C¹`. -/
lemma czV_contDiff_star_comp {n : ℕ} {g : (Fin n → ℂ) → ℂ} (hg : ContDiff ℝ 1 g) :
    ContDiff ℝ 1 (fun w => star (g w)) := by
  have hconj : ContDiff ℝ 1 (fun z : ℂ => star z) := by
    have h : ContDiff ℝ 1 (⇑Complex.conjCLE) := Complex.conjCLE.contDiff
    rwa [show (⇑Complex.conjCLE : ℂ → ℂ) = (fun z => star z) from funext (fun z => by
      rw [Complex.conjCLE_apply, starRingEnd_apply])] at h
  simpa only [Function.comp_def] using hconj.comp hg

/-- The conjugate of a compactly supported function has compact support. -/
lemma czV_hasCompactSupport_star_comp {n : ℕ} {g : (Fin n → ℂ) → ℂ}
    (hg : HasCompactSupport g) : HasCompactSupport (fun w => star (g w)) := by
  have h := hg.comp_left (g := fun z : ℂ => star z) (by simp)
  simpa [Function.comp_def] using h

/-- The `(0,1)`-derivative of a `C¹` function is continuous. -/
lemma czV_continuous_dbarCoord_of_contDiff_one {n : ℕ} {g : (Fin n → ℂ) → ℂ}
    (hg : ContDiff ℝ 1 g) (k : Fin n) : Continuous (fun y => Work.CR.Flat.dbarCoord k g y) := by
  have hfd : Continuous (fun y => fderiv ℝ g y) := hg.continuous_fderiv (by norm_num)
  have h1 : Continuous (fun y => fderiv ℝ g y (Pi.single k (1 : ℂ))) :=
    hfd.clm_apply continuous_const
  have h2 : Continuous (fun y => fderiv ℝ g y (Pi.single k Complex.I)) :=
    hfd.clm_apply continuous_const
  have h3 : (fun y => Work.CR.Flat.dbarCoord k g y)
      = fun y => (1 / 2 : ℂ) * (fderiv ℝ g y (Pi.single k (1 : ℂ))
          + Complex.I * fderiv ℝ g y (Pi.single k Complex.I)) := by
    funext y; rfl
  rw [h3]
  exact (h1.add (continuous_const.mul h2)).const_mul (1 / 2 : ℂ)

/-- Each summand `bmKernel l · * star (∂̄_i φ_i (z + ·))` of the adjoint field is integrable:
the local integrability of the Bochner–Martinelli kernel against a continuous compactly
supported function. -/
lemma czV_integrable_summand {n : ℕ} (hn : 0 < n) {φ : Fin n → (Fin n → ℂ) → ℂ}
    (hφ : ∀ i, ContDiff ℝ 1 (φ i)) (hφc : ∀ i, HasCompactSupport (φ i))
    (z : Fin n → ℂ) (l : Fin n) (i : Fin n) :
    Integrable (fun x => Work.CR.Flat.Cauchy.bmKernel l x *
      star (Work.CR.Flat.dbarCoord i (φ i) (z + x))) := by
  have hcont : Continuous (fun y => star (Work.CR.Flat.dbarCoord i (φ i) y)) :=
    continuous_star.comp (czV_continuous_dbarCoord_of_contDiff_one (hφ i) i)
  have hcs : HasCompactSupport (fun y => star (Work.CR.Flat.dbarCoord i (φ i) y)) :=
    czV_hasCompactSupport_star_comp (hasCompactSupport_dbarCoordAux (hφc i) i)
  exact integrable_bmKernel_mul_comp hn l hcont hcs z

theorem czV_eq_sum_dCoord {n : ℕ} (hn : 0 < n)
    {φ : Fin n → (Fin n → ℂ) → ℂ}
    (hφ : ∀ i, ContDiff ℝ 1 (φ i)) (hφc : ∀ i, HasCompactSupport (φ i))
    (z : Fin n → ℂ) (l : Fin n) :
    Work.NN.Core.czV φ z l = ∑ i, Work.CR.Flat.dCoord i
      (Work.CR.Flat.Cauchy.bmPotential (Work.NN.Core.singleFam l (fun w => star (φ i w)))) z := by
  -- Pointwise description of each `∂_i (bmPotential (singleFam l (star ∘ φ_i)))`.
  have hkey : ∀ i, Work.CR.Flat.dCoord i
        (Work.CR.Flat.Cauchy.bmPotential
          (Work.NN.Core.singleFam l (fun w => star (φ i w)))) z
      = ∫ x, Work.CR.Flat.Cauchy.bmKernel l x *
          star (Work.CR.Flat.dbarCoord i (φ i) (z + x)) := by
    intro i
    have hcd : ∀ m, ContDiff ℝ 1 (Work.NN.Core.singleFam l (fun w => star (φ i w)) m) :=
      Work.NN.Core.contDiff_singleFam (czV_contDiff_star_comp (hφ i))
    have hcs : ∀ m, HasCompactSupport (Work.NN.Core.singleFam l (fun w => star (φ i w)) m) :=
      Work.NN.Core.hasCompactSupport_singleFam (czV_hasCompactSupport_star_comp (hφc i))
    have h1 := Work.NN.Core.bmPotential_dCoord_eq hn hcd hcs i z
    -- reduce the sum produced by `bmPotential_dCoord_eq` to its `l`-th term
    have hsingle : (∑ m, ∫ x, Work.CR.Flat.Cauchy.bmKernel m x *
          Work.CR.Flat.dCoord i (Work.NN.Core.singleFam l (fun w => star (φ i w)) m) (z + x))
        = ∫ x, Work.CR.Flat.Cauchy.bmKernel l x *
          Work.CR.Flat.dCoord i (Work.NN.Core.singleFam l (fun w => star (φ i w)) l) (z + x) := by
      rw [Finset.sum_eq_single l]
      · intro m _ hm
        rw [Work.NN.Core.singleFam_of_ne hm]
        simp [Work.CR.Flat.dCoord]
      · intro hl; exact absurd (Finset.mem_univ l) hl
    rw [h1, hsingle]
    simp only [Work.NN.Core.singleFam_self]
    congr 1
    funext x
    rw [czV_dCoord_star_comp]
  -- Linearity of the integral over the finite sum of the summands.
  have hsum : (∑ i, ∫ x, Work.CR.Flat.Cauchy.bmKernel l x *
        star (Work.CR.Flat.dbarCoord i (φ i) (z + x)))
      = ∫ x, Work.CR.Flat.Cauchy.bmKernel l x *
          star (∑ i, Work.CR.Flat.dbarCoord i (φ i) (z + x)) := by
    rw [show (∫ x, Work.CR.Flat.Cauchy.bmKernel l x *
            star (∑ i, Work.CR.Flat.dbarCoord i (φ i) (z + x)))
        = ∫ x, ∑ i, Work.CR.Flat.Cauchy.bmKernel l x *
            star (Work.CR.Flat.dbarCoord i (φ i) (z + x)) from by
      congr 1
      funext x
      rw [star_sum, Finset.mul_sum]]
    exact (MeasureTheory.integral_finsetSum (Finset.univ)
      (fun i _ => czV_integrable_summand hn hφ hφc z l i)).symm
  rw [Finset.sum_congr rfl (fun i _ => hkey i), hsum]
  -- Move to the translated form and identify `Σ_i ∂̄_i φ_i` with `czTheta φ`.
  rw [Work.NN.Core.czV_apply]
  have hshift := MeasureTheory.integral_sub_right_eq_self (μ := volume)
    (fun y : Fin n → ℂ => Work.CR.Flat.Cauchy.bmKernel l y *
      star (Work.NN.Core.czTheta φ (z + y))) z
  simp only [add_sub_cancel] at hshift
  exact hshift

end Work.NN.Core
