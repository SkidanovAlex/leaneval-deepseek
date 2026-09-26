import Mathlib
import Submission.Work.RadialSpace.RSch
import Submission.Work.RadialSpace.exists_contDiff_comp_sq
import Submission.Work.RadialSpace.schwartz_comp_norm_sq

/-!
# Radial Schwartz functions and even functions of one variable

This file contains the backward direction of CKMRV Lemma 2.6: an even Schwartz
function `g` of one variable gives a radial Schwartz function `x ↦ g ‖x‖` on
`R^n`, and the resulting equivalence between radial Schwartz functions on `R^n`
and even Schwartz functions of one variable.

The analytic input is the factorization of an even smooth function through the
square map (`Work.RadialSpace.exists_contDiff_comp_sq`), which is applied to turn
`x ↦ g ‖x‖` into the composition of a globally smooth function of one variable
with the smooth function `x ↦ ‖x‖ ^ 2`; the decay of the derivatives is
`Work.RadialSpace.schwartz_comp_norm_sq`.

## Main results

* `Work.RadialSpace.contDiff_comp_norm`
* `Work.RadialSpace.exists_schwartz_comp_norm`
* `Work.RadialSpace.rschOfEven`, `Work.RadialSpace.radialSchwartzEquiv`
-/

open Filter Topology
open scoped SchwartzMap Topology ContDiff ENNReal

namespace Work.RadialSpace

open LeanEval.Analysis.CKMRVInterpolation
open Work.Core

variable {n : ℕ} [NeZero n]

/-- If `g` is even and smooth then `x ↦ g ‖x‖` is smooth on `R^n`. -/
theorem contDiff_comp_norm {g : ℝ → ℂ} (hg : ContDiff ℝ Smooth g) (he : Function.Even g) :
    ContDiff ℝ Smooth (fun x : EuclideanSpace ℝ (Fin n) => g ‖x‖) := by
  obtain ⟨h, hh, hgh⟩ := exists_contDiff_comp_sq hg he
  have hfun : (fun x : EuclideanSpace ℝ (Fin n) => g ‖x‖) = fun x => h (‖x‖ ^ 2) :=
    funext fun x => hgh ‖x‖
  rw [hfun]
  simpa [Function.comp_def] using hh.comp (contDiff_norm_sq ℝ)

/-- **CKMRV Lemma 2.6, backward direction.** An even Schwartz function of one
variable composed with the norm is a Schwartz function on `R^n`. -/
theorem exists_schwartz_comp_norm (g : 𝓢(ℝ, ℂ)) (he : ∀ t : ℝ, g (-t) = g t) :
    ∃ F : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), ∀ x, F x = g ‖x‖ := by
  have hg : ContDiff ℝ Smooth (⇑g) := g.smooth'
  obtain ⟨h, hh, hgh⟩ := exists_contDiff_comp_sq hg he
  obtain ⟨F, hF⟩ := schwartz_comp_norm_sq (n := n) g h hh hgh
  exact ⟨F, fun x => (hF x).trans (hgh ‖x‖).symm⟩

/-- The radial Schwartz function on `R^n` attached to an even Schwartz function
of one variable: `x ↦ g ‖x‖`. -/
noncomputable def rschOfEven (n : ℕ) [NeZero n] (g : 𝓢(ℝ, ℂ))
    (he : ∀ t : ℝ, g (-t) = g t) : RSch n :=
  ⟨(exists_schwartz_comp_norm (n := n) g he).choose, by
    have hspec := funext (exists_schwartz_comp_norm (n := n) g he).choose_spec
    rw [show ⇑(exists_schwartz_comp_norm (n := n) g he).choose = fun x => g ‖x‖ from hspec]
    exact radial_comp_norm⟩

lemma rschOfEven_coe (n : ℕ) [NeZero n] (g : 𝓢(ℝ, ℂ)) (he : ∀ t : ℝ, g (-t) = g t)
    (x : EuclideanSpace ℝ (Fin n)) : (rschOfEven n g he).1 x = g ‖x‖ :=
  (exists_schwartz_comp_norm (n := n) g he).choose_spec x

/-- **CKMRV Lemma 2.6, packaged.** Radial complex Schwartz functions on `R^n` are
equivalent to even complex Schwartz functions of one variable, via composition
with the norm. -/
noncomputable def radialSchwartzEquiv (n : ℕ) [NeZero n] :
    RSch n ≃ {g : 𝓢(ℝ, ℂ) // ∀ t : ℝ, g (-t) = g t} where
  toFun f := ⟨rschProfile f, rschProfile_even f⟩
  invFun g := rschOfEven n g.1 g.2
  left_inv f := by
    refine Subtype.ext (SchwartzMap.ext fun x => ?_)
    rw [rschOfEven_coe n, rschProfile_apply]
    exact (profile_eq_of_radial f.2 x).symm
  right_inv g := by
    refine Subtype.ext (SchwartzMap.ext fun t => ?_)
    rw [rschProfile_apply, rschOfEven_coe n, Work.Sampling.realIncl_norm]
    by_cases ht : 0 ≤ t
    · rw [abs_of_nonneg ht]
    · rw [abs_of_neg (not_le.mp ht)]
      exact g.2 t

end Work.RadialSpace
