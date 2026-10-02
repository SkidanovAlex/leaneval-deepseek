/-
Work.MRMT.Found — auxiliary vocabulary for the smooth case of the principal solution.

The main theorem of `Found/exists_contDiff_principal_of_contDiff.lean` (a `C¹` diffeomorphism of
`ℂ` solving the Beltrami equation for a smooth compactly supported coefficient `μ` with
`‖μ‖ ≤ k < 1`) is proved by the classical Ahlfors–Bers construction: the solution is `z + C h`
where `h` is the `L²` solution of the Ahlfors–Bers equation `h = μ (1 + S h)` (`S` the Beurling
transform) and `C` the Cauchy transform.  The smoothness of the map comes from the fact that for
*smooth* coefficients this `L²` solution is `C^∞`.

This file collects the definitions used to state the intermediate lemmas:

* `mulL2Canon μ` — multiplication by `μ` on `L²(ℂ)`, in a form that does not carry the
  measurability and a.e.-boundedness proofs as arguments;
* `qsol μ m` — the `L²` solution of the *inhomogeneous* Ahlfors–Bers equation `q = m + μ S q`
  (the case `m = μ` recovers `hsol`); it is needed to run Ahlfors' trick (the exponential
  `e^{-σ}` with `σ = C q`, where `q` solves the equation with source `m = ∂μ`) in the proof that
  `dz F` has no zeros.
-/
import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Cauchy.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Filter Topology Complex Function
open scoped Distributions Topology ENNReal

namespace Work.MRMT.Found

/-! ## The inhomogeneous Ahlfors–Bers equation -/

/-- Multiplication by `μ` on `L²(ℂ)`, in a form that avoids carrying the measurability and
a.e.-boundedness proofs as arguments: it is `mulL2 μ` whenever those hold, and `0` otherwise. -/
noncomputable def mulL2Canon (μ : ℂ → ℂ) :
    Lp ℂ 2 (volume : Measure ℂ) →L[ℂ] Lp ℂ 2 (volume : Measure ℂ) := by
  classical
  exact if _h : AEStronglyMeasurable μ (volume : Measure ℂ) ∧
      ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ 1 then
    mulL2 μ _h.1 _h.2
  else 0

theorem mulL2Canon_eq (μ : ℂ → ℂ) (hm : AEStronglyMeasurable μ (volume : Measure ℂ))
    (h1 : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ 1) :
    mulL2Canon μ = mulL2 μ hm h1 := by
  rw [mulL2Canon]
  exact dite_eq_left ⟨hm, h1⟩

theorem mulL2Canon_eq_mulL2_aux (μ : ℂ → ℂ) (hm hm' : AEStronglyMeasurable μ (volume : Measure ℂ))
    (h1 : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ 1)
    (h1' : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ 1) :
    mulL2 μ hm h1 = mulL2 μ hm' h1' := by
  refine ContinuousLinearMap.ext fun f => Lp.ext ?_
  filter_upwards [mulL2_apply_ae μ hm h1 f, mulL2_apply_ae μ hm' h1' f] with z hz hz'
  simp only [hz, hz']

theorem mulL2Canon_apply_ae (μ : ℂ → ℂ) (hm : AEStronglyMeasurable μ (volume : Measure ℂ))
    (h1 : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ 1)
    (f : Lp ℂ 2 (volume : Measure ℂ)) :
    (((mulL2Canon μ) f : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ)
      =ᵐ[(volume : Measure ℂ)] fun z => μ z * ((f : ℂ → ℂ) z) := by
  rw [mulL2Canon_eq μ hm h1]
  exact mulL2_apply_ae μ hm h1 f

/-- The `L²` solution of the inhomogeneous Ahlfors–Bers equation `q = m + μ · S q`, where `S` is
the Beurling transform on `L²(ℂ)`: the Neumann series `∑ₙ (M_μ S)ⁿ m`. -/
noncomputable def qsol (μ m : ℂ → ℂ) (hm : MemLp m 2 (volume : Measure ℂ)) :
    Lp ℂ 2 (volume : Measure ℂ) :=
  Ring.inverse (1 - (mulL2Canon μ).comp beurlingL2) (hm.toLp m)

/-- `hsol` agrees with `qsol` for the source `m = μ`. -/
theorem hsol_eq_qsol (μ : ℂ → ℂ) (hm : AEStronglyMeasurable μ (volume : Measure ℂ))
    (h1 : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ 1) (hLp : MemLp μ 2 (volume : Measure ℂ)) :
    hsol μ hm h1 hLp = qsol μ μ hLp := by
  unfold qsol hsol
  rw [mulL2Canon_eq μ hm h1]


/-- The weight `(1 + ‖ξ‖²)²` used in the Fourier-side formulation of the regularity of `L²`
solutions: `∫ (1+‖ξ‖²)⁴ |𝓕q|² < ∞` (the conclusion of four difference quotients) is equivalent
to the weighted Fourier transform `ξ ↦ (1+‖ξ‖²)² 𝓕q(ξ)` being in `L²`. -/
def fourierWeight (ξ : ℂ) : ℂ := ((1 + ‖ξ‖ ^ 2) ^ 2 : ℝ)

@[simp] theorem fourierWeight_apply (ξ : ℂ) : fourierWeight ξ = ((1 + ‖ξ‖ ^ 2) ^ 2 : ℝ) := rfl


/-- The `n`-th difference operator of `L²(ℂ)` with step `t`: `(τ_t - 1)^n`. -/
noncomputable def diffOp (t : ℂ) (n : ℕ) :
    Lp ℂ 2 (volume : Measure ℂ) →L[ℂ] Lp ℂ 2 (volume : Measure ℂ) :=
  (translateL2 t - 1) ^ n

theorem diffOp_apply (t : ℂ) (n : ℕ) (f : Lp ℂ 2 (volume : Measure ℂ)) :
    diffOp t n f = ((translateL2 t - 1) ^ n) f := rfl

end Work.MRMT.Found
