import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixR.ChiR0Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.LocaliseGradWideDefs` — the cutoff `η` for `LocaliseGradWideNow`

This module fixes the *definitions* used by the proof of
`Work.BoseFixR.LocaliseGradWideNow` and by the auxiliary lemmas delegated for it.

## The objects

For `ℓ > 0` we use the radial cutoff

  `etaOf ℓ x = Phi (‖x‖² / ℓ²)`,  `Phi u = Real.smoothTransition ((4 - u)/3)`

where `Real.smoothTransition` is Mathlib's `C^∞` step (`0` on `(-∞,0]`, `1` on `[1,∞)`).
Thus

* `etaOf ℓ = 1` on the closed ball of radius `ℓ` (indeed `Phi u = 1` for `u ≤ 1`);
* `0 ≤ etaOf ℓ ≤ 1`;
* `etaOf ℓ` is `C^∞` (hence `C²`) and compactly supported, with support in the ball of
  radius `2ℓ` (indeed `Phi u = 0` for `u ≥ 4`);
* `deriv Phi u = 0` for `u > 4`, so `gradient (etaOf ℓ) x = 0` for `‖x‖ > 2ℓ`.

## Constants used in `LocaliseGradWideNow`

The final inequality has the constant `4000`.  The two ingredients are

* the *lattice multiplicity* of the support: for `y ∈ cell ℓ` and `n : Fin 3 → ℤ` with
  `η (y + lat ℓ n) ≠ 0` one must have `‖y + lat ℓ n‖ ≤ 2ℓ`, hence `‖lat ℓ n‖ ≤ 2ℓ + (√3/2)ℓ`,
  i.e. `|n i| ≤ 2` for all `i`: at most `5³ = 125` lattice points.
* the *derivative bound* `‖gradient (etaOf ℓ) x‖² ≤ 15 / ℓ²`, obtained from
  `|deriv Phi u| ≤ (1/3) * (45/16) = 15/16` (see `Work.BoseFixR.LGW.STDerivBound`) and
  `‖gradient (fun x => ‖x‖²/ℓ²) x‖ = 2‖x‖/ℓ² ≤ 4/ℓ` (which holds whenever the first factor
  is non-zero, since then `‖x‖ ≤ 2ℓ`).

The chain of inequalities in `LocaliseGradWideNow` is then

  `∫ ‖∇(η φ)‖² ≤ 2 ∫ η² ‖∇φ‖² + 2 ∫ φ² ‖∇η‖²`
  `            ≤ 2·125·∫_{box} ‖∇φ‖² + 2·125·(15/ℓ²)·∫_{box} φ²`
  `            = 250·I₁ + 3750·ℓ⁻²·I₂  ≤ 4000·(I₁ + ℓ⁻²·I₂)`.

The first inequality is the elementary `‖a + b‖² ≤ 2‖a‖² + 2‖b‖²` applied to the gradient
product rule `∇(ηφ) = η ∇φ + φ ∇η`; the second is the periodisation lemma
`Work.BoseFixR.LGW.PeriodiseLe`, which bounds `∫_{ℝ³} g·u` for a compactly supported `g`
vanishing outside the ball of radius `2ℓ` and an `ℓ`-periodic nonnegative `u` by
`125 · (sup g) · ∫_{cell ℓ} u`.
-/

noncomputable section

open scoped Real Topology BigOperators Pointwise
open MeasureTheory

namespace Work.BoseFixR

/-- The radial profile of the cutoff: `1` for `u ≤ 1`, `0` for `u ≥ 4`, and a `C^∞` sigmoid
in between.  (`Real.smoothTransition` is `0` on `(-∞,0]` and `1` on `[1,∞)`.) -/
def Phi (u : ℝ) : ℝ := Real.smoothTransition ((4 - u) / 3)

/-- The (squared) radial variable `ψ(x) = ‖x‖² / ℓ²`, written as a polynomial in the
coordinates so that it is `C^∞` and its Fréchet derivative is easy to compute. -/
def psiOf (ℓ : ℝ) (x : EuclideanSpace ℝ (Fin 3)) : ℝ := (∑ i, x i ^ 2) / ℓ ^ 2

/-- The cutoff `η_ℓ(x) = Phi (‖x‖²/ℓ²)`. -/
def etaOf (ℓ : ℝ) (x : EuclideanSpace ℝ (Fin 3)) : ℝ := Phi (psiOf ℓ x)

@[simp] lemma Phi_apply (u : ℝ) : Phi u = Real.smoothTransition ((4 - u) / 3) := rfl

@[simp] lemma etaOf_apply (ℓ : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    etaOf ℓ x = Phi (psiOf ℓ x) := rfl

lemma Phi_eq_one {u : ℝ} (hu : u ≤ 1) : Phi u = 1 := by
  rw [Phi, Real.smoothTransition.one_of_one_le]
  linarith

lemma Phi_eq_zero {u : ℝ} (hu : 4 ≤ u) : Phi u = 0 := by
  rw [Phi, Real.smoothTransition.zero_of_nonpos]
  linarith

lemma Phi_mem (u : ℝ) : 0 ≤ Phi u ∧ Phi u ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

lemma psiOf_eq (ℓ : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    psiOf ℓ x = (∑ i, x i ^ 2) / ℓ ^ 2 := rfl

lemma psiOf_nonneg (ℓ : ℝ) (x : EuclideanSpace ℝ (Fin 3)) : 0 ≤ psiOf ℓ x :=
  div_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) (sq_nonneg _)

lemma psiOf_eq_norm_sq {ℓ : ℝ} (hℓ : ℓ ≠ 0) (x : EuclideanSpace ℝ (Fin 3)) :
    psiOf ℓ x = ‖x‖ ^ 2 / ℓ ^ 2 := by
  rw [psiOf_eq, EuclideanSpace.real_norm_sq_eq]

lemma etaOf_mem (ℓ : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    0 ≤ etaOf ℓ x ∧ etaOf ℓ x ≤ 1 := Phi_mem _

lemma etaOf_eq_one {ℓ : ℝ} (hℓ : 0 < ℓ) {x : EuclideanSpace ℝ (Fin 3)} (hx : ‖x‖ ≤ ℓ) :
    etaOf ℓ x = 1 := by
  apply Phi_eq_one
  rw [psiOf_eq_norm_sq hℓ.ne']
  rw [div_le_one (by positivity)]
  nlinarith [norm_nonneg x, hx]

lemma etaOf_eq_zero {ℓ : ℝ} (hℓ : 0 < ℓ) {x : EuclideanSpace ℝ (Fin 3)} (hx : 2 * ℓ ≤ ‖x‖) :
    etaOf ℓ x = 0 := by
  apply Phi_eq_zero
  rw [psiOf_eq_norm_sq hℓ.ne']
  rw [le_div_iff₀ (by positivity)]
  nlinarith [norm_nonneg x, hx]

end Work.BoseFixR
