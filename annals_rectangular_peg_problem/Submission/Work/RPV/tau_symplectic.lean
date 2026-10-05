import Mathlib
import Submission.Work.RPV.Defs

/-!
# `tau θ` is symplectic (`Work.RPV.tau_symplectic`)

`tau θ` is the time-`θ` flow of `K₀` on `PS = T^*ℝ²`: it rotates the `(q₁, p₁)` plane by `θ` and
shifts the angle `q₂` by `θ`.  The node statement says that its differential preserves the
symplectic form `symp = dp₁∧dq₁ + dp₂∧dq₂`:

`symp (fderiv ℝ (tau θ) x a) (fderiv ℝ (tau θ) x b) = symp a b`.

## Proof

`tau θ` is the *affine* map `y ↦ L_θ y + ((0,θ),(0,0))`, where `L_θ` is the linear map rotating
the `(q₁,p₁)` plane and fixing `q₂`, `p₂`.  Hence its derivative at every point is `L_θ`
(`fderiv_tau`), and it remains to check that `symp (L_θ a) (L_θ b) = symp a b` for the explicit
linear map.  Writing the `(q₁,p₁)` block as the rotation matrix
`[[c, -s], [s, c]]` (`c = cos θ`, `s = sin θ`), an expansion gives

`symp (L_θ a) (L_θ b) - symp a b = (c² + s² - 1) * (a^{p₁} b^{q₁} - a^{q₁} b^{p₁})`,

which vanishes because `c² + s² = 1`; `linear_combination` performs exactly this reduction.
-/

set_option autoImplicit false

noncomputable section

namespace Work.RPV

/-! ## The linear part of `tau θ` -/

/-- The linear part of `tau θ`: rotation by `θ` in the `(q₁, p₁)` plane, identity on `q₂`, `p₂`.
The shift `q₂ ↦ q₂ + θ` of `tau` is the constant term, put in by `tau_eq_linear_add`. -/
def tauLinear (θ : ℝ) : PS →L[ℝ] PS :=
  let fst' : PS →L[ℝ] ℝ × ℝ := ContinuousLinearMap.fst ℝ (ℝ × ℝ) (ℝ × ℝ)
  let snd' : PS →L[ℝ] ℝ × ℝ := ContinuousLinearMap.snd ℝ (ℝ × ℝ) (ℝ × ℝ)
  let A : PS →L[ℝ] ℝ := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp fst'
  let B : PS →L[ℝ] ℝ := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp fst'
  let C : PS →L[ℝ] ℝ := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp snd'
  let D : PS →L[ℝ] ℝ := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp snd'
  (((Real.cos θ) • A - (Real.sin θ) • C).prod B).prod
    (((Real.sin θ) • A + (Real.cos θ) • C).prod D)

/-- Coordinates of `tauLinear θ`. -/
lemma tauLinear_apply (θ : ℝ) (x : PS) : tauLinear θ x =
    ((Real.cos θ * x.1.1 - Real.sin θ * x.2.1, x.1.2),
     (Real.sin θ * x.1.1 + Real.cos θ * x.2.1, x.2.2)) := by
  simp [tauLinear, ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
    smul_eq_mul]

/-- `tau θ` is the affine map `y ↦ tauLinear θ y + ((0,θ),(0,0))`. -/
lemma tau_eq_linear_add (θ : ℝ) (x : PS) :
    tau θ x = tauLinear θ x + ((0, θ), (0, 0)) := by
  rw [tauLinear_apply]
  simp only [tau, Prod.mk_add_mk]
  ring_nf

/-- The derivative of `tau θ` at every point is its linear part `tauLinear θ`. -/
lemma fderiv_tau (θ : ℝ) (x : PS) : fderiv ℝ (tau θ) x = tauLinear θ := by
  have h1 : (fun y => tau θ y) = fun y => tauLinear θ y + ((0, θ), (0, 0)) := by
    funext y; exact tau_eq_linear_add θ y
  change fderiv ℝ (fun y => tau θ y) x = tauLinear θ
  rw [h1, fderiv_add_const]
  exact ContinuousLinearMap.fderiv (tauLinear θ)

/-! ## The linear part is symplectic -/

/-- The explicit linear map `tauLinear θ` preserves `symp`. -/
lemma symp_tauLinear (θ : ℝ) (a b : PS) :
    symp (tauLinear θ a) (tauLinear θ b) = symp a b := by
  rw [tauLinear_apply, tauLinear_apply]
  simp only [symp]
  have h : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
  linear_combination (a.2.1 * b.1.1 - a.1.1 * b.2.1) * h

/-! ## The node statement -/

theorem tau_symplectic (θ : ℝ) (x a b : PS) :
    Work.RPV.symp (fderiv ℝ (Work.RPV.tau θ) x a) (fderiv ℝ (Work.RPV.tau θ) x b)
      = Work.RPV.symp a b := by
  rw [fderiv_tau θ x]
  exact symp_tauLinear θ a b

end Work.RPV
