/-
# `Assembly/ProdDeriv.lean` — the `D`-calculus of the product ansatz

For a product `f z θ = ψ z * g θ` the operators `D_z = z ∂_z`, `D_θ = sin(2θ) ∂_θ` act on
the two factors separately:

* `DzIter j (fun z θ => ψ z * g θ) = fun z θ => vzIter j ψ z * g θ` (`DzIter_prod`);
* `DthIter i (fun z θ => ψ z * g θ) = fun z θ => ψ z * vthIter i g θ` (`DthIter_prod`), hence
* `mixed j i (fun z θ => ψ z * g θ) = fun z θ => vzIter j ψ z * vthIter i g θ`
  (`mixed_prod`).

All three are stated for `C^∞` (`Work.Stability.smoothOrder`) factors, the regularity needed
for the iterated `deriv` of the one-variable factors.  This gives, in particular, the
identities used by the counterexample:
`D_z^j D_θ f = (vzIter j ψ)·(vthIter 1 h)` and `D_θ^i f = ψ·(vthIter i h)`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.CoercivityFix.Assembly.AnsatzDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Assembly

set_option autoImplicit false

/-- `deriv` of a `C^∞`-function is `C^∞` (the `∞`-order instance of
`ContDiff.iterate_deriv`). -/
theorem contDiff_deriv_of {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ Work.Stability.smoothOrder ψ) :
    ContDiff ℝ Work.Stability.smoothOrder (deriv ψ) := by
  have h : ContDiff ℝ Work.Stability.smoothOrder (deriv^[1] ψ) :=
    ContDiff.iterate_deriv 1 hψ
  simpa using h

/-- `vz` preserves `C^∞`-smoothness. -/
theorem contDiff_vz {ψ : ℝ → ℝ} (hψ : ContDiff ℝ Work.Stability.smoothOrder ψ) :
    ContDiff ℝ Work.Stability.smoothOrder (vz ψ) := by
  have := (contDiff_id (𝕜 := ℝ)).mul (contDiff_deriv_of hψ)
  exact this

/-- `vzIter` preserves `C^∞`-smoothness. -/
theorem contDiff_vzIter (ψ : ℝ → ℝ) (hψ : ContDiff ℝ Work.Stability.smoothOrder ψ)
    (j : ℕ) : ContDiff ℝ Work.Stability.smoothOrder (vzIter j ψ) := by
  induction j with
  | zero => simpa using hψ
  | succ j ih => simpa [vzIter_succ] using contDiff_vz ih

/-- `vth` preserves `C^∞`-smoothness. -/
theorem contDiff_vth {g : ℝ → ℝ} (hg : ContDiff ℝ Work.Stability.smoothOrder g) :
    ContDiff ℝ Work.Stability.smoothOrder (vth g) := by
  have hsin : ContDiff ℝ Work.Stability.smoothOrder (fun θ : ℝ => Real.sin (2 * θ)) :=
    Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)
  have := hsin.mul (contDiff_deriv_of hg)
  exact this

/-- `vthIter` preserves `C^∞`-smoothness. -/
theorem contDiff_vthIter (g : ℝ → ℝ) (hg : ContDiff ℝ Work.Stability.smoothOrder g)
    (i : ℕ) : ContDiff ℝ Work.Stability.smoothOrder (vthIter i g) := by
  induction i with
  | zero => simpa using hg
  | succ i ih => simpa [vthIter_succ] using contDiff_vth ih

theorem smoothOrder_ne_zero : Work.Stability.smoothOrder ≠ 0 := by
  simp [Work.Stability.smoothOrder]

/-- The iterated `D_z` of a product, on the first factor. -/
theorem DzIter_prod (j : ℕ) (ψ g : ℝ → ℝ)
    (hψ : ContDiff ℝ Work.Stability.smoothOrder ψ) :
    Work.Spaces.DzIter j (fun z θ => ψ z * g θ)
      = fun z θ => vzIter j ψ z * g θ := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Work.Spaces.DzIter_succ, ih]
      funext z θ
      show z * deriv (fun z' => vzIter j ψ z' * g θ) z = vzIter (j + 1) ψ z * g θ
      rw [deriv_mul_const ((contDiff_vzIter ψ hψ j).differentiable
        smoothOrder_ne_zero).differentiableAt]
      rw [vzIter_succ, vz]
      ring

/-- The iterated `D_θ` of a product, on the second factor. -/
theorem DthIter_prod (i : ℕ) (ψ g : ℝ → ℝ)
    (hg : ContDiff ℝ Work.Stability.smoothOrder g) :
    Work.Spaces.DthIter i (fun z θ => ψ z * g θ)
      = fun z θ => ψ z * vthIter i g θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Work.Spaces.DthIter_succ, ih]
      funext z θ
      show Real.sin (2 * θ) * deriv (fun θ' => ψ z * vthIter i g θ') θ
        = ψ z * vthIter (i + 1) g θ
      rw [deriv_const_mul (ψ z) ((contDiff_vthIter g hg i).differentiable
        smoothOrder_ne_zero).differentiableAt]
      rw [vthIter_succ, vth]
      ring

/-- The iterated mixed derivative of a product. -/
theorem mixed_prod (j i : ℕ) (ψ g : ℝ → ℝ)
    (hψ : ContDiff ℝ Work.Stability.smoothOrder ψ)
    (hg : ContDiff ℝ Work.Stability.smoothOrder g) :
    Work.Spaces.mixed j i (fun z θ => ψ z * g θ)
      = fun z θ => vzIter j ψ z * vthIter i g θ := by
  rw [Work.Spaces.mixed, DthIter_prod i ψ g hg,
    DzIter_prod j ψ (vthIter i g) hψ]

end Work.FTS.CoercivityFix.Assembly
