import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Submission.Work.FTS.RegPkgGal.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.RegPkgGal.R1b

open Set Filter Topology MeasureTheory
open scoped Topology Real

set_option autoImplicit false

/-! ## The local objects -/

/-- The `θ`-slice of the family, as a function on the `(z,τ)`-plane. -/
noncomputable def baseFn (g : ℝ → ℝ → ℝ → ℝ) (θ : ℝ) : ℝ × ℝ → ℝ := fun q => g q.1 θ q.2

/-- The `τ`-derivative of the family at `τ = 0`, as a function of `z`. -/
noncomputable def tauDer (g : ℝ → ℝ → ℝ → ℝ) (θ : ℝ) : ℝ → ℝ :=
  fun z => deriv (fun s => g z θ s) 0

/-- `tauDer`, viewed as a function on the `(z,τ)`-plane (constant in `τ`). -/
noncomputable def tauDerFn (g : ℝ → ℝ → ℝ → ℝ) (θ : ℝ) : ℝ × ℝ → ℝ := fun q => tauDer g θ q.1

/-- The first-order Taylor jet of the family in `τ` at `τ = 0`: the `τ < 0` branch of `extG`. -/
noncomputable def jetFn (g : ℝ → ℝ → ℝ → ℝ) (θ : ℝ) : ℝ × ℝ → ℝ :=
  fun q => g q.1 θ 0 + q.2 * tauDer g θ q.1

/-- The extension `extG g · θ ·`, as a function on the `(z,τ)`-plane. -/
noncomputable def extFun (g : ℝ → ℝ → ℝ → ℝ) (θ : ℝ) : ℝ × ℝ → ℝ :=
  fun q => Work.FTS.RegPkgGal.extG g q.1 θ q.2

/-- The candidate derivative of the extension.  For `z ≤ 0` the extension vanishes identically
nearby, so the derivative is `0`; for `z > 0` it is the Fréchet derivative of the branch
(`jetFn` for `τ < 0`, `baseFn` for `τ ≥ 0`), written in terms of the two partial derivatives. -/
noncomputable def extDeriv (g : ℝ → ℝ → ℝ → ℝ) (θ : ℝ) : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] ℝ) :=
  fun q =>
    if q.1 ≤ 0 then 0
    else if q.2 < 0 then
      (deriv (fun z => jetFn g θ (z, q.2)) q.1) • ContinuousLinearMap.fst ℝ ℝ ℝ
        + (deriv (fun t => jetFn g θ (q.1, t)) q.2) • ContinuousLinearMap.snd ℝ ℝ ℝ
    else
      (deriv (fun z => baseFn g θ (z, q.2)) q.1) • ContinuousLinearMap.fst ℝ ℝ ℝ
        + (deriv (fun t => baseFn g θ (q.1, t)) q.2) • ContinuousLinearMap.snd ℝ ℝ ℝ

@[simp] theorem baseFn_apply (g : ℝ → ℝ → ℝ → ℝ) (θ z τ : ℝ) :
    baseFn g θ (z, τ) = g z θ τ := rfl

@[simp] theorem tauDerFn_apply (g : ℝ → ℝ → ℝ → ℝ) (θ z τ : ℝ) :
    tauDerFn g θ (z, τ) = tauDer g θ z := rfl

@[simp] theorem jetFn_apply (g : ℝ → ℝ → ℝ → ℝ) (θ z τ : ℝ) :
    jetFn g θ (z, τ) = g z θ 0 + τ * tauDer g θ z := rfl

@[simp] theorem extFun_apply (g : ℝ → ℝ → ℝ → ℝ) (θ z τ : ℝ) :
    extFun g θ (z, τ) = Work.FTS.RegPkgGal.extG g z θ τ := rfl

@[simp] theorem extDeriv_of_nonpos (g : ℝ → ℝ → ℝ → ℝ) (θ : ℝ) {z : ℝ} (hz : z ≤ 0) (τ : ℝ) :
    extDeriv g θ (z, τ) = 0 := by
  simp only [extDeriv]
  rw [if_pos hz]

theorem extDeriv_of_pos_of_neg (g : ℝ → ℝ → ℝ → ℝ) (θ : ℝ) {z τ : ℝ} (hz : 0 < z) (hτ : τ < 0) :
    extDeriv g θ (z, τ)
      = (deriv (fun z' => jetFn g θ (z', τ)) z) • ContinuousLinearMap.fst ℝ ℝ ℝ
        + (deriv (fun t => jetFn g θ (z, t)) τ) • ContinuousLinearMap.snd ℝ ℝ ℝ := by
  simp only [extDeriv]
  rw [if_neg (not_le.mpr hz), if_pos hτ]

theorem extDeriv_of_pos_of_nonneg (g : ℝ → ℝ → ℝ → ℝ) (θ : ℝ) {z τ : ℝ} (hz : 0 < z)
    (hτ : 0 ≤ τ) :
    extDeriv g θ (z, τ)
      = (deriv (fun z' => baseFn g θ (z', τ)) z) • ContinuousLinearMap.fst ℝ ℝ ℝ
        + (deriv (fun t => baseFn g θ (z, t)) τ) • ContinuousLinearMap.snd ℝ ℝ ℝ := by
  simp only [extDeriv]
  rw [if_neg (not_le.mpr hz), if_neg (not_lt.mpr hτ)]

/-! ## The extension as a piecewise function -/

theorem extFun_of_nonpos (g : ℝ → ℝ → ℝ → ℝ) (θ : ℝ) {z τ : ℝ} (hz : z ≤ 0) :
    extFun g θ (z, τ) = 0 := by
  simp only [extFun_apply]
  exact extG_of_nonpos hz

theorem extFun_of_pos_of_nonneg (g : ℝ → ℝ → ℝ → ℝ) (θ : ℝ) {z τ : ℝ} (hz : 0 < z)
    (hτ : 0 ≤ τ) : extFun g θ (z, τ) = baseFn g θ (z, τ) := by
  simp only [extFun_apply, baseFn_apply]
  exact extG_of_pos hz hτ

theorem extFun_of_pos_of_neg (g : ℝ → ℝ → ℝ → ℝ) (θ : ℝ) {z τ : ℝ} (hz : 0 < z) (hτ : τ < 0) :
    extFun g θ (z, τ) = jetFn g θ (z, τ) := by
  simp only [extFun_apply, jetFn_apply]
  rw [extG_of_neg hz hτ]
  simp only [tauDer]

/-- At `τ = 0` the jet agrees with the family. -/
theorem jetFn_eq_baseFn_at_zero (g : ℝ → ℝ → ℝ → ℝ) (θ z : ℝ) :
    jetFn g θ (z, 0) = baseFn g θ (z, 0) := by
  simp only [jetFn_apply, baseFn_apply]
  ring


noncomputable def jetBranch (g : ℝ → ℝ → ℝ → ℝ) (θ : ℝ) : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] ℝ) :=
  fun q => (deriv (fun z => jetFn g θ (z, q.2)) q.1) • ContinuousLinearMap.fst ℝ ℝ ℝ
    + (deriv (fun t => jetFn g θ (q.1, t)) q.2) • ContinuousLinearMap.snd ℝ ℝ ℝ

/-- The `τ ≥ 0` branch of the candidate derivative. -/
noncomputable def baseBranch (g : ℝ → ℝ → ℝ → ℝ) (θ : ℝ) : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] ℝ) :=
  fun q => (deriv (fun z => baseFn g θ (z, q.2)) q.1) • ContinuousLinearMap.fst ℝ ℝ ℝ
    + (deriv (fun t => baseFn g θ (q.1, t)) q.2) • ContinuousLinearMap.snd ℝ ℝ ℝ

theorem extDeriv_of_pos_of_neg' (g : ℝ → ℝ → ℝ → ℝ) (θ : ℝ) {z τ : ℝ} (hz : 0 < z)
    (hτ : τ < 0) : extDeriv g θ (z, τ) = jetBranch g θ (z, τ) :=
  extDeriv_of_pos_of_neg g θ hz hτ

theorem extDeriv_of_pos_of_nonneg' (g : ℝ → ℝ → ℝ → ℝ) (θ : ℝ) {z τ : ℝ} (hz : 0 < z)
    (hτ : 0 ≤ τ) : extDeriv g θ (z, τ) = baseBranch g θ (z, τ) :=
  extDeriv_of_pos_of_nonneg g θ hz hτ

end Work.FTS.RegPkgGal.R1b
