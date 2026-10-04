import Mathlib
import Submission.Work.Diff.STE.B3.VarCoef.OpOrder
import Submission.Work.Diff.STE.B3.SymCalcStep8.pd_CSqZ_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The partial derivative `∂ᵢ` is an operator of order `1` (`VarCoef` layer)

This file proves `Work.Diff.STE.B3.VarCoef.pdOp_isOrd`: the `i`-th partial derivative
`pdOp i = fun f => ∂ᵢ f` belongs to the order calculus of `VarCoef/OpOrder.lean` with order `1` and
the *constant* constant function `C t = 4π²` (independent of `t`).

The three ingredients of `IsOrd 1 C (pdOp i)`:

* `Preserves`: `∂ᵢ` maps smooth `1`-periodic functions to smooth `1`-periodic functions
  (`pd_contDiff_top`, `pd_periodic1`);
* `LinSP`: `∂ᵢ` is additive and `ℂ`-homogeneous on them (`pd_add_fn`, `pd_smul_fn`, from the
  additivity/`smul` rules for `fderiv`);
* the order bound `CSqZ (t - 1) (fourierCoeff (∂ᵢ f)) ≤ 4π² · CSqZ t (fourierCoeff f)`, which is
  `Work.Diff.STE.B3.SymCalcStep8.pd_CSqZ_le` (the Fourier multiplier of `∂ᵢ` is `m ↦ 2πi mᵢ`, and
  `(2π mᵢ)² ≤ 4π² ⟨m⟩`) with the exponent shifted by one.
-/

noncomputable section

namespace Work.Diff.STE.B3.VarCoef

/-! ## Regularity of a partial derivative -/

/-- A partial derivative of a smooth function is smooth (the top level `⊤ : ℕ∞`, i.e. `∞`, is
fixed by `fderiv`). -/
theorem pd_contDiff_top {ι : Type*} [Fintype ι] [DecidableEq ι] {f : (ι → ℝ) → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : ι) : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.pd i f) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) := hf.fderiv_right (m := (⊤ : ℕ∞)) (by norm_num)
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun x : ι → ℝ => (fderiv ℝ f x) (Pi.single i 1)) :=
    h1.clm_apply contDiff_const
  rw [show Work.Diff.STE.pd i f = (fun x : ι → ℝ => (fderiv ℝ f x) (Pi.single i 1)) from rfl]
  exact h2

/-- A partial derivative of a `1`-periodic function is `1`-periodic.  No differentiability is
needed: `fderiv_comp_add_right` holds unconditionally (both sides are the junk value `0` where `f`
is not differentiable). -/
theorem pd_periodic1 {ι : Type*} [Fintype ι] [DecidableEq ι] {f : (ι → ℝ) → ℂ}
    (hf : Work.Diff.STE.Periodic1 f) (i : ι) :
    Work.Diff.STE.Periodic1 (Work.Diff.STE.pd i f) := by
  intro j x
  have hfun : (fun y : ι → ℝ => f (y + Pi.single j (1 : ℝ))) = f := funext (hf j)
  have h : fderiv ℝ f (x + Pi.single j (1 : ℝ)) = fderiv ℝ f x := by
    rw [← fderiv_comp_add_right (f := f) (x := x) (Pi.single j (1 : ℝ)), hfun]
  simp only [Work.Diff.STE.pd]
  rw [h]

/-! ## Linearity of a partial derivative -/

/-- `pd` is additive on differentiable functions. -/
theorem pd_add_fn {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) (f g : (ι → ℝ) → ℂ)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    Work.Diff.STE.pd i (f + g) = Work.Diff.STE.pd i f + Work.Diff.STE.pd i g := by
  funext x
  show fderiv ℝ (f + g) x (Pi.single i 1)
    = fderiv ℝ f x (Pi.single i 1) + fderiv ℝ g x (Pi.single i 1)
  rw [fderiv_add (hf x) (hg x), add_apply]

/-- `pd` commutes with multiplication by a constant. -/
theorem pd_smul_fn {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) (c : ℂ)
    {f : (ι → ℝ) → ℂ} (hf : Differentiable ℝ f) :
    Work.Diff.STE.pd i (c • f) = c • Work.Diff.STE.pd i f := by
  funext x
  show fderiv ℝ (c • f) x (Pi.single i 1) = (c • Work.Diff.STE.pd i f) x
  rw [show fderiv ℝ (c • f) x = fderiv ℝ (fun y : ι → ℝ => c • f y) x from rfl]
  rw [fderiv_fun_const_smul (hf x) c]
  simp [Work.Diff.STE.pd]

/-! ## The operator `pdOp i` in the order calculus -/

theorem pdOp_preserves {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    Preserves (pdOp i) := by
  intro f hf
  exact ⟨pd_contDiff_top hf.1 i, pd_periodic1 hf.2 i⟩

theorem linSP_pdOp {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) : LinSP (pdOp i) where
  add f g hf hg := by
    have hf' : Differentiable ℝ f := hf.1.differentiable (by simp)
    have hg' : Differentiable ℝ g := hg.1.differentiable (by simp)
    simpa only [pdOp] using pd_add_fn i f g hf' hg'
  smul c f hf := by
    have hf' : Differentiable ℝ f := hf.1.differentiable (by simp)
    simpa only [pdOp] using pd_smul_fn i c hf'

theorem pdOp_isOrd {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    ∃ C : ℤ → ℝ, Work.Diff.STE.B3.VarCoef.IsOrd 1 C (Work.Diff.STE.B3.VarCoef.pdOp i) := by
  refine isOrd_of_pointwise (pdOp_preserves i) (linSP_pdOp i) ?_
  intro t
  obtain ⟨C, hC0, hC⟩ := Work.Diff.STE.B3.SymCalcStep8.pd_CSqZ_le i (t - 1)
  refine ⟨C, hC0, ?_⟩
  intro f hf
  have h := hC f hf.1 hf.2
  simpa only [pdOp, sub_add_cancel] using h

end Work.Diff.STE.B3.VarCoef
