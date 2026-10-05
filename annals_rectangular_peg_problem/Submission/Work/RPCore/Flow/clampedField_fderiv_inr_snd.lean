import Mathlib
import Submission.Work.RPCore.Flow.HamFlow
import Submission.Work.RPCore.Flow.clampedField_bounds

/-!
# The vertical derivative of the clamped field

The autonomous field of the time-clamped Hamiltonian is

`clampedField Hh z = (1, X_{clampHam Hh z.1} z.2)`

on `ℝ × PS`.  Its first coordinate is constant, so its Fréchet derivative in *any* direction has
vanishing first coordinate.  Here we compute the second coordinate of the derivative in a
*vertical* direction `(0, δ) = inr ℝ ℝ PS δ`:

`(fderiv ℝ (clampedField Hh) z (inr δ)).2 = fderiv ℝ (hamVF (clampHam Hh z.1)) z.2 δ`,

i.e. the vertical derivative of the autonomous field is the derivative of the time-`z.1` slice.

The proof is the chain rule in two steps.

* Write `clampedSlice Hh z = X_{clampHam Hh z.1} z.2` for the second coordinate of the field.  It
  is `C³`: it is the "partial Hamiltonian vector field" `z ↦ hamVF (fun y => U (z.1, y)) z.2` of
  the uncurried clamped Hamiltonian `U z = clampHam Hh z.1 z.2`, which is `C⁴`
  (`contDiff_hamVF_partial` applied to `U`).
* Since `clampedField Hh z = (1, clampedSlice Hh z)` has *constant* first coordinate, its
  derivative at `z` is `(0).prod (fderiv ℝ (clampedSlice Hh) z)`, and reading the second
  coordinate of the value on `inr δ` gives `fderiv ℝ (clampedSlice Hh) z (inr δ)`.
* On the other hand the vertical slice `x ↦ clampedSlice Hh (z.1, x)` of `clampedSlice Hh` is the
  composite of `clampedSlice Hh` with `x ↦ (z.1, x)`, whose derivative at `z.2` is
  `ContinuousLinearMap.inr ℝ ℝ PS`; the chain rule turns that into
  `fderiv ℝ (clampedSlice Hh) z (inr δ) = fderiv ℝ (fun x => clampedSlice Hh (z.1, x)) z.2 δ`.

The function `x ↦ clampedSlice Hh (z.1, x)` is definitionally `x ↦ hamVF (clampHam Hh z.1) x`,
which closes the goal.
-/

namespace Work.RPCore.Flow

open Work.RPV

set_option autoImplicit false

noncomputable section

/-- The second coordinate of the clamped autonomous field, as a function of `z = (t, x) ∈ ℝ × PS`:
`clampedSlice Hh z = X_{clampHam Hh t} x`.  The clamped field is `z ↦ (1, clampedSlice Hh z)`. -/
noncomputable def clampedSlice (Hh : CptPerHam) : ℝ × PS → PS :=
  fun z => hamVF (clampHam Hh z.1) z.2

@[simp] theorem clampedSlice_apply (Hh : CptPerHam) (z : ℝ × PS) :
    clampedSlice Hh z = hamVF (clampHam Hh z.1) z.2 := rfl

/-- The uncurried clamped Hamiltonian `(t, x) ↦ clampHam Hh t x` is `C⁴`. -/
theorem contDiff_clampHam_uncurried (Hh : CptPerHam) :
    ContDiff ℝ 4 (fun z : ℝ × PS => clampHam Hh z.1 z.2) := by
  have h1 : ContDiff ℝ 4 (fun z : ℝ × PS => (clampPsi z.1, z.2)) :=
    (clampPsi_contDiff.comp contDiff_fst).prodMk contDiff_snd
  have h2 : ContDiff ℝ 4 (fun z : ℝ × PS => Hh.H (clampPsi z.1) z.2) :=
    Hh.smooth.comp h1
  simpa only [clampHam] using h2

/-- The field `z ↦ X_{clampHam Hh z.1} z.2` is `C³`. -/
theorem contDiff_clampedSlice (Hh : CptPerHam) : ContDiff ℝ 3 (clampedSlice Hh) := by
  have hU := contDiff_clampHam_uncurried Hh
  have h3 : ContDiff ℝ 3
      (fun z : ℝ × PS => hamVF (fun y : PS => clampHam Hh z.1 y) z.2) :=
    contDiff_hamVF_partial 3 (fun z : ℝ × PS => clampHam Hh z.1 z.2) hU
  have hfun : (fun z : ℝ × PS => hamVF (fun y : PS => clampHam Hh z.1 y) z.2)
      = clampedSlice Hh := rfl
  rw [hfun] at h3
  exact h3

theorem clampedField_fderiv_inr_snd (Hh : Work.RPV.CptPerHam) (z : ℝ × Work.RPV.PS) (δ : Work.RPV.PS) :
    (fderiv ℝ (Work.RPCore.clampedField Hh) z (ContinuousLinearMap.inr ℝ ℝ Work.RPV.PS δ)).2
      = fderiv ℝ (Work.RPV.hamVF (Work.RPCore.clampHam Hh z.1)) z.2 δ := by
  have hcd : ContDiff ℝ 3 (clampedSlice Hh) := contDiff_clampedSlice Hh
  have hd : DifferentiableAt ℝ (clampedSlice Hh) z :=
    (hcd.differentiable (by norm_num)).differentiableAt
  -- The vertical slice of `clampedSlice Hh` is the composite with the slice inclusion.
  have hslice : fderiv ℝ (fun x : PS => clampedSlice Hh (z.1, x)) z.2
      = (fderiv ℝ (clampedSlice Hh) z).comp (ContinuousLinearMap.inr ℝ ℝ PS) := by
    have h1 : HasFDerivAt (fun x : PS => ((z.1, x) : ℝ × PS))
        (ContinuousLinearMap.inr ℝ ℝ PS) z.2 :=
      hasFDerivAt_prodMk_right z.1 z.2
    exact (HasFDerivAt.comp z.2 hd.hasFDerivAt h1).fderiv
  -- The clamped field is `(1, clampedSlice Hh ·)`, so its derivative at `z` is `0.prod _`.
  have hpair : HasFDerivAt (fun w : ℝ × PS => ((1 : ℝ), clampedSlice Hh w))
      ((0 : (ℝ × PS) →L[ℝ] ℝ).prod (fderiv ℝ (clampedSlice Hh) z)) z :=
    (hasFDerivAt_const (1 : ℝ) z).prodMk hd.hasFDerivAt
  have hprod : (fderiv ℝ (fun w : ℝ × PS => ((1 : ℝ), clampedSlice Hh w)) z
        (ContinuousLinearMap.inr ℝ ℝ PS δ)).2
      = fderiv ℝ (clampedSlice Hh) z (ContinuousLinearMap.inr ℝ ℝ PS δ) := by
    rw [hpair.fderiv]
    simp
  have hfield : Work.RPCore.clampedField Hh
      = fun w : ℝ × PS => ((1 : ℝ), clampedSlice Hh w) := by
    funext w
    rfl
  rw [hfield, hprod]
  -- Convert `fderiv (clampedSlice Hh) z (inr δ)` into the slice derivative.
  have h2 : fderiv ℝ (clampedSlice Hh) z (ContinuousLinearMap.inr ℝ ℝ PS δ)
      = fderiv ℝ (fun x : PS => clampedSlice Hh (z.1, x)) z.2 δ := by
    have := congrArg (fun (L : PS →L[ℝ] PS) => L δ) hslice
    simpa only [ContinuousLinearMap.comp_apply] using this.symm
  rw [h2]
  rfl

end

end Work.RPCore.Flow
