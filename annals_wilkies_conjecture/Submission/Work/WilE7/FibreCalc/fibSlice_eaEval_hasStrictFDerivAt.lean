import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE9.EaD.eaEval_contDiff
import Submission.Work.WilE9.EaD.eaD_hasFDerivAt

namespace Work.WilE7.FibreCalc

open WilkiesDesign.E

/-!
## The strict derivative of the slice `y ↦ eaEval c Q (Fin.append x y)`

The map `y ↦ Fin.append x y` is *affine* (not linear!) from `Fin q → ℝ` to `Fin (p + q) → ℝ`:
on the first `p` coordinates it is the constant `x`, on the last `q` coordinates the identity.
Its strict derivative is therefore the linear map `h ↦ Fin.append 0 h`, which inserts `0` in the
first block. We build that map (`finAppendZeroLM`, `finAppendZeroCLM`) and then compose it with the
strict derivative of `eaEval c Q`, obtained from `eaEval_contDiff` (`ContDiff ℝ ⊤`, hence
`ContDiffAt ℝ 1`, hence strictly differentiable) together with the value of the Fréchet derivative
`eaD_hasFDerivAt`. The `p` coordinates contribute `0` to the composite, leaving exactly the
`q` sum in the statement.
-/

/-- `y ↦ Fin.append 0 y`: the insertion of `Fin q → ℝ` as the *second* block of `Fin (p+q) → ℝ`. -/
noncomputable def finAppendZeroLM (p q : ℕ) : (Fin q → ℝ) →ₗ[ℝ] (Fin (p + q) → ℝ) where
  toFun := fun y => Fin.append (0 : Fin p → ℝ) y
  map_add' := by
    intro u v; ext i
    refine Fin.addCases ?_ ?_ i
    · intro a; simp
    · intro b; simp
  map_smul' := by
    intro a u; ext i
    refine Fin.addCases ?_ ?_ i
    · intro c; simp
    · intro b; simp

/-- The same map, as a continuous linear map (the domain is finite dimensional). -/
noncomputable def finAppendZeroCLM (p q : ℕ) : (Fin q → ℝ) →L[ℝ] (Fin (p + q) → ℝ) :=
  LinearMap.toContinuousLinearMap (finAppendZeroLM p q)

@[simp]
theorem finAppendZeroCLM_apply (p q : ℕ) (y : Fin q → ℝ) :
    finAppendZeroCLM p q y = Fin.append (0 : Fin p → ℝ) y := rfl

/-- The affine map `y ↦ Fin.append x y` is strictly differentiable, with derivative
`finAppendZeroCLM p q`. -/
theorem hasStrictFDerivAt_finAppend (p q : ℕ) (x : Fin p → ℝ) (y₀ : Fin q → ℝ) :
    HasStrictFDerivAt (fun y : Fin q → ℝ => Fin.append x y) (finAppendZeroCLM p q) y₀ := by
  -- `Fin.append x y = Fin.append x 0 + Fin.append 0 y`.
  have h := (ContinuousLinearMap.hasStrictFDerivAt (finAppendZeroCLM p q) (x := y₀)).const_add
    (Fin.append x (0 : Fin q → ℝ))
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  ext i
  refine Fin.addCases ?_ ?_ i
  · intro a; simp
  · intro b; simp

/-- The Fréchet derivative of `eaEval c Q` at `v`, in the form of `eaD`, is also its *strict*
Fréchet derivative: `eaEval c Q` is smooth (`eaEval_contDiff`), so its `fderiv` is a strict
derivative, and `eaD_hasFDerivAt` identifies that `fderiv`. -/
theorem hasStrictFDerivAt_eaEval {N r : ℕ} (c : EAChain N r) (Q : EAPoly N r)
    (v : Fin N → ℝ) :
    HasStrictFDerivAt (fun z : Fin N → ℝ => eaEval c Q z)
      (∑ i : Fin N, eaEval c (eaD c i Q) v •
        (ContinuousLinearMap.proj i : (Fin N → ℝ) →L[ℝ] ℝ)) v := by
  have hcd : ContDiffAt ℝ 1 (fun z : Fin N → ℝ => eaEval c Q z) v :=
    (Work.WilE9.EaD.eaEval_contDiff c Q).contDiffAt.of_le le_top
  have h := hcd.hasStrictFDerivAt (by norm_num)
  rwa [(Work.WilE9.EaD.eaD_hasFDerivAt c Q v).fderiv] at h

theorem fibSlice_eaEval_hasStrictFDerivAt {p q r : ℕ} (c : WilkiesDesign.E.EAChain (p + q) r)
    (Q : WilkiesDesign.E.EAPoly (p + q) r) (x : Fin p → ℝ) (y₀ : Fin q → ℝ) :
    HasStrictFDerivAt (fun y : Fin q → ℝ => WilkiesDesign.E.eaEval c Q (Fin.append x y))
      (∑ d : Fin q, WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c (Fin.natAdd p d) Q) (Fin.append x y₀) •
        (ContinuousLinearMap.proj d : (Fin q → ℝ) →L[ℝ] ℝ)) y₀ := by
  have hL := hasStrictFDerivAt_finAppend p q x y₀
  have hout := hasStrictFDerivAt_eaEval c Q (Fin.append x y₀)
  have hcomp := hout.comp y₀ hL
  refine hcomp.congr_fderiv ?_
  -- The composite of the two derivatives: only the last `q` coordinates survive.
  ext y
  simp only [ContinuousLinearMap.comp_apply, finAppendZeroCLM_apply, Fin.sum_univ_add]
  simp

end Work.WilE7.FibreCalc
