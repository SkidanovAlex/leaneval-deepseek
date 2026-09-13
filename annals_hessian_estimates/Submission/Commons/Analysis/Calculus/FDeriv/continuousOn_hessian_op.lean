import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Order.CompletePartialOrder

/-!
# Continuity of the Hessian operator of a `C²` function on an open set

For an open set `s` and a function `φ : E → ℝ` which is `C²` on `s`, the map
`x ↦ InnerProductSpace.continuousLinearMapOfBilin (fderivWithin ℝ (fderivWithin ℝ φ s) s x)`
— the second derivative of `φ` at `x`, viewed through the Fréchet–Riesz representation
theorem as a continuous linear operator `E →L[ℝ] E` — is continuous on `s`.

The proof is a composition of two continuous maps:

* `x ↦ fderivWithin ℝ (fderivWithin ℝ φ s) s x` is continuous on `s`: since `φ` is `C²` on `s`,
  its within-derivative `fderivWithin ℝ φ s` is `C¹` on `s` (`ContDiffOn.fderivWithin`), hence its
  own within-derivative is continuous on `s` (`ContDiffOn.continuousOn_fderivWithin`);

* `InnerProductSpace.continuousLinearMapOfBilin` is continuous: it is the map
  `B ↦ toDual.symm.comp B`, obtained by fixing the first argument of the (continuous) composition
  of continuous linear maps (`Continuous.const_clm_comp`).
-/

namespace Commons.Analysis.Calculus.FDeriv

theorem continuousOn_hessian_op
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {φ : E → ℝ} {s : Set E} (hs : IsOpen s) (hφ : ContDiffOn ℝ 2 φ s) :
    ContinuousOn (fun x => InnerProductSpace.continuousLinearMapOfBilin
        (fderivWithin ℝ (fderivWithin ℝ φ s) s x)) s := by
  -- On an open set one has `UniqueDiffOn`, so the `ContDiffOn` API for derivatives applies.
  have hu : UniqueDiffOn ℝ s := hs.uniqueDiffOn
  -- `fderivWithin ℝ φ s` is `C¹` on `s`, because `φ` is `C²` on `s`.
  have h1 : ContDiffOn ℝ 1 (fderivWithin ℝ φ s) s :=
    hφ.fderivWithin hu (by norm_num)
  -- Hence the (within) second derivative of `φ` is continuous on `s`.
  have h2 : ContinuousOn (fun x => fderivWithin ℝ (fderivWithin ℝ φ s) s x) s :=
    h1.continuousOn_fderivWithin hu (by norm_num)
  -- `continuousLinearMapOfBilin` is continuous: it is `B ↦ L.comp B` for the fixed continuous
  -- linear map `L = toDual.symm`.
  have hcont : Continuous (fun B : E →L[ℝ] E →L[ℝ] ℝ =>
      InnerProductSpace.continuousLinearMapOfBilin B) := by
    have key : (fun B : E →L[ℝ] E →L[ℝ] ℝ =>
          InnerProductSpace.continuousLinearMapOfBilin B)
        = fun B => ((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap).comp B := rfl
    rw [key]
    exact Continuous.const_clm_comp continuous_id _
  -- Compose the two continuous-on-`s` maps.
  simpa [Function.comp_def] using
    hcont.continuousOn.comp h2 (Set.mapsTo_univ _ _)

end Commons.Analysis.Calculus.FDeriv