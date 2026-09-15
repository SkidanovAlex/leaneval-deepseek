import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.RCLike.Basic

namespace Commons.Analysis.Calculus.FDeriv

lemma fderiv_along_axis_eq_deriv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {H : E → F} {p e : E}
    (hH : DifferentiableAt ℝ H p) :
    HasDerivAt (fun s : ℝ => H (p + s • e)) ((fderiv ℝ H p) e) 0 := by
  -- the map s ↦ s • e has derivative e at 0
  have hsmul : HasDerivAt (fun s : ℝ => s • e) e 0 := by
    have hsmul0 : HasDerivAt ((fun s : ℝ => s) • (fun _ : ℝ => e)) e 0 := by
      simpa using
        (HasDerivAt.smul (𝕜 := ℝ) (𝕜' := ℝ) (F := E) (c := fun s : ℝ => s)
          (c' := (1 : ℝ)) (f := fun _ : ℝ => e) (f' := (0 : E)) (hasDerivAt_id 0)
          (hasDerivAt_const 0 e))
    convert hsmul0 using 1
    · ext s
      rfl
  -- adding the constant p does not change the derivative
  have hconst : HasDerivAt (fun _ : ℝ => p) (0 : E) 0 := hasDerivAt_const 0 p
  have hg : HasDerivAt (fun s : ℝ => p + s • e) e 0 := by
    have hg0 : HasDerivAt ((fun _ : ℝ => p) + (fun s : ℝ => s • e)) e 0 := by
      simpa using (HasDerivAt.add hconst hsmul)
    convert hg0 using 1
    · ext s
      rfl
  -- chain rule with the differentiability of H at p
  have hl : HasFDerivAt H (fderiv ℝ H p) (p + (0 : ℝ) • e) := by
    simpa using hH.hasFDerivAt
  have hcomp : HasDerivAt (fun s : ℝ => H (p + s • e)) ((fderiv ℝ H p) e) 0 := by
    convert
      (HasFDerivAt.comp_hasDerivAt (f := fun s : ℝ => p + s • e) (f' := e) (x := (0 : ℝ))
        (l := H) (l' := fderiv ℝ H p) hl hg) using 1
    · ext s
      rfl
  exact hcomp

end Commons.Analysis.Calculus.FDeriv