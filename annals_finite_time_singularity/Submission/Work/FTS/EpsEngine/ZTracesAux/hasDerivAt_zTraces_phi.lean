/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `z`-derivative of the trace function `z ↦ z * (D_z^b D_θ^a f · w)²`

The leaf `Work.FTS.EpsEngine.zTraces_T1` controls the two boundary traces (at `z → 0⁺` and
`z → ∞`) of the function

  `φ z := z * (Work.Spaces.mixed b a f z θ * Work.Spaces.w z) ^ 2`

by integrating its derivative, and this module supplies that derivative: for a datum which is
`C^∞` on the open quadrant (`Work.FTS.EllipticEst.SmoothOpen f`), an interior angle `θ` and
`z > 0`,

  `φ'(z) = (D_z^b D_θ^a f · w)² + 2 (D_z^b D_θ^a f · w) · w · (D_z^{b+1} D_θ^a f - 2 D_z^b D_θ^a f/(1+z))`.

The three ingredients are:

* the `z`-slice derivative `∂_z (D_z^b D_θ^a f) = Work.Spaces.pz (mixed b a f)` at an interior
  angle (`SmoothOpen.hasDerivAt_slice`, from `C^∞` on the open quadrant);
* the derivative `w' y = -2(1+y)/y³` of the radial weight `w y = (1+y)²/y²`
  (the library lemma `Work.FTS.EpsEngine.ZTracesAux.hasDerivAt_w`);
* the definitional identity `D_z^{b+1} D_θ^a f = z · ∂_z (D_z^b D_θ^a f)` of
  `Work.Spaces.mixed`, which turns the `z · w · ∂_z(D_z^b D_θ^a f)` term produced by the
  product rule into `w · D_z^{b+1} D_θ^a f`; the leftover `z · w'(z) = -2 w z/(1+z)`
  (the lemma `Work.FTS.EpsEngine.ZTracesAux.z_mul_deriv_w`) is what creates the `/ (1+z)`
  in the statement.

Everything is elementary; the only non-routine point is the exact shape of the derivative
value, which is closed by clearing the denominators of `w` (`field_simp`) and `ring`.
-/
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EpsEngine.ZTracesAux.hasDerivAt_w

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

namespace Work.FTS.EpsEngine.ZTracesAux

theorem hasDerivAt_zTraces_phi {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (b a : ℕ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ∀ z : ℝ, 0 < z → HasDerivAt
      (fun z' : ℝ => z' * (Work.Spaces.mixed b a f z' θ * Work.Spaces.w z') ^ 2)
      ((Work.Spaces.mixed b a f z θ * Work.Spaces.w z) ^ 2
        + 2 * (Work.Spaces.mixed b a f z θ * Work.Spaces.w z)
          * (Work.Spaces.w z * (Work.Spaces.mixed (b + 1) a f z θ
              - 2 * Work.Spaces.mixed b a f z θ / (1 + z)))) z := by
  intro z hz
  have hz0 : z ≠ 0 := ne_of_gt hz
  -- the `z`-derivative of the slice `z' ↦ D_z^b D_θ^a f z' θ` (an interior angle)
  have hslice : HasDerivAt (fun z' : ℝ => Work.Spaces.mixed b a f z' θ)
      (Work.Spaces.pz (Work.Spaces.mixed b a f) z θ) z :=
    (hf.mixed b a).hasDerivAt_slice hθ hz
  -- product rule with the weight, then the square, then the outer factor `z'`
  have hprod := hslice.mul (hasDerivAt_w z hz0)
  have hsq := hprod.pow 2
  have hmain := (hasDerivAt_id z).mul hsq
  refine hmain.congr_deriv ?_
  have hmix : Work.Spaces.mixed (b + 1) a f z θ
      = z * Work.Spaces.pz (Work.Spaces.mixed b a f) z θ := rfl
  simp only [Pi.mul_apply, Pi.pow_apply, id_eq]
  rw [hmix]
  norm_num
  simp only [Work.Spaces.w]
  field_simp
  ring

end Work.FTS.EpsEngine.ZTracesAux
