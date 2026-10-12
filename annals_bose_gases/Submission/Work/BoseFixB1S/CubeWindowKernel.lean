import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.CubeWindowKinetic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.CubeWindowKernel` — the **cube overlap kernel** and the staged
# kernel-form identity of the cube family form

Holder of `Submission/Work/BoseFixB1S/LowCountWindowB1copy.lean`.  Companion of
`CubeWindowKinetic.lean` (the definitional half) and of `FINDING_LowCountWindowB1copy_session2.md`
§5 (the decomposition of the matched single-cube-cutoff route).

## What this module banks

* `convScaleCube M a z := conv3 (chiSmall M) (chiSmall M) (a⁻¹ • z)` — **the cube family's overlap
  kernel**, the exact cube analogue of the corpus's `Submission.BoseGases.convScale ℓ`
  (`= conv3 chi chi ((ℓ⁻¹)•·)`), with `chi` (the ball `ContDiffBump`) replaced by FS's own cosine
  bump `chiSmall M`.
* **`integral_cubeWin_mul_cubeWin`** — PROVED here: `∫_u cubeWin M a u x · cubeWin M a u y
  = convScaleCube M a (x − y)`, the cube analogue of the proved
  `Submission.BoseGases.chiU_chiU_integral` (`= convScale ℓ (x−y)`).  Same three-step argument
  (translation `integral_comp_sub_left`, the affine rewrite, and the evenness of the base bump —
  `chiSmall_even`), with the ball bump's `chi_even` replaced by `chiSmall_even`.

## What is *staged* (not proved here — the delegation target)

`familyFormUnprojCube_eq_kernelForm` below is the cube instance of the proved
`Work.BSKinetic.familyFormUnproj_eq_kernelForm`.  Its ball version goes through exactly three
window-specific ingredients:

1. `Work.SmallBoxBridge.winModeForm_eq_kernelForm_general` — **already generic in the window**
   (only `χ·ψ` integrable is needed), so it applies to `cubeWin M a u` verbatim;
2. the overlap identity at fixed `(x,y)` — supplied for the cube by
   `integral_cubeWin_mul_cubeWin` above (and `integral_chi_conv` for the ball);
3. the joint/slice integrability and compact-support bookkeeping
   (`integrable_bkiFam`-analogues), for which the cube needs `chiSmall`'s continuity
   (`chiSmall_continuous`) and support in the unit cube (`chiSmall` is supported in the cube
   `|z_j| ≤ 1/2`, so `tsupport ⊆ closedBall 0 (√3/2)`).

So the cube kernel-form identity is a *bounded* re-run: the analytic input (2) is now proved, and
(1) is window-generic; only (3)'s bookkeeping is new.

**Note on why this cannot be inherited from the ball version.**  The ball identity rests on
`convScale ℓ` being *the `bsWin`-family's* overlap kernel; the cube family has a different kernel
(`convScaleCube`), and the pointwise domination `bsWin ≤ C·cubeWin`
(`Work.BoseFixB1.chiB_le_const_mul_chiSmallB`, PROVED) does **not** pass to Fourier space, so the
kernel-form identity (and the symbol comparison that consumes it,
`Work.BoseFixB1.Core.symA_fsKinCoeff_mix_scaled`) must be re-run at the cube cutoff.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1S

open _root_.BoseGases Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The cube overlap kernel -/

/-- **The cube family's overlap kernel**: `(χ_M ⋆ χ_M)(z/a)` — the cube analogue of
`Submission.BoseGases.convScale ℓ` (which is `(χ ⋆ χ)(z/ℓ)` for the corpus's ball bump `χ`). -/
noncomputable def convScaleCube (M : ℕ) (a : ℝ) (z : E3) : ℝ :=
  Submission.BoseGases.conv3 (Submission.BoseGases.chiSmall M)
    (Submission.BoseGases.chiSmall M) (a⁻¹ • z)

/-- **The cube overlap identity**: `∫_u cubeWin M a u x · cubeWin M a u y du = convScaleCube M a (x−y)`.

Cube analogue of the proved `Submission.BoseGases.chiU_chiU_integral`; the three steps are the
translation `integral_comp_sub_left`, the affine rewriting of the two arguments, and the evenness
`chiSmall_even` of the cosine bump. -/
theorem integral_cubeWin_mul_cubeWin (M : ℕ) (hM : 1 ≤ M) {a : ℝ} (ha : a ≠ 0) (x y : E3) :
    (∫ u : E3, cubeWin M a u x * cubeWin M a u y) = convScaleCube M a (x - y) := by
  calc (∫ u : E3, cubeWin M a u x * cubeWin M a u y)
      = ∫ u : E3, Submission.BoseGases.chiSmall M (a⁻¹ • x - u)
            * Submission.BoseGases.chiSmall M (a⁻¹ • y - u) := by
        apply integral_congr_ae
        filter_upwards with u
        rfl
    _ = ∫ w : E3, Submission.BoseGases.chiSmall M (a⁻¹ • x - (a⁻¹ • x - w))
            * Submission.BoseGases.chiSmall M (a⁻¹ • y - (a⁻¹ • x - w)) := by
        symm
        exact integral_comp_sub_left (g := fun u : E3 =>
          Submission.BoseGases.chiSmall M (a⁻¹ • x - u)
            * Submission.BoseGases.chiSmall M (a⁻¹ • y - u)) (a⁻¹ • x)
    _ = ∫ w : E3, Submission.BoseGases.chiSmall M w
            * Submission.BoseGases.chiSmall M (w - (a⁻¹ • x - a⁻¹ • y)) := by
        apply integral_congr_ae
        filter_upwards with w
        rw [show a⁻¹ • x - (a⁻¹ • x - w) = w by abel,
          show a⁻¹ • y - (a⁻¹ • x - w) = w - (a⁻¹ • x - a⁻¹ • y) by abel]
    _ = ∫ w : E3, Submission.BoseGases.chiSmall M w
            * Submission.BoseGases.chiSmall M ((a⁻¹ • x - a⁻¹ • y) - w) := by
        apply integral_congr_ae
        filter_upwards with w
        rw [show w - (a⁻¹ • x - a⁻¹ • y) = -((a⁻¹ • x - a⁻¹ • y) - w) by abel,
          Submission.BoseGases.chiSmall_even hM ((a⁻¹ • x - a⁻¹ • y) - w)]
    _ = convScaleCube M a (x - y) := by
        rw [convScaleCube, smul_sub]
        rfl

/-! ## 2. The kernel-form identity — kept *out* of this module

`familyFormUnprojCube_eq_kernelForm` (the cube instance of
`Work.BSKinetic.familyFormUnproj_eq_kernelForm`, with `convScaleCube` in place of `convScale`) is
**delegated**, not stated here: declaring it here with a `sorry` would collide with the delegated
file of the same name, and this module is meant to stay `sorry`-free.  Its window-specific analytic
ingredient is `integral_cubeWin_mul_cubeWin` above; the rest is the integrability bookkeeping of
`BSKinetic/familyFormUnproj_eq_kernelForm` plus the window-generic
`Work.SmallBoxBridge.winModeForm_eq_kernelForm_general`.

-/

end Work.BoseFixB1S
