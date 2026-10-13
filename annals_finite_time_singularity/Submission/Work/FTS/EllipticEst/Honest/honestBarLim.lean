/-
Copyright: work module for the Elgindi finite-time singularity project.

# The honest bar limit at `θ → π/2`

`Work.FTS.EllipticEst.Honest.honestBarLim`: for honest data `Hon α F Ψ` and every `z > 0` the
"bar" function `θ ↦ Ψ z θ / cos θ` has a finite limit as `θ → π/2⁻`.

## Mathematics

Write `u_z := (fun θ => Ψ z θ)` for the `θ`-slice at radius `z > 0` and `δ := π/2 - θ`.  The
honest hypotheses (`Honest.Basic`) give, for every `z > 0`:

* `u_z` is `C^∞` on `(0,π/2)` (`Hon.sm`);
* `∂_θθu_z` is `L²` against the singular weight `σ θ = sin(2θ)^{-η}` (`Hon.memB`); since `σ ≥ 1`
  this gives `∂_θθ u_z ∈ L¹`, hence `u_z` and `u_z'` have *finite* one-sided limits at `π/2⁻`;
* the slice limit `Q z := lim_{θ→π/2⁻} Ψ z θ` is `0`, by
  `Work.FTS.EllipticEst.Honest.HonSliceRightTendsto`: the polar equation, together with the
  `ℋ⁰`-honesty of `F`, `∂_θθΨ` and `z²∂_zzΨ`, forces the slice to vanish at `π/2` (the
  `(π/2-θ)^{-1}` indicial mode is excluded).

Then `u_z θ = -L·(π/2-θ) + o(π/2-θ)` with `L := lim u_z'`, so `u_z θ / cos θ → -L` because
`cos θ = sin(π/2-θ) ~ π/2-θ`; this is the imported lemma
`divCos_tendsto_of_tendsto_deriv` (with the limit of `u_z` equal to `0`).

## Where the pieces live

* `Work.FTS.EllipticEst.Honest.barLimSlices` — the slice facts above for the honest class
  (`hon_slice_contDiffOn`, `hon_slice_deriv2_integrableOn_Iθ`, `hon_Lzero1_slice`, the generic
  one-sided limit lemma `exists_tendsto_nhdsWithin_Iio_of_integrableOn_deriv`, and
  `hon_slice_limit`, `hon_slice_deriv_limit`);
* `Work.FTS.EllipticEst.Honest.divCos_tendsto_of_tendsto_deriv` — the final one-dimensional step
  `u → 0`, `u' → L` at `π/2⁻` ⟹ `u / cos θ → -L`;
* `Work.FTS.EllipticEst.Honest.HonSliceRightTendsto` — the vanishing of the slice at `π/2`.

An alternative route to the same vanishing, which does not go through
`HonSliceRightTendsto` but through the `(π/2-θ)^{-2}`-coefficient rigidity of `∂_zΨ`, is developed
in the sibling modules `XLemma`, `honPzDivSq`, `honPzDiff`, `honBarConst`, `avgBarZero`.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.Honest.Basic
import Submission.Work.FTS.EllipticEst.Honest.barLimSlices
import Submission.Work.FTS.EllipticEst.Honest.HonSliceRightTendsto
import Submission.Work.FTS.EllipticEst.Honest.divCos_tendsto_of_tendsto_deriv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false

theorem honestBarLim (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.Honest.Hon α F Ψ) :
    ∀ z, 0 < z → ∃ c : ℝ, Filter.Tendsto (fun θ => Ψ z θ / Real.cos θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds c) := by
  intro z hz
  -- the derivative of the slice has a finite limit `L` at `π/2⁻`
  obtain ⟨L, hL⟩ := hon_slice_deriv_limit h hz
  -- the slice itself tends to `0`, so `Ψ z θ / cos θ → -L`
  exact ⟨-L, divCos_tendsto_of_tendsto_deriv (hon_slice_contDiffOn h hz)
    (HonSliceRightTendsto α F Ψ h z hz) hL⟩

end Work.FTS.EllipticEst.Honest
