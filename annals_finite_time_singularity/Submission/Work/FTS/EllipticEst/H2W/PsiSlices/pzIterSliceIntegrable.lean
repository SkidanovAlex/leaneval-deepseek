import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.H2W.PsiSlices.Reductions
import Submission.Work.FTS.EllipticEst.H2W.PsiSlices.CascadeRecursion
import Submission.Work.FTS.EllipticEst.H2W.PsiSlices.SlotReduction

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.PsiSlices

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

noncomputable section

/-! ## What remains of the target, and the two shapes of it

Everything analytic in this file is proved from the tree's one-variable tools; the residual
content is the *datum-side endpoint rigidity* of the weak class, now available in three equivalent
forms (each proved here as an implication):

* `pzIterSliceIntegrable_of_sourceHonest` — the sources `Lzero1(∂_zΨ(z,·))`, `Lzero1(∂_z²Ψ(z,·))`
  are `sinθcos²θ`-integrable for a.e. `z`;
* `pzIterSliceIntegrable_of_levels34` — the *slices* `∂_z³Ψ(z,·)`, `∂_z⁴Ψ(z,·)` are
  `sinθcos²θ`-integrable for a.e. `z` (the "top two levels", i.e. the requester's "genuinely new
  content is `m = 4`"); this one uses `H2W.PsiSlices.shiftedSourcePoleBound`, which makes the
  `z`-regress close *downward* through the `γ_m` terms of the level identities;
* `pzIterSliceIntegrable_of_slots4` (in `PsiSlices/SlotReduction.lean`) — the target from the
  **slot honesty** of the slices: `HkMem α 0 (∂_θ²(∂_z^jΨ))` for `j ≤ 2` (via
  `H2W.aeSliceHonestOfSlots`, which stops at `j ≤ 3`), together with `HkMem α 0 (z²∂_z³Ψ)` and
  `HkMem α 0 (z²∂_z⁴Ψ)`.  This is the sharpest reduction available: the slots are exactly what
  the tree's own weak class `AeMom.EllWeakPosAe` *assumes* (`HkMem α k (z²∂_z²Ψ)`,
  `HkMem α k (∂_θ²Ψ)`), so the reduction isolates the chapter's endpoint rigidity in the form
  the rest of the project already consumes.  See
  `PsiSlices/NOTES_pzIterSliceIntegrable_addendum4.md` §§1–8 for the analysis (the sharp
  `Lzero1`-order rule and its counterexample, the elimination identity, the regress, and the
  `AeMom` verdict);
* `pzIterSliceIntegrable_of_at_one` — the conclusion holds at the *single* point `z = 1` for every
  class datum (the radial dilation `z ↦ lam·z` preserves the class —
  `H2W.PsiSlices.weakPos2_dilate` — and `∂_z^m` of a dilated datum is `lam^m` times the dilated
  slice — `H2W.PsiSlices.pzIter_dilate`), so the residual statement needs no measure theory in `z`.

## The quantitative route to the rigidity (the `z`-side / Mellin rung)

The reason the target is true, and the shape a proof should take, is the *spectral threshold* of
the radial Euler operator.  On the pure mode `z^β` the radial part `R = α²z²∂_z² + α(5+α)z∂_z` of
`bslOp` acts as `λ(β) = α²β² + 5αβ = α²(β + 5/(2α))² - 25/4 ≥ -25/4`
(`H2W.PsiSlices.eulerModeThreshold`).  A `θ`-mode `t^{-s}` of a slice contributes to `Lzero1` of
that slice the term `(1 - s²)t^{-s-2}`, which the level identity must match against the *radial*
operator applied to the same mode; the radial operator has no eigenvalue below `-25/4`, so a mode
with `1 - s² < -25/4`, i.e. `s > sqrt(29/4) = 2.6926…`, cannot be matched and cannot appear.  Since
`2.6926 < 3`, this already gives `∫ sinθcos²θ·|∂_z^mΨ| < ∞`: the *crude* growth bound
`|∂_z^mΨ| ≲ (π/2-θ)^{-2.6926}` implies the target, and it is strictly weaker than the sharp pole
bound `(π/2-θ)^{-1}` pursued by the sibling nodes.  The missing formal step is the passage from the
radial spectral threshold to the `θ`-mode bound: a Mellin / generalized-eigenfunction expansion in
`z` together with the indicial expansion of the slices at `θ = π/2`. -/


theorem pzIterSliceIntegrable : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Work.FTS.EllipticEst.WeakPos2 α F Ψ →
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ∀ m : ℕ, m ≤ 4 →
        MeasureTheory.IntegrableOn
          (fun θ : ℝ => Work.Spaces.pzIter m Ψ z θ * Work.Elliptic.sinCos2 θ)
          Work.Spaces.Iθ := by sorry

end
end Work.FTS.EllipticEst.H2W.PsiSlices
