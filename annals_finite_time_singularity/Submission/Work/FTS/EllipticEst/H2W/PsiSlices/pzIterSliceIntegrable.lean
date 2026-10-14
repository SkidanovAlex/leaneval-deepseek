import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Cores.Dil.HkSqLimit
import Submission.Work.FTS.EllipticEst.Cores.PPureShiftRad.Basic
import Submission.Work.FTS.EllipticEst.Cores.pPureShiftAux.Basic
import Submission.Work.FTS.EllipticEst.Cores.pPureShiftAux.MajEst
import Submission.Work.FTS.EllipticEst.H2W.PsiSlices.CascadeRecursion
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.Physical.Ident.vorticity_psiField_scaled
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.Dil.DqqHonest =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cores.Dil


end Work.FTS.EllipticEst.Cores.Dil
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.pPureShiftTwoAlpha4 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cores

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option autoImplicit false

/-!
# `Cores/pPureShiftTwoAlpha4` — the `α⁴`-weighted pure `∂_θ²` slot of the twice shifted datum

The target is

```
(h0 : ∃ C, 0 < C ∧ TT.EllWeak0 C) →
∃ C, 0 < C ∧ ∀ α F Ψ, 0 < α → α ≤ 1/4 → TT.EllWeakPos α 2 F Ψ →
  α⁴ · ∫_z w² ∫_θ (∂_θ²(D_z²Ψ))² · sin(2θ)^{-η}  ≤  C · HkSq α 2 F,
```

i.e. the pure angular slot `|∂_θ²(D_z²Ψ)|²_{ℋ⁰}` of the twice radially shifted solution,
weighted by `α⁴`.

## The route

1. `lhs_eq_HkSq'` (`Cores.pPureShiftAux.Basic`, proved) identifies the left-hand side with
   `α⁴ · HkSq α 0 (pthIter 2 (DzIter 2 Ψ))`.
2. `Pieces.TL2.shiftZeroSlots_bound` (proved, and *parameterised* by its only analytic input
   `DilEstimate`) applied with `k = j = 2` gives the two level-`0` slots of the twice radially
   shifted solution:

     `α⁴ |z²∂_z²(D_z²Ψ)|²_{ℋ⁰} + |∂_θ²(D_z²Ψ)|²_{ℋ⁰} ≤ C |F|²_{ℋ²}`,

   with a constant `C` uniform in `α`.  Its proof is the dilation difference-quotient argument:
   the twice-iterated difference-quotient datum `(dqq c F, dqq c Ψ)` is again a datum of the
   weak class (`EllWeakPos_dqq`, whose moments are the difference quotients of the vanishing
   moments of the datum), `EllWeak0` is applied to it, and the limit `c → 1⁺` is taken by Fatou
   (`Dil.HkSq_zero_le_of_eventually_le`) using the slot identities
   `∂_θ²(dqq c Ψ) = dqq c (∂_θ²Ψ)` and `z²∂_z²(dqq c Ψ) = dqq c (z²∂_z²Ψ)`.
3. The analytic input `DilEstimate` — the difference-quotient engine
   `HkMem α 0 (dq c g) ∧ HkSq α 0 (dq c g) ≤ c³ HkSq α 0 (D_z g)` for `g` smooth on the open
   quadrant with `D_z g ∈ ℋ⁰` — is supplied here as `dilEstimate_fts`, from the proved lemma
   `Cores.pPureShiftAux.HkMem_dq_and_HkSq_dq_le_self`.
4. Since `α ≤ 1/4` gives `α⁴ ≤ 1` and the slot is nonnegative, the `α⁴`-weighted form follows
   from the unweighted one: **the target holds with `α⁴` replaced by `1`.**
-/

/-- **The difference-quotient engine** (`DilEstimate`), supplied from the proved lemma
`Cores.pPureShiftAux.HkMem_dq_and_HkSq_dq_le_self`: for `g` of class `C^∞` on the open quadrant
whose radial derivative `D_z g` is honestly in `ℋ⁰`, and `c > 1`, the radial difference
quotient `dq c g` is again in `ℋ⁰` and its squared `ℋ⁰`-norm is at most `c³` times that of
`D_z g`. -/
theorem dilEstimate_fts : Pieces.TL2.DilEstimate := by
  intro α c g hg hgmem hc
  exact pPureShiftAux.HkMem_dq_and_HkSq_dq_le_self hg hgmem hc



end

end Work.FTS.EllipticEst.Cores
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.PsiSlices.pzIterSliceIntegrable =====
section

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



end
end Work.FTS.EllipticEst.H2W.PsiSlices
end
