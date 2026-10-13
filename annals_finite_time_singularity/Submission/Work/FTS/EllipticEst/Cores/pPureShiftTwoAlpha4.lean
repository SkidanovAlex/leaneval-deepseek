import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.Cores.Dil.DilBasic
import Submission.Work.FTS.EllipticEst.Cores.Dil.HkSqLimit
import Submission.Work.FTS.EllipticEst.Cores.Dil.dqIterTendsto
import Submission.Work.FTS.EllipticEst.Cores.pPureShiftAux.Basic
import Submission.Work.FTS.EllipticEst.Cores.Pieces.TL2.shiftZeroSlots

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

/-- **The pure `∂_θ²` slot of the twice radially shifted datum, unweighted.**

The `i = 2` angular slot of `prop:H2` at level `2`: for every datum of the weak class
`EllWeakPos α 2 F Ψ` with `0 < α ≤ 1/4`,

  `|∂_θ²(D_z²Ψ)|²_{ℋ⁰} ≤ C |F|²_{ℋ²}`,

with a universal (`α`-independent) constant `C`, *given* the level-`0` estimate `EllWeak0`.

This is the same conclusion as `Cores.pPureShiftTwo` (which routes through the instantiated
`Pieces.TL2.shiftZeroSlots` and is therefore available only once that module's remaining
analytic input `Dil.HkMem_dq_le` is discharged), but proved here from the *parameterised*
`Pieces.TL2.shiftZeroSlots_bound` together with the engine `dilEstimate_fts`; it is the strong
form from which `pPureShiftTwoAlpha4` follows by dropping a factor `α⁴ ≤ 1`. -/
theorem pPureShiftTwo_unweighted
    (h0 : ∃ C : ℝ, 0 < C ∧ Work.FTS.EllipticEst.TT.EllWeak0 C) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ) z θ) ^ 2 *
            Work.FTS.EllipticEst.sEta θ))
        ≤ C * Work.Spaces.HkSq α 2 F := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := h0
  -- the two level-`0` slots of the twice radially shifted datum
  obtain ⟨C, hCpos, hC⟩ := Pieces.TL2.shiftZeroSlots_bound dilEstimate_fts
    Dil.dqIterTendsto 2 2 le_rfl C₀ hC₀pos hC₀
  refine ⟨C, hCpos, ?_⟩
  intro α F Ψ hα hα4 h
  have htwo := hC α F Ψ hα hα4 h
  -- drop the (nonnegative) `α⁴`-weighted `z²∂_z²`-slot
  have hB : Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ))
      ≤ C * Work.Spaces.HkSq α 2 F := by
    have hnn : 0 ≤ α ^ 4 * Work.Spaces.HkSq α 0
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 2 Ψ) z θ) :=
      mul_nonneg (by positivity) (Work.Spaces.HkSq_nonneg _ _ _)
    linarith
  -- the left-hand side is `HkSq α 0 (∂_θ²(D_z²Ψ))`
  rw [pPureShiftAux.lhs_eq_HkSq' α Ψ]
  exact hB

/-- **The `α⁴`-weighted pure `∂_θ²` slot of the twice radially shifted datum.**

The target: for every datum of the weak class `EllWeakPos α 2 F Ψ` with `0 < α ≤ 1/4`,

  `α⁴ |∂_θ²(D_z²Ψ)|²_{ℋ⁰} ≤ C |F|²_{ℋ²}`

with a universal (`α`-independent) constant `C`, *given* the level-`0` estimate `EllWeak0`.
Immediate from the unweighted `pPureShiftTwo_unweighted` because `α ≤ 1/4` gives `α⁴ ≤ 1` and
the slot is nonnegative. -/
theorem pPureShiftTwoAlpha4 (h0 : ∃ C : ℝ, 0 < C ∧ Work.FTS.EllipticEst.TT.EllWeak0 C) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      α ^ 4 * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ) z θ) ^ 2 *
            Work.FTS.EllipticEst.sEta θ))
        ≤ C * Work.Spaces.HkSq α 2 F := by
  obtain ⟨C, hCpos, hC⟩ := pPureShiftTwo_unweighted h0
  refine ⟨C, hCpos, ?_⟩
  intro α F Ψ hα hα4 h
  have hB := hC α F Ψ hα hα4 h
  rw [pPureShiftAux.lhs_eq_HkSq' α Ψ] at hB
  -- the left-hand side is `α⁴ · HkSq α 0 (∂_θ²(D_z²Ψ))`
  rw [pPureShiftAux.lhs_eq_HkSq' α Ψ]
  -- `α⁴ ≤ 1`, and multiplying by a factor `≤ 1` only lowers the nonnegative slot
  have hα4le : α ^ 4 ≤ 1 := by
    have h1 : α ^ 4 ≤ (1 / 4 : ℝ) ^ 4 := pow_le_pow_left₀ hα.le hα4 4
    norm_num at h1
    linarith
  have hXnn : 0 ≤ Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ)) :=
    Work.Spaces.HkSq_nonneg _ _ _
  calc α ^ 4 * Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ))
      ≤ 1 * Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ)) :=
        mul_le_mul_of_nonneg_right hα4le hXnn
    _ = Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ)) := one_mul _
    _ ≤ C * Work.Spaces.HkSq α 2 F := hB

end

end Work.FTS.EllipticEst.Cores
