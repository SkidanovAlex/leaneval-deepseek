import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseBoxFock.PCFU.SlotPieceDefs
import Submission.Work.BoseBoxFock.PCFU.lowSlot_L2_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.chAslotAux` — the assembly layer of `PCFU.chAslot_le`

The slot bound `PCFU.chAslot_le` is assembled from the two per-kernel pieces
`PCFU.chAslotTaper_le` (`KfrU − latPer3 ℓ W₁`) and `PCFU.chAslotImages_le`
(`latPer3 ℓ W₁ − ℓ³W₁`) plus the elementary bookkeeping collected here:

* `boxRestrictR_sq_integral` — `∫ ‖boxRestrictR ℓ Φ‖² = ∫_{abox}Φ²`,
* `boxRestrictR_abs_le` — the box-restricted state is bounded by the state's box sup,
* the pointwise kernel split `KfrU − ℓ³W₁ = (KfrU − latPer3 ℓ W₁) + (latPer3 ℓ W₁ − ℓ³W₁)`.

(Further assembly lemmas — the product rule relating the windowed slot Dirichlet form of `Φ`
to its raw form, the `aP`/`aQ` contraction for the box-restricted state, and the arithmetic
choosing `K0, A, T` — are added in the follow-up session; see
`PCFU/FINDING_chAslot_le_SESSION1.md` §6.)
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The box restriction of a state, squared, integrates to the `L²`-norm square of the state. -/
theorem boxRestrictR_sq_integral {n : ℕ} (ℓ : ℝ) (Φ : Submission.BoseGases.X n → ℝ) :
    ∫ x : Submission.BoseGases.X n, (Work.BoseBoxFock.boxRestrictR ℓ Φ x) ^ 2
      = ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 := by
  have hfun : (fun x : Submission.BoseGases.X n => (Work.BoseBoxFock.boxRestrictR ℓ Φ x) ^ 2)
      = (Submission.BoseGases.abox n ℓ).indicator (fun x => (Φ x) ^ 2) := by
    funext x
    rw [Work.BoseBoxFock.boxRestrictR]
    by_cases hx : x ∈ Submission.BoseGases.abox n ℓ
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      ring
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
      ring
  rw [hfun, MeasureTheory.integral_indicator
    (Submission.BoseGases.abox_measurable n ℓ)]

/-- The box restriction of a state is bounded by the state's supremum on the box. -/
theorem boxRestrictR_abs_le {n : ℕ} (ℓ C : ℝ) {Φ : Submission.BoseGases.X n → ℝ}
    (hC : ∀ x ∈ Submission.BoseGases.abox n ℓ, |Φ x| ≤ C) (x : Submission.BoseGases.X n) :
    |Work.BoseBoxFock.boxRestrictR ℓ Φ x| ≤ max C 0 := by
  rw [Work.BoseBoxFock.boxRestrictR]
  by_cases hx : x ∈ Submission.BoseGases.abox n ℓ
  · rw [Set.indicator_of_mem hx, mul_one]
    exact le_trans (hC x hx) (le_max_left _ _)
  · rw [Set.indicator_of_notMem hx, mul_zero, abs_zero]
    exact le_max_right _ _

/-- **The pointwise kernel split.**  The full alias kernel of the `(A)`-slot is the sum of its
*taper* part (`KfrU − latPer3 ℓ W₁`) and its *images* part (`latPer3 ℓ W₁ − ℓ³W₁`). -/
theorem aliasKernel_split {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ}
    {fu : Work.BoseBoxFix.LowCut} {N : ℕ} (z : E3) :
    (Work.BoseBoxFock.PCFU.KfrU v h μ fu N z
        - ((ellH v μ) ^ 3 : ℂ) * ((Work.BoseFixR.W1fun v h (ellH v μ) z : ℝ) : ℂ))
      = ((Work.BoseBoxFock.PCFU.KfrU v h μ fu N z
            - Work.BoseBoxFock.latPer3 (ellH v μ) (Work.BoseFixR.W1fun v h (ellH v μ)) z)
          + (Work.BoseBoxFock.latPer3 (ellH v μ) (Work.BoseFixR.W1fun v h (ellH v μ)) z
              - ((ellH v μ) ^ 3 : ℂ) * ((Work.BoseFixR.W1fun v h (ellH v μ) z : ℝ) : ℂ))) := by
  ring

/-- **The budget is saturated by the maximal constant.**  With
`A μ := K0·(a v)/(8·μ·(ℓ³+1))` (`ℓ = ellH v μ`), the `SlotPieceBound` arithmetic constraint
`2ℓ⁻³·(4μ²ℓ⁶(1+ℓ⁻³)·A μ) ≤ K0·(μ·a v)` holds **with equality** for every `μ ≠ 0` — so the whole
`μ`-dependent slack of `SlotPiece` is carried by the *free* `K0`. -/
theorem budget_saturates {v : E3 → ℝ} {μ : ℝ} (hμ : μ ≠ 0) (K0 : ℝ) :
    2 * (ellH v μ) ^ (-3 : ℤ)
        * (4 * μ ^ 2 * (ellH v μ) ^ 6 * (1 + (ellH v μ) ^ (-3 : ℤ))
            * (K0 * BoseGases.a v / (8 * μ * ((ellH v μ) ^ 3 + 1))))
      = K0 * (μ * BoseGases.a v) := by
  have hℓ : (ellH v μ) ≠ 0 := ne_of_gt (ellH_pos v μ)
  have hpos : (0 : ℝ) < ellH v μ := ellH_pos v μ
  have h4 : (1 : ℝ) + (ellH v μ) ^ 3 ≠ 0 := by positivity
  rw [zpow_neg, zpow_ofNat]
  field_simp
  ring

end Work.BoseBoxFock.PCFU
