import ChallengeDeps
import Submission.Work.BoseBoxFock.FRK.potCubicZeroCell_exists
import Submission.Work.BoseBoxFock.PCFU.LhsDict
import Submission.Work.BoseBoxFock.PCFU.pairSum_slot_const
import Submission.Work.BoseBoxFock.errKafz_dominates_uniform
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseBoxFock/PCFU/SlotPieceDefs` — the slot-piece interface

`SlotPieceBound` / `SlotPiece` (and the `N`-threshold `chNThresh` they mention) live here rather
than in `PotCubicFreeU_exists`, so that the eight channel pieces can import this module *without*
importing the node that consumes them (the otherwise-circular edge
`PotCubicFreeU_exists → chX_le → PotCubicFreeU_exists`).
-/

namespace Work.BoseBoxFock

open MeasureTheory

/-- The `N`-threshold below which the label arithmetic of the cubic dictionary (`kmomLab`
additivity and the support conditions of `fLh`/`W1h`) is unavailable.  A function
`Nmin : ℝ → ℕ` dominating it discharges the dictionary's hypotheses `hN`/`hsub` for every
`N ≥ Nmin μ`. -/
noncomputable def chNThresh (v : ℝ³ → ℝ) (μ : ℝ) : ℝ :=
  4 * ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2 * ellH v μ)⁻¹ * ellH v μ / (2 * Real.pi)
    + 2

/-- **The per-slot piece statement** — the common shape of the eight channel pieces
`chAslot, chAimg, chBslot, chBimg` (the `chSlotAB` half) and `chCslot, chCimg, chDslot, chDimg`
(the `chSlotCD` half): a constant `A`, an extra `N`-threshold `T : ℝ → ℕ`, the budget `budget μ`
for the arithmetic `2ℓ⁻³(4μ²ℓ⁶(1+ℓ⁻³)A μ) ≤ budget μ`, and the per-pair bound for every `Nmin`
dominating `⌈chNThresh⌉` and `T`.  The eight pieces are delegated with the budget `μ (a v)` each,
so that their eight budgets sum to `8 μ (a v) ≤ ½·errKafz v R μ 16` (`errKafz_ge`). -/
noncomputable def SlotPieceBound (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (R J ε₀ : ℝ) (budget : ℝ → ℝ)
    (slot : ∀ (n : ℕ) (μ : ℝ) (N : ℕ) (i j : Fin n), (Submission.BoseGases.X n → ℝ) → ℂ) :
    Prop :=
  ∃ (A : ℝ → ℝ) (T : ℝ → ℕ), (∀ μ : ℝ, 0 ≤ A μ) ∧
    (∀ μ : ℝ, 0 < μ →
      2 * (ellH v μ) ^ (-3 : ℤ)
        * (4 * μ ^ 2 * (ellH v μ) ^ 6 * (1 + (ellH v μ) ^ (-3 : ℤ)) * A μ)
        ≤ budget μ) ∧
    (∀ (Nmin : ℝ → ℕ), (∀ μ : ℝ, ⌈chNThresh v μ⌉₊ ≤ Nmin μ) →
      (∀ μ : ℝ, T μ ≤ Nmin μ) →
      (∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        R ≤ ellH v μ * Submission.BoseGases.chiR0 ∧ 4 * R ≤ ellH v μ) →
      ∀ (HM : ∀ μ : ℝ, HonestModes v μ), (∀ μ, Nmin μ ≤ (HM μ).N) →
        ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
          J ≤ (Work.BoseBox.paramsAt μ (BoseGases.a v)).KB ^ 3 →
          ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (BoseGases.a v))),
            (n : ℝ) ≤ 2 * μ * Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3 →
            0 < Work.BoseBoxFix.normB v μ n Φ →
            Work.BoseBoxFix.IsLowB v h J μ n Φ →
          Work.BoseBox.SpectralNPlusLe (Work.BoseBox.sideAt μ (BoseGases.a v))
            (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ)
            (Φ : Submission.BoseGases.X n → ℝ) →
            ∀ (i j : Fin n), i ≠ j →
              ‖slot n μ (HM μ).N i j
                  (boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ))‖
                ≤ A μ * Work.BoseBoxFix.normB v μ n Φ)


/-- **A single channel piece.**  A constant `K0 > 0`, a bound constant `A : ℝ → ℝ` and an
`N`-threshold `T : ℝ → ℕ` such that the per-pair bound holds with the budget `K0·μ·(a v)`.  The
`K0` is produced by the piece's prover; the final error coefficient `C` of the target is chosen at
the end as twice the sum of the eight `K0`'s — that is why the budget carries a constant factor,
which is exactly the freedom the arithmetic of `errKafz` has (`errKafz v R μ C ≥ C·μ·(a v)` is
all the budget ever sees). -/
noncomputable def SlotPiece (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (R J ε₀ : ℝ)
    (slot : ∀ (n : ℕ) (μ : ℝ) (N : ℕ) (i j : Fin n), (Submission.BoseGases.X n → ℝ) → ℂ) :
    Prop :=
  ∃ K0 : ℝ, 0 < K0 ∧
    SlotPieceBound v h fc fu R J ε₀ (fun μ => K0 * (μ * BoseGases.a v)) slot

/-- The real box restriction of a permutation-invariant state is permutation invariant
(the box `abox n ℓ` is a product set, hence invariant under relabelling). -/
theorem permInvariant_boxRestrictR {n : ℕ} {ℓ : ℝ} {Φ : Submission.BoseGases.X n → ℝ}
    (hΦ : Submission.BoseGases.PermInvariant n Φ) :
    Submission.BoseGases.PermInvariant n (boxRestrictR ℓ Φ) := by
  intro σ x
  have hmem : (Submission.BoseGases.actPerm n σ x ∈ Submission.BoseGases.abox n ℓ)
      ↔ (x ∈ Submission.BoseGases.abox n ℓ) := by
    rw [Submission.BoseGases.mem_abox_iff, Submission.BoseGases.mem_abox_iff]
    constructor
    · intro h i
      have := h (σ.symm i)
      simpa [Submission.BoseGases.actPerm] using this
    · intro h i
      exact h (σ i)
  simp only [boxRestrictR, hΦ σ x]
  by_cases hx : x ∈ Submission.BoseGases.abox n ℓ
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.mpr hx)]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun hc => hx (hmem.mp hc))]

/-- The real box restriction of a smooth state is measurable and bounded. -/
theorem boxRestrictR_measurable_bounded {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : Continuous Φ) :
    Measurable (boxRestrictR ℓ Φ) ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |boxRestrictR ℓ Φ x| ≤ C := by
  constructor
  · unfold boxRestrictR
    exact hΦ.measurable.mul
      (measurable_const.indicator (Submission.BoseGases.abox_measurable n ℓ))
  · obtain ⟨C, hC⟩ := (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn
      hΦ.continuousOn
    refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
    rw [boxRestrictR]
    by_cases hx : x ∈ Submission.BoseGases.abox n ℓ
    · rw [Set.indicator_of_mem hx, mul_one]
      exact le_trans (by simpa [Real.norm_eq_abs] using hC x hx) (le_max_left _ _)
    · rw [Set.indicator_of_notMem hx, mul_zero, abs_zero]
      exact le_max_right _ _

end Work.BoseBoxFock
