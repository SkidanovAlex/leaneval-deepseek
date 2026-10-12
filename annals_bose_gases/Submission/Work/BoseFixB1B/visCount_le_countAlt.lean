import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBoxFix.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.visCount_le_countAlt` — the χ-visible count is dominated by `n·‖Φ‖²`

This is the *existential-constant* (hence directly usable) form of
`Submission.Work.BoseFixB1B.visCount_le_count`: for every box state `Φ` at FS's parameters,

    ∫_{abox n ℓ} Φ²·(Σᵢ chiScale ℓ (xᵢ))  ≤  n·C·‖Φ‖²_{abox n ℓ} ,     ℓ = sideAt μ (a v) ,

with a constant `C` **independent of `μ`, `n`, `ℓ` and `Φ`** (in fact independent of everything:
`C = chiSup = (∫χ²)^{-1/2}`, the pointwise sup of `χ`).

The content is exactly two elementary facts:

* the pointwise bound `Σ_{i} chiScale ℓ (x i) ≤ n·chiSup`, which follows from
  `0 ≤ χ` and `|χ_ℓ| ≤ chiSup` (`Submission.BoseGases.abs_chiScale_le_chiSup`);
* the integrability of `Φ²` over the centred box `abox n ℓ` for **every** real `ℓ`
  (`Work.BoseFixB1B.integrableOn_sq_abox_of_continuous`): a `BoxState` is globally smooth
  (`BoxState.contDiff`), and `abox n ℓ ⊆ abox n (max ℓ 0)` with the latter compact — this is
  what makes the integrands non-degenerate, so that `integral_mono_of_nonneg` applies and Lean's
  junk value `∫ = 0` for non-integrable integrands can never produce a spurious `0 ≤ 0`.

No use is made of `h : ScatSol v`: the estimate holds for an arbitrary potential.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## Two elementary ingredients -/

/-- The centred cube is monotone in its radius *for all real radii*:
`acube ℓ ⊆ acube (max ℓ 0)` (for `ℓ < 0` the cube is empty, for `ℓ = 0` it is `{0}`). -/
lemma acube_subset_acube_max (ℓ : ℝ) :
    Submission.BoseGases.acube ℓ ⊆ Submission.BoseGases.acube (max ℓ 0) := by
  intro y hy m
  simp only [acube, Set.mem_Icc] at hy ⊢
  rcases le_total 0 ℓ with h | h
  · rw [max_eq_left h]; exact hy m
  · rw [max_eq_right h]; constructor <;> linarith [hy m]

/-- `Φ²` is integrable over the centred box `abox n ℓ`, for **every** real radius `ℓ`
and every continuous `Φ`. -/
lemma integrableOn_sq_abox_of_continuous {n : ℕ} {ℓ : ℝ} {Φ : X n → ℝ}
    (hΦ : Continuous Φ) :
    IntegrableOn (fun x : X n => (Φ x) ^ 2) (abox n ℓ) volume := by
  have hK : IsCompact (abox n (max ℓ 0)) :=
    (Metric.isCompact_iff_isClosed_bounded).mpr
      ⟨abox_isClosed n (max ℓ 0), abox_isBounded n (max ℓ 0) (le_max_right ℓ 0)⟩
  have hsub : abox n ℓ ⊆ abox n (max ℓ 0) := fun x hx i => acube_subset_acube_max ℓ (hx i)
  exact (ContinuousOn.integrableOn_compact hK (hΦ.pow 2).continuousOn).mono_set hsub

/-! ## The estimate -/

/-- The χ-visible count is bounded by `n·chiSup·‖Φ‖²` on the centred box, for every real
radius `ℓ` and every continuous `Φ`. -/
lemma visCount_le_chiSup_mul {n : ℕ} {ℓ : ℝ} {Φ : X n → ℝ} (hΦ : Continuous Φ) :
    (∫ x in Submission.BoseGases.abox n ℓ,
        (Φ x) ^ 2 * (∑ i : Fin n, Submission.BoseGases.chiScale ℓ (x i)))
      ≤ (n : ℝ) * Submission.BoseGases.chiSup *
          (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) := by
  have hInt : IntegrableOn (fun x : X n => (Φ x) ^ 2) (abox n ℓ) volume :=
    integrableOn_sq_abox_of_continuous hΦ
  have hmono :
      (∫ x in abox n ℓ, (Φ x) ^ 2 * (∑ i : Fin n, chiScale ℓ (x i)))
        ≤ ∫ x in abox n ℓ, ((Φ x) ^ 2 * ((n : ℝ) * Submission.BoseGases.chiSup)) := by
    refine integral_mono_of_nonneg ?_ ?_ ?_
    · filter_upwards with x
      exact mul_nonneg (sq_nonneg _)
        (Finset.sum_nonneg (fun i _ => chiScale_nonneg ℓ (x i)))
    · exact hInt.mul_const ((n : ℝ) * Submission.BoseGases.chiSup)
    · filter_upwards with x
      have hsum : (∑ i : Fin n, chiScale ℓ (x i)) ≤ (n : ℝ) * Submission.BoseGases.chiSup := by
        calc (∑ i : Fin n, chiScale ℓ (x i))
            ≤ ∑ _i : Fin n, Submission.BoseGases.chiSup :=
              Finset.sum_le_sum
                (fun i _ => le_trans (le_abs_self _) (abs_chiScale_le_chiSup ℓ (x i)))
          _ = (n : ℝ) * Submission.BoseGases.chiSup := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
  calc (∫ x in abox n ℓ, (Φ x) ^ 2 * (∑ i : Fin n, chiScale ℓ (x i)))
      ≤ ∫ x in abox n ℓ, ((Φ x) ^ 2 * ((n : ℝ) * Submission.BoseGases.chiSup)) := hmono
    _ = (∫ x in abox n ℓ, (Φ x) ^ 2) * ((n : ℝ) * Submission.BoseGases.chiSup) :=
        integral_mul_const ((n : ℝ) * Submission.BoseGases.chiSup) (fun x : X n => (Φ x) ^ 2)
    _ = (n : ℝ) * Submission.BoseGases.chiSup * (∫ x in abox n ℓ, (Φ x) ^ 2) := by ring

theorem visCount_le_countAlt {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {μ : ℝ} {n : ℕ}
        {Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))},
        (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 *
              (∑ i : Fin n,
                Submission.BoseGases.chiScale (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (x i)))
          ≤ (n : ℝ) * C * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
  refine ⟨Submission.BoseGases.chiSup, Submission.BoseGases.chiSup_pos, ?_⟩
  intro μ n Φ
  have hΦc : Continuous (Φ : Submission.BoseGases.X n → ℝ) := Φ.contDiff.continuous
  have hmain := visCount_le_chiSup_mul (n := n)
    (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (Φ := (Φ : Submission.BoseGases.X n → ℝ)) hΦc
  simpa [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB] using hmain

end Work.BoseFixB1B
