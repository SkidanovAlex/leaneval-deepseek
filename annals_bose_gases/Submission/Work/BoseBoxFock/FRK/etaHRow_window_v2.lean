import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.FRK.etaH_majorant_exists
import Submission.Work.BoseBoxFock.FRK.labN_sum_le_tsum_of_growth
import Submission.Work.BoseBoxFock.frkCore
import Submission.Work.BoseBoxFock.kinRow_lattice_tauPhi
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.FRK.etaHRow_window_v2` — the η_H row of the FRK design, at the
**well-posed** W3

The η_H row bounds the lattice sum of the threshold profile over the low-momentum window

    ∑_{k ∈ Lab N} η_H fu κ (k_k) · ℓ⁻³‖kinFT (winState ℓ ψ) k_k‖²
      ≤ 24 · momForm ℓ d 0 ψ + K · d⁶ · gapBare ℓ 0 ψ ,

from three inputs: the windowed high-momentum split `(S1)`, the lattice sampling row `(W3)` and a
`C^∞` majorant `H` of the threshold profile.

Unlike the sibling `etaHRow_window_of_pieces`, whose `hW3` (no parentheses) parses the gap
reserve *inside* the continuum integral and is therefore unsatisfiable, this statement carries the
reserve term **outside** the integral

    ∑' n, ℓ⁻³ σ(k_n)‖kinFT (winState ℓ ψ)(k_n)‖²
      ≤ (2π)⁻³ ∫ p, σ p ‖kinFT (winState ℓ ψ) p‖²
        + K (∫ p, ‖D⁶σ p‖) ℓ⁻³ gapBare ℓ 0 ψ ,

which is the form used by the proof (FS `lm:appendpoint`).

## The proof (four rows)

1. **Pointwise majorant.** `η_H fu κ ≤ H κ` (`hMaj`), so the `Lab N` sum is dominated by the
   `H κ`-sum; both sides are nonnegative.
2. **Truncation.** The finite `Lab N` sum is a sub-sum of the full `ℤ³` lattice series
   (`FRK.labN_sum_le_tsum_of_growth` applied to `g = winState ℓ ψ`), which W3 bounds.
3. **Continuum row.** `H κ ≤ 1_{3κ/2 ≤ ‖·‖}` pointwise, and the windowed high-momentum density is
   integrable (`integrable_window_mul_kinFT_sq`), so `MeasureTheory.integral_mono_of_nonneg` gives
   `∫ H κ ‖kinFT‖² ≤ ∫ 1_{…} ‖kinFT‖²`, which is S1: `≤ 23·momForm + K₁·d⁶·gapBare`.
4. **Reserve row.** `∫ p, ‖D⁶(H κ) p‖ ≤ C·κ⁻³` (`hMaj`) and `κ ≥ (d²ℓ)⁻¹` give
   `≤ K₃C·d⁶·gapBare` (`inv_cube_mul_inv_cube_le`: `κ⁻³ℓ⁻³ ≤ d⁶`).

Adding: `23·momForm + (K₁ + K₃C)·d⁶·gapBare ≤ 24·momForm + (K₁ + K₃C)·d⁶·gapBare`
(`momForm ≥ 0`), so the constant is `K = K₁ + K₃C`.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock.FRK

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The `(d²ℓ)⁻¹`-bookkeeping**: if `(d²ℓ)⁻¹ ≤ κ` with `0 < ℓ`, `0 < d`, then
`κ⁻³·ℓ⁻³ ≤ d⁶`.  This converts the six-derivative mass `∫‖∂⁶(H κ)‖ ≤ C·κ⁻³` of the majorant
into the target's `d⁶` row. -/
private theorem inv_cube_mul_inv_cube_le_v2 {d ℓ κ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hκ : (d ^ 2 * ℓ)⁻¹ ≤ κ) :
    κ ^ (-3 : ℤ) * (ℓ ^ 3)⁻¹ ≤ d ^ 6 := by
  have hd2l : 0 < d ^ 2 * ℓ := by positivity
  have hκpos : 0 < κ := lt_of_lt_of_le (inv_pos.mpr hd2l) hκ
  -- `κ⁻¹ ≤ d²ℓ`
  have hκinv : κ⁻¹ ≤ d ^ 2 * ℓ := (inv_le_comm₀ hκpos hd2l).mpr hκ
  -- hence `κ⁻³ ≤ (d²ℓ)³`
  have hcube : κ ^ (-3 : ℤ) ≤ (d ^ 2 * ℓ) ^ 3 := by
    have h1 : κ ^ (-3 : ℤ) = (κ⁻¹) ^ 3 := by
      rw [zpow_neg, inv_pow]
      rfl
    rw [h1]
    exact pow_le_pow_left₀ (by positivity) hκinv 3
  calc κ ^ (-3 : ℤ) * (ℓ ^ 3)⁻¹ ≤ (d ^ 2 * ℓ) ^ 3 * (ℓ ^ 3)⁻¹ :=
        mul_le_mul_of_nonneg_right hcube (by positivity)
    _ = d ^ 6 := by
        field_simp

/-- **The windowed high-momentum density is integrable**: for `0 < ℓ` and `ψ` smooth, the function
`p ↦ 1_{3κ/2 ≤ ‖p‖}·‖kinFT (winState ℓ ψ) p‖²` is integrable (it is dominated pointwise by the
integrable `p ↦ ‖kinFT (winState ℓ ψ) p‖²`). -/
private theorem integrable_window_mul_kinFT_sq_v2 {ℓ κ : ℝ} (hℓ : 0 < ℓ)
    {ψ : E3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    Integrable (fun p : E3 =>
      (if 3 * κ / 2 ≤ ‖p‖ then (1 : ℝ) else 0) *
        ‖Submission.BoseGases.kinFT (Work.BoseBoxFock.winState ℓ ψ) p‖ ^ 2) := by
  have hwcd : ContDiff ℝ (⊤ : ℕ∞) (Work.BoseBoxFock.winState ℓ ψ) :=
    Work.BoseBoxFock.winState_contDiff hℓ hψ
  have hwcs : HasCompactSupport (Work.BoseBoxFock.winState ℓ ψ) :=
    Work.BoseBoxFock.winState_hasCompactSupport hℓ ψ
  have hwint : Integrable (fun p : E3 =>
      ‖Submission.BoseGases.kinFT (Work.BoseBoxFock.winState ℓ ψ) p‖ ^ 2) :=
    Work.BoseBoxFock.SqrtKin.kinFT_sq_integrable hwcd hwcs
  refine hwint.mono' ?_ ?_
  · have hconst : Measurable (fun _ : E3 => (1 : ℝ)) := measurable_const
    have hms : MeasurableSet {p : E3 | 3 * κ / 2 ≤ ‖p‖} :=
      measurableSet_le measurable_const continuous_norm.measurable
    exact ((hconst.indicator hms).aestronglyMeasurable.mul hwint.aestronglyMeasurable)
  · filter_upwards with p
    have hw0 : (0 : ℝ) ≤ ‖Submission.BoseGases.kinFT (Work.BoseBoxFock.winState ℓ ψ) p‖ ^ 2 :=
      by positivity
    have hle : |(if 3 * κ / 2 ≤ ‖p‖ then (1 : ℝ) else 0)| ≤ 1 := by
      split_ifs <;> norm_num
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw0]
    calc |(if 3 * κ / 2 ≤ ‖p‖ then (1 : ℝ) else 0)| *
          ‖Submission.BoseGases.kinFT (Work.BoseBoxFock.winState ℓ ψ) p‖ ^ 2
        ≤ 1 * ‖Submission.BoseGases.kinFT (Work.BoseBoxFock.winState ℓ ψ) p‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hle hw0
      _ = ‖Submission.BoseGases.kinFT (Work.BoseBoxFock.winState ℓ ψ) p‖ ^ 2 := one_mul _

theorem etaHRow_window_v2
    (hS1 : ∃ K : ℝ, 0 ≤ K ∧ ∀ {ℓ d κ : ℝ}, 0 < ℓ → 0 < d → d ≤ 1 → (d ^ 2 * ℓ)⁻¹ ≤ κ →
      ∀ (ψ : EuclideanSpace ℝ (Fin 3) → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
      ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
          (if 3 * κ / 2 ≤ ‖p‖ then (1 : ℝ) else 0)
            * ‖Submission.BoseGases.kinFT (Work.BoseBoxFock.winState ℓ ψ) p‖ ^ 2
        ≤ 23 * Work.BoseKinLoc.momForm ℓ d 0 ψ
          + K * d ^ 6 * Work.BoseKinLoc.gapBare ℓ 0 ψ)
    (hW3 : ∃ K : ℝ, 0 ≤ K ∧ ∀ {ℓ : ℝ}, 0 < ℓ → ∀ (σ : EuclideanSpace ℝ (Fin 3) → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) σ → (∀ p, 0 ≤ σ p) →
      (∃ A : ℝ, ∀ p, |σ p| ≤ A * (1 + ‖p‖) ^ 2) →
      MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => ‖iteratedFDeriv ℝ 6 σ p‖) →
      ∀ (ψ : EuclideanSpace ℝ (Fin 3) → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
      (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * σ (Work.BoseBoxFock.kmomInt ℓ n) *
          ‖Submission.BoseGases.kinFT (Work.BoseBoxFock.winState ℓ ψ) (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2)
        ≤ ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : EuclideanSpace ℝ (Fin 3),
            σ p * ‖Submission.BoseGases.kinFT (Work.BoseBoxFock.winState ℓ ψ) p‖ ^ 2)
          + K * (∫ p : EuclideanSpace ℝ (Fin 3), ‖iteratedFDeriv ℝ 6 σ p‖) *
              (ℓ ^ 3)⁻¹ * Work.BoseKinLoc.gapBare ℓ 0 ψ)
    (hMaj : ∃ (C : ℝ) (H : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ), 0 ≤ C ∧
      (∀ (fu : Work.BoseBoxFix.LowCut) {κ : ℝ}, 0 < κ → ∀ k : EuclideanSpace ℝ (Fin 3),
        Work.BoseBoxFock.etaH fu κ k ≤ H κ k) ∧
      (∀ {κ : ℝ}, 0 < κ → ∀ k : EuclideanSpace ℝ (Fin 3),
        H κ k ≤ (if 3 * κ / 2 ≤ ‖k‖ then (1 : ℝ) else 0)) ∧
      (∀ {κ : ℝ}, 0 < κ → ContDiff ℝ (⊤ : ℕ∞) (H κ)) ∧
      (∀ {κ : ℝ}, 0 < κ → ∀ k : EuclideanSpace ℝ (Fin 3), 0 ≤ H κ k) ∧
      (∀ {κ : ℝ}, 0 < κ → ∃ A : ℝ, ∀ k : EuclideanSpace ℝ (Fin 3), |H κ k| ≤ A * (1 + ‖k‖) ^ 2) ∧
      (∀ {κ : ℝ}, 0 < κ → MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
        ‖iteratedFDeriv ℝ 6 (H κ) p‖)) ∧
      (∀ {κ : ℝ}, 0 < κ → (∫ p : EuclideanSpace ℝ (Fin 3),
        ‖iteratedFDeriv ℝ 6 (H κ) p‖) ≤ C * κ ^ (-3 : ℤ))) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {ℓ d κ : ℝ}, 0 < ℓ → 0 < d → d ≤ 1 → (d ^ 2 * ℓ)⁻¹ ≤ κ →
      ∀ (fu : Work.BoseBoxFix.LowCut) (N : ℕ) (ψ : EuclideanSpace ℝ (Fin 3) → ℝ),
        ContDiff ℝ (⊤ : ℕ∞) ψ →
      (∑ k : Work.BoseBoxFock.Lab N, Work.BoseBoxFock.etaH fu κ (Work.BoseBoxFock.kmomLab ℓ N k) *
          ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT (Work.BoseBoxFock.winState ℓ ψ)
            (Work.BoseBoxFock.kmomLab ℓ N k)‖ ^ 2))
        ≤ 24 * Work.BoseKinLoc.momForm ℓ d 0 ψ
          + K * d ^ 6 * Work.BoseKinLoc.gapBare ℓ 0 ψ := by
  classical
  obtain ⟨K₁, hK₁0, hS1'⟩ := hS1
  obtain ⟨K₃, hK₃0, hW3'⟩ := hW3
  obtain ⟨C, H, hC0, hHle, hHind, hHcd, hHnn, hHgrow, hHint, hHder⟩ := hMaj
  refine ⟨K₁ + K₃ * C, add_nonneg hK₁0 (mul_nonneg hK₃0 hC0), ?_⟩
  intro ℓ d κ hℓ hd hd1 hκ fu N ψ hψ
  have hκpos : 0 < κ := lt_of_lt_of_le (inv_pos.mpr (by positivity : (0 : ℝ) < d ^ 2 * ℓ)) hκ
  have hG0 : 0 ≤ Work.BoseKinLoc.gapBare ℓ 0 ψ := gapBare_nonneg ℓ ψ
  have hM0 : 0 ≤ Work.BoseKinLoc.momForm ℓ d 0 ψ := momForm_nonneg ℓ d ψ
  have hπ : (0 : ℝ) ≤ ((2 * Real.pi) ^ 3 : ℝ)⁻¹ := by positivity
  have hwcd : ContDiff ℝ (⊤ : ℕ∞) (Work.BoseBoxFock.winState ℓ ψ) :=
    Work.BoseBoxFock.winState_contDiff hℓ hψ
  have hwcs : HasCompactSupport (Work.BoseBoxFock.winState ℓ ψ) :=
    Work.BoseBoxFock.winState_hasCompactSupport hℓ ψ
  have hindint : Integrable (fun p : E3 =>
      (if 3 * κ / 2 ≤ ‖p‖ then (1 : ℝ) else 0) *
        ‖Submission.BoseGases.kinFT (Work.BoseBoxFock.winState ℓ ψ) p‖ ^ 2) :=
    integrable_window_mul_kinFT_sq_v2 hℓ hψ
  -- ## Rows 1 + 2: `η_H ≤ H κ`, reordering, truncation to the full lattice series
  have hsum_le : (∑ k : Work.BoseBoxFock.Lab N, Work.BoseBoxFock.etaH fu κ
        (Work.BoseBoxFock.kmomLab ℓ N k) *
        ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT (Work.BoseBoxFock.winState ℓ ψ)
          (Work.BoseBoxFock.kmomLab ℓ N k)‖ ^ 2))
      ≤ ∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * H κ (Work.BoseBoxFock.kmomInt ℓ n) *
        ‖Submission.BoseGases.kinFT (Work.BoseBoxFock.winState ℓ ψ)
          (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2 := by
    refine le_trans ?_ (labN_sum_le_tsum_of_growth hℓ (hHnn hκpos) (hHgrow hκpos) hwcd hwcs N)
    calc (∑ k : Work.BoseBoxFock.Lab N, Work.BoseBoxFock.etaH fu κ
            (Work.BoseBoxFock.kmomLab ℓ N k) *
            ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT (Work.BoseBoxFock.winState ℓ ψ)
              (Work.BoseBoxFock.kmomLab ℓ N k)‖ ^ 2))
        = ∑ k : Work.BoseBoxFock.Lab N,
            ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT (Work.BoseBoxFock.winState ℓ ψ)
              (Work.BoseBoxFock.kmomLab ℓ N k)‖ ^ 2) *
            Work.BoseBoxFock.etaH fu κ (Work.BoseBoxFock.kmomLab ℓ N k) :=
          Finset.sum_congr rfl fun k _ => by ring
      _ ≤ ∑ k : Work.BoseBoxFock.Lab N,
            ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT (Work.BoseBoxFock.winState ℓ ψ)
              (Work.BoseBoxFock.kmomLab ℓ N k)‖ ^ 2) *
            H κ (Work.BoseBoxFock.kmomLab ℓ N k) :=
          Finset.sum_le_sum fun k _ =>
            mul_le_mul_of_nonneg_left (hHle fu hκpos _) (by positivity)
      _ = ∑ k : Work.BoseBoxFock.Lab N, (ℓ ^ 3)⁻¹ * H κ
            (Work.BoseBoxFock.kmomLab ℓ N k) *
            ‖Submission.BoseGases.kinFT (Work.BoseBoxFock.winState ℓ ψ)
              (Work.BoseBoxFock.kmomLab ℓ N k)‖ ^ 2 :=
          Finset.sum_congr rfl fun k _ => by ring
  -- ## W3 (valid form) at `σ = H κ`
  have hW := hW3' hℓ (H κ) (hHcd hκpos) (hHnn hκpos) (hHgrow hκpos) (hHint hκpos) ψ hψ
  -- ## Row 3: the continuum piece is dominated by the (S1) left-hand side
  have hintle : (∫ p : E3, H κ p * ‖Submission.BoseGases.kinFT
        (Work.BoseBoxFock.winState ℓ ψ) p‖ ^ 2)
      ≤ ∫ p : E3, (if 3 * κ / 2 ≤ ‖p‖ then (1 : ℝ) else 0) *
        ‖Submission.BoseGases.kinFT (Work.BoseBoxFock.winState ℓ ψ) p‖ ^ 2 :=
    MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun p => mul_nonneg (hHnn hκpos p) (by positivity))
      hindint
      (Filter.Eventually.of_forall fun p =>
        mul_le_mul_of_nonneg_right (hHind hκpos p) (by positivity))
  have hint : ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, H κ p * ‖Submission.BoseGases.kinFT
        (Work.BoseBoxFock.winState ℓ ψ) p‖ ^ 2)
      ≤ 23 * Work.BoseKinLoc.momForm ℓ d 0 ψ + K₁ * d ^ 6 * Work.BoseKinLoc.gapBare ℓ 0 ψ := by
    have hS := hS1' hℓ hd hd1 hκ ψ hψ
    have h2 := mul_le_mul_of_nonneg_left hintle hπ
    linarith
  -- ## Row 4: the six-derivative reserve row (`κ⁻³ℓ⁻³ ≤ d⁶`)
  have hgap : K₃ * (∫ p : E3, ‖iteratedFDeriv ℝ 6 (H κ) p‖) * (ℓ ^ 3)⁻¹ *
        Work.BoseKinLoc.gapBare ℓ 0 ψ
      ≤ K₃ * C * d ^ 6 * Work.BoseKinLoc.gapBare ℓ 0 ψ := by
    have hder := hHder hκpos
    have hbook := inv_cube_mul_inv_cube_le_v2 hℓ hd hκ
    have h1 : K₃ * (∫ p : E3, ‖iteratedFDeriv ℝ 6 (H κ) p‖) ≤ K₃ * (C * κ ^ (-3 : ℤ)) :=
      mul_le_mul_of_nonneg_left hder hK₃0
    have h2 : K₃ * (∫ p : E3, ‖iteratedFDeriv ℝ 6 (H κ) p‖) * (ℓ ^ 3)⁻¹
        ≤ K₃ * C * d ^ 6 := by
      have h3 : K₃ * (∫ p : E3, ‖iteratedFDeriv ℝ 6 (H κ) p‖) * (ℓ ^ 3)⁻¹
          ≤ K₃ * (C * κ ^ (-3 : ℤ)) * (ℓ ^ 3)⁻¹ :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
      have h4 : K₃ * (C * κ ^ (-3 : ℤ)) * (ℓ ^ 3)⁻¹ = K₃ * C * (κ ^ (-3 : ℤ) * (ℓ ^ 3)⁻¹) :=
        by ring
      have h5 : K₃ * C * (κ ^ (-3 : ℤ) * (ℓ ^ 3)⁻¹) ≤ K₃ * C * d ^ 6 :=
        mul_le_mul_of_nonneg_left hbook (by positivity)
      rw [h4] at h3
      exact le_trans h3 h5
    exact mul_le_mul_of_nonneg_right h2 hG0
  -- ## assembly
  calc (∑ k : Work.BoseBoxFock.Lab N, Work.BoseBoxFock.etaH fu κ
        (Work.BoseBoxFock.kmomLab ℓ N k) *
        ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT (Work.BoseBoxFock.winState ℓ ψ)
          (Work.BoseBoxFock.kmomLab ℓ N k)‖ ^ 2))
      ≤ ∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * H κ (Work.BoseBoxFock.kmomInt ℓ n) *
        ‖Submission.BoseGases.kinFT (Work.BoseBoxFock.winState ℓ ψ)
          (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2 := hsum_le
    _ ≤ ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, H κ p * ‖Submission.BoseGases.kinFT
          (Work.BoseBoxFock.winState ℓ ψ) p‖ ^ 2)
        + K₃ * (∫ p : E3, ‖iteratedFDeriv ℝ 6 (H κ) p‖) * (ℓ ^ 3)⁻¹ *
          Work.BoseKinLoc.gapBare ℓ 0 ψ := hW
    _ ≤ 24 * Work.BoseKinLoc.momForm ℓ d 0 ψ
        + (K₁ + K₃ * C) * d ^ 6 * Work.BoseKinLoc.gapBare ℓ 0 ψ := by
        refine le_trans (add_le_add hint hgap) ?_
        calc (23 * Work.BoseKinLoc.momForm ℓ d 0 ψ + K₁ * d ^ 6 * Work.BoseKinLoc.gapBare ℓ 0 ψ)
              + K₃ * C * d ^ 6 * Work.BoseKinLoc.gapBare ℓ 0 ψ
            = 23 * Work.BoseKinLoc.momForm ℓ d 0 ψ
              + (K₁ + K₃ * C) * d ^ 6 * Work.BoseKinLoc.gapBare ℓ 0 ψ := by ring
          _ ≤ 24 * Work.BoseKinLoc.momForm ℓ d 0 ψ
              + (K₁ + K₃ * C) * d ^ 6 * Work.BoseKinLoc.gapBare ℓ 0 ψ := by linarith [hM0]

end Work.BoseBoxFock.FRK
