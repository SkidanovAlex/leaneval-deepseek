import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Pert.Basic
import Submission.Work.Pert.EndDefect
import Submission.Work.Pert.GateDriftRate.high_band_defect_sum_le
import Submission.Work.Pert.GateDriftRate.deep_band_defect_sum_le
import Submission.Work.Pert.GateDriftRate.end_defect_le_half_alpha_Xi
import Submission.Work.Pert.GateDriftRate.waist_band_defect_sum_le
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Interfaces.Fatou

/-!
# `Work.Pert.GateDriftRate.gate_walk_drift_rate_log`

The drift of a legal walk in the lower gate `Qm Ξ α` for a perturbation datum `(σ, u, α)` of
`f z = z + z(z-σ)u z`:  along a walk `w_j = F^[j] z` (`F = liftF u σ α`) which stays in the gate,

  `‖F^[n] z - (z+n)‖ ≤ n·(1/2)‖α‖Ξ + 2^31(1+Ξ+1/Ξ+1/rr)(1 + log(2+M) + log(2+‖z‖))`.

## Structure

* **Telescoping** (`iterate_sub_eq_sum_defect`, proved here): the drift is `∑_{j<n} d_j`, where
  `d(w) = liftF u σ α w - (w+1)` is the per-step defect.

* **Coherent rate** (`end_defect_le_half_alpha_Xi`): the lower-end limit `D = endDefect u σ α` of
  the defect satisfies `‖D‖ ≤ (1/2)‖α‖Ξ`; this covers the linear term of the target.

* **Three band estimates** (`high_band_defect_sum_le`, `deep_band_defect_sum_le`,
  `waist_band_defect_sum_le`): splitting the walk indices by the *level* `t_j = Im(α w_j)` —
  upper band `t_j ≥ 1`, lower band `t_j ≤ -1`, waist `|t_j| < 1` — one has

  * upper band: the *unreduced* defects are summable: `∑ ‖d_j‖ ≲ 2^28 F L`
    (at the far upper end `τ_f → 0` hence `d → 0`, so the raw sum is small; it is only the
    *reduced* sum `∑(d_j - D)` that grows linearly with `n` there — see
    `GateCoboundary/NOTES_coboundary_is_FALSE.md`),
  * lower band: the *reduced* defects are summable: `∑ ‖d_j - D‖ ≲ 2^29 F L`
    (there `τ_f → σ` and `d → D` geometrically),
  * waist: `∑ ‖d_j - D‖ ≲ 2^30 F L`
    (the defect is `≤ 1/32` there and the gate's `Re`-width is `O(1/‖α‖)`, so only `O(1)` many
    lattice periods occur; the `log` factors absorb the harmonic contribution),

  with `F = 1+Ξ+1/Ξ+1/rr` and `L = 1 + log(2+M) + log(2+‖z‖)`.

The four estimates are proved in separate files; this file contains the telescoping identity, the
band decomposition (which is exactly where the *unreduced* defect is used in the upper band and the
*reduced* one in the lower bands, as the plane-wave refutation of the global reduced-sum bound
requires) and the final arithmetic.
-/

namespace Work.Pert.GateDriftRate

open Complex
open scoped BigOperators

noncomputable section

/-- Elementary splitting identity: for any `t : ℝ` and `f D : ℂ`, `f` is the sum of its upper-band
part, its lower-band reduced part, its waist reduced part, and the corresponding multiple of `D`. -/
private lemma defect_band_split (f D : ℂ) (t : ℝ) :
    f = (if 1 ≤ t then f else 0) + (if t ≤ -1 then f - D else 0)
        + (if ¬ (1 ≤ t) ∧ ¬ (t ≤ -1) then f - D else 0)
        + ((if t ≤ -1 then (1 : ℂ) else 0)
            + (if ¬ (1 ≤ t) ∧ ¬ (t ≤ -1) then (1 : ℂ) else 0)) * D := by
  by_cases h1 : 1 ≤ t
  · have h2 : ¬ (t ≤ -1) := by linarith
    have h3 : ¬ (¬ (1 ≤ t) ∧ ¬ (t ≤ -1)) := by tauto
    simp [h1, h2, h3]
  · by_cases h2 : t ≤ -1
    · have h3 : ¬ (¬ (1 ≤ t) ∧ ¬ (t ≤ -1)) := by tauto
      simp [h1, h2, h3]
    · have h3 : ¬ (1 ≤ t) ∧ ¬ (t ≤ -1) := ⟨h1, h2⟩
      simp [h1, h2, h3]

/-- **Telescoping of the defect sum.**  With `d(w) = liftF u σ α w - (w+1)` the defect of the
near-translation, the total drift along `n` steps is the sum of the defects at the walk points:
`F^[n] z - (z+n) = ∑_{j<n} d(F^[j] z)`. -/
theorem iterate_sub_eq_sum_defect {α σ : ℂ} {u : ℂ → ℂ} {z : ℂ} {n : ℕ} :
    (Work.Pert.liftF u σ α)^[n] z - (z + (n : ℂ)) =
      ∑ j ∈ Finset.range n,
        (Work.Pert.liftF u σ α ((Work.Pert.liftF u σ α)^[j] z)
          - ((Work.Pert.liftF u σ α)^[j] z + 1)) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih, Function.iterate_succ_apply']
    push_cast
    ring

/-! ### The four analytic inputs (proved in separate files of this directory) -/

/-- **The requested drift bound.** -/
theorem gate_walk_drift_rate_log {Ξ rr M : ℝ} {α σ : ℂ} {u : ℂ → ℂ} {z : ℂ} {n : ℕ}
    (hΞ : 0 < Ξ) (hrr : 0 < rr) (hM : 2 ^ 10 ≤ M) (hInF1 : MandelDim.InF1 α)
    (hα : ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ)))
    (hσ : σ ≠ 0) (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hu : DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr))
    (hu2 : ∀ w ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u w‖ ∧ ‖u w‖ ≤ 2)
    (hτQ : ∀ w ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α w ∈ Metric.ball (0 : ℂ) rr)
    (hNT : ∀ w ∈ Work.Pert.Qm Ξ α, ‖Work.Pert.liftF u σ α w - (w + 1)‖ ≤ 1 / 32)
    (hz : z ∈ Work.Pert.Qm Ξ α)
    (hwalk : ∀ j ≤ n, (Work.Pert.liftF u σ α)^[j] z ∈ Work.Pert.Qm Ξ α) :
    ‖(Work.Pert.liftF u σ α)^[n] z - (z + (n : ℂ))‖ ≤
      (n : ℝ) * ((1 / 2) * ‖α‖ * Ξ) +
        2 ^ 31 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M) + Real.log (2 + ‖z‖)) := by
  -- local abbreviations (definitionally transparent, so the band lemmas apply verbatim)
  let F : ℂ → ℂ := Work.Pert.liftF u σ α
  let P : ℕ → Prop := fun j => 1 ≤ (α * F^[j] z).im
  let Q : ℕ → Prop := fun j => (α * F^[j] z).im ≤ -1
  let R : ℕ → Prop := fun j => ¬ P j ∧ ¬ Q j
  let f : ℕ → ℂ := fun j => F (F^[j] z) - (F^[j] z + 1)
  let D : ℂ := Work.Pert.endDefect u σ α
  -- the four inputs
  have hHi : (∑ j ∈ (Finset.range n).filter P, ‖f j‖)
      ≤ 2 ^ 28 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M) + Real.log (2 + ‖z‖)) :=
    high_band_defect_sum_le hΞ hrr hM hInF1 hα hσ hnorm hu hu2 hτQ hNT hz hwalk
  have hLo : (∑ j ∈ (Finset.range n).filter Q, ‖f j - D‖)
      ≤ 2 ^ 29 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M) + Real.log (2 + ‖z‖)) :=
    deep_band_defect_sum_le hΞ hrr hM hInF1 hα hσ hnorm hu hu2 hτQ hNT hz hwalk
  have hMid : (∑ j ∈ (Finset.range n).filter R, ‖f j - D‖)
      ≤ 2 ^ 30 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M) + Real.log (2 + ‖z‖)) :=
    waist_band_defect_sum_le hΞ hrr hM hInF1 hα hσ hnorm hu hu2 hτQ hNT hz hwalk
  have hDle : ‖D‖ ≤ (1 / 2) * ‖α‖ * Ξ :=
    end_defect_le_half_alpha_Xi hΞ hrr hM hInF1 hα hσ hnorm hu hu2 hτQ hNT
  -- convert the band sums to indicator form
  rw [Finset.sum_filter] at hHi hLo hMid
  -- the pointwise decomposition
  have hpt : ∀ j : ℕ, f j
      = (if P j then f j else 0) + (if Q j then f j - D else 0)
        + (if R j then f j - D else 0)
        + ((if Q j then (1 : ℂ) else 0) + (if R j then (1 : ℂ) else 0)) * D := by
    intro j
    exact defect_band_split (f j) D ((α * F^[j] z).im)
  -- the sums of the four pieces
  have hsum : (∑ j ∈ Finset.range n, f j)
      = ((∑ j ∈ Finset.range n, (if P j then f j else 0))
          + (∑ j ∈ Finset.range n, (if Q j then f j - D else 0)))
        + ((∑ j ∈ Finset.range n, (if R j then f j - D else 0))
            + (∑ j ∈ Finset.range n,
                ((if Q j then (1 : ℂ) else 0) + (if R j then (1 : ℂ) else 0)) * D)) := by
    rw [Finset.sum_congr rfl (fun j _ => hpt j)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
    ring
  -- bounds for the four pieces
  have hA : ‖∑ j ∈ Finset.range n, (if P j then f j else 0)‖ ≤ 2 ^ 28 * (1 + Ξ + 1 / Ξ + 1 / rr)
      * (1 + Real.log (2 + M) + Real.log (2 + ‖z‖)) := by
    have h : ∀ j : ℕ, ‖(if P j then f j else 0)‖ = (if P j then ‖f j‖ else 0) := by
      intro j; by_cases hp : P j <;> simp [hp]
    calc ‖∑ j ∈ Finset.range n, (if P j then f j else 0)‖
        ≤ ∑ j ∈ Finset.range n, ‖(if P j then f j else 0)‖ := norm_sum_le _ _
      _ = ∑ j ∈ Finset.range n, (if P j then ‖f j‖ else 0) := Finset.sum_congr rfl (fun j _ => h j)
      _ ≤ _ := hHi
  have hB : ‖∑ j ∈ Finset.range n, (if Q j then f j - D else 0)‖
      ≤ 2 ^ 29 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M) + Real.log (2 + ‖z‖)) := by
    have h : ∀ j : ℕ, ‖(if Q j then f j - D else 0)‖ = (if Q j then ‖f j - D‖ else 0) := by
      intro j; by_cases hq : Q j <;> simp [hq]
    calc ‖∑ j ∈ Finset.range n, (if Q j then f j - D else 0)‖
        ≤ ∑ j ∈ Finset.range n, ‖(if Q j then f j - D else 0)‖ := norm_sum_le _ _
      _ = ∑ j ∈ Finset.range n, (if Q j then ‖f j - D‖ else 0) :=
          Finset.sum_congr rfl (fun j _ => h j)
      _ ≤ _ := hLo
  have hC : ‖∑ j ∈ Finset.range n, (if R j then f j - D else 0)‖
      ≤ 2 ^ 30 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M) + Real.log (2 + ‖z‖)) := by
    have h : ∀ j : ℕ, ‖(if R j then f j - D else 0)‖ = (if R j then ‖f j - D‖ else 0) := by
      intro j; by_cases hr : R j <;> simp [hr]
    calc ‖∑ j ∈ Finset.range n, (if R j then f j - D else 0)‖
        ≤ ∑ j ∈ Finset.range n, ‖(if R j then f j - D else 0)‖ := norm_sum_le _ _
      _ = ∑ j ∈ Finset.range n, (if R j then ‖f j - D‖ else 0) :=
          Finset.sum_congr rfl (fun j _ => h j)
      _ ≤ _ := hMid
  have hE : ‖∑ j ∈ Finset.range n,
        ((if Q j then (1 : ℂ) else 0) + (if R j then (1 : ℂ) else 0)) * D‖
      ≤ (n : ℝ) * ((1 / 2) * ‖α‖ * Ξ) := by
    have hcard : (∑ j ∈ Finset.range n,
          ((if Q j then (1 : ℂ) else 0) + (if R j then (1 : ℂ) else 0)))
        = ((((Finset.range n).filter Q).card : ℕ) : ℂ)
          + ((((Finset.range n).filter R).card : ℕ) : ℂ) := by
      rw [Finset.sum_add_distrib]
      congr 1
      · rw [Finset.card_filter]; push_cast; rfl
      · rw [Finset.card_filter]; push_cast; rfl
    have hle : ((Finset.range n).filter Q).card + ((Finset.range n).filter R).card ≤ n := by
      have hdisj : Disjoint ((Finset.range n).filter Q) ((Finset.range n).filter R) := by
        rw [Finset.disjoint_left]
        intro j hjQ hjR
        simp only [Finset.mem_filter] at hjQ hjR
        exact hjR.2.2 hjQ.2
      have hsub : ((Finset.range n).filter Q) ∪ ((Finset.range n).filter R) ⊆ Finset.range n := by
        intro j hj
        simp only [Finset.mem_union, Finset.mem_filter] at hj
        rcases hj with h | h <;> exact h.1
      calc ((Finset.range n).filter Q).card + ((Finset.range n).filter R).card
          = (((Finset.range n).filter Q) ∪ ((Finset.range n).filter R)).card :=
            (Finset.card_union_of_disjoint hdisj).symm
        _ ≤ (Finset.range n).card := Finset.card_le_card hsub
        _ = n := Finset.card_range n
    have hcast : ((((Finset.range n).filter Q).card : ℕ) : ℂ)
          + ((((Finset.range n).filter R).card : ℕ) : ℂ)
        = ((((Finset.range n).filter Q).card + ((Finset.range n).filter R).card : ℕ) : ℂ) := by
      push_cast; ring
    rw [← Finset.sum_mul, hcard, hcast, norm_mul, Complex.norm_natCast]
    exact mul_le_mul (by exact_mod_cast hle) hDle (norm_nonneg D) (Nat.cast_nonneg n)
  -- assemble
  have hmain : ‖∑ j ∈ Finset.range n, f j‖
      ≤ (n : ℝ) * ((1 / 2) * ‖α‖ * Ξ)
        + 2 ^ 31 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M) + Real.log (2 + ‖z‖)) := by
    have h1 : ‖(∑ j ∈ Finset.range n, (if P j then f j else 0))
          + (∑ j ∈ Finset.range n, (if Q j then f j - D else 0))‖
        ≤ 2 ^ 28 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M) + Real.log (2 + ‖z‖))
          + 2 ^ 29 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M) + Real.log (2 + ‖z‖)) :=
      le_trans (norm_add_le _ _) (add_le_add hA hB)
    have h2 : ‖(∑ j ∈ Finset.range n, (if R j then f j - D else 0))
          + (∑ j ∈ Finset.range n,
              ((if Q j then (1 : ℂ) else 0) + (if R j then (1 : ℂ) else 0)) * D)‖
        ≤ 2 ^ 30 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M) + Real.log (2 + ‖z‖))
          + (n : ℝ) * ((1 / 2) * ‖α‖ * Ξ) :=
      le_trans (norm_add_le _ _) (add_le_add hC hE)
    have hA0 : (0 : ℝ) ≤ 1 + Ξ + 1 / Ξ + 1 / rr := by
      have h1 : (0 : ℝ) ≤ Ξ := le_of_lt hΞ
      have h2 : (0 : ℝ) ≤ 1 / Ξ := by positivity
      have h3 : (0 : ℝ) ≤ 1 / rr := by positivity
      linarith
    have hB0 : (0 : ℝ) ≤ 1 + Real.log (2 + M) + Real.log (2 + ‖z‖) := by
      have h1 : 0 ≤ Real.log (2 + M) := Real.log_nonneg (by linarith [hM])
      have h2 : 0 ≤ Real.log (2 + ‖z‖) :=
        Real.log_nonneg (by have := norm_nonneg z; linarith)
      linarith
    have harith : 2 ^ 28 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M) + Real.log (2 + ‖z‖))
          + (2 ^ 29 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M) + Real.log (2 + ‖z‖))
            + 2 ^ 30 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M) + Real.log (2 + ‖z‖)))
        ≤ 2 ^ 31 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M) + Real.log (2 + ‖z‖)) := by
      have := mul_nonneg hA0 hB0
      nlinarith [this]
    calc ‖∑ j ∈ Finset.range n, f j‖
        = ‖((∑ j ∈ Finset.range n, (if P j then f j else 0))
            + (∑ j ∈ Finset.range n, (if Q j then f j - D else 0)))
          + ((∑ j ∈ Finset.range n, (if R j then f j - D else 0))
            + (∑ j ∈ Finset.range n,
                ((if Q j then (1 : ℂ) else 0) + (if R j then (1 : ℂ) else 0)) * D))‖ := by
          rw [hsum]
      _ ≤ ‖(∑ j ∈ Finset.range n, (if P j then f j else 0))
            + (∑ j ∈ Finset.range n, (if Q j then f j - D else 0))‖
          + ‖(∑ j ∈ Finset.range n, (if R j then f j - D else 0))
            + (∑ j ∈ Finset.range n,
                ((if Q j then (1 : ℂ) else 0) + (if R j then (1 : ℂ) else 0)) * D)‖ :=
          norm_add_le _ _
      _ ≤ _ := by linarith [h1, h2, harith]
  calc ‖F^[n] z - (z + (n : ℂ))‖
      = ‖∑ j ∈ Finset.range n, f j‖ := by
        have h := iterate_sub_eq_sum_defect (α := α) (σ := σ) (u := u) (z := z) (n := n)
        exact congrArg Norm.norm h
    _ ≤ _ := hmain

end

end Work.Pert.GateDriftRate
