import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Pert.Pin3.dev_horiz_log
import Submission.Work.Pert.Pin3.dev_vert_log
import Submission.Work.Pert.Pin3.dev_vert_log_neg
import Submission.Work.Pert.Pin3.dev_deriv_le_pt
import Submission.Work.Pert.Pin3.dev_seg_const
import Submission.Work.Pert.Qm_slice
import Submission.Work.Pert.dev_base_v3

namespace Work.Pert.PinAux

open MandelDim Complex Metric MeasureTheory

noncomputable section

/-!
# `Work.Pert.PinAux.dev_axis_transport`

Transport of the deviation `Dev := Φ - id` of a Fatou coordinate `Φ` on the gate `Qm Ξ α`
from a point `z` of the gate (whose `R₁`-ball lies in the gate) to the two axis points `± i T`.

The proof is assembled from two independent estimates, each delegated and proved in its own
file:

* `Work.Pert.PinAux.collar_to_medial` bounds the deviation between `z` and the *medial* point
  `med Ξ α z.im` of its slice (at the same height):
  `‖Dev z - Dev (med z.im)‖ ≤ Λ (1 + log (2 + ‖z‖)) + (c/(1-c)) (‖z - med z.im‖ + 1)`;
  this is the collar estimate (the point `z` may be arbitrarily close to the boundary of the
  gate, where `FatouDerivEstimate` is unavailable; that estimate is only used on the "fat" part
  and the thin part is handled by compactness).
* `Work.Pert.PinAux.medial_to_axis` transports the medial value to the axis points `± i T`:
  for a suitable `T ∈ [Y₀, Y₀+1]`,
  `‖Dev (med z.im) - Dev (±iT)‖ ≤ C (1 + log (2 + ‖z‖)) + Λ (|z.im ∓ T| + 1)`
  with `Λ ≤ 2 c/(1-c)`.

Both estimates carry a linear term with the true slope `c/(1-c)` (the deviation `Φ - id` of a
near-translation of defect `≤ c` can grow with slope `c/(1-c)`, e.g. `F w = w+(1-c)`,
`Φ w = w/(1-c)`); the two linear terms are combined here by the elementary lemmas `arith_lin`
and `arith_absorb`, the budget being `3 c/(1-c) ≤ 1/64` (which follows from `c ≤ 1/256`).
-/

/-- The deviation `Dev := Φ - id` of the Fatou coordinate. -/
def Dev (Φ : ℂ → ℂ) (w : ℂ) : ℂ := Φ w - w

/-- The midpoint of the gate slice at height `t` (the "medial" real part). -/
def xMid (Ξ : ℝ) (α : ℂ) (t : ℝ) : ℝ := (sliceLo Ξ α t + sliceHi Ξ t) / 2

/-- The medial point of the gate at height `t`. -/
def med (Ξ : ℝ) (α : ℂ) (t : ℝ) : ℂ := (xMid Ξ α t : ℂ) + (t : ℂ) * Complex.I

/-- The slice width `sliceHi - sliceLo` at height `t`: this is also `margA + margB`. -/
def width (Ξ : ℝ) (α : ℂ) (t : ℝ) : ℝ := sliceHi Ξ t - sliceLo Ξ α t

@[simp] lemma Dev_apply (Φ : ℂ → ℂ) (w : ℂ) : Dev Φ w = Φ w - w := rfl

lemma med_re (Ξ : ℝ) (α : ℂ) (t : ℝ) : (med Ξ α t).re = xMid Ξ α t := by
  simp [med]

lemma med_im (Ξ : ℝ) (α : ℂ) (t : ℝ) : (med Ξ α t).im = t := by
  simp [med]

lemma margA_med (Ξ : ℝ) (α : ℂ) (t : ℝ) :
    margA Ξ α (med Ξ α t) = width Ξ α t / 2 := by
  rw [margA_eq_sub_sliceLo (ξ := Ξ) (α := α) (z := med Ξ α t), med_re, med_im, xMid, width]
  ring

lemma margB_med (Ξ : ℝ) (α : ℂ) (t : ℝ) :
    margB Ξ α (med Ξ α t) = width Ξ α t / 2 := by
  rw [margB_eq_sliceHi_sub (ξ := Ξ) (α := α) (z := med Ξ α t), med_re, med_im, xMid, width]
  ring

lemma width_eq (Ξ : ℝ) (α : ℂ) (t : ℝ) :
    width Ξ α t = (1 / α).re - 2 * Ξ + |t| + |t + (1 / α).im| := by
  simp only [width, sliceHi, sliceLo]; ring

/-- **The walk relation**: if `w` and `F w` both lie in the gate, then the deviation of the
Fatou coordinate changes exactly by minus the defect of the near-translation.  This is
`IsFatouCoordOn`'s Abel relation `Φ (F w) = Φ w + 1` rewritten for `Dev = Φ - id`. -/
theorem dev_walk {F Φ : ℂ → ℂ} {Ξ : ℝ} {α : ℂ}
    (hΦ : MandelDim.IsFatouCoordOn F Φ (Work.Pert.Qm Ξ α))
    {w : ℂ} (hw : w ∈ Work.Pert.Qm Ξ α) (hFw : F w ∈ Work.Pert.Qm Ξ α) :
    Dev Φ (F w) - Dev Φ w = -(F w - (w + 1)) := by
  have h := hΦ.2.2 w hw hFw
  simp only [Dev]
  linear_combination h

/-- Consequence of the walk relation and the near-translation bound: the deviation is
Lipschitz along the walk. -/
theorem dev_walk_le {F Φ : ℂ → ℂ} {Ξ : ℝ} {α : ℂ} {K c : ℝ}
    (hΦ : MandelDim.IsFatouCoordOn F Φ (Work.Pert.Qm Ξ α))
    (hsharp : ∀ w ∈ Work.Pert.Qm Ξ α, ‖F w - (w + 1)‖ ≤ K / ‖w‖ + c)
    {w : ℂ} (hw : w ∈ Work.Pert.Qm Ξ α) (hFw : F w ∈ Work.Pert.Qm Ξ α) :
    ‖Dev Φ (F w) - Dev Φ w‖ ≤ K / ‖w‖ + c := by
  rw [dev_walk hΦ hw hFw, norm_neg]
  exact hsharp w hw

/-- The medial point of a nonempty slice lies in the gate. -/
theorem med_mem {Ξ : ℝ} {α : ℂ} {t : ℝ} (h : 0 < width Ξ α t) : med Ξ α t ∈ Qm Ξ α := by
  rw [mem_Qm_iff_marg, margA_med, margB_med]
  constructor <;> linarith

/-- The medial point has both margins equal to half the slice width, hence distance
`width/(2√2)` from the complement of the gate. -/
theorem med_clearance {Ξ : ℝ} {α : ℂ} {t : ℝ} {R : ℝ} (h : R * Real.sqrt 2 ≤ width Ξ α t / 2) :
    Metric.ball (med Ξ α t) R ⊆ Qm Ξ α := by
  by_cases hR : R ≤ 0
  · intro u hu
    rw [Metric.mem_ball] at hu
    exact absurd hu (not_lt.mpr (le_trans hR (dist_nonneg)))
  · have hRpos : 0 < R := not_le.mp hR
    have hR2 : 0 < R * Real.sqrt 2 := mul_pos hRpos (Real.sqrt_pos.mpr (by norm_num))
    have hmed : med Ξ α t ∈ Qm Ξ α := med_mem (by linarith)
    have hmin : R * Real.sqrt 2 ≤
        min (xMid Ξ α t - sliceLo Ξ α t) (sliceHi Ξ t - xMid Ξ α t) := by
      have h1 : xMid Ξ α t - sliceLo Ξ α t = width Ξ α t / 2 := by rw [xMid, width]; ring
      have h2 : sliceHi Ξ t - xMid Ξ α t = width Ξ α t / 2 := by rw [xMid, width]; ring
      rw [h1, h2, min_self]; exact h
    have hsub := ball_subset_Qm_of_margin_slice (ξ := Ξ) (α := α) (x := xMid Ξ α t) (t := t) (r := R)
      (by simpa [med] using hmed) hmin
    simpa [med] using hsub

/-- The horizontal displacement from `z` (a point of the gate) to the medial point of its slice
is at most half the slice width. -/
theorem norm_sub_med_le {Ξ : ℝ} {α : ℂ} {z : ℂ} (hz : z ∈ Qm Ξ α) :
    ‖z - med Ξ α z.im‖ ≤ width Ξ α z.im / 2 := by
  have hA := margA_eq_sub_sliceLo (ξ := Ξ) (α := α) (z := z)
  have hB := margB_eq_sliceHi_sub (ξ := Ξ) (α := α) (z := z)
  have hA0 : 0 < margA Ξ α z := ((mem_Qm_iff_marg Ξ α z).mp hz).1
  have hB0 : 0 < margB Ξ α z := ((mem_Qm_iff_marg Ξ α z).mp hz).2
  have hw : width Ξ α z.im = margA Ξ α z + margB Ξ α z := by
    rw [width, hA, hB]; ring
  have hd : z - med Ξ α z.im = (((z.re - xMid Ξ α z.im : ℝ)) : ℂ) := by
    rw [med]
    apply Complex.ext <;> simp
  have hzre : z.re - xMid Ξ α z.im = (margA Ξ α z - margB Ξ α z) / 2 := by
    rw [hA, hB]
    simp only [xMid]
    ring
  rw [hd, Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor
  · rw [hzre, hw]
    linarith
  · rw [hzre, hw]
    linarith

/-- The half slice width at height `t` is at most `|t|` plus a datum-dependent constant. -/
theorem width_div_two_le (Ξ : ℝ) (α : ℂ) (t : ℝ) :
    width Ξ α t / 2 ≤ |t| + ((1 / α).re - 2 * Ξ + |(1 / α).im|) / 2 := by
  rw [width_eq]
  have h1 : |t + (1 / α).im| ≤ |t| + |(1 / α).im| := abs_add_le _ _
  linarith

/-- The linear bookkeeping of the two transport estimates. -/
lemma arith_lin {c ΛB y ℓ dd M Y₀ : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 1 / 256)
    (hΛB0 : 0 ≤ ΛB) (hΛB : ΛB ≤ 2 * (c / (1 - c)))
    (hℓ : ℓ ≤ y + M) (hd : |dd| ≤ y + (Y₀ + 1)) :
    (c / (1 - c)) * (ℓ + 1) + ΛB * (|dd| + 1)
      ≤ (3 * (c / (1 - c))) * y
        + ((c / (1 - c)) * (M + 1) + (2 * (c / (1 - c))) * (Y₀ + 2)) := by
  have hrate0 : 0 ≤ c / (1 - c) := div_nonneg hc0 (by linarith)
  have h1 : (c / (1 - c)) * (ℓ + 1) ≤ (c / (1 - c)) * (y + M + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) hrate0
  have h2 : ΛB * (|dd| + 1) ≤ (2 * (c / (1 - c))) * (|dd| + 1) :=
    mul_le_mul_of_nonneg_right hΛB (by linarith [abs_nonneg dd])
  have h3 : (2 * (c / (1 - c))) * (|dd| + 1) ≤ (2 * (c / (1 - c))) * (y + (Y₀ + 1) + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  linarith [h1, h2, h3]

/-- The logarithmic absorption of the additive constant. -/
lemma arith_absorb {ΛA CB K : ℝ} (hΛA : 0 < ΛA) (hCB : 0 < CB) (hKnn : 0 ≤ K)
    (hlog2 : 0 < Real.log 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 1 + Real.log 2 ≤ L → K + (ΛA + CB) * L ≤ C * L := by
  have hKdiv : 0 ≤ K / (1 + Real.log 2) := div_nonneg hKnn (by linarith)
  refine ⟨ΛA + CB + K / (1 + Real.log 2) + 1, by linarith, ?_⟩
  intro L hL
  have hKle : K ≤ (K / (1 + Real.log 2)) * L := by
    calc K = (K / (1 + Real.log 2)) * (1 + Real.log 2) :=
          (div_mul_cancel₀ K (by linarith : (1 + Real.log 2) ≠ 0)).symm
      _ ≤ (K / (1 + Real.log 2)) * L := mul_le_mul_of_nonneg_left hL hKdiv
  nlinarith [hKle, hKdiv, hΛA, hCB, hL, hlog2]

end

end Work.Pert.PinAux
