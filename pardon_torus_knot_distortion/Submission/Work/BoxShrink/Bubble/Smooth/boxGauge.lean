import Mathlib
import Submission.Work.BoxShrink.Bubble.Smooth

/-!
# A smooth gauge dominating Pardon's box norm

`Submission.boxNorm c σ` is the piecewise-linear function whose sublevel sets are Pardon's boxes
`Submission.PBox s c σ`; it is `max` of the three functions
`y ↦ |y (σ i) - c (σ i)| / boxSide i`, hence only Lipschitz, with corners.  Many arguments
(such as the flow construction of the push-off in `Work.BoxShrink.Bubble.Smooth`) need a *smooth*
function which is squeezed between `boxNorm` and `boxNorm + ε`.

This file provides it, by the standard "log-sum-exp" smoothing of the maximum: for `β > 0` put

`gaugeFun c σ β y = (1/β) * log (∑ i, (exp (β * t i) + exp (-(β * t i))))`,
where `t i = (y (σ i) - c (σ i)) / boxSide i`.

Since `max_i |t i| = boxNorm c σ y`, the sum lies between `exp (β * boxNorm c σ y)` and
`6 * exp (β * boxNorm c σ y)`, so that

`boxNorm c σ y ≤ gaugeFun c σ β y ≤ boxNorm c σ y + log 6 / β`;

`gaugeFun c σ β` is `C^∞` because `exp` is and the argument of `log` is a strictly positive sum.
Choosing `β = log 6 / ε` gives the gauge of `boxGauge`.
-/

namespace Work.BoxShrink.Bubble.Smooth

open LeanEval.KnotTheory.PardonDistortion

noncomputable section

/-- The `i`-th normalised signed coordinate of `y` relative to the box centre `c`.  The box norm is
the maximum of the three absolute values of these. -/
def coord (c : R3) (σ : Equiv.Perm (Fin 3)) (i : Fin 3) (y : R3) : ℝ :=
  (y (σ i) - c (σ i)) / Submission.boxSide i

/-- The log-sum-exp smoothing of the box norm, at smoothing parameter `β > 0`. -/
def gaugeFun (c : R3) (σ : Equiv.Perm (Fin 3)) (β : ℝ) : R3 → ℝ :=
  fun y => (1 / β) * Real.log (∑ i : Fin 3,
    (Real.exp (β * coord c σ i y) + Real.exp (-(β * coord c σ i y))))

/-- The box norm is the maximum of the three absolute normalised coordinates. -/
theorem boxNorm_eq_max_coord (c : R3) (σ : Equiv.Perm (Fin 3)) (y : R3) :
    Submission.boxNorm c σ y
      = max (max (|coord c σ 0 y|) (|coord c σ 1 y|)) (|coord c σ 2 y|) := by
  rw [Submission.boxNorm,
    show |coord c σ 0 y| = |y (σ 0) - c (σ 0)| / Submission.boxSide 0 from by
      rw [coord, abs_div, abs_of_pos (Submission.boxSide_pos 0)],
    show |coord c σ 1 y| = |y (σ 1) - c (σ 1)| / Submission.boxSide 1 from by
      rw [coord, abs_div, abs_of_pos (Submission.boxSide_pos 1)],
    show |coord c σ 2 y| = |y (σ 2) - c (σ 2)| / Submission.boxSide 2 from by
      rw [coord, abs_div, abs_of_pos (Submission.boxSide_pos 2)]]

/-- The map `y ↦ β * coord c σ i y` is `C²`. -/
theorem contDiff_coord (c : R3) (σ : Equiv.Perm (Fin 3)) (i : Fin 3) (β : ℝ) :
    ContDiff ℝ 2 (fun y : R3 => β * coord c σ i y) := by
  have h1 : ContDiff ℝ 2 (fun y : R3 => y (σ i)) :=
    (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (σ i) : R3 →L[ℝ] ℝ).contDiff
  have h2 : ContDiff ℝ 2 (fun y : R3 => y (σ i) - c (σ i)) := h1.sub contDiff_const
  have h3 : ContDiff ℝ 2 (fun y : R3 => (y (σ i) - c (σ i)) / Submission.boxSide i) :=
    h2.div_const _
  simpa [coord] using h3.const_smul β

/-- `gaugeFun c σ β` is `C²` (indeed `C^∞`): a sum of exponentials of `C²` functions followed by
`log` of a strictly positive function. -/
theorem contDiff_gaugeFun (c : R3) (σ : Equiv.Perm (Fin 3)) (β : ℝ) :
    ContDiff ℝ 2 (gaugeFun c σ β) := by
  unfold gaugeFun
  refine ContDiff.mul contDiff_const (ContDiff.log ?_ ?_)
  · exact ContDiff.sum (fun i _ =>
      ((contDiff_coord c σ i β).exp).add (((contDiff_coord c σ i β).neg).exp))
  · intro y
    exact ne_of_gt (Finset.sum_pos (fun i _ => add_pos (Real.exp_pos _) (Real.exp_pos _))
      Finset.univ_nonempty)

/-- If `exp (β s) ≤ S` with `β > 0`, then `s ≤ S` on the log-sum-exp scale. -/
theorem le_gauge_of {β : ℝ} (hβ : 0 < β) {S : ℝ} {s : ℝ}
    (hs : Real.exp (β * s) ≤ S) : s ≤ (1 / β) * Real.log S := by
  have hlog : β * s ≤ Real.log S := by
    have h := Real.log_le_log (Real.exp_pos _) hs
    rwa [Real.log_exp] at h
  calc s = (1 / β) * (β * s) := by
        rw [← mul_assoc, one_div, inv_mul_cancel₀ (ne_of_gt hβ), one_mul]
    _ ≤ (1 / β) * Real.log S :=
        mul_le_mul_of_nonneg_left hlog (by positivity)

/-- **Lower bound.**  The box norm is dominated by `gaugeFun`. -/
theorem boxNorm_le_gaugeFun (c : R3) (σ : Equiv.Perm (Fin 3)) {β : ℝ} (hβ : 0 < β) (y : R3) :
    Submission.boxNorm c σ y ≤ gaugeFun c σ β y := by
  set S : ℝ := ∑ i : Fin 3,
    (Real.exp (β * coord c σ i y) + Real.exp (-(β * coord c σ i y))) with hS
  have hgauge : gaugeFun c σ β y = (1 / β) * Real.log S := by rw [gaugeFun, ← hS]
  have hnonneg : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      0 ≤ Real.exp (β * coord c σ i y) + Real.exp (-(β * coord c σ i y)) :=
    fun i _ => add_nonneg (le_of_lt (Real.exp_pos _)) (le_of_lt (Real.exp_pos _))
  have hsummand : ∀ i : Fin 3,
      Real.exp (β * coord c σ i y) + Real.exp (-(β * coord c σ i y)) ≤ S := by
    intro i
    rw [hS]
    exact Finset.single_le_sum hnonneg (Finset.mem_univ i)
  have hcoord : ∀ i : Fin 3, |coord c σ i y| ≤ gaugeFun c σ β y := by
    intro i
    have h1 : coord c σ i y ≤ gaugeFun c σ β y := by
      rw [hgauge]
      exact le_gauge_of hβ
        (le_trans (le_add_of_nonneg_right (le_of_lt (Real.exp_pos _))) (hsummand i))
    have h2 : -(coord c σ i y) ≤ gaugeFun c σ β y := by
      rw [hgauge]
      refine le_gauge_of hβ ?_
      rw [mul_neg]
      exact le_trans (le_add_of_nonneg_left (le_of_lt (Real.exp_pos _))) (hsummand i)
    exact abs_le.mpr ⟨by linarith, h1⟩
  rw [boxNorm_eq_max_coord]
  exact max_le (max_le (hcoord 0) (hcoord 1)) (hcoord 2)

/-- **Upper bound.**  `gaugeFun` exceeds the box norm by at most `log 6 / β`. -/
theorem gaugeFun_le (c : R3) (σ : Equiv.Perm (Fin 3)) {β : ℝ} (hβ : 0 < β) (y : R3) :
    gaugeFun c σ β y ≤ Submission.boxNorm c σ y + Real.log 6 / β := by
  set S : ℝ := ∑ i : Fin 3,
    (Real.exp (β * coord c σ i y) + Real.exp (-(β * coord c σ i y))) with hS
  have hSpos : 0 < S := by
    rw [hS]
    exact Finset.sum_pos (fun i _ => add_pos (Real.exp_pos _) (Real.exp_pos _))
      Finset.univ_nonempty
  have hgauge : gaugeFun c σ β y = (1 / β) * Real.log S := by rw [gaugeFun, ← hS]
  have hle : ∀ i : Fin 3, |coord c σ i y| ≤ Submission.boxNorm c σ y := by
    intro i
    rw [boxNorm_eq_max_coord]
    fin_cases i <;> simp
  have hterm : ∀ i : Fin 3, Real.exp (β * coord c σ i y) + Real.exp (-(β * coord c σ i y))
      ≤ Real.exp (β * Submission.boxNorm c σ y)
        + Real.exp (β * Submission.boxNorm c σ y) := by
    intro i
    have hi := hle i
    have ht : coord c σ i y ≤ Submission.boxNorm c σ y := le_trans (le_abs_self _) hi
    have hn : -(coord c σ i y) ≤ Submission.boxNorm c σ y := le_trans (neg_le_abs _) hi
    refine add_le_add ?_ ?_
    · exact Real.exp_le_exp.mpr (by nlinarith [hβ, ht])
    · rw [← mul_neg]
      exact Real.exp_le_exp.mpr (by nlinarith [hβ, hn])
  have hSle : S ≤ 6 * Real.exp (β * Submission.boxNorm c σ y) := by
    have hcongr : (∑ i : Fin 3, (Real.exp (β * Submission.boxNorm c σ y)
        + Real.exp (β * Submission.boxNorm c σ y)))
        = 6 * Real.exp (β * Submission.boxNorm c σ y) := by
      rw [Fin.sum_univ_three]; ring
    rw [hS, ← hcongr]
    exact Finset.sum_le_sum (fun i _ => hterm i)
  have hlog : Real.log S ≤ Real.log (6 * Real.exp (β * Submission.boxNorm c σ y)) :=
    Real.log_le_log hSpos hSle
  have hlogval : Real.log (6 * Real.exp (β * Submission.boxNorm c σ y))
      = Real.log 6 + β * Submission.boxNorm c σ y := by
    rw [Real.log_mul (by norm_num) (ne_of_gt (Real.exp_pos _)), Real.log_exp]
  rw [hgauge]
  calc (1 / β) * Real.log S
      ≤ (1 / β) * (Real.log 6 + β * Submission.boxNorm c σ y) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [← hlogval]; exact hlog
    _ = Submission.boxNorm c σ y + Real.log 6 / β := by
        field_simp
        ring

theorem boxGauge (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3)) {ε : ℝ} (hε : 0 < ε) :
    ∃ gauge : LeanEval.KnotTheory.PardonDistortion.R3 → ℝ,
      ContDiff ℝ 2 gauge ∧
        (∀ y : LeanEval.KnotTheory.PardonDistortion.R3, 0 ≤ gauge y) ∧
        (∀ y : LeanEval.KnotTheory.PardonDistortion.R3, Submission.boxNorm c σ y ≤ gauge y) ∧
        (∀ y : LeanEval.KnotTheory.PardonDistortion.R3, gauge y ≤ Submission.boxNorm c σ y + ε) := by
  have hlog6pos : 0 < Real.log 6 := Real.log_pos (by norm_num)
  refine ⟨gaugeFun c σ (Real.log 6 / ε), contDiff_gaugeFun c σ _, ?_, ?_, ?_⟩
  · intro y
    exact le_trans (Submission.boxNorm_nonneg c σ y)
      (boxNorm_le_gaugeFun c σ (div_pos hlog6pos hε) y)
  · intro y
    exact boxNorm_le_gaugeFun c σ (div_pos hlog6pos hε) y
  · intro y
    refine le_trans (gaugeFun_le c σ (div_pos hlog6pos hε) y) ?_
    have h : Real.log 6 / (Real.log 6 / ε) = ε := by field_simp
    linarith [h]

end

end Work.BoxShrink.Bubble.Smooth
