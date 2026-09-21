import Mathlib
import Submission.Work.VolterraLong.Defs
import Submission.Work.VolterraLong.Weighted.Basic

/-!
# The triangle inequality for the exponentially weighted supremum distance

`wdist lam Z U ≤ wdist lam Z W + wdist lam W U` for `lam ≥ 0`.

The proof is the usual sup-norm argument: on the interval the weight
`e^{-λ(b-s)}` is at most `1` (this is where `0 ≤ lam` is used), so for each `s`

`‖Z s - U s‖ e^{-λ(b-s)} ≤ (‖Z s - W s‖ + ‖W s - U s‖) e^{-λ(b-s)}`

is a sum of two summands each bounded by the corresponding `wdist`, and the
characterisation `wdist_le_iff` of the weighted distance as a sup turns the
pointwise bound into the desired inequality.  When `b < a` the interval is
empty and all three weighted distances vanish.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace Work.VolterraLong.Weighted

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- In the degenerate case where the interval `[a,b]` is empty (`b < a`), the
weighted distance vanishes identically (the supremum is taken over an empty
range). -/
lemma wdist_eq_zero_of_lt {a b : ℝ} (h : b < a) (lam : ℝ)
    (Z W : BoundedContinuousFunction (Set.Icc a b) E) : wdist lam Z W = 0 := by
  have : IsEmpty (Set.Icc a b) :=
    ⟨fun s => absurd (le_trans s.2.1 s.2.2) (not_le.mpr h)⟩
  rw [wdist, Set.range_eq_empty_iff.mpr inferInstance, Real.sSup_empty]

/-- The weight `e^{-λ(b-s)}` is at most `1` on `[a,b]` when `λ ≥ 0`. -/
lemma wdist_weight_le_one {a b lam : ℝ} (hlam : 0 ≤ lam) (s : Set.Icc a b) :
    Real.exp (-(lam * (b - (s : ℝ)))) ≤ 1 :=
  Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hlam (sub_nonneg.mpr s.2.2)))

/-- Pointwise triangle inequality for the integrand of `wdist`:
`‖Z s - U s‖ e^{-λ(b-s)}` is bounded by the sum of the corresponding
pointwise terms for `Z,W` and `W,U`. -/
lemma wdist_integrand_triangle {a b lam : ℝ}
    (Z W U : BoundedContinuousFunction (Set.Icc a b) E) (s : Set.Icc a b) :
    ‖Z s - U s‖ * Real.exp (-(lam * (b - (s : ℝ)))) ≤
      ‖Z s - W s‖ * Real.exp (-(lam * (b - (s : ℝ)))) +
        ‖W s - U s‖ * Real.exp (-(lam * (b - (s : ℝ)))) := by
  have h3 : ‖Z s - U s‖ ≤ ‖Z s - W s‖ + ‖W s - U s‖ := by
    rw [← sub_add_sub_cancel (Z s) (W s) (U s)]
    exact norm_add_le _ _
  calc ‖Z s - U s‖ * Real.exp (-(lam * (b - (s : ℝ))))
      ≤ (‖Z s - W s‖ + ‖W s - U s‖) * Real.exp (-(lam * (b - (s : ℝ)))) :=
        mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
    _ = ‖Z s - W s‖ * Real.exp (-(lam * (b - (s : ℝ)))) +
          ‖W s - U s‖ * Real.exp (-(lam * (b - (s : ℝ)))) := by ring

theorem wdist_triangle {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℝ} {lam : ℝ} (hlam : 0 ≤ lam)
    (Z W U : BoundedContinuousFunction (Set.Icc a b) E) :
    wdist lam Z U ≤ wdist lam Z W + wdist lam W U := by
  rcases le_or_gt a b with hab | hlt
  · rw [wdist_le_iff hab hlam]
    intro s
    calc ‖Z s - U s‖ * Real.exp (-(lam * (b - (s : ℝ))))
        ≤ ‖Z s - W s‖ * Real.exp (-(lam * (b - (s : ℝ)))) +
            ‖W s - U s‖ * Real.exp (-(lam * (b - (s : ℝ)))) :=
          wdist_integrand_triangle Z W U s
      _ ≤ wdist lam Z W + wdist lam W U :=
          add_le_add (le_wdist hlam Z W s) (le_wdist hlam W U s)
  · rw [wdist_eq_zero_of_lt hlt lam Z U, wdist_eq_zero_of_lt hlt lam Z W,
      wdist_eq_zero_of_lt hlt lam W U]
    norm_num

end Work.VolterraLong.Weighted
