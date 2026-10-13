/-
# `SeriesAux.Basic` — shared elementary facts for the mode-series smoothness

The majorant `(m+1)^{-3/2}`, its summability, the smoothing of `iteratedDeriv`, and the
"integral of a continuous function on a compact subinterval of `(0,∞)`" helper.
-/
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series.SmoothAux

set_option autoImplicit false

/-- The majorant `maj m = (m+1)^{-3/2}`. -/
def maj (m : ℕ) : ℝ := (((m : ℝ) + 1) ^ (3 / 2 : ℝ))⁻¹

lemma maj_nonneg (m : ℕ) : 0 ≤ maj m := by
  have h : (0 : ℝ) < ((m : ℝ) + 1) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  simpa [maj] using inv_nonneg.mpr (le_of_lt h)

/-- The majorant is summable. -/
lemma summable_maj : Summable maj := by
  have h2 : Summable (fun n : ℕ => (((n : ℝ) + 1) ^ (3 / 2 : ℝ))⁻¹) := by
    have h : Summable (fun n : ℕ => ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
      (Real.summable_nat_rpow_inv (p := (3 / 2 : ℝ))).mpr (by norm_num)
    have h3 := (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹) 1).mpr h
    simpa only [Nat.cast_add, Nat.cast_one] using h3
  exact h2

/-- **Smoothing of `iteratedDeriv`.**  If `f` is `C^k` on `(0,∞)` for every `k`, then so is each
of its iterated derivatives. -/
lemma contDiffOn_iteratedDeriv {f : ℝ → ℝ} (hf : ∀ k : ℕ, ContDiffOn ℝ k f (Set.Ioi 0)) :
    ∀ (a n : ℕ), ContDiffOn ℝ n (iteratedDeriv a f) (Set.Ioi 0) := by
  intro a
  induction a with
  | zero => intro n; simpa only [iteratedDeriv_zero] using hf n
  | succ a ih =>
    intro n
    have h1 : ContDiffOn ℝ ((n : ℕ∞ω) + 1) (iteratedDeriv a f) (Set.Ioi 0) := by
      have := ih (n + 1)
      simpa only [Nat.cast_add, Nat.cast_one] using this
    have h2 := ((contDiffOn_succ_iff_deriv_of_isOpen (𝕜 := ℝ) isOpen_Ioi).1 h1).2.2
    rw [iteratedDeriv_succ]
    exact h2

/-- The real power `z ↦ z ^ s` is `C^n` on `(0,∞)`. -/
lemma contDiffOn_rpow_const (s : ℝ) (n : ℕ) :
    ContDiffOn ℝ n (fun z : ℝ => z ^ s) (Set.Ioi 0) :=
  contDiffOn_id.rpow_const_of_ne (fun x hx => ne_of_gt hx)

/-- On a compact interval inside `(0,∞)`, a function continuous on `(0,∞)` is interval
integrable. -/
lemma intervalIntegrable_of_continuousOn_Ioi {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Ioi 0))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : IntervalIntegrable f volume a b :=
  (hf.mono (fun t ht => by
    rw [Set.uIcc_of_le hab] at ht
    exact lt_of_lt_of_le ha ht.1)).intervalIntegrable

end Work.FTS.PhiStar.Series.SmoothAux
