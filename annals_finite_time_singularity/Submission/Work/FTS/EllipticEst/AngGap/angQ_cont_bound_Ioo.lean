/-
# Continuity and pointwise bound of the angular gradient `Q = h' - 2 cot(2θ) h`

`Q = angQ h` is the `L²`-form of the angular operator of Elgindi's §'Elliptic
Regularity Estimates'.  This file records the two elementary facts about it that
the Cauchy–Schwarz step of the gap-Wirtinger inequality needs:

* `Q` is continuous on the open interval `(0, π/2)` — `h'` is (`ContDiffOn` +
  `IsOpen`), `cot (2θ)` is (as `cos / sin`, the denominator being non-zero), and
  `h` is;
* `|Q θ| ≤ 3 C` there, from `|h' θ| ≤ C` and `|cot 2θ| ≤ 1/sin 2θ` together with
  the hypothesis `|h θ| ≤ C sin 2θ`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.AngGap.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngGap

theorem angQ_cont_bound_Ioo (h : ℝ → ℝ) (hh : ContDiffOn ℝ 2 h (Set.Icc 0 (π / 2)))
    (C : ℝ) (hC : 0 < C)
    (hbdd : ∀ θ ∈ Set.Icc 0 (π / 2), |h θ| ≤ C * Real.sin (2 * θ))
    (hbdd' : ∀ θ ∈ Set.Ioo 0 (π / 2), |deriv h θ| ≤ C) :
    ContinuousOn (Work.FTS.EllipticEst.AngGap.angQ h) (Set.Ioo 0 (π / 2)) ∧
    ∀ θ ∈ Set.Ioo 0 (π / 2), |Work.FTS.EllipticEst.AngGap.angQ h θ| ≤ 3 * C := by
  constructor
  · -- ## Continuity of `Q = h' - 2 cot(2θ) h` on `(0, π/2)`
    have hIoo : Set.Ioo (0 : ℝ) (π / 2) ⊆ Set.Icc (0 : ℝ) (π / 2) := Set.Ioo_subset_Icc_self
    have hdcont : ContinuousOn (deriv h) (Set.Ioo 0 (π / 2)) :=
      (hh.mono hIoo).continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
    have hhcont : ContinuousOn h (Set.Ioo 0 (π / 2)) := (hh.mono hIoo).continuousOn
    have hcotcont : ContinuousOn (fun θ : ℝ => Real.cot (2 * θ)) (Set.Ioo 0 (π / 2)) := by
      have hfun : (fun θ : ℝ => Real.cot (2 * θ))
          = fun θ : ℝ => Real.cos (2 * θ) / Real.sin (2 * θ) := by
        funext θ; rw [Real.cot_eq_cos_div_sin]
      rw [hfun]
      exact (by fun_prop : ContinuousOn (fun θ : ℝ => Real.cos (2 * θ))
          (Set.Ioo 0 (π / 2))).div (by fun_prop)
        (fun θ hθ => ne_of_gt (sin_two_pos hθ))
    exact hdcont.sub ((hcotcont.const_mul 2).mul hhcont)
  · -- ## The pointwise bound `|Q θ| ≤ 3 C`
    intro θ hθ
    have hspos : 0 < Real.sin (2 * θ) := sin_two_pos hθ
    have hcot := abs_cot_two_le hθ
    have hb := hbdd θ ⟨hθ.1.le, hθ.2.le⟩
    have hd := hbdd' θ hθ
    have h2 : |2 * Real.cot (2 * θ) * h θ| ≤ 2 * C := by
      have habs : |2 * Real.cot (2 * θ) * h θ| = 2 * (|Real.cot (2 * θ)| * |h θ|) := by
        rw [show 2 * Real.cot (2 * θ) * h θ = 2 * (Real.cot (2 * θ) * h θ) by ring, abs_mul,
          abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_mul]
      rw [habs]
      have hmul : |Real.cot (2 * θ)| * |h θ|
          ≤ (1 / Real.sin (2 * θ)) * (C * Real.sin (2 * θ)) :=
        mul_le_mul hcot hb (abs_nonneg _) (by positivity)
      have h3 : (1 / Real.sin (2 * θ)) * (C * Real.sin (2 * θ)) = C := by field_simp
      linarith [hmul.trans_eq h3]
    have hsplit : |deriv h θ - 2 * Real.cot (2 * θ) * h θ|
        ≤ |deriv h θ| + |2 * Real.cot (2 * θ) * h θ| := by
      have := abs_add_le (deriv h θ) (-(2 * Real.cot (2 * θ) * h θ))
      simpa only [sub_eq_add_neg, abs_neg] using this
    rw [angQ]
    linarith

end Work.FTS.EllipticEst.AngGap
