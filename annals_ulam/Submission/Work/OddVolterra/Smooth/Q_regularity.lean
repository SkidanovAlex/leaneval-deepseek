import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Existence.E1_E2_contDiff
import Submission.Work.OddVolterra.Smooth.E1_E2_continuousOn_Icc

/-!
# Regularity of the right-hand side `Q` of the Abel system

`Q n h s = (-E₁(s) + ∂^{n+1}(momentRHS n) s, -E₂(s))` is the inhomogeneity of the
transition-slope Volterra equation for the odd case `d = 2n+1`.  This file proves

* `ContinuousOn (Q n h) (Icc a 1)`: the two inhomogeneities are continuous on `[a,1]`
  (`E1_E2_continuousOn_Icc`; the only delicate point is `s = 1`, where the radicand vanishes at
  the endpoints of the section), and the remaining term `∂^{n+1}(momentRHS n)` is continuous;
* `ContDiffOn ℝ 2 (Q n h) (Icc a b)` for `a < b < 1`: on `(0,1)` the section is uniformly
  non-degenerate, so both inhomogeneities are `C^∞` there (`E1_E2_contDiff`).

Note that the smallness hypothesis `|h| ≤ 1/100` of the paper's setting is *not* needed here:
the non-degeneracy of the section is supplied by the hypothesis `hmid` on the ball radicand.
-/

namespace Work.OddVolterra.Smooth

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval

open Commons.Geometry.Ulam

noncomputable section

set_option linter.unusedVariables false

/-- The ball right-hand side `momentRHS n : s ↦ C / √(1+s²)` is `C^∞`. -/
lemma Qreg_contDiff_momentRHS (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (Work.OddVolterra.momentRHS n) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => 1 + s ^ 2) := by fun_prop
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => Real.sqrt (1 + s ^ 2)) :=
    ContDiff.sqrt h1 (fun x => by positivity)
  have h3 : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => (Real.sqrt (1 + s ^ 2))⁻¹) :=
    ContDiff.inv h2 (fun x => by positivity)
  unfold Work.OddVolterra.momentRHS
  exact ContDiff.mul contDiff_const h3

/-- The `(n+1)`-st derivative of the ball right-hand side is continuous. -/
lemma Qreg_continuous_iteratedDeriv_momentRHS (n : ℕ) :
    Continuous (fun s : ℝ => iteratedDeriv (n + 1) (Work.OddVolterra.momentRHS n) s) :=
  (Qreg_contDiff_momentRHS n).continuous_iteratedDeriv (n + 1)
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl (n + 1))

/-- The `(n+1)`-st derivative of the ball right-hand side is `C^∞`. -/
lemma Qreg_contDiffOn_iteratedDeriv_momentRHS (n : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun s : ℝ => iteratedDeriv (n + 1) (Work.OddVolterra.momentRHS n) s) Set.univ := by
  rw [iteratedDeriv_eq_iterate]
  exact (ContDiff.iterate_deriv (n + 1) (Qreg_contDiff_momentRHS n)).contDiffOn

/-- **Regularity of the Abel inhomogeneity `Q`.**  Under the paper's hypotheses on the
perturbation `h` (smooth, supported on the transition window, and non-degeneracy of the ball
section), `Q n h` is continuous on `[a,1]` for every `a > 0`, and `C²` on every `[a,b]` with
`a < b < 1`. -/
theorem Q_regularity (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {a : ℝ}
    (ha : 0 < a)
    (hsupp : Function.support h ⊆
      Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hsmall : ∀ t : ℝ, |h t| ≤ 1 / 100)
    (hmid : ∀ s ∈ Set.Ioo (0 : ℝ) 1,
      ∀ t ∈ Set.Icc (-(Commons.Geometry.Ulam.profileX 1)) (Commons.Geometry.Ulam.profileX 1),
      0 < Work.OddVolterra.psi h Commons.Geometry.Ulam.semicircle s t) :
    ContinuousOn (Work.OddVolterra.Q n h) (Set.Icc a 1) ∧
    (∀ b : ℝ, a < b → b < 1 → ContDiffOn ℝ 2 (Work.OddVolterra.Q n h) (Set.Icc a b)) := by
  classical
  -- the two inhomogeneities and their smoothness on the open interval
  obtain ⟨hE1c, hE2c⟩ := E1_E2_continuousOn_Icc n hn hh hsupp hmid ha
  obtain ⟨hE1d, hE2d⟩ := Work.OddVolterra.Existence.E1_E2_contDiff n hn hh hmid
  have hRHScont := Qreg_continuous_iteratedDeriv_momentRHS n
  have hRHS2 := Qreg_contDiffOn_iteratedDeriv_momentRHS n
  have h2le : (2 : ℕ∞ω) ≤ (⊤ : ℕ∞) :=
    ENat.natCast_le_of_coe_top_le_withTop le_rfl 2
  constructor
  · -- continuity on `[a,1]`, component by component
    rw [continuousOn_pi]
    intro i
    fin_cases i
    · have hgoal : ContinuousOn (fun x : ℝ => - Work.OddVolterra.E1 n h x
          + iteratedDeriv (n + 1) (Work.OddVolterra.momentRHS n) x) (Set.Icc a 1) :=
        (hE1c.neg).add hRHScont.continuousOn
      convert hgoal using 1
      funext x
      simp [Work.OddVolterra.Q]
    · have hgoal : ContinuousOn (fun x : ℝ => - Work.OddVolterra.E2 n h x) (Set.Icc a 1) :=
        hE2c.neg
      convert hgoal using 1
      funext x
      simp [Work.OddVolterra.Q]
  · -- `C²` on `[a,b]` for `a < b < 1`, where the section stays inside the positivity region
    intro b hab hb1
    have hsub : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) 1 :=
      fun x hx => ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb1⟩
    have h0 : ContDiffOn ℝ 2 (fun x : ℝ => - Work.OddVolterra.E1 n h x
        + iteratedDeriv (n + 1) (Work.OddVolterra.momentRHS n) x) (Set.Icc a b) :=
      ((hE1d.mono hsub).neg.of_le h2le).add
        ((hRHS2.mono (Set.subset_univ _)).of_le h2le)
    have h1 : ContDiffOn ℝ 2 (fun x : ℝ => - Work.OddVolterra.E2 n h x) (Set.Icc a b) :=
      (hE2d.mono hsub).neg.of_le h2le
    rw [contDiffOn_pi]
    intro i
    fin_cases i
    · convert h0 using 1
      funext x
      simp [Work.OddVolterra.Q]
    · convert h1 using 1
      funext x
      simp [Work.OddVolterra.Q]

end

end Work.OddVolterra.Smooth
