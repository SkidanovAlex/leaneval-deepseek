import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.B3.SymCalc
import Submission.Work.Diff.STE.B3.SymCalcStep1.friedrichs_commutator_supp
import Submission.Work.Diff.STE.B3.SymCalcStep7.flat_multiplier_gain
import Submission.Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff
import Submission.Work.Diff.STE.B3.SymCalcStep8.flat_multiplier_commutator_no_one

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3.SymCalcStep8

/-!
# The flat multiplier commutator in function form, without the normalisation `ρ 0 = 1`

This is `Work.Diff.STE.B3.SymCalcStep7.flat_multiplier_gain` with the hypothesis `ρ 0 = 1`
removed: the only profile hypotheses kept are the bound `‖ρ‖ ≤ 1`, the *support* condition
`ρ y = 0` for `2 < Σ yᵢ²` and the Lipschitz bound.  (The normalisation is genuinely unnecessary
for the commutator estimate: the commutator only sees the *differences*
`ρ (ε (k - l)) - ρ (ε k)`, which are controlled by the support plus the Lipschitz bound, and
`ρ 0 = 1` is never used in the coefficient-level estimate — see
`Work.Diff.STE.B3.SymCalcStep1.flat_multiplier_commutator`.)

Route (exactly the route of `flat_multiplier_gain`, with the coefficient-level input supplied by
`Work.Diff.STE.B3.SymCalcStep8.flat_multiplier_commutator_no_one`): the two Fourier-coefficient
identities `fourierCoeff_mul_flatCut` / `fourierCoeff_flatCut_mul` identify the coefficients of the
commutator `β · S_ε h - S_ε (β · h)` with
`conv (fourierCoeff β) (trunc ρ ε (fourierCoeff h)) - trunc ρ ε (conv (fourierCoeff β)
(fourierCoeff h))`, and the coefficient-level estimate then bounds its `CSq (t+1)` by
`C · CSq t (fourierCoeff h)` with `C` independent of `ε ∈ (0,1]`.
-/

theorem flat_multiplier_gain_no_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : (ι → ℝ) → ℝ) (hρ : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1)
    (hdiam : ∀ y : ι → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (L : ℝ) (hL : 0 ≤ L) (hρlip : ∀ y z : ι → ℝ, ‖ρ y - ρ z‖ ≤ L * ‖y - z‖)
    (β : (ι → ℝ) → ℂ) (hβ : ContDiff ℝ (⊤ : ℕ∞) β) (hβp : Work.Diff.STE.Periodic1 β) (t : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε : ℝ), 0 < ε → ε ≤ 1 → ∀ h : (ι → ℝ) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) h → Work.Diff.STE.Periodic1 h →
      Work.Diff.STE.CSq (t + 1) (Work.Diff.STE.fourierCoeff (fun x : ι → ℝ =>
          β x * Work.Diff.STE.B3.SymCalc.flatCut ρ ε h x
            - Work.Diff.STE.B3.SymCalc.flatCut ρ ε (fun y : ι → ℝ => β y * h y) x))
        ≤ C * Work.Diff.STE.CSq t (Work.Diff.STE.fourierCoeff h) := by
  classical
  -- The coefficient-family certificate, with `a = fourierCoeff β` (rapidly decaying by
  -- `summable_wt_pow_mul_norm_fourierCoeff`).
  obtain ⟨C, hC0, hC⟩ :=
    Work.Diff.STE.B3.SymCalcStep8.flat_multiplier_commutator_no_one ρ hρ hdiam L hL hρlip
      (Work.Diff.STE.fourierCoeff β)
      (fun N => Work.Diff.STE.B3.summable_wt_pow_mul_norm_fourierCoeff N β hβ hβp) t
  refine ⟨C, hC0, ?_⟩
  intro ε hε hε1 h hh hhp
  -- The Fourier transform of the commutator is the commutator of the Fourier transforms.
  have hcoef : Work.Diff.STE.fourierCoeff (fun x : ι → ℝ => β x *
        Work.Diff.STE.B3.SymCalc.flatCut ρ ε h x
      - Work.Diff.STE.B3.SymCalc.flatCut ρ ε (fun y : ι → ℝ => β y * h y) x)
      = fun k : ι → ℤ => Work.Diff.STE.conv (Work.Diff.STE.fourierCoeff β)
            (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.fourierCoeff h)) k
          - Work.Diff.STE.trunc ρ ε (Work.Diff.STE.conv (Work.Diff.STE.fourierCoeff β)
              (Work.Diff.STE.fourierCoeff h)) k := by
    have hFh_sm : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.SymCalc.flatCut ρ ε h) :=
      Work.Diff.STE.B3.SymCalcStep1.flatCut_contDiff ρ hρ ε hh hhp
    have hFbh_sm : ContDiff ℝ (⊤ : ℕ∞)
        (Work.Diff.STE.B3.SymCalc.flatCut ρ ε (fun y : ι → ℝ => β y * h y)) :=
      Work.Diff.STE.B3.SymCalcStep1.flatCut_contDiff ρ hρ ε (hβ.mul hh)
        (Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hβp hhp)
    funext k
    rw [Work.Diff.STE.flat.fourierCoeff_sub_of_continuous
      (fun x : ι → ℝ => β x * Work.Diff.STE.B3.SymCalc.flatCut ρ ε h x)
      (Work.Diff.STE.B3.SymCalc.flatCut ρ ε (fun y : ι → ℝ => β y * h y))
      (hβ.continuous.mul hFh_sm.continuous) hFbh_sm.continuous k]
    rw [Work.Diff.STE.B3.SymCalcStep7.fourierCoeff_mul_flatCut ρ hρ ε β h hβ.continuous hh hhp k]
    rw [Work.Diff.STE.B3.SymCalcStep7.fourierCoeff_flatCut_mul ρ hρ ε β h hβ hβp hh hhp k]
  rw [hcoef]
  exact hC ε hε hε1 (Work.Diff.STE.fourierCoeff h)
    (Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff h hh hhp t)

end Work.Diff.STE.B3.SymCalcStep8
