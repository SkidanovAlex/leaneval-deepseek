/-
# `N0Aux.B4NA1` — the level-`4` bound for the `F_*`-only piece `NA1`

`NA1 α` is the `w`-independent half of the `N₀`-row; `H6Rows.FstarI12H6` gives
`HkMem α 6 (NA1 α)` and `HkNorm α 6 (NA1 α) ≤ K₁₂ α²`, and `HkSq_mono_order` upgrades the
level-`6` bound to the level-`4` one.  The extra factor `1 + HkSq α 5 w ≥ 1` absorbs the
`α`-dependence.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.FTS.StrongPersist.H6Rows.FstarI12H6
import Submission.Work.FTS.StrongPersist.H6Aux.Facts
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.N0row_defs
import Submission.Work.FTS.ClassC.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux

open Work.FTS.StrongPersist.H6Pair6Aux (NA1 NA4 NA5 NA6 NP3 NP4a NP4b NP5a NP5b NP6)

set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem NA1_HkSq4_le (C₀ : ℝ) : ∃ K : ℝ, 0 < K ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1,
    ∀ w : Work.FTS.Galerkin.Fn,
    Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
    Work.Spaces.HkSq α 4 (NA1 α) ≤ K * (1 + Work.Spaces.HkSq α 5 w) := by
  obtain ⟨K12, hK12, hNA1⟩ := Work.FTS.StrongPersist.H6Rows.FstarI12H6
  refine ⟨K12 ^ 2 + 1, by positivity, ?_⟩
  intro α hαIoc w _ _
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  obtain ⟨hmem6, hbd⟩ := hNA1 α hα hα1
  have h5w : (0 : ℝ) ≤ Work.Spaces.HkSq α 5 w := Work.Spaces.HkSq_nonneg α 5 w
  have hone : (1 : ℝ) ≤ 1 + Work.Spaces.HkSq α 5 w := by linarith
  have hmono : Work.Spaces.HkSq α 4 (NA1 α) ≤ Work.Spaces.HkSq α 6 (NA1 α) :=
    Work.FTS.StrongPersist.H6Aux.HkSq_mono_order α (by norm_num) hmem6
  have hsq : Work.Spaces.HkSq α 6 (NA1 α) = (Work.Spaces.HkNorm α 6 (NA1 α)) ^ 2 := by
    rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 (NA1 α))]
  have h3 : (Work.Spaces.HkNorm α 6 (NA1 α)) ^ 2 ≤ (K12 * α ^ 2) ^ 2 :=
    pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 6 (NA1 α)) hbd 2
  have h4 : (K12 * α ^ 2) ^ 2 ≤ K12 ^ 2 := by
    have h5 : (K12 * α ^ 2) ^ 2 = K12 ^ 2 * (α ^ 2) ^ 2 := by ring
    rw [h5]
    have h6 : α ^ 2 ≤ 1 := by nlinarith [hα, hα1]
    have h7 : (α ^ 2) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (α ^ 2), h6]
    calc K12 ^ 2 * (α ^ 2) ^ 2 ≤ K12 ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left h7 (sq_nonneg K12)
      _ = K12 ^ 2 := by ring
  have h8 : Work.Spaces.HkSq α 4 (NA1 α) ≤ K12 ^ 2 :=
    le_trans hmono (le_trans (le_of_eq hsq) (le_trans h3 h4))
  calc Work.Spaces.HkSq α 4 (NA1 α) ≤ K12 ^ 2 := h8
    _ ≤ K12 ^ 2 * (1 + Work.Spaces.HkSq α 5 w) := by
        have h9 : K12 ^ 2 * 1 ≤ K12 ^ 2 * (1 + Work.Spaces.HkSq α 5 w) :=
          mul_le_mul_of_nonneg_left hone (sq_nonneg K12)
        linarith [h9]
    _ ≤ (K12 ^ 2 + 1) * (1 + Work.Spaces.HkSq α 5 w) := by
        have hKnn : (0 : ℝ) ≤ K12 ^ 2 := sq_nonneg K12
        have hHnn : (0 : ℝ) ≤ 1 + Work.Spaces.HkSq α 5 w := by linarith
        nlinarith [hKnn, hHnn]

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux
