import Mathlib
import Submission.Work.LinnikAreas.A5.LFunction_disc_zeroCount
import Submission.Work.LinnikAreas.ownRepelNW.orderSum_invSq_bound_of_count

namespace Work.LinnikAreas.ownRepelNW

open scoped BigOperators

/-!
# The `kMult`-compatible (`pfP`-clash-free) inverse-square zero sum of `Λ(·,χ)`

`Work.LinnikAreas.ownRepelNW.completedLOrderShiftInvSqBound` proves the same estimate, but its
proof imports `Commons.NumberTheory.DirichletCharacter.completedL_ballZeroCount_uniform`, whose
closure contains `Commons.NumberTheory.Linnik.completedL_pf_identity_rect` — one of the two
modules declaring `Commons.NumberTheory.Linnik.pfP`.  Hence *that* module cannot be imported from
any `DhK`-side consumer (see `NOTE_pfP_import_clash.md`), although the statement mentions nothing
`DhK`-specific.

This module provides the same statement with a proof that stays entirely inside the
`pfP`-clash-free world, so it is importable from `Work.LinnikAreas.DhK.*` and from the `kMult`
family:

* the joint general lemma `orderSum_invSq_bound_of_count` (finite order sums controlled by a ball
  count for the divisor, uniformly in the count parameter `q`);
* the *uniform* disk zero count `Work.LinnikAreas.A5.ball_zeroCount_uniformL_A5`, which is
  proved from the explicit local count `diskZeroCount_two_half` + the window covering lemma
  `completedL_window_cover` (no `BombieriVinogradov`/`pfP`-clashing input).

As before, `‖s‖ ≤ 11` is used only through `log (2 + ‖s‖) ≤ log 13 ≤ log 16 = 4 log 2 ≤ 4`, which
is absorbed into the constant: the final constant is `3 C₀ + 1` where `C₀` is the constant of the
general lemma at the uniform count constant `c`.
-/

theorem completedLOrderShiftInvSqBound_rectFree : ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → χ.IsPrimitive →
    ∀ s : ℂ, ‖s‖ ≤ 11 → ∀ S : Finset ℂ,
      ∑ u ∈ S, (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℝ) *
        (1 / (1 + ‖s - u‖ ^ 2)) ≤ C * (Real.log (N : ℝ) + 2) := by
  classical
  obtain ⟨c, hcpos, hcount⟩ := Work.LinnikAreas.A5.ball_zeroCount_uniformL_A5
  have hc : 0 ≤ c := le_of_lt hcpos
  obtain ⟨C0, hC0pos, hgen⟩ := orderSum_invSq_bound_of_count (c := c) hc
  refine ⟨3 * C0 + 1, by linarith, ?_⟩
  intro N _ χ hχ hχprim s hs S
  have hlogN : (0:ℝ) ≤ Real.log (N : ℝ) := Commons.NumberTheory.Linnik.log_N_nonneg
  have hF : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) Set.univ :=
    fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z
  have hcnt : ∀ (a : ℂ) (ρ : ℝ), 1 ≤ ρ →
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall a ρ)) u : ℤ) : ℝ))
        ≤ c * (ρ + 1) * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2) :=
    fun a ρ hρ => hcount χ hχ hχprim a ρ hρ
  have hmain := hgen (DirichletCharacter.completedLFunction χ) hF
    (Real.log (N : ℝ)) hlogN hcnt s S
  have hlog : Real.log (2 + ‖s‖) ≤ 4 := by
    have h1 : Real.log (2 + ‖s‖) ≤ Real.log (13:ℝ) :=
      Real.log_le_log (by linarith [norm_nonneg s]) (by linarith)
    have h2 : Real.log (13:ℝ) ≤ Real.log (16:ℝ) :=
      Real.log_le_log (by norm_num) (by norm_num)
    have h3 : Real.log (16:ℝ) = 4 * Real.log 2 := by
      rw [show (16:ℝ) = 2^4 by norm_num, Real.log_pow]
      norm_num
    have h4 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
      linarith
    linarith
  calc ∑ u ∈ S, (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℝ) *
        (1 / (1 + ‖s - u‖ ^ 2))
      ≤ C0 * (Real.log (2 + ‖s‖) + Real.log (N : ℝ) + 2) := hmain
    _ ≤ (3 * C0 + 1) * (Real.log (N : ℝ) + 2) := by
        have h5 : C0 * (Real.log (2 + ‖s‖) + Real.log (N : ℝ) + 2)
            ≤ C0 * (4 + Real.log (N : ℝ) + 2) :=
          mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hC0pos)
        have h6 : C0 * (4 + Real.log (N : ℝ) + 2) = C0 * (Real.log (N : ℝ) + 6) := by ring
        have h7 : C0 * (Real.log (N : ℝ) + 6) ≤ (3 * C0 + 1) * (Real.log (N : ℝ) + 2) := by
          nlinarith [hlogN, hC0pos]
        linarith

end Work.LinnikAreas.ownRepelNW
