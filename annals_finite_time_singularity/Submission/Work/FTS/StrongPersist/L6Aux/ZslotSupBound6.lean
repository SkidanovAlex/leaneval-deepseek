import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.NatFactorial
import Submission.Work.FTS.Nonlinear.N4Fields.wang_field_smoothInt
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongPersist.L3Aux.acoef_gamCoef_slots_le
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.Spaces.ProductRuleInW
-- ===== merged: Submission.Work.FTS.Nonlinear.N4Fields.wrad_field_smoothInt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.Nonlinear.N4Fields

set_option maxHeartbeats 1600000

/-! ## Two elementary facts about radial (`z`-only) functions

Both are specialisations of the junk-free parts of the `D_θ`-calculus: `D_θ` carries the factor
`sin(2θ)`, so it kills every function of `z` alone, and `∂_z` kills the zero function. -/




/-! ## The pointwise bound

`Work.Spaces.pz_DthIter_mul_eq` expands `∂_z^k D_θ^j (φ·h)` binomially in both variables; the
`a ≥ 1` terms of the angular expansion are killed by the radiality of `φ`, and each of the
surviving `a = 0` terms is bounded by `Work.Spaces.WlInf_z_bound` (for `φ`) and
`Work.Spaces.factor_bound` (for `h`).  The resulting `2^k` summands are then summed with
`Nat.sum_range_choose`. -/



end Work.FTS.Nonlinear.N4Fields
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L6Aux.ZslotSupBound6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.L6Aux

/-! ## The Bell numbers of the rows `b ≤ 6` -/

/-- The Bell numbers of the rows `0 ≤ n ≤ 6` are `1, 1, 2, 5, 15, 52, 203`, all of them
well below `1000`. -/
theorem bell_row_six_le (n : ℕ) (hn : n ≤ 6) : Work.Spaces.bell n ≤ 1000 := by
  interval_cases n <;> decide

/-! ## `|D_z^b h| ≤ 1000 M` from the level-six weighted bounds -/

/-- **`D_z`-derivatives are bounded by the `z^j ∂_z^j`-bounds, up to order six.**  If the
smooth function `h` satisfies `|z^j ∂_z^j h| ≤ M` on `[0,∞) × [0,π/2]` for all `j ≤ 6`, then
the first six iterates of `D_z = z ∂_z` satisfy `|D_z^b h| ≤ 1000 M` on the whole domain, for
every `b ≤ 6`.  (Verbatim the level-four argument of
`Work.Spaces.DzIter_le_of_pzIter`, with `bell b ≤ 100` replaced by `bell b ≤ 1000`.) -/
theorem dzIter_le_of_pzIter_six {h : ℝ → ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hsmooth : ∀ θ ∈ Work.Spaces.Iθ, ContDiffOn ℝ ⊤ (fun z => h z θ) (Set.Ioi (-1)))
    (hbound : ∀ j ≤ 6, ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |z ^ j * Work.Spaces.pzIter j h z θ| ≤ M)
    (b : ℕ) (hb : b ≤ 6) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, |Work.Spaces.DzIter b h z θ| ≤ 1000 * M := by
  intro z hz θ hθ
  have hz' : z ∈ Set.Ioi (-1) := by
    simp only [Work.Spaces.Iz, Set.mem_Ici] at hz
    simp only [Set.mem_Ioi]; linarith
  rw [Work.Spaces.DzIter_eq_sum_scoef hsmooth b z hz' θ hθ]
  have hsum := Work.Spaces.abs_sum_scoef_mul_le b M (fun k => z ^ k * Work.Spaces.pzIter k h z θ)
    (fun k hk => hbound k (le_trans hk hb) z hz θ hθ)
  have hbell : (Work.Spaces.bell b : ℝ) ≤ 1000 := by exact_mod_cast bell_row_six_le b hb
  calc |∑ k ∈ Finset.range (b + 1),
        (Work.Spaces.scoef b k : ℝ) * (z ^ k * Work.Spaces.pzIter k h z θ)|
      ≤ (Work.Spaces.bell b : ℝ) * M := hsum
    _ ≤ 1000 * M := mul_le_mul_of_nonneg_right hbell hM

/-! ## The `z`-slot bound at level six -/

theorem ZslotSupBound6 : ∃ K : ℝ, 0 < K ∧ ∀ b ≤ 6, ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
    |Work.Spaces.DzIter b (fun z (_ : ℝ) => 2 * z / (1 + z) ^ 2) z θ| ≤ K := by
  refine ⟨1000 * 10080, by norm_num, ?_⟩
  intro b hb z hz θ hθ
  have hsmooth : ∀ θ' ∈ Work.Spaces.Iθ,
      ContDiffOn ℝ ⊤ (fun z : ℝ => 2 * z / (1 + z) ^ 2) (Set.Ioi (-1)) :=
    fun _ _ => Work.FTS.StrongPersist.L3Aux.contDiffOn_two_z_div
  have hbound : ∀ j ≤ 6, ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |z ^ j * Work.Spaces.pzIter j (fun z (_ : ℝ) => 2 * z / (1 + z) ^ 2) z θ| ≤ 10080 := by
    intro j hj z hz' θ hθ'
    have h1 := Work.FTS.StrongPersist.L3Aux.zpow_pzIter_two_z_div_le j hz' θ
    have h2 : (j.factorial : ℝ) * (j + 1) ≤ 5040 := by interval_cases j <;> norm_num
    linarith
  have hmain := dzIter_le_of_pzIter_six
    (h := fun z (_ : ℝ) => 2 * z / (1 + z) ^ 2) (M := 10080) (by norm_num)
    hsmooth hbound b hb z hz θ hθ
  linarith

end Work.FTS.StrongPersist.L6Aux
end
