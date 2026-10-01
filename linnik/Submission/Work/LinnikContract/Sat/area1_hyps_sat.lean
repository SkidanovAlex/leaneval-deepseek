import Mathlib
import Submission.Work.LinnikContract.Pre

set_option linter.unusedVariables false

namespace Work.LinnikContract.Sat

/-- Non-degeneracy of the hypothesis list of AREA 1 (`LBound13`): the side conditions
`3 ≤ k`, `ε' > 0`, `N ≥ 2`, `χ ≠ 1`, `1 - 1/k ≤ σ ≤ 1 + log log N / log N` are simultaneously
satisfiable, and with room to spare (both inequalities on σ are *strict*), so the area is not
vacuous and the Burgess range is a genuine interval.

Prover notes: take `k = 3`, `ε' = 1`, `N = 1000`, `σ = 3/4`, `t = 0`.
`1 - 1/3 < 3/4` is `norm_num`; `3/4 < 1 + log(log 1000)/log 1000` follows from
`0 < log (log 1000)` (i.e. `1 < log 1000`, from `Real.log_pos` and `Real.log_two_gt_d9`:
`log 1000 = 3 log 10 > 3 log 8 = 9 log 2 ≥ 6.2 > 1`) and `0 < log 1000` (`Real.log_pos`, `1 < 1000`).
For the character: `DirichletCharacter.exists_apply_ne_one_of_hasEnoughRootsOfUnity` at
`a = 3 : ZMod 1000` (a *unit* ≠ 1; `3 ≠ 1` by `decide`/`norm_num` since `ZMod 1000` has decidable
equality) gives `χ` with `χ 3 ≠ 1`, hence `χ ≠ 1` (the trivial character sends the unit `3` to `1`).
No `native_decide`. -/
theorem area1_hyps_sat :
    ∃ (k : ℕ) (ε' σ t : ℝ) (N : ℕ), 3 ≤ k ∧ 0 < ε' ∧ 2 ≤ N ∧
      (∃ χ : DirichletCharacter ℂ N, χ ≠ 1) ∧
      (1 - 1/(k:ℝ) ≤ σ ∧ σ ≤ 1 + Real.log (Real.log (N:ℝ)) / Real.log (N:ℝ)) ∧
      (1 - 1/(k:ℝ) < σ ∧ σ < 1 + Real.log (Real.log (N:ℝ)) / Real.log (N:ℝ)) := by
  -- positivity of the log-log fraction at `N = 1000`, the engine of both σ-inequalities
  have hlog : 0 < Real.log (1000:ℝ) := Real.log_pos (by norm_num)
  have hloglog : 0 < Real.log (Real.log (1000:ℝ)) := by
    apply Real.log_pos
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0:ℝ) < 1000)]
    linarith [Real.exp_one_lt_d9]
  have hfrac : 0 < Real.log (Real.log (1000:ℝ)) / Real.log (1000:ℝ) := div_pos hloglog hlog
  refine ⟨3, 1, 3/4, 0, 1000, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩
  · -- a non-trivial Dirichlet character mod 1000
    obtain ⟨χ, hχ⟩ :=
      DirichletCharacter.exists_apply_ne_one_of_hasEnoughRootsOfUnity
        (n := 1000) (R := ℂ) (a := (3 : ZMod 1000)) (by decide)
    refine ⟨χ, fun h => hχ ?_⟩
    rw [h]
    exact MulChar.one_apply ((ZMod.isUnit_iff_coprime 3 1000).mpr (by decide))
  · -- non-strict Burgess range
    constructor
    · norm_num
    · linarith [hfrac]
  · -- strict Burgess range (room to spare)
    constructor
    · norm_num
    · linarith [hfrac]

end Work.LinnikContract.Sat
