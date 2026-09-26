import Mathlib
import Submission.Work.SG.SellingDefs
import Submission.Work.SG.SellingStep
import Submission.Work.SG.selling_step_det
import Submission.Work.SG.selling_step_sb
import Submission.Work.SG.selling_step_measure

namespace Work.SG

open LeanEval.Geometry.SpaceGroupsProblem

open scoped Matrix

/-- **Selling reduction.** For every symmetric positive-semidefinite integer form `Q` there is a
unimodular `W` whose superbase `sb W` (see `SellingDefs`) is `Q`-obtuse, i.e. all cross terms
`bf Q (sb W m) (sb W n)` (`m ≠ n`) are `≤ 0`.

Route: iterate the Selling step on a *superbase* `v : Fin 4 → IVec` with `∑ m, v m = 0` and
`(v 1, v 2, v 3)` a `ℤ`-basis (start from `sb 1`).  If some `p_ij = bf Q (v i) (v j) > 0`, replace
`v` by `step v i j := fun m => if m = i then - v i else if m = j then v j else v m + v i`,
which is again a superbase, and the natural number `∑ m, qf Q (v m)` drops by exactly `2 * p_ij`
(use `∑_n bf Q (v i) (v n) = 0`, from `∑ m, v m = 0`, to write `qf Q (v i) = -∑_{n≠i} ...`).
Strong induction on that `ℕ` terminates.  Finally take `W := ![v 1, v 2, v 3]`. -/
theorem selling_reduce (Q : IMat) (hsym : Q.transpose = Q) (hpsd : ∀ v : IVec, 0 ≤ qf Q v) :
    ∃ W : IMat, IsUnit W.det ∧ ObSbase Q W := by
  -- The energy `∑ m, qf Q (v m)` of a superbase is a natural number; it is bounded below by `0`
  -- (`hpsd`) and each Selling step at a positive cross term `p_ij > 0` lowers it by `2 p_ij`.
  have hnonneg : ∀ W : IMat, 0 ≤ ∑ m, qf Q (sb W m) :=
    fun W => Finset.sum_nonneg fun m _ => hpsd _
  -- `hmain n` is the strong induction on the value `n` of the energy of the current basis.
  suffices hmain : ∀ n : ℕ, ∀ W : IMat, IsUnit W.det → (∑ m, qf Q (sb W m)).toNat = n →
      ∃ W' : IMat, IsUnit W'.det ∧ ObSbase Q W' by
    exact hmain _ 1 (by simp) rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro W hdet hn
    by_cases hob : ObSbase Q W
    · -- already obtuse
      exact ⟨W, hdet, hob⟩
    · -- some cross term is positive: perform one Selling step
      simp only [ObSbase, not_forall, not_le] at hob
      obtain ⟨i, j, hij, hp⟩ := hob
      -- the new basis is unimodular
      have hdet' : IsUnit (W * sellStepMat i j).det := by
        rw [Matrix.det_mul]
        exact hdet.mul (selling_step_det i j hij)
      -- its superbase is the Selling step of the old one, and the energy drops by `2 p_ij`
      have hmeas : ∑ m, qf Q (sb (W * sellStepMat i j) m)
          = ∑ m, qf Q (sb W m) - 2 * bf Q (sb W i) (sb W j) := by
        rw [selling_step_sb W i j hij]
        exact selling_step_measure Q hsym (sb W) (sb_sum_zero W) i j hij
      -- so its energy is a strictly smaller natural number
      have hlt : (∑ m, qf Q (sb (W * sellStepMat i j) m)).toNat < n := by
        have hF : (∑ m, qf Q (sb W m))
            = (∑ m, qf Q (sb (W * sellStepMat i j) m)) + 2 * bf Q (sb W i) (sb W j) := by
          rw [hmeas]; ring
        have hpos : 0 < (∑ m, qf Q (sb W m)) := by
          have := hnonneg (W * sellStepMat i j); rw [hF]; linarith
        rw [← hn, Int.toNat_lt_toNat hpos, hmeas]
        linarith
      exact ih _ hlt (W * sellStepMat i j) hdet' rfl

end Work.SG
