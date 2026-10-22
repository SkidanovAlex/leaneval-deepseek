import Mathlib
import Submission.Work.ANALYTIC.HaarPar

namespace Work.ANALYTIC

/-- Off-diagonal biorthogonality of the Haar/Schauder basis: `Haar.phi n` is the functional
`lam ↦ lam (a n) - lam (par n)` and `Haar.fCyl m` is the indicator of the level-`n(m)` cylinder of
the enumerated point `a m`; for `n ≠ m` the pairing vanishes.
Suggested route: `fCyl m x = if e_{n(m)} x = a m then 1 else 0` (`Haar.fCyl_apply'`).  Put
`L = lvl m`, `p = lvl n`.
* If `L + 1 ≤ p`: `π_L (par n) = π_L (a n)` (`Haar.proj_par_eq`), so `fCyl m (par n) = fCyl m (a n)`
  (`Haar.fCyl_congr_proj`), and the two terms of `phi` cancel.
* If `p ≤ L`: `e_L` fixes both `a n` (it lies in `A p ⊆ A L`) and `par n`
  (`Haar.par_mem_A_pred`, `∈ A (p-1) ⊆ A L`); moreover `a n ≠ a m`
  (`Work.ATOM.levelData_a_inj`) and `par n ≠ a m` (`Haar.par_ne_a_of_lvl_le`), so both values
  are `0`.
Helper lemmas `Work.ANALYTIC.Haar.mem_A_iff_fix`, `e_fixes_of_mem_A_le`, `proj_e_eq_of_le`,
`par_mem_A_pred`, `par_ne_self`, `e_lvl_par`, `fCyl_par_self`, `par_ne_a_of_lvl_le`,
`fCyl_congr_proj`, `proj_par_eq`, `phi_one` are in `Submission.Work.ANALYTIC.HaarPar`. -/
theorem haar_offdiag (T : LightProfinite.{0}) [Infinite T] (n m : ℕ) (h : n ≠ m) :
    Work.ANALYTIC.Haar.phi T n (Work.ANALYTIC.Haar.fCyl T m) = 0 := by
  have hphi : Work.ANALYTIC.Haar.phi T n (Work.ANALYTIC.Haar.fCyl T m)
      = Work.ANALYTIC.Haar.fCyl T m ((Work.ATOM.levelData T).a n)
        - Work.ANALYTIC.Haar.fCyl T m (Work.ANALYTIC.Haar.par T n) := rfl
  rw [hphi]
  by_cases hcase : Work.ANALYTIC.Haar.lvl T m + 1 ≤ Work.ANALYTIC.Haar.lvl T n
  · -- the level of `m` is strictly below the level of `n`: `π_{lvl m}` does not distinguish
    -- `par n` from `a n`
    have hpr : Work.ANALYTIC.Haar.fCyl T m (Work.ANALYTIC.Haar.par T n)
        = Work.ANALYTIC.Haar.fCyl T m ((Work.ATOM.levelData T).a n) :=
      Work.ANALYTIC.Haar.fCyl_congr_proj T (Work.ANALYTIC.Haar.proj_par_eq T hcase)
    rw [hpr, sub_self]
  · -- the level of `n` is at most the level of `m`: `e_{lvl m}` fixes both `a n` and `par n`,
    -- and neither is `a m`
    have hle : Work.ANALYTIC.Haar.lvl T n ≤ Work.ANALYTIC.Haar.lvl T m := by omega
    have ha : Work.ANALYTIC.Haar.fCyl T m ((Work.ATOM.levelData T).a n) = 0 := by
      rw [Work.ANALYTIC.Haar.fCyl_apply' T m, if_neg]
      intro hc
      rw [Work.ANALYTIC.Haar.e_a_of_lvl_le T hle] at hc
      exact h (Work.ATOM.levelData_a_inj hc)
    have hp : Work.ANALYTIC.Haar.fCyl T m (Work.ANALYTIC.Haar.par T n) = 0 := by
      rw [Work.ANALYTIC.Haar.fCyl_apply' T m, if_neg]
      intro hc
      rw [Work.ANALYTIC.Haar.e_par_of_lvl_le T hle] at hc
      exact Work.ANALYTIC.Haar.par_ne_a_of_lvl_le T hle hc
    rw [ha, hp, sub_zero]

end Work.ANALYTIC
