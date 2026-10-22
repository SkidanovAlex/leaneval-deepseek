import Mathlib
import Submission.Work.ANALYTIC.HaarBasisDefs

/-!
# The parent map `par` of the Haar/Schauder basis: elementary level facts

This file collects the elementary facts about the "parent" map
`Haar.par T j = e_{n(j)-1}(a_j)` (and `s₀` when `n(j) = 0`) which are needed to prove the
biorthogonality of the dual bases `phi T j : LC T → ℤ` and `fCyl T j : LC T` of
`Submission/Work/ANALYTIC/HaarDefs.lean`, i.e. `phi i (fCyl j) = δᵢⱼ`.

The key points are:

* `A n` is the *fixed point set* of the idempotent `e n` (`mem_A_iff_fix`), and
  `e n` fixes `A m` for `m ≤ n` (`e_fixes_of_mem_A_le`);
* `par j ∈ A (n(j) - 1)` (`par_mem_A_pred`), so its level is `< n(j)`; in particular
  `par j ≠ a j` (`par_ne_self`) and `par j` is never a point of level `≥ n(j)`
  (`par_ne_a_of_lvl_le`);
* `fCyl m` only depends on the level-`n(m)` projection (`fCyl_congr_proj`), and for
  `n(m) + 1 ≤ n(j)` the parent `par j` has the same level-`n(m)` projection as `a_j`
  (`proj_par_eq`);
* `phi j` vanishes on the constant function (`phi_one`).
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open OnePoint

attribute [local instance] Classical.propDecidable

noncomputable section

namespace Work.ANALYTIC

namespace Haar

variable (T : LightProfinite.{0}) [Infinite T]

/-! ## The level sets as fixed point sets -/

/-- `A n` is exactly the set of fixed points of the idempotent `e n`. -/
theorem mem_A_iff_fix (n : ℕ) (y : ↥T) : y ∈ Work.ATOM.A T n ↔ Work.ATOM.e T n y = y :=
  ⟨fun hy => Work.ATOM.e_fixes_of_mem_A T hy, fun hy => ⟨y, hy⟩⟩

/-- If `y ∈ A m` and `m ≤ n`, then `e n` fixes `y`. -/
theorem e_fixes_of_mem_A_le {m n : ℕ} (h : m ≤ n) {y : ↥T} (hy : y ∈ Work.ATOM.A T m) :
    Work.ATOM.e T n y = y :=
  Work.ATOM.e_fixes_of_mem_A T (Work.ATOM.A_mono_le T h hy)

/-- For `m ≤ k`, the `m`-th projection of `e_k x` is the `m`-th projection of `x`. -/
theorem proj_e_eq_of_le {k m : ℕ} (h : m ≤ k) (x : ↥T) :
    T.proj m (Work.ATOM.e T k x) = T.proj m x := by
  rw [proj_e_apply, Work.ATOM.leg_of_le T k m h]
  exact congrFun (T.proj_comp_transitionMapLE' (n := m) (m := k) h) x

/-! ## The parent map -/

/-- `par j` is the value of `β` at `(j, a_j)`. -/
theorem par_eq_betaFun (j : ℕ) :
    par T j = Work.ATOM.betaFun T (((j : ℕ) : ℕ∪{∞}), (Work.ATOM.levelData T).a j) := by
  by_cases h : Work.ATOM.lvl T j = 0
  · rw [par, dif_pos h, Work.ATOM.betaFun_lvl, if_pos h]
  · rw [par, dif_neg h, Work.ATOM.betaFun_lvl, if_neg h]

/-- For `n(j) ≠ 0`, the parent is `e_{n(j)-1}(a_j)`. -/
theorem par_eq_e_of_ne_zero (j : ℕ) (h : Work.ATOM.lvl T j ≠ 0) :
    par T j = Work.ATOM.e T (Work.ATOM.lvl T j - 1) ((Work.ATOM.levelData T).a j) := by
  rw [par, dif_neg h]

/-- The parent `par j` lies in `A (n(j)-1)`. -/
theorem par_mem_A_pred (j : ℕ) : par T j ∈ Work.ATOM.A T (Work.ATOM.lvl T j - 1) := by
  by_cases h : Work.ATOM.lvl T j = 0
  · rw [show par T j = (Work.ATOM.levelData T).s₀ from by rw [par, dif_pos h], h]
    simpa using (Work.ATOM.levelData T).mem_A0
  · rw [par_eq_e_of_ne_zero T j h]
    exact ⟨_, rfl⟩

/-- The parent of `a_j` is not `a_j` (its level is strictly smaller). -/
theorem par_ne_self (j : ℕ) : par T j ≠ (Work.ATOM.levelData T).a j := by
  by_cases h : Work.ATOM.lvl T j = 0
  · rw [show par T j = (Work.ATOM.levelData T).s₀ from by rw [par, dif_pos h]]
    exact fun hh => Work.ATOM.levelData_a_ne (S := T) j hh.symm
  · intro hc
    have h1 : (Work.ATOM.levelData T).lv (par T j) ≤ Work.ATOM.lvl T j - 1 :=
      Work.ATOM.levelData_lv_le (S := T) (par_mem_A_pred T j)
    rw [hc, Work.ATOM.levelData_lvl] at h1
    omega

/-- `e_{n(j)}` fixes the parent `par j`. -/
theorem e_lvl_par (j : ℕ) : Work.ATOM.e T (Work.ATOM.lvl T j) (par T j) = par T j :=
  e_fixes_of_mem_A_le T (Nat.sub_le _ _) (par_mem_A_pred T j)

/-- `f_j (par j) = 0`: the parent is not in the cylinder of `a_j`. -/
theorem fCyl_par_self (j : ℕ) : fCyl T j (par T j) = 0 := by
  rw [fCyl_apply', if_neg]
  intro h
  exact par_ne_self T j ((e_lvl_par T j).symm.trans h)

/-- If `n(j) ≤ n(k)` then `par j` is not the new point `a_k`: the level of `par j` is `< n(j)`. -/
theorem par_ne_a_of_lvl_le {n m : ℕ} (h : Work.ATOM.lvl T n ≤ Work.ATOM.lvl T m) :
    par T n ≠ (Work.ATOM.levelData T).a m := by
  by_cases h0 : Work.ATOM.lvl T n = 0
  · rw [show par T n = (Work.ATOM.levelData T).s₀ from by rw [par, dif_pos h0]]
    exact fun hc => Work.ATOM.levelData_a_ne (S := T) m hc.symm
  · intro hc
    have h1 : (Work.ATOM.levelData T).lv (par T n) ≤ Work.ATOM.lvl T n - 1 :=
      Work.ATOM.levelData_lv_le (S := T) (par_mem_A_pred T n)
    rw [hc, Work.ATOM.levelData_lvl] at h1
    omega

/-! ## The values of the cylinder functions -/

/-- `f_m` only depends on `π_{n(m)}`. -/
theorem fCyl_congr_proj {m : ℕ} {x y : ↥T}
    (h : T.proj (Work.ATOM.lvl T m) x = T.proj (Work.ATOM.lvl T m) y) :
    fCyl T m x = fCyl T m y := by
  rw [fCyl_apply T m x, fCyl_apply T m y, h]

/-- If `n(m) + 1 ≤ n(j)` then the parent `par j` has the same level-`n(m)` projection as `a_j`. -/
theorem proj_par_eq {n m : ℕ} (h : Work.ATOM.lvl T m + 1 ≤ Work.ATOM.lvl T n) :
    T.proj (Work.ATOM.lvl T m) (par T n)
      = T.proj (Work.ATOM.lvl T m) ((Work.ATOM.levelData T).a n) := by
  have h0 : Work.ATOM.lvl T n ≠ 0 := by omega
  rw [par_eq_e_of_ne_zero T n h0]
  exact proj_e_eq_of_le T (by omega) _

/-- `phi j` vanishes on the constant function `1`. -/
theorem phi_one (j : ℕ) : phi T j (1 : LC T) = 0 := by
  rw [phi, LocallyConstant.one_apply, LocallyConstant.one_apply, sub_self]

end Haar

end Work.ANALYTIC
