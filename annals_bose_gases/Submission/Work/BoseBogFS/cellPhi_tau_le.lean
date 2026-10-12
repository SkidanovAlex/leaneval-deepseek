import Mathlib.Analysis.Real.Sqrt
import Submission.Work.BoseBogFS.cellSplitDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.cellPhi_tau_le` — the `τ`-increment of `cellPhi`

With `cellPhi τ β = τ + β − √(τ² + 2τβ)`, the difference of two values of `cellPhi`
taken at the **same** `β = b` but at two different `τ, τ'` is bounded by

  `cellPhi τ b − cellPhi τ' b ≤ (u_hi − u_lo) + √((u_hi − u_lo) · (2 u_hi + 2 V))`

whenever `u_lo ≤ τ, τ' ≤ u_hi`, `0 ≤ u_lo` and `|b| ≤ V`.

This is one of the three pieces of `Work.BoseBogFS.psiSc_cell_sqrt_le` (the other two
being `Work.BoseBogFS.cellPhi_beta_le` and `Work.BoseBogFS.radialPair_le`); it is the
increment of the `τ`-slot `tauSc` of the clean bracket over a `τ`-window of width
`h = u_hi − u_lo`.

## The proof

Writing `x = τ² + 2τb`, `y = τ'² + 2τ'b` one has, definitionally,

  `cellPhi τ b − cellPhi τ' b = (τ − τ') + (√y − √x)`

which, since `√y − √x ≤ √|y − x|` for **all** real `x, y` (with the junk convention
`√x = 0` for `x < 0`; see `sqrt_sub_sqrt_le_sqrt_abs_sub` below), is at most

  `(τ − τ') + √|y − x| ≤ (u_hi − u_lo) + √(h · (2 u_hi + 2 V))`

because `τ − τ' ≤ h` and `|y − x| = |(τ' − τ)(τ' + τ + 2b)| ≤ h (2 u_hi + 2 V)`.
Note that the mixed-sign cases of `x, y` are *not* exceptions: they are covered by the
junk-safe form of `√y − √x ≤ √|y − x|`.
-/

namespace Work.BoseBogFS

/-- Junk-safe form of `|√y − √x| ≤ √|y − x|`: the one-sided version
`√y − √x ≤ √|y − x|` holds for all real `x, y`, including the negative arguments on
which `Real.sqrt` returns `0`. -/
lemma sqrt_sub_sqrt_le_sqrt_abs_sub (x y : ℝ) :
    Real.sqrt y - Real.sqrt x ≤ Real.sqrt |y - x| := by
  rcases le_or_gt 0 x with hx | hx
  · rcases le_or_gt 0 y with hy | hy
    · rcases le_or_gt y x with hyx | hyx
      · have h1 : Real.sqrt y ≤ Real.sqrt x := Real.sqrt_le_sqrt hyx
        have h2 : 0 ≤ Real.sqrt |y - x| := Real.sqrt_nonneg _
        linarith
      · have h1 : Real.sqrt y ≤ Real.sqrt x + Real.sqrt |y - x| := by
          rw [Real.sqrt_le_iff]
          refine ⟨by positivity, ?_⟩
          have hsq : (Real.sqrt x + Real.sqrt |y - x|) ^ 2
              = x + |y - x| + 2 * (Real.sqrt x * Real.sqrt |y - x|) := by
            rw [add_sq, Real.sq_sqrt hx, Real.sq_sqrt (abs_nonneg _)]
            ring
          rw [hsq]
          have h2 : y ≤ x + |y - x| := by
            rw [abs_of_nonneg (by linarith : 0 ≤ y - x)]
            linarith
          have h3 : 0 ≤ 2 * (Real.sqrt x * Real.sqrt |y - x|) := by positivity
          linarith
        linarith
    · have hy0 : Real.sqrt y = 0 := Real.sqrt_eq_zero_of_nonpos (le_of_lt hy)
      rw [hy0]
      have h2 : 0 ≤ Real.sqrt |y - x| := Real.sqrt_nonneg _
      have h3 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg _
      linarith
  · have hx0 : Real.sqrt x = 0 := Real.sqrt_eq_zero_of_nonpos (le_of_lt hx)
    rw [hx0]
    have h2 : Real.sqrt y ≤ Real.sqrt |y - x| := by
      apply Real.sqrt_le_sqrt
      calc y ≤ y - x := by linarith
        _ ≤ |y - x| := le_abs_self _
    linarith

theorem cellPhi_tau_le {τ τ' b u_lo u_hi V : ℝ}
    (hu0 : 0 ≤ u_lo) (hτl : u_lo ≤ τ) (hτh : τ ≤ u_hi) (hτ'l : u_lo ≤ τ')
    (hτ'h : τ' ≤ u_hi) (hV : |b| ≤ V) :
    Work.BoseBogFS.cellPhi τ b - Work.BoseBogFS.cellPhi τ' b
      ≤ (u_hi - u_lo) + Real.sqrt ((u_hi - u_lo) * (2 * u_hi + 2 * V)) := by
  have hh : 0 ≤ u_hi - u_lo := by linarith
  have hτ0 : 0 ≤ τ := le_trans hu0 hτl
  have hτ'0 : 0 ≤ τ' := le_trans hu0 hτ'l
  have hb1 : -V ≤ b := (abs_le.mp hV).1
  have hb2 : b ≤ V := (abs_le.mp hV).2
  have hkey : Real.sqrt (τ' ^ 2 + 2 * τ' * b) - Real.sqrt (τ ^ 2 + 2 * τ * b)
      ≤ Real.sqrt |τ' ^ 2 + 2 * τ' * b - (τ ^ 2 + 2 * τ * b)| :=
    sqrt_sub_sqrt_le_sqrt_abs_sub _ _
  have hfac : τ' ^ 2 + 2 * τ' * b - (τ ^ 2 + 2 * τ * b)
      = (τ' - τ) * (τ' + τ + 2 * b) := by ring
  have h1 : |τ' - τ| ≤ u_hi - u_lo := by
    rw [abs_le]; constructor <;> linarith
  have h2 : |τ' + τ + 2 * b| ≤ 2 * u_hi + 2 * V := by
    rw [abs_le]; constructor <;> linarith
  have harg : |τ' ^ 2 + 2 * τ' * b - (τ ^ 2 + 2 * τ * b)|
      ≤ (u_hi - u_lo) * (2 * u_hi + 2 * V) := by
    rw [hfac, abs_mul]
    exact mul_le_mul h1 h2 (abs_nonneg _) hh
  have hsqrt := Real.sqrt_le_sqrt harg
  have hdiff : τ - τ' ≤ u_hi - u_lo := by linarith
  have hunfold : Work.BoseBogFS.cellPhi τ b - Work.BoseBogFS.cellPhi τ' b
      = (τ - τ') + (Real.sqrt (τ' ^ 2 + 2 * τ' * b) - Real.sqrt (τ ^ 2 + 2 * τ * b)) := by
    simp only [Work.BoseBogFS.cellPhi]; ring
  rw [hunfold]
  linarith

end Work.BoseBogFS
